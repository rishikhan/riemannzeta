#!/usr/bin/env python3
"""Multi-node worker for q12x subtree jobs on a shared file system (Perlmutter).

    python qrun.py WORK ROOTS [--procs 128] [--xgen X] [--opts "..."] [--budget 200] [--resplit-depth 4]
                   [--presplit-depth 0] [--deadline EPOCH|+SECS] [--events FILE]
                   [--steal [--tail-threads T] [--tail-wait S] [--steal-interval S] [--handoff-wait S]] [--nice N]

Same file protocol as run_root.py (WORK/r<k>/top.nodes, jobs.txt, job_<id>.nodes / .jobs / .box / .log),
so run_root.py WORK k --check assembles and checks the result.  Differences from run_root.py --part:

* Jobs are shared dynamically between all qrun processes (any node, any Slurm job) through claim files
  WORK/r<k>/claims/<id> created with O_EXCL; a claim whose owner Slurm job is no longer running (or whose
  owner process on this host is gone) is stale and is taken over.
* ROOTS is a comma list worked in order: workers take pending jobs of the first root before the next.
* --presplit-depth D: a top-level job (id without '.') runs as `xgen frontier --depth D` instead of a tree,
  so its sub-jobs are spread over all workers without first overflowing a budget.
* --deadline: at that time (or on SIGTERM / SIGINT) the running xgen processes are terminated, their claims
  removed, and qrun exits 0.  Only the in-progress jobs are lost: xgen renames its output into place on
  success, so a later qrun resumes from the files.
* --steal (needs xgen_st): work stealing instead of budget / resplit.  Every tree job runs with
  `--steal-dir WORK/r<k>/queue --job-id <id>`; a running xgen donates its shallowest pending box as a job
  file queue/<id>.job on SIGUSR1, and the job's node file gets a "J <rel id>" placeholder (FORMAT.md).
  Every second qrun reads the queue directory and, while idle slots exceed queued jobs (summed over all
  qrun processes through WORK/qstate/), sends SIGUSR1 to its longest-running xgen processes (its share of
  the shortfall in proportion to its running jobs; one process at most every --steal-interval seconds).
  The deadline is passed to xgen (--deadline) and also sent as SIGTERM: xgen finishes the node in progress,
  donates every box it has not started, renames its output into place and exits 0, so nothing is lost;
  qrun waits --handoff-wait seconds before SIGKILL.  --budget N then means a hand-off at N leaves.
  --tail-threads T: once idle slots have exceeded queued jobs for --tail-wait seconds (donation is not
  keeping up, i.e. the tail), a job is started with up to T scan threads (xgen --threads, same tree); a job
  occupies as many slots as it has threads.
* --nice N: run xgen at that nice level.  Without Slurm (a workstation, a login node) claims are checked by
  process id on the same host, so qrun.py alone is the single-node driver too:
  run_root.py WORK k --frontier-only, then qrun.py WORK k --steal --procs P --nice 19, then run_root.py WORK k --check.
* Events (one JSON object per line): one record per finished or killed job (wall, user CPU, max RSS,
  leaves) and a sample every --sample seconds (busy workers, load average).
Needs the top frontier of each root (run_root.py WORK k --frontier-only); roots without it are skipped.
"""
import argparse
import json
import math
import os
import shutil
import signal
import socket
import subprocess
import sys
import threading
import time
from collections import deque

HOST = socket.gethostname()
JOBID = os.environ.get('SLURM_JOB_ID', '')
OWNER = '%s %s %d' % (JOBID or 'none', HOST, os.getpid())


def stats_line(path):
    try:
        with open(path) as f:
            for ln in f:
                if ln.startswith('# rc'):
                    v = ln[2:].split()
                    return {v[i]: float(v[i + 1]) for i in range(0, len(v) - 1, 2) if v[i] != 'stages'}
    except OSError:
        pass
    return None


def memavail():
    try:
        for ln in open('/proc/meminfo'):
            if ln.startswith('MemAvailable:'):
                return int(ln.split()[1])
    except OSError:
        pass
    return None


class Q:
    def __init__(self, a):
        self.a = a
        self.W = os.path.abspath(a.work)
        self.roots = [int(x) for x in a.roots.split(',')]
        self.eng = os.path.join(self.W, 'model.pkl.eng')
        self.ex = os.path.join(self.W, 'exact.txt')
        self.lock = threading.RLock()     # re-entrant: the signal handler may run while the main thread holds it
        self.queue = deque()          # (root, jid, vals)
        self.local = set()            # (root, jid) queued or running here
        self.running = {}             # (root, jid) -> Popen
        self.stop = threading.Event()
        self.last_scan = 0.0
        self.live = set()
        self.live_t = 0.0
        self.squeue_lock = threading.Lock()
        self.ev = open(a.events, 'a', buffering=1)
        self.nbusy = 0
        self.done_all = False
        self.slots = 0                # slots in use (a job with T scan threads uses T)
        self.meta = {}                # (root, jid) -> (start time, threads, mode) of running jobs
        self.signaled = {}            # (root, jid) -> time of the last SIGUSR1
        self.hungry_since = None      # idle slots > queued jobs since then (None: not hungry)
        self.ndonated = 0
        self.qseen = set()            # (root, jid) of queue entries already examined
        self.qstate = os.path.join(self.W, 'qstate', '%s.%d' % (HOST, os.getpid()))
        self.fin = {}                 # (root, jid) -> .jobs lines of a finished job (its files never change again)
        self.closed = set()           # (root, jid) whose whole subtree is finished
        self.deep_t = 0.0             # time of the last scan that read the claim files
        # node-local scratch for job_<id>.box / .log: on Lustre each client serializes creates, renames and lookups
        # in one directory, so per-job files in r<k>/ stall the workers and the scan (2026-10-25, job 60276828)
        self.tmp = os.path.join(os.environ.get('TMPDIR') or '/tmp', 'q12x_%s_%d' % (JOBID or 'none', os.getpid()))
        self.names = {}               # root -> names in r<k>/ from one listing at the first scan (files never vanish)
        self.failed = {}              # root -> ids parked in r<k>/failed/ (one listing per scan)

    def event(self, **kw):
        kw.update(t=round(time.time(), 1), host=HOST, job=JOBID)
        with self.lock:
            self.ev.write(json.dumps(kw) + '\n')

    def R(self, root):
        return os.path.join(self.W, 'r%d' % root)

    # ---- claims -------------------------------------------------------------------------------------
    def live_jobs(self):
        """running Slurm job ids of this user; one squeue call at a time, at most every 5 minutes"""
        with self.squeue_lock:
            if time.time() - self.live_t > 300:
                try:
                    out = subprocess.run(['squeue', '-h', '-u', os.environ.get('USER', ''), '-t', 'R', '-o', '%A'],
                                         capture_output=True, text=True, timeout=60).stdout
                    self.live = set(out.split())
                except Exception:
                    pass              # keep the previous set: never treat claims as stale on a squeue error
                self.live_t = time.time()
            return self.live

    def stale(self, path):
        try:
            jid, host, pid = open(path).read().split()
        except (OSError, ValueError):
            return False              # being written, or gone
        if host == HOST:
            try:
                os.kill(int(pid), 0)
                return False
            except ProcessLookupError:
                return True
            except (PermissionError, ValueError):
                return False
        if jid == 'none' or jid == JOBID:
            return False              # another node of this Slurm job, or a login-node run elsewhere
        return jid not in self.live_jobs()

    def claim(self, root, jid):
        d = os.path.join(self.R(root), 'claims')
        os.makedirs(d, exist_ok=True)
        p = os.path.join(d, jid)
        for _ in range(2):
            try:
                fd = os.open(p, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o644)
                os.write(fd, OWNER.encode())
                os.close(fd)
                return True
            except FileExistsError:
                if not self.stale(p):
                    return False
                try:
                    os.unlink(p)
                except FileNotFoundError:
                    pass
        return False

    def unclaim(self, root, jid):
        try:
            os.unlink(os.path.join(self.R(root), 'claims', jid))
        except FileNotFoundError:
            pass

    def claimed_live(self, root, jid):
        p = os.path.join(self.R(root), 'claims', jid)
        return os.path.exists(p) and not self.stale(p)

    def claims(self, root):
        try:
            return set(os.listdir(os.path.join(self.R(root), 'claims')))
        except FileNotFoundError:
            return set()

    def taken(self, root, jid, claimed, deep):
        """claimed by a live worker.  Only a deep scan reads the claim file (stale-claim check); otherwise an
        existing claim counts as live, so a scan costs one directory listing instead of a read per claim."""
        if jid not in claimed:
            return False
        return self.claimed_live(root, jid) if deep else True

    # ---- pending jobs (run_root.py's rule) ----------------------------------------------------------
    def pending(self, root, jid, vals, claimed=()):
        """Finished jobs are remembered (xgen writes .jobs before it renames .nodes into place, and neither file
        changes afterwards), and a claimed job counts as unfinished without a stat (the claim is removed only after
        the rename), so a rescan stats only the unclaimed unfinished jobs, not every job file of the root."""
        key = (root, jid)
        if key in self.closed:
            return []
        subs = self.fin.get(key)
        if subs is None:
            if jid in claimed or key in self.local:   # queued here: job() checks for its output before running
                return [(jid, vals)]
            R = self.R(root)
            names = self.names.get(root)
            if names is None or 'job_%s.nodes' % jid not in names:
                if not os.path.exists(os.path.join(R, 'job_%s.nodes' % jid)):
                    if jid + '.job' in self.failed.get(root, ()):
                        return []     # parked build failure: not pending (see job())
                    return [(jid, vals)]
                hasjobs = os.path.exists(os.path.join(R, 'job_%s.jobs' % jid))
            else:                     # .jobs is written before .nodes is renamed into place
                hasjobs = 'job_%s.jobs' % jid in names
            sub = os.path.join(R, 'job_%s.jobs' % jid)
            subs = [ln.split() for ln in open(sub)] if hasjobs else []
            self.fin[key] = subs
        res = []
        for v in subs:
            res += self.pending(root, '%s.%s' % (jid, v[0]), v[1:], claimed)
        if not res:
            self.closed.add(key)
            self.fin.pop(key, None)
        return res

    def scan_queue(self, full=True, deep=False):
        """add the donated jobs (WORK/r<k>/queue/<id>.job) to the queue; drop entries of finished jobs.
        Returns the number of unfinished entries.  full=False (every second): only entries not seen before,
        so the shared file system sees two directory listings per root (queue/, claims/), not a stat per entry.
        Claimed entries are not stat'ed in either mode; deep=True also reads their claim files."""
        npend = 0
        new = []
        gone = set()                  # queued here, but finished or claimed elsewhere
        for root in self.roots:
            R = self.R(root)
            d = os.path.join(R, 'queue')
            try:
                names = os.listdir(d)
            except FileNotFoundError:
                continue
            claimed = self.claims(root)
            if not full:
                entries = set(nm[:-4] for nm in names if nm.endswith('.job'))
                with self.lock:
                    for x in self.queue:
                        if x[0] == root and (x[1] in claimed or ((root, x[1]) in self.qseen and x[1] not in entries)):
                            gone.add((root, x[1]))
            for nm in names:
                if not nm.endswith('.job'):
                    continue
                jid = nm[:-4]
                if (root, jid) in self.qseen and (not full or not deep):
                    continue
                self.qseen.add((root, jid))
                if (root, jid) in self.local or self.taken(root, jid, claimed, deep):
                    npend += 1
                    continue
                npend += 1            # (an entry whose job finished but kept its file: job() removes it)
                try:
                    vals = open(os.path.join(d, nm)).read().split()
                except FileNotFoundError:
                    continue
                new.append((root, jid, vals))
        with self.lock:
            if gone:
                self.queue = deque(x for x in self.queue if (x[0], x[1]) not in gone)
                self.local -= gone
            for x in new:
                if (x[0], x[1]) not in self.local:
                    self.local.add((x[0], x[1]))
                    self.queue.append(x)
            if new:
                self.order()
        return npend

    def order(self):
        """roots in ROOTS order: frontier and donated jobs of an early root run before those of a later one
        (caller holds the lock; the sort is stable, so each root keeps its own order)"""
        if len(self.roots) > 1:
            self.queue = deque(sorted(self.queue, key=lambda x: self.roots.index(x[0])))

    def scan(self):
        """refill the queue from the files; returns the number of pending jobs anywhere (claimed or not).
        Claim files are read (stale claims taken over) on the first scan and then at most every 5 minutes, the
        refresh period of live_jobs, which bounds how fast a dead Slurm job's claims can be detected anyway."""
        now = time.time()
        deep = now - self.deep_t >= 300
        if deep:
            self.deep_t = now
        npend = self.scan_queue(deep=deep) if self.a.steal else 0
        if self.a.steal:              # drop queued jobs that another worker finished
            with self.lock:
                items = list(self.queue)
            done = set((x[0], x[1]) for x in items if (x[0], x[1]) not in self.qseen     # queue/ entries: steal_tick
                       and os.path.exists(os.path.join(self.R(x[0]), 'job_%s.nodes' % x[1])))
            if done:
                with self.lock:
                    self.queue = deque(x for x in self.queue if (x[0], x[1]) not in done)
                    self.local -= done
        new = []
        for root in self.roots:
            R = self.R(root)
            jobs = os.path.join(R, 'jobs.txt')
            if not os.path.exists(os.path.join(R, 'top.nodes')) or not os.path.exists(jobs):
                continue
            claimed = self.claims(root)
            try:
                self.failed[root] = set(os.listdir(os.path.join(R, 'failed')))
            except FileNotFoundError:
                self.failed[root] = set()
            if root not in self.names:
                self.names[root] = set(os.listdir(R))
            for ln in open(jobs):
                v = ln.split()
                for jid, vals in self.pending(root, v[0], v[1:], claimed):
                    npend += 1
                    if (root, jid) in self.local or self.taken(root, jid, claimed, deep):
                        continue
                    new.append((root, jid, vals))
        with self.lock:
            for x in new:
                if (x[0], x[1]) not in self.local:
                    self.local.add((x[0], x[1]))
                    self.queue.append(x)
            if new:
                self.order()
            self.last_scan = time.time()
        return npend

    # ---- one job ------------------------------------------------------------------------------------
    def run(self, root, jid, cmd, log, threads=1, mode='tree'):
        if self.a.nice:
            cmd = ['nice', '-n', str(self.a.nice)] + cmd
        with open(log, 'a') as f:
            p = subprocess.Popen(cmd, stdout=f, stderr=subprocess.STDOUT)
            with self.lock:
                self.running[(root, jid)] = p
                self.meta[(root, jid)] = (time.time(), threads, mode)
            if self.stop.is_set():
                p.terminate()
            _, status, ru = os.wait4(p.pid, 0)
            p.returncode = os.waitstatus_to_exitcode(status)
            with self.lock:
                self.running.pop((root, jid), None)
                self.meta.pop((root, jid), None)
                self.signaled.pop((root, jid), None)
        return p.returncode, ru

    def job(self, root, jid, vals, threads=1):
        a = self.a
        R = self.R(root)
        out = os.path.join(R, 'job_%s.nodes' % jid)
        if os.path.exists(out):
            try:
                os.unlink(os.path.join(R, 'queue', jid + '.job'))
            except FileNotFoundError:
                pass
            return
        td = os.path.join(self.tmp, 'r%d' % root)
        os.makedirs(td, exist_ok=True)
        bx = os.path.join(td, 'job_%s.box' % jid)
        with open(bx, 'w') as f:
            f.write(' '.join(vals) + '\n')
        log = os.path.join(td, 'job_%s.log' % jid)
        jobsf = os.path.join(R, 'job_%s.jobs' % jid)
        opts = a.opts.split()
        pre = '.' not in jid and a.presplit_depth > 0
        if pre:
            mode = 'presplit'
            cmd = [a.xgen, 'frontier', self.eng, self.ex, bx, out, jobsf, '--depth', str(a.presplit_depth)] + opts
        else:
            mode = 'tree'
            cmd = [a.xgen, 'tree', self.eng, self.ex, bx, out] + (['--budget', str(a.budget)] if a.budget else []) + opts
            if a.steal:
                qd = os.path.join(R, 'queue')
                os.makedirs(qd, exist_ok=True)
                cmd += ['--steal-dir', qd, '--job-id', jid] + (['--deadline', '%d' % a.deadline] if a.deadline else [])
            if threads > 1:
                cmd += ['--threads', str(threads)]
        t0 = time.time()
        rc, ru = self.run(root, jid, cmd, log, threads, mode)
        st = stats_line(out if rc == 0 else out + '.tmp') or {}
        self.event(kind='job', root=root, jid=jid, mode=mode, rc=rc, wall=round(time.time() - t0, 2),
                   utime=round(ru.ru_utime, 2), maxrss_kb=ru.ru_maxrss, leaves=st.get('leaves'),
                   jobs=st.get('jobs'), threads=threads, donated=st.get('donated'), handoff=st.get('handoff'),
                   killed=self.stop.is_set() and rc != 0)
        if rc == 0 and a.steal:
            try:
                os.unlink(os.path.join(R, 'queue', jid + '.job'))
            except FileNotFoundError:
                pass
            with self.lock:
                self.ndonated += int(st.get('donated') or 0)
        if rc == 1 and mode == 'tree' and a.budget and not a.steal and st.get('rc') == 1 and not self.stop.is_set():
            t1 = time.time()
            rc2, ru = self.run(root, jid, [a.xgen, 'frontier', self.eng, self.ex, bx, out, jobsf, '--depth',
                                           str(a.resplit_depth)] + opts, log)
            st = stats_line(out if rc2 == 0 else out + '.tmp') or {}
            self.event(kind='job', root=root, jid=jid, mode='resplit', rc=rc2, wall=round(time.time() - t1, 2),
                       utime=round(ru.ru_utime, 2), maxrss_kb=ru.ru_maxrss, leaves=st.get('leaves'),
                       jobs=st.get('jobs'), killed=self.stop.is_set() and rc2 != 0)
            rc = rc2
        if rc == 0 and os.path.exists(jobsf) and os.path.exists(out):
            subs = []
            for ln in open(jobsf):
                v = ln.split()
                subs.append((root, '%s.%s' % (jid, v[0]), v[1:]))
            with self.lock:
                for x in reversed(subs):          # front of the queue: finish this root's subtrees first
                    if (x[0], x[1]) not in self.local:
                        self.local.add((x[0], x[1]))
                        self.queue.appendleft(x)
        elif rc != 0 and not self.stop.is_set() and rc != 5:
            self.event(kind='fail', root=root, jid=jid, rc=rc)
            shutil.copy(log, os.path.join(R, 'job_%s.log' % jid))   # run_root.py counts failed runs' CPU from it
            if rc == 1 and mode == 'tree':
                # deterministic build failure (maxdepth / no split / certify): park the box in failed/ so that
                # no worker retries it; the root then ends with these boxes listed instead of looping on them
                fd = os.path.join(R, 'failed')
                os.makedirs(fd, exist_ok=True)
                with open(os.path.join(fd, jid + '.job.tmp'), 'w') as f:
                    f.write(' '.join(vals) + '\n')
                    f.write('# ' + json.dumps(st) + '\n')
                os.replace(os.path.join(fd, jid + '.job.tmp'), os.path.join(fd, jid + '.job'))
                try:
                    os.unlink(os.path.join(R, 'queue', jid + '.job'))
                except FileNotFoundError:
                    pass
        for f in (bx, log):
            try:
                os.unlink(f)
            except FileNotFoundError:
                pass

    def worker(self):
        a = self.a
        while not self.stop.is_set():
            item = None
            with self.lock:
                if self.queue and self.slots < a.procs:
                    item = self.queue.popleft()
                    t = 1
                    if a.tail_threads > 1 and self.hungry_since is not None and time.time() - self.hungry_since >= a.tail_wait:
                        free = a.procs - self.slots
                        t = max(1, min(a.tail_threads, free // (len(self.queue) + 1)))
                    self.slots += t
            if item is None:
                if self.done_all:
                    return
                time.sleep(0.2 if a.steal else 1)
                continue
            root, jid, vals = item
            try:
                if self.claim(root, jid):
                    with self.lock:
                        self.nbusy += 1
                    try:
                        self.job(root, jid, vals, t)
                    finally:
                        self.unclaim(root, jid)
                        with self.lock:
                            self.nbusy -= 1
            finally:
                with self.lock:
                    self.slots -= t
                    self.local.discard((root, jid))

    # ---- stealing -----------------------------------------------------------------------------------
    def others(self):
        """(idle slots, running jobs) of the other qrun processes (WORK/qstate/, updated within 10 s)"""
        d = os.path.dirname(self.qstate)
        idle = busy = 0
        try:
            names = os.listdir(d)
        except FileNotFoundError:
            return 0, 0
        for nm in names:
            p = os.path.join(d, nm)
            if p == self.qstate or nm.endswith('.tmp'):
                continue
            try:
                t, i, b = open(p).read().split()
                if time.time() - float(t) < 10:
                    idle += int(i); busy += int(b)
            except (OSError, ValueError):
                pass
        return idle, busy

    def steal_tick(self):
        """publish this node's state; send SIGUSR1 to running xgen processes while slots are idle"""
        a = self.a
        self.scan_queue(full=False)
        now = time.time()
        with self.lock:
            idle = a.procs - self.slots
            qn = len(self.queue)
            cand = sorted((m[0], k) for k, m in self.meta.items()     # not in their first 3 s (start-up)
                          if m[2] == 'tree' and now - m[0] >= 3 and now - self.signaled.get(k, 0) >= a.steal_interval)
            mine = sum(1 for m in self.meta.values() if m[2] == 'tree')
        os.makedirs(os.path.dirname(self.qstate), exist_ok=True)
        with open(self.qstate + '.tmp', 'w') as f:
            f.write('%.1f %d %d\n' % (now, idle, mine))
        os.replace(self.qstate + '.tmp', self.qstate)
        oi, ob = self.others()
        want = idle + oi - qn
        if want <= 0:
            self.hungry_since = None
            return
        if self.hungry_since is None:
            self.hungry_since = now
        share = math.ceil(want * mine / max(1, mine + ob))
        for _, k in cand[:share]:
            with self.lock:
                p = self.running.get(k)
                if p is None:
                    continue
                self.signaled[k] = now
            try:
                p.send_signal(signal.SIGUSR1)
            except ProcessLookupError:
                pass

    def shutdown(self, why):
        if self.stop.is_set():
            return
        self.stop.set()
        with self.lock:
            procs = dict(self.running)
        for p in procs.values():
            try:
                p.terminate()
            except ProcessLookupError:
                pass
        t = time.time()
        while time.time() - t < (self.a.handoff_wait if self.a.steal else 10):
            with self.lock:
                if not self.running:
                    break
            time.sleep(0.2)
        with self.lock:
            for p in self.running.values():
                try:
                    p.kill()
                except ProcessLookupError:
                    pass
        for (root, jid) in procs:
            self.unclaim(root, jid)
        try:
            os.unlink(self.qstate)
        except FileNotFoundError:
            pass
        self.event(kind='stop', why=why, killed=len(procs))

    def main(self):
        a = self.a
        self.event(kind='start', procs=a.procs, roots=a.roots, budget=a.budget, presplit=a.presplit_depth,
                   xgen=a.xgen, opts=a.opts, steal=a.steal, tail_threads=a.tail_threads)
        ths = [threading.Thread(target=self.worker, daemon=True) for _ in range(a.procs)]
        for th in ths:
            th.start()
        last_sample = 0.0
        while not self.stop.is_set():
            now = time.time()
            if a.deadline and now >= a.deadline:
                self.shutdown('deadline')
                break
            with self.lock:
                qn, busy, slots = len(self.queue), self.nbusy, self.slots
            if qn < a.procs and now - self.last_scan > a.rescan:
                npend = self.scan()
                with self.lock:
                    if npend == 0 and self.nbusy == 0 and not self.queue:
                        self.done_all = True
                if self.done_all:
                    break
            elif a.steal:
                self.steal_tick()
            if now - last_sample >= a.sample:
                self.event(kind='sample', busy=busy, slots=slots, queued=qn, donated=self.ndonated,
                           load=os.getloadavg()[0], mem_avail_kb=memavail())
                last_sample = now
            time.sleep(1)
        for th in ths:
            th.join(timeout=30)
        try:
            os.unlink(self.qstate)
        except FileNotFoundError:
            pass
        self.event(kind='end', done_all=self.done_all)
        print('qrun %s: %s' % (HOST, 'all roots done' if self.done_all else 'stopped'), flush=True)


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser()
    ap.add_argument('work'); ap.add_argument('roots')
    ap.add_argument('--procs', type=int, default=128)
    ap.add_argument('--xgen', default=os.path.join(here, '..', 'cpp_race', 'xgen'))
    ap.add_argument('--opts', default='')
    ap.add_argument('--budget', type=int, default=None, help='default 200; 0 with --steal (hand-off at N leaves)')
    ap.add_argument('--resplit-depth', type=int, default=4)
    ap.add_argument('--presplit-depth', type=int, default=0)
    ap.add_argument('--deadline', default='')
    ap.add_argument('--rescan', type=float, default=20.0)
    ap.add_argument('--sample', type=float, default=30.0)
    ap.add_argument('--events', default='')
    ap.add_argument('--steal', action='store_true', help='work stealing and deadline hand-off (xgen_st)')
    ap.add_argument('--steal-interval', type=float, default=5.0, help='s between SIGUSR1 to the same xgen')
    ap.add_argument('--handoff-wait', type=float, default=45.0, help='s from SIGTERM to SIGKILL with --steal')
    ap.add_argument('--tail-threads', type=int, default=1)
    ap.add_argument('--tail-wait', type=float, default=20.0)
    ap.add_argument('--nice', type=int, default=0)
    a = ap.parse_args()
    a.xgen = os.path.abspath(a.xgen)
    if a.budget is None:
        a.budget = 0 if a.steal else 200
    if a.deadline.startswith('+'):
        a.deadline = time.time() + float(a.deadline[1:])
    else:
        a.deadline = float(a.deadline) if a.deadline else 0.0
    if not a.events:
        a.events = os.path.join(os.path.abspath(a.work), 'qrun_%s_%s.jsonl' % (JOBID or 'login', HOST))
    q = Q(a)
    signal.signal(signal.SIGTERM, lambda *_: q.shutdown('SIGTERM'))
    signal.signal(signal.SIGINT, lambda *_: q.shutdown('SIGINT'))
    q.main()


if __name__ == '__main__':
    main()
