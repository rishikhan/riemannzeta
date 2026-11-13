#!/usr/bin/env python3
"""Perlmutter evaluation worker for pm_driver.py: claims task files, runs winobj.evaluate, writes results.

    python pm_worker.py --run RUN --threads 42 --deadline EPOCH [--est 240] [--idle 600]

RUN/tasks/NAME.json holds {xfree, x0, rounds, q, kb}; a worker claims a task by renaming it into
RUN/running/ (atomic on one file system), touches the claim every 20 s, writes RUN/results/NAME.json
and removes the claim.  It claims nothing when now + est passes the deadline, and exits when
RUN/STOP exists or no task has appeared for --idle seconds.
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "VECLIB_MAXIMUM_THREADS", "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "1")

import argparse                                  # noqa: E402
import json
import socket
import threading
import time
from pathlib import Path

import winobj


def heartbeat(path, stop):
    while not stop.wait(20):
        try:
            os.utime(path)
        except OSError:
            return


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--run', required=True)
    ap.add_argument('--threads', type=int, default=42)
    ap.add_argument('--deadline', type=float, required=True)
    ap.add_argument('--est', type=float, default=240)
    ap.add_argument('--idle', type=float, default=600)
    a = ap.parse_args()
    run = Path(a.run)
    tag = '%s.%d.%s' % (socket.gethostname(), os.getpid(), os.environ.get('SLURM_JOB_ID', 'x'))
    last = time.time()
    while not (run / 'STOP').exists() and time.time() + a.est < a.deadline:
        claim = None
        for t in sorted((run / 'tasks').glob('*.json')):
            dst = run / 'running' / (t.stem + '.' + tag)
            try:
                os.rename(t, dst)
            except OSError:
                continue
            os.utime(dst)                        # rename keeps the task's old mtime
            claim = (t.stem, dst)
            break
        if claim is None:
            if time.time() - last > a.idle:
                break
            time.sleep(2)
            continue
        name, dst = claim
        task = json.loads(dst.read_text())
        stop = threading.Event()
        threading.Thread(target=heartbeat, args=(dst, stop), daemon=True).start()
        x0 = json.load(open(task['x0']))['x'] if task.get('x0') else None
        try:
            r = winobj.evaluate(task['xfree'], task['q'], rounds=task['rounds'], threads=a.threads,
                                x0=x0, kb=task['kb'])
        except Exception as e:                   # a crashed refit counts as a failed window
            r = dict(achieved=-1.0, fail=['error: %r' % e])
        stop.set()
        r.update(xfree=task['xfree'], worker=tag, x0=task.get('x0'))
        tmp = run / 'results' / (name + '.tmp')
        tmp.write_text(json.dumps(r))
        os.rename(tmp, run / 'results' / (name + '.json'))
        try:
            dst.unlink()
        except OSError:
            pass
        last = time.time()


if __name__ == '__main__':
    main()
