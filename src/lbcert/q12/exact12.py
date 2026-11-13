#!/usr/bin/env python3
"""Exact leaves on a sample of boxes at Q gaps: certify + exact replay, with timings.

    python exact12.py MODEL.pkl PTS.pkl OUT.pkl --root 0 [--descend 14] [--boxes 4] [--budget 60]
        [--threads 8] [--seed 1]

Descends from the root along random children of the float builder's splits to `descend` levels
(or until the box is a float leaf), then builds the exact tree (q9hs TreeBuilder2: LeafSolverHS with
the half-space row, certificates checked by HSChecker) on that box with a leaf budget, and replays
it with HSChecker.walkC.  The split word is 1 + AXB + 3 bits with AXB = (Q + NP - 1).bit_length()
(7 at Q = 12, where the 78 axes do not fit q = 9's 6-bit field).  Reports per box: leaves, exact
fails, seconds in certification (LP + rounding + exact check), seconds in splits, replay seconds.
"""
import argparse
import os
import pickle
import random
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import fb12                                   # noqa: E402
from fb12 import root_state, children, G      # noqa: E402
import hs                                     # noqa: E402
import tables as T                            # noqa: E402
from leafhs import LeafSolverHS               # noqa: E402
from treehs import TreeBuilder2, Bits         # noqa: E402
from qgen import replay                       # noqa: E402

nsub = replay.nsub


class HSCheckerW(hs.HSChecker):
    """Split word with AXB axis bits."""
    def walkC(self, bits, fuel, pos, s, cuts=None, rec=None, depth=0):
        if fuel == 0:
            return 0
        AXB = fb12.axis_bits(self.M)
        w = bits(pos)
        if (w & 1) == 1:
            ax = (w >> 1) & ((1 << AXB) - 1)
            md = (w >> (1 + AXB)) & 7
            return self.splitAx(bits, fuel, md, pos + 4 + AXB, ax, s, cuts, rec, depth)
        return self.leafStep(pos, w, s, rec, depth)


class TB(TreeBuilder2):
    """TreeBuilder2 (no half-gate) writing the AXB-bit split word; timings of certify and choose."""
    def __init__(self, *a, **kw):
        super().__init__(*a, **kw)
        self.AXB = fb12.axis_bits(self.M)
        self.t_cert = 0.0
        self.t_scan = 0.0

    def certify(self, s):
        t0 = time.time()
        try:
            return super().certify(s)
        finally:
            self.t_cert += time.time() - t0

    def choose(self, s):
        t0 = time.time()
        try:
            return super().choose(s)
        finally:
            self.t_scan += time.time() - t0

    def node(self, s, out, depth, m=None):
        st = self.stats
        st['maxdepth'] = max(st['maxdepth'], depth)
        if self.leaf_budget and st['leaves'] + st['refl'] > self.leaf_budget:
            raise RuntimeError('leaf budget %d exceeded' % self.leaf_budget)
        Q = self.M.Q
        if s[1][Q - 1] < s[0][0]:
            out.put(0, 1)
            st['refl'] += 1
            return
        if m is None:
            m = self.margin(s)
        if m < self.gate and self.pen > 0:
            mr = self.E.margin_raw(s)
            if mr >= self.gate:
                m = mr
        if m >= self.gate:
            pl, nb, mg, _ = self.certify(s)
            if pl is not None:
                out.put(0, 2)
                out.put(pl, nb)
                st['leaves'] += 1
                st['leafbits'] += 2 + nb
                st['margins'].append(mg)
                self.note_anchors(s, pl, False)
                st['half'] += 1 if getattr(self.C, 'last_half', 0) else 0
                return
            st['fails'] += 1
        if depth >= self.max_depth:
            raise RuntimeError('depth limit')
        if m >= self.gate:
            r = max(range(Q), key=lambda r: s[1][r] - s[0][r])
            best = (0.0, r, 0, None, None)
        else:
            best = self.choose(s)
            if best is not None and m < 0 and best[0] - m < self.stall * (-m):
                r = max(range(Q), key=lambda r: s[1][r] - s[0][r])
                if s[1][r] - s[0][r] >= 2:
                    cands = [t for t in self.scan(s) if t[1] == r]
                    if cands:
                        best = cands[0]
        if best is None:
            raise RuntimeError('no split')
        _, a, md, x, y = best
        q, left, right = children(self.C, s, a, md)
        out.put(1 | (a << 1) | (md << (1 + self.AXB)), 4 + self.AXB)
        st['splits'] += 1
        self.node(left, out, depth + 1, x)
        self.node(right, out, depth + 1, y)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('model'); ap.add_argument('pts'); ap.add_argument('out')
    ap.add_argument('--root', type=int, default=0)
    ap.add_argument('--descend', type=int, default=14)
    ap.add_argument('--boxes', type=int, default=4)
    ap.add_argument('--budget', type=int, default=60)
    ap.add_argument('--threads', type=int, default=8)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--worse', type=float, default=0.8, help='probability of descending into the worse child')
    a = ap.parse_args()
    M, C0, P, E = fb12.setup(a.model, a.pts)
    C = HSCheckerW(M)
    C.half = True
    fields = hs.tb_fields(C) if M.KB <= (1 << 20) else {}
    M.TBL = hs.pack_tb(fields)
    PT = T.Points(C); PT.cache = P; PT.frozen = True
    C.PT = PT.pt
    ls = LeafSolverHS(C, PT.pt, half=True, var=False)
    ls.MAXBITS = M.WMASK.bit_length() - 2
    roots = G.roots_of(M)
    sh = fb12.shared0(P)
    fbld = fb12.FloatBuilder(C, E, nthreads=a.threads, shared=set(sh))
    fbld.pen = 3e-8
    rng = random.Random(a.seed)
    res = []
    for b in range(a.boxes):
        s = root_state(C, roots[a.root])
        E.set_pen(fbld.shared, fbld.pen)
        for d in range(a.descend):
            m = fbld.margin(s)
            if m >= 0 or s[1][M.Q - 1] < s[0][0]:
                break
            _, ax, md, x, y = fbld.decide(s, m, d)
            q, l, r = E.children(s, ax, md)
            worse_left = x <= y
            s = l if (rng.random() < a.worse) == worse_left else r
        tb = TB(C, ls, E, nthreads=a.threads, shared=set(sh))
        tb.pen = 3e-8
        tb.leaf_budget = a.budget
        out = Bits()
        t0 = time.time()
        E.set_pen(tb.shared, tb.pen)
        try:
            tb.node(s, out, 0)
            ok = True
        except RuntimeError as e:
            ok = str(e)[:80]
        secs = time.time() - t0
        st = dict(tb.stats); st.pop('margins')
        rep = None
        if ok is True:
            t1 = time.time()
            end = C.walkC(lambda pos: (out.v >> pos) & M.WMASK, 400, 0, s)
            rep = dict(ok=end == out.n, secs=time.time() - t1)
        r = dict(box=b, depth=d, done=ok, secs=secs, t_cert=tb.t_cert, t_scan=tb.t_scan, stats=st, replay=rep,
                 bits=out.n, leafbits_per_leaf=st['leafbits'] / max(1, st['leaves']))
        print(r, flush=True)
        res.append(r)
        pickle.dump(res, open(a.out, 'wb'))


if __name__ == '__main__':
    main()
