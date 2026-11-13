#!/usr/bin/env python3
"""Leaf-count measurement: roots of a Q-gap model built with the q9hs leaf options.

    python gen_treeshs.py MODEL.pkl PTS.pkl OUT.pkl [--half] [--var] [--roots 0,5,..]
        [--threads 3] [--pen 3e-8] [--leaf-budget N] [--shared-from A.pkl,B.pkl]

q9/gen_trees9.py with HSChecker (half-space multiplier records), LeafSolverHS and the q9hs
engine (eng_set_opts).  Every root starts from the same shared-anchor set (grid points x % 256 == 0
plus the anchors recorded in --shared-from), so per-root counts are comparable across option sets;
anchors found while building a root are not carried to the next root.  Every finished tree is
replayed exactly (HSChecker.walkC, variance leaves read the model's TB = hs.make_tb).
"""
import argparse
import ctypes
import itertools
import os
import pickle
import sys
import time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import hs                                    # noqa: E402
import qgen                                  # noqa: E402
from core import root_state                  # noqa: E402
import tables as T                           # noqa: E402
from leafhs import LeafSolverHS              # noqa: E402
from treehs import TreeBuilder2              # noqa: E402

LIB = os.path.join(HERE, 'cpp', 'libengine.dylib' if sys.platform == 'darwin' else 'libengine.so')


class EngineHS(qgen.Engine):
    def __init__(self, path, Q, NP):
        qgen.LIB = LIB             # qgen.Engine loads qgen.LIB: point it at the q9hs build
        super().__init__(path, Q, NP)
        self.lib.eng_set_opts.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_int, ctypes.c_void_p,
                                          ctypes.c_int, ctypes.c_double]

    def set_opts(self, half, var, tbf, VD):
        self._opts = (half, var, np.asarray(tbf, dtype=np.int64), VD)
        a = self._opts[2]
        self.lib.eng_set_opts(self.h, int(half), int(var), a.ctypes.data, len(a), float(VD))

    def set_half(self, on):
        half, var, a, VD = self._opts
        self.lib.eng_set_opts(self.h, int(on), int(var), a.ctypes.data, len(a), float(VD))


def roots_of(M):
    lens = [len([s for s in M.COV[r] if not s[2]]) for r in range(M.Q)]
    return list(itertools.product(*[range(n) for n in lens]))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('model'); ap.add_argument('pts'); ap.add_argument('out')
    ap.add_argument('--half', action='store_true')
    ap.add_argument('--var', action='store_true')
    ap.add_argument('--half-gate', action='store_true',
                    help='half-space row in the leaf gate and leaf certificates only; splits scored without it')
    ap.add_argument('--threads', type=int, default=3)
    ap.add_argument('--pen', type=float, default=3e-8)
    ap.add_argument('--roots', default=None)
    ap.add_argument('--leaf-budget', type=int, default=0)
    ap.add_argument('--shared-from', default='')
    a = ap.parse_args()
    M = pickle.load(open(a.model, 'rb'))
    C = hs.HSChecker(M)
    if a.half_gate:
        a.half = True
    C.half = a.half
    fields = hs.tb_fields(C)
    M.TBL = hs.pack_tb(fields)
    assert C.tbOk(M.TBL)
    tbf = [fields.get(i, 0) for i in range(M.KB // 256 + 1)]
    pts = pickle.load(open(a.pts, 'rb'))
    eng = a.out + '.eng'
    qgen.dump(M, C, pts, eng)
    E = EngineHS(eng, M.Q, M.NP)
    E.set_opts(a.half and not a.half_gate, a.var, tbf, M.VD)
    P = T.Points(C); P.cache = pts; P.frozen = True
    C.PT = P.pt
    ls = LeafSolverHS(C, P.pt, half=a.half, var=a.var)
    roots = roots_of(M)
    res = pickle.load(open(a.out, 'rb')) if os.path.exists(a.out) else {}
    shared0 = {x for x in pts if x % 256 == 0 and pts[x]}
    for f in [x for x in a.shared_from.split(',') if x]:
        for T0 in pickle.load(open(f, 'rb')).values():
            shared0 |= set(T0.get('anchors', ()))
    print('model Q %d NP %d, TB cells %d, shared anchors %d, half %s var %s half-gate %s'
          % (M.Q, M.NP, len(fields), len(shared0), a.half, a.var, a.half_gate), flush=True)
    ks = [int(x) for x in a.roots.split(',')] if a.roots else range(len(roots))
    for k in ks:
        if k in res:
            continue
        shared = set(shared0)
        tb = TreeBuilder2(C, ls, E, nthreads=a.threads, shared=shared)
        tb.pen = a.pen
        tb.halfgate = a.half_gate
        tb.leaf_budget = a.leaf_budget
        tb.progress = 500
        s = root_state(C, roots[k])
        t0 = time.time()
        try:
            bits = tb.build(s)
        except RuntimeError as e:
            st = dict(tb.stats)
            st.pop('margins')
            st['secs'] = time.time() - t0
            res[k] = dict(idx=roots[k], failed=str(e)[:200], stats=st, anchors=sorted(shared - shared0))
            print(k, roots[k], 'FAILED', str(e)[:200], st, flush=True)
            pickle.dump(res, open(a.out + '.tmp', 'wb'))
            os.replace(a.out + '.tmp', a.out)
            continue
        st = dict(tb.stats)
        mg = st.pop('margins')
        st['minmargin'] = min(mg) if mg else None
        t1 = time.time()
        end = C.walkC(lambda pos: (bits.v >> pos) & M.WMASK, 128, 1, s)
        st['replay_ok'] = end == bits.n
        st['replay_secs'] = time.time() - t1
        res[k] = dict(idx=roots[k], bits=bits.v, nbits=bits.n, stats=st, anchors=sorted(shared - shared0))
        pickle.dump(res, open(a.out + '.tmp', 'wb'))
        os.replace(a.out + '.tmp', a.out)
        print(k, roots[k], st, flush=True)


if __name__ == '__main__':
    main()
