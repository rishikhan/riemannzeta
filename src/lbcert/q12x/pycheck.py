#!/usr/bin/env python3
"""Independent exact check of xgen node files with the Python Z mirror (q9sparse zfmt.ZChecker).

    python pycheck.py MODEL.pkl PTS.pkl BOX NODES [--top] [--jobdir D] [--table T.lean.txt]

NODES is a tree file (or, with --jobdir, a frontier file whose J records are substituted by
D/job_<id>.nodes).  The node list is encoded as one Z stream (xio.zstream) and walked from BOX with the
Python checker against the generation table (PTS.pkl, maximal intervals) or against a final table
(rows x stored_word n).  Prints ok, leaves, failures, minimum margin and stream bits.
"""
import argparse
import os
import pickle
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xio                                    # noqa: E402


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('model'); ap.add_argument('pts'); ap.add_argument('box'); ap.add_argument('nodes')
    ap.add_argument('--jobdir', default=None)
    ap.add_argument('--table', default=None)
    a = ap.parse_args()
    M = pickle.load(open(a.model, 'rb'))
    Q, NP = M.Q, M.NP
    v = list(map(int, open(a.box).read().split()))
    s = (v[:Q], v[Q:2 * Q], v[2 * Q:2 * Q + NP], v[2 * Q + NP:])
    nodes = xio.assemble(a.nodes, a.jobdir) if a.jobdir else xio.read_nodes(a.nodes)
    Z = xio.ZW(M)
    if a.table:
        tab = {}
        for ln in open(a.table):
            x, w, n = map(int, ln.split())
            tab[x] = Z.pwD(x, w)
    else:
        P = pickle.load(open(a.pts, 'rb'))
        tab = xio.table_from_pts(Z, P)
    t0 = time.time()
    r = xio.walk(M, nodes, s, lambda x: tab.get(x, 0))
    r['secs'] = round(time.time() - t0, 2)
    print(r)
    sys.exit(0 if r['ok'] and r['fail'] == 0 else 1)


if __name__ == '__main__':
    main()
