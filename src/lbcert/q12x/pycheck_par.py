#!/usr/bin/env python3
"""Parallel pycheck of one assembled tree: the same exact Python walk (xio.walk, ZW = q9sparse zfmt.ZChecker)
as pycheck.py, split over a process pool.

    python pycheck_par.py MODEL PTS BOX TREE [--procs 128] [--parts 20000] [--table T.lean.txt] [--lowmem] [--fuel 400]

The tree (a node list, xio.read_nodes) is cut into subtrees of at most about leaves/parts leaves each.  The
skeleton above the cuts (split nodes only) is walked once with ZW.splitAx, which computes the state at every
cut from the root state with the checker's own split functions; at a cut the walk records the state and
continues at the cut subtree's end position.  Each cut subtree is then walked from its recorded state with
fuel FUEL - depth (--fuel, default 400), exactly as the whole-tree walk would reach it, in a worker process.  The tree passes when
the skeleton walk ends at the stream end, every subtree walk ends at its own end with no failed leaf, and the
leaf and reflection counts add up.  pycheck.py builds one stream of the whole tree, which takes too long at
1M leaves; this script never builds it.
"""
import argparse
import json
import os
import pickle
import sys
import time
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xio                                    # noqa: E402

FUEL = 400
G = {}                                        # shared with the forked workers


def node_len(nd, NT, AXB, PB, QB):
    """bit length of one node in the stream (xio.zstream)"""
    if nd[0] == 'S':
        return 4 + AXB
    if nd[0] == 'R':
        return 1
    o = 1 + NT
    for (n, z, jp, p, jr, r, lam) in nd[1]:
        o += 3
        if z != 0:
            o += 7
        if z == 3:
            o += 7
        if z in (2, 3) or z >= 4:
            o += 10
    return o + len(nd[2]) * (2 + PB + QB) + 1


def part(job):
    """xio.walk on nodes[i:j] from state st, with one ZW per worker process"""
    i, j, st, depth = job
    M = G['M']
    Z = G.get('Z')
    if Z is None:
        tab = G['tab']
        Z = G['Z'] = xio.ZW(M)
        Z.PT = lambda x: tab.get(x, 0)
    if 'lines' in G:
        bits, e_exp = xio.zstream_lines(G['lines'][i:j], len(M.TS), Z.AXB, M.NP.bit_length(), M.QB)
    else:
        bits, e_exp = xio.zstream(G['nodes'][i:j], len(M.TS), Z.AXB, M.NP.bit_length(), M.QB)
    rec = dict(leaves=0, refl=0, margins=[], fail=[], splits=0, split_axes={}, split_modes={}, depths=[], var=0)
    e = Z.walkC(lambda p: (bits >> p) & M.WMASK, FUEL - depth, 1, st, rec=rec)
    mm = min([m for m in rec['margins'] if m is not None], default=None)
    return dict(i=i, ok=(e == e_exp), leaves=rec['leaves'], refl=rec['refl'], fail=len(rec['fail']),
                minmargin=None if mm is None else str(mm))


def main():
    global FUEL
    ap = argparse.ArgumentParser()
    ap.add_argument('model'); ap.add_argument('pts'); ap.add_argument('box'); ap.add_argument('nodes')
    ap.add_argument('--procs', type=int, default=128)
    ap.add_argument('--parts', type=int, default=20000)
    ap.add_argument('--table', default=None, help='final table rows "x word n" (table.lean.txt) instead of PTS')
    ap.add_argument('--lowmem', action='store_true', help='keep the node lines as text and parse each part in its '
                    'worker (xsplit: states from the split records only); the same checks with far less memory')
    ap.add_argument('--fuel', type=int, default=FUEL, help='walk fuel from the root (default 400)')
    a = ap.parse_args()
    FUEL = a.fuel
    t0 = time.time()
    M = pickle.load(open(a.model, 'rb'))
    Q, NP = M.Q, M.NP
    v = list(map(int, open(a.box).read().split()))
    s0 = (v[:Q], v[Q:2 * Q], v[2 * Q:2 * Q + NP], v[2 * Q + NP:])
    Z = xio.ZW(M)
    if a.table:
        tab = {}
        for ln in open(a.table):
            x, w, _ = map(int, ln.split())
            tab[x] = Z.pwD(x, w)
    else:
        tab = xio.table_from_pts(Z, pickle.load(open(a.pts, 'rb')))
    if a.lowmem:
        return lowmem(a, M, s0, tab, t0)
    nodes = xio.read_nodes(a.nodes)
    NT, AXB, PB, QB = len(M.TS), xio.fb12.axis_bits(M), M.NP.bit_length(), M.QB
    assert AXB == Z.AXB
    n = len(nodes)
    # preorder positions, subtree ends and leaf counts (iteratively)
    pos = [0] * (n + 1)
    pos[0] = 1
    for k, nd in enumerate(nodes):
        if nd[0] == 'J':
            raise ValueError('unassembled J record at node %d' % k)
        pos[k + 1] = pos[k] + node_len(nd, NT, AXB, PB, QB)
    end = [0] * n                             # index after the subtree of node k
    nleaf = [0] * n
    stack = []                                # [index, children still to see]
    for k, nd in enumerate(nodes):
        if nd[0] == 'S':
            stack.append([k, 2])
            continue
        e, c = k + 1, 1
        end[k], nleaf[k] = e, c
        while stack:
            top = stack[-1]
            top[1] -= 1
            nleaf[top[0]] += c
            if top[1] > 0:
                break
            stack.pop()
            end[top[0]] = e
            c = nleaf[top[0]]
    if stack or end[0] != n:
        print(json.dumps(dict(ok=False, why='structure', nodes=n)))
        sys.exit(1)
    tot = nleaf[0]
    lim = max(1, tot // a.parts)
    # cuts: maximal subtrees with at most lim leaves (or a single leaf)
    cuts = {}                                 # stream position -> (node index, depth)
    st = [(0, 0)]
    while st:
        k, d = st.pop()
        if nodes[k][0] != 'S' or nleaf[k] <= lim:
            cuts[pos[k]] = (k, d)
            continue
        st.append((end[k + 1], d + 1))        # right child (popped after the left)
        st.append((k + 1, d + 1))
    # skeleton walk: the checker's split functions compute the state at each cut
    words = {pos[k]: 1 | (nodes[k][1] << 1) | (nodes[k][2] << (1 + AXB)) for k in range(n) if nodes[k][0] == 'S'}
    states = {}

    class Skel(xio.ZW):
        def walkC(self, bits, fuel, p, s, cuts_=None, rec=None, depth=0):
            if fuel == 0:
                return 0
            if p in cuts:
                states[p] = (s, depth)
                return pos[end[cuts[p][0]]]
            if p not in words:
                return 0                      # a leaf outside every cut: cannot happen
            return super().walkC(bits, fuel, p, s, cuts_, rec, depth)

    sk = Skel(M)
    sk.PT = lambda x: tab.get(x, 0)
    e = sk.walkC(lambda p: words.get(p, 0) & M.WMASK, FUEL, 1, s0, rec=None)
    skel_ok = e == pos[n] and len(states) == len(cuts)
    for p, (k, d) in cuts.items():
        if p in states and states[p][1] != d:
            skel_ok = False
    t_prep = time.time() - t0
    G.update(M=M, nodes=nodes, tab=tab)
    jobs = sorted(((cuts[p][0], end[cuts[p][0]], states[p][0], states[p][1]) for p in states),
                  key=lambda x: -(x[1] - x[0]))
    res = []
    with Pool(a.procs) as pool:
        for r in pool.imap_unordered(part, jobs, chunksize=1):
            res.append(r)
    ok = skel_ok and all(r['ok'] and r['fail'] == 0 for r in res)
    leaves = sum(r['leaves'] for r in res)
    refl = sum(r['refl'] for r in res)
    mm = [int(r['minmargin']) for r in res if r['minmargin'] is not None]
    out = dict(ok=ok, skeleton_ok=skel_ok, end=e, expect=pos[n], parts=len(jobs), leaves=leaves, refl=refl,
               tree_leaves=tot, fail=sum(r['fail'] for r in res), bad_parts=sum(1 for r in res if not r['ok']),
               minmargin=str(min(mm)) if mm else None, max_part=max(j[1] - j[0] for j in jobs),
               prep_secs=round(t_prep, 1), secs=round(time.time() - t0, 1))
    ok = ok and leaves + refl == tot
    out['ok'] = ok
    print(json.dumps(out))
    sys.exit(0 if ok else 1)


def lowmem(a, M, s0, tab, t0):
    import xsplit
    lines = [ln.rstrip('\n') for ln in open(a.nodes) if ln.strip() and ln[0] != '#']
    if any(ln[0] == 'J' for ln in lines):
        print(json.dumps(dict(ok=False, why='unassembled J record')))
        sys.exit(1)
    try:
        end, nleaf = xsplit.structure(lines)
    except ValueError:
        print(json.dumps(dict(ok=False, why='structure', nodes=len(lines))))
        sys.exit(1)
    tot = nleaf[0] + sum(1 for ln in lines if ln[0] == 'R')    # leaves and reflections, as tree_leaves above
    cuts, flat = xsplit.parts(M, s0, lines, max(1, nleaf[0] // a.parts))
    Q, NP = M.Q, M.NP
    G.update(M=M, lines=lines, tab=tab)
    jobs = sorted(((i, j, (f[:Q], f[Q:2 * Q], f[2 * Q:2 * Q + NP], f[2 * Q + NP:]), d)
                   for (i, j, d), f in ((c, flat[c[0]]) for c in cuts)), key=lambda x: -(x[1] - x[0]))
    t_prep = time.time() - t0
    res = []
    with Pool(a.procs) as pool:
        for r in pool.imap_unordered(part, jobs, chunksize=1):
            res.append(r)
    ok = all(r['ok'] and r['fail'] == 0 for r in res)
    leaves = sum(r['leaves'] for r in res)
    refl = sum(r['refl'] for r in res)
    mm = [int(r['minmargin']) for r in res if r['minmargin'] is not None]
    out = dict(ok=ok, skeleton_ok=True, parts=len(jobs), leaves=leaves, refl=refl, tree_leaves=tot,
               fail=sum(r['fail'] for r in res), bad_parts=sum(1 for r in res if not r['ok']),
               minmargin=str(min(mm)) if mm else None, max_part=max(j[1] - j[0] for j in jobs),
               prep_secs=round(t_prep, 1), secs=round(time.time() - t0, 1), lowmem=True)
    ok = ok and leaves + refl == tot
    out['ok'] = ok
    print(json.dumps(out))
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
