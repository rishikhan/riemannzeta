#!/usr/bin/env python3
"""Q-gap Lean certificate (written for Q = 12, used for Q = 10, 11, 12) as a Lake library of many modules (no
single-file limit).

    python gen12.py BASE.lean MODEL.pkl PTS.pkl OUTDIR (--trees ZT.pkl | --subtrees ZS.pkl)
        [--ptn TABLE] [--cut-leaves 400] [--module-leaves 8000] [--no-skip] [--date D] [--lib Q12]

BASE: the 16-harmonic base q9lean/work/w16_v3.lean (a file derived from attempt-031, after a structural edit to 16 window
harmonics) with the window patched by w16/regen_window.py.  The instance module, the leaf check and the tail
come from q9lean (geninst.py, gen9.py) with the options of the q = 9 entry (gsplit, yrow, helpers, notn, adjlam,
sparse, leaf2=ypbS, ptb, q9fixed's patch); the
changes for Q = 12 are in Inst12 below.  Output, under OUTDIR/<lib>/:

  Base.lean     every notice, the imports, the analysis and window part, the instance module (checker and its
                soundness), the tables (pyramids, REG, the tangent point tree PTB) and the root cover COV / RC.
  C/M<i>.lean   data modules: each holds a group of cut subtrees; per subtree its walk words (WLc<k>_<j>, re-based
                to start at position 0), its start state CSc<k>, the walk theorem wcsc<k> (decide +kernel) and
                ccsc<k> : Covered (toCl CSc<k>).  They import only Base, so `lake build` checks them in parallel.
  Final.lean    imports every data module; per root the skeleton walk (root stream with the cut subtrees zeroed,
                cuts CUTS<r> = the imported states and theorems) rc<r>; run, cert, the reflection step, the weights,
                Opeth.AMFinal and the candidate theorems.
  Simple.lean   (not in a TEST) imports Final; the N0simple forms of the final theorems (simple12.lean.in with this
                certificate's κ, H_W floor, c and B).
  <lib>.lean    imports Simple (Final in a TEST).

--trees ZT.pkl: {root k: {'idx': idx, 'bits': Z stream from position 1, 'nbits': end}} (a complete root cover).
Roots missing from --trees make the output a TEST (MissOK hypothesis for every root box; the roots given are still
    proved and used in run's case split).
--subtrees ZS.pkl: TEST ONLY: [{'s': state, 'bits': Z stream from position 0, 'nbits': n}]: each subtree gets its
    ccsc theorem, and every root box is a hypothesis (MissOK) of cert and the theorems after it.
--no-skip: leave out `set_option debug.skipKernelTC true` (a plain `lake build` then kernel-checks everything).
--fast: walk the root streams for their structure only (split states, leaf lengths from the payload) without the
    exact leaf check, which takes hours at 10^6 leaves; the trees must already pass q12x's two checkers against the
    same table (finalize.py), and the table words are the whole --ptn table.  Stream reads are windowed, so a root
    stream of 10^9 bits costs linear time.
--super-leaves S (with --fast): two cut levels and compact skeletons.  Level 1 is the cut subtrees as before; level
    2 takes the maximal subtrees of more than --cut-leaves and at most S leaves.  A level-2 cut is walked with
    walkCutR over its level-1 cuts (covered_of_walkCutR) in the data module that holds its level-1 cuts, and the
    root skeletons in Final walk over the level-2 cuts and the remaining level-1 cuts.  In every skeleton stream
    (level-2 cuts and roots) each cut subtree is replaced by one placeholder bit, and its cut entry is (p, state,
    p + 1); cutAt answers at p before the walk reads the bit.  A data module never splits a level-2 cut from its
    level-1 cuts.  Without the option the output is unchanged.
"""
import argparse
import itertools
import os
import pickle
import re
import sys
from fractions import Fraction

sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('q9lean', 'gen', 'q9', 'q9hs', 'q12', 'q9sparse', 'q9enc', 'q9fixed', os.path.join('q9lean', 'dead')):
    sys.path.insert(0, os.path.join(LB, d))
import geninst                                  # noqa: E402
import gen9                                     # noqa: E402
import emit                                     # noqa: E402

SA = gen9.SA
W40 = gen9.W40
OPEN = 'open AMW.Cert AMW.Cert.Pyr AMW.Cert.PyrD AMW.Cert.PCell AMW.Cert.PC9XA'
SKIP = ('-- The build skips its own kernel check; nanoda and the Lean kernel replay of the export check every declaration.\n'
        'set_option debug.skipKernelTC true\n')


# ------------------------------------------------------------------ instance for Q gaps with an AXB-bit axis field
class Inst12(geninst.Inst):
    """geninst.Inst with (a) the split word 1 + AXB + 3 bits, children at pos + 4 + AXB (AXB = 7 for 78 slots),
    (b) the prefix sums x_ij / y_ij of every pair (ycs of lever y reads x_ij of all pairs, also those whose
    term weight is zero)."""

    RESERVED = {'by', 'do', 'if', 'in', 'fi', 'at', 'ee', 'kk', 'ax', 'md', 'qb', 'ih', 'pp', 'qe', 'qf', 'pb', 'lo', 'hi'}

    def __init__(self, spec):
        super().__init__(spec)
        self.AXB = (self.Q + self.NP - 1).bit_length()
        # binder names of the state: q9's list reaches the two-letter names 'ee' (rowK's parameter) and 'ax' at
        # 157 fields, which would shadow parameters; skip every name the generated code uses as a parameter
        one = [c for c in 'abcdefghijlmnorstuvwxyz'] + [c for c in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ']
        two = [f + t for f in 'abcdefgh' for t in 'abcdefghijlmnoruvwxyz' if f + t not in self.RESERVED]
        self.V = (one + two)[:self.NF]
        assert len(self.V) == self.NF

    def helper_defs(self):
        L = []
        need = sorted({(t[0], j) for t in self.TS for j in range(t[0] + 2, t[1] + 1)}
                      | {(i, k) for (i, j) in self.PR for k in range(i + 2, j + 1)})
        for (i, j) in need:
            for v, f in (('x', 'l'), ('y', 'u')):
                prev = 's.%s%d' % (f, i) if j == i + 2 else '(%s%d%d s)' % (v, i, j - 1)
                L.append('def %s%d%d (s : St) : ℕ := Nat.add %s s.%s%d' % (v, i, j, prev, f, j - 1))
        for t in self.TS:
            i, j = t[0], t[1]
            if j > i + 1:
                L.append('def e%d%d (s : St) : ℕ := nmax s.A%d%d (x%d%d s)' % (i, j, i, j, i, j))
                L.append('def f%d%d (s : St) : ℕ := nmin s.B%d%d (y%d%d s)' % (i, j, i, j, i, j))
        for t in self.TS:
            L.append('def a%d%d : ℕ := %d' % (t[0], t[1], t[2]))
        return L

    def walk_rest(self, *a):
        L = super().walk_rest(*a)
        old = ('    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) 7) 7) (Nat.add pos 10) '
               '(Nat.land (Nat.shiftRight (bits pos) 1) 63))')
        new = ('    (splitAx ih (Nat.land (Nat.shiftRight (bits pos) %d) 7) (Nat.add pos %d) '
               '(Nat.land (Nat.shiftRight (bits pos) 1) %d))' % (1 + self.AXB, 4 + self.AXB, (1 << self.AXB) - 1))
        assert L.count(old) == 1
        return [new if x == old else x for x in L]


# ------------------------------------------------------------------ Z-stream walker (exact mirror, AXB-bit split word)
class Walker:
    def __init__(self, M, P):
        import fb12
        import zfmt
        import exact12
        self.M, self.fb12 = M, fb12
        self.AXB = fb12.axis_bits(M)
        self.H = exact12.HSCheckerW(M)
        self.H.half = True
        self.Z = zfmt.ZChecker(M)
        self.Z.PT = lambda x: self.Z.pwD(x, P[x]) if P.get(x) else 0

    def walk(self, bits, pos, s):
        """-> (end, leaves, refl, anchors, nodes [(pos, s, end, leaves, depth)])"""
        M, AXB = self.M, self.AXB
        st = dict(leaves=0, refl=0, anchors=set(), nodes=[])

        def rec(pos, s, depth):
            w = (bits >> pos) & M.WMASK
            if w & 1:
                ax = (w >> 1) & ((1 << AXB) - 1)
                md = (w >> (1 + AXB)) & 7
                assert ax < M.Q + M.NP
                q, left, right = self.fb12.children(self.H, s, ax, md)
                n0 = st['leaves']
                p = rec(pos + 4 + AXB, left, depth + 1)
                e = rec(p, right, depth + 1)
                st['nodes'].append((pos, s, e, st['leaves'] - n0, depth))
                return e
            if s[1][M.Q - 1] < s[0][0]:
                st['refl'] += 1
                return pos + 1
            n, margin, nt = self.Z.zleaf(w >> 1, s, anchors=st['anchors'])
            assert n, ('leaf fails', pos)
            st['leaves'] += 1
            return pos + 1 + n
        e = rec(pos, s, 0)
        return e, st


class FastWalker:
    """structure-only walk of a Z stream: the split states from the checker's split functions (fb12.children,
    as Walker), leaf lengths from the payload layout (FORMAT.md), no leaf check; windowed reads of the stream"""

    def __init__(self, M):
        import fb12
        import exact12
        self.M, self.fb12 = M, fb12
        self.AXB = fb12.axis_bits(M)
        self.H = exact12.HSCheckerW(M)
        self.H.half = True
        self.NT, self.REC = len(M.TS), 2 + M.NP.bit_length() + M.QB

    def load(self, bits, nbits):
        self.buf = bits.to_bytes((nbits + 7) // 8 + 160, 'little')

    def word(self, pos):
        i = pos >> 3
        return (int.from_bytes(self.buf[i:i + 130], 'little') >> (pos & 7)) & self.M.WMASK

    def extract(self, a, b):
        """bits [a, b) of the loaded stream, re-based to 0"""
        if b <= a:
            return 0
        return (int.from_bytes(self.buf[a >> 3:(b >> 3) + 1], 'little') >> (a & 7)) & ((1 << (b - a)) - 1)

    def leaf_len(self, x):
        NT = self.NT
        o = NT
        for _ in range(bin(x & ((1 << NT) - 1)).count('1')):
            z = (x >> o) & 7
            o += 3
            if z != 0:
                o += 7
            if z == 3:
                o += 7
            if z in (2, 3) or z >= 4:
                o += 10
        while (x >> o) & 1:
            o += self.REC
        return o + 1

    def step(self, pos, s):
        """-> ('S', left pos, left, right) | ('R', next) | ('L', next)"""
        M, AXB = self.M, self.AXB
        w = self.word(pos)
        if w & 1:
            ax = (w >> 1) & ((1 << AXB) - 1)
            md = (w >> (1 + AXB)) & 7
            assert ax < M.Q + M.NP
            q, left, right = self.fb12.children(self.H, s, ax, md)
            return 'S', pos + 4 + AXB, left, right
        if s[1][M.Q - 1] < s[0][0]:
            return 'R', pos + 1
        return 'L', pos + 1 + self.leaf_len(w >> 1)

    def walk1(self, pos, s):
        """-> (end, leaves, refl, nodes): nodes [(pos, end, leaves, depth, max depth below)] of the splits, postorder"""
        st = [0, 0]
        nodes = []

        def rec(pos, s, depth):
            r = self.step(pos, s)
            if r[0] == 'S':
                n0 = st[0]
                p, m1 = rec(r[1], r[2], depth + 1)
                e, m2 = rec(p, r[3], depth + 1)
                nodes.append((pos, e, st[0] - n0, depth, max(m1, m2)))
                return e, max(m1, m2)
            st[0 if r[0] == 'L' else 1] += 1
            return r[1], depth
        e, _ = rec(pos, s, 0)
        return e, st[0], st[1], nodes

    def walk2(self, pos, s, want, skip, pieces):
        """states at the positions in `want`; the subtrees at the positions in `skip` (pos -> end) are jumped over.
        pieces: {piece root pos: max depth reached below it, relative} for the root (key `pos`) and every position
        in `want` that is not in `skip`"""
        states = {}

        def rec(pos, s, depth, base, bp):
            if pos in want:
                states[pos] = s
                if pos != bp:
                    pieces[bp] = max(pieces.get(bp, 0), depth - base)
                if pos in skip:
                    return skip[pos]
                base, bp = depth, pos
            pieces[bp] = max(pieces.get(bp, 0), depth - base)
            r = self.step(pos, s)
            if r[0] == 'S':
                p = rec(r[1], r[2], depth + 1, base, bp)
                return rec(p, r[3], depth + 1, base, bp)
            return r[1]
        e = rec(pos, s, 0, 0, pos)
        return e, states


def greedy(cands, rem, lim):
    """gen12's cut choice (largest first, no overlap, until at most lim leaves remain) on [(pos, end, leaves, ...)];
    the overlap test uses the sorted starts of the chosen (disjoint) intervals"""
    import bisect
    chosen, starts, ends = [], [], []
    for n in sorted(cands, key=lambda n: -n[2]):
        if rem <= lim:
            break
        pos, ce = n[0], n[1]
        i = bisect.bisect_left(starts, ce) - 1
        if i >= 0 and ends[i] > pos:
            continue
        starts.insert(i + 1, pos)
        ends.insert(i + 1, ce)
        chosen.append(n)
        rem -= n[2]
    return chosen, rem


class BitAcc:
    """append-only bit string (linear time)"""

    def __init__(self, n0=0):
        self.out, self.acc, self.na, self.done = bytearray(), 0, n0, 0

    def put(self, v, n):
        self.acc |= v << self.na
        self.na += n
        if self.na >= 1 << 18:
            self.out += (self.acc & ((1 << (1 << 18)) - 1)).to_bytes(1 << 15, 'little')
            self.acc >>= 1 << 18
            self.na -= 1 << 18
            self.done += 1 << 18

    @property
    def n(self):
        return self.done + self.na

    def value(self):
        return int.from_bytes(bytes(self.out) + self.acc.to_bytes((self.na + 7) // 8, 'little'), 'little')


def compact(FW, a, b, kids, n0):
    """stream [a, b) of the loaded root stream with each kid (p, e, k) replaced by one 0 bit, starting at position
    n0 -> (bits, end, entries [(p', k, p' + 1)])"""
    acc = BitAcc(n0)
    ents = []
    cur = a
    for (p, e, k) in kids:
        acc.put(FW.extract(cur, p), p - cur)
        ents.append((acc.n, k, acc.n + 1))
        acc.put(0, 1)
        cur = e
    acc.put(FW.extract(cur, b), b - cur)
    return acc.value(), acc.n, ents


def nest_select(nodes, c1, c2, T):
    """--nest-leaves T: inside each level-2 cut whose own walk has more than T leaves (leaves outside its level-1
    cuts), nested level-2 cuts, chosen bottom-up: a split node outside every level-1 cut becomes a nested cut when
    the leaves its own walk would have exceed T // 2, so every walk keeps at most T leaves.
    -> ({level-2 start: own leaves after nesting}, [(pos, end, own leaves)] of the nested cuts)"""
    import bisect
    s1 = [n[0] for n in c1]
    e1 = [n[1] for n in c1]
    pre = [0]
    for n in c1:
        pre.append(pre[-1] + n[2])

    def own(pos, end):                          # leaves of [pos, end) outside the level-1 cuts inside it
        return pre[bisect.bisect_left(s1, end)] - pre[bisect.bisect_left(s1, pos)]
    s2 = [n[0] for n in c2]
    big = {}
    for n in c2:
        o = n[2] - own(n[0], n[1])
        if o > T:
            big[n[0]] = (n, o)
    cand = {p: [] for p in big}
    for m in nodes:
        i = bisect.bisect_right(s2, m[0]) - 1
        if i < 0 or s2[i] not in big or m[0] == s2[i] or m[0] >= c2[i][1]:
            continue
        j = bisect.bisect_right(s1, m[0]) - 1
        if j >= 0 and m[0] < e1[j]:
            continue                            # inside (or at) a level-1 cut
        cand[s2[i]].append(m)
    tops, nested = {}, []
    for p, (n, o) in big.items():
        mx = []                                 # maximal chosen nested cuts so far, ascending start: (pos, end, own)
        for m in sorted(cand[p], key=lambda m: -m[0]):
            om = m[2] - own(m[0], m[1])
            i = 0
            while i < len(mx) and mx[i][0] < m[1]:
                i += 1
            r = om - sum(x[2] for x in mx[:i])
            if r > T // 2:
                nested.append((m[0], m[1], r))
                mx[:i] = [(m[0], m[1], om)]
        tops[p] = o - sum(x[2] for x in mx)
    # `own` of a nested cut above is its residual walk; mx keeps its full own count for its parents' residuals
    return tops, sorted(nested)


def plan_root(FW, T, s0, cut_leaves, super_leaves, k0, nest_leaves=0):
    """--fast cuts of one root.  -> (cuts [(k, flat, stream, nbits, leaves, unit, kids)], skel, leaves, refl):
    level-1 cuts have kids None; a level-2 cut has its compact stream and kids [(p', k, p' + 1)], and its `leaves`
    are the leaves its own skeleton walks.  skel = (stream, end, entries, leaves walked by the skeleton).
    nest_leaves: nested level-2 cuts inside the larger level-2 cuts (nest_select); a nested cut is a level-2 cut
    whose kids are level-1 cuts and nested cuts."""
    FW.load(T['bits'], T['nbits'])
    e, leaves, refl, nodes = FW.walk1(1, s0)
    assert e == T['nbits'], (e, T['nbits'])
    rem = leaves
    c1 = []
    if rem > cut_leaves:
        c1, rem = greedy([n for n in nodes if n[3] >= 1 and n[2] <= cut_leaves], rem, cut_leaves)
    c2 = []
    if super_leaves and leaves > super_leaves:
        c2, _ = greedy([n for n in nodes if n[3] >= 1 and cut_leaves < n[2] <= super_leaves], leaves + 1, -1)
    c1.sort()
    c2.sort()
    tops, nested = nest_select(nodes, c1, c2, nest_leaves) if nest_leaves else ({}, [])
    del nodes
    want = {n[0] for n in c1} | {n[0] for n in c2} | {x[0] for x in nested}
    skip = {n[0]: n[1] for n in c1}
    pieces = {}
    e2, states = FW.walk2(1, s0, want, skip, pieces)
    assert e2 == T['nbits']
    for n in c1:
        pieces[('in', n[0])] = n[4] - n[3]
    # fuel: 128 as before; a walk that goes deeper gets fuel 400, and beyond 399 levels fuel 512.  The root
    # skeleton walks of rcOfC have 128; a deeper root skeleton gets Final's rcOfCF<fuel> (rcOfC with that fuel)
    assert max(pieces.values()) <= 511, ('walk depth beyond fuel 512', max(pieces.values()))

    def fuel(key):
        d = pieces.get(key, 0)
        return 128 if d <= 127 else 400 if d <= 399 else 512
    flat = {p: FW.H.st_flat(s) for p, s in states.items()}
    # level-1 cuts inside each level-2 cut
    inner = {n[0]: [] for n in c2}
    top1 = []
    import bisect
    st2 = [n[0] for n in c2]
    for n in c1:
        i = bisect.bisect_right(st2, n[0]) - 1
        if i >= 0 and n[0] < c2[i][1]:
            inner[c2[i][0]].append(n)
        else:
            top1.append(n)
    cuts = []
    k = k0
    unit = 0
    top = []                                    # (pos, end, k) of the root skeleton's entries
    items = sorted([(n[0], 1, n) for n in top1] + [(n[0], 2, n) for n in c2])
    nst = [x[0] for x in nested]

    def compound(pos, end, own, inner1):
        """a level-2 cut [pos, end) with `own` leaves in its walk; inner1: the level-1 cuts inside it.  The nested
        cuts inside it are emitted first (each with the cuts inside it), so the cut list is in postorder."""
        nonlocal k
        a = bisect.bisect_right(nst, pos)
        b = bisect.bisect_left(nst, end)
        its = sorted([(m[0], 1, m) for m in inner1] + [(x[0], 3, x) for x in nested[a:b]])
        kids = []
        i = 0
        while i < len(its):
            _, typ, x = its[i]
            if typ == 1:
                cuts.append((k, flat[x[0]], FW.extract(x[0], x[1]), x[1] - x[0], x[2], unit, None, fuel(('in', x[0]))))
                kids.append((x[0], x[1], k))
                k += 1
                i += 1
            else:
                j = i + 1
                while j < len(its) and its[j][0] < x[1]:
                    j += 1
                kk = compound(x[0], x[1], x[2], [y[2] for y in its[i + 1:j] if y[1] == 1])
                kids.append((x[0], x[1], kk))
                i = j
        zs, e_, ents = compact(FW, pos, end, kids, 0)
        cuts.append((k, flat[pos], zs, e_, own, unit, ents, fuel(pos)))
        k += 1
        return k - 1
    for _, lev, n in items:
        if lev == 1:
            cuts.append((k, flat[n[0]], FW.extract(n[0], n[1]), n[1] - n[0], n[2], unit, None, fuel(('in', n[0]))))
            top.append((n[0], n[1], k))
            k += 1
        elif n[0] in tops:
            kk = compound(n[0], n[1], tops[n[0]], inner[n[0]])
            top.append((n[0], n[1], kk))
        else:
            kids = []
            for m in inner[n[0]]:
                cuts.append((k, flat[m[0]], FW.extract(m[0], m[1]), m[1] - m[0], m[2], unit, None, fuel(('in', m[0]))))
                kids.append((m[0], m[1], k))
                k += 1
            zs, end, ents = compact(FW, n[0], n[1], kids, 0)
            own = n[2] - sum(m[2] for m in inner[n[0]])
            cuts.append((k, flat[n[0]], zs, end, own, unit, ents, fuel(n[0])))
            top.append((n[0], n[1], k))
            k += 1
        unit += 1
    zs, end, ents = compact(FW, 1, T['nbits'], top, 1)
    srem = leaves - sum(n[2] for n in top1) - sum(n[2] for n in c2)
    return cuts, (zs, end, ents, srem, fuel(1)), leaves, refl


_PLAN = {}                                      # shared with forked workers (--procs)


def _plan(r):
    import fb12
    G = _PLAN
    return plan_root(G['FW'], G['trees'][r], fb12.root_state(G['FW'].H, G['roots'][r]), G['a'].cut_leaves,
                     G['a'].super_leaves, 0, G['a'].nest_leaves)


def rcofc_fuel(Q, fu):
    """rcOfC (gen9's base theorem) with root skeleton walk fuel fu instead of 128, for a deep root skeleton"""
    iv = gen9.gvars(Q, 'i')
    ivs = ' '.join('i%d' % r for r in range(Q))
    return ['theorem rcOfCF%d {%s : ℕ} (wb : ℕ → ℕ) (cuts : List (ℕ × St × ℕ)) (hc : CutsOk cuts) (e : ℕ)' % (fu, iv),
            '    (h : U (walkCutR TOP BK TOPD BKD PT REG wb cuts %d 1) (ofCl (RC %s) 0) = e) (he : e ≠ 0) : Covered (RC %s) := by'
            % (fu, ivs, ivs),
            '  have h\' := covered_of_walkCutR lbS lbD ptS hR wb hc %d 1 e _ h he' % fu,
            '  rwa [toCl_ofCl _ _ rfl rfl rfl rfl] at h\'']


def super_text(k, s_flat, stream, nbits, extra, ents, fuel=128):
    """a level-2 cut: compact stream, its cut list over level-1 cuts of the same module, walkCutR theorem"""
    L, wd = wl_defs('WLc%d' % k, stream, nbits, extra)
    L.append('def CSc%d : St := %s' % (k, emit.st_text(s_flat)))
    L.append('def CUTSc%d : List (ℕ × St × ℕ) := [%s]' % (k, ', '.join('(%d, CSc%d, %d)' % (p, j, ce) for (p, j, ce) in ents)))
    oks = 'cutsOk_nil'
    for (p, j, ce) in reversed(ents):
        oks = '(cutsOk_cons ccsc%d %s)' % (j, oks)
    L.append('theorem wcsc%d : U (walkCutR TOP BK TOPD BKD PT REG %s CUTSc%d %d 0) CSc%d = %d := by' % (k, wd, k, fuel, k, nbits))
    L.append('  decide +kernel')
    L.append('theorem ccsc%d : Covered (toCl CSc%d) :=' % (k, k))
    L.append('  covered_of_walkCutR lbS lbD ptS hR %s %s %d 0 %d _ wcsc%d (by decide)' % (wd, oks, fuel, nbits, k))
    return L


# ------------------------------------------------------------------ text pieces
def ptb_checker():
    """q9leaf2/lean/PTB.lean without its zfPTB macro (the trees are written out)"""
    t = open(os.path.join(LB, 'q9leaf2', 'lean', 'PTB.lean')).read()
    i = t.index('namespace PackDec')
    return t[:i].rstrip('\n')


def ptb_tree(E):
    """balanced PTB text over entries [(x, word with n - 1 above bit 140)] (PackDec.ptbTree in Python)"""
    def rec(a, b):
        if b <= a + 1:
            x, w = E[a]
            v = w % (1 << 140)
            g = v % (1 << 96) + ((x - (v >> 96) % (1 << 20)) << 96) + ((x + (v >> 116)) << 120)
            return '(.lf %d %d %d)' % (x, g, w >> 140)
        m = a + (b - a) // 2
        return '(.nd %d %s %s)' % (E[m][0], rec(a, m), rec(m, b))
    return rec(0, len(E))


def emit_table(words, part_pts=600):
    """words {x: word | (n - 1) << 140}: parts PTT_i (balanced trees), their checks, the top tree, PT and ptS"""
    E = sorted(words.items())
    np_ = max(1, (len(E) + part_pts - 1) // part_pts)
    chunks = [E[i * len(E) // np_:(i + 1) * len(E) // np_] for i in range(np_)]
    L = []
    for i, ch in enumerate(chunks):
        L.append('def PTT_%d : PTB := %s' % (i, ptb_tree(ch)))
        L.append('theorem PTT_%d_ok : ptOkB REG TOP BK TOPD BKD 4 PTT_%d = true := by decide +kernel' % (i, i))

    def top(a, b):
        if b - a == 1:
            return 'PTT_%d' % a, 'PTT_%d_ok' % a
        m = (a + b) // 2
        l, lp = top(a, m)
        r, rp = top(m, b)
        return '(.nd %d %s %s)' % (chunks[m][0][0], l, r), '(ptOkB_nd %s %s)' % (lp, rp)
    t, p = top(0, np_)
    L.append('def PTT : PTB := %s' % t)
    L.append('theorem PTT_ok : ptOkB REG TOP BK TOPD BKD 4 PTT = true := %s' % p)
    L.append('def PT (x : ℕ) : ℕ := ptGetB PTT x')
    L.append('theorem ptS : ∀ x, PVI x (PT x) := ptTB_sound (csh := 4) lbS lbD hR PTT PTT_ok')
    return L


def wl_defs(name, stream, nbits, extra):
    """walk-word blocks and the dispatch of one stream -> (lines, WD name)"""
    L = []
    blocks = emit.wl_blocks(stream, nbits, extra=extra)
    keys = [j for j in range(len(blocks)) if blocks[j]]
    for j in keys:
        L.append('def %s_%d : ℕ := %s' % (name, j, emit.zf(blocks[j])))
    L += emit.dispatch(name, keys, lambda j: '%s_%d' % (name, j), name)
    L.append('def WD%s : ℕ → ℕ := rdw %s' % (name, name))
    return L, 'WD' + name


def cut_text(k, s_flat, stream, nbits, extra, fuel=128):
    """one cut subtree, re-based to position 0: walk words, state, walk theorem, covered theorem"""
    L, wd = wl_defs('WLc%d' % k, stream, nbits, extra)
    L.append('def CSc%d : St := %s' % (k, emit.st_text(s_flat)))
    L.append('theorem wcsc%d : U (walkC TOP BK TOPD BKD PT REG %s %d 0) CSc%d = %d := by' % (k, wd, fuel, k, nbits))
    L.append('  decide +kernel')
    L.append('theorem ccsc%d : Covered (toCl CSc%d) :=' % (k, k))
    L.append('  covered_of_walkCP lbS lbD ptS hR %s %d 0 %d _ wcsc%d (by decide)' % (wd, fuel, nbits, k))
    return L


def module_head(lib, imports, skip, note):
    L = ['/- %s -/' % note] + ['import %s' % m for m in imports]
    if skip:
        L.append(SKIP.rstrip('\n'))
    L += ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000', 'noncomputable section',
          'namespace AMW.Cert.PC9XAData', OPEN]
    return L


DATA_NOTE = ('Generated data module of the Q = %d certificate (Lake library %s); part of the work whose copyright,\n'
             'license (Apache-2.0) and attribution notices are kept verbatim in %s.Base. Changes (Apache-2.0 §4(b)),\n'
             '%s, by Rishi Khan: generated walk words, states and walk theorems of cut subtrees.')


def fixed_patch(src):
    """q9fixed/patch.py's edits for a file without the zfE decoder: edits (a), (b) (pvCheck through pvCheck2 with
    this window's ρ and Lipschitz constant) and the nlinarith replacements; the decoder edits (c) do not apply."""
    import patch
    import zfe_prims
    zfe = set(a for a, _ in zfe_prims.PAIRS)
    m = re.search(r'^def cellU \(i : ℕ\) : ℚ := sumQ \(termU i\) 17 \+ (\d+) / 1024$', src, re.M)
    rho = re.search(r'^theorem pvCheck_AM : pvCheck \((\d+) / (\d+)\) = true := by decide \+kernel$', src, re.M)
    assert m and rho
    src = patch.pack_table(src)
    for old, new, n in patch.EDITS:
        if old in zfe:
            assert src.count(old) == 0
            continue
        if old.startswith('set_option maxRecDepth 100000 in\ntheorem pvCheck_AM : pvCheck (1 / 25)'):
            old = old.replace('(1 / 25)', '(%s / %s)' % (rho[1], rho[2]))
            new = new.replace('(1 / 25)', '(%s / %s)' % (rho[1], rho[2]))
            assert new.count(' + 167 / 1024') == 1
            new = new.replace(' + 167 / 1024', ' + %s / 1024' % m[1])
        c = src.count(old)
        assert c == n, 'edit expected %d matches, found %d: %s' % (n, c, old[:80])
        src = src.replace(old, new)
    return src


# ------------------------------------------------------------------ kernel-table size (pyramid levels PLV, regions NREG)
# attempt-031's checker has PLV = 20 pyramid levels (lb domain x < 2^19, 512 blocks of 2^10 units, top levels 11..19)
# and NREG = 16 convexity regions.  A model with M.PLV / M.NREG (q12x/extend_model.py) needs the same literals raised
# in the declarations below; every other declaration is unchanged.  Per declaration: the literal tokens it holds in
# the base and how many of each (checked, so a changed base fails loudly).
WIDEN_LEVEL = {
    # name: {token: count}; tokens 19 (top level), 20 (first level past the top), 9 (levels above the blocks),
    # 512 (blocks), 524289 / 524288 (lb cut / domain)
    'entry': {'19': 1, '20': 1}, 'topv': {'19': 1}, 'topOk': {'9': 1, '19': 2}, 'topv_top': {'19': 1},
    'lb': {'524289': 1}, 'lbF': {'524289': 1}, 'blocks_of': {'512': 2},
    'top_sound': {'512': 1, '9': 6, '19': 2},
    'entry_sound': {'512': 3, '9': 3, '19': 6, '20': 2},
    'entry_ge20': {'20': 2}, 'entry_pack_sound': {'512': 1, '19': 3},
    'dcore_sound': {'512': 1, '19': 7}, 'dstep_sound': {'512': 1, '19': 2}, 'dcov_sound': {'512': 1, '19': 2},
    'lb_sound': {'512': 1, '524289': 2, '524288': 1, '19': 5},
}
WIDEN_LEVEL.update({{'entry': 'entry2', 'topv': 'topv2', 'topOk': 'topOk2', 'topv_top': 'topv2_top', 'lb': 'lbDr',
                     'lbF': 'lbDrF', 'blocks_of': 'blocks2_of', 'top_sound': 'top2_sound', 'entry_sound': 'entry2_sound',
                     'entry_ge20': 'entry2_ge20', 'entry_pack_sound': 'entry2_pack_sound', 'dcore_sound': 'dcore2_sound',
                     'dstep_sound': 'dstep2_sound', 'dcov_sound': 'dcov2_sound', 'lb_sound': 'lbDr_sound'}[k]: v
                    for k, v in list(WIDEN_LEVEL.items())})
WIDEN_DEPTH = ('entry_sound', 'entry2_sound', 'dcore_sound', 'dcore2_sound', 'lb_sound', 'lbDr_sound')
WIDEN_REGION = {'rgOk': ' allBelow 16 fun k =>', 'rg_conv': '{k : ℕ} (hk : k < 16)', 'tcheckZC': '   Nat.blt k 16 &&'}
DECL = re.compile(r'^(?:def|theorem|lemma|end|namespace|section|noncomputable|set_option|open|/-|--|@\[)', re.M)


def decl_span(src, name):
    """[start, end) of the unique top-level `def name` / `theorem name` block"""
    ms = list(re.finditer(r'^(?:def|theorem) %s[ \n]' % re.escape(name), src, re.M))
    assert len(ms) == 1, (name, len(ms))
    i = ms[0].start()
    m = DECL.search(src, ms[0].end())
    return i, m.start()


def widen_tables(src, plv, nreg):
    """raise the pyramid to plv levels and the region count to nreg (identity for 20 / 16)"""
    if (plv, nreg) == (20, 16):
        return src
    assert plv >= 20 and 16 <= nreg and nreg * 32768 <= 1 << 20, (plv, nreg)   # rgA / rgB fields are 20 bits
    new = {'19': plv - 1, '20': plv, '9': plv - 11, '512': 1 << (plv - 11), '524289': (1 << (plv - 1)) + 1,
           '524288': 1 << (plv - 1)}
    for name, want in WIDEN_LEVEL.items():
        i, j = decl_span(src, name)
        txt = src[i:j]
        tok = re.compile(r'\b(%s)\b' % '|'.join(sorted(new, key=len, reverse=True)))
        got = {}
        for t in tok.findall(txt):
            got[t] = got.get(t, 0) + 1
        assert got == want, (name, got, want)
        src = src[:i] + tok.sub(lambda m: str(new[m.group(1)]), txt) + src[j:]
    # with exponents past 19 the `congr` / `rw` steps of these proofs exceed the default maxRecDepth (512)
    for name in WIDEN_DEPTH:
        i, j = decl_span(src, name)
        src = src[:i] + 'set_option maxRecDepth 100000 in\n' + src[i:]
    for name, s in WIDEN_REGION.items():
        i, j = decl_span(src, name)
        txt = src[i:j]
        assert txt.count(s) == 1, name
        src = src[:i] + txt.replace(s, s.replace('16', str(nreg))) + src[j:]
    return src


def cell_ranges(bk, nb, parts, cells=1024):
    """block-check ranges [(a, n)]: emit.ranges(nb, parts), each range further cut so that it holds at most `cells`
    finest cells (a block with finest level r has 2^(10 - r) cells; blocks of 4-unit cells hold 256)"""
    out = []
    for a, n in emit.ranges(nb, parts):
        s, w = a, 0
        for j in range(a, a + n):
            c = (1 << (10 - (bk[j] & 31))) if bk.get(j) else 0
            if w and w + c > cells:
                out.append((s, j - s))
                s, w = j, 0
            w += c
        out.append((s, a + n - s))
    return out


def emit_pyramids(TOP, BK, TOPD, BKD, nb):
    """gen/emit.emit_pyramids with nb blocks (the block checks in 5 / 4 parts per 512 blocks)"""
    if nb == 512:
        return emit.emit_pyramids(TOP, BK, TOPD, BKD)
    L = []
    for pre, chk, parts, top, bk, nm, okn, sound in (
            ('blk', 'Pyr.blockOk (BK j) j', 5 * nb // 512, TOP, BK, 'BK', 'theorem top_ok : Pyr.topOk TOP BK = true',
             'theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok'),
            ('dblk', 'blockOk2 (BKD j) j', 4 * nb // 512, TOPD, BKD, 'BKD', 'theorem topD_ok : topOk2 TOPD BKD = true',
             'theorem lbD : LBSoundD TOPD BKD := lbDr_sound (blocks2_of dblk_all) topD_ok')):
        L.append('def %s : ℕ := %s' % ('TOP' if nm == 'BK' else 'TOPD', emit.zf(top)))
        keys = sorted(bk)
        for j in keys:
            L.append('def %s_%d : ℕ := %s' % (nm, j, hex(bk[j]) if nm == 'BK' else emit.zf(bk[j])))
        L += emit.dispatch(nm, keys, lambda j, nm=nm: '%s_%d' % (nm, j), nm)
        L.append(okn + ' := by decide +kernel')
        names = []
        for i, (a, n) in enumerate(cell_ranges(bk, nb, parts)):
            L.append('theorem %s_%d : Pyr.allFrom %d %d (fun j => %s) = true := by decide +kernel' % (pre, i, a, n, chk))
            names.append('%s_%d' % (pre, i))
        L.append('theorem %s_all : Pyr.allFrom 0 %d (fun j => %s) = true := by' % (pre, nb, chk))
        L.append('  have h := %s' % emit.chain_add(names))
        L.append('  exact h')
        L.append(sound)
    return L


def simple_text(a, Q, lib, hw, kappa, cN, B):
    """<lib>/Simple.lean: the N0simple forms of Final's theorems, from simple12.lean.in with this certificate's constants"""
    s = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'simple12.lean.in')).read()
    for k, v in [('Q', Q), ('LIB', lib), ('DATE', a.date), ('HW', hw), ('KN', kappa.numerator), ('KD', kappa.denominator),
                 ('CN', cN), ('B', B), ('SA', SA), ('N', Q + 1), ('WN', 'W%d' % (Q + 1))]:
        s = s.replace('@@%s@@' % k, str(v))
    assert '@@' not in s
    return s


def changes_block(a, Q, NP, NT, cN, B, hw, kappa, npts, nleaves, ncuts, nmods, test):
    L = [
        '/-',
        'Changes (Apache-2.0 §4(b)), %s, by Rishi Khan. This work is derived from Samuel Lavery\'s riemannzeta.fun' % a.date,
        'attempt-031 (Solution.lean sha256 0adbf8e04b4bc3db5dae886dfe003dc4fb9b9acd6d998a43f2a5603cba515f32, Apache-2.0); every',
        'copyright, license and attribution notice above and below is retained verbatim. Changes:',
        '* The window family has 17 terms, v(s) = cos(√2 s) + ∑_{j=1}^{16} c_j cos(2πj s): the window-dependent declarations',
        '  are written for 16 harmonics, with every window literal and the H_W floor (HW_ge %d/10⁴⁰)' % hw,
        '  recomputed for the window.',
        '* KB (the gap range of the root cover and of the cell keys a·KB + b) is %d (2^%d) instead of 1048576.' % (a.kb, a.kb.bit_length() - 1),
    ]
    if (a.plv, a.nreg) != (20, 16):
        L += [
            '* Kernel tables raised: %d pyramid levels (lb domain x < 2^%d, %d blocks; entry, topOk, lb, lbF and the' % (a.plv, a.plv - 1, 1 << (a.plv - 11)),
            '  derivative copies entry2, topOk2, lbDr, lbDrF with their soundness proofs written for that depth) and %d' % a.nreg,
            '  convexity regions (rgOk, rg_conv, tcheckZC); entry_sound, dcore_sound, lb_sound and their copies run with',
            '  maxRecDepth 100000.',
        ]
    L += [
        '* %d-point certificate (Q = %d gaps): the instance module PC9XA is generated for %d gaps, %d pairs and %d weighted' % (Q + 1, Q, Q, NP, NT),
        '  terms (a state of %d naturals, a %d-bit split axis, multiplier records with a %d-bit pair index).' % (2 * Q + 2 * NP + 1, (Q + NP - 1).bit_length(), NP.bit_length()),
        '* The reflection half-space g_0 ≤ g_%d as one more multiplier row (c = %d): module PCellHalf and its instance' % (Q - 1, NP),
        '  part from Samuel Lavery\'s attempt-032 (am-cert, 2026-10-22, Apache-2.0), regenerated for %d gaps.' % Q,
        '* Weights b_r, a_ij (integers over 2²³·10²⁴, palindromic), floor c = %d/%d,' % (cN, SA),
        '  B = %d/%d; κ = (H_W⁻ − B)/(1 − c) = %d/%d.' % (B, SA, kappa.numerator, kappa.denominator),
        '* Declarations outside the dependency closure of the three scored theorems removed; notices kept.',
        '* Sparse leaf check (a leaf lists only its nonzero terms, folded into running sums: mleafZ, tzG, zfin; soundness',
        '  mleafZ_ok through the fold invariant ZInv), with every term\'s λ stored in the walk words; packed 256-bit gap',
        '  lanes (TZ = CVP, CN, VP, VN), a %d-way dispatch for a multiplier\'s pair bounds (ycs, yupdS2), one definition' % NP,
        '  per term kind (tzk0 .. tzk4, tzL), split slots by balanced dispatch.',
        '* Tangent point table of {:,} points as a balanced binary tree (inductive PTB, ptOkB, ptTB_sound), each entry'.format(npts),
        '  with its own zside piece count.',
        '* Fixed-cost changes: CellA.k, CellA.side, CellA.ok, treadU, treadD, treadUF, treadDF and tcheckZC put the literal',
        '  operand first; pvCheck_AM is proved through pvCheck2 / pvCheck2_eq (packed sine table, ℤ sums, sinPiI2);',
        '  nlinarith calls of deleted_strips and strips_le replaced by the products they search for.',
        '* The work is a Lake library of modules: %s.Base (this module), data modules %s.C.M<i> with the cut subtrees,' % (a.lib, a.lib),
        '  and %s.Final with the root walks and the final assembly (counts in %s.Final\'s header).' % (a.lib, a.lib),
    ]
    if not a.no_skip:
        L.append('* `set_option debug.skipKernelTC true` after the imports of every module: the build skips its own kernel')
        L.append('  check; nanoda and the Lean kernel replay of the export check every declaration.')
    if test:
        L.append('* COMPILE TEST ONLY, not a certificate: every root box is a hypothesis (AMW.Cert.PC9XAData.MissOK) of cert and')
        L.append('  of the theorems after it; the data modules check standalone subtrees.')
    L.append('-/')
    return '\n'.join(L) + '\n'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('base'); ap.add_argument('model'); ap.add_argument('pts'); ap.add_argument('out')
    ap.add_argument('--trees'); ap.add_argument('--subtrees')
    ap.add_argument('--ptn', help='point table rows "x word n"; default: pts.pkl words with n = 32')
    ap.add_argument('--cut-leaves', type=int, default=400)
    ap.add_argument('--module-leaves', type=int, default=8000)
    ap.add_argument('--no-skip', action='store_true')
    ap.add_argument('--data-check', action='store_true', help='MEASUREMENT: data modules without skipKernelTC (the build '
                    'kernel-checks their walks), Base and Final with it')
    ap.add_argument('--profile', action='store_true', help='MEASUREMENT: set_option profiler true in the data modules')
    ap.add_argument('--date', default='2026-10-25')
    ap.add_argument('--lib', default='Q12')
    ap.add_argument('--part-pts', type=int, default=600)
    ap.add_argument('--fast', action='store_true', help='structure-only walk (no exact leaf re-check), linear time')
    ap.add_argument('--super-leaves', type=int, default=0, help='with --fast: level-2 cuts of at most this many leaves')
    ap.add_argument('--procs', type=int, default=1, help='with --fast: roots walked in parallel processes')
    ap.add_argument('--nest-leaves', type=int, default=0, help='with --super-leaves: nested level-2 cuts so that no '
                    'level-2 walk has more than this many leaves outside its level-1 cuts (0: off)')
    a = ap.parse_args()
    assert not a.super_leaves or a.fast
    assert a.trees or a.subtrees
    import fb12
    M = pickle.load(open(a.model, 'rb'))
    P = pickle.load(open(a.pts, 'rb'))
    Q, NP = M.Q, M.NP
    if a.ptn:
        tab = {}
        for l in open(a.ptn):
            x, w, n = map(int, l.split())
            tab[x] = (w, n)
        P = {x: w for x, (w, n) in tab.items()}
    else:
        tab = {x: (w, 32) for x, w in P.items() if w}
    W = Walker(M, P)
    extra = M.WMASK.bit_length()
    lens = [len([s for s in M.COV[r] if not s[2]]) for r in range(Q)]
    roots = list(itertools.product(*[range(n) for n in lens]))

    # ---------------- cut subtrees (k, flat state, stream re-based at 0, length, leaves)
    cuts = []
    skel = {}            # root -> (zeroed stream, end, [(pos, k, end)], leaves walked by the skeleton)
    skf = {}             # root -> root skeleton walk fuel (--fast; 128 when absent)
    anchors = set()
    nleaves = 0
    trees = pickle.load(open(a.trees, 'rb')) if a.trees else {}
    test = sorted(trees) != list(range(len(roots)))
    if a.subtrees:
        for t in pickle.load(open(a.subtrees, 'rb')):
            e, st = W.walk(t['bits'], 0, t['s'])
            assert e == t['nbits']
            anchors |= st['anchors']
            nleaves += st['leaves']
            cuts.append((len(cuts), W.H.st_flat(t['s']), t['bits'], t['nbits'], st['leaves']))
    if a.fast:
        assert a.ptn and not a.subtrees
        FW = FastWalker(M)

        _PLAN.update(FW=FW, trees=trees, roots=roots, a=a)
        plan = _plan
        for r in trees:
            assert tuple(trees[r]['idx']) == roots[r]
        if a.procs > 1:
            import multiprocessing
            with multiprocessing.get_context('fork').Pool(min(a.procs, len(trees))) as pool:
                order = sorted(trees, key=lambda r: -trees[r]['nbits'])
                R = dict(zip(order, pool.imap(plan, order, chunksize=1)))
        else:
            R = {r: plan(r) for r in sorted(trees)}
        unit0 = 0
        for r in sorted(trees):
            cs, sk, lv, rf = R[r]
            k0 = len(cuts)
            # renumber the cut ids and units of this root after the previous roots'
            ren = lambda j: j + k0
            for (k, flat, sub, n, cnt, unit, kids, fu) in cs:
                cuts.append((ren(k), flat, sub, n, cnt, unit0 + unit,
                             None if kids is None else [(p, ren(j), ce) for (p, j, ce) in kids], fu))
            unit0 += 1 + max([c[5] for c in cs], default=-1)
            zs, end, ents, rem, skf[r] = sk
            skel[r] = (zs, end, [(p, ren(j), ce) for (p, j, ce) in ents], rem)
            nleaves += lv
            print('root', r, 'leaves', lv, 'refl', rf, 'cuts', len(cs), 'level-2', sum(1 for c in cs if c[6] is not None),
                  'skeleton entries', len(ents), 'skeleton leaves', rem, 'skeleton bits', end, flush=True)
            del R[r]
        anchors = set(tab)
    else:
        for r in sorted(trees):
            T = trees[r]
            assert tuple(T['idx']) == roots[r]
            s0 = fb12.root_state(W.H, roots[r])
            e, st = W.walk(T['bits'], 1, s0)
            assert e == T['nbits'], (r, e, T['nbits'])
            anchors |= st['anchors']
            nleaves += st['leaves']
            rem = st['leaves']
            chosen = []
            if rem > a.cut_leaves:
                for (pos, s, ce, cnt, d) in sorted([n for n in st['nodes'] if n[4] >= 1 and n[3] <= a.cut_leaves],
                                                   key=lambda n: -n[3]):
                    if rem <= a.cut_leaves:
                        break
                    if any(not (ce <= p0 or e0 <= pos) for (p0, e0, _, _) in chosen):
                        continue
                    chosen.append((pos, ce, s, cnt))
                    rem -= cnt
            chosen.sort()
            zs = T['bits']
            ents = []
            for (pos, ce, s, cnt) in chosen:
                sub = (T['bits'] >> pos) & ((1 << (ce - pos)) - 1)
                k = len(cuts)
                cuts.append((k, W.H.st_flat(s), sub, ce - pos, cnt))
                zs &= ~(((1 << (ce - pos)) - 1) << pos)
                ents.append((pos, k, ce))
            skel[r] = (zs, T['nbits'], ents, rem)
    # ---------------- table words
    assert anchors <= set(tab), 'leaves use points outside the table'
    words = {x: tab[x][0] + ((tab[x][1] - 1) << 140) for x in anchors}
    print('cuts', len(cuts), 'leaves', nleaves, 'tangent points', len(words))

    # ---------------- single source with the data module split out
    spec = dict(Q=Q, PR=M.PR, TS=M.TS, BS=M.BS, SL=M.SL, BND=M.BND, ADJ=M.ADJ, cN=M.cN, SIG=M.SIG, SA=SA,
                wmask_bits=extra, half=True, pb=NP.bit_length(), yfuel=M.YFUEL, TB=[], kfmt=True, novar=True,
                gsplit=True, yrow=True, helpers=True, notn=True, adjlam=True, sparse=True, leaf2='ypbS')
    assert [tuple(p) for p in M.PR] == [(i, j) for i in range(Q) for j in range(i + 2, Q + 1)]
    inst = Inst12(spec).emit()
    src = open(a.base).read()
    # the model's gap range: the q12 models use KB = 2^22 (q12/cert12.py refit "kb22", q9/build9.py --kb); the base
    # (attempt-031) has KB = 2^20, and its proofs read KB only through `norm_num [KB]` and KB's role in CellN keys
    kb_old = 'def KB : ℕ := 1048576\n'
    assert src.count(kb_old) == 1
    src = src.replace(kb_old, 'def KB : ℕ := %d\n' % M.KB)
    i0 = src.index('-- SWAP BEGIN certificate')
    i1 = src.index('end AMW.Cert.PC9XA\nend\n', i0) + len('end AMW.Cert.PC9XA\nend\n')
    src = src[:i0] + gen9.half_module() + inst + src[i1:]
    BK = {j: v for j, v in M.BKv.items() if v}
    BKD = {j: v for j, v in M.BKDv.items() if v}
    PLV, NREG = getattr(M, 'PLV', 20), getattr(M, 'NREG', 16)
    assert len(M.REG[2]) == NREG and len(M.BKv) <= 1 << (PLV - 11)
    pre = emit_pyramids(M.TOP, BK, M.TOPD, BKD, 1 << (PLV - 11)) + emit.emit_reg(M.REG)
    pre += emit_table(words, a.part_pts)
    pre += gen9.emit_cover(Q, NP, M.COV, M.SMAX)
    MARK = '-- @@ROOTS@@'
    data = ['end', ptb_checker(), 'noncomputable section',
            'namespace AMW.Cert.PC9XAData', OPEN, 'set_option maxRecDepth 100000'] + pre + [MARK, 'end AMW.Cert.PC9XAData']
    src = gen9.replace_between(src, 'namespace AMW.Cert.PC9XAData\n', 'end AMW.Cert.PC9XAData\n', '\n'.join(data) + '\n',
                               inclusive_b=True)
    AW = {(t[0], t[1]): t[2] for t in M.TS}
    hw = gen9.hw_from(src)
    B = sum(M.BS)
    cN = M.cN
    kappa = (Fraction(hw, 10 ** 40) - Fraction(B, SA)) / (1 - Fraction(cN, SA))
    tail = gen9.emit_tail(Q, M.BS, AW, cN, hw, kappa, test)
    j0 = src.index('end AMW.Cert.PC9XAData\n') + len('end AMW.Cert.PC9XAData\n')
    j0 = src.index('end\n', j0) + len('end\n')
    j1 = src.index('-- SWAP END certificate')
    src = src[:j0] + '\n'.join(tail) + '\n' + src[j1:]
    fin = gen9.emit_final(Q, B, cN, hw, kappa, test)
    src = gen9.replace_between(src, 'namespace Opeth.AMFinal\n', 'end Opeth.AMFinal\n', '\n'.join(fin) + '\n', inclusive_b=True)
    src = re.sub(r'(candidateKappa = \()\d+ / \d+( : ℝ\))',
                 lambda m: '%s%d / %d%s' % (m.group(1), kappa.numerator, kappa.denominator, m.group(2)), src, count=1)
    if test:
        src = src.replace('  exact Opeth.AMFinal.actual_dyadic\n', '  exact Opeth.AMFinal.actual_dyadic hm\n', 1)
        src = src.replace('  exact Opeth.AMFinal.actual_cumulative\n', '  exact Opeth.AMFinal.actual_cumulative hm\n', 1)
        src = src.replace('theorem candidate_critical_line_bound :\n', 'theorem candidate_critical_line_bound (hm : AMW.Cert.PC9XAData.MissOK) :\n', 1)
        src = src.replace('theorem candidate_critical_line_bound_cumulative :\n',
                          'theorem candidate_critical_line_bound_cumulative (hm : AMW.Cert.PC9XAData.MissOK) :\n', 1)
    import prune_names
    names = set(x for x in open(os.path.join(LB, 'q9lean', 'dead', 'removed.names')).read().split() if x)
    names |= gen9.PTD_NAMES | {'ystepH', 'ydecH', 'ystepH_ok', 'ydecH_ok'}
    src, missing = prune_names.prune(src, names)
    assert not missing, missing
    src = fixed_patch(src)
    src = widen_tables(src, PLV, NREG)
    for head in ('/-\nChanges (Apache-2.0 §4(b)), 2026-10-23, by Rishi Khan.',
                 '/-\nChanges (Apache-2.0 §4(b)), by Rishi Khan, 2026-10-23.'):
        while head in src:
            i = src.index(head)
            j = src.index('-/\n', i) + 3
            src = src[:i] + src[j:]
    nmods_guess = 0
    # ---------------- modules
    groups = []
    for i, c in enumerate(cuts):
        unit_start = len(c) < 6 or i == 0 or cuts[i - 1][5] != c[5]
        if not groups or (unit_start and sum(x[4] for x in groups[-1]) >= a.module_leaves):
            groups.append([])
        groups[-1].append(c)
    a.kb = M.KB
    a.plv, a.nreg = PLV, NREG
    src = src.replace('import ChallengeDeps\n', changes_block(a, Q, NP, len(M.TS), cN, B, hw, kappa, len(words), nleaves,
                                                              len(cuts), len(groups), test) + 'import ChallengeDeps\n', 1)
    m = src.index(MARK)
    base_txt = src[:m] + 'end AMW.Cert.PC9XAData\nend\n'
    rest = src[m + len(MARK) + 1:]
    assert rest.startswith('end AMW.Cert.PC9XAData\n')
    # Base: skip option right after the imports
    k = base_txt.index('\n', base_txt.rindex('\nimport ') + 1) + 1
    if '\nset_option debug.skipKernelTC' in base_txt:
        raise SystemExit('base already has skipKernelTC')
    if not a.no_skip:
        base_txt = base_txt[:k] + SKIP + base_txt[k:]
    lib = a.lib
    od = os.path.join(a.out, lib)
    os.makedirs(os.path.join(od, 'C'), exist_ok=True)
    open(os.path.join(od, 'Base.lean'), 'w').write(base_txt)
    mods = []
    note = DATA_NOTE % (Q, lib, lib, a.date)
    for gi, g in enumerate(groups):
        L = module_head(lib, ['%s.Base' % lib], not (a.no_skip or a.data_check), note)
        if a.profile:
            L.insert(L.index('noncomputable section'), 'set_option profiler true\nset_option profiler.threshold 1')
        for c in g:
            if len(c) > 6 and c[6] is not None:
                L += super_text(c[0], c[1], c[2], c[3], extra, c[6], c[7])
            elif len(c) > 7:
                L += cut_text(*c[:4], extra, c[7])
            else:
                L += cut_text(*c[:4], extra)
        L += ['end AMW.Cert.PC9XAData', 'end']
        nm = 'M%d' % gi
        open(os.path.join(od, 'C', nm + '.lean'), 'w').write('\n'.join(L) + '\n')
        mods.append('%s.C.%s' % (lib, nm))
    # Final: root skeletons, run, cert, then the rest of the source (tail, final theorems, notices)
    F = ['/- Final module of the Q = %d certificate (Lake library %s): root walks over the data modules\' cut subtrees, the' % (Q, lib),
         'root cover and the final assembly. Copyright, license (Apache-2.0) and attribution notices: %s.Base and the' % lib,
         'notices kept verbatim below. Changes (Apache-2.0 §4(b)), %s, by Rishi Khan: generated as described in %s.Base;' % (a.date, lib),
         '%d data modules, %d cut subtrees, %d leaves, %d tangent points%s. -/' % (len(groups), len(cuts), nleaves, len(words),
                                                                              ' (COMPILE TEST: roots missing)' if test else '')]
    F += ['import %s' % x for x in (mods or ['%s.Base' % lib])]
    if not a.no_skip:
        F.append(SKIP.rstrip('\n'))
    F += ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000', 'noncomputable section',
          'namespace AMW.Cert.PC9XAData', OPEN]
    have = set()
    have_f = set()
    for r in sorted(skel):
        zs, end, ents, rem = skel[r]
        assert ents or skf.get(r, 128) == 128, ('root skeleton without cuts deeper than fuel 128', r)
        L, wd = wl_defs('WS%d' % r, zs, end, extra)
        F += L
        ix = ' '.join(str(i) for i in roots[r])
        if not ents:
            F.append('theorem rc%d : Covered (RC %s) := rcOf %s %d (by decide +kernel) (by decide)' % (r, ix, wd, end))
        else:
            F.append('def CUTS%d : List (ℕ × St × ℕ) := [%s]' % (r, ', '.join('(%d, CSc%d, %d)' % (p, k, ce) for (p, k, ce) in ents)))
            oks = 'cutsOk_nil'
            for (p, k, ce) in reversed(ents):
                oks = '(cutsOk_cons ccsc%d %s)' % (k, oks)
            fu = skf.get(r, 128)
            if fu == 128:
                F.append('theorem rc%d : Covered (RC %s) := rcOfC %s CUTS%d %s %d (by decide +kernel) (by decide)' % (r, ix, wd, r, oks, end))
            else:
                if fu not in have_f:
                    F += rcofc_fuel(Q, fu)
                    have_f.add(fu)
                F.append('theorem rc%d : Covered (RC %s) := rcOfCF%d %s CUTS%d %s %d (by decide +kernel) (by decide)' % (r, ix, fu, wd, r, oks, end))
        have.add(r)
    F += gen9.emit_run(Q, NP, lens, have, test)
    final_txt = '\n'.join(F) + '\n' + rest
    open(os.path.join(od, 'Final.lean'), 'w').write(final_txt)
    if test:
        open(os.path.join(a.out, lib + '.lean'), 'w').write('import %s.Final\n' % lib)
    else:
        open(os.path.join(od, 'Simple.lean'), 'w').write(simple_text(a, Q, lib, hw, kappa, cN, B))
        open(os.path.join(a.out, lib + '.lean'), 'w').write('import %s.Simple\n' % lib)
    import json
    json.dump(dict(cuts=[dict(k=c[0], leaves=c[4], bits=c[3], module=gi, **({'kids': len(c[6])} if len(c) > 6 and c[6] else {}))
                         for gi, g in enumerate(groups) for c in g],
                   roots={r: dict(skeleton_leaves=skel[r][3], end=skel[r][1], cuts=len(skel[r][2])) for r in skel},
                   leaves=nleaves, points=len(words), test=test), open(os.path.join(a.out, 'cuts.json'), 'w'), indent=1)
    tot = sum(os.path.getsize(os.path.join(dp, f)) for dp, _, fs in os.walk(od) for f in fs)
    print('modules', len(mods), 'cuts', len(cuts), 'leaves', nleaves, 'bytes', tot,
          'base', len(base_txt.encode()), 'final', len(final_txt.encode()))
    print('kappa', kappa.numerator, kappa.denominator, float(kappa), 'c', cN / SA, 'B', B / SA)


if __name__ == '__main__':
    main()
