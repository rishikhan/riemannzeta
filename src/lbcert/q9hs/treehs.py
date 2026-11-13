"""q9hs copy of q9/tree9.py: a leaf that needs the variance bonus is written with leaf bit 1 set
(attempt-031 mleafV), and the stats count variance leaves and leaves using the half-space row.

Tree builder with C++ split evaluation (gen/tree2.py for Q gaps: the reflection test reads
U_{Q-1}, and an optional leaf budget stops a root that blows up).

Original notes: tree builder with C++ split evaluation and depth-2 lookahead.

A node tries the reflection leaf, then (when the C++ LP margin >= gate) an exact leaf
certified in Python (leaf.py), first with anchors restricted to the shared set, then
unrestricted.  Otherwise it evaluates every axis x mode in C++ (one batched, threaded
call), keeps the top-k splits by the worse child margin, and for each of them looks one
level further: a child that already certifies (margin >= gate) scores +inf, otherwise its
best one-step split's worse grandchild margin.  The split with the best worse score wins.
"""
import time

from core import children, axis_bounds

MODES = (0, 1, 2, 3, 4, 5, 6, 7)


class Bits:
    def __init__(self):
        self.v = 0
        self.n = 0

    def put(self, val, nb):
        self.v |= val << self.n
        self.n += nb


class TreeBuilder2:
    def __init__(self, C, ls, E, nthreads=6, k=3, gate=0.0, max_depth=120, shared=None, lookahead=True):
        self.C, self.M, self.ls, self.E = C, C.M, ls, E
        self.nthreads, self.k, self.gate = nthreads, k, gate
        self.max_depth = max_depth
        self.lookahead = lookahead
        self.shared = shared if shared is not None else set()
        self.axmd = [(a, m) for a in range(self.M.Q + self.M.NP) for m in MODES]
        self.cache = {}
        self.peel = False
        self.halfgate = False
        self.leaf_budget = 0
        self.progress = 0
        self.stall = 0.2
        self.stall_depth = 0
        self.pen = 0.0
        self.pen_every = 50
        self.peel_gate = 2e-8
        self.peel_min = 0.25
        self.stats = dict(leaves=0, refl=0, splits=0, evals=0, fails=0, maxdepth=0, margins=[], newanchors=0,
                          var=0, half=0, leafbits=0)

    @staticmethod
    def key(s):
        return (tuple(s[0]), tuple(s[1]), tuple(s[2]), tuple(s[3]))

    def margin(self, s):
        if s[1][self.M.Q - 1] < s[0][0] or any(s[0][r] > s[1][r] for r in range(self.M.Q)):
            return 1.0
        return self.E.margin(s)

    def scan(self, s):
        """All splits of s, sorted by worse child margin: [(score, ax, md, ml, mr)]."""
        k = self.key(s)
        r = self.cache.get(k)
        if r is not None:
            return r
        ml, mr = self.E.splits(s, self.axmd, self.nthreads)
        self.stats['evals'] += 2 * len(self.axmd)
        out = []
        for (a, m), x, y in zip(self.axmd, ml, mr):
            if x <= -1e8:
                continue
            out.append((min(x, y), a, m, x, y))
        out.sort(key=lambda t: -t[0])
        if len(self.cache) > 20000:
            self.cache.clear()
        self.cache[k] = out
        return out

    def child_score(self, c, mc):
        if mc >= self.gate:
            return mc
        sc = self.scan(c)
        return sc[0][0] if sc else -1.0

    def choose(self, s):
        sc = self.scan(s)
        if not sc:
            return None
        if self.peel:
            best = None
            for (score, a, m, x, y) in sc:
                if max(x, y) < self.peel_gate:
                    continue
                i, j, lo, hi = axis_bounds(self.M, s, a)
                q = self.E.children(s, a, m)[0]
                f = (q - lo) / (hi - lo) if x >= y else (hi - q) / (hi - lo)
                key = (f, min(x, y))
                if best is None or key > best[0]:
                    best = (key, (score, a, m, x, y))
            if best is not None and best[0][0] >= self.peel_min:
                return best[1]
        if not self.lookahead:
            return sc[0]
        best = None
        for (score, a, m, x, y) in sc[:self.k]:
            q, left, right = children(self.C, s, a, m)
            v = min(self.child_score(left, x), self.child_score(right, y))
            if best is None or v > best[0]:
                best = (v, a, m, x, y)
        return best

    def certify(self, s):
        ls = self.ls
        for allowed in (self.shared, None):
            ls.allowed = allowed if allowed else None
            ls._tc.clear()
            r = ls.certify(s)
            if r[0] is not None:
                ls.allowed = None
                return r
        ls.allowed = None
        ls._tc.clear()
        return r

    def node(self, s, out, depth, m=None):
        st = self.stats
        st['maxdepth'] = max(st['maxdepth'], depth)
        if self.leaf_budget and st['leaves'] + st['refl'] > self.leaf_budget:
            raise RuntimeError('leaf budget %d exceeded' % self.leaf_budget)
        if s[1][self.M.Q - 1] < s[0][0]:
            out.put(0, 1)
            st['refl'] += 1
            return
        if m is None:
            m = self.margin(s)
        if self.halfgate and m < self.gate:
            # half-gate mode: splits are scored without the half-space row, the leaf gate uses it
            self.E.set_half(True)
            try:
                m = max(m, self.margin(s))
                if m < self.gate and self.pen > 0 and not (s[1][self.M.Q - 1] < s[0][0]):
                    m = max(m, self.E.margin_raw(s))
            finally:
                self.E.set_half(False)
        if m < self.gate and self.pen > 0 and not (s[1][self.M.Q - 1] < s[0][0]):
            mr = self.E.margin_raw(s)
            if mr >= self.gate:
                m = mr
        if m >= self.gate:
            pl, nb, mg, _ = self.certify(s)
            if pl is not None:
                isvar = self.ls.last_var
                out.put(2 if isvar else 0, 2)
                out.put(pl, nb)
                st['leaves'] += 1
                st['var'] += 1 if isvar else 0
                st['leafbits'] += 2 + nb
                st['margins'].append(mg)
                if self.progress and st['leaves'] % self.progress == 0:
                    print('  .. leaves %d refl %d splits %d depth %d maxdepth %d anchors+ %d'
                          % (st['leaves'], st['refl'], st['splits'], depth, st['maxdepth'], st['newanchors']), flush=True)
                self.note_anchors(s, pl, isvar)
                st['half'] += 1 if getattr(self.C, 'last_half', 0) else 0
                return
            st['fails'] += 1
        if depth >= self.max_depth:
            raise RuntimeError('depth limit at %r' % (s,))
        if m >= self.gate:
            # LP certifies but the quantised leaf does not: halve the widest gap
            r = max(range(self.M.Q), key=lambda r: s[1][r] - s[0][r])
            best = (0.0, r, 0, None, None)
        else:
            best = self.choose(s)
            if best is not None and depth >= self.stall_depth and m < 0 and best[0] - m < self.stall * (-m):
                r = max(range(self.M.Q), key=lambda r: s[1][r] - s[0][r])
                if s[1][r] - s[0][r] >= 2:
                    cands = [t for t in self.scan(s) if t[1] == r]
                    if cands:
                        best = cands[0]
        if best is None:
            raise RuntimeError('no split at %r' % (s,))
        _, a, md, x, y = best
        q, left, right = children(self.C, s, a, md)
        out.put(1 | (a << 1) | (md << 7), 10)
        st['splits'] += 1
        self.node(left, out, depth + 1, x)
        self.node(right, out, depth + 1, y)

    def note_anchors(self, s, payload, isvar=False):
        n, det = self.C.mleaf(payload, s, isvar, want_detail=True)
        for (a, lam, p, r) in det['terms']:
            for x in ((p,) if a in (1, 2) else (p, r) if a == 3 else ()):
                if x not in self.shared:
                    self.shared.add(x)
                    self.stats['newanchors'] += 1
                    if self.pen > 0 and self.stats['newanchors'] % self.pen_every == 0:
                        self.E.set_pen(self.shared, self.pen)

    def build(self, s):
        out = Bits()
        out.put(0, 1)
        t0 = time.time()
        if self.pen > 0:
            self.E.set_pen(self.shared, self.pen)
        self.node(s, out, 0)
        self.stats['secs'] = time.time() - t0
        return out
