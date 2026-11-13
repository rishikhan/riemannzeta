"""Window-dependent tables: value and derivative pyramids, convexity regions, tangent
point words with their precertified intervals, and the root cover.

Every value is the largest one the corresponding Lean check accepts, computed with
replay's CellEval/Checker on the (possibly patched) model M.
"""
from core import SC, replay

nsub = replay.nsub
M32 = 0xFFFFFFFF


# ------------------------------------------------------------------ pyramids
def vmax_cell(C, LN, UN):
    """Largest v with cellOkCore (v/1e10 <= w on the cell), capped to 32 bits; 0 if not ok."""
    c = C.CE.cell(LN, UN)
    if not c['ok']:
        return 0
    return min(M32, (c['KAn'] * c['KAn'] * C.SW) // (1000 * C.DZ * C.DZ))


def dmax_cell(C, LN, UN):
    """Packed derivative lanes (lo32: KU1 + W1LO, hi32: KU1 - W1HI), 0 lanes when not ok."""
    if not C.okD(LN, UN):
        return 0
    lo = C.KU1 + C.W1LO(LN, UN)
    hi = C.KU1 - C.W1HI(LN, UN)
    lo = lo if 0 < lo <= M32 else 0
    hi = hi if 0 < hi <= M32 else 0
    return lo + (hi << 32)


def pmin(a, b):
    return min(a & M32, b & M32) + (min(a >> 32, b >> 32) << 32)


def build_block(C, j, r, leafval, fw, mn):
    """Block j with finest level r: heap of fields (field width fw bits), root at index 0."""
    D = 10 - r
    n = 1 << D
    lev = [leafval(C, ((j << D) + t) << r, ((j << D) + t + 1) << r) for t in range(n)]
    heap = {}
    for t, v in enumerate(lev):
        heap[(1 << D) - 1 + t] = v
    for d in range(D - 1, -1, -1):
        for t in range(1 << d):
            heap[(1 << d) - 1 + t] = mn(heap[(1 << (d + 1)) - 1 + 2 * t], heap[(1 << (d + 1)) - 1 + 2 * t + 1])
    Y = 0
    for i, v in heap.items():
        Y |= v << (fw * i)
    if Y == 0:
        return 0
    return r | (Y << 5)


def build_pyramid(C, blocks, deriv=False):
    """blocks: {j: r}. -> (TOP, {j: BK_j})."""
    fw = 64 if deriv else 32
    mn = pmin if deriv else min
    leafval = dmax_cell if deriv else vmax_cell
    BK = {}
    for j, r in blocks.items():
        X = build_block(C, j, r, leafval, fw, mn)
        if X:
            BK[j] = X
    mask = (1 << fw) - 1

    def root(j):
        X = BK.get(j, 0)
        return (X >> 5) & mask
    # level 10 = block roots; levels 11..PLV-1 in TOP at index 2^(PLV-1-l) + i (PLV = 20 in the Lean checker)
    PLV = getattr(C, 'PLV', 20)
    cur = [root(j) for j in range(1 << (PLV - 11))]
    TOP = 0
    for l in range(11, PLV):
        nxt = [mn(cur[2 * i], cur[2 * i + 1]) for i in range(len(cur) // 2)]
        for i, v in enumerate(nxt):
            TOP |= v << (fw * ((1 << (PLV - 1 - l)) + i))
        cur = nxt
    return TOP, BK


# ------------------------------------------------------------------ convexity regions
def build_regions(C, lo_first=16384, step=256, kmin=1):
    """One convex region per integer k = 1..NREG-1 (nearest-integer indexing; NREG = 16 in the Lean checker);
    region 0 empty.  kmin > 1: regions below kmin are left empty (the caller merges them from another build).
    -> (Apack, Bpack, chains)."""
    NREG = getattr(C, 'NREG', 16)
    A = [1] + [0] * (NREG - 1)
    B = [0] * NREG
    chains = [[]]
    for k in range(1, NREG):
        if k < kmin:
            A[k], B[k] = 1, 0
            chains.append([])
            continue
        lo_lim = max(k * SC - 16384, lo_first)
        hi_lim = k * SC + 16383
        # maximal run of step cells containing a convex cell near the centre
        cells = list(range(lo_lim, hi_lim - step + 1, step))
        okc = [C.convOk(a, a + step) for a in cells]
        # pick the longest run
        best, cur = None, None
        for i, o in enumerate(okc):
            if o:
                cur = (cur[0], i) if cur else (i, i)
                if best is None or cur[1] - cur[0] > best[1] - best[0]:
                    best = cur
            else:
                cur = None
        if best is None:
            A[k], B[k] = 1, 0
            chains.append([])
            continue
        a, b = cells[best[0]], cells[best[1]] + step
        # extend the ends with halving widths
        w = step // 2
        while w >= 1:
            while a - w >= lo_lim and C.convOk(a - w, a):
                a -= w
            while b + w <= hi_lim and C.convOk(b, b + w):
                b += w
            w //= 2
        chain = coarse_chain(C, a, b)
        A[k], B[k] = a, b
        chains.append(chain)
    Ap = sum(v << (20 * k) for k, v in enumerate(A))
    Bp = sum(v << (20 * k) for k, v in enumerate(B))
    return Ap, Bp, chains


def coarse_chain(C, a, b):
    """Chain a = b_0 < b_1 < ... = b of convOk links, greedily as long as possible."""
    out = []
    x = a
    while x < b:
        w = 1
        while x + 2 * w <= b and C.convOk(x, x + 2 * w):
            w *= 2
        # try to stretch to b directly
        if C.convOk(x, b):
            nx = b
        else:
            nx = x + w
            # extend by binary steps
            st = w // 2
            while st >= 1:
                if nx + st <= b and C.convOk(x, nx + st):
                    nx += st
                st //= 2
        assert C.convOk(x, nx), (x, nx)
        out.append(nx)
        x = nx
    return out


# ------------------------------------------------------------------ tangent points
class Points:
    """Virtual tangent point table: point words computed on demand, intervals maximal
    under tcheckZC.  pt(x) returns the pwD-expanded word (0 if x cannot be an anchor)."""

    def __init__(self, C, n=32, csh=4, maxoff=(1 << 20) - 1):
        self.C = C
        self.n, self.csh = n, csh
        self.maxoff = maxoff
        self.cache = {}
        self.frozen = False

    def trip(self, x):
        C = self.C
        if not C.okD(x, x):
            return 0
        V = vmax_cell(C, x, x)
        P = C.KU1 + C.W1LO(x, x)
        Mv = C.KU1 - C.W1HI(x, x)
        if not (1 <= P <= M32 and 1 <= Mv <= M32):
            return 0
        return V + (P << 32) + (Mv << 64)

    def right_ok(self, x, X, U):
        C = self.C
        k = (x + 16384) >> 15
        B = C.rgB(k)
        if U <= B:
            return True
        lo32, hi32 = C.lo32, C.hi32
        Mv, V = hi32(hi32(X)), lo32(X)
        jj = C.blen(nsub(U, B) >> self.csh)
        uc = C.rup(U, jj)
        tu = C.treadU(uc, x)
        if (1 <= lo32(tu) and 4000000000 <= lo32(tu) + Mv) or C.zsideF(V, Mv, x, B, uc, self.n, True):
            return True
        EU = C.treadU(U, x)
        if 1 <= lo32(EU) and 4000000000 <= lo32(EU) + Mv:
            return True
        return C.zsideF(V, Mv, x, B, U, self.n, True)

    def left_ok(self, x, X, L):
        C = self.C
        k = (x + 16384) >> 15
        A = C.rgA(k)
        if A <= L:
            return True
        lo32, hi32 = C.lo32, C.hi32
        Pv, V = lo32(hi32(X)), lo32(X)
        jj = C.blen(nsub(A, L) >> self.csh)
        lc = C.rdn(L, jj)
        td = C.treadD(lc, x)
        if (1 <= hi32(td) and 4000000000 <= hi32(td) + Pv) or C.zsideF(V, Pv, x, lc, A, self.n, False):
            return True
        ED = C.treadD(L, x)
        if 1 <= hi32(ED) and 4000000000 <= hi32(ED) + Pv:
            return True
        return C.zsideF(V, Pv, x, L, A, self.n, False)

    def search(self, ok, lo, hi):
        """Largest t in [lo, hi] with ok(t), assuming ok(lo); exponential then binary search."""
        if ok(hi):
            return hi
        good, step = lo, 1
        while good + step < hi and ok(good + step):
            good += step
            step *= 2
        bad = min(hi, good + step)
        while bad - good > 1:
            mid = (good + bad) // 2
            if ok(mid):
                good = mid
            else:
                bad = mid
        return good

    def word(self, x):
        """Stored (pre-pwD) word for x, or 0."""
        r = self.cache.get(x)
        if r is not None:
            return r
        if self.frozen:
            return 0
        C = self.C
        r = 0
        k = (x + 16384) >> 15
        if k < getattr(C, 'NREG', 16) and C.rgA(k) <= x <= C.rgB(k) and x + 1 <= C.KB:
            X = self.trip(x)
            if X:
                Umax = min(C.KB - 1, x + self.maxoff)
                Lmin = max(0, x - self.maxoff)
                U = self.search(lambda u: self.right_ok(x, X, u), x, Umax)
                L = x - self.search(lambda t: self.left_ok(x, X, x - t), 0, x - Lmin)
                r = X | ((x - L) << 96) | ((U - x) << 116)
                v = C.pwD(x, r)
                assert C.pt3e(x, C.trip(v)) and C.ivOk(self.n, self.csh, x, v), x
        self.cache[x] = r
        return r

    def pt(self, x):
        w = self.word(x)
        return self.C.pwD(x, w) if w else 0


# ------------------------------------------------------------------ root cover
def good_cell(C, cN, aadj, a, b):
    return cN * C.SW <= aadj * C.WZ(a, b)


def build_cover(C, cN, aadj, smax, bad_from=None, splits=()):
    """Good segments from 16384 while the adjacent term alone certifies (dyadic steps,
    largest first), then one bad segment to smax (optionally cut at `splits`)."""
    pos = 16384
    segs = []
    w = 4096
    while w >= 16:
        while pos + w <= (bad_from or smax) and good_cell(C, cN, aadj, pos, pos + w):
            segs.append((pos, pos + w, True))
            pos += w
        w //= 2
    cuts = [pos] + [s for s in splits if pos < s < smax] + [smax]
    for a, b in zip(cuts, cuts[1:]):
        segs.append((a, b, False))
    return segs


def _pt_worker(args):
    import pickle
    path, xs = args
    M, C, = pickle.load(open(path, 'rb'))
    P = Points(C)
    return {x: P.word(x) for x in xs}


def precompute_points(M, C, grid=8, workers=6, tmp='/tmp/lbgen_mc.pkl', kmin=1):
    """Words of every grid point inside the convexity regions k >= kmin, in parallel -> {x: word}."""
    import pickle
    from multiprocessing import Pool
    xs = []
    for k in range(kmin, getattr(C, 'NREG', 16)):
        a, b = C.rgA(k), C.rgB(k)
        if b < a:
            continue
        xs += list(range(((a + grid - 1) // grid) * grid, b + 1, grid))
    C.CE.cache.clear(); C.lb_cache.clear(); C.lbd_cache.clear(); C.pt_cache.clear()
    pickle.dump((M, C), open(tmp, 'wb'))
    chunks = [xs[i::workers * 8] for i in range(workers * 8)]
    out = {}
    with Pool(workers) as pool:
        for d in pool.imap_unordered(_pt_worker, [(tmp, ch) for ch in chunks]):
            out.update(d)
    return out
