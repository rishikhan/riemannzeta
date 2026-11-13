"""Root cover construction with maximal good segments (exact coverChk semantics).

A segment [a, b] is good for gap r when cN*SW <= a_adj(r)*WZ(a, b) (replay's coverChk).
Good runs are grown greedily with the longest certified segment at each step
(exponential then binary search on the free end, any integer boundary), from 16384
upwards and, for interior good regions, outwards from a certified centre.
"""


def good(C, cN, aadj, a, b):
    return a < b and cN * C.SW <= aadj * C.WZ(a, b)


def longest(ok, lo, hi):
    """Largest t in (lo, hi] with ok(t), probing outward from lo; lo if none."""
    if hi <= lo or not ok(lo + 1):
        return lo
    good_t, step = lo + 1, 1
    while good_t + step <= hi and ok(good_t + step):
        good_t += step
        step *= 2
    bad = min(hi + 1, good_t + step)
    while bad - good_t > 1:
        m = (good_t + bad) // 2
        if ok(m):
            good_t = m
        else:
            bad = m
    return good_t


MINW = 16   # stop a good run when the next certified step is shorter than this


def chain_up(C, cN, aadj, pos, hi):
    segs = []
    while pos < hi:
        b = longest(lambda t: good(C, cN, aadj, pos, t), pos, hi)
        if b - pos < MINW:
            break
        segs.append((pos, b, True))
        pos = b
    return segs, pos


def chain_down(C, cN, aadj, pos, lo):
    segs = []
    while pos > lo:
        d = longest(lambda t: good(C, cN, aadj, pos - t, pos), 0, pos - lo)
        if d < MINW:
            break
        segs.append((pos - d, pos, True))
        pos -= d
    return segs[::-1], pos


def interior_regions(C, cN, aadj, lo, hi, w=64):
    """Runs of good width-w cells in [lo, hi): candidate centres for interior good regions."""
    out, cur = [], None
    for a in range(lo, hi - w, w):
        if good(C, cN, aadj, a, a + w):
            cur = (cur[0], a + w) if cur else (a, a + w)
        elif cur:
            out.append(cur)
            cur = None
    if cur:
        out.append(cur)
    return out


def build_cover(C, cN, aadj, smax, interior=True, splits=(), scan_hi=None, min_interior=1024):
    """COV for one gap: low good run from 16384, optional interior good regions,
    bad segments between them (optionally cut at `splits`), last bad segment ends at smax."""
    low, pos = chain_up(C, cN, aadj, 16384, smax)
    goods = [low]
    if interior:
        scan_hi = scan_hi or min(smax, 3 * 32768)
        for (a, b) in interior_regions(C, cN, aadj, pos + 64, scan_hi):
            if b - a < min_interior:
                continue
            mid = (a + b) // 2
            dn, l = chain_down(C, cN, aadj, mid, pos + 1)
            up, r = chain_up(C, cN, aadj, mid, smax)
            goods.append(dn + up)
    segs = list(low)
    cur = pos
    for g in goods[1:]:
        if not g or g[0][0] <= cur:
            continue
        cuts = [cur] + [s for s in splits if cur < s < g[0][0]] + [g[0][0]]
        segs += [(x, y, False) for x, y in zip(cuts, cuts[1:])]
        segs += g
        cur = g[-1][1]
    cuts = [cur] + [s for s in splits if cur < s < smax] + [smax]
    segs += [(x, y, False) for x, y in zip(cuts, cuts[1:])]
    return segs


def bad_of(cov):
    return [s for s in cov if not s[2]]


def check(C, M, COV, SMAX):
    ok = all(C.coverChk(M.cN, M.TS[M.ADJ[r]][2], 16384, SMAX[r], COV[r]) for r in range(M.Q))
    hS = all(M.cN * 32768 <= M.BS[r] * SMAX[r] for r in range(M.Q))
    return ok and hS
