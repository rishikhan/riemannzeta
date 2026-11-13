"""Packed encodings for the tangent point table (PTT_k) and the pyramids (TOP/BK, TOPD/BKD).

A payload is a bit string written in the zfNat64 alphabet (A-Z a-z 0-9 + _, 6 bits per character,
most significant bit first, the last character padded with zero bits). Integers are exp-Golomb
codes of order k (`eg`), signed ones zigzag-mapped first (`sg`). The Lean decoder (ZeroForgePack in
the emitted Solution.lean) mirrors `PTT_decode` and `pyr_decode` below step for step.

PTT chunk: eg0 n, then six orders k_dx k_P k_V k_S k_A k_B (eg0 each), then per entry
  x  = x' + 8 (1 + eg k_dx)                       (x' = 0 before the first entry)
  P  = P' + (P' - P'') * dx / dx' + sg k_P        (floor division; P' = P'' = 0, dx' = 1 at the start)
  V  = V' + 10 dx (P' + P - 4e9) / 65536 + sg k_V
  S  = S' + sg k_S, M = 4e9 - P + S
  A  = A' + sg k_A, B = B' + sg k_B               (interval ends ivA, ivB)
  word = V + 2^32 P + 2^64 M + 2^96 (x - A) + 2^116 (B - x)
The entries are grouped by x / 1024 into leaves (x mod 1024, word) and the leaves into the PTrD tree
of gen/emit.py:ptt_tree.

Pyramid (lanes = 1 for TOP/BK, 2 for TOPD/BKD; each lane 32 bits, a field is lanes * 32 bits):
  eg0 nblocks, orders k_j k_r k_leaf k_in k_top (eg0 each), then per block
    j = j' + 1 + eg k_j, r = r' + sg k_r (j' = -1, r' = 0 at the start),
    the 2^(10-r) leaf fields (heap depth 10 - r) per lane: v = 2 v' - v'' + sg k_leaf
      (v', v'' the lane's previous two leaves over all blocks so far, 0 at the start),
    the inner fields bottom-up per lane: v = min(children) - sg k_in;
  block word = r + 2^5 * sum_i field_i 2^(32 lanes i), heap index i = 2^d - 1 + t.
  Then the top heap: 512 fields, field 0 = sg k_top, field h (1 <= h < 512, from h = 511 down)
  per lane = min(child 2h, child 2h + 1) - sg k_top, where the children of h >= 256 are the roots
  (field 0) of blocks 2(h - 256), 2(h - 256) + 1 (0 when the block is absent).
"""

B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+_'
B64I = {c: i for i, c in enumerate(B64)}
FOUR = 4000000000


class W:
    def __init__(self):
        self.bits = []

    def put(self, v, n):
        for i in range(n - 1, -1, -1):
            self.bits.append((v >> i) & 1)

    def eg(self, n, k):
        assert n >= 0
        m = n + (1 << k)
        b = m.bit_length()
        self.bits.extend([0] * (b - 1 - k))
        self.put(m, b)

    def sg(self, v, k):
        self.eg(2 * v if v >= 0 else -2 * v - 1, k)

    def text(self):
        b = self.bits + [0] * (-len(self.bits) % 6)
        return ''.join(B64[int(''.join(map(str, b[i:i + 6])), 2)] for i in range(0, len(b), 6))


def eg_len(n, k):
    return 2 * (n + (1 << k)).bit_length() - 1 - k


def zz(v):
    return 2 * v if v >= 0 else -2 * v - 1


def best_k(vals, signed):
    vs = [zz(v) for v in vals] if signed else vals
    return min(range(40), key=lambda k: sum(eg_len(v, k) for v in vs))


class R:
    def __init__(self, text):
        self.d = [B64I[c] for c in text]
        self.p = 0

    def bit(self):
        q, r = divmod(self.p, 6)
        if q >= len(self.d):
            raise ValueError('payload ends early')
        self.p += 1
        return (self.d[q] >> (5 - r)) & 1

    def bits(self, n):
        v = 0
        for _ in range(n):
            v = 2 * v + self.bit()
        return v

    def eg(self, k):
        z = 0
        while self.bit() == 0:
            z += 1
        return (1 << (z + k)) + self.bits(z + k) - (1 << k)

    def sg(self, k):
        u = self.eg(k)
        return u // 2 if u % 2 == 0 else -(u // 2) - 1

    def done(self):
        # every bit after the last code is padding and must be 0, within the last character
        return len(self.d) == (self.p + 5) // 6 and all(
            ((self.d[q] >> (5 - r)) & 1) == 0 for q, r in (divmod(i, 6) for i in range(self.p, 6 * len(self.d))))


# ---------------------------------------------------------------- PTT

def ptt_fields(entries):
    """entries: sorted [(x, word)] -> per-entry residual tuples (dxc, rP, rV, rS, rA, rB)."""
    out = []
    px, pP, pdP, pdx, pV, pS, pA, pB = 0, 0, 0, 1, 0, 0, 0, 0
    for x, w in entries:
        V = w & 0xffffffff
        P = (w >> 32) & 0xffffffff
        M = (w >> 64) & 0xffffffff
        A = x - ((w >> 96) & 0xfffff)
        B = x + (w >> 116)
        dx = x - px
        assert dx > 0 and dx % 8 == 0
        rP = P - (pP + pdP * dx // pdx)
        rV = V - (pV + 10 * dx * (pP + P - FOUR) // 65536)
        S = M - (FOUR - P)
        out.append((dx // 8 - 1, rP, rV, S - pS, A - pA, B - pB))
        pdP, pdx = P - pP, dx
        px, pP, pV, pS, pA, pB = x, P, V, S, A, B
    assert ptt_decode_fields(out) == list(entries)
    return out


def ptt_decode_fields(fs):
    res = []
    px, pP, pdP, pdx, pV, pS, pA, pB = 0, 0, 0, 1, 0, 0, 0, 0
    for dxc, rP, rV, rS, rA, rB in fs:
        dx = 8 * (dxc + 1)
        x = px + dx
        P = pP + pdP * dx // pdx + rP
        V = pV + 10 * dx * (pP + P - FOUR) // 65536 + rV
        S = pS + rS
        A = pA + rA
        B = pB + rB
        M = FOUR - P + S
        assert 0 <= V < 2**32 and 0 <= P < 2**32 and 0 <= M < 2**32 and 0 <= x - A < 2**20 and B >= x
        res.append((x, V + (P << 32) + (M << 64) + ((x - A) << 96) + ((B - x) << 116)))
        pdP, pdx = P - pP, dx
        px, pP, pV, pS, pA, pB = x, P, V, S, A, B
    return res


def ptt_encode(entries):
    fs = ptt_fields(entries)
    ks = [best_k([f[0] for f in fs], False)] + [best_k([f[i] for f in fs], True) for i in range(1, 6)]
    w = W()
    w.eg(len(fs), 0)
    for k in ks:
        w.eg(k, 0)
    for f in fs:
        w.eg(f[0], ks[0])
        for i in range(1, 6):
            w.sg(f[i], ks[i])
    t = w.text()
    assert ptt_decode(t) == list(entries)
    return t


def ptt_encode_n(entries):
    """entries whose words carry the piece count n - 1 above bit 140 (zfPTTN)"""
    base = [(x, w & ((1 << 140) - 1)) for x, w in entries]
    ns = [w >> 140 for x, w in entries]
    fs = ptt_fields(base)
    ks = [best_k([f[0] for f in fs], False)] + [best_k([f[i] for f in fs], True) for i in range(1, 6)] + [best_k(ns, False)]
    w = W()
    w.eg(len(fs), 0)
    for k in ks:
        w.eg(k, 0)
    for f, n in zip(fs, ns):
        w.eg(f[0], ks[0])
        for i in range(1, 6):
            w.sg(f[i], ks[i])
        w.eg(n, ks[6])
    t = w.text()
    assert ptt_decode_n(t) == list(entries)
    return t


def ptt_decode_n(text):
    r = R(text)
    n = r.eg(0)
    ks = [r.eg(0) for _ in range(7)]
    fs, ns = [], []
    for _ in range(n):
        fs.append((r.eg(ks[0]),) + tuple(r.sg(ks[i]) for i in range(1, 6)))
        ns.append(r.eg(ks[6]))
    assert r.done()
    return [(x, w + (m << 140)) for (x, w), m in zip(ptt_decode_fields(fs), ns)]


def ptt_decode(text):
    r = R(text)
    n = r.eg(0)
    ks = [r.eg(0) for _ in range(6)]
    fs = [(r.eg(ks[0]),) + tuple(r.sg(ks[i]) for i in range(1, 6)) for _ in range(n)]
    assert r.done()
    return ptt_decode_fields(fs)


def ptt_tree_text(entries):
    """Same text as gen/emit.py:ptt_tree on the grouped entries."""
    byj = {}
    for x, w in entries:
        byj.setdefault(x // 1024, []).append((x % 1024, w))
    items = sorted(byj.items())

    def t(items):
        if len(items) == 1:
            j, lst = items[0]
            return '(.lf %d [%s])' % (j, ', '.join('(%d, %s)' % (o, hex(w)) for o, w in lst))
        m = len(items) // 2
        return '(.nd %d %s %s)' % (items[m][0], t(items[:m]), t(items[m:]))
    return t(items)


# ---------------------------------------------------------------- pyramids

def lane(v, l):
    return (v >> (32 * l)) & 0xffffffff


def pyr_decode(text, lanes):
    r = R(text)
    nb = r.eg(0)
    kj, kr, kl, ki, kt = [r.eg(0) for _ in range(5)]
    blocks = {}
    j, rr = -1, 0
    hist = [[0, 0] for _ in range(lanes)]          # per lane: [v'', v']
    fw = 32 * lanes
    for _ in range(nb):
        j += 1 + r.eg(kj)
        rr += r.sg(kr)
        assert 0 <= rr <= 10 and j < 512
        D = 10 - rr
        nf = (1 << (D + 1)) - 1
        F = [[0] * nf for _ in range(lanes)]
        for l in range(lanes):
            for t in range(1 << D):
                v = 2 * hist[l][1] - hist[l][0] + r.sg(kl)
                hist[l] = [hist[l][1], v]
                F[l][(1 << D) - 1 + t] = v
        for l in range(lanes):
            for i in range((1 << D) - 2, -1, -1):
                F[l][i] = min(F[l][2 * i + 1], F[l][2 * i + 2]) - r.sg(ki)
        X = rr
        for i in range(nf):
            for l in range(lanes):
                assert 0 <= F[l][i] < 2**32
                X += F[l][i] << (5 + fw * i + 32 * l)
        blocks[j] = X
    root = {jj: [lane(X >> 5, l) for l in range(lanes)] for jj, X in blocks.items()}
    T = [[0] * 512 for _ in range(lanes)]
    for l in range(lanes):
        T[l][0] = r.sg(kt)
        for h in range(511, 0, -1):
            if h >= 256:
                a = root.get(2 * (h - 256), [0] * lanes)[l]
                b = root.get(2 * (h - 256) + 1, [0] * lanes)[l]
            else:
                a, b = T[l][2 * h], T[l][2 * h + 1]
            T[l][h] = min(a, b) - r.sg(kt)
    top = 0
    for h in range(512):
        for l in range(lanes):
            assert 0 <= T[l][h] < 2**32
            top += T[l][h] << (fw * h + 32 * l)
    assert r.done()
    return top, blocks


def pyr_encode(top, blocks, lanes):
    fw = 32 * lanes
    keys = sorted(blocks)
    J, RR, LF, IN, TP = [], [], [], [], []
    pj, pr = -1, 0
    hist = [[0, 0] for _ in range(lanes)]
    for j in keys:
        X = blocks[j]
        rr = X & 31
        J.append(j - pj - 1); RR.append(rr - pr); pj, pr = j, rr
        D = 10 - rr
        nf = (1 << (D + 1)) - 1
        assert X >> (5 + fw * nf) == 0
        F = [[lane(X >> (5 + fw * i), l) for i in range(nf)] for l in range(lanes)]
        for l in range(lanes):
            for t in range(1 << D):
                v = F[l][(1 << D) - 1 + t]
                LF.append(v - (2 * hist[l][1] - hist[l][0]))
                hist[l] = [hist[l][1], v]
        for l in range(lanes):
            for i in range((1 << D) - 2, -1, -1):
                IN.append(min(F[l][2 * i + 1], F[l][2 * i + 2]) - F[l][i])
    root = {jj: [lane(X >> 5, l) for l in range(lanes)] for jj, X in blocks.items()}
    assert top >> (fw * 512) == 0
    T = [[lane(top >> (fw * h), l) for h in range(512)] for l in range(lanes)]
    for l in range(lanes):
        TP.append(T[l][0])
        for h in range(511, 0, -1):
            if h >= 256:
                a = root.get(2 * (h - 256), [0] * lanes)[l]
                b = root.get(2 * (h - 256) + 1, [0] * lanes)[l]
            else:
                a, b = T[l][2 * h], T[l][2 * h + 1]
            TP.append(min(a, b) - T[l][h])
    ks = [best_k(J, False), best_k(RR, True), best_k(LF, True), best_k(IN, True), best_k(TP, True)]
    w = W()
    w.eg(len(keys), 0)
    for k in ks:
        w.eg(k, 0)
    il = it = 0
    lfi = ini = 0
    for bi, j in enumerate(keys):
        w.eg(J[bi], ks[0]); w.sg(RR[bi], ks[1])
        D = 10 - (blocks[j] & 31)
        for _ in range(lanes << D):
            w.sg(LF[lfi], ks[2]); lfi += 1
        for _ in range(lanes * ((1 << D) - 1)):
            w.sg(IN[ini], ks[3]); ini += 1
    for v in TP:
        w.sg(v, ks[4])
    t = w.text()
    assert pyr_decode(t, lanes) == (top, blocks)
    return t
