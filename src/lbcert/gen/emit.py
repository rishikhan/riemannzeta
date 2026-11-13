"""Lean text emission: the data module PC9XAData, the instance constants, the weight
declarations and the final constants, spliced into attempt-031's Solution.lean.

Only data and window/weight literals change; every proof text is copied from the base.
"""
import re

B64 = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+_'


def zf(v):
    """zfNat64 literal of v (ZeroForgePackedNat.decode64 inverse)."""
    if v == 0:
        return 'zfNat64 0 "A"'
    bits = v.bit_length()
    assert bits <= 65536
    n = (bits + 5) // 6
    out = []
    for i in range(n):
        out.append(B64[(v >> (6 * (n - 1 - i))) & 63])
    return 'zfNat64 %d "%s"' % (bits, ''.join(out))


def dispatch(prefix, keys, leafname, funname):
    """Balanced dsel/dpk tree over the sorted block indices `keys`.
    -> (list of def lines, top expression)."""
    lines = []

    def rec(a, b):
        if b - a == 1:
            return '(dpk j %d %s)' % (keys[a], leafname(keys[a]))
        m = (a + b) // 2
        left = rec(a, m)
        right = rec(m, b)
        name = '%ss%d_%d' % (prefix, a, b)
        lines.append('def %s (j : ℕ) : ℕ := dsel j %d %s %s' % (name, keys[m], strip(left), strip(right)))
        return '(%s j)' % name

    def strip(e):
        return e
    if not keys:
        top = '0'
    else:
        top = rec(0, len(keys))
    lines.append('def %s (j : ℕ) : ℕ := %s' % (funname, top))
    return lines


def ranges(n, parts):
    step = (n + parts - 1) // parts
    out = []
    a = 0
    while a < n:
        out.append((a, min(step, n - a)))
        a += step
    return out


def chain_add(names):
    e = names[0]
    for nm in names[1:]:
        e = '(Pyr.allFrom_add %s %s)' % (e, nm)
    return e


def emit_pyramids(TOP, BK, TOPD, BKD, parts=5):
    L = []
    L.append('def TOP : ℕ := %s' % zf(TOP))
    keys = sorted(BK)
    for j in keys:
        L.append('def BK_%d : ℕ := %s' % (j, hex(BK[j])))
    L += dispatch('BK', keys, lambda j: 'BK_%d' % j, 'BK')
    L.append('theorem top_ok : Pyr.topOk TOP BK = true := by decide +kernel')
    rs = ranges(512, parts)
    names = []
    for i, (a, n) in enumerate(rs):
        L.append('theorem blk_%d : Pyr.allFrom %d %d (fun j => Pyr.blockOk (BK j) j) = true := by decide +kernel' % (i, a, n))
        names.append('blk_%d' % i)
    L.append('theorem blk_all : Pyr.allFrom 0 512 (fun j => Pyr.blockOk (BK j) j) = true := by')
    L.append('  have h := %s' % chain_add(names))
    L.append('  exact h')
    L.append('theorem lbS : Pyr.LBSound TOP BK := Pyr.lb_sound (Pyr.blocks_of blk_all) top_ok')
    L.append('def TOPD : ℕ := %s' % zf(TOPD))
    keys = sorted(BKD)
    for j in keys:
        L.append('def BKD_%d : ℕ := %s' % (j, zf(BKD[j])))
    L += dispatch('BKD', keys, lambda j: 'BKD_%d' % j, 'BKD')
    L.append('theorem topD_ok : topOk2 TOPD BKD = true := by decide +kernel')
    names = []
    for i, (a, n) in enumerate(ranges(512, parts - 1)):
        L.append('theorem dblk_%d : Pyr.allFrom %d %d (fun j => blockOk2 (BKD j) j) = true := by decide +kernel' % (i, a, n))
        names.append('dblk_%d' % i)
    L.append('theorem dblk_all : Pyr.allFrom 0 512 (fun j => blockOk2 (BKD j) j) = true := by')
    L.append('  have h := %s' % chain_add(names))
    L.append('  exact h')
    L.append('theorem lbD : LBSoundD TOPD BKD := lbDr_sound (blocks2_of dblk_all) topD_ok')
    return L


def emit_reg(REG):
    Ap, Bp, chains = REG
    ch = '[' + ', '.join('[' + ', '.join(str(x) for x in c) + ']' for c in chains) + ']'
    return ['def REG : ℕ × ℕ × List (List ℕ) := (%d, %d, %s)' % (Ap, Bp, ch),
            'theorem hR : rgOk REG = true := by decide +kernel']


def ptt_tree(items):
    """items: sorted list of (j, [(off, word)]) -> PTrD text (BST on x/1024)."""
    if len(items) == 1:
        j, lst = items[0]
        return '(.lf %d [%s])' % (j, ', '.join('(%d, %s)' % (o, hex(w)) for o, w in lst))
    m = len(items) // 2
    return '(.nd %d %s %s)' % (items[m][0], ptt_tree(items[:m]), ptt_tree(items[m:]))


def emit_ptt(words, parts=8):
    """words: {x: stored word} (nonzero only)."""
    byj = {}
    for x in sorted(words):
        byj.setdefault(x // 1024, []).append((x % 1024, words[x]))
    items = sorted(byj.items())
    parts = min(parts, len(items))
    # split into `parts` chunks (power of two count kept as in the base: 8)
    chunks = [items[i * len(items) // parts:(i + 1) * len(items) // parts] for i in range(parts)]
    L = []
    for i, ch in enumerate(chunks):
        L.append('def PTT_%d : PTrD := %s' % (i, ptt_tree(ch)))
        L.append('theorem PTT_%d_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT_%d = true := by decide +kernel' % (i, i))

    def top(a, b):
        if b - a == 1:
            return 'PTT_%d' % a, 'PTT_%d_ok' % a
        m = (a + b) // 2
        l, lp = top(a, m)
        r, rp = top(m, b)
        return '(.nd %d %s %s)' % (chunks[m][0][0], l, r), '(ptOkTD_nd %s %s)' % (lp, rp)
    t, p = top(0, parts)
    if t.startswith('('):
        t = t
    L.append('def PTT : PTrD := %s' % t)
    L.append('theorem PTT_ok : ptOkTD REG TOP BK TOPD BKD 32 4 PTT = true := %s' % p)
    L.append('def PT (x : ℕ) : ℕ := ptGetD PTT x')
    L.append('theorem ptS : ∀ x, PVI x (PT x) := ptTD_sound (n := 32) (csh := 4) lbS lbD hR (by decide) PTT PTT_ok')
    return L


def emit_cover(COV, SMAX, W=1099511627776):
    L = ['def COV : List (List (ℕ × ℕ × Bool)) := [']
    for r, segs in enumerate(COV):
        txt = '[' + ', '.join('(%d, %d, %s)' % (a, b, 'true' if t else 'false') for a, b, t in segs) + ']'
        L.append('  ' + txt + (',' if r < len(COV) - 1 else ']'))
    L.append('def SMAX (r : ℕ) : ℕ := [%s].getD r 0' % ', '.join(str(x) for x in SMAX))
    L.append('def RC (i0 i1 i2 i3 i4 i5 i6 i7 : ℕ) : Cl := rootCl 8 28 %d COV (fun r => [i0, i1, i2, i3, i4, i5, i6, i7].getD r 0)' % W)
    return L


def wl_blocks(stream, nbits, block=32768, extra=600):
    nb = (nbits + block - 1) // block
    mask = (1 << (block + extra)) - 1
    return [(stream >> (block * j)) & mask for j in range(nb)]


def st_text(flat):
    return '⟨' + ', '.join(str(x) for x in flat) + ', 0⟩'


def emit_root(r, idx, stream, nbits, end, cuts=()):
    """cuts: list of (pos, flat_state, cut_end)."""
    L = []
    blocks = wl_blocks(stream, nbits)
    keys = [j for j in range(len(blocks)) if blocks[j]]
    for j in keys:
        L.append('def WL%d_%d : ℕ := %s' % (r, j, zf(blocks[j])))
    L += dispatch('WL%d' % r, keys, lambda j: 'WL%d_%d' % (r, j), 'WL%d' % r)
    L.append('def WD%d : ℕ → ℕ := rdw WL%d' % (r, r))
    ix = ' '.join(str(i) for i in idx)
    if not cuts:
        L.append('theorem rc%d : Covered (RC %s) := rcOf WD%d %d (by decide +kernel) (by decide)' % (r, ix, r, end))
        return L
    entries = []
    for k, (pos, flat, ce) in enumerate(cuts, 1):
        nm = 'CS%d_%d' % (r, k)
        L.append('def %s : St := %s' % (nm, st_text(flat)))
        L.append('theorem wcs%d_%d : U (walkC TOP BK TOPD BKD PT REG WD%d 128 %d) %s = %d := by' % (r, k, r, pos, nm, ce))
        L.append('  decide +kernel')
        L.append('theorem ccs%d_%d : Covered (toCl %s) :=' % (r, k, nm))
        L.append('  covered_of_walkCP lbS lbD ptS hR WD%d 128 %d %d _ wcs%d_%d (by decide)' % (r, pos, ce, r, k))
        entries.append('(%d, %s, %d)' % (pos, nm, ce))
    oks = 'cutsOk_nil'
    for k in range(len(cuts), 0, -1):
        oks = '(cutsOk_cons ccs%d_%d %s)' % (r, k, oks)
    L.append('def CUTS%d : List (ℕ × St × ℕ) := [%s]' % (r, ', '.join(entries)))
    L.append('theorem rc%d : Covered (RC %s) := rcOfC WD%d CUTS%d %s %d (by decide +kernel) (by decide)' % (r, ix, r, r, oks, end))
    return L


def emit_run(lens, W=1099511627776):
    import itertools
    L = []
    hs = ' '.join('(h%d : i%d < %d)' % (r, r, n) for r, n in enumerate(lens))
    L.append('theorem run8 (i0 i1 i2 i3 i4 i5 i6 i7 : ℕ) %s :' % hs)
    L.append('    Covered (rootCl 8 28 %d COV (fun r => [i0, i1, i2, i3, i4, i5, i6, i7].getD r 0)) := by' % W)
    L.append('  match i0, i1, i2, i3, i4, i5, i6, i7, h0, h1, h2, h3, h4, h5, h6, h7 with')
    for k, idx in enumerate(itertools.product(*[range(n) for n in lens])):
        L.append('  | %s, _, _, _, _, _, _, _, _ => exact rc%d' % (', '.join(str(i) for i in idx), k))
    for r, n in enumerate(lens):
        pat = ['_'] * 8
        pat[r] = 'i + %d' % n
        hp = ['_'] * 8
        hp[r] = 'hi'
        L.append('  | %s, %s => exact absurd hi (by omega)' % (', '.join(pat), ', '.join(hp)))
    L.append('theorem run : ∀ idx : ℕ → ℕ, (∀ r < 8, idx r < (badOf (COV.getD r [])).length) → Covered (rootCl 8 28 %d COV idx) := by' % W)
    L.append('  intro idx h')
    L.append('  rw [rootCl_congr (idx\' := fun r => [idx 0, idx 1, idx 2, idx 3, idx 4, idx 5, idx 6, idx 7].getD r 0) (fun r hr => by interval_cases r <;> rfl)]')
    for r, n in enumerate(lens):
        L.append('  have l%d : (badOf (COV.getD %d [])).length = %d := rfl' % (r, r, n))
    L.append('  exact run8 _ _ _ _ _ _ _ _ ' + ' '.join('(l%d ▸ h %d (by norm_num))' % (r, r) for r in range(8)))
    L.append('theorem cert : ∀ g : ℕ → ℝ, (∀ r < 8, 0 ≤ g r) → Pg cN 8 BS TS g :=')
    L.append('  cert_of COV SMAX (by decide) (by decide +kernel) (by decide) %d (by decide) run' % W)
    return L


def splice_data(src, body_lines):
    """Replace the generated part of namespace AMW.Cert.PC9XAData, keeping its header and
    the rcOf / rcOfC theorems verbatim."""
    i0 = src.index('namespace AMW.Cert.PC9XAData\n')
    h = src.index('set_option maxRecDepth 100000\n', i0) + len('set_option maxRecDepth 100000\n')
    r0 = src.index('theorem rcOf {', i0)
    r1 = src.index('def WL0_0', r0)
    e0 = src.index('end AMW.Cert.PC9XAData\n', i0)
    rcof = src[r0:r1]
    pre, post = body_lines
    return src[:h] + '\n'.join(pre) + '\n' + rcof + '\n'.join(post) + '\n' + src[e0:]


# ------------------------------------------------------------------ comments and literals
def comment_mask(src):
    """Boolean per character: inside a /- ... -/ block comment (nesting) or a -- line comment."""
    mask = bytearray(len(src))
    i, depth, n = 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1
            mask[i] = mask[i + 1] = 1
            i += 2
            continue
        if depth and src.startswith('-/', i):
            mask[i] = mask[i + 1] = 1
            depth -= 1
            i += 2
            continue
        if depth:
            mask[i] = 1
            i += 1
            continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                mask[k] = 1
            i = j
            continue
        if src[i] == '"':           # string literal (zfNat64 payloads contain no quotes)
            j = src.index('"', i + 1)
            i = j + 1
            continue
        i += 1
    return mask


def replace_code(src, old, new, mask=None):
    """Replace whole-number occurrences of `old` outside comments."""
    mask = comment_mask(src) if mask is None else mask
    out = []
    last = 0
    cnt = 0
    for m in re.finditer(r'(?<![0-9])%s(?![0-9])' % re.escape(old), src):
        if mask[m.start()]:
            continue
        out.append(src[last:m.start()])
        out.append(new)
        last = m.end()
        cnt += 1
    out.append(src[last:])
    return ''.join(out), cnt


GSUMS = ['g0', 'g1', 'g2', 'g3', 'g4', 'g5', 'g6', 'g7']


def emit_weights(src, BS, AW, cN):
    """BS: 8 ints (b_r * SA); AW: {(i, j): int} for all 0 <= i < j <= 8 (a_ij * SA)."""
    SA = 8388608000000000000000000000000
    TSs = re.search(r'^def TS : List Term := (\[.*\])$', src, re.M).group(1)
    import ast
    TS = ast.literal_eval(TSs)
    newTS = [(i, j, AW[(i, j)], k) for (i, j, a, k) in TS]
    # value map old weight -> new weight inside the instance module (unrolled checker code)
    oldBS = ast.literal_eval(re.search(r'^def BS : List ℕ := (\[.*\])$', src, re.M).group(1))
    vmap = {}
    for (o, n) in [(t[2], AW[(t[0], t[1])]) for t in TS] + list(zip(oldBS, BS)):
        assert vmap.get(o, n) == n, ('inconsistent weight map', o)
        vmap[o] = n
    assert vmap.get(SA, SA) == SA, 'a weight equal to SA must stay SA'
    i0 = src.index('namespace AMW.Cert.PC9XA\n')
    i1 = src.index('end AMW.Cert.PC9XA\n')
    inst = src[i0:i1]
    inst = re.sub(r'(?<![0-9])(\d{25,})(?![0-9])', lambda m: str(vmap.get(int(m.group(1)), int(m.group(1)))), inst)
    src = src[:i0] + inst + src[i1:]
    assert all(AW[(i, j)] == 0 for (i, j) in [(0, 2), (6, 8)])
    src = re.sub(r'^def TS : List Term := \[.*\]$', 'def TS : List Term := [%s]' % ', '.join('(%d, %d, %d, %d)' % t for t in newTS), src, count=1, flags=re.M)
    src = re.sub(r'^def BS : List ℕ := \[.*\]$', 'def BS : List ℕ := [%s]' % ', '.join(str(b) for b in BS), src, count=1, flags=re.M)
    src = re.sub(r'(namespace AMW\.Cert\.PC9XA\n(?:.*\n){0,2}?)def cN : ℕ := \d+', lambda m: m.group(1) + 'def cN : ℕ := %d' % cN, src, count=1)
    # G
    l1 = '  ' + ' + '.join('(%d / (SA:ℝ)) * g%d' % (BS[r], r) for r in range(8))
    parts = []
    for i in range(8):
        for j in range(i + 1, 9):
            parts.append('(%d / (SA:ℝ)) * wfun (%s)' % (AW[(i, j)], ' + '.join(GSUMS[i:j])))
    l2 = '    + ' + ' + '.join(parts)
    src = re.sub(r'(def G \(g0 g1 g2 g3 g4 g5 g6 g7 : ℝ\) : ℝ :=\n).*\n.*\n', lambda m: m.group(1) + l1 + '\n' + l2 + '\n', src, count=1)
    # RiemannFail weights
    for (i, j), v in AW.items():
        src = re.sub(r'^  \| %d, %d => \(\d+ : ℝ\) / %d$' % (i, j, SA), '  | %d, %d => (%d : ℝ) / %d' % (i, j, v, SA), src, count=1, flags=re.M)
        src = re.sub(r'^theorem aW9_%d_%d : aW9 %d %d = \(\d+ : ℝ\) / %d := rfl$' % (i, j, i, j, SA),
                     'theorem aW9_%d_%d : aW9 %d %d = (%d : ℝ) / %d := rfl' % (i, j, i, j, v, SA), src, count=1, flags=re.M)
    for r in range(8):
        src = re.sub(r'^  \| %d => \(\d+ : ℝ\) / %d$' % (r, SA), '  | %d => (%d : ℝ) / %d' % (r, BS[r], SA), src, count=1, flags=re.M)
        src = re.sub(r'^theorem bW9_%d : bW9 %d = \(\d+ : ℝ\) / %d := rfl$' % (r, r, SA),
                     'theorem bW9_%d : bW9 %d = (%d : ℝ) / %d := rfl' % (r, r, BS[r], SA), src, count=1, flags=re.M)
    return src
