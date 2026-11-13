"""Kernel-code levers on the sparse leaf check Z (Lean text), applied to the definitions of a Solution file.

Options (a set of letters):
  y  multiplier step: Cp / Cm read A_c, B_c and x_c straight from the state through a 36-way dispatch (ycs)
     instead of sumR / List.getD on toCl s (yupdS2, ystepH2, ydecH2)
  e  eager record: tzG forces the new record fields and the next offset before the continuation (tzGE)
  q  anchor decode with each repeated subterm forced once (gqF, gptQF)
  u  tzv / tzG bind their intermediate values lazily (letT: k a) instead of forcing them (forceT / forceR)
  v  as u, in ystepH2 as well (needs y)
  x  tzG forces a·2e9·mw and a·sl once (the nine gap updates read the values)
  p  packed gap sums: record (CVP, CN, VP, VN); a term adds a·2e9·mw and a·sl to 256-bit lanes i..j-1 of VP / VN
     by one multiplication with the lane mask of [i, j); zchk reads V_r = KVz + lane_r VP - lane_r VN

bench_defs(SRC, opts, sfx) -> Lean text of the changed kernel definitions (no proofs), with mleaf<sfx> and the
names it needs.
"""
import re

B = 'Bool.rec (motive := fun _ => ℕ)'
PAIRS = [(i, j) for i in range(9) for j in range(i + 2, 10)]


def defn(lines, name, kw='def'):
    TOP = ('def ', 'theorem ', 'abbrev ', 'structure ', 'set_option ', 'local ', 'lemma ', 'end ', 'namespace ', '@[', '/--')
    for i, l in enumerate(lines):
        if l.startswith('%s %s ' % (kw, name)):
            j = i + 1
            while j < len(lines) and not lines[j].startswith(TOP):
                j += 1
            return '\n'.join(lines[i:j]) + '\n'
    raise KeyError(name)


def ycs_text():
    """dispatch on the multiplier index c (PR order): k (A_c) (B_c) (x_c)"""
    def tree(lo, hi):
        if hi - lo == 1:
            i, j = PAIRS[lo]
            return '(k s.A%d%d s.B%d%d (x%d%d s))' % (i, j, i, j, i, j)
        mid = (lo + hi) // 2
        return '(Bool.rec (motive := fun _ => YA) %s %s (Nat.blt c %d))' % (tree(mid, hi), tree(lo, mid), mid)
    return 'def ycs (c : ℕ) (s : St) (k : ℕ → ℕ → ℕ → YA) : YA :=\n  %s\n' % tree(0, 36)


def y_text(lines):
    """yupdS2 / ystepH2 / ydecH2"""
    t = defn(lines, 'yupdS')
    i = t.index('(Nat.add (Nat.add y.Cp')
    head = t[:i]
    head = head.replace('def yupdS ', 'def yupdS2 ').replace(':=\n  ⟨', ':=\n  ycs c s fun a b x => ⟨')
    cpcm = ('(Nat.add (Nat.add y.Cp (Nat.mul Ylo (Nat.sub x a))) (Nat.mul Yhi (Nat.sub b x))), '
            '(Nat.add (Nat.add y.Cm (Nat.mul Ylo (Nat.sub a x))) (Nat.mul Yhi (Nat.sub x b)))⟩\n')
    out = ycs_text() + head + cpcm
    st = defn(lines, 'ystepH').replace('def ystepH ', 'def ystepH2 ').replace('(yupdS c s', '(yupdS2 c s')
    assert 'yupdS2' in st
    dc = defn(lines, 'ydecH').replace('def ydecH ', 'def ydecH2 ').replace('ystepH s qb w ih', 'ystepH2 s qb w ih')
    assert 'ystepH2' in dc
    return out + st + dc


def q_text():
    return ('def gqF (L U jj gs : ℕ) : ℕ :=\n'
            '  forceT (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) (Nat.land jj 63)) 5)) gs) gs) fun xf =>\n'
            '  forceT (Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 gs) 1)) gs) gs) fun lc =>\n'
            '  %s (forceT (Nat.shiftLeft (Nat.shiftRight U gs) gs) fun uf => %s xf uf (Nat.ble uf xf)) lc (Nat.ble xf lc)\n'
            'def gptQF (fs L U jj : ℕ) : ℕ :=\n'
            '  %s (%s (gqF L U jj (%s 8 fs (Nat.beq (Nat.land (Nat.shiftRight jj 6) 1) 1))) U (Nat.beq jj 34)) L (Nat.beq jj 33)\n'
            % (B, B, B, B, B))


LETT = 'def letT {α : Sort _} (a : ℕ) (k : ℕ → α) : α := k a\n'
FRCB = 'def frcB {α : Sort _} (a : ℕ) (k : ℕ → α) : α := Bool.rec (motive := fun _ => α) (k a) (k a) (Nat.beq a 0)\n'


def h_text():
    return ('def gqB (xf lc uf : ℕ) : ℕ := %s (%s xf uf (Nat.ble uf xf)) lc (Nat.ble xf lc)\n'
            'def gqA (L U X gs : ℕ) : ℕ := gqB (Nat.shiftLeft (Nat.shiftRight X gs) gs) '
            '(Nat.shiftLeft (Nat.shiftRight (Nat.add L (Nat.sub (Nat.shiftLeft 1 gs) 1)) gs) gs) (Nat.shiftLeft (Nat.shiftRight U gs) gs)\n'
            'def gptQH (fs L U jj : ℕ) : ℕ :=\n'
            '  %s (%s (gqA L U (Nat.add L (Nat.shiftRight (Nat.mul (Nat.sub U L) (Nat.land jj 63)) 5)) '
            '(%s 8 fs (Nat.beq (Nat.land (Nat.shiftRight jj 6) 1) 1))) U (Nat.beq jj 34)) L (Nat.beq jj 33)\n' % (B, B, B, B, B))


def tzv_text(lines, opts, sfx):
    t = defn(lines, 'tzv').replace('def tzv ', 'def tzv%s ' % sfx)
    if 'q' in opts:
        t = t.replace('gptQG 3 ', 'gptQF 3 ')
    if 'u' in opts:
        t = t.replace('forceT ', 'letT ')
    if 'f' in opts:
        t = t.replace('forceT ', 'frcB ')
    if 'h' in opts:
        t = t.replace('gptQG 3 ', 'gptQH 3 ')
    return t


def tzg_text(lines, opts, sfx):
    t = defn(lines, 'tzG').replace('def tzG ', 'def tzG%s ' % sfx).replace('     tzv top bk f ', '     tzv%s top bk f ' % sfx)
    assert ('tzv%s top' % sfx) in t
    if 'u' in opts:
        t = t.replace('forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>', 'letT eL fun eL => letT eU fun eU => letT e0 fun e0 =>')
    if 'f' in opts:
        t = t.replace('forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>', 'frcB eL fun eL => frcB eU fun eU => frcB e0 fun e0 =>')
    if 'x' in opts:
        i = t.index("     Bool.rec (motive := fun _ => ℕ) (k o' ⟨")
        X, Y = '(Nat.mul a (Nat.mul 2000000000 mw))', '(Nat.mul a sl)'
        assert t.count(X) == 9 and t.count(Y) == 9
        t = t[:i] + t[i:].replace(X, 'xX').replace(Y, 'xY')
        t = t[:i] + '     forceR %s fun xX => forceR %s fun xY =>\n' % (X, Y) + t[i:]
    if 'e' in opts:
        i = t.index("     Bool.rec (motive := fun _ => ℕ) (k o' ⟨")
        j = t.index('⟩) 0 (Nat.beq ok 0))', i)
        rec = t[i + len("     Bool.rec (motive := fun _ => ℕ) (k o' ⟨"):j]
        # split the record's fields at top-level commas
        fl, d, cur = [], 0, ''
        for ch in rec:
            if ch == '(':
                d += 1
            elif ch == ')':
                d -= 1
            if ch == ',' and d == 0:
                fl.append(cur.strip())
                cur = ''
            else:
                cur += ch
        fl.append(cur.strip())
        assert len(fl) == 11, len(fl)
        names = ['q%d' % k for k in range(11)]
        frc = ''.join('forceR (%s) fun %s => ' % (f, n) for f, n in zip(fl, names))
        new = "     Bool.rec (motive := fun _ => ℕ) (forceR o' fun o2 => %sk o2 ⟨%s" % (frc, ', '.join(names))
        t = t[:i] + new + t[j:]
    return t


def packed_text(lines, sfx, chk=False):
    t = defn(lines, 'tzG').replace('def tzG ', 'def tzG%s ' % sfx).replace('     tzv top bk f ', '     tzv%s top bk f ' % sfx)
    t = t.replace('(t : TZ)', '(t : TZP)').replace('(k : ℕ → TZ → ℕ)', '(k : ℕ → TZP → ℕ)')
    i = t.index("     Bool.rec (motive := fun _ => ℕ) (k o' ⟨")
    j = t.index('⟩) 0 (Nat.beq ok 0))', i)
    if chk:
        t = (t[:i] + "     Bool.rec (motive := fun _ => ℕ) (k o' ⟨Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))), "
             "Nat.add t.CN (Nat.mul a cn), Nat.add t.VP (Nat.mul (Nat.mul a (Nat.mul 2000000000 mw)) (lmask i j)), Nat.add t.VN (Nat.mul (Nat.mul a sl) (lmask i j))⟩) 0\n"
             "       (Bool.rec (motive := fun _ => Bool) true (Bool.rec (motive := fun _ => Bool) true (Nat.beq ok 0) (Nat.blt mw 2049)) (Nat.blt sl 8796093022209)))"
             + t[j + len('⟩) 0 (Nat.beq ok 0))'):])
        lm = 'def lmask (i j : ℕ) : ℕ := Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 256 (Nat.sub j i))) 1) LMSK) (Nat.mul 256 i)\n'
    else:
        t = (t[:i] + "     forceR (lmask i j) fun lm => Bool.rec (motive := fun _ => ℕ) (k o' ⟨Nat.add t.CVP (Nat.mul a (Nat.add (Nat.mul 32768 mv) (Nat.mul 10 cp))), "
             "Nat.add t.CN (Nat.mul a cn), Nat.add t.VP (Nat.mul (Nat.mul a (Nat.mul 2000000000 mw)) lm), Nat.add t.VN (Nat.mul (Nat.mul a sl) lm)" + t[j:])
        lm = 'def lmask (i j : ℕ) : ℕ := Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 256 j)) (Nat.shiftLeft 1 (Nat.mul 256 i))) LMSK\n'
    hd = ('structure TZP where\n  (CVP CN VP VN : ℕ)\n'
          'def LMSK : ℕ := %d\n' % ((1 << 256) - 1) + lm +
          'def lane (r x : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 256 r)) LMSK\n')
    z = defn(lines, 'zchk').replace('def zchk ', 'def zchkP ').replace('(t : TZ)', '(t : TZP)')
    for r in range(9):
        z = z.replace('t.V%d ' % r, '(Nat.sub (Nat.add KVz (lane %d t.VP)) (lane %d t.VN)) ' % (r, r))
    assert 't.V' not in z.replace('t.VP', '').replace('t.VN', '')
    zf = defn(lines, 'zfin').replace('def zfin ', 'def zfinP ').replace('(t : TZ)', '(t : TZP)').replace('(zchk s t y)', '(zchkP s t y)')
    return hd + t + z + zf


def split_bodies(t_tzv, t_tzg, sfx):
    '''b: tzv as a dispatcher over one definition per kind; tzG as a dispatcher over its listed path'''
    hdr_v = t_tzv.split('\n')[0]
    body = '\n'.join(t_tzv.split('\n')[1:])
    # body: B (B (B (B k4 k2 (z2)) k0 (z0)) k3 (z3)) k1 (z1)
    def args(x):
        # top-level parenthesised arguments after the head 'Bool.rec (motive := fun _ => ℕ)'
        x = x.strip()
        h = 'Bool.rec (motive := fun _ => ℕ)'
        assert x.startswith(h), x[:60]
        x = x[len(h):].strip()
        out, d, cur = [], 0, ''
        for ch in x:
            if ch == '(':
                d += 1
                if d == 1:
                    cur = ''
                    continue
            if ch == ')':
                d -= 1
                if d == 0:
                    out.append(cur)
                    continue
            if d >= 1:
                cur += ch
        return out
    a1 = args(body)                      # [inner3, k1, beq z 1]
    a3 = args(a1[0])                     # [inner0, k3, beq z 3]
    a0 = args(a3[0])                     # [inner2, k0, beq z 0]
    a2 = args(a0[0])                     # [k4, k2, beq z 2]
    ks = {'1': a1[1], '3': a3[1], '0': a0[1], '4': a2[0], '2': a2[1]}
    sig = hdr_v[hdr_v.index('(top'):hdr_v.index(' :=')]
    out = ''
    call = {}
    for z, k in ks.items():
        nm = 'tzk%s%s' % (z, sfx)
        out += 'def %s %s :=\n  %s\n' % (nm, sig.replace('(z w o', '(w o'), k.strip())
        call[z] = '(%s top bk f w o eL eU e0 k)' % nm
    B_ = 'Bool.rec (motive := fun _ => ℕ)'
    disp = '%s (%s (%s (%s %s %s (Nat.beq z 2)) %s (Nat.beq z 0)) %s (Nat.beq z 3)) %s (Nat.beq z 1)' % (
        B_, B_, B_, B_, call['4'], call['2'], call['0'], call['3'], call['1'])
    out += hdr_v + '\n  ' + disp + '\n'
    # tzG: listed path in its own definition
    lines = t_tzg.rstrip('\n').split('\n')
    hdr_g = lines[0]
    assert lines[1].startswith('  Bool.rec (motive := fun _ => ℕ) (k o t)')
    listed = '\n'.join(lines[2:-1]).strip()
    assert lines[-1].strip() == '(Nat.beq (Nat.land (Nat.shiftRight m n) 1) 1)'
    gsig = hdr_g[hdr_g.index('(top'):hdr_g.index(' :=')]
    nmL = 'tzL' + sfx
    out += 'def %s %s :=\n  %s\n' % (nmL, gsig.replace(' n m w o ', ' w o '), listed[1:-1] if listed.startswith('(') else listed)
    out += hdr_g + '\n  Bool.rec (motive := fun _ => ℕ) (k o t) (%s top bk f i j a eL eU e0 w o t k)\n    %s\n' % (nmL, lines[-1].strip())
    return out


def bench_defs(SRC, opts, sfx):
    lines = SRC.split('\n')
    out = (LETT if ('u' in opts or 'v' in opts) else '') + (FRCB if 'f' in opts else '')
    if 'y' in opts:
        yt = y_text(lines)
        if 'v' in opts:
            yt = yt.replace('forceT ', 'letT ')
        out += yt
    if 'q' in opts:
        out += q_text()
    if 'h' in opts:
        out += h_text()
    tv = tzv_text(lines, opts, sfx)
    tg = packed_text(lines, sfx, 'P' in opts) if ('p' in opts or 'P' in opts) else tzg_text(lines, opts, sfx)
    if 'f' in opts:
        tg = tg.replace('forceR eL fun eL => forceR eU fun eU => forceR e0 fun e0 =>', 'frcB eL fun eL => frcB eU fun eU => frcB e0 fun e0 =>')
    if 'b' in opts:
        if 'p' in opts or 'P' in opts:
            k = tg.index('def tzG')
            out += tg[:k]
            zi = tg.index('def zchkP')
            out += split_bodies(tv, tg[k:zi], sfx) + tg[zi:]
        else:
            out += split_bodies(tv, tg, sfx)
    else:
        out += tv + tg
    ml = defn(lines, 'mleafZ').replace('def mleafZ ', 'def mleaf%s ' % sfx).replace('tzG top bk f', 'tzG%s top bk f' % sfx)
    if 'p' in opts or 'P' in opts:
        ml = re.sub(r'⟨0, 0, KVz(, KVz)*⟩', '⟨0, 0, 0, 0⟩', ml).replace('  zfin s t45', '  zfinP s t45')
    if 'y' in opts:
        ml = ml.replace('(ydecH s 14 w 42', '(ydecH2 s 14 w 42')
    out += ml
    return out


def pwD(x, w):
    w &= (1 << 140) - 1
    return (w & ((1 << 96) - 1)) + (max(0, x - ((w >> 96) & 1048575)) << 96) + ((x + (w >> 116)) << 120)


def read_table(path):
    rows = []
    for l in open(path):
        x, w, n = map(int, l.split())
        rows.append((x, w, n))
    rows.sort()
    return rows


def ptb_tree(rows, lo, hi):
    if hi - lo == 1:
        x, w, n = rows[lo]
        return '(.lf %d %d)' % (x, pwD(x, w))
    mid = (lo + hi) // 2
    return '(.nd %d %s %s)' % (rows[mid][0], ptb_tree(rows, lo, mid), ptb_tree(rows, mid, hi))


def ptb_bench_text(table):
    """BENCH: balanced tree over the table points, leaves hold the looked-up word (pwD applied)"""
    rows = read_table(table)
    return ('inductive PTB where\n  | lf (x g : ℕ)\n  | nd (k : ℕ) (l r : PTB)\n'
            'def ptGetB (t : PTB) (x : ℕ) : ℕ :=\n'
            '  PTB.rec (motive := fun _ => ℕ) (fun k g => Bool.rec (motive := fun _ => ℕ) 0 g (Nat.beq x k))\n'
            '    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt x k)) t\n'
            'def PTB0 : PTB := %s\n'
            'def PTb (x : ℕ) : ℕ := ptGetB PTB0 x\n' % ptb_tree(rows, 0, len(rows)))


def ptb_parts_text(table, parts=32, name='PTBT', single=False):
    """balanced tree over the table points in `parts` named parts (a balanced top tree over PTB_i)"""
    rows = read_table(table)
    n = len(rows)
    cuts = [n * k // parts for k in range(parts + 1)]
    out = ''
    for k in range(parts):
        out += 'def %s_%d : PTB := %s\n' % (name, k, ptb_tree(rows, cuts[k], cuts[k + 1]))

    def top(lo, hi):
        if hi - lo == 1:
            return '%s_%d' % (name, lo)
        mid = (lo + hi) // 2
        return '(.nd %d %s %s)' % (rows[cuts[mid]][0], top(lo, mid), top(mid, hi))
    out += 'def %s : PTB := %s\n' % (name, top(0, parts))
    return out


def ptb_bench_text2(table, parts=32):
    return ('inductive PTB where\n  | lf (x g : ℕ)\n  | nd (k : ℕ) (l r : PTB)\n'
            'def ptGetB (t : PTB) (x : ℕ) : ℕ :=\n'
            '  PTB.rec (motive := fun _ => ℕ) (fun k g => Bool.rec (motive := fun _ => ℕ) 0 g (Nat.beq x k))\n'
            '    (fun k _ _ gl gr => Bool.rec (motive := fun _ => ℕ) gr gl (Nat.blt x k)) t\n'
            + ptb_parts_text(table, parts) + 'def PTb (x : ℕ) : ℕ := ptGetB PTBT x\n')


SLOTS = [(r, r + 1) for r in range(9)] + PAIRS


def slot_text():
    """S: split axis -> (i, j) by a balanced dispatch (slI / slJ) instead of List.getD on SLOTS"""
    def tree(lo, hi, f):
        if hi - lo == 1:
            return str(SLOTS[lo][f])
        mid = (lo + hi) // 2
        return '(%s %s %s (Nat.blt ax %d))' % (B, tree(mid, hi, f), tree(lo, mid, f), mid)
    return ('def slI (ax : ℕ) : ℕ := %s\ndef slJ (ax : ℕ) : ℕ := %s\n'
            'def splitAx2 (ih : WF) (md pos ax : ℕ) : ST :=\n'
            '  forceT (slI ax) fun i => forceT (slJ ax) fun j =>\n'
            '  Bool.rec (motive := fun _ => ST) zK (splG ih pos (qsAx md ax) (colD i) (rowD j) (colD j) (rowD i)) (Nat.blt ax 45)\n'
            % (tree(0, 45, 0), tree(0, 45, 1)))
