"""Exact replay of every finite `decide +kernel` check of the nine-point certificate
in a riemannzeta.fun Solution.lean (attempt-031 layout: AMW.Cert.PC9XA / PC9XAData).

Every function below mirrors one Lean definition (named in its docstring) in exact
integer or rational arithmetic.  The Lean source is the only input: all tables, weights,
window literals and walk bits are read from it (the zfNat64 numerals are decoded with
the same validation as the macro).  Nothing here is a proof; the soundness of each
check is the corresponding Lean theorem (see FORMAT.md).

Representation choice: AMW.G.SZ is a pair (p, n) of naturals with value p - n.  Every
operation the checker applies to an SZ (add/sub/mul/muln/min/max/fl/ce/le/nonneg and the
final readers KAn, W1LO, W1HI, W2L.nonneg, curvatureOk) depends only on the value p - n,
so SZ is a signed Python int here.  Nat.sub truncates (`nsub`), Nat.div by 0 is 0
(`ndiv`), and `ndivc a b = Nat.div (a + b - 1) b`.

Usage:
  python -I replay.py SOLUTION.lean [--workers 4] [--only FAMILY ...] [--mutate]
       [--stats out.json]
Families: decide pv win tb pyr pyrd reg ptt cover roots cuts
"""
import sys, re, ast, time, json, argparse, itertools
from fractions import Fraction
from functools import lru_cache

sys.setrecursionlimit(100000)
try:
    sys.set_int_max_str_digits(0)
except AttributeError:
    pass

# ----------------------------------------------------------------------------------
# Nat helpers
# ----------------------------------------------------------------------------------

def nsub(a, b):
    """Nat.sub (truncated)."""
    return a - b if a > b else 0

def ndiv(a, b):
    """Nat.div (x / 0 = 0)."""
    return a // b if b else 0

def ndivc(a, b):
    """AMW.G.ndivc a b = Nat.div (Nat.sub (a + b) 1) b."""
    return nsub(a + b, 1) // b if b else 0

def fl_sz(v, d):
    """AMW.G.SZ.fl on the value v: floor(v / d) (0 if d = 0)."""
    if d == 0:
        return 0
    return v // d

def ce_sz(v, d):
    """AMW.G.SZ.ce on the value v: ceil(v / d) (0 if d = 0)."""
    if d == 0:
        return 0
    return -((-v) // d)

# ----------------------------------------------------------------------------------
# zfNat64 decoding (ZeroForgePackedNat.decode64, with all its checks)
# ----------------------------------------------------------------------------------

def _digit64(ch):
    c = ord(ch)
    if 65 <= c <= 90: return c - 65
    if 97 <= c <= 122: return c - 97 + 26
    if 48 <= c <= 57: return c - 48 + 52
    if c == 43: return 62
    if c == 95: return 63
    raise ValueError("zfNat64: invalid ASCII digit")

def decode64(bits, text):
    if bits > 65536:
        raise ValueError("zfNat64: bit length exceeds bound")
    if bits == 0:
        if text == "A":
            return 0
        raise ValueError("zfNat64: zero must be A")
    if len(text) != (bits + 5) // 6:
        raise ValueError("zfNat64: encoded length mismatch")
    lead = (bits - 1) % 6 + 1
    lower, upper = 1 << (lead - 1), 1 << lead
    v = 0
    for i, ch in enumerate(text):
        d = _digit64(ch)
        if i == 0 and not (lower <= d < upper):
            raise ValueError("zfNat64: leading digit mismatch")
        v = (v << 6) + d
    assert v.bit_length() == bits
    return v

def decode_source(text):
    count = [0]
    def rep(m):
        count[0] += 1
        return str(decode64(int(m.group(1)), m.group(2)))
    out = re.sub(r'zfNat64\s+(\d+)\s+"([A-Za-z0-9+_]*)"', rep, text)
    return out, count[0]

# ----------------------------------------------------------------------------------
# Lean source model
# ----------------------------------------------------------------------------------

class Model:
    pass

def _num(s):
    s = s.strip()
    return int(s, 16) if s.startswith('0x') else int(s)

def _pylit(s):
    s = s.replace('true', 'True').replace('false', 'False')
    s = re.sub(r'0x[0-9a-fA-F]+', lambda m: str(int(m.group(0), 16)), s)
    return ast.literal_eval(s)

def _tokens(expr):
    return re.findall(r'\(|\)|[^\s()]+', expr)

def _parse_sexpr(expr):
    toks = ['('] + _tokens(expr) + [')']
    pos = [0]
    def p():
        t = toks[pos[0]]; pos[0] += 1
        if t != '(':
            return t
        items = []
        while toks[pos[0]] != ')':
            items.append(p())
        pos[0] += 1
        return items[0] if len(items) == 1 else items
    r = p()
    assert pos[0] == len(toks)
    return r

class Dispatch:
    """Evaluates the balanced `dsel`/`dpk` dispatch functions (AMW.Cert.PyrD.dsel, dpk)."""
    def __init__(self, consts, funs):
        self.consts = consts      # name -> int
        self.funs = funs          # name -> parsed expr (argument j)
    def ev(self, t, j):
        if isinstance(t, str):
            if t == 'j':
                return j
            if re.fullmatch(r'0x[0-9a-fA-F]+|\d+', t):
                return _num(t)
            if t in self.consts:
                return self.consts[t]
            raise KeyError(t)
        head = t[0]
        if head == 'dsel':      # dsel j m a b := if m <= j then b else a
            jj, m = self.ev(t[1], j), self.ev(t[2], j)
            return self.ev(t[4], j) if m <= jj else self.ev(t[3], j)
        if head == 'dpk':       # dpk j k v := if j = k then v else 0
            jj, k = self.ev(t[1], j), self.ev(t[2], j)
            return self.ev(t[3], j) if jj == k else 0
        assert len(t) == 2 and t[1] == 'j', t
        return self.ev(self.funs[head], j)
    def call(self, name, j):
        return self.ev(self.funs[name], j)

def load_model(path):
    raw = open(path, encoding='utf-8').read()
    src, npk = decode_source(raw)
    M = Model()
    M.path = path
    M.raw = raw
    M.src = src
    M.n_packed = npk
    lines = src.split('\n')

    def one(pattern, flags=re.M):
        r = re.findall(pattern, src, flags)
        assert len(r) == 1, (pattern, len(r))
        return r[0]

    # ---- window literals (AMW.cAMn) ----
    blk = one(r'def cAMn : ℕ → ℤ\n((?: \| \d+ => -?\d+\n)+)')
    M.cAMn = {int(a): int(b) for a, b in re.findall(r'\| (\d+) => (-?\d+)', blk)}
    # ---- pvCheck constants ----
    M.sinTabZ = _pylit(one(r'^def sinTabZ : List \(ℤ × ℤ\) := (\[.*\])$'))
    M.pv_rho = Fraction(*map(int, one(r'theorem pvCheck_AM : pvCheck \((\d+) / (\d+)\) = true')))
    M.pv_terms, M.pv_lip, pv_half = map(int, one(r'def cellU \(i : ℕ\) : ℚ := sumQ \(termU i\) (\d+) \+ (\d+) / (\d+)'))
    M.pv_cells = int(one(r'^ tabOk && allQ termOk (\d+) && decide'))   # cells of width 1/(2 pv_cells) on [0, 1/2]
    assert pv_half == 4 * M.pv_cells
    # ---- cell evaluator constants (AMW.G) ----
    g = {}
    for name in ['DZ', 'DZ2', 'PLN', 'PUN', 'E20', 'ERRD', 'E9', 'GAM0', 'GAM1']:
        g[name] = int(one(r'^def %s : ℕ := (\d+)$' % name))
    for name in ['PIC', 'PI2C', 'G1C', 'G2C', 'RHOC', 'SIGC', 'TAUC']:
        a, b = one(r'^def %s : IV := IV.ofN (\d+) (\d+)$' % name)
        g[name] = (int(a), int(b))
    farline = one(r'^ let a := (\(farJ n k XL XU XL2 XU2 .*)$')
    g['FAR'] = [(int(j), int(e), s == 'true') for j, e, s in
                re.findall(r'(?<=[⟩)]) (\d+) (\d+) (true|false)\)', farline)]
    assert [t[0] for t in g['FAR']] == list(range(1, len(g['FAR']) + 1))
    cj = one(r'def CJ \(j : ℕ\) : ℕ × Bool :=\n match j with\n((?:.*\n){3})')
    g['CJ'] = {int(j): (int(m), s == 'true') for j, m, s in
               re.findall(r'\| (\d+) => \((\d+), (true|false)\)', cj)}
    g['CE'] = _pylit(one(r'def CE : List \(ℕ × ℕ × Bool\) :=\n ((?:.*\n){3})').replace('\n', ' '))
    assert [(j, e, s) for (j, e, s) in g['FAR']] == [tuple(t) for t in g['CE']]   # FA unrolls CE
    g['nearK'] = int(one(r'def nearOn \(c : CellA\) : Bool := Nat.beq \(Nat.mod c.k 2\) 0 && Nat.ble 2 c.k && Nat.ble c.k (\d+)'))
    M.G = g
    # ---- AMW.Cert constants ----
    assert re.findall(r'^def SC : ℕ := (\d+)$', src, re.M) == ['32768', '32768']   # AMW.G.SC and AMW.Cert.SC
    M.SC = 32768
    M.KB = int(one(r'^def KB : ℕ := (\d+)$'))
    M.SW = int(one(r'^def SW : ℕ := (\d+)$'))
    M.U1 = int(one(r'^def U1 : ℕ := (\d+)$'))
    M.KU1 = int(one(r'^def KU1 : ℕ := (\d+)$'))
    M.BL8 = int(one(r'^def BL8 : ℕ := (0x[0-9a-f]+)$'), 16)
    M.MAGIC = int(one(r'let t := Nat.land \(Nat.shiftRight (\d+) \(Nat.mul 3 \(Nat.add \(Nat.mul 17 \(Nat.land g 15\)\) \(Nat.sub d \(Nat.sub d 16\)\)\)\)\) 7\n let h := Nat.shiftRight g t\n let v := forceR \(Nat.add \(Nat.shiftLeft \(Nat.add k t\) 40\) h\) fun lh => entry top'))
    mags = re.findall(r'let t := Nat.land \(Nat.shiftRight (\d+) \(Nat.mul 3 ', src)
    assert len(mags) == 2 and all(int(x) == M.MAGIC for x in mags)   # dstep and dstep2 share the table
    M.BB = int(one(r'^def BB : ℕ := (\d+)$'))
    M.TBIAS = int(one(r'^def TB : ℕ := (\d+)$'))
    M.VD = int(one(r'^def VD : ℕ := (\d+)$'))
    # ---- instance PC9XA ----
    i0 = src.index('namespace AMW.Cert.PC9XA\n')
    i1 = src.index('end AMW.Cert.PC9XA\n')
    inst = src[i0:i1]
    def ione(p):
        r = re.findall(p, inst, re.M)
        assert len(r) == 1, (p, len(r))
        return r[0]
    M.cN = int(ione(r'^def cN : ℕ := (\d+)$'))
    M.SIG = int(ione(r'^def SIG : ℕ := (\d+)$'))
    M.SA = int(ione(r'^def SA : ℕ := (\d+)$'))
    M.PR = _pylit(ione(r'^def PR : List \(ℕ × ℕ\) := (\[.*\])$'))
    M.BS = _pylit(ione(r'^def BS : List ℕ := (\[.*\])$'))
    M.TS = _pylit(ione(r'^def TS : List Term := (\[.*\])$'))
    M.SL = _pylit(ione(r'^def SL : List ℕ := (\[.*\])$'))
    M.BND = _pylit(ione(r'^def BND : List ℕ := (\[.*\])$'))
    M.ADJ = _pylit(ione(r'^def ADJ : List ℕ := (\[.*\])$'))
    M.TBL = [tuple(e) for e in _pylit(ione(r'^def TB : List \(ℕ × ℕ × ℕ\) := (\[.*\])$'))]
    # leaf decoder parameters, fixed in mleafP / mleafV
    decs = re.findall(r'^  dec4QG (\d+) (\d+) w o0 ', inst, re.M)
    assert len(decs) == 2 and decs[0] == decs[1]
    M.FS, M.LB = int(decs[0][0]), int(decs[0][1])
    yd = re.findall(r'\(ydecS s (\d+) w (\d+) ⟨o34,', inst)
    assert len(yd) == 2 and yd[0] == yd[1]
    M.QB, M.YFUEL = int(yd[0][0]), int(yd[0][1])
    M.Q = 8
    M.NP = len(M.PR)
    # ---- data module PC9XAData ----
    d0 = src.index('namespace AMW.Cert.PC9XAData\n')
    d1 = src.index('end AMW.Cert.PC9XAData\n')
    data = src[d0:d1]
    M.data_offset_line = src[:d0].count('\n') + 1
    consts = {}
    for name, val in re.findall(r'^def (\w+) : ℕ := (0x[0-9a-f]+|\d+)$', data, re.M):
        consts[name] = _num(val)
    funs = {}
    for name, expr in re.findall(r'^def (\w+) \(j : ℕ\) : ℕ := (.+)$', data, re.M):
        funs[name] = _parse_sexpr(expr)
    M.disp = Dispatch(consts, funs)
    M.TOP = consts['TOP']
    M.TOPD = consts['TOPD']
    M.WMASK = int(one(r'^def WMASK : ℕ := (\d+)$'))
    M.BKv = {j: M.disp.call('BK', j) for j in range(512)}
    M.BKDv = {j: M.disp.call('BKD', j) for j in range(512)}
    M.n_BK_blocks = sum(1 for k in consts if re.fullmatch(r'BK_\d+', k))
    M.n_BKD_blocks = sum(1 for k in consts if re.fullmatch(r'BKD_\d+', k))
    reg = re.findall(r'^def REG : ℕ × ℕ × List \(List ℕ\) := \((\d+), (\d+), (\[.*\])\)$', data, re.M)
    assert len(reg) == 1
    M.REG = (int(reg[0][0]), int(reg[0][1]), _pylit(reg[0][2]))
    # tangent point tree
    M.PTT = {}
    for name, expr in re.findall(r'^def (PTT(?:_\d+)?) : PTrD := (.+)$', data, re.M):
        M.PTT[name] = parse_ptrd(expr, M.PTT)
    M.ptt_checks = re.findall(r'^theorem (PTT_\d+)_ok : ptOkTD REG TOP BK TOPD BKD (\d+) (\d+) PTT_\d+ = true := by decide \+kernel$', data, re.M)
    covtxt = re.findall(r'^def COV : List \(List \(ℕ × ℕ × Bool\)\) := \[\n((?:  .*\n)+)', data, re.M)
    assert len(covtxt) == 1
    M.COV = _pylit('[' + covtxt[0].replace('\n', ' '))
    M.SMAX = _pylit(re.findall(r'^def SMAX \(r : ℕ\) : ℕ := (\[.*\])\.getD r 0$', data, re.M)[0])
    M.RCW = int(re.findall(r'^def RC \(i0 i1 i2 i3 i4 i5 i6 i7 : ℕ\) : Cl := rootCl 8 28 (\d+) COV', data, re.M)[0])
    certw = re.findall(r'cert_of COV SMAX \(by decide\) \(by decide \+kernel\) \(by decide\) (\d+) \(by decide\) run', data)
    assert len(certw) == 1
    M.CERTW = int(certw[0])
    # walk words: WD r = rdw WL r
    M.WD = {}
    for r, wl in re.findall(r'^def WD(\d+) : ℕ → ℕ := rdw (WL\d+)$', data, re.M):
        M.WD[int(r)] = wl
    M.WLblocks = {}
    for name in set(M.WD.values()):
        blocks = {}
        for k, v in consts.items():
            m = re.fullmatch(name + r'_(\d+)', k)
            if m:
                blocks[int(m.group(1))] = v
        nb = max(blocks) + 1
        M.WLblocks[name] = [M.disp.call(name, j) for j in range(nb + 1)]
    # cut states and cut walks
    M.CS = {}
    for name, body in re.findall(r'^def (CS\d+_\d+) : St := ⟨([\d, ]+)⟩$', data, re.M):
        vals = [int(x) for x in body.split(',')]
        assert len(vals) == 2 * M.Q + 2 * M.NP + 1
        M.CS[name] = vals
    M.WCS = []
    for name, wd, fuel, pos, csn, e in re.findall(
            r'^theorem (wcs\d+_\d+) : U \(walkC TOP BK TOPD BKD PT REG (WD\d+) (\d+) (\d+)\) (CS\d+_\d+) = (\d+) := by\n  decide \+kernel$', data, re.M):
        M.WCS.append(dict(name=name, wd=int(wd[2:]), fuel=int(fuel), pos=int(pos), cs=csn, e=int(e)))
    M.CUTS = {}
    for r, body in re.findall(r'^def CUTS(\d+) : List \(ℕ × St × ℕ\) := \[(.*)\]$', data, re.M):
        M.CUTS[int(r)] = [(int(p), c, int(e)) for p, c, e in re.findall(r'\((\d+), (CS\d+_\d+), (\d+)\)', body)]
    M.ROOTS = []
    for r, idx, wd, e in re.findall(
            r'^theorem rc(\d+) : Covered \(RC ([\d ]+)\) := rcOf (WD\d+) (\d+) \(by decide \+kernel\) \(by decide\)$', data, re.M):
        M.ROOTS.append(dict(r=int(r), idx=tuple(map(int, idx.split())), wd=int(wd[2:]), e=int(e), cuts=None))
    for r, idx, wd, cuts, e in re.findall(
            r'^theorem rc(\d+) : Covered \(RC ([\d ]+)\) := rcOfC (WD\d+) (CUTS\d+) \(cutsOk_cons [^\n]*\) (\d+) \(by decide \+kernel\) \(by decide\)$', data, re.M):
        M.ROOTS.append(dict(r=int(r), idx=tuple(map(int, idx.split())), wd=int(wd[2:]), e=int(e), cuts=int(cuts[4:])))
    M.ROOTS.sort(key=lambda d: d['r'])
    M.FUEL = 128
    M.dk_lines = [i + 1 for i, L in enumerate(lines) if 'decide +kernel' in L]
    return M

def parse_ptrd(expr, env):
    """Parses a PTrD literal: (.nd k l r) / (.lf j [(off, word), ...]) / PTT_i references."""
    toks = re.findall(r'\.nd|\.lf|\[[^\]]*\]|PTT_\d+|\d+|\(|\)', expr)
    pos = [0]
    def p():
        t = toks[pos[0]]; pos[0] += 1
        if t == '(':
            r = p(); assert toks[pos[0]] == ')'; pos[0] += 1; return r
        if t.startswith('PTT_'):
            return env[t]
        if t == '.nd':
            k = int(toks[pos[0]]); pos[0] += 1
            l = p(); r = p()
            return ('nd', k, l, r)
        if t == '.lf':
            j = int(toks[pos[0]]); pos[0] += 1
            L = _pylit(toks[pos[0]]); pos[0] += 1
            return ('lf', j, [tuple(e) for e in L])
        raise ValueError(t)
    r = p()
    assert pos[0] == len(toks)
    return r

# ----------------------------------------------------------------------------------
# AMW.G cell evaluator (CellA), window dependent
# ----------------------------------------------------------------------------------

class CellEval:
    """AMW.G.CellA and its readers; IV = (lo, hi) of signed ints (SZ values)."""
    def __init__(self, M):
        g = M.G
        self.SC = 32768
        self.DZ = g['DZ']; self.DZ2 = g['DZ2']; self.PLN = g['PLN']; self.PUN = g['PUN']
        self.E20 = g['E20']; self.ERRD = g['ERRD']; self.E9 = g['E9']
        self.GAM0 = g['GAM0']; self.GAM1 = g['GAM1']
        self.PIC = g['PIC']; self.PI2C = g['PI2C']; self.G1C = g['G1C']; self.G2C = g['G2C']
        self.RHOC = g['RHOC']; self.SIGC = g['SIGC']; self.TAUC = g['TAUC']
        self.FAR = g['FAR']; self.CJt = g['CJ']; self.nearK = g['nearK']
        DZ = self.DZ
        self.DZp = [DZ ** k for k in range(12)]
        self.CDEN = 3628800 * DZ ** 9
        self.SDEN = 39916800 * DZ ** 10
        self.SCDEN = 39916800 * DZ ** 9
        self.S1DEN = 3991680 * DZ ** 8
        self.S2DEN = 39916800 * DZ ** 9
        self.cache = {}
    # polynomial numerators (AMW.G.cosP ... s2N)
    def cosP(self, T): D = self.DZp; return 3628800 * D[10] + 151200 * T**4 * D[6] + 90 * T**8 * D[2]
    def cosN(self, T): D = self.DZp; return 1814400 * T**2 * D[8] + 5040 * T**6 * D[4] + T**10
    def sinP(self, T): D = self.DZp; return 39916800 * T * D[10] + 332640 * T**5 * D[6] + 110 * T**9 * D[2]
    def sinN(self, T): D = self.DZp; return 6652800 * T**3 * D[8] + 7920 * T**7 * D[4] + T**11
    def scP(self, T): D = self.DZp; return 39916800 * D[10] + 332640 * T**4 * D[6] + 110 * T**8 * D[2]
    def scN(self, T): D = self.DZp; return 6652800 * T**2 * D[8] + 7920 * T**6 * D[4] + T**10
    def s1P(self, T): D = self.DZp; return 133056 * T**3 * D[6] + 88 * T**7 * D[2]
    def s1N(self, T): D = self.DZp; return 1330560 * T * D[8] + 4752 * T**5 * D[4] + T**9
    def s2P(self, T): D = self.DZp; return 3991680 * T**2 * D[8] + 6160 * T**6 * D[4] + T**10
    def s2N(self, T): D = self.DZp; return 13305600 * D[10] + 237600 * T**4 * D[6] + 90 * T**8 * D[2]
    # IV operations (AMW.G.IV)
    def mul(self, I, J):
        ps = (I[0] * J[0], I[0] * J[1], I[1] * J[0], I[1] * J[1])
        return (fl_sz(min(ps), self.DZ), ce_sz(max(ps), self.DZ))
    def mulc(self, C, I):
        lo = C[0] * I[0] if I[0] >= 0 else C[1] * I[0]
        hi = C[1] * I[1] if I[1] >= 0 else C[0] * I[1]
        return (fl_sz(lo, self.DZ), ce_sz(hi, self.DZ))
    @staticmethod
    def add(I, J): return (I[0] + J[0], I[1] + J[1])
    @staticmethod
    def sub(I, J): return (I[0] - J[1], I[1] - J[0])
    @staticmethod
    def neg(I): return (-I[1], -I[0])
    @staticmethod
    def muln(m, I): return (m * I[0], m * I[1])
    @staticmethod
    def divn(I, d): return (fl_sz(I[0], d), ce_sz(I[1], d))
    def divp(self, I, e0, e1):
        DZ = self.DZ
        lo = fl_sz(I[0] * DZ, e1) if I[0] >= 0 else fl_sz(I[0] * DZ, e0)
        hi = ce_sz(I[1] * DZ, e0) if I[1] >= 0 else ce_sz(I[1] * DZ, e1)
        return (lo, hi)
    def scl(self, ng, m, I):
        r = self.muln(m, I)
        return self.neg(r) if ng else r
    # far sum (AMW.G.farJ / CellA.FA)
    def FA(self, n, k, XL, XU):
        DZ = self.DZ
        XL2, XU2 = XL * XL, XU * XU
        pl = ph = nl = nh = 0
        for (j, e, sg) in self.FAR:
            J = j * DZ; J2 = J * J
            if 2 * j == k:
                ng = sg ^ (n == 1)
                m0 = ndiv(self.DZp[n + 2], self.hden(n, XU + J))
                m1 = ndivc(self.DZp[n + 2], self.hden(n, XL + J))
            elif 2 * j < k:
                ng = sg ^ (True if n == 1 else (not True))
                m0 = ndiv(self.mnum(n, XU, XU2, J2), nsub(XU2, J2) ** (n + 1))
                m1 = ndivc(self.mnum(n, XL, XL2, J2), nsub(XL2, J2) ** (n + 1))
            else:
                ng = sg ^ (True if n == 1 else (not False))
                m0 = ndiv(self.mnum(n, XL, XL2, J2), nsub(J2, XL2) ** (n + 1))
                m1 = ndivc(self.mnum(n, XU, XU2, J2), nsub(J2, XU2) ** (n + 1))
            if not ng:
                pl += e * m0; ph += e * m1
            else:
                nl += e * m0; nh += e * m1
        return self.divn((pl - nh, ph - nl), self.E9)
    def mnum(self, n, X, X2, J2):
        D = self.DZp
        if n == 0: return X * D[2]
        if n == 1: return (X2 + J2) * D[3]
        return 2 * X * (X2 + 3 * J2) * D[4]
    @staticmethod
    def hden(n, Y):
        if n == 0: return 2 * Y
        if n == 1: return 2 * (Y * Y)
        return Y ** 3
    def CJ(self, j):
        return self.CJt.get(j, (0, False))

    def cell(self, LN, UN):
        """All CellA readers the checker uses, for the cell [LN/SC, UN/SC]."""
        key = (LN, UN)
        r = self.cache.get(key)
        if r is not None:
            return r
        if len(self.cache) > 400000:
            self.cache.clear()
        r = self._cell(LN, UN)
        self.cache[key] = r
        return r

    def _cell(self, LN, UN):
        SC, DZ = self.SC, self.DZ
        k = ndiv(2 * (LN + UN) + SC, 2 * SC)
        side = k * SC <= 2 * LN
        LLO = ndiv(LN * DZ, SC)
        UHI = ndivc(UN * DZ, SC)
        AD = k * self.DZ2
        RLO = nsub(LLO, AD) if side else nsub(AD, UHI)
        RHI = nsub(UHI, AD) if side else nsub(AD, LLO)
        TLZ = ndiv(self.PLN * RLO, self.E20)
        TUZ = ndivc(self.PUN * RHI, self.E20)
        BLZ = ndiv(self.PLN * LLO, self.E20)
        BUZ = ndivc(self.PUN * UHI, self.E20)
        E0 = nsub(ndiv(2 * (BLZ * BLZ), DZ), DZ)
        E1 = nsub(ndivc(2 * (BUZ * BUZ), DZ), DZ)
        ok = (LN <= UN and TUZ <= DZ and
              ((k * SC <= 2 * LN) if side else (2 * UN <= k * SC)) and 0 < E0)
        res = {'ok': ok, 'k': k, 'E0': E0}
        # the readers below are evaluated whatever `ok` is (Lean evaluates them lazily, the values agree)
        ERRD = self.ERRD
        CI = (ndiv(nsub(self.cosP(TUZ), self.cosN(TUZ)), self.CDEN) - ERRD,
              ndivc(nsub(self.cosP(TLZ), self.cosN(TLZ)), self.CDEN) + ERRD)
        SI = (ndiv(nsub(self.sinP(TLZ), self.sinN(TLZ)), self.SDEN) - ERRD,
              ndivc(nsub(self.sinP(TUZ), self.sinN(TUZ)), self.SDEN) + ERRD)
        km4 = k % 4
        neg = self.neg
        if km4 == 0:
            CX = CI; SX = SI if side else neg(SI)
        elif km4 == 1:
            CX = neg(SI) if side else SI; SX = CI
        elif km4 == 2:
            CX = neg(CI); SX = neg(SI) if side else SI
        else:
            CX = SI if side else neg(SI); SX = neg(CI)
        BI = (BLZ, BUZ)
        PG = (ndiv(self.GAM0 * BLZ, DZ), ndivc(self.GAM1 * BUZ, DZ))
        NI = self.sub(CX, self.mulc(PG, SX))
        EI = (E0, E1)
        near = (k % 2 == 0) and 2 <= k and k <= self.nearK
        S0 = (fl_sz(self.scP(TLZ) - self.scN(TUZ), self.SCDEN) - ERRD,
              ce_sz(self.scP(TUZ) - self.scN(TLZ), self.SCDEN) + ERRD)
        G1 = (fl_sz(self.s1P(TLZ) - self.s1N(TUZ), self.S1DEN) - 2 * ERRD,
              ce_sz(self.s1P(TUZ) - self.s1N(TLZ), self.S1DEN) + 2 * ERRD)
        G2 = (fl_sz(self.s2P(TLZ) - self.s2N(TUZ), self.S2DEN) - 5 * ERRD,
              ce_sz(self.s2P(TUZ) - self.s2N(TLZ), self.S2DEN) + 5 * ERRD)
        j0 = k // 2
        mag, sg = self.CJ(j0)
        zero = (0, 0)
        B0 = self.divn(self.scl(sg, mag, S0), 2 * self.E9) if near else zero
        B1 = self.divn(self.scl(sg, mag, self.mulc(self.PIC, G1 if side else neg(G1))), 2 * self.E9) if near else zero
        B2 = self.divn(self.scl(sg, mag, self.mulc(self.PI2C, G2)), 2 * self.E9) if near else zero
        FA0 = self.FA(0, k, LLO, UHI)
        FA1 = self.FA(1, k, LLO, UHI)
        FA2 = self.FA(2, k, LLO, UHI)
        SF0 = self.mul(SX, FA0)
        K0 = self.add(self.divp(neg(NI), E0, E1), self.add(self.mulc(self.SIGC, SF0), self.mulc(self.RHOC, B0)))
        MI = self.add(self.mulc(EI, self.add(self.mulc(self.G1C, SX), self.mulc(PG, CX))),
                      self.mulc(self.muln(4, BI), NI))
        E2L = ndiv(E0 * E0, DZ)
        E2U = ndivc(E1 * E1, DZ)
        K1 = self.add(self.mulc(self.PIC, self.divp(MI, E2L, E2U)),
                      self.add(self.add(self.mulc(self.RHOC, self.mul(CX, FA0)),
                                        self.mulc(self.SIGC, self.mul(SX, FA1))),
                               self.mulc(self.RHOC, B1)))
        N2 = self.sub(self.mulc(PG, SX), self.mulc(self.G2C, CX))
        E3L = ndiv(E2L * E0, DZ)
        E3U = ndivc(E2U * E1, DZ)
        PP = self.add(self.sub(self.mulc((E2L, E2U), N2), self.muln(4, self.mulc(EI, NI))),
                      self.muln(8, self.mulc(BI, MI)))
        K2 = self.add(neg(self.mulc(self.PI2C, self.divp(PP, E3L, E3U))),
                      self.add(self.sub(self.muln(2, self.mulc(self.RHOC, self.mul(CX, FA1))),
                                        self.mulc(self.TAUC, SF0)),
                               self.add(self.mulc(self.SIGC, self.mul(SX, FA2)), self.mulc(self.RHOC, B2))))
        KA = max(0, max(K0[0], -K0[1]))
        KAn = max(KA, 0)
        W1 = self.muln(2, self.mul(K0, K1))
        mabsK1 = max(0, max(K1[0], -K1[1]))
        W2L = mabsK1 * mabsK1 + self.mul(K0, K2)[0] * DZ
        res.update(KAn=KAn, E2L=E2L, E3L=E3L, W1=W1, W2L=W2L, K0=K0, K1=K1, K2=K2)
        return res

# ----------------------------------------------------------------------------------
# Checker
# ----------------------------------------------------------------------------------

class Checker:
    def __init__(self, M):
        self.M = M
        self.CE = CellEval(M)
        self.SC = 32768
        self.KB = M.KB; self.SW = M.SW; self.KU1 = M.KU1
        self.DZ = M.G['DZ']
        # pyramid levels (lb domain x < 2^(PLV-1)) and convexity-region count; the Lean checker has 20 and 16.
        # A model may raise them (M.PLV = 21, M.NREG = 32: domain 2^20, regions to 31 SC; q12x m12r_x).
        self.PLV = getattr(M, 'PLV', 20)
        self.NREG = getattr(M, 'NREG', 16)
        self.LBCUT = (1 << (self.PLV - 1)) + 1
        self.lb_cache = {}
        self.lbd_cache = {}
        self.pt_cache = {}
        self.stats = {}

    # ---- AMW.Cert.CellN readers ----
    def okC(self, LN, UN):
        return self.CE.cell(LN, UN)['ok']
    def WZ(self, LN, UN):
        """CellN.WZ: floor(KAn^2 SW / DZ^2) if ok, else 0."""
        c = self.CE.cell(LN, UN)
        if not c['ok']:
            return 0
        return ndiv(c['KAn'] * c['KAn'] * self.SW, self.DZ * self.DZ)
    def okD(self, LN, UN):
        c = self.CE.cell(LN, UN)
        return c['ok'] and 0 < c['E2L']
    def W1LO(self, LN, UN):
        return fl_sz(self.CE.cell(LN, UN)['W1'][0], 1000000)
    def W1HI(self, LN, UN):
        return ce_sz(self.CE.cell(LN, UN)['W1'][1], 1000000)
    def convOk(self, LN, UN):
        c = self.CE.cell(LN, UN)
        return c['ok'] and 0 < c['E2L'] and 0 < c['E3L'] and c['W2L'] >= 0
    def cellOkCore(self, LN, UN, v):
        """Pyr.cellOkCore: okC && v*1000*DZ^2 <= KAn^2*SW (w >= v/1e10 on the cell)."""
        c = self.CE.cell(LN, UN)
        return c['ok'] and v * 1000 * self.DZ * self.DZ <= c['KAn'] * c['KAn'] * self.SW

    # ---- Pyr: value pyramid (AMW.Cert.Pyr) ----
    @staticmethod
    def fld(X, i): return (X >> (32 * i)) & 0xFFFFFFFF
    def cellOk(self, l, i, v):
        if v == 0:
            return True
        if not (((i + 1) << l) + 1 <= self.KB):
            return False
        return self.cellOkCore(i << l, (i + 1) << l, v)
    def blockOkX(self, X, j):
        r = X & 31
        D = nsub(10, r)
        Y = X >> 5
        if not r <= 10:
            return False
        for t in range(1 << D):
            if not self.cellOk(r, (j << D) + t, self.fld(Y, nsub(1 << D, 1) + t)):
                return False
        for d in range(D):
            for t in range(1 << d):
                a = self.fld(Y, nsub(1 << d, 1) + t)
                b0 = self.fld(Y, nsub(1 << (d + 1), 1) + 2 * t)
                b1 = self.fld(Y, nsub(1 << (d + 1), 1) + 2 * t + 1)
                if not a <= min(b0, b1):
                    return False
        return True
    def blockOk(self, X, j):
        return True if X == 0 else self.blockOkX(X, j)
    def topv(self, top, bk, l, i):
        if l == 10:
            return self.fld(bk(i) >> 5, 0)
        return self.fld(top, (1 << nsub(self.PLV - 1, l)) + i)
    def topOk(self, top, bk):
        for l in range(11, self.PLV):
            for i in range(1 << nsub(self.PLV - 1, l)):
                a = self.fld(top, (1 << nsub(self.PLV - 1, l)) + i)
                if not a <= min(self.topv(top, bk, l - 1, 2 * i), self.topv(top, bk, l - 1, 2 * i + 1)):
                    return False
        return True
    def BK(self, j):
        v = self.M.BKv.get(j)
        return v if v is not None else self.M.disp.call('BK', j)
    def BKD(self, j):
        v = self.M.BKDv.get(j)
        return v if v is not None else self.M.disp.call('BKD', j)
    def entry(self, l, i):
        if 11 <= l:
            if self.PLV <= l:
                return 0
            return self.fld(self.M.TOP, (1 << nsub(self.PLV - 1, l)) + i)
        j = i >> nsub(10, l)
        X = self.BK(j)
        kk = l + nsub(X & 31, l)
        d = nsub(10, kk)
        return self.fld(X >> 5, nsub(1 << d, 1) + nsub(i >> nsub(kk, l), j << d))
    def blen(self, x):
        BL8 = self.M.BL8
        if 256 <= x:
            return 8 + ((BL8 >> (4 * (x >> 8))) & 15)
        return (BL8 >> (4 * x)) & 15
    def dcov(self, k, ib, g, entry, mn):
        """Pyr.dcov / PyrD.dcov2: 14 nested dstep."""
        E = ib + 1
        MAGIC = self.M.MAGIC
        def step(n, g):
            if n == 0:
                return 0
            d = nsub(E, g)
            t = (MAGIC >> (3 * (17 * (g & 15) + nsub(d, nsub(d, 16))))) & 7
            h = g >> t
            lh = ((k + t) << 40) + h
            v = entry(lh >> 40, lh & 1099511627775)
            nxt = (h + 1) << t
            if E <= nxt:
                return v
            return mn(v, step(n - 1, nxt))
        return step(14, g)
    def lb(self, lo, hi):
        """Pyr.lb (= lbF): lower bound of 1e10 * w on [lo/SC, hi/SC]."""
        key = (lo, hi)
        r = self.lb_cache.get(key)
        if r is not None:
            return r
        if hi <= lo or self.LBCUT <= hi:
            r = 0
        else:
            k = self.blen(nsub(hi, lo) >> 5)
            r = self.dcov(k, nsub(hi, 1) >> k, lo >> k, self.entry, min)
        if len(self.lb_cache) > 2000000:
            self.lb_cache.clear()
        self.lb_cache[key] = r
        return r

    # ---- PyrD: derivative pyramid ----
    @staticmethod
    def fld2(X, i): return (X >> (64 * i)) & 0xFFFFFFFFFFFFFFFF
    @staticmethod
    def lo32(v): return v & 0xFFFFFFFF
    @staticmethod
    def hi32(v): return v >> 32
    @staticmethod
    def pmin(a, b):
        return min(a & 0xFFFFFFFF, b & 0xFFFFFFFF) + (min(a >> 32, b >> 32) << 32)
    @staticmethod
    def ple(a, b):
        return (a & 0xFFFFFFFF) <= (b & 0xFFFFFFFF) and (a >> 32) <= (b >> 32)
    def cellOkD(self, sgn, l, i, v):
        if v == 0:
            return True
        if not (((i + 1) << l) + 1 <= self.KB):
            return False
        LN, UN = i << l, (i + 1) << l
        if not self.okD(LN, UN):
            return False
        if sgn:
            return v <= self.KU1 + self.W1LO(LN, UN)
        return v <= self.KU1 - self.W1HI(LN, UN)
    def cellOk2(self, l, i, v):
        return self.cellOkD(True, l, i, self.lo32(v)) and self.cellOkD(False, l, i, self.hi32(v))
    def blockOk2X(self, X, j):
        r = X & 31
        D = nsub(10, r)
        Y = X >> 5
        if not r <= 10:
            return False
        for t in range(1 << D):
            if not self.cellOk2(r, (j << D) + t, self.fld2(Y, nsub(1 << D, 1) + t)):
                return False
        for d in range(D):
            for t in range(1 << d):
                a = self.fld2(Y, nsub(1 << d, 1) + t)
                b = self.pmin(self.fld2(Y, nsub(1 << (d + 1), 1) + 2 * t),
                              self.fld2(Y, nsub(1 << (d + 1), 1) + 2 * t + 1))
                if not self.ple(a, b):
                    return False
        return True
    def blockOk2(self, X, j):
        return True if X == 0 else self.blockOk2X(X, j)
    def topv2(self, top, bk, l, i):
        if l == 10:
            return self.fld2(bk(i) >> 5, 0)
        return self.fld2(top, (1 << nsub(self.PLV - 1, l)) + i)
    def topOk2(self, top, bk):
        for l in range(11, self.PLV):
            for i in range(1 << nsub(self.PLV - 1, l)):
                a = self.fld2(top, (1 << nsub(self.PLV - 1, l)) + i)
                if not self.ple(a, self.pmin(self.topv2(top, bk, l - 1, 2 * i), self.topv2(top, bk, l - 1, 2 * i + 1))):
                    return False
        return True
    def entry2(self, l, i):
        if 11 <= l:
            if self.PLV <= l:
                return 0
            return self.fld2(self.M.TOPD, (1 << nsub(self.PLV - 1, l)) + i)
        j = i >> nsub(10, l)
        X = self.BKD(j)
        kk = l + nsub(X & 31, l)
        d = nsub(10, kk)
        return self.fld2(X >> 5, nsub(1 << d, 1) + nsub(i >> nsub(kk, l), j << d))
    def lbDr(self, lo, hi):
        """PyrD.lbDr (= lbDrF): packed (lo32: 1e9 (w'+2) lower, hi32: 1e9 (2-w') lower)."""
        key = (lo, hi)
        r = self.lbd_cache.get(key)
        if r is not None:
            return r
        if hi <= lo or self.LBCUT <= hi:
            r = 0
        else:
            k = self.blen(nsub(hi, lo) >> 6)
            r = self.dcov(k, nsub(hi, 1) >> k, lo >> k, self.entry2, self.pmin)
        if len(self.lbd_cache) > 2000000:
            self.lbd_cache.clear()
        self.lbd_cache[key] = r
        return r

    # ---- convexity regions (PyrD.rgOk) ----
    def rgA(self, k): return (self.M.REG[0] >> (20 * k)) & 1048575
    def rgB(self, k): return (self.M.REG[1] >> (20 * k)) & 1048575
    def chainOk(self, a, l):
        for b in l:
            if not (a <= b and b + 1 <= self.KB and self.convOk(a, b)):
                return False
            a = b
        return True
    def rgOk(self):
        for k in range(self.NREG):
            A, B = self.rgA(k), self.rgB(k)
            ch = self.M.REG[2][k] if k < len(self.M.REG[2]) else []
            if B < A:
                continue
            if not (1 <= len(ch) and self.chainOk(A, ch) and (ch[-1] if ch else A) == B):
                return False
        return True

    # ---- tangent points (PCell.ptlOkD / ivOk / tcheckPZC) ----
    def ptOk(self, x, v):
        if v == 0:
            return True
        if not x + 1 <= self.KB:
            return False
        return self.cellOkCore(x, x, v)
    def ptdOk(self, x, p, m):
        if not x + 1 <= self.KB:
            return False
        okp = p == 0 or (self.okD(x, x) and p <= self.KU1 + self.W1LO(x, x))
        okm = m == 0 or (self.okD(x, x) and m <= self.KU1 - self.W1HI(x, x))
        return okp and okm
    def pt3e(self, x, v):
        return self.ptOk(x, self.lo32(v)) and self.ptdOk(x, self.lo32(self.hi32(v)), self.hi32(self.hi32(v)))
    @staticmethod
    def trip(v): return v & ((1 << 96) - 1)
    @staticmethod
    def ivA(v): return (v >> 96) & 16777215
    @staticmethod
    def ivB(v): return v >> 120
    @staticmethod
    def pwD(x, w):
        return (w & ((1 << 96) - 1)) + (nsub(x, (w >> 96) & 1048575) << 96) + ((x + (w >> 116)) << 120)
    def zpt(self, v, c, x, lbv):
        return v * 32768 + 10 * nsub(2000000000, c) * x <= lbv * 32768 + 10 * nsub(c, 2000000000) * x
    def zpc(self, v, c, p, x0, x1, right):
        if x1 <= x0:
            return True
        lbv = self.lb(x0, x1)
        if right:
            return self.zpt(v, c, nsub(x0, p), lbv) and self.zpt(v, c, nsub(x1, p), lbv)
        return self.zpt(v, c, nsub(p, x0), lbv) and self.zpt(v, c, nsub(p, x1), lbv)
    @staticmethod
    def zpe(a, b, n, k): return a + ndiv(nsub(b, a) * k, n)
    def zside(self, v, c, p, a, b, n, right):
        for k in range(n):
            if not self.zpc(v, c, p, self.zpe(a, b, n, k), self.zpe(a, b, n, k + 1), right):
                return False
        return True
    def zsideF(self, v, c, p, a, b, n, right):
        return self.zside(v, c, p, a, b, 1, right) or self.zside(v, c, p, a, b, 2, right) or self.zside(v, c, p, a, b, n, right)
    @staticmethod
    def rup(U, j): return ((U + nsub(1 << j, 1)) >> j) << j
    @staticmethod
    def rdn(L, j): return (L >> j) << j
    def treadU(self, U, p):
        k = (p + 16384) >> 15
        return 0 if U <= self.rgB(k) else self.lbDr(self.rgB(k), U)
    def treadD(self, L, p):
        k = (p + 16384) >> 15
        return 0 if self.rgA(k) <= L else self.lbDr(L, self.rgA(k))
    def tcheckZC(self, n, csh, L, U, p, X, EU, ED):
        lo32, hi32 = self.lo32, self.hi32
        k = (p + 16384) >> 15
        A, B = self.rgA(k), self.rgB(k)
        if not (k < self.NREG and A <= p and p <= B and L <= p and p <= U
                and 1 <= lo32(hi32(X)) and 1 <= hi32(hi32(X))):
            return False
        Mv, Pv, V = hi32(hi32(X)), lo32(hi32(X)), lo32(X)
        right = U <= B
        if not right:
            jj = self.blen(nsub(U, B) >> csh); uc = self.rup(U, jj)
            tu = self.treadU(uc, p)
            right = (1 <= lo32(tu) and 4000000000 <= lo32(tu) + Mv) or self.zsideF(V, Mv, p, B, uc, n, True)
        if not right:
            right = (1 <= lo32(EU) and 4000000000 <= lo32(EU) + Mv)
        if not right:
            right = self.zsideF(V, Mv, p, B, U, n, True)
        if not right:
            return False
        left = A <= L
        if not left:
            jj = self.blen(nsub(A, L) >> csh); lc = self.rdn(L, jj)
            td = self.treadD(lc, p)
            left = (1 <= hi32(td) and 4000000000 <= hi32(td) + Pv) or self.zsideF(V, Pv, p, lc, A, n, False)
        if not left:
            left = (1 <= hi32(ED) and 4000000000 <= hi32(ED) + Pv)
        if not left:
            left = self.zsideF(V, Pv, p, L, A, n, False)
        return left
    def tcheckPZC(self, n, csh, L, U, p, X, EU, ED):
        if L == U and L == p:
            return 1 <= self.lo32(self.hi32(X)) and 1 <= self.hi32(self.hi32(X))
        return self.tcheckZC(n, csh, L, U, p, X, EU, ED)
    def ivOk(self, n, csh, x, v):
        if self.ivB(v) == 0:
            return True
        return self.tcheckPZC(n, csh, self.ivA(v), self.ivB(v), x, self.trip(v),
                              self.treadU(self.ivB(v), x), self.treadD(self.ivA(v), x))
    def ptlOkD(self, n, csh, j, L):
        for (off, w) in L:
            x = 1024 * j + off
            v = self.pwD(x, w)
            if not (self.pt3e(x, self.trip(v)) and self.ivOk(n, csh, x, v)):
                return False
        return True
    def ptOkTD(self, n, csh, t):
        if t[0] == 'lf':
            return self.ptlOkD(n, csh, t[1], t[2])
        return self.ptOkTD(n, csh, t[2]) and self.ptOkTD(n, csh, t[3])
    def PT(self, x):
        """ptGetD PTT x: the point word (pwD-expanded) or 0."""
        r = self.pt_cache.get(x)
        if r is not None:
            return r
        t = self.M.PTT['PTT']
        while t[0] == 'nd':
            t = t[2] if (x // 1024) < t[1] else t[3]
        r = 0
        if x // 1024 == t[1]:
            for (off, w) in t[2]:
                if off == x % 1024:
                    r = self.pwD(x, w)
                    break
        self.pt_cache[x] = r
        return r

    # ---- curvature table (PCell.Var) ----
    def curvatureOk(self, a, b, n, den):
        c = self.CE.cell(a, b)
        return 0 < den and c['ok'] and 0 < c['E2L'] and 0 < c['E3L'] and n * self.DZ ** 2 <= 2 * den * c['W2L']
    @staticmethod
    def fat(T, j): return (T >> (12 * j)) & 4095
    def tbOk(self, TB):
        for (B0, N, T) in TB:
            if not T < 2 ** (12 * N):
                return False
            for j in range(N):
                f = self.fat(T, j)
                if f == 0:
                    continue
                a, b = 256 * (B0 + j), 256 * (B0 + j + 1)
                if not (a <= b and self.curvatureOk(a, b, f * 524288, self.M.VD)):
                    return False
        return True
    def tfld(self, i):
        for (B0, N, T) in self.M.TBL:
            if B0 <= i:
                return self.fat(T, i - B0)
        return 0
    def cmin(self, i, n):
        v = self.tfld(i)
        for m in range(1, n + 1):
            u = self.tfld(i + m)
            if u <= v:
                v = u
        return v
    def vbon(self, mu, m, p, r):
        d = nsub(p, r) + nsub(r, p)
        return ndiv(10000000000 * mu * (m * nsub(1024, m)) * (d * d), 2048 * (32768 * 32768) * self.M.VD)
    def vbW(self, L, U, k, m, p, r):
        if k != 3:
            return 0
        a, b = 256 * (L // 256), 256 * (U // 256 + 1)
        vin = a <= L and U <= b and a <= p and p <= b and a <= r and r <= b
        if nsub(U // 256, L // 256) <= 4 and vin:
            return self.vbon(self.cmin(L // 256, nsub(U // 256, L // 256)) * 524288, m, p, r)
        return 0

    # ---- window bound on [1/4, 1/2] ----
    def winOk(self, i):
        c = self.CE.cell(8192 + 512 * i, 8704 + 512 * i)
        return c['ok'] and self.DZ * self.DZ <= 4 * (c['KAn'] * c['KAn'])

    # ---- root cover (PCell.coverChk) ----
    def coverChk(self, cN, aAdj, pos, S, cover):
        for (a, b, cl) in cover:
            if not (a == pos and a <= b and b < self.KB):
                return False
            if cl and not (cN * self.SW <= aAdj * self.WZ(a, b)):
                return False
            pos = b
        return S <= pos

    # ---- polytope cell state: (L[8], U[8], A[28], B[28]) ----
    def pI(self, k): return self.M.PR[k][0]
    def pJ(self, k): return self.M.PR[k][1]
    def matC(self, s):
        """PCell.matC (the root step `tm`): A_k <- max(A_k, sum L), B_k <- min(B_k, sum U)."""
        L, U, A, B = s
        A2 = [max(A[k], sum(L[self.pI(k):self.pJ(k)])) for k in range(self.M.NP)]
        B2 = [min(B[k], sum(U[self.pI(k):self.pJ(k)])) for k in range(self.M.NP)]
        return (L, U, A2, B2)
    def slT(self, a, b): return self.M.SL[a * (self.M.Q + 1) + b]
    def sLo(self, s, x):
        Q = self.M.Q
        return s[0][x] if x < Q else s[2][x - Q]
    def sHi(self, s, x):
        Q = self.M.Q
        return s[1][x] if x < Q else s[3][x - Q]
    def dE(self, s, E, a, b):
        if a < b:
            return E + self.sHi(s, self.slT(a, b))
        if a == b:
            return E
        return nsub(E, self.sLo(s, self.slT(b, a)))
    def colB(self, s, x0):
        return [self.dE(s, self.M.BB, x, x0) for x in range(self.M.Q + 1)]
    def rowB(self, s, E, t):
        return [self.dE(s, E, t, x) for x in range(self.M.Q + 1)]
    def cuB(self, s, X, Y):
        L, U, A, B = s
        TB = self.M.TBIAS
        Q = self.M.Q
        L2 = [max(L[r], nsub(TB, X[r + 1] + Y[r])) for r in range(Q)]
        U2 = [min(U[r], nsub(X[r] + Y[r + 1], TB)) for r in range(Q)]
        A2 = [max(A[k], nsub(TB, X[self.pJ(k)] + Y[self.pI(k)])) for k in range(self.M.NP)]
        B2 = [min(B[k], nsub(X[self.pI(k)] + Y[self.pJ(k)], TB)) for k in range(self.M.NP)]
        return (L2, U2, A2, B2)
    def bcutL(self, bm, lo, hi):
        def bdist(sm, z): return nsub(z + z, sm) + nsub(sm, z + z)
        acc = ((lo + hi) >> 1, False)
        for z in self.M.BND:
            if lo + bm <= z and z + bm <= hi and ((not acc[1]) or bdist(lo + hi, z) < bdist(lo + hi, acc[0])):
                acc = (z, True)
        return acc[0]
    @staticmethod
    def fracQ(lo, hi, md):
        return lo + ((nsub(hi, lo) * (nsub(md, 1) if md <= 4 else md)) >> 3)

    # ---- the leaf ----
    def gptQG(self, fs, L, U, jj):
        if jj == 33:
            return L
        if jj == 34:
            return U
        gs = fs if ((jj >> 6) & 1) == 1 else 8
        x = L + ((nsub(U, L) * (jj & 63)) >> 5)
        A = (x >> gs) << gs
        cL = ((L + nsub(1 << gs, 1)) >> gs) << gs
        fU = (U >> gs) << gs
        if A <= cL:
            return cL
        return fU if fU <= A else A
    @staticmethod
    def plenF(lb, a):
        if a == 1: return 9
        if a == 2: return 9 + lb
        if a == 3: return 16 + lb
        return 2
    def dec4QG(self, fs, lb, w, o, L, U):
        a = (w >> o) & 3
        mask = nsub(1 << lb, 1)
        if a == 2:
            lam = (w >> (o + 9)) & mask
        elif a == 3:
            lam = (w >> (o + 16)) & mask
        else:
            lam = 0
        p = 0 if a == 0 else self.gptQG(fs, L, U, (w >> (o + 2)) & 127)
        r = self.gptQG(fs, L, U, (w >> (o + 9)) & 127) if a == 3 else 0
        return a, lam << nsub(10, lb), p, r, o + self.plenF(lb, a)
    @staticmethod
    def mwc(k, lam):
        if k == 1: return 0
        if k == 2: return nsub(1024, lam)
        if k == 3: return 0
        return 1024
    @staticmethod
    def mw1(k, lam):
        if k == 1: return 1024
        if k == 2: return lam
        if k == 3: return nsub(1024, lam)
        return 0
    @staticmethod
    def mw2(k, lam): return lam if k == 3 else 0
    def term_ranges(self, s):
        """eL / eU / eL0 for every term (PCell.eL, eU, eL0)."""
        L, U, A, B = s
        out = []
        for (i, j, a, kk) in self.M.TS:
            sL = sum(L[i:j]); sU = sum(U[i:j])
            if j - i == 1:
                out.append((L[i], U[i], sL))
            else:
                out.append((max(A[kk], sL), min(B[kk], sU), sL))
        return out
    def ydec(self, s, qb, w, fuel, o):
        """ydecS: the multiplier list; each entry adds a pair-constraint multiple (mul_step)."""
        L, U, A, B = s
        P = [0] * self.M.Q; S = [0] * self.M.Q; Cp = 0; Cm = 0
        n = 0
        for _ in range(fuel):
            if ((w >> o) & 1) != 1:
                o = o + 1
                break
            c = (w >> (o + 1)) & 31
            o1 = o + 6
            if not c < 28:
                o = o1 + qb + 1
                break
            Y = self.M.SIG * ((w >> (o1 + 1)) & nsub(1 << qb, 1))
            sd = (w >> o1) & 1
            Ylo = 0 if sd == 1 else Y
            Yhi = Y if sd == 1 else 0
            i, j = self.PR_(c)
            sL = sum(L[i:j])
            for r in range(i, j):
                P[r] += Ylo; S[r] += Yhi
            Cp += Ylo * nsub(sL, A[c]) + Yhi * nsub(B[c], sL)
            Cm += Ylo * nsub(A[c], sL) + Yhi * nsub(sL, B[c])
            o = o1 + qb + 1
            n += 1
        return o, P, S, Cp, Cm, n
    def PR_(self, k):
        if k < len(self.M.PR):
            return self.M.PR[k]
        return (0, 0)
    def mleaf(self, w, s, variance, want_detail=False):
        """mleafP / mleafV: decode 34 terms, the multipliers, then mcheckGX / mcheckW.
        Returns (end offset or 0, detail)."""
        M = self.M
        rngs = self.term_ranges(s)
        o = 0
        terms = []
        for n, (eL, eU, eL0) in enumerate(rngs):
            a, lam, p, r, o = self.dec4QG(M.FS, M.LB, w, o, eL, eU)
            terms.append((a, lam, p, r))
        yo, P, S, Cp, Cm, nmul = self.ydec(s, M.QB, w, M.YFUEL, o)
        ok, lhs, rhs, info = self.mcheck(s, rngs, terms, P, S, Cp, Cm, variance)
        det = None
        if want_detail:
            det = dict(lhs=lhs, rhs=rhs, terms=terms, nmul=nmul, info=info, end=yo)
        return (yo if ok else 0), det
    def mcheck(self, s, rngs, terms, P, S, Cp, Cm, variance):
        """PCell.mcheckGX (mokI) / PCell.Var.mcheckW (vbW TB)."""
        M = self.M
        L, U, A, B = s
        lo32, hi32, trip = self.lo32, self.hi32, self.trip
        def f(x): return trip(self.PT(x))
        def Mv(x): return hi32(hi32(f(x)))
        def Pv(x): return lo32(hi32(f(x)))
        sum_mcn = 0; sum_mcp = 0; sum_mv = 0
        okterms = True
        wsl = [0] * M.Q     # per gap: sum of tA * mwT over terms containing r
        ssl = [0] * M.Q     # per gap: sum of tA * mslT
        bonus_used = 0
        for n, (i, j, tA, kk) in enumerate(M.TS):
            eL, eU, eL0 = rngs[n]
            a, lam, p, r = terms[n]
            l1, l2, lc = self.mw1(a, lam), self.mw2(a, lam), self.mwc(a, lam)
            # mokI: lam <= 1024 and every used tangent's interval contains [eL, eU]
            ok = lam <= 1024
            if ok and l1 != 0:
                ok = self.ivIn(self.PT(p), eL, eU, p)
            if ok and l2 != 0:
                ok = self.ivIn(self.PT(r), eL, eU, r)
            okterms = okterms and ok
            mcn = l1 * nsub(2000000000, Mv(p)) * nsub(p, eL0) + l2 * nsub(2000000000, Mv(r)) * nsub(r, eL0) if (l1 or l2) else 0
            mcp = l1 * nsub(Mv(p), 2000000000) * nsub(p, eL0) + l2 * nsub(Mv(r), 2000000000) * nsub(r, eL0) if (l1 or l2) else 0
            uc = max(eU, eL + 1)
            mv = lc * (self.lb(eL, uc) if lc else 0) + l1 * (lo32(f(p)) if l1 else 0) + l2 * (lo32(f(r)) if l2 else 0)
            if variance:
                bon = self.vbW(eL, eU, a, lam, p, r)
                mv += bon
                bonus_used += 1 if bon else 0
            msl = l1 * (Pv(p) if l1 else 0) + l2 * (Pv(r) if l2 else 0)
            sum_mcn += tA * mcn
            sum_mcp += tA * mcp
            sum_mv += tA * mv
            for g in range(i, j):
                wsl[g] += tA * (l1 + l2)
                ssl[g] += tA * msl
        Ng_sum = 0
        for g in range(M.Q):
            Ng = nsub(2000000000 * wsl[g] + P[g], 1024000000000 * M.BS[g] + ssl[g] + S[g])
            Ng_sum += nsub(U[g], L[g]) * Ng
        lhs = 335544320000000000 * M.cN + 10 * (sum_mcn + Cp + Ng_sum)
        rhs = 10240000000000 * sum(M.BS[g] * L[g] for g in range(M.Q)) + 32768 * sum_mv + 10 * (sum_mcp + Cm)
        boxok = all(L[g] <= U[g] for g in range(M.Q))
        return (lhs <= rhs and okterms and boxok), lhs, rhs, dict(okterms=okterms, boxok=boxok, bonus=bonus_used)
    def ivIn(self, v, L, U, p):
        return 1 <= self.ivB(v) and self.ivA(v) <= L and L <= p and p <= U and U <= self.ivB(v)

    # ---- the walk (PC9XA.node / walkC / walk / walkCut / walkCutR) ----
    def make_bits(self, wd):
        blocks = self.M.WLblocks[self.M.WD[wd]]
        WMASK = self.M.WMASK
        disp = self.M.disp
        name = self.M.WD[wd]
        def bits(pos):
            j = pos // 32768
            X = blocks[j] if j < len(blocks) else disp.call(name, j)
            return (X >> (pos % 32768)) & WMASK
        return bits
    def walkC(self, bits, fuel, pos, s, cuts=None, rec=None, depth=0):
        """walkC (cuts=None) or walkCut (cuts = list of (pos, state, e)); returns the end position or 0."""
        if fuel == 0:
            return 0
        if cuts:
            for (cp, cst, ce) in cuts:
                if cp == pos:
                    return ce if self.st_eq(s, cst) else 0
        w = bits(pos)
        if (w & 1) == 1:
            ax = (w >> 1) & 63
            md = (w >> 7) & 7
            return self.splitAx(bits, fuel, md, pos + 10, ax, s, cuts, rec, depth)
        return self.leafStep(pos, w, s, rec, depth)
    def splitAx(self, bits, fuel, md, pos, ax, s, cuts, rec, depth):
        M = self.M
        if ax >= M.Q + M.NP:
            return 0
        if ax < M.Q:
            i, j = ax, ax + 1
            lo, hi = s[0][ax], s[1][ax]
        else:
            i, j = M.PR[ax - M.Q]
            lo, hi = s[2][ax - M.Q], s[3][ax - M.Q]
        if 2 <= md:
            q = self.fracQ(lo, hi, md)
        elif md == 1:
            q = self.bcutL(64, lo, hi)
        else:
            q = (lo + hi) >> 1
        if rec is not None:
            rec['splits'] += 1
            rec['split_axes'][ax] = rec['split_axes'].get(ax, 0) + 1
            rec['split_modes'][md] = rec['split_modes'].get(md, 0) + 1
        left = self.cuB(s, self.colB(s, i), self.rowB(s, M.BB + q, j))
        pp = self.walkC(bits, fuel - 1, pos, left, cuts, rec, depth + 1)
        if pp == 0:
            return 0
        right = self.cuB(s, self.colB(s, j), self.rowB(s, nsub(M.BB, q), i))
        return self.walkC(bits, fuel - 1, pp, right, cuts, rec, depth + 1)
    def leafStep(self, pos, w, s, rec, depth):
        L, U = s[0], s[1]
        if U[7] < L[0]:
            if rec is not None:
                rec['refl'] += 1
                rec['depths'].append(depth)
            return pos + 1
        variance = ((w >> 1) & 1) == 1
        n, det = self.mleaf(w >> 2, s, variance, want_detail=rec is not None)
        if rec is not None:
            rec['leaves'] += 1
            rec['depths'].append(depth)
            rec['var'] += 1 if variance else 0
            rec['margins'].append((det['rhs'] - det['lhs'], pos, variance, det['nmul'],
                                   [t[0] for t in det['terms']], tuple(s[0]), tuple(s[1])))
        if n == 0:
            if rec is not None:
                rec['fail'].append((pos, det['info'], det['lhs'], det['rhs']))
            return 0
        return pos + 2 + n
    def st_eq(self, s, cst):
        return self.st_flat(s) == cst[:-1] and cst[-1] == 0
    def st_flat(self, s):
        L, U, A, B = s
        out = []
        for r in range(self.M.Q):
            out += [L[r], U[r]]
        for k in range(self.M.NP):
            out += [A[k], B[k]]
        return out
    def st_of_flat(self, v):
        Q, NP = self.M.Q, self.M.NP
        L = [v[2 * r] for r in range(Q)]; U = [v[2 * r + 1] for r in range(Q)]
        A = [v[2 * Q + 2 * k] for k in range(NP)]; B = [v[2 * Q + 2 * k + 1] for k in range(NP)]
        return (L, U, A, B)
    def badOf(self, cover):
        return [(a, b) for (a, b, t) in cover if not t]
    def rootState(self, idx):
        """rootCl 8 28 W COV idx (then ofCl ... 0: M = 0)."""
        M = self.M
        L = []; U = []
        for r in range(M.Q):
            bad = self.badOf(M.COV[r])
            a, b = bad[idx[r]] if idx[r] < len(bad) else (0, 0)
            L.append(a); U.append(b)
        return (L, U, [0] * M.NP, [M.RCW] * M.NP)

def new_rec():
    return dict(splits=0, leaves=0, refl=0, var=0, depths=[], margins=[], fail=[], split_axes={}, split_modes={})

# ----------------------------------------------------------------------------------
# pvCheck (AMW.pvCheck), rational
# ----------------------------------------------------------------------------------

def pv_check(M):
    import math
    piLo, piHi = Fraction(3141592, 10**6), Fraction(3141593, 10**6)
    s2Lo, s2Hi = Fraction(14142135, 10**7), Fraction(14142136, 10**7)
    errQ = Fraction(13, 5748019200)
    E10 = 10**10
    def fl(x): return Fraction(math.floor(x * E10), E10)
    def cl(x): return Fraction(math.ceil(x * E10), E10)
    def tCos(t):
        s = t * t
        return 1 + s * (Fraction(-1, 2) + s * (Fraction(1, 24) + s * (Fraction(-1, 720) + s * (Fraction(1, 40320) + s * Fraction(-1, 3628800)))))
    def tSin(t):
        s = t * t
        return t * (1 + s * (Fraction(-1, 6) + s * (Fraction(1, 120) + s * (Fraction(-1, 5040) + s * (Fraction(1, 362880) + s * Fraction(-1, 39916800))))))
    def TLo(a): return fl(piLo * a)
    def THi(a): return cl(piHi * a)
    def cosI(a): return (fl(tCos(THi(a)) - errQ), cl(tCos(TLo(a)) + errQ))
    def sinI(a): return (fl(tSin(TLo(a)) - errQ), cl(tSin(THi(a)) + errQ))
    def csA(k): return [(1, 0), (0, 1), (-1, 0), (0, -1)][k % 4]
    def imulZ(e, I): return (e * I[0], e * I[1]) if e >= 0 else (e * I[1], e * I[0])
    def iadd(I, J): return (I[0] + J[0], I[1] + J[1])
    def isub(I, J): return (I[0] - J[1], I[1] - J[0])
    def kOf(t): return max(math.floor(2 * t + Fraction(1, 2)), 0)
    def rOf(t): return t - Fraction(kOf(t), 2)
    def sinPiI(t):
        k, r = kOf(t), rOf(t)
        if 0 <= r:
            return iadd(imulZ(csA(k)[1], cosI(r)), imulZ(csA(k)[0], sinI(r)))
        return isub(imulZ(csA(k)[1], cosI(-r)), imulZ(csA(k)[0], sinI(-r)))
    def sinPiOk(t): return 0 <= TLo(abs(rOf(t))) and THi(abs(rOf(t))) <= 1
    tab = M.sinTabZ
    def tabI(q):
        a, b = tab[q] if q < len(tab) else (0, 0)
        return (Fraction(a, E10), Fraction(b, E10))
    PQ = getattr(M, 'pv_cells', 128)
    tabOk = True
    for q in range(PQ + 1):
        t = Fraction(q, 2 * PQ)
        sp = sinPiI(t)
        if not (sinPiOk(t) and tabI(q)[0] <= sp[0] and sp[1] <= tabI(q)[1]):
            tabOk = False
            break
    def ineg(I): return (-I[1], -I[0])
    def sinLook(r):
        m = r % (4 * PQ)
        if m <= PQ: return tabI(m)
        if m <= 2 * PQ: return tabI(2 * PQ - m)
        if m <= 3 * PQ: return ineg(tabI(m - 2 * PQ))
        return ineg(tabI(4 * PQ - m))
    def piMul(S): return (min(piLo * S[0], piHi * S[0]), max(piLo * S[1], piHi * S[1]))
    def cAM(j): return Fraction(M.cAMn.get(j, 0), 10**9)
    def midQ(i): return Fraction(2 * i + 1, 4 * PQ)
    def termU(i, j):
        if j == 0:
            return -(s2Lo * max(Fraction(0), fl(tSin(fl(s2Lo * midQ(i))) - errQ)))
        e = -(2 * j * cAM(j))
        if 0 <= e:
            return e * piMul(sinLook(j * (2 * i + 1)))[1]
        return e * piMul(sinLook(j * (2 * i + 1)))[0]
    def termOk(i): return 0 <= fl(s2Lo * midQ(i)) and s2Hi * midQ(i) <= 1
    allok = all(termOk(i) for i in range(PQ))
    total = sum(max(sum(termU(i, j) for j in range(M.pv_terms)) + Fraction(M.pv_lip, 4 * PQ), Fraction(0)) for i in range(PQ))
    val = total / (Fraction(5, 2) * PQ)
    M.pv_value, M.pv_sinPiI = val, sinPiI   # exact value and the table reference, for generators
    return (tabOk and allok and val <= M.pv_rho), dict(tabOk=tabOk, termOk=allok, value=float(val), rho=float(M.pv_rho))

# ----------------------------------------------------------------------------------
# small `decide` checks (PRok, TSok, SLok, hADJ, CE_pos, cert_of side conditions)
# ----------------------------------------------------------------------------------

def decide_checks(M, C):
    out = {}
    Q, PR, TS, SL = M.Q, M.PR, M.TS, M.SL
    out['hPR'] = all(i + 2 <= j and j <= Q for (i, j) in PR)
    def sI(s): return s if s < Q else PR[s - Q][0]
    def sJ(s): return s + 1 if s < Q else PR[s - Q][1]
    out['hTS'] = all(i < j and j <= Q and (j - i == 1 or (k < len(PR) and PR[k] == (i, j))) for (i, j, a, k) in TS)
    out['hSL'] = all(SL[a * (Q + 1) + b] < Q + len(PR) and sI(SL[a * (Q + 1) + b]) == a and sJ(SL[a * (Q + 1) + b]) == b
                     for a in range(Q + 1) for b in range(Q + 1) if a < b)
    out['hADJ'] = all(M.ADJ[r] < len(TS) and TS[M.ADJ[r]][0] == r and TS[M.ADJ[r]][1] == r + 1 for r in range(Q))
    out['CE_pos'] = all(1 <= t[0] for t in M.G['CE'])
    out['cert.hS'] = all(M.cN * 32768 <= M.BS[r] * M.SMAX[r] for r in range(Q))
    out['cert.hwin'] = all(M.cN * 4 <= TS[M.ADJ[r]][2] for r in range(Q))
    out['cert.hW'] = 8 * M.KB <= M.CERTW
    out['RC.W = cert W'] = M.RCW == M.CERTW
    # run: the 48 root theorems are exactly the product of the bad-segment indices
    lens = [len(C.badOf(M.COV[r])) for r in range(Q)]
    prod = set(itertools.product(*[range(n) for n in lens]))
    out['run: roots = product of bad segments'] = prod == set(d['idx'] for d in M.ROOTS) and len(M.ROOTS) == len(prod)
    # palindromic weights (needed by PC9XA_G_rev, proved by ring_nf in Lean; checked here for information)
    aw = {(i, j): a for (i, j, a, k) in TS}
    out['info: weights symmetric'] = (M.BS == M.BS[::-1] and all(aw.get((Q - j, Q - i), 0) == a for (i, j), a in aw.items()))
    return out

# ----------------------------------------------------------------------------------
# drivers
# ----------------------------------------------------------------------------------

def run_block_range(args):
    path, kind, a, n, mut = args
    M = load_cached(path, mut)
    C = Checker(M)
    bad = []
    for j in range(a, a + n):
        if kind == 'pyr':
            ok = C.blockOk(C.BK(j), j)
        else:
            ok = C.blockOk2(C.BKD(j), j)
        if not ok:
            bad.append(j)
    return (kind, a, n, bad)

def run_ptt(args):
    path, name, n, csh, mut = args
    M = load_cached(path, mut)
    C = Checker(M)
    ok = C.ptOkTD(n, csh, M.PTT[name])
    return (name, ok)

def run_root(args):
    path, ridx, mut = args
    M = load_cached(path, mut)
    C = Checker(M)
    d = M.ROOTS[ridx]
    bits = C.make_bits(d['wd'])
    s = C.matC(C.rootState(d['idx']))
    rec = new_rec()
    cuts = None
    if d['cuts'] is not None:
        cuts = [(p, M.CS[cs], e) for (p, cs, e) in M.CUTS[d['cuts']]]
    end = C.walkC(bits, M.FUEL, 1, s, cuts, rec)
    return (d['r'], end, d['e'], rec)

def run_cut(args):
    path, cidx, mut = args
    M = load_cached(path, mut)
    C = Checker(M)
    d = M.WCS[cidx]
    bits = C.make_bits(d['wd'])
    s = C.st_of_flat(M.CS[d['cs']])
    rec = new_rec()
    end = C.walkC(bits, d['fuel'], d['pos'], s, None, rec)
    return (d['name'], end, d['e'], rec)

_MCACHE = {}
def load_cached(path, mut):
    key = (path, mut)
    if key not in _MCACHE:
        M = load_model(path)
        if mut:
            apply_mutation(M, mut)
        _MCACHE[key] = M
    return _MCACHE[key]

# ---- mutations: one data value per check family ----
def apply_mutation(M, mut):
    kind = mut
    if kind == 'pv':          # sine table entry q = 64: raise its lower end above sin(pi/4)
        a, b = M.sinTabZ[64]; M.sinTabZ[64] = (a + 10**7, b)
    elif kind == 'win':       # window literal c_1 in the cell evaluator's far sum (CE/FA): sign flipped, x60
        M.G['FAR'][0] = (M.G['FAR'][0][0], M.G['FAR'][0][1] * 60, not M.G['FAR'][0][2])
    elif kind == 'tb':        # first curvature field of cluster 0 raised to 4095
        B0, N, T = M.TBL[0]; M.TBL[0] = (B0, N, T | 4095)
    elif kind == 'top':       # TOP level-19 field (whole range) raised by 1e9
        M.TOP = M.TOP + (10**9 << 32)
    elif kind == 'blk':       # BK block 300: its root field raised by 1
        M.BKv[300] = M.BKv[300] + (1 << 5)
    elif kind == 'topd':
        M.TOPD = M.TOPD + (10**8 << 64)
    elif kind == 'dblk':      # BKD block 214: root lo32 field raised by 1
        j = next(j for j in range(512) if M.BKDv[j] != 0)
        M.BKDv[j] = M.BKDv[j] + (1 << 5)
        M.mut_block = j
    elif kind == 'reg':       # convexity region 1: chain extended past its region end
        ch = M.REG[2][1]; ch[-1] = ch[-1] + 65536
    elif kind == 'ptt':       # first tangent word of PTT_0: value lower bound + 10^6
        t = M.PTT['PTT_0']
        while t[0] == 'nd':
            t = t[2]
        off, w = t[2][0]
        t[2][0] = (off, w + 10**6)
    elif kind == 'cover':     # COV gap 0: the bad segment marked as certified
        a, b, _ = M.COV[0][-1]; M.COV[0][-1] = (a, b, True)
    elif kind == 'root':      # one bit of root 0's walk words
        name = M.WD[0]
        M.WLblocks[name][0] ^= (1 << 700)
    elif kind == 'rootend':   # root 0: stated end position off by one
        M.ROOTS[0]['e'] += 1
    elif kind == 'cut':       # cut state of wcs9_1: one coordinate changed
        M.CS['CS9_1'][3] += 1
    elif kind == 'cutend':    # wcs9_1: stated end position off by one
        M.WCS[0]['e'] += 1
    elif kind == 'bs':        # per-gap pressure b_0 lowered by 2^-20 relative (leaf weights)
        M.BS = list(M.BS); M.BS[0] -= (M.BS[0] >> 20)
    elif kind == 'floor':     # the floor c raised by 2^-40 relative
        M.cN = M.cN + (M.cN >> 40) + 1
    else:
        raise ValueError(kind)

def root_end(M, C, ridx):
    d = M.ROOTS[ridx]
    cuts = [(p, M.CS[cs], e) for (p, cs, e) in M.CUTS[d['cuts']]] if d['cuts'] is not None else None
    end = C.walkC(C.make_bits(d['wd']), M.FUEL, 1, C.matC(C.rootState(d['idx'])), cuts)
    return end == d['e'] and end != 0

def cut_end(M, C, cidx):
    d = M.WCS[cidx]
    end = C.walkC(C.make_bits(d['wd']), d['fuel'], d['pos'], C.st_of_flat(M.CS[d['cs']]), None)
    return end == d['e'] and end != 0

MUTATIONS = [
    # (mutation, check family, what is evaluated)
    ('pv', 'pvCheck_AM', lambda M, C: pv_check(M)[0]),
    ('win', 'winOk_all', lambda M, C: all(C.winOk(i) for i in range(16))),
    ('tb', 'TB_ok', lambda M, C: C.tbOk(M.TBL)),
    ('top', 'top_ok', lambda M, C: C.topOk(M.TOP, C.BK)),
    ('blk', 'blk_2 (block 300)', lambda M, C: C.blockOk(C.BK(300), 300)),
    ('topd', 'topD_ok', lambda M, C: C.topOk2(M.TOPD, C.BKD)),
    ('dblk', 'dblk_* (first nonzero block)', lambda M, C: C.blockOk2(C.BKD(M.mut_block), M.mut_block)),
    ('reg', 'hR', lambda M, C: C.rgOk()),
    ('ptt', 'PTT_0_ok', lambda M, C: C.ptOkTD(int(M.ptt_checks[0][1]), int(M.ptt_checks[0][2]), M.PTT['PTT_0'])),
    ('cover', 'cert.hcov', lambda M, C: all(C.coverChk(M.cN, M.TS[M.ADJ[r]][2], 16384, M.SMAX[r], M.COV[r]) for r in range(M.Q))),
    ('root', 'rc0 (walk bit)', lambda M, C: root_end(M, C, 0)),
    ('rootend', 'rc0 (stated end)', lambda M, C: root_end(M, C, 0)),
    ('cut', 'rc9 (cut state)', lambda M, C: root_end(M, C, 9)),
    ('cutend', 'wcs9_1 (stated end)', lambda M, C: cut_end(M, C, 0)),
    ('bs', 'rc37 (weight b_0)', lambda M, C: root_end(M, C, 37)),
    ('floor', 'rc37 (floor c)', lambda M, C: root_end(M, C, 37)),
]

def mutation_suite(path):
    """Baseline (unmutated) and mutated value of one check per family; the mutated value must be false."""
    allgood = True
    base = load_model(path)
    for mut, name, fn in MUTATIONS:
        Mb = base
        Mb.mut_block = next(j for j in range(512) if Mb.BKDv[j] != 0)
        b = fn(Mb, Checker(Mb))
        Mm = load_model(path)
        apply_mutation(Mm, mut)
        m = fn(Mm, Checker(Mm))
        good = (b is True) and (m is False)
        allgood = allgood and good
        print('%-8s %-30s unmutated=%s mutated=%s %s' % (mut, name, b, m, 'ok' if good else 'PROBLEM'), flush=True)
    print('MUTATION SUITE:', 'every mutation detected' if allgood else 'PROBLEM')
    return allgood

def summarize_margins(recs, M):
    margins = []
    for r, rec in recs:
        for (m, pos, var, nmul, kinds, L, U) in rec['margins']:
            margins.append((m, r, pos, var, nmul, kinds, L, U))
    margins.sort(key=lambda t: t[0])
    scale = 335544320000000000 * M.SA
    vals = [m[0] / scale for m in margins]
    def q(p):
        return vals[min(len(vals) - 1, int(p * (len(vals) - 1)))]
    hist = {}
    for v in vals:
        if v <= 0:
            b = '<=0'
        else:
            import math
            e = math.floor(math.log10(v))
            b = '1e%d' % e
        hist[b] = hist.get(b, 0) + 1
    kinds = {0: 0, 1: 0, 2: 0, 3: 0}
    nm = []
    for m in margins:
        for k in m[5]:
            kinds[k] += 1
        nm.append(m[4])
    return dict(n=len(vals), min=vals[0], q01=q(0.01), q10=q(0.10), median=q(0.5), q90=q(0.9), max=vals[-1],
                hist=dict(sorted(hist.items())),
                smallest=[dict(margin=m[0] / scale, root=m[1], pos=m[2], variance=m[3], nmul=m[4],
                               L=[x / 32768 for x in m[6]], U=[x / 32768 for x in m[7]]) for m in margins[:12]],
                term_kinds=kinds, mult_per_leaf=dict(mean=sum(nm) / len(nm), max=max(nm),
                                                     zero=sum(1 for x in nm if x == 0)))

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('solution')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--only', nargs='*', default=None)
    ap.add_argument('--mutate', default=None, help='apply one mutation (see apply_mutation)')
    ap.add_argument('--stats', default=None)
    ap.add_argument('--roots', default=None, help='comma-separated root indices (default all)')
    ap.add_argument('--mutation-suite', action='store_true')
    a = ap.parse_args()
    if a.mutation_suite:
        return 0 if mutation_suite(a.solution) else 1
    t0 = time.time()
    M = load_cached(a.solution, a.mutate)
    C = Checker(M)
    fam = set(a.only) if a.only else {'decide', 'pv', 'win', 'tb', 'pyr', 'pyrd', 'reg', 'ptt', 'cover', 'roots', 'cuts'}
    results = []
    stats = {}
    def report(name, ok, extra=''):
        results.append((name, ok))
        print('%-28s %s %s' % (name, 'true' if ok else 'FALSE', extra), flush=True)
    print('source: %s  (%d zfNat64 numerals decoded, %d lines contain "decide +kernel")' % (a.solution, M.n_packed, len(M.dk_lines)))
    if a.mutate:
        print('MUTATION:', a.mutate)
    if 'decide' in fam:
        for k, v in decide_checks(M, C).items():
            report(k, v)
    if 'pv' in fam:
        ok, info = pv_check(M)
        report('pvCheck_AM', ok, json.dumps(info))
        stats['pv'] = info
    if 'win' in fam:
        ok = all(C.winOk(i) for i in range(16))
        mins = min(4 * C.CE.cell(8192 + 512 * i, 8704 + 512 * i)['KAn'] ** 2 / C.DZ ** 2 for i in range(16))
        report('winOk_all', ok, 'min 4 KAn^2/DZ^2 = %.6f' % mins)
    if 'tb' in fam:
        report('TB_ok', C.tbOk(M.TBL))
    from multiprocessing import Pool
    pool = Pool(a.workers) if a.workers > 1 else None
    def pmap(fn, items):
        if pool is None:
            return [fn(x) for x in items]
        return pool.map(fn, items, chunksize=1)
    if 'pyr' in fam:
        report('top_ok', C.topOk(M.TOP, C.BK))
        ranges = re.findall(r'^theorem (blk_\d+) : Pyr.allFrom (\d+) (\d+) \(fun j => Pyr.blockOk \(BK j\) j\) = true := by decide \+kernel$', M.src, re.M)
        chunks = []
        for name, s0, n in ranges:
            s0, n = int(s0), int(n)
            for b in range(s0, s0 + n, 8):
                chunks.append((a.solution, 'pyr', b, min(8, s0 + n - b), a.mutate))
        res = pmap(run_block_range, chunks)
        for name, s0, n in ranges:
            s0, n = int(s0), int(n)
            bad = [j for (k, b, m, bl) in res for j in bl if s0 <= j < s0 + n]
            report(name, not bad, ('failing blocks %s' % bad[:5]) if bad else '')
        cover = sorted((int(s0), int(n)) for _, s0, n in ranges)
        report('blk ranges cover 0..512', sum(n for _, n in cover) == 512 and cover[0][0] == 0 and
               all(cover[i][0] + cover[i][1] == cover[i + 1][0] for i in range(len(cover) - 1)))
    if 'pyrd' in fam:
        report('topD_ok', C.topOk2(M.TOPD, C.BKD))
        ranges = re.findall(r'^theorem (dblk_\d+) : Pyr.allFrom (\d+) (\d+) \(fun j => blockOk2 \(BKD j\) j\) = true := by decide \+kernel$', M.src, re.M)
        chunks = []
        for name, s0, n in ranges:
            s0, n = int(s0), int(n)
            for b in range(s0, s0 + n, 8):
                chunks.append((a.solution, 'pyrd', b, min(8, s0 + n - b), a.mutate))
        res = pmap(run_block_range, chunks)
        for name, s0, n in ranges:
            s0, n = int(s0), int(n)
            bad = [j for (k, b, m, bl) in res for j in bl if s0 <= j < s0 + n]
            report(name, not bad, ('failing blocks %s' % bad[:5]) if bad else '')
    if 'reg' in fam:
        report('hR (rgOk REG)', C.rgOk())
    if 'ptt' in fam:
        items = [(a.solution, nm + '', int(n), int(csh), a.mutate) for (nm, n, csh) in M.ptt_checks]
        for name, ok in pmap(run_ptt, items):
            report(name + '_ok', ok)
        npts = 0
        def cnt(t):
            return len(t[2]) if t[0] == 'lf' else cnt(t[2]) + cnt(t[3])
        stats['tangent_points'] = cnt(M.PTT['PTT'])
    if 'cover' in fam:
        ok = all(C.coverChk(M.cN, M.TS[M.ADJ[r]][2], 32768 // 2, M.SMAX[r], M.COV[r]) for r in range(M.Q))
        report('cert.hcov (coverChk)', ok)
    if 'cuts' in fam:
        res = pmap(run_cut, [(a.solution, i, a.mutate) for i in range(len(M.WCS))])
        cstats = []
        for name, end, e, rec in res:
            report(name, end == e and end != 0, 'end %d expected %d, %d leaves, %d reflection' % (end, e, rec['leaves'], rec['refl']))
            cstats.append((name, rec))
        stats['cuts'] = cstats
    if 'roots' in fam:
        idxs = list(range(len(M.ROOTS)))
        if a.roots:
            idxs = [int(x) for x in a.roots.split(',')]
        res = pmap(run_root, [(a.solution, i, a.mutate) for i in idxs])
        rstats = []
        for r, end, e, rec in res:
            report('rc%d' % r, end == e and end != 0, 'end %d expected %d, %d leaves (%d variance), %d reflection, %d splits, max depth %d' %
                   (end, e, rec['leaves'], rec['var'], rec['refl'], rec['splits'], max(rec['depths']) if rec['depths'] else 0))
            if rec['fail']:
                print('   first failing leaf:', rec['fail'][0][:2])
            rstats.append((r, rec))
        stats['roots'] = rstats
    if pool is not None:
        pool.close()
    nfalse = sum(1 for _, ok in results if not ok)
    print('ALL CHECKS TRUE' if nfalse == 0 else '%d CHECK(S) FALSE' % nfalse, '(%.1f s)' % (time.time() - t0))
    if a.stats and 'roots' in stats:
        allrec = stats['roots'] + [(n, r) for (n, r) in stats.get('cuts', [])]
        out = dict(margins=summarize_margins(allrec, M))
        depths = [d for _, rec in allrec for d in rec['depths']]
        out['leaves'] = sum(rec['leaves'] for _, rec in allrec)
        out['reflection_leaves'] = sum(rec['refl'] for _, rec in allrec)
        out['variance_leaves'] = sum(rec['var'] for _, rec in allrec)
        out['splits'] = sum(rec['splits'] for _, rec in allrec)
        out['depth'] = dict(min=min(depths), max=max(depths), mean=sum(depths) / len(depths),
                            hist={str(k): depths.count(k) for k in sorted(set(depths))})
        ax = {}; md = {}
        for _, rec in allrec:
            for k, v in rec['split_axes'].items():
                ax[k] = ax.get(k, 0) + v
            for k, v in rec['split_modes'].items():
                md[k] = md.get(k, 0) + v
        out['split_axes'] = {str(k): ax[k] for k in sorted(ax)}
        out['split_modes'] = {str(k): md[k] for k in sorted(md)}
        out['per_root'] = [dict(root=r, leaves=rec['leaves'], refl=rec['refl'], splits=rec['splits'],
                                maxdepth=max(rec['depths']) if rec['depths'] else 0) for r, rec in stats['roots']]
        out['pv'] = stats.get('pv')
        out['tangent_points'] = stats.get('tangent_points')
        json.dump(out, open(a.stats, 'w'), indent=1, default=str)
        print('stats written to', a.stats)
    return 0 if nfalse == 0 else 1

if __name__ == '__main__':
    sys.exit(main())
