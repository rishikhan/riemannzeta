"""Lean text of the E-format decoder (design A, q9enc/FORMAT.md sections 3 and 4; reference
q9enc/decoder_a.py): a command `zfE nroots ["chunk", ...]` that range-decodes the base-93 text,
rebuilds every root's K-format walk stream and adds the definitions WL<r>_<j> (blocks of 32768 +
WMASK bits, nonzero blocks only) to the current namespace.  The decoder runs at elaboration time;
the kernel only sees the numerals it adds, so decoder errors cannot affect soundness (a wrong
stream makes a root's `decide +kernel` fail).  Every function is total (fuel or `for` loops over
ranges); no `partial`, no `unsafe`.

    decoder_text(Q, wmask_bits) -> str
"""

CODES = list(range(33)) + list(range(64, 97)) + [33, 34]


def decoder_text(Q=9, wmask_bits=1024, block=32768, adjlam=False):
    NT = (Q + 1) * Q // 2
    NP = len([(i, j) for i in range(Q + 1) for j in range(i + 2, Q + 1)])
    PB = NP.bit_length()
    adj = [1 if j - i == 1 else 0 for i in range(Q + 1) for j in range(i + 1, Q + 1)]
    # context table layout (offsets); a tree context with b bits uses indices m = 1 .. 2^b - 1
    # q9enc/FORMAT.md section 4.4 (NT0 .. ME0; total 20,187 for Q = 9)
    sizes = [('nt', 25), ('ax', 64), ('md', 64 * 8), ('rf', 1), ('k', NT * 25 * 4), ('same', NT * 2 * 4),
             ('d1', NT * 128), ('c', NT * 128), ('lam', 2 * 1024), ('mn', 5), ('mc', 64), ('ms', 64),
             ('me', 64 * 16)] + ([('laa', 2 * 1024)] if adjlam else [])
    # adjlam: adjacent kinds 2, 3 also carry a 10-bit lambda, 10-bit tree at LAA + 1024 (k - 2) (q9enc/ecode.py --adj-lam)
    off, o = {}, 0
    for name, n in sizes:
        off[name] = o
        o += n
    total = o
    t = r'''/- E-format decoder (track A design A, q9enc/FORMAT.md section 4; reference q9enc/decoder_a.py).
`zfE n ["chunk", ...]` decodes the base-93 text of the n roots' walk streams at elaboration time and adds
the walk-word literals WL<r>_<j> to the current namespace. -/
section
open Lean Elab Command
namespace ZfE
def dig (c : Char) : Nat := let n := c.toNat; if n < 34 then n - 32 else if n < 92 then n - 33 else n - 34
/-- base-93 text -> bytes: 4 digits = 26 bits, big-endian bit string, trailing partial byte dropped -/
def b93 (s : String) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  let mut acc := 0
  let mut nb := 0
  let mut d := 0
  let mut k := 0
  for c in s.toList do
    d := d * 93 + dig c
    k := k + 1
    if k == 4 then
      acc := acc * 67108864 + d
      nb := nb + 26
      d := 0
      k := 0
      while nb ≥ 8 do
        out := out.push (acc >>> (nb - 8)).toUInt8
        nb := nb - 8
        acc := acc % (1 <<< nb)
  return out
structure RC where
  data : ByteArray
  i : Nat
  range : Nat
  code : Nat
  P : Array Nat
def byte (r : RC) : Nat × RC := (if r.i < r.data.size then (r.data.get! r.i).toNat else 0, { r with i := r.i + 1 })
def norm (r : RC) : RC := Id.run do
  let mut r := r
  for _ in [0:4] do
    if r.range < 16777216 then
      let (b, r') := byte r
      r := { r' with range := (r'.range <<< 8) % 4294967296, code := ((r'.code <<< 8) ||| b) % 4294967296 }
  return r
def init (d : ByteArray) : RC := Id.run do
  let mut r : RC := ⟨d, 0, 4294967295, 0, Array.replicate @TOTAL@ 1024⟩
  for _ in [0:5] do
    let (b, r') := byte r
    r := { r' with code := ((r'.code <<< 8) ||| b) % 1099511627776 }
  return { r with code := r.code % 4294967296 }
def bit (r : RC) (c : Nat) : Nat × RC :=
  let p := r.P[c]!
  let bound := (r.range >>> 11) * p
  if r.code < bound then (0, norm { r with range := bound, P := r.P.set! c (p + ((2048 - p) >>> 5)) })
  else (1, norm { r with code := r.code - bound, range := r.range - bound, P := r.P.set! c (p - (p >>> 5)) })
def tree (r : RC) (base nb : Nat) : Nat × RC := Id.run do
  let mut r := r
  let mut m := 1
  for _ in [0:nb] do
    let (b, r') := bit r (base + m)
    r := r'
    m := 2 * m + b
  return (m - (1 <<< nb), r)
def direct (r : RC) (nb : Nat) : Nat × RC := Id.run do
  let mut r := r
  let mut v := 0
  for _ in [0:nb] do
    let rg := r.range >>> 1
    let b := if r.code ≥ rg then 1 else 0
    r := norm { r with range := rg, code := if b == 1 then r.code - rg else r.code }
    v := 2 * v + b
  return (v, r)
/-- LSB-first bit writer -/
structure BW where
  out : ByteArray
  cur : Nat
  n : Nat
def put (w : BW) (v nb : Nat) : BW := Id.run do
  let mut w := w
  let mut v := v
  for _ in [0:nb] do
    w := { w with cur := w.cur ||| ((v % 2) <<< w.n), n := w.n + 1 }
    v := v / 2
    if w.n == 8 then w := ⟨w.out.push w.cur.toUInt8, 0, 0⟩
  return w
def flush (w : BW) : ByteArray × Nat := (if w.n == 0 then w.out else w.out.push w.cur.toUInt8, 8 * w.out.size + w.n)
/-- little-endian bytes [a, a + n) as a natural number (divide and conquer) -/
def leNat (b : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, a, n => if n == 0 then 0 else if n == 1 then (if a < b.size then (b.get! a).toNat else 0)
    else leNat b f a (n / 2) + (leNat b f (a + n / 2) (n - n / 2) <<< (8 * (n / 2)))
def CODES : Array Nat := #[@CODESLIST@]
def ADJ : Array Nat := #[@ADJLIST@]
/-- one root: preorder decode with a depth stack; prev = previous inequality leaf's (kind, codes) per term -/
def root (r : RC) (prev : Array (Nat × Array Nat)) (fuel : Nat) : RC × Array (Nat × Array Nat) × ByteArray × Nat := Id.run do
  let mut r := r
  let mut prev := prev
  let mut w : BW := ⟨ByteArray.empty, 0, 0⟩
  w := put w 0 1
  let mut todo : Array Nat := #[0]
  for _ in [0:fuel] do
    if todo.isEmpty then break
    let depth := todo.back!
    todo := todo.pop
    let (sp, r1) := bit r (@NT@ + min depth 24)
    r := r1
    if sp == 1 then
      let (ax, r2) := tree r @AX@ 6
      let (md, r3) := tree r2 (@MD@ + ax * 8) 3
      r := r3
      w := put w (1 + 2 * ax + 128 * md) 10
      todo := (todo.push (depth + 1)).push (depth + 1)
      continue
    let (rf, r2) := bit r @RF@
    r := r2
    if rf == 1 then
      w := put w 0 1
      continue
    w := put w 0 1
    let mut terms : Array (Nat × Array Nat) := #[]
    for n in [0:@NTERMS@] do
      let pk := if prev.isEmpty then 4 else prev[n]!.1
      let lk := if n == 0 then 4 else terms[n - 1]!.1
      let (kind, r3) := tree r (@K@ + ((n * 5 + pk) * 5 + lk) * 4) 2
      r := r3
      w := put w kind 2
      let mut cis : Array Nat := #[]
      let nsl := if kind == 0 then 0 else if kind == 3 then 2 else 1
      for sl in [0:nsl] do
        let pc := if prev.isEmpty then #[] else prev[n]!.2
        let mut done := false
        if sl < pc.size then
          let (same, r4) := bit r (@SAME@ + (n * 2 + sl) * 4 + kind)
          r := r4
          if same == 1 then
            cis := cis.push pc[sl]!
            done := true
        if !done then
          if sl == 1 then
            let (d, r4) := tree r (@D1@ + n * 128) 7
            r := r4
            cis := cis.push ((cis[0]! + d) % 128)
          else
            let (c, r4) := tree r (@C@ + n * 128) 7
            r := r4
            cis := cis.push c
        w := put w CODES[cis[sl]!]! 7
      if kind ≥ 2 && ADJ[n]! == 0 then
        let (lam, r4) := tree r (@LAM@ + (kind - 2) * 1024) 10
        r := r4
        w := put w lam 10
@ADJLAM@      terms := terms.push (kind, cis)
    let mut j := 0
    for _ in [0:fuel] do
      let (more, r3) := bit r (@MN@ + min j 4)
      r := r3
      if more == 0 then break
      let (c, r4) := tree r @MC@ 6
      let (sd, r5) := bit r4 (@MS@ + c)
      let (eb, r6) := tree r5 (@ME@ + c * 16) 4
      let (mant, r7) := direct r6 (eb - 1)
      r := r7
      w := put w (1 + 2 * c + (sd <<< (1 + @PB@)) + (((1 <<< (eb - 1)) + mant) <<< (2 + @PB@))) (2 + @PB@ + @QB@)
      j := j + 1
    w := put w 0 1
    prev := terms
  let (bytes, nbits) := flush w
  return (r, prev, bytes, nbits)
end ZfE
elab "zfE " n:num "[" ss:str,* "]" : command => do
  let mut r := ZfE.init (ZfE.b93 (String.join (ss.getElems.map (·.getString)).toList))
  let mut prev : Array (Nat × Array Nat) := #[]
  let ns ← getCurrNamespace
  for rk in [0:n.getNat] do
    let (r', prev', bytes, nbits) := ZfE.root r prev (8 * r.data.size + 64)
    r := r'
    prev := prev'
    for j in [0:(nbits + @BLOCK@ - 1) / @BLOCK@] do
      let v := ZfE.leNat bytes 64 (j * @BLOCKB@) (@BLOCKB@ + @EXTRAB@)
      if v != 0 then
        let v := v % (1 <<< (@BLOCK@ + @EXTRA@))
        let nm := ns ++ Name.mkSimple ("WL" ++ toString rk ++ "_" ++ toString j)
        liftCoreM <| addAndCompile (Declaration.defnDecl (mkDefinitionValEx nm [] (mkConst ``Nat) (mkNatLit v) (.regular 0) .safe [nm]))
end
'''
    rep = {'TOTAL': total, 'NTERMS': NT, 'CODESLIST': ', '.join(map(str, CODES)), 'ADJLIST': ', '.join(map(str, adj)),
           'BLOCKB': block // 8, 'EXTRAB': -(-wmask_bits // 8), 'BLOCK': block, 'EXTRA': wmask_bits, 'PB': PB, 'QB': 14}
    for name in off:
        rep[name.upper()] = off[name]
    rep['ADJLAM'] = ('''      else if kind ≥ 2 then
        let (lam, r4) := tree r (%d + (kind - 2) * 1024) 10
        r := r4
        w := put w lam 10
''' % off['laa']) if adjlam else ''
    for key, v in rep.items():
        t = t.replace('@%s@' % key, str(v))
    assert '@' not in t
    if Q == 9:
        assert total == 20187 + (2048 if adjlam else 0), total
    return t


if __name__ == '__main__':
    print(decoder_text())


def zfe_command(n, text, chunk=60000):
    return 'zfE %d [%s]' % (n, ', '.join('"%s"' % text[k:k + chunk] for k in range(0, len(text), chunk)))
