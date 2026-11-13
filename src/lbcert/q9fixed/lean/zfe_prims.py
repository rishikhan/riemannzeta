"""Faster zfE decoder primitives (same names, signatures and results as q9sparse/edec_z.py's): norm without a loop,
tree / direct by structural recursion, put writes bytes instead of single bits. Used by patch.py."""
OLD_NORM = '''def norm (r : RC) : RC := Id.run do
  let mut r := r
  for _ in [0:4] do
    if r.range < 16777216 then
      let (b, r') := byte r
      r := { r' with range := (r'.range <<< 8) % 4294967296, code := ((r'.code <<< 8) ||| b) % 4294967296 }
  return r
'''
NEW_NORM = '''def shift1 (r : RC) : RC :=
  let (b, r') := byte r
  { r' with range := (r'.range <<< 8) % 4294967296, code := ((r'.code <<< 8) ||| b) % 4294967296 }
/-- the four rounds of the range renormalisation, unrolled -/
def norm (r : RC) : RC :=
  if r.range < 16777216 then
    let r := shift1 r
    if r.range < 16777216 then
      let r := shift1 r
      if r.range < 16777216 then
        let r := shift1 r
        if r.range < 16777216 then shift1 r else r
      else r
    else r
  else r
'''
OLD_TREE = '''def tree (r : RC) (base nb : Nat) : Nat × RC := Id.run do
  let mut r := r
  let mut m := 1
  for _ in [0:nb] do
    let (b, r') := bit r (base + m)
    r := r'
    m := 2 * m + b
  return (m - (1 <<< nb), r)
'''
NEW_TREE = '''def treeGo (base : Nat) : Nat → Nat → RC → Nat × RC
  | 0, m, r => (m, r)
  | k + 1, m, r => let (b, r') := bit r (base + m); treeGo base k (2 * m + b) r'
def tree (r : RC) (base nb : Nat) : Nat × RC :=
  let (m, r) := treeGo base nb 1 r
  (m - (1 <<< nb), r)
'''
OLD_DIRECT = '''def direct (r : RC) (nb : Nat) : Nat × RC := Id.run do
  let mut r := r
  let mut v := 0
  for _ in [0:nb] do
    let rg := r.range >>> 1
    let b := if r.code ≥ rg then 1 else 0
    r := norm { r with range := rg, code := if b == 1 then r.code - rg else r.code }
    v := 2 * v + b
  return (v, r)
'''
NEW_DIRECT = '''def directGo : Nat → Nat → RC → Nat × RC
  | 0, v, r => (v, r)
  | k + 1, v, r =>
    let rg := r.range >>> 1
    if r.code ≥ rg then directGo k (2 * v + 1) (norm { r with range := rg, code := r.code - rg })
    else directGo k (2 * v) (norm { r with range := rg })
def direct (r : RC) (nb : Nat) : Nat × RC := directGo nb 0 r
'''
OLD_PUT = '''def put (w : BW) (v nb : Nat) : BW := Id.run do
  let mut w := w
  let mut v := v
  for _ in [0:nb] do
    w := { w with cur := w.cur ||| ((v % 2) <<< w.n), n := w.n + 1 }
    v := v / 2
    if w.n == 8 then w := ⟨w.out.push w.cur.toUInt8, 0, 0⟩
  return w
'''
NEW_PUT = '''def putFlush : Nat → ByteArray → Nat → Nat → BW
  | 0, out, cur, n => ⟨out, cur, n⟩
  | f + 1, out, cur, n => if n ≥ 8 then putFlush f (out.push (cur % 256).toUInt8) (cur >>> 8) (n - 8) else ⟨out, cur, n⟩
/-- append the low nb bits of v, LSB first, whole bytes at a time -/
def put (w : BW) (v nb : Nat) : BW :=
  putFlush ((w.n + nb) / 8 + 1) w.out (w.cur ||| ((v % (1 <<< nb)) <<< w.n)) (w.n + nb)
'''
PAIRS = [(OLD_NORM, NEW_NORM), (OLD_TREE, NEW_TREE), (OLD_DIRECT, NEW_DIRECT), (OLD_PUT, NEW_PUT)]
