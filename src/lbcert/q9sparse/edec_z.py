"""Lean text of the E-format decoder for the sparse leaf format Z (reference: ecode_z.py, FORMAT.md in this directory):
a command `zfE nroots ["chunk", ...]` that range-decodes the base-93 text, rebuilds every root's Z-format walk stream
and adds the definitions WL<r>_<j> (blocks of 32768 + WMASK bits, nonzero blocks only) with addAndCompile.  It runs
at elaboration time; the kernel sees only the numerals, so a decoder error makes a root's `decide +kernel` fail and
cannot affect soundness.  Every function is total (fuel or `for` loops over ranges); no `partial`, no `unsafe`.

    decoder_text(Q, wmask_bits) -> str
It shares the base-93 reader, the range decoder, the bit writer and the block emission with q9lean/edec/gen_edec.py;
only the leaf syntax and the context layout differ.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'q9lean', 'edec'))
import gen_edec                              # noqa: E402

CODES = gen_edec.CODES


def layout(Q=9):
    NT = (Q + 1) * Q // 2
    sizes = [('nt', 25), ('ax', 64), ('md', 64 * 8), ('rf', 1), ('k', NT * 7 * 7 * 8), ('same', NT * 2 * 8),
             ('d1', NT * 128), ('c', NT * 128), ('lam', 3 * 1024), ('mn', 5), ('mc', 64), ('ms', 64), ('me', 64 * 16)]
    off, o = {}, 0
    for name, n in sizes:
        off[name] = o
        o += n
    return off, o


LEAF = r'''    w := put w 0 1
    let mut mask := 0
    let mut items : Array (Nat × Nat) := #[]
    let mut nsym : Array Nat := #[]
    let mut nci : Array (Array Nat) := #[]
    let mut lk := 6
    for n in [0:@NTERMS@] do
      let pk := psym[n]!
      let (sym, r3) := tree r (@K@ + ((n * 7 + pk) * 7 + lk) * 8) 3
      r := r3
      lk := sym
      nsym := nsym.push sym
      if sym == 0 then
        nci := nci.push #[]
      else
        mask := mask + (1 <<< n)
        let z := sym - 1
        items := items.push (z, 3)
        let nsl := if z == 0 then 0 else if z == 3 then 2 else 1
        let mut cis : Array Nat := #[]
        for sl in [0:nsl] do
          let pc := pci[n]!
          let mut done := false
          if sl < pc.size then
            let (same, r4) := bit r (@SAME@ + (n * 2 + sl) * 8 + sym)
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
          items := items.push (CODES[cis[sl]!]!, 7)
        if z ≥ 2 then
          let (lam, r4) := tree r (@LAM@ + (z - 2) * 1024) 10
          r := r4
          items := items.push (lam, 10)
        nci := nci.push cis
    w := put w mask @NTERMS@
    for it in items do
      w := put w it.1 it.2
'''


def decoder_text(Q=9, wmask_bits=1024, block=32768):
    t = gen_edec.decoder_text(Q, wmask_bits, block)
    NT = (Q + 1) * Q // 2
    off, total = layout(Q)
    old_off, old_total = gen_edec_layout(Q)
    # 1. context array size
    t = t.replace('Array.replicate %d 1024' % old_total, 'Array.replicate %d 1024' % total)
    # 2. the root function: previous-leaf state (symbol and code indices per term)
    t = t.replace('def root (r : RC) (prev : Array (Nat × Array Nat)) (fuel : Nat) : RC × Array (Nat × Array Nat) × ByteArray × Nat := Id.run do',
                  'def root (r : RC) (psym : Array Nat) (pci : Array (Array Nat)) (fuel : Nat) : RC × Array Nat × Array (Array Nat) × ByteArray × Nat := Id.run do')
    t = t.replace('  let mut prev := prev\n', '  let mut psym := psym\n  let mut pci := pci\n')
    i0 = t.index('    w := put w 0 1\n    let mut terms')
    i1 = t.index('    let mut j := 0\n')
    leaf = LEAF
    rep = {'NTERMS': NT, 'K': off['k'], 'SAME': off['same'], 'D1': off['d1'], 'C': off['c'], 'LAM': off['lam']}
    for k, v in rep.items():
        leaf = leaf.replace('@%s@' % k, str(v))
    t = t[:i0] + leaf + t[i1:]
    t = t.replace('    w := put w 0 1\n    prev := terms\n', '    w := put w 0 1\n    psym := nsym\n    pci := nci\n')
    t = t.replace('  return (r, prev, bytes, nbits)', '  return (r, psym, pci, bytes, nbits)')
    # 3. remaining context offsets (node, multiplier contexts)
    for name in ('nt', 'ax', 'md', 'rf', 'mn', 'mc', 'ms', 'me'):
        if old_off[name] != off[name]:
            t = replace_offset(t, name, old_off[name], off[name])
    # 4. the command: initial previous-leaf state
    t = t.replace('  let mut prev : Array (Nat × Array Nat) := #[]\n',
                  '  let mut psym : Array Nat := Array.replicate %d 6\n  let mut pci : Array (Array Nat) := Array.replicate %d #[]\n' % (NT, NT))
    t = t.replace('    let (r\', prev\', bytes, nbits) := ZfE.root r prev (8 * r.data.size + 64)\n    r := r\'\n    prev := prev\'\n',
                  '    let (r\', psym\', pci\', bytes, nbits) := ZfE.root r psym pci (8 * r.data.size + 64)\n    r := r\'\n    psym := psym\'\n    pci := pci\'\n')
    t = t.replace('/- E-format decoder (track A design A, q9enc/FORMAT.md section 4; reference q9enc/decoder_a.py).',
                  '/- E-format decoder for the sparse leaf format (q9enc/FORMAT.md section 4 with the sparse leaf syntax).')
    t = t.replace("prev = previous inequality leaf's (kind, codes) per term", "psym, pci = previous inequality leaf's symbol and code indices per term")
    import re
    assert not re.search(r"\bprev\b|prev'", t), [l for l in t.split('\n') if re.search(r"\bprev\b", l)]
    return t


def gen_edec_layout(Q):
    NT = (Q + 1) * Q // 2
    sizes = [('nt', 25), ('ax', 64), ('md', 64 * 8), ('rf', 1), ('k', NT * 25 * 4), ('same', NT * 2 * 4),
             ('d1', NT * 128), ('c', NT * 128), ('lam', 2 * 1024), ('mn', 5), ('mc', 64), ('ms', 64), ('me', 64 * 16)]
    off, o = {}, 0
    for name, n in sizes:
        off[name] = o
        o += n
    return off, o


def replace_offset(t, name, old, new):
    """the node / multiplier context offsets appear as literals in fixed expressions of gen_edec's template"""
    pats = {'nt': ('bit r (%d + min depth 24)',), 'ax': ('tree r %d 6',), 'md': ('tree r2 (%d + ax * 8) 3',), 'rf': ('bit r %d\n',),
            'mn': ('bit r (%d + min j 4)',), 'mc': ('tree r %d 6\n',), 'ms': ('bit r4 (%d + c)',), 'me': ('tree r5 (%d + c * 16) 4',)}
    for p in pats[name]:
        a, b = p % old, p % new
        assert t.count(a) == 1, (name, a, t.count(a))
        t = t.replace(a, b)
    return t


if __name__ == '__main__':
    print(decoder_text())
