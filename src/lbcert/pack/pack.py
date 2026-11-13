"""Packs the PTT_k and pyramid literals of a Solution.lean into zfPTT / zfPyr payloads.

Usage: python -I pack.py IN.lean OUT.lean [--test TEST.lean]

The packed file is checked here by expanding it back (expand.py) and comparing with IN byte for
byte. With --test, also writes a Lean file that elaborates the original and the packed
declarations side by side (namespaces Old and New, with stub copies of PTrD, dsel and dpk) and
compares every constant's type and value Expr (Expr.equal, after renaming Old.* to New.*).
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import codec
from expand import expand, num_literal, pyr_ranges

CHANGE_ANCHOR = '  427269334276793352226483860057466636485376/634306291990192240529320608054656982421875.\n-/\n'
CHANGE_LINE = (
    '* Packed literals (Rishi Khan, 2026-10-23): the tangent point table PTT_0 .. PTT_31 and the pyramids TOP/BK and\n'
    '  TOPD/BKD (with their dsel/dpk dispatch definitions) are written as `zfPTT` / `zfPyr` payloads: exp-Golomb\n'
    '  codes of field deltas in the zfNat64 alphabet, decoded at elaboration time by the macros of namespace\n'
    '  ZeroForgePack into the same declarations and terms (up to the hygienic binder names that the list literal\n'
    '  macro introduces), so the kernel checks the same expressions.\n')


def pack(src):
    lines = src.split('\n')
    out = list(lines)
    # pyramids: replace each range [TOP .. def BK] by one zfPyr command
    for (a, b, top, bk, lanes) in reversed(pyr_ranges(lines)):
        blk = '\n'.join(lines[a:b + 1])
        topv = num_literal(re.search(r'^def %s : ℕ := (.+)$' % top, blk, re.M)[1])
        blocks = {int(j): num_literal(v) for j, v in re.findall(r'^def %s_(\d+) : ℕ := (.+)$' % bk, blk, re.M)}
        out[a:b + 1] = ['zfPyr %s %s %d "%s"' % (top, bk, lanes, codec.pyr_encode(topv, blocks, lanes))]
    res = []
    for L in out:
        m = re.fullmatch(r'def (PTT_\d+) : PTrD := (.+)', L)
        if m:
            E = []
            for j, lst in re.findall(r'\.lf (\d+) \[([^\]]*)\]', m[2]):
                for o, w in re.findall(r'\((\d+), (0x[0-9a-f]+)\)', lst):
                    E.append((int(j) * 1024 + int(o), int(w, 16)))
            assert codec.ptt_tree_text(E) == m[2], m[1]
            if any(w >> 140 for _, w in E):
                L = 'def %s : PTrD := zfPTTN "%s"' % (m[1], codec.ptt_encode_n(E))
            else:
                L = 'def %s : PTrD := zfPTT "%s"' % (m[1], codec.ptt_encode(E))
        res.append(L)
    return '\n'.join(res)


def add_header(packed):
    """Inserts the decoder after the zfNat64 macro and the line in the Changes block."""
    dec = open(os.path.join(HERE, 'Decoder.lean')).read()
    anchor = '    Lean.Macro.throwErrorAt payload message\nset_option Elab.async false\n'
    assert packed.count(anchor) == 1 and packed.count(CHANGE_ANCHOR) == 1
    packed = packed.replace(anchor, anchor.replace('set_option', dec + 'set_option'))
    packed = packed.replace(CHANGE_ANCHOR, CHANGE_ANCHOR[:-3] + CHANGE_LINE + '-/\n')
    return packed


def check_words(src, packed):
    for bad in ('sorry', 'admit', 'axiom', 'native', 'extern', 'unsafe', 'implemented'):
        assert packed.count(bad) == src.count(bad), bad


def test_file(src, packed):
    """Lean file elaborating the original and the packed data declarations side by side."""
    hdr0 = src.index('namespace ZeroForgePackedNat')
    hdr1 = src.index('set_option Elab.async false\n')
    dec = open(os.path.join(HERE, 'Decoder.lean')).read()
    lines = src.split('\n')
    plines = packed.split('\n')
    old = [L for L in lines if is_data(L)]
    new = [L for L in plines if is_data(L) or L.startswith('zfPyr ')]
    ptrd = re.search(r'^inductive PTrD where\n.*\n.*\n', src, re.M)[0]
    dsel = re.search(r'^def dsel .*\n', src, re.M)[0] + re.search(r'^def dpk .*\n', src, re.M)[0]
    body = ['import Mathlib', src[hdr0:hdr1] + dec,
            'namespace AMW.Cert.PCell', ptrd + 'end AMW.Cert.PCell',
            'noncomputable section', 'namespace AMW.Cert.PyrD', dsel + 'end AMW.Cert.PyrD', 'set_option maxRecDepth 100000',
            'namespace Old', 'open AMW.Cert.PyrD AMW.Cert.PCell'] + old + ['end Old',
            'namespace New', 'open AMW.Cert.PyrD AMW.Cert.PCell', 'set_option profiler true',
            'set_option profiler.threshold 1'] + new + ['set_option profiler false', 'end New', 'end',
            open(os.path.join(HERE, 'Compare.lean')).read()]
    names = [re.match(r'def (\w+)', L)[1] for L in old if re.match(r'def (TOP|TOPD|BK|BKD|PTT_\d+) ', L)]
    body += ['theorem rfl_%s : Old.%s = New.%s := rfl' % (n, n, n) for n in names]
    return '\n'.join(body) + '\n'


def is_data(L):
    return bool(re.match(r'def (TOP|TOPD|BK|BKD|PTT_\d+|BKs\d+_\d+|BKDs\d+_\d+|BK_\d+|BKD_\d+) ', L))


def main():
    a = sys.argv[1:]
    src = open(a[0], encoding='utf-8').read()
    packed = add_header(pack(src))
    check_words(src, packed)
    assert expand(packed) == add_header(src), 'expansion differs from the input'
    open(a[1], 'w', encoding='utf-8').write(packed)
    print('%s: %d bytes -> %s: %d bytes' % (a[0], len(src.encode()), a[1], len(packed.encode())))
    if '--test' in a:
        open(a[a.index('--test') + 1], 'w', encoding='utf-8').write(test_file(src, packed))


if __name__ == '__main__':
    main()
