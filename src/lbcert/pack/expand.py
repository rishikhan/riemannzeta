"""Expands the zfPTT / zfPyr payloads of a packed Solution.lean back into the literal text that
gen/emit.py writes (PTT trees with hex words; TOP, TOPD, BKD_j as zfNat64, BK_j as hex; the
dsel/dpk dispatch definitions). The decoding mirrors the Lean macros of namespace ZeroForgePack.

Usage: python -I expand.py PACKED.lean OUT.lean
"""
import os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, '..'))
import codec
from replay import decode64
from gen.emit import zf, dispatch

FMT = {'TOP': zf, 'TOPD': zf, 'BK': hex, 'BKD': zf}


def num_literal(s):
    m = re.fullmatch(r'zfNat64 (\d+) "([A-Za-z0-9+_]*)"', s)
    return decode64(int(m[1]), m[2]) if m else int(s, 0)


def pyr_ranges(lines):
    """[(first line, last line, top name, block name, lanes)] of the two pyramid definitions."""
    out = []
    for top, bk, lanes in (('TOP', 'BK', 1), ('TOPD', 'BKD', 2)):
        a = [i for i, L in enumerate(lines) if L.startswith('def %s : ℕ := ' % top)]
        b = [i for i, L in enumerate(lines) if L.startswith('def %s (j : ℕ) : ℕ := ' % bk)]
        assert len(a) == 1 and len(b) == 1 and a[0] < b[0]
        for L in lines[a[0] + 1:b[0]]:
            assert re.match(r'def %s(_\d+ : ℕ|s\d+_\d+ \(j : ℕ\) : ℕ) := ' % bk, L), L[:80]
        out.append((a[0], b[0], top, bk, lanes))
    return out


def pyr_text(top, bk, lanes, payload):
    v, blocks = codec.pyr_decode(payload, lanes)
    L = ['def %s : ℕ := %s' % (top, FMT[top](v))]
    keys = sorted(blocks)
    L += ['def %s_%d : ℕ := %s' % (bk, j, FMT[bk](blocks[j])) for j in keys]
    return L + dispatch(bk, keys, lambda j: '%s_%d' % (bk, j), bk)


def expand(text):
    out = []
    for L in text.split('\n'):
        m = re.fullmatch(r'zfPyr (\w+) (\w+) (\d+) "([A-Za-z0-9+_]*)"', L)
        if m:
            out += pyr_text(m[1], m[2], int(m[3]), m[4])
            continue
        m = re.fullmatch(r'def (PTT_\d+) : PTrD := zfPTT "([A-Za-z0-9+_]*)"', L)
        if m:
            L = 'def %s : PTrD := %s' % (m[1], codec.ptt_tree_text(codec.ptt_decode(m[2])))
        m = re.fullmatch(r'def (PTT_\d+) : PTrD := zfPTTN "([A-Za-z0-9+_]*)"', L)
        if m:
            L = 'def %s : PTrD := %s' % (m[1], codec.ptt_tree_text(codec.ptt_decode_n(m[2])))
        assert ':= zfPTT "' not in L and ':= zfPTTN "' not in L and not L.startswith('zfPyr '), L[:80]
        out.append(L)
    return '\n'.join(out)


if __name__ == '__main__':
    open(sys.argv[2], 'w', encoding='utf-8').write(expand(open(sys.argv[1], encoding='utf-8').read()))
