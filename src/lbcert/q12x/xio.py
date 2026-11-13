"""q12x Python side: inputs for cpp_race/xgen, node files -> Z streams, and the independent exact walk.

* setup(model, pts, workdir): engine dump (fb12.setup / qgen.dump), exact.txt (SIG, cN, BS, TA, QB, YFUEL)
  and one box file per root (root_<k>.box: the root state flattened L, U, A, B).
* read_nodes(path): node file of xgen (preorder records) -> list of nodes ('S', ax, md) | ('R',) | ('J', id) |
  ('L', [(n, z, jp, p, jr, r, lam)], [(c, sd, q)]).
* assemble(top, jobdir): a frontier file with its job files substituted -> one node list (frontier jobs,
  resplits and boxes donated by xgen_st, all "J id" records; FORMAT.md).
* zstream(nodes, NT, AXB, PB, QB): the Z-format kernel stream (bits, end), positions from 1 (q9sparse
  ecode_z.zstream with the split word 1 | ax << 1 | md << (1 + AXB)).
* ZW: q9sparse zfmt.ZChecker (exact mirror of mleafZ, half-space row) with the AXB-bit split word; walk()
  replays a stream against a point table and reports leaves / failures / margins.
"""
import os
import pickle
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
LB = os.path.join(HERE, '..')
for d in ('q12', 'q9sparse'):
    p = os.path.join(LB, d)
    if p not in sys.path:
        sys.path.insert(0, p)
import fb12                                   # noqa: E402
from fb12 import root_state, G                # noqa: E402
import zfmt                                   # noqa: E402

sys.setrecursionlimit(100000)


def setup(model, pts, workdir):
    os.makedirs(workdir, exist_ok=True)
    M, C, P, E = fb12.setup(model, pts)
    eng = model + '.eng'
    with open(os.path.join(workdir, 'exact.txt'), 'w') as f:
        f.write('SIG %d\ncN %d\nQB %d\nYFUEL %d\n' % (M.SIG, M.cN, M.QB, M.YFUEL))
        f.write('BS ' + ' '.join(str(b) for b in M.BS) + '\n')
        f.write('TA ' + ' '.join(str(t[2]) for t in M.TS) + '\n')
    roots = G.roots_of(M)
    for k, idx in enumerate(roots):
        s = root_state(C, idx)
        with open(os.path.join(workdir, 'root_%d.box' % k), 'w') as f:
            f.write(' '.join(str(int(v)) for v in list(s[0]) + list(s[1]) + list(s[2]) + list(s[3])) + '\n')
    return M, C, P, E, eng, roots


def read_nodes(path):
    return parse_nodes(open(path))


def parse_nodes(lines):
    out = []
    for ln in lines:
        if not ln.strip() or ln[0] == '#':
            continue
        v = ln.split()
        if v[0] == 'S':
            out.append(('S', int(v[1]), int(v[2])))
        elif v[0] == 'R':
            out.append(('R',))
        elif v[0] == 'J':
            out.append(('J', v[1]))
        else:
            x = list(map(int, v[1:]))
            nt = x[0]
            t = [tuple(x[1 + 7 * i: 8 + 7 * i]) for i in range(nt)]
            o = 1 + 7 * nt
            nm = x[o]
            y = [tuple(x[o + 1 + 3 * i: o + 4 + 3 * i]) for i in range(nm)]
            out.append(('L', t, y))
    return out


def stats_line(path):
    for ln in open(path):
        if ln.startswith('# rc'):
            v = ln[2:].split()
            return {v[i]: float(v[i + 1]) for i in range(0, len(v) - 1, 2) if v[i] != 'stages'}
    return None


def assemble(top, jobdir, prefix=''):
    """Frontier file with its job files substituted, recursively: a J k record of a file whose job id is P
    refers to job_<P.k>.nodes (top level: job_<k>.nodes); a job file may itself be a frontier (resplit) or
    a tree with placeholders of donated boxes (J p<hex>, xgen --steal-dir), which nest the same way."""
    out = []
    for nd in read_nodes(top):
        if nd[0] == 'J':
            jid = prefix + nd[1]
            f = os.path.join(jobdir, 'job_%s.nodes' % jid)
            if not os.path.exists(f):
                raise FileNotFoundError('job %s (referenced by %s) is not finished' % (jid, top))
            out += assemble(f, jobdir, jid + '.')
        else:
            out.append(nd)
    return out


def zstream(nodes, NT, AXB, PB, QB):
    bits = 0
    pos = 1
    for nd in nodes:
        if nd[0] == 'S':
            bits |= (1 | (nd[1] << 1) | (nd[2] << (1 + AXB))) << pos
            pos += 4 + AXB
        elif nd[0] == 'R':
            pos += 1
        elif nd[0] == 'L':
            mask = 0
            for t in nd[1]:
                mask |= 1 << t[0]
            bits |= mask << (pos + 1)
            o = pos + 1 + NT
            for (n, z, jp, p, jr, r, lam) in nd[1]:
                bits |= z << o; o += 3
                if z != 0:
                    bits |= jp << o; o += 7
                if z == 3:
                    bits |= jr << o; o += 7
                if z in (2, 3) or z >= 4:
                    bits |= lam << o; o += 10
            for (c, sd, q) in nd[2]:
                bits |= (1 | (c << 1) | (sd << (1 + PB)) | (q << (2 + PB))) << o
                o += 2 + PB + QB
            o += 1
            pos = o
        else:
            raise ValueError(nd)
    return bits, pos


def zstream_lines(lines, NT, AXB, PB, QB):
    """zstream of the node records in `lines` (node-file lines, comments skipped) in linear time: the same
    (bits, end) as zstream(parse_nodes(lines), ...), built 32,768 bits at a time instead of OR-ing into one
    growing integer, and without holding the parsed records."""
    out = bytearray()
    acc, na, done = 0, 1, 0                   # bit 0 unused
    for ln in lines:
        if not ln.strip() or ln[0] == '#':
            continue
        v = ln.split()
        if v[0] == 'S':
            w, n = 1 | (int(v[1]) << 1) | (int(v[2]) << (1 + AXB)), 4 + AXB
        elif v[0] == 'R':
            w, n = 0, 1
        elif v[0] == 'L':
            x = list(map(int, v[1:]))
            nt = x[0]
            w, o = 0, 1 + NT
            for i in range(nt):
                tn, z, jp, p, jr, r, lam = x[1 + 7 * i: 8 + 7 * i]
                w |= 1 << (1 + tn)
                w |= z << o; o += 3
                if z != 0:
                    w |= jp << o; o += 7
                if z == 3:
                    w |= jr << o; o += 7
                if z in (2, 3) or z >= 4:
                    w |= lam << o; o += 10
            b = 1 + 7 * nt
            for i in range(x[b]):
                c, sd, q = x[b + 1 + 3 * i: b + 4 + 3 * i]
                w |= (1 | (c << 1) | (sd << (1 + PB)) | (q << (2 + PB))) << o
                o += 2 + PB + QB
            n = o + 1
        else:
            raise ValueError(v[0])
        acc |= w << na
        na += n
        if na >= 1 << 18:
            out += (acc & ((1 << (1 << 18)) - 1)).to_bytes(1 << 15, 'little')
            acc >>= 1 << 18
            na -= 1 << 18
            done += 1 << 18
    out += acc.to_bytes((na + 7) // 8, 'little')
    return int.from_bytes(out, 'little'), done + na


class ZW(zfmt.ZChecker):
    """Z walker with the AXB-bit split word."""
    AXB = 7

    def walkC(self, bits, fuel, pos, s, cuts=None, rec=None, depth=0):
        if fuel == 0:
            return 0
        w = bits(pos)
        if (w & 1) == 1:
            ax = (w >> 1) & ((1 << self.AXB) - 1)
            md = (w >> (1 + self.AXB)) & 7
            return self.splitAx(bits, fuel, md, pos + 4 + self.AXB, ax, s, cuts, rec, depth)
        return self.leafStep(pos, w, s, rec, depth)


def table_from_pts(C, P):
    """{x: expanded word} of the generation table (maximal intervals)."""
    return {x: C.pwD(x, w) for x, w in P.items() if w}


def walk(M, nodes, s, PT, fuel=400):
    """Exact Python walk of the node list from state s against PT(x) -> expanded word (0 if absent).
    Returns dict(ok, leaves, refl, fail, minmargin, nterms)."""
    Z = ZW(M)
    Z.PT = PT
    NT = len(M.TS)
    PB = M.NP.bit_length()
    bits, end = zstream(nodes, NT, fb12.axis_bits(M), PB, M.QB)
    rec = dict(leaves=0, refl=0, margins=[], fail=[], splits=0, split_axes={}, split_modes={}, depths=[], var=0)
    e = Z.walkC(lambda pos: (bits >> pos) & M.WMASK, fuel, 1, s, rec=rec)
    return dict(ok=(e == end), end=e, expect=end, leaves=rec['leaves'], refl=rec['refl'], fail=len(rec['fail']),
                minmargin=min([m for m in rec['margins'] if m is not None], default=None),
                nterms=sum(rec.get('nterms', [])) / max(1, rec['leaves']), bits=end - 1)
