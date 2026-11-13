"""Split one root's node file into subtrees with their start boxes, for running xgen per part in parallel.

    parts(M, box_state, lines, lim) -> (cuts, states)

lines: the node records of a whole tree (xgen node file without comment lines), preorder.  The tree is cut into
maximal subtrees of at most `lim` leaves (a single leaf or reflection is always a part); the skeleton above the
cuts (split records only) is walked with the checker's split functions (xio.ZW.splitAx, as pycheck_par.py does),
which gives the state at every cut.  Returns cuts [(i, j, depth)] (the part is lines[i:j]) in preorder and the
state of each cut as a flat list (L, U, A, B), the format of a .box file.
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import xio                                    # noqa: E402


def structure(lines):
    """end index (after the subtree) and leaf count per record, from the record kinds only"""
    n = len(lines)
    end = [0] * n
    nleaf = [0] * n
    stack = []
    for k, ln in enumerate(lines):
        c0 = ln[0]
        if c0 == 'S':
            stack.append([k, 2])
            continue
        if c0 not in 'LR':
            raise ValueError('record %d: %r' % (k, ln[:20]))
        e, c = k + 1, (1 if c0 == 'L' else 0)
        end[k], nleaf[k] = e, c
        while stack:
            top = stack[-1]
            top[1] -= 1
            nleaf[top[0]] += c
            if top[1] > 0:
                break
            stack.pop()
            end[top[0]] = e
            c = nleaf[top[0]]
    if stack or (n and end[0] != n):
        raise ValueError('bad tree structure')
    return end, nleaf


def parts(M, s0, lines, lim):
    end, nleaf = structure(lines)
    cuts = {}
    st = [(0, 0)]
    while st:
        k, d = st.pop()
        if lines[k][0] != 'S' or nleaf[k] <= lim:
            cuts[k] = d
            continue
        st.append((end[k + 1], d + 1))
        st.append((k + 1, d + 1))
    states = {}

    class Skel(xio.ZW):
        # positions are record indices: the left child of a split record k is record k + 1
        def walkC(self, bits, fuel, p, s, cuts_=None, rec=None, depth=0):
            if p in cuts:
                states[p] = s
                return end[p]
            v = lines[p].split()
            assert v[0] == 'S'
            return self.splitAx(bits, fuel, int(v[2]), p + 1, int(v[1]), s, None, None, depth)

    e = Skel(M).walkC(None, 10 ** 9, 0, s0)
    assert e == len(lines) and len(states) == len(cuts)
    out = sorted((k, end[k], d) for k, d in cuts.items())
    flat = {k: [int(x) for x in list(s[0]) + list(s[1]) + list(s[2]) + list(s[3])] for k, s in states.items()}
    return out, flat
