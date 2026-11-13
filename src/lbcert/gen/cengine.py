"""ctypes wrapper of cpp/engine.cpp: model dump, LP margins, batched split evaluation."""
import ctypes
import os
import struct
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LIB = os.path.join(HERE, 'cpp', 'libengine.dylib' if sys.platform == 'darwin' else 'libengine.so')
Q, NP = 8, 28
NS = 2 * Q + 2 * NP


def words64(v):
    out = []
    while v:
        out.append(v & ((1 << 64) - 1))
        v >>= 64
    return out or [0]


def dump(M, C, pts, path):
    """Binary model for eng_load (field order must match engine.cpp)."""
    b = bytearray()
    q = lambda v: b.extend(struct.pack('<q', int(v)))
    u = lambda v: b.extend(struct.pack('<Q', int(v)))
    d = lambda v: b.extend(struct.pack('<d', float(v)))
    for v in (C.SC, M.BB, M.TBIAS, M.KB, M.FS):
        q(v)
    for big in (M.MAGIC, M.BL8):
        w = words64(big)
        q(len(w))
        for x in w:
            u(x)
    for (i, j) in M.PR:
        q(i); q(j)
    for x in M.SL:
        q(x)
    q(len(M.TS))
    for (i, j, a, k) in M.TS:
        q(i); q(j); q(k); d(a / M.SA)
    for x in M.BS:
        d(x / M.SA)
    yunit = 1024e9 * M.SA
    d(M.cN / M.SA); d(M.SIG / yunit); d(M.SIG / yunit * 16383)
    q(len(M.BND))
    for x in M.BND:
        q(x)
    ent = []
    PLV = getattr(C, 'PLV', 20)      # pyramid levels (20 in the Lean checker); engine.cpp infers it from len(ent)
    for l in range(PLV):
        for i in range(1 << (PLV - 1 - l)):
            ent.append(C.entry(l, i))
    q(len(ent))
    b.extend(np.asarray(ent, dtype='<i8').tobytes())
    xs = sorted(x for x, w in pts.items() if w)
    q(len(xs))
    for x in xs:
        q(x)
    for x in xs:
        v = C.pwD(x, pts[x])
        q(v & 0xFFFFFFFF); q((v >> 32) & 0xFFFFFFFF); q((v >> 64) & 0xFFFFFFFF); q(C.ivA(v)); q(C.ivB(v))
    open(path, 'wb').write(bytes(b))


class Engine:
    def __init__(self, path):
        lib = ctypes.CDLL(LIB)
        lib.eng_load.restype = ctypes.c_void_p
        lib.eng_load.argtypes = [ctypes.c_char_p]
        lib.eng_margin.restype = ctypes.c_double
        lib.eng_margin.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_margin_raw.restype = ctypes.c_double
        lib.eng_margin_raw.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_splits.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p, ctypes.c_void_p,
                                   ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int]
        lib.eng_children.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_int,
                                     ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p]
        lib.eng_set_pen.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_int, ctypes.c_double]
        self.lib = lib
        self.h = lib.eng_load(path.encode())
        assert self.h, path

    @staticmethod
    def flat(s):
        return np.asarray(list(s[0]) + list(s[1]) + list(s[2]) + list(s[3]), dtype=np.int64)

    @staticmethod
    def unflat(a):
        a = [int(x) for x in a]
        return (a[:Q], a[Q:2 * Q], a[2 * Q:2 * Q + NP], a[2 * Q + NP:])

    def margin(self, s):
        st = self.flat(s)
        return self.lib.eng_margin(self.h, st.ctypes.data)

    def margin_raw(self, s):
        st = self.flat(s)
        return self.lib.eng_margin_raw(self.h, st.ctypes.data)

    def splits(self, s, axmd, nthreads=1):
        st = self.flat(s)
        ax = np.asarray([a for a, m in axmd], dtype=np.int32)
        md = np.asarray([m for a, m in axmd], dtype=np.int32)
        ml = np.zeros(len(axmd)); mr = np.zeros(len(axmd))
        self.lib.eng_splits(self.h, st.ctypes.data, len(axmd), ax.ctypes.data, md.ctypes.data,
                            ml.ctypes.data, mr.ctypes.data, nthreads)
        return ml, mr

    def children(self, s, ax, md):
        st = self.flat(s)
        l = np.zeros(NS, dtype=np.int64); r = np.zeros(NS, dtype=np.int64); q = np.zeros(1, dtype=np.int64)
        self.lib.eng_children(self.h, st.ctypes.data, ax, md, l.ctypes.data, r.ctypes.data, q.ctypes.data)
        return int(q[0]), self.unflat(l), self.unflat(r)

    def set_pen(self, xs, pen):
        a = np.asarray(sorted(xs), dtype=np.int64)
        self.lib.eng_set_pen(self.h, a.ctypes.data, len(a), pen)
