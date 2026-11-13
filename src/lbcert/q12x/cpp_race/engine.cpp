// q12x snapshot of src/lbcert/q12/cpp/engine.cpp (sha1 7aeff611), replay.inc dropped.
// src/lbcert/q12 copy of q9hs/cpp/engine.cpp plus builder.inc (float tree builder in C++).
// Leaf LP and split evaluation for the (Q+1)-point certificate generator (Q gaps, NP pairs read
// from the model dump; src/lbcert/gen/cpp/engine.cpp with Q = 8, NP = 28 fixed).
//
// q9hs copy of src/lbcert/q9/cpp/engine.cpp with two leaf-LP options (eng_set_opts):
//   half: the reflection half-space g_0 <= g_{Q-1} as one more multiplier column (attempt-032's
//         PCellHalf row): row Q-1 coefficient +1, row 0 coefficient -1, objective (L_0 - L_{Q-1})/SC,
//         bound [0, ymax] like a pair multiplier.
//   var:  attempt-031's anchor-variance bonus (mleafV / vbW): for a term whose range spans at most
//         five 256-cells, extra columns for two-tangent mixes (p, r, lambda) with lambda in
//         {1/4, 1/2, 3/4} and (p, r) neighbours or second neighbours among the term's valid anchors
//         sorted by position, valued lambda-mix of the two tangents
//         + (mu/VD) lambda (1 - lambda) ((p - r)/SC)^2 / 2, mu = 2^19 min TB field over the range's
//         cells.  (For w'' = mu exactly this is the tangent at the mixed point: the bonus acts as a
//         virtual anchor between two table points.)
//   void eng_set_opts(void*, int half, int var, const int64_t* tbf, int ntb, double VD)
//
// Mirrors leaf.py LeafSolver.solve_lp (margin model of FORMAT.md section 8) and the
// closure split of replay.py (cuB / colB / rowB, fracQ, bcutL).  Exactness is not needed
// here: these margins only guide the tree builder; every emitted leaf is certified in
// Python against replay.py's exact checker.
//
// C ABI for ctypes:
//   void* eng_load(const char* path)            model dump written by cengine.py
//   double eng_margin(void*, const int64_t* st)  LP margin of one cell (F units)
//   void eng_splits(void*, const int64_t* st, int n, const int* ax, const int* md,
//                   double* ml, double* mr, int nthreads)
//   void eng_children(void*, const int64_t* st, int ax, int md, int64_t* left, int64_t* right, int64_t* q)
//   double eng_margin_raw(void*, const int64_t* st)  same without the anchor penalty
//   void eng_set_pen(void*, const int64_t* xs, int n, double pen)   shared anchors; others pay pen
#include <cstdint>
#include <climits>
#include <atomic>
#include <chrono>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cmath>
#include <vector>
#include <thread>
#include <algorithm>
#include <unordered_set>
#include <unordered_map>
#include <memory>
#include "Highs.h"

typedef int64_t i64;
static const int MAXQ = 16, MAXNP = 136, MAXNS = 2 * MAXQ + 2 * MAXNP;

struct Model {
  int Q, NP, NS;
  i64 SC, BB, TBIAS, KB;
  int FS;
  uint64_t MAGIC_lo, MAGIC_hi;  // MAGIC < 2^128? stored as words
  std::vector<uint64_t> MAGIC;  // little-endian 64-bit words
  std::vector<uint64_t> BL8;
  int PI[MAXNP], PJ[MAXNP];
  std::vector<int> SL;
  int nT;
  std::vector<int> TI, TJ, TK;
  std::vector<double> ta;   // a_n
  double tb[MAXQ];          // b_r
  double c;                 // cN / SA
  double yq, ymax;
  std::vector<i64> BND;
  // pyramid entries: level l, index i -> value; offsets per level
  std::vector<uint32_t> ent;
  i64 eoff[24];
  int PLV = 20;             // pyramid levels: lb domain x < 2^(PLV-1); 20 in the Lean checker, set from the entry count
  // points: per x index into arrays (or -1)
  std::vector<int> pidx;
  std::vector<uint64_t> hasp;   // bit x set when pidx[x] >= 0
  // the points packed in increasing x (one record per x with pidx[x] >= 0, from that index):
  // record of x = prank[x >> 6] + popcount(hasp[x >> 6] below bit x & 63); one cache line per lookup
  struct PRec { i64 V, P, M, A, B; int shared, pad; };
  std::vector<uint32_t> prank;
  std::vector<PRec> prec;
  std::vector<std::pair<int32_t, int32_t>> pab;   // (A, B) per record: the interval test touches 8 bytes
  void pack_points() {
    prank.assign(hasp.size(), 0);
    prec.clear(); pab.clear();
    for (size_t w = 0; w < hasp.size(); w++) {
      prank[w] = (uint32_t)prec.size();
      for (int b = 0; b < 64; b++) {
        size_t x = (w << 6) + b;
        if (x < pidx.size() && pidx[x] >= 0) { int i = pidx[x]; prec.push_back({pV[i], pP[i], pM[i], pA[i], pB[i], shared[i], 0});
          pab.push_back({(int32_t)std::min<i64>(std::max<i64>(pA[i], INT32_MIN), INT32_MAX), (int32_t)std::min<i64>(std::max<i64>(pB[i], INT32_MIN), INT32_MAX)}); }
      }
    }
  }
  std::vector<i64> pV, pP, pM, pA, pB;
  std::vector<char> shared;   // per point: shared anchor flag
  double pen = 0.0;
  int half = 0, var = 0;
  std::vector<int> tbf;     // curvature field per 256-cell (0 = none)
  double VD = 1e9;
};

static int getbits(const std::vector<uint64_t>& w, int pos, int n) {
  // bits [pos, pos+n) of a little-endian multiword integer
  int res = 0;
  for (int b = 0; b < n; b++) {
    int p = pos + b;
    int wi = p >> 6;
    if (wi < (int)w.size() && ((w[wi] >> (p & 63)) & 1ULL)) res |= 1 << b;
  }
  return res;
}

static i64 nsub(i64 a, i64 b) { return a > b ? a - b : 0; }

struct Eng {
  Model m;
  int Q, NP;
  // ---------------------------------------------------------------- pyramid lb
  int blen(i64 x) const {
    if (x >= 256) return 8 + getbits(m.BL8, 4 * (int)(x >> 8), 4);
    return getbits(m.BL8, 4 * (int)x, 4);
  }
  i64 entry(int l, i64 i) const {
    if (l >= m.PLV) return 0;
    i64 n = (i64)1 << (m.PLV - 1 - l);
    if (i < 0 || i >= n) return 0;   // beyond the pyramid
    return m.ent[m.eoff[l] + i];
  }
  i64 lb(i64 lo, i64 hi) const {
    if (hi <= lo || ((i64)1 << (m.PLV - 1)) + 1 <= hi) return 0;
    int k = blen(nsub(hi, lo) >> 5);
    i64 ib = nsub(hi, 1) >> k, g = lo >> k;
    i64 E = ib + 1;
    i64 best = -1;
    for (int n = 14; n > 0; n--) {
      i64 d = nsub(E, g);
      int t = getbits(m.MAGIC, 3 * (int)(17 * (g & 15) + nsub(d, nsub(d, 16))), 3);
      i64 h = g >> t;
      i64 v = entry(k + t, h);
      best = best < 0 ? v : std::min(best, v);
      i64 nxt = (h + 1) << t;
      if (E <= nxt) return best;
      g = nxt;
    }
    return best < 0 ? 0 : std::min(best, (i64)0);   // fuel exhausted: dstep returns 0 at n = 0
  }
  i64 gpt(i64 L, i64 U, int jj) const {
    if (jj == 33) return L;
    if (jj == 34) return U;
    int gs = ((jj >> 6) & 1) ? m.FS : 8;
    i64 x = L + ((nsub(U, L) * (jj & 63)) >> 5);
    i64 A = (x >> gs) << gs;
    i64 cL = ((L + ((1LL << gs) - 1)) >> gs) << gs;
    i64 fU = (U >> gs) << gs;
    if (A <= cL) return cL;
    return fU <= A ? fU : A;
  }
  // ---------------------------------------------------------------- closure split
  i64 slo(const i64* s, int x) const { return x < Q ? s[x] : s[2 * Q + (x - Q)]; }
  i64 shi(const i64* s, int x) const { return x < Q ? s[Q + x] : s[2 * Q + NP + (x - Q)]; }
  i64 dE(const i64* s, i64 E, int a, int b) const {
    if (a < b) return E + shi(s, m.SL[a * (Q + 1) + b]);
    if (a == b) return E;
    return nsub(E, slo(s, m.SL[b * (Q + 1) + a]));
  }
  void cuB(const i64* s, const i64* X, const i64* Y, i64* o) const {
    i64 TB = m.TBIAS;
    for (int r = 0; r < Q; r++) {
      o[r] = std::max(s[r], nsub(TB, X[r + 1] + Y[r]));
      o[Q + r] = std::min(s[Q + r], nsub(X[r] + Y[r + 1], TB));
    }
    for (int k = 0; k < NP; k++) {
      o[2 * Q + k] = std::max(s[2 * Q + k], nsub(TB, X[m.PJ[k]] + Y[m.PI[k]]));
      o[2 * Q + NP + k] = std::min(s[2 * Q + NP + k], nsub(X[m.PI[k]] + Y[m.PJ[k]], TB));
    }
  }
  i64 bcutL(i64 bm, i64 lo, i64 hi) const {
    i64 acc = (lo + hi) >> 1;
    bool have = false;
    auto bdist = [](i64 sm, i64 z) { return nsub(z + z, sm) + nsub(sm, z + z); };
    for (i64 z : m.BND)
      if (lo + bm <= z && z + bm <= hi && ((!have) || bdist(lo + hi, z) < bdist(lo + hi, acc))) { acc = z; have = true; }
    return acc;
  }
  i64 cut(i64 lo, i64 hi, int md) const {
    if (md >= 2) return lo + ((nsub(hi, lo) * (md <= 4 ? md - 1 : md)) >> 3);
    if (md == 1) return bcutL(64, lo, hi);
    return (lo + hi) >> 1;
  }
  void children(const i64* s, int ax, int md, i64* left, i64* right, i64* qo) const {
    int i, j; i64 lo, hi;
    if (ax < Q) { i = ax; j = ax + 1; lo = s[ax]; hi = s[Q + ax]; }
    else { i = m.PI[ax - Q]; j = m.PJ[ax - Q]; lo = s[2 * Q + ax - Q]; hi = s[2 * Q + NP + ax - Q]; }
    i64 q = cut(lo, hi, md);
    i64 X[MAXQ + 1], Y[MAXQ + 1];
    for (int x = 0; x <= Q; x++) { X[x] = dE(s, m.BB, x, i); Y[x] = dE(s, m.BB + q, j, x); }
    cuB(s, X, Y, left);
    for (int x = 0; x <= Q; x++) { X[x] = dE(s, m.BB, x, j); Y[x] = dE(s, nsub(m.BB, q), i, x); }
    cuB(s, X, Y, right);
    if (qo) *qo = q;
  }
  // ---------------------------------------------------------------- LP
  struct Cand { double val, slope; };
  // Warm start: the optimal basis of one margin LP, keyed by column identity (term n and anchor p,
  // the term's constant column, pair multiplier, half-space row, kappa slack), so that it can seed
  // the LP of a related box whose anchor columns differ.
  struct WS {
    bool ok = false;
    std::vector<i64> key;    // term columns only; the columns after them are the same in every box
    std::vector<int> tcol;   // first column per term, nT + 1 entries
    HighsBasis b;
    std::vector<std::pair<i64, int>> skey;   // (key, column) sorted within each term's range (warm lookup)
    std::vector<double> y;   // kappa-row duals (Q entries, >= 0) for ub(); empty when unset
  };
  static i64 tkey(int n, i64 p) { return ((i64)n << 32) | (p & 0xffffffffLL); }
  // map wi's basis onto an LP whose term columns have keys ckey (term boundaries tc) and pass it to h
  void warm(Highs& h, const WS& wi, const std::vector<i64>& ckey, const std::vector<int>& tc, int ncol, int nrow) const {
    HighsBasis b;
    b.col_status.assign(ncol, HighsBasisStatus::kLower);
    b.row_status = wi.b.row_status;
    int nb = 0;
    for (int r = 0; r < nrow; r++) if (b.row_status[r] == HighsBasisStatus::kBasic) nb++;
    for (int n = 0; n < m.nT; n++) {
      int o0 = wi.tcol[n], o1 = wi.tcol[n + 1];
      bool any = false;
      if (wi.skey.empty()) {
        for (int c = tc[n]; c < tc[n + 1]; c++)
          for (int u = o0; u < o1; u++)
            if (wi.key[u] == ckey[c]) {
              b.col_status[c] = wi.b.col_status[u];
              if (b.col_status[c] == HighsBasisStatus::kBasic) { nb++; any = true; }
              break;
            }
      } else {
        auto b0 = wi.skey.begin() + o0, b1 = wi.skey.begin() + o1;
        for (int c = tc[n]; c < tc[n + 1]; c++) {
          auto it = std::lower_bound(b0, b1, std::make_pair(ckey[c], INT_MIN));
          if (it == b1 || it->first != ckey[c]) continue;
          b.col_status[c] = wi.b.col_status[it->second];
          if (b.col_status[c] == HighsBasisStatus::kBasic) { nb++; any = true; }
        }
      }
      // a term whose basic columns all vanished: its constant column (always present) becomes basic
      if (!any && nb < nrow && b.row_status[Q + n] != HighsBasisStatus::kBasic) {
        b.col_status[tc[n]] = HighsBasisStatus::kBasic; nb++;
      }
    }
    // the remaining columns (pairs, half-space, kappa slacks) are the same in every box
    int o = wi.tcol[m.nT];
    for (int c = tc[m.nT]; c < ncol; c++, o++) {
      b.col_status[c] = wi.b.col_status[o];
      if (b.col_status[c] == HighsBasisStatus::kBasic) nb++;
    }
    for (int r = 0; r < Q && nb < nrow; r++)
      if (b.row_status[r] != HighsBasisStatus::kBasic) { b.row_status[r] = HighsBasisStatus::kBasic; nb++; }
    if (nb != nrow) return;      // cannot happen with a consistent wi; solve cold
    b.valid = true;
    // XG_ALIEN=0: pass the basis as non-alien (HiGHS then checks only its consistency instead of
    // scaling and factorising in setBasis and again in run)
    static const bool alien = !(getenv("XG_ALIEN") && atoi(getenv("XG_ALIEN")) == 0);
    b.alien = alien;
    h.setBasis(b);
  }
  // profiling counters (XG_PROF=1): LPs, simplex iterations, seconds in build / warm / run
  static bool prof_on() { static int v = getenv("XG_PROF") ? atoi(getenv("XG_PROF")) : 0; return v != 0; }
  struct Prof { std::atomic<long long> lp{0}, it{0}, ub{0}, ubmiss{0}; std::atomic<long long> ns_build{0}, ns_warm{0}, ns_run{0}, ns_ub{0}; };
  static Prof& prof() { static Prof p; return p; }
  static long long tns() { return std::chrono::duration_cast<std::chrono::nanoseconds>(std::chrono::steady_clock::now().time_since_epoch()).count(); }
  void term_range(const i64* s, int n, i64& eL, i64& eU, i64& L0) const {
    const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
    int i = m.TI[n], j = m.TJ[n], kk = m.TK[n];
    i64 sL = 0, sU = 0;
    for (int r = i; r < j; r++) { sL += L[r]; sU += U[r]; }
    if (j - i == 1) { eL = L[i]; eU = U[i]; } else { eL = std::max(A[kk], sL); eU = std::min(B[kk], sU); }
    L0 = sL;
  }
  // columns of term n with ranges (eL, eU, L0), in LP order: f(val, slope, key) (key -1: mixed column)
  template <class F> void termcols(int n, i64 eL, i64 eU, i64 L0, bool usepen, F&& f) const {
    const double SCd = (double)m.SC;
    double an = m.ta[n];
    i64 lbv = lb(eL, std::max(eU, eL + 1));
    f((double)lbv / 1e10, 0.0, tkey(n, -1));
    // gpt is nondecreasing in jj within the coarse (0..32) and the fine (64..96) family, so a
    // family's new point repeats an earlier point of its own family only when it equals the
    // previous one, and the coarse points in seen are ascending (same result as a full search)
    i64 seen[80]; int ns = 0;
    i64 vp[80]; double vv[80], vs[80]; int nv = 0;
    int f0 = 0, fc = 0, cp = 0;
    i64 prev = -1;
    for (int t = 0; t < 2 + 33 + 33; t++) {
      int jj = t < 2 ? 33 + t : (t < 35 ? t - 2 : 64 + (t - 35));
      if (t == 2) { f0 = ns; prev = -1; }
      if (t == 35) { fc = ns; prev = -1; cp = f0; }
      i64 p = gpt(eL, eU, jj);
      if (p < eL || p > eU) continue;
      if (t >= 2) {
        if (p == prev) continue;
        prev = p;
      }
      bool dup = false;
      for (int u = 0; u < (t < 2 ? ns : f0); u++) if (seen[u] == p) { dup = true; break; }
      if (t >= 35 && !dup) {
        while (cp < fc && seen[cp] < p) cp++;
        dup = cp < fc && seen[cp] == p;
      }
      if (dup) continue;
      seen[ns++] = p;
      if (p < 0 || p >= (i64)m.pidx.size()) continue;
      const uint64_t hw = m.hasp[p >> 6];
      if (!((hw >> (p & 63)) & 1)) continue;   // no point at p (pidx[p] < 0)
      const size_t ri = m.prank[p >> 6] + __builtin_popcountll(hw & ((1ULL << (p & 63)) - 1));
      // pre-test on (A, B) clamped to int32 (exact for |eL|, |eU| < 2^31); the full record repeats the test
      if (!(m.pab[ri].second >= 1 && (i64)m.pab[ri].first <= eL && eU <= (i64)m.pab[ri].second)) continue;
      const Model::PRec& R = m.prec[ri];
      if (!(1 <= R.B && R.A <= eL && eL <= p && p <= eU && eU <= R.B)) continue;
      double val = (double)R.V / 1e10 - (2e9 - (double)R.M) / 1e9 * (double)nsub(p, L0) / SCd;
      if (usepen && m.pen > 0 && !R.shared) val -= m.pen / std::max(an, 1e-12);
      f(val, ((double)R.P - 2e9) / 1e9, tkey(n, p));
      vp[nv] = p; vv[nv] = val; vs[nv] = ((double)R.P - 2e9) / 1e9; nv++;
    }
    if (m.var && nv >= 2) {
      i64 c0 = eL >> 8, c1 = eU >> 8;
      if (c1 - c0 <= 4 && c1 < (i64)m.tbf.size()) {
        int fmin = 1 << 30;
        for (i64 c = c0; c <= c1; c++) fmin = std::min(fmin, m.tbf[c]);
        if (fmin > 0) {
          double mu = 524288.0 * fmin / m.VD;
          int ord[80];
          for (int u = 0; u < nv; u++) ord[u] = u;
          std::sort(ord, ord + nv, [&](int x, int y) { return vp[x] < vp[y]; });
          i64 cpp[80]; double cv[80], cs[80]; int nc = nv;
          for (int u = 0; u < nv; u++) { cpp[u] = vp[ord[u]]; cv[u] = vv[ord[u]]; cs[u] = vs[ord[u]]; }
          for (int u = 0; u < nc; u++)
            for (int v = u + 1; v < nc && v <= u + 2; v++) {
              double d = (double)(cpp[u] - cpp[v]) / SCd;
              for (int k = 1; k <= 3; k++) {
                double lam = 0.25 * k;
                f((1 - lam) * cv[u] + lam * cv[v] + mu * lam * (1 - lam) * d * d * 0.5,
                  (1 - lam) * cs[u] + lam * cs[v], (i64)-1);
              }
            }
        }
      }
    }
  }
  // term columns of box s, in LP order: f(n, i, j, an, val, slope, key)
  template <class F> void gencols(const i64* s, bool usepen, F&& f) const {
    for (int n = 0; n < m.nT; n++) {
      i64 eL, eU, L0;
      term_range(s, n, eL, eU, L0);
      int i = m.TI[n], j = m.TJ[n];
      double an = m.ta[n];
      termcols(n, eL, eU, L0, usepen, [&](double val, double slope, i64 key) { f(n, i, j, an, val, slope, key); });
    }
  }
  // max over term n's columns of a_n val + a_n slope Y (ub()): the columns of termcols, without its
  // duplicate filter (a repeated point repeats a value) when the mixed-column option is off
  double termmax(int n, i64 eL, i64 eU, i64 L0, bool usepen, double Y) const {
    const double an = m.ta[n];
    double w = an * ((double)lb(eL, std::max(eU, eL + 1)) / 1e10) + an * 0.0 * Y;
    if (m.var) {
      termcols(n, eL, eU, L0, usepen, [&](double val, double slope, i64) { w = std::max(w, an * val + an * slope * Y); });
      return w;
    }
    const double SCd = (double)m.SC;
    // three passes so that the memory accesses of all points overlap: points (prefetch the bitmap
    // words), record indices (prefetch the records), values
    i64 ps[70]; size_t ri[70]; int np = 0, nr = 0;
    i64 prev = -1;
    const i64 NX = (i64)m.pidx.size();
    for (int t = 0; t < 2 + 33 + 33; t++) {
      int jj = t < 2 ? 33 + t : (t < 35 ? t - 2 : 64 + (t - 35));
      if (t == 2 || t == 35) prev = -1;
      i64 p = gpt(eL, eU, jj);
      if (p < eL || p > eU || p == prev) continue;
      prev = p;
      if (p < 0 || p >= NX) continue;
      __builtin_prefetch(&m.hasp[p >> 6]);
      ps[np++] = p;
    }
    for (int u = 0; u < np; u++) {
      const i64 p = ps[u];
      const uint64_t hw = m.hasp[p >> 6];
      if (!((hw >> (p & 63)) & 1)) continue;
      size_t r = m.prank[p >> 6] + __builtin_popcountll(hw & ((1ULL << (p & 63)) - 1));
      __builtin_prefetch(&m.pab[r]);
      __builtin_prefetch(&m.prec[r]);
      ps[nr] = p; ri[nr++] = r;
    }
    for (int u = 0; u < nr; u++) {
      const i64 p = ps[u];
      const size_t r = ri[u];
      if (!(m.pab[r].second >= 1 && (i64)m.pab[r].first <= eL && eU <= (i64)m.pab[r].second)) continue;
      const Model::PRec& R = m.prec[r];
      if (!(1 <= R.B && R.A <= eL && eL <= p && p <= eU && eU <= R.B)) continue;
      double val = (double)R.V / 1e10 - (2e9 - (double)R.M) / 1e9 * (double)nsub(p, L0) / SCd;
      if (usepen && m.pen > 0 && !R.shared) val -= m.pen / std::max(an, 1e-12);
      w = std::max(w, an * val + an * (((double)R.P - 2e9) / 1e9) * Y);
    }
    return w;
  }
  // the term columns of one box (a scan's parent), for ub() on its children: terms whose ranges are
  // unchanged reuse them
  struct TermCache { std::vector<i64> eL, eU, L0; std::vector<int> off; std::vector<double> av, as; };
  void term_cache(const i64* s, bool usepen, TermCache& tc) const {
    tc.eL.resize(m.nT); tc.eU.resize(m.nT); tc.L0.resize(m.nT); tc.off.assign(m.nT + 1, 0);
    tc.av.clear(); tc.as.clear();
    for (int n = 0; n < m.nT; n++) {
      term_range(s, n, tc.eL[n], tc.eU[n], tc.L0[n]);
      tc.off[n] = (int)tc.av.size();
      double an = m.ta[n];
      termcols(n, tc.eL[n], tc.eU[n], tc.L0[n], usepen, [&](double val, double slope, i64) {
        tc.av.push_back(an * val); tc.as.push_back(an * slope);
      });
    }
    tc.off[m.nT] = (int)tc.av.size();
  }
  // Upper bound on margin(s, usepen) by weak LP duality from kappa-row duals y (>= 0, Q entries):
  // y_r is clipped to the slack column's bound (U_r - L_r) / SC, each term row's dual is the largest
  // reduced value of its columns, and the bounded multiplier columns add ymax * max(0, reduced cost).
  double ub(const i64* s, const std::vector<double>& y0, bool usepen = true, const TermCache* tc = nullptr) const {
    const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
    for (int r = 0; r < Q; r++) if (L[r] > U[r]) return 1.0;
    if (U[Q - 1] < L[0]) return 1.0;
    long long t0 = prof_on() ? tns() : 0;
    const double SCd = (double)m.SC;
    double y[MAXQ], cy[MAXQ + 1];
    cy[0] = 0;
    for (int r = 0; r < Q; r++) {
      y[r] = std::min(std::max(y0[r], 0.0), (double)(U[r] - L[r]) / SCd);
      cy[r + 1] = cy[r] + y[r];
    }
    double cst = -m.c;
    for (int r = 0; r < Q; r++) cst += m.tb[r] * (double)L[r] / SCd;
    double tot = 0;
    for (int r = 0; r < Q; r++) tot += m.tb[r] * y[r];
    for (int n = 0; n < m.nT; n++) {
      i64 eL, eU, L0;
      term_range(s, n, eL, eU, L0);
      const double Y = cy[m.TJ[n]] - cy[m.TI[n]];
      double w = -1e300;
      if (tc && tc->eL[n] == eL && tc->eU[n] == eU && tc->L0[n] == L0) {
        for (int c = tc->off[n]; c < tc->off[n + 1]; c++) w = std::max(w, tc->av[c] + tc->as[c] * Y);
      } else {
        if (t0) prof().ubmiss++;
        w = termmax(n, eL, eU, L0, usepen, Y);
      }
      tot += w;
    }
    double sp = 0;
    for (int k = 0; k < NP; k++) {
      i64 sLp = 0; for (int r = m.PI[k]; r < m.PJ[k]; r++) sLp += L[r];
      double ys = cy[m.PJ[k]] - cy[m.PI[k]];
      sp += std::max(0.0, (double)(A[k] - sLp) / SCd - ys);
      sp += std::max(0.0, (double)(sLp - B[k]) / SCd + ys);
    }
    if (m.half && Q >= 2) sp += std::max(0.0, (double)(L[0] - L[Q - 1]) / SCd + y[0] - y[Q - 1]);
    tot += m.ymax * sp;
    if (t0) { prof().ub++; prof().ns_ub += tns() - t0; }
    return cst + tot;
  }
  double margin(const i64* s, Highs& h, bool usepen = true, const WS* wi = nullptr, WS* wo = nullptr,
                std::vector<double>* yo = nullptr) const {
    const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
    if (yo) yo->clear();
    for (int r = 0; r < Q; r++) if (L[r] > U[r]) return 1.0;
    if (U[Q - 1] < L[0]) return 1.0;
    const bool pf = prof_on();
    long long t0 = pf ? tns() : 0;
    const double SCd = (double)m.SC;
    thread_local std::vector<double> cost, lo, up, aval;
    thread_local std::vector<int> astart, aidx, termcol;
    thread_local std::vector<i64> ckey;
    cost.clear(); lo.clear(); up.clear(); aval.clear(); astart.clear(); aidx.clear(); ckey.clear();
    termcol.assign(m.nT + 1, 0);
    const bool keys = wi || wo;
    double cst = -m.c;
    for (int r = 0; r < Q; r++) cst += m.tb[r] * (double)L[r] / SCd;
    int curn = -1;
    gencols(s, usepen, [&](int n, int i, int j, double an, double val, double slope, i64 key) {
      if (n != curn) { termcol[n] = (int)cost.size(); curn = n; }
      astart.push_back((int)aidx.size());
      cost.push_back(an * val); lo.push_back(0); up.push_back(kHighsInf);
      if (slope != 0.0) for (int r = i; r < j; r++) { aidx.push_back(r); aval.push_back(-an * slope); }
      aidx.push_back(Q + n); aval.push_back(1.0);
      if (keys) ckey.push_back(key);
    });
    termcol[m.nT] = (int)cost.size();
    i64 sLp[MAXNP];
    for (int k = 0; k < NP; k++) { sLp[k] = 0; for (int r = m.PI[k]; r < m.PJ[k]; r++) sLp[k] += L[r]; }
    for (int sd = 0; sd < 2; sd++)
      for (int k = 0; k < NP; k++) {
        astart.push_back((int)aidx.size());
        double obj = sd == 0 ? (double)(A[k] - sLp[k]) / SCd : (double)(sLp[k] - B[k]) / SCd;
        cost.push_back(obj); lo.push_back(0); up.push_back(m.ymax);
        for (int r = m.PI[k]; r < m.PJ[k]; r++) { aidx.push_back(r); aval.push_back(sd == 0 ? 1.0 : -1.0); }
      }
    if (m.half && Q >= 2) {
      astart.push_back((int)aidx.size());
      cost.push_back((double)(L[0] - L[Q - 1]) / SCd); lo.push_back(0); up.push_back(m.ymax);
      aidx.push_back(0); aval.push_back(-1.0);
      aidx.push_back(Q - 1); aval.push_back(1.0);
    }
    for (int r = 0; r < Q; r++) {
      astart.push_back((int)aidx.size());
      cost.push_back(-(double)(U[r] - L[r]) / SCd); lo.push_back(0); up.push_back(kHighsInf);
      aidx.push_back(r); aval.push_back(-1.0);
    }
    int ncol = (int)cost.size(), nrow = Q + m.nT;
    HighsLp lp;
    lp.num_col_ = ncol; lp.num_row_ = nrow;
    lp.col_cost_ = cost; lp.col_lower_ = lo; lp.col_upper_ = up;
    lp.row_lower_.resize(nrow); lp.row_upper_.resize(nrow);
    for (int r = 0; r < Q; r++) { lp.row_lower_[r] = -kHighsInf; lp.row_upper_[r] = m.tb[r]; }
    for (int n = 0; n < m.nT; n++) { lp.row_lower_[Q + n] = 1.0; lp.row_upper_[Q + n] = 1.0; }
    lp.sense_ = ObjSense::kMaximize;
    lp.a_matrix_.format_ = MatrixFormat::kColwise;
    astart.push_back((int)aidx.size());
    lp.a_matrix_.start_ = astart; lp.a_matrix_.index_ = aidx; lp.a_matrix_.value_ = aval;
    lp.a_matrix_.num_col_ = ncol; lp.a_matrix_.num_row_ = nrow;
    h.clearModel();
    h.passModel(std::move(lp));
    long long t1 = pf ? tns() : 0;
    if (wi && wi->ok) warm(h, *wi, ckey, termcol, ncol, nrow);
    long long t2 = pf ? tns() : 0;
    HighsStatus st = h.run();
    if (pf) {
      long long t3 = tns();
      Prof& P = prof();
      P.lp++; P.it += h.getInfo().simplex_iteration_count;
      P.ns_build += t1 - t0; P.ns_warm += t2 - t1; P.ns_run += t3 - t2;
    }
    if (wo) wo->ok = false;
    if (st != HighsStatus::kOk || h.getModelStatus() != HighsModelStatus::kOptimal) return -1.0;
    if (yo) { const std::vector<double>& rd = h.getSolution().row_dual; yo->assign(rd.begin(), rd.begin() + Q); }
    if (wo) {
      wo->key = ckey; wo->tcol = termcol; wo->b = h.getBasis();
      wo->ok = wo->b.valid;
      wo->skey.resize(ckey.size());
      for (int n = 0; n < m.nT; n++) {
        for (int c = termcol[n]; c < termcol[n + 1]; c++) wo->skey[c] = {ckey[c], c};
        std::sort(wo->skey.begin() + termcol[n], wo->skey.begin() + termcol[n + 1]);
      }
      const std::vector<double>& rd = h.getSolution().row_dual;
      wo->y.assign(rd.begin(), rd.begin() + Q);
    }
    return cst + h.getInfo().objective_function_value;
  }
};

static void cfg(Highs& h) {
  h.setOptionValue("output_flag", false);
  h.setOptionValue("threads", 1);
  h.setOptionValue("presolve", "off");
  h.setOptionValue("solver", "simplex");
  h.setOptionValue("simplex_strategy", 4);   // primal simplex: fastest on these small LPs
  if (const char* v = getenv("ENG_STRAT")) h.setOptionValue("simplex_strategy", atoi(v));
  if (const char* v = getenv("ENG_SCALE")) h.setOptionValue("simplex_scale_strategy", atoi(v));
}

extern "C" {

void* eng_load(const char* path) {
  FILE* f = fopen(path, "rb");
  if (!f) return nullptr;
  Eng* e = new Eng();
  Model& m = e->m;
  auto rd64 = [&](i64& v) { fread(&v, 8, 1, f); };
  auto rdd = [&](double& v) { fread(&v, 8, 1, f); };
  auto rdvec64 = [&](std::vector<i64>& v) { i64 n; rd64(n); v.resize(n); if (n) fread(v.data(), 8, n, f); };
  auto rdvecu64 = [&](std::vector<uint64_t>& v) { i64 n; rd64(n); v.resize(n); if (n) fread(v.data(), 8, n, f); };
  i64 t;
  rd64(t); m.Q = (int)t; rd64(t); m.NP = (int)t;
  if (m.Q < 1 || m.Q > MAXQ || m.NP > MAXNP) { fclose(f); delete e; return nullptr; }
  m.NS = 2 * m.Q + 2 * m.NP;
  e->Q = m.Q; e->NP = m.NP;
  const int Q = m.Q, NP = m.NP;
  rd64(m.SC); rd64(m.BB); rd64(m.TBIAS); rd64(m.KB); rd64(t); m.FS = (int)t;
  rdvecu64(m.MAGIC); rdvecu64(m.BL8);
  for (int k = 0; k < NP; k++) { rd64(t); m.PI[k] = (int)t; rd64(t); m.PJ[k] = (int)t; }
  m.SL.resize((Q + 1) * (Q + 1));
  for (int k = 0; k < (Q + 1) * (Q + 1); k++) { rd64(t); m.SL[k] = (int)t; }
  rd64(t); m.nT = (int)t;
  m.TI.resize(m.nT); m.TJ.resize(m.nT); m.TK.resize(m.nT); m.ta.resize(m.nT);
  for (int n = 0; n < m.nT; n++) { rd64(t); m.TI[n] = (int)t; rd64(t); m.TJ[n] = (int)t; rd64(t); m.TK[n] = (int)t; rdd(m.ta[n]); }
  for (int r = 0; r < Q; r++) rdd(m.tb[r]);
  rdd(m.c); rdd(m.yq); rdd(m.ymax);
  rdvec64(m.BND);
  std::vector<i64> ent; rdvec64(ent);
  m.ent.resize(ent.size());
  for (size_t i = 0; i < ent.size(); i++) m.ent[i] = (uint32_t)ent[i];
  // a pyramid of PLV levels has 2^PLV - 1 entries (PLV = 20: the Lean checker's domain x < 2^19)
  m.PLV = 0;
  while (((i64)1 << m.PLV) - 1 < (i64)ent.size()) m.PLV++;
  if (((i64)1 << m.PLV) - 1 != (i64)ent.size() || m.PLV < 11 || m.PLV > 23) { fclose(f); delete e; return nullptr; }
  i64 off = 0;
  for (int l = 0; l < m.PLV; l++) { m.eoff[l] = off; off += (i64)1 << (m.PLV - 1 - l); }
  std::vector<i64> px, pw; rdvec64(px);
  i64 np = (i64)px.size();
  m.pV.resize(np); m.pP.resize(np); m.pM.resize(np); m.pA.resize(np); m.pB.resize(np);
  for (i64 i = 0; i < np; i++) { rd64(m.pV[i]); rd64(m.pP[i]); rd64(m.pM[i]); rd64(m.pA[i]); rd64(m.pB[i]); }
  m.pidx.assign(m.KB + 2, -1);
  for (i64 i = 0; i < np; i++) if (px[i] >= 0 && px[i] < (i64)m.pidx.size()) m.pidx[px[i]] = (int)i;
  m.shared.assign(np, 1);
  m.hasp.assign((m.pidx.size() >> 6) + 1, 0);
  for (size_t x = 0; x < m.pidx.size(); x++) if (m.pidx[x] >= 0) m.hasp[x >> 6] |= 1ULL << (x & 63);
  m.pack_points();
  fclose(f);
  return e;
}

double eng_margin(void* h, const i64* st) {
  Eng* e = (Eng*)h;
  thread_local std::unique_ptr<Highs> hs;
  if (!hs) { hs.reset(new Highs()); cfg(*hs); }
  return e->margin(st, *hs);
}

double eng_margin_raw(void* h, const i64* st) {
  Eng* e = (Eng*)h;
  thread_local std::unique_ptr<Highs> hs;
  if (!hs) { hs.reset(new Highs()); cfg(*hs); }
  return e->margin(st, *hs, false);
}

void eng_children(void* h, const i64* st, int ax, int md, i64* left, i64* right, i64* q) {
  ((Eng*)h)->children(st, ax, md, left, right, q);
}

void eng_set_pen(void* h, const i64* xs, int n, double pen) {
  Eng* e = (Eng*)h;
  Model& m = e->m;
  std::fill(m.shared.begin(), m.shared.end(), 0);
  for (int i = 0; i < n; i++) if (xs[i] >= 0 && xs[i] < (i64)m.pidx.size() && m.pidx[xs[i]] >= 0) m.shared[m.pidx[xs[i]]] = 1;
  m.pen = pen;
  m.pack_points();
}

void eng_set_opts(void* h, int half, int var, const i64* tbf, int ntb, double VD) {
  Model& m = ((Eng*)h)->m;
  m.half = half; m.var = var; m.VD = VD;
  m.tbf.assign(tbf, tbf + ntb);
}

void eng_splits(void* h, const i64* st, int n, const int* ax, const int* md, double* ml, double* mr, int nthreads) {
  Eng* e = (Eng*)h;
  if (nthreads < 1) nthreads = 1;
  std::vector<std::thread> th;
  for (int t = 0; t < nthreads; t++)
    th.emplace_back([=]() {
      Highs hs; cfg(hs);
      i64 left[MAXNS], right[MAXNS], q;
      const int Q = e->Q, NP = e->NP;
      for (int k = t; k < n; k += nthreads) {
        i64 lo, hi;
        int a = ax[k];
        if (a < Q) { lo = st[a]; hi = st[Q + a]; } else { lo = st[2 * Q + a - Q]; hi = st[2 * Q + NP + a - Q]; }
        if (hi - lo < 2) { ml[k] = mr[k] = -1e9; continue; }
        e->children(st, a, md[k], left, right, &q);
        if (!(lo < q && q < hi)) { ml[k] = mr[k] = -1e9; continue; }
        ml[k] = e->margin(left, hs);
        mr[k] = e->margin(right, hs);
      }
    });
  for (auto& x : th) x.join();
}

}  // extern "C"

// q12 additions: the float tree builder in C++ (see builder.inc)
#include "builder.inc"
// q12 additions: exact replay in C++ with GMP (see replay.inc)
// (replay.inc not included in the q12x snapshot)
