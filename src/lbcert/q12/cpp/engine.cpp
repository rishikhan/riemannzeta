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
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cmath>
#include <vector>
#include <thread>
#include <algorithm>
#include <unordered_set>
#include <memory>
#include <atomic>
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
  i64 eoff[21];
  // points: per x index into arrays (or -1)
  std::vector<int> pidx;
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

// LP profile counters (eng_lpstats): calls, build+pass seconds, solve seconds, simplex iterations, columns
#include <chrono>
static std::atomic<long long> g_lp_n{0}, g_lp_it{0}, g_lp_col{0};
static std::atomic<long long> g_lp_tpass{0}, g_lp_tsolve{0};   // nanoseconds
static void lpstat_add(double tp, double ts, long long it, long long nc) {
  g_lp_n++; g_lp_it += it; g_lp_col += nc;
  g_lp_tpass += (long long)(tp * 1e9); g_lp_tsolve += (long long)(ts * 1e9);
}

struct Eng {
  Model m;
  int Q, NP;
  // ---------------------------------------------------------------- pyramid lb
  int blen(i64 x) const {
    if (x >= 256) return 8 + getbits(m.BL8, 4 * (int)(x >> 8), 4);
    return getbits(m.BL8, 4 * (int)x, 4);
  }
  i64 entry(int l, i64 i) const {
    if (l >= 20) return 0;
    i64 n = (i64)1 << (19 - l);
    if (i < 0 || i >= n) return 0;   // beyond the pyramid
    return m.ent[m.eoff[l] + i];
  }
  i64 lb(i64 lo, i64 hi) const {
    if (hi <= lo || 524289 <= hi) return 0;
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
  double margin(const i64* s, Highs& h, bool usepen = true) const {
    const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
    for (int r = 0; r < Q; r++) if (L[r] > U[r]) return 1.0;
    if (U[Q - 1] < L[0]) return 1.0;
    const double SCd = (double)m.SC;
    // columns: mu per term candidate, ylo[28], yhi[28], z[8]
    std::vector<double> cost, lo, up;
    std::vector<int> astart, aidx; std::vector<double> aval;   // column-wise
    std::vector<int> termcol(m.nT + 1);
    // rows: 0..7 kappa rows (<= b_r), 8..8+nT-1 equality rows
    double cst = -m.c;
    for (int r = 0; r < Q; r++) cst += m.tb[r] * (double)L[r] / SCd;
    for (int n = 0; n < m.nT; n++) {
      termcol[n] = (int)cost.size();
      int i = m.TI[n], j = m.TJ[n], kk = m.TK[n];
      i64 sL = 0, sU = 0;
      for (int r = i; r < j; r++) { sL += L[r]; sU += U[r]; }
      i64 eL, eU;
      if (j - i == 1) { eL = L[i]; eU = U[i]; } else { eL = std::max(A[kk], sL); eU = std::min(B[kk], sU); }
      i64 L0 = sL;
      double an = m.ta[n];
      auto addcol = [&](double val, double slope) {
        astart.push_back((int)aidx.size());
        cost.push_back(an * val); lo.push_back(0); up.push_back(kHighsInf);
        if (slope != 0.0) for (int r = i; r < j; r++) { aidx.push_back(r); aval.push_back(-an * slope); }
        aidx.push_back(Q + n); aval.push_back(1.0);
      };
      i64 lbv = lb(eL, std::max(eU, eL + 1));
      addcol((double)lbv / 1e10, 0.0);
      // distinct anchors
      i64 seen[80]; int ns = 0;
      i64 vp[80]; double vv[80], vs[80]; int nv = 0;
      for (int t = 0; t < 2 + 33 + 33; t++) {
        int jj = t < 2 ? 33 + t : (t < 35 ? t - 2 : 64 + (t - 35));
        i64 p = gpt(eL, eU, jj);
        if (p < eL || p > eU) continue;
        bool dup = false;
        for (int u = 0; u < ns; u++) if (seen[u] == p) { dup = true; break; }
        if (dup) continue;
        seen[ns++] = p;
        if (p < 0 || p >= (i64)m.pidx.size()) continue;
        int pi = m.pidx[p];
        if (pi < 0) continue;
        if (!(1 <= m.pB[pi] && m.pA[pi] <= eL && eL <= p && p <= eU && eU <= m.pB[pi])) continue;
        double val = (double)m.pV[pi] / 1e10 - (2e9 - (double)m.pM[pi]) / 1e9 * (double)nsub(p, L0) / SCd;
        if (usepen && m.pen > 0 && !m.shared[pi]) val -= m.pen / std::max(an, 1e-12);
        addcol(val, ((double)m.pP[pi] - 2e9) / 1e9);
        vp[nv] = p; vv[nv] = val; vs[nv] = ((double)m.pP[pi] - 2e9) / 1e9; nv++;
      }
      if (m.var && nv >= 2) {
        i64 c0 = eL >> 8, c1 = eU >> 8;
        if (c1 - c0 <= 4 && c1 < (i64)m.tbf.size()) {
          int fmin = 1 << 30;
          for (i64 c = c0; c <= c1; c++) fmin = std::min(fmin, m.tbf[c]);
          if (fmin > 0) {
            double mu = 524288.0 * fmin / m.VD;
            // sort the valid anchors by position
            int ord[80];
            for (int u = 0; u < nv; u++) ord[u] = u;
            std::sort(ord, ord + nv, [&](int x, int y) { return vp[x] < vp[y]; });
            i64 cp[80]; double cv[80], cs[80]; int nc = nv;
            for (int u = 0; u < nv; u++) { cp[u] = vp[ord[u]]; cv[u] = vv[ord[u]]; cs[u] = vs[ord[u]]; }
            for (int u = 0; u < nc; u++)
              for (int v = u + 1; v < nc && v <= u + 2; v++) {
                double d = (double)(cp[u] - cp[v]) / SCd;
                for (int k = 1; k <= 3; k++) {
                  double lam = 0.25 * k;
                  addcol((1 - lam) * cv[u] + lam * cv[v] + mu * lam * (1 - lam) * d * d * 0.5,
                         (1 - lam) * cs[u] + lam * cs[v]);
                }
              }
          }
        }
      }
    }
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
    std::vector<double> rlo(nrow), rup(nrow);
    for (int r = 0; r < Q; r++) { rlo[r] = -kHighsInf; rup[r] = m.tb[r]; }
    for (int n = 0; n < m.nT; n++) { rlo[Q + n] = 1.0; rup[Q + n] = 1.0; }
    HighsLp lp;
    lp.num_col_ = ncol; lp.num_row_ = nrow;
    lp.col_cost_ = cost; lp.col_lower_ = lo; lp.col_upper_ = up;
    lp.row_lower_ = rlo; lp.row_upper_ = rup;
    lp.sense_ = ObjSense::kMaximize;
    lp.a_matrix_.format_ = MatrixFormat::kColwise;
    astart.push_back((int)aidx.size());
    lp.a_matrix_.start_ = astart; lp.a_matrix_.index_ = aidx; lp.a_matrix_.value_ = aval;
    lp.a_matrix_.num_col_ = ncol; lp.a_matrix_.num_row_ = nrow;
    auto tA_ = std::chrono::steady_clock::now();
    h.clearModel();
    h.passModel(lp);
    auto tB_ = std::chrono::steady_clock::now();
    HighsStatus st = h.run();
    auto tC_ = std::chrono::steady_clock::now();
    lpstat_add(std::chrono::duration<double>(tB_ - tA_).count(), std::chrono::duration<double>(tC_ - tB_).count(),
               h.getInfo().simplex_iteration_count, ncol);
    if (st != HighsStatus::kOk || h.getModelStatus() != HighsModelStatus::kOptimal) return -1.0;
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
  i64 off = 0;
  for (int l = 0; l < 20; l++) { m.eoff[l] = off; off += (i64)1 << (19 - l); }
  std::vector<i64> px, pw; rdvec64(px);
  i64 np = (i64)px.size();
  m.pV.resize(np); m.pP.resize(np); m.pM.resize(np); m.pA.resize(np); m.pB.resize(np);
  for (i64 i = 0; i < np; i++) { rd64(m.pV[i]); rd64(m.pP[i]); rd64(m.pM[i]); rd64(m.pA[i]); rd64(m.pB[i]); }
  m.pidx.assign(m.KB + 2, -1);
  for (i64 i = 0; i < np; i++) if (px[i] >= 0 && px[i] < (i64)m.pidx.size()) m.pidx[px[i]] = (int)i;
  m.shared.assign(np, 1);
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

extern "C" void eng_lpstats(double* out) {
  out[0] = (double)g_lp_n; out[1] = g_lp_tpass * 1e-9; out[2] = g_lp_tsolve * 1e-9; out[3] = (double)g_lp_it; out[4] = (double)g_lp_col;
}

// q12 additions: the float tree builder in C++ (see builder.inc)
#include "builder.inc"
// q12 additions: exact replay in C++ with GMP (see replay.inc)
#include "replay.inc"
