// xgen: exact certified tree generator for the Q-gap leaf checker in the sparse Z format.
//
// Built on the q12 float engine (engine.cpp + builder.inc, snapshot in this directory): the split
// decisions are the float builder's (fb::decide: full axis x mode scan, lookahead k, stall rule), a
// node whose float leaf margin is >= 0 is certified exactly here, and a node whose certificate fails
// is split on its widest gap at the midpoint (q9hs TreeBuilder2's rule).  No Python per node.
//
// Leaf certificate (FORMAT.md in the parent directory): Z terms (presence mask, kind z, anchor codes,
// 10-bit lambda) and the multiplier list with the half-space row c = NP.  The leaf LP is the engine's
// margin LP with column bookkeeping; quantisation tries, in order: rounded / floored / ceiled
// multipliers; multipliers re-solved with the quantised terms frozen; the same with the kappa rows
// tightened by tau = 4 multiplier quanta; iterative rounding (one mixed term, then one multiplier at a
// time, LP re-solved after each).  First with the anchor penalty of the float builder, then without.
// Every emitted leaf passes zcheck(), an exact integer mirror of q9sparse/zfmt.ZChecker.zleaf
// (GMP for every sum that carries a term weight).
//
// Modes (one process, single-threaded by default; all state is per process):
//   xgen tree     ENG EXACT BOX OUT [opts]   whole subtree of the box in BOX (one line, NS ints)
//   xgen frontier ENG EXACT BOX OUT JOBS --depth D [opts]
//                 the top D levels; nodes at depth D become jobs (JOBS: "id NS-ints" per line),
//                 OUT holds the top nodes with "J id" placeholders
//   xgen check    ENG EXACT BOX IN [--table T] [--usage U]
//                 walks a node file from BOX, re-checks every leaf exactly (against table T if given:
//                 lines "x V P M A B"), optional per-point usage (x count minEL maxEU)
//   xgen select   ENG EXACT BOX IN OUT --allowed A
//                 re-certifies every leaf with anchors restricted to the points in A (no penalty);
//                 a leaf that fails keeps its certificate
// Options: --k 3 --stall 0.2 --pen 3e-8 --shared FILE (anchor x per line; default x % 256 == 0)
//          --threads 1 --budget 0 --maxdepth 160 --wmax 1024 (leaf bits incl. the leading 0 bit)
// Work stealing (tree mode; all off by default):
//   --steal-dir D   donation on: a pending box (a right child not yet started on the current path) can be
//                   handed to other workers as a job file D/<id>.job; the output gets "J <rel id>" in its
//                   place.  Requests: SIGUSR1 (one box per signal), or the flag file --hungry F (renamed away
//                   by the process that serves it; checked at most every 0.5 s).  Either one donates the
//                   shallowest pending box.  A request with no pending box is dropped.
//   --job-id P      this job's id (donated ids are P.<rel id>; empty for a top-level run)
//   --jobs-out F    list of the donated jobs ("rel-id box..." lines; default OUT with .nodes -> .jobs)
//   --deadline T    hand off at epoch T (as on SIGTERM): the node in progress is finished, every box
//                   entered afterwards is donated, the output is renamed into place and xgen exits 0
//                   (exit 5 without output when the hand-off comes before the first box was built)
//   --budget N      with --steal-dir: hand off at N leaves instead of aborting
//   --steal-force   donate every pending box at every node (test mode)
// A donated box carries its depth and the margin its parent's scan gave it (box trailer
// "M have_m m depth", m as a C99 hex float), so its subtree is the one this process would have built.
//
// Node file (text, preorder): "S ax md" | "R" | "J id" |
//   "L nt  n z jp p jr r lam ...  nm  c sd q ..." (jp/jr anchor codes, p/r points, -1 when unused)
#include "engine.cpp"
#include <gmpxx.h>
#include <fstream>
#include <sstream>
#include <string>
#include <chrono>
#include <map>
#include <csignal>
#include <ctime>
#include <unistd.h>

namespace xg {

static double now() {
  return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count();
}

static const int CODES[68] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23,
                              24, 25, 26, 27, 28, 29, 30, 31, 32, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75,
                              76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96,
                              33, 34};

struct Exact {
  mpz_class SIG, cN, KV;
  std::vector<mpz_class> BS, tA, tA2e9, BSK;   // tA2e9 = tA * 2e9; BSK = 1024e9 * BS + KV
  int QB = 14, YFUEL = 42, PB = 7, NT = 0;
  int wmax = 1024;
};

struct ZT { int n, z; i64 p, r; int jp, jr, lam; };
struct ML { int c, sd, q; };
struct Leaf { std::vector<ZT> t; std::vector<ML> y; };

struct G {
  Eng* e;
  Exact X;
  int Q, NP, NS, nT;
  // point table used by the exact check (defaults to the engine's maximal-interval words)
  std::vector<int> pidx;
  std::vector<i64> pV, pP, pM, pA, pB;
  std::vector<char> allowed;    // per point index; empty = all
};

static inline bool ptget(const G& g, i64 x, i64& V, i64& P, i64& M, i64& A, i64& B) {
  if (x < 0 || x >= (i64)g.pidx.size()) return false;
  int i = g.pidx[x];
  if (i < 0) return false;
  V = g.pV[i]; P = g.pP[i]; M = g.pM[i]; A = g.pA[i]; B = g.pB[i];
  return true;
}

static inline void ranges(const G& g, const i64* s, int n, i64& eL, i64& eU, i64& e0) {
  const Model& m = g.e->m;
  const int Q = g.Q, NP = g.NP;
  const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
  int i = m.TI[n], j = m.TJ[n], kk = m.TK[n];
  i64 sL = 0, sU = 0;
  for (int r = i; r < j; r++) { sL += L[r]; sU += U[r]; }
  if (j - i == 1) { eL = L[i]; eU = U[i]; } else { eL = std::max(A[kk], sL); eU = std::min(B[kk], sU); }
  e0 = sL;
}

static int code_of(const G& g, i64 eL, i64 eU, i64 p) {
  for (int c : CODES) if (g.e->gpt(eL, eU, c) == p) return c;
  return -1;
}

static int leaf_bits(const G& g, const Leaf& lf) {
  int b = 1 + g.nT;
  for (const ZT& t : lf.t) b += 3 + (t.z == 0 ? 0 : t.z == 3 ? 14 : 7) + ((t.z == 2 || t.z == 3 || t.z >= 4) ? 10 : 0);
  b += (int)lf.y.size() * (2 + g.X.PB + g.X.QB) + 1;
  return b;
}

static mpz_class mz(__int128 v) {
  // v >= 0 here
  unsigned __int128 u = (unsigned __int128)v;
  mpz_class x((unsigned long)(u >> 64));
  x <<= 64;
  x += mpz_class((unsigned long)(uint64_t)u);
  return x;
}

static void msub_floor0(mpz_class& v, const mpz_class& a) {   // v = nsub(v, a)
  if (v > a) v -= a; else v = 0;
}

// Exact mirror of zfmt.ZChecker.zleaf (+ hs.ydec_half): true when the leaf passes. margin = rhs - lhs.
// Also enforces the leaf-word window (bits <= wmax), the multiplier fuel, field widths and the
// q9leaf2 lever-P bounds (mw < 2049, sl <= 2^43).
static bool zcheck(const G& g, const i64* s, const Leaf& lf, mpz_class* margin = nullptr, const char** why = nullptr) {
  const Model& m = g.e->m;
  const Exact& X = g.X;
  const int Q = g.Q, NP = g.NP;
  const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
  auto fail = [&](const char* w) { if (why) *why = w; return false; };
  if (leaf_bits(g, lf) > X.wmax) return fail("width");
  if ((int)lf.y.size() > X.YFUEL - 1) return fail("fuel");
  if (U[Q - 1] < L[0]) return fail("refl box");
  mpz_class CVP = 0, CN = 0, tmp;
  std::vector<mpz_class> V(Q, X.KV);
  int last = -1;
  const i64 T9 = 2000000000;
  for (const ZT& t : lf.t) {
    if (t.n <= last || t.n >= g.nT) return fail("order");
    last = t.n;
    if (t.z < 0 || t.z > 7 || t.lam < 0 || t.lam > 1023) return fail("field");
    i64 eL, eU, e0;
    ranges(g, s, t.n, eL, eU, e0);
    __int128 mv = 0, cp = 0, cn = 0, sl = 0; i64 mw = 0;
    // the points are decoded from the anchor codes (as the checker does); the stored p / r are not read
    i64 tp = -1, tr = -1;
    if (t.z != 0) {
      if (t.jp < 0 || t.jp > 127) return fail("code p");
      tp = g.e->gpt(eL, eU, t.jp);
      if (t.z == 3) { if (t.jr < 0 || t.jr > 127) return fail("code r"); tr = g.e->gpt(eL, eU, t.jr); }
    }
    i64 Vp, Pp, Mp, Ap, Bp, Vr, Pr, Mr, Ar, Br;
    auto ivin = [&](i64 x, i64 Ai, i64 Bi) { return 1 <= Bi && Ai <= eL && eL <= x && x <= eU && eU <= Bi; };
    if (t.z == 0) {
      mv = (__int128)1024 * g.e->lb(eL, std::max(eU, eL + 1));
    } else if (t.z == 1) {
      if (!ptget(g, tp, Vp, Pp, Mp, Ap, Bp)) { Vp = Pp = Mp = Ap = Bp = 0; }
      if (!ivin(tp, Ap, Bp)) return fail("iv");
      mv = (__int128)1024 * Vp;
      cp = (__int128)1024 * nsub(Mp, T9) * nsub(tp, e0);
      cn = (__int128)1024 * nsub(T9, Mp) * nsub(tp, e0);
      sl = (__int128)1024 * Pp; mw = 1024;
    } else if (t.z == 3) {
      if (!ptget(g, tp, Vp, Pp, Mp, Ap, Bp)) { Vp = Pp = Mp = Ap = Bp = 0; }
      if (!ptget(g, tr, Vr, Pr, Mr, Ar, Br)) { Vr = Pr = Mr = Ar = Br = 0; }
      if (!(ivin(tp, Ap, Bp) && ivin(tr, Ar, Br))) return fail("iv");
      i64 l1 = nsub(1024, t.lam), lam = t.lam;
      mv = (__int128)l1 * Vp + (__int128)lam * Vr;
      cp = (__int128)l1 * nsub(Mp, T9) * nsub(tp, e0) + (__int128)lam * nsub(Mr, T9) * nsub(tr, e0);
      cn = (__int128)l1 * nsub(T9, Mp) * nsub(tp, e0) + (__int128)lam * nsub(T9, Mr) * nsub(tr, e0);
      sl = (__int128)l1 * Pp + (__int128)lam * Pr; mw = l1 + lam;
    } else {   // z == 2 or z >= 4
      if (!ptget(g, tp, Vp, Pp, Mp, Ap, Bp)) { Vp = Pp = Mp = Ap = Bp = 0; }
      if (!ivin(tp, Ap, Bp)) return fail("iv");
      i64 lam = t.lam;
      mv = (__int128)lam * Vp;
      if (t.z == 2) mv += (__int128)nsub(1024, lam) * g.e->lb(eL, std::max(eU, eL + 1));
      cp = (__int128)lam * nsub(Mp, T9) * nsub(tp, e0);
      cn = (__int128)lam * nsub(T9, Mp) * nsub(tp, e0);
      sl = (__int128)lam * Pp; mw = lam;
    }
    if (!(mw < 2049 && sl <= ((__int128)1 << 43))) return fail("lever-P bound");
    const mpz_class& a = X.tA[t.n];
    tmp = mz((__int128)32768 * mv + (__int128)10 * cp);
    CVP += a * tmp;
    if (cn) { tmp = mz(cn); CN += a * tmp; }
    mpz_class add = X.tA2e9[t.n] * (long)mw, sub = a * mz(sl);
    for (int r = m.TI[t.n]; r < m.TJ[t.n]; r++) { V[r] += add; msub_floor0(V[r], sub); }
  }
  // multipliers (ydecH)
  std::vector<mpz_class> P(Q), S(Q);
  for (int r = 0; r < Q; r++) { P[r] = 0; S[r] = 0; }
  mpz_class Cp = 0, Cm = 0;
  for (const ML& y : lf.y) {
    if (y.c < 0 || y.c > NP || y.q < 0 || y.q >= (1 << X.QB) || y.sd < 0 || y.sd > 1) return fail("mult field");
    mpz_class Y = X.SIG * (long)y.q;
    if (y.c == NP) {
      P[Q - 1] += Y; S[0] += Y;
      Cp += Y * (long)nsub(L[Q - 1], L[0]);
      Cm += Y * (long)nsub(L[0], L[Q - 1]);
    } else {
      int i = m.PI[y.c], j = m.PJ[y.c];
      i64 sL = 0;
      for (int r = i; r < j; r++) sL += L[r];
      for (int r = i; r < j; r++) { if (y.sd) S[r] += Y; else P[r] += Y; }
      if (y.sd) { Cp += Y * (long)nsub(B[y.c], sL); Cm += Y * (long)nsub(sL, B[y.c]); }
      else { Cp += Y * (long)nsub(sL, A[y.c]); Cm += Y * (long)nsub(A[y.c], sL); }
    }
  }
  mpz_class ngs = 0, bl = 0, d;
  for (int r = 0; r < Q; r++) {
    mpz_class lh = V[r] + P[r], rh = X.BSK[r] + S[r];
    if (lh > rh) { d = lh - rh; ngs += d * (long)nsub(U[r], L[r]); }
    bl += X.BS[r] * (long)L[r];
  }
  static const mpz_class K1("335544320000000000"), K2("10240000000000");
  mpz_class lhs = K1 * X.cN + 10 * (CN + Cp + ngs);
  mpz_class rhs = K2 * bl + CVP + 10 * Cm;
  for (int r = 0; r < Q; r++) if (L[r] > U[r]) return fail("box");
  if (margin) *margin = rhs - lhs;
  if (!(lhs <= rhs)) return fail("ineq");
  return true;
}

// ------------------------------------------------------------------------------------------ leaf LP
struct Col { int term; int kind; i64 p; int jj; double w; };   // kind 0 const, 1 tangent

struct LeafLP {
  G* g;
  Highs h;
  std::vector<Col> cols;
  std::vector<int> tfirst, tcnt;
  std::vector<i64> lbv;
  int ylo0 = 0, yhi0 = 0, yh = -1, z0 = 0, ncol = 0;
  std::vector<double> lo0, up0;
  std::vector<double> x;
  double cst = 0, obj = 0;
  i64 nsolve = 0;
  bool cold = getenv("XGEN_COLD") != nullptr;
  double bitpen = 0.0;   // > 0: every anchor (shared or not) pays bitpen / a_n (XG_WIDTHFIX retries)

  LeafLP() { cfg(h); }

  // build the LP of box s; pen > 0: non-shared anchors pay pen / a_n (engine margin); tau: kappa rows
  // tightened by tau multiplier quanta on gaps wider than 64
  bool build(const i64* s, double pen, double tau) {
    Eng* e = g->e;
    const Model& m = e->m;
    const int Q = g->Q, NP = g->NP, nT = g->nT;
    const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
    const double SCd = (double)m.SC;
    cols.clear(); tfirst.assign(nT, 0); tcnt.assign(nT, 0); lbv.assign(nT, 0);
    std::vector<double> cost, lo, up, aval;
    std::vector<int> astart, aidx;
    cst = -m.c;
    for (int r = 0; r < Q; r++) cst += m.tb[r] * (double)L[r] / SCd;
    for (int n = 0; n < nT; n++) {
      tfirst[n] = (int)cost.size();
      int i = m.TI[n], j = m.TJ[n];
      i64 eL, eU, L0;
      ranges(*g, s, n, eL, eU, L0);
      double an = m.ta[n];
      auto addcol = [&](double val, double slope, int kind, i64 p, int jj) {
        astart.push_back((int)aidx.size());
        cost.push_back(an * val); lo.push_back(0); up.push_back(kHighsInf);
        if (slope != 0.0) for (int r = i; r < j; r++) { aidx.push_back(r); aval.push_back(-an * slope); }
        aidx.push_back(Q + n); aval.push_back(1.0);
        cols.push_back({n, kind, p, jj, 0.0});
      };
      i64 lb = e->lb(eL, std::max(eU, eL + 1));
      lbv[n] = lb;
      addcol((double)lb / 1e10, 0.0, 0, -1, -1);
      i64 seen[80]; int ns = 0;
      for (int t = 0; t < 2 + 33 + 33; t++) {
        int jj = t < 2 ? 33 + t : (t < 35 ? t - 2 : 64 + (t - 35));
        i64 p = e->gpt(eL, eU, jj);
        if (p < eL || p > eU) continue;
        bool dup = false;
        for (int u = 0; u < ns; u++) if (seen[u] == p) { dup = true; break; }
        if (dup) continue;
        seen[ns++] = p;
        if (p < 0 || p >= (i64)g->pidx.size()) continue;
        int pi = g->pidx[p];
        if (pi < 0) continue;
        if (!g->allowed.empty() && !g->allowed[pi]) continue;
        if (!(1 <= g->pB[pi] && g->pA[pi] <= eL && eL <= p && p <= eU && eU <= g->pB[pi])) continue;
        double val = (double)g->pV[pi] / 1e10 - (2e9 - (double)g->pM[pi]) / 1e9 * (double)nsub(p, L0) / SCd;
        int epi = (p < (i64)m.pidx.size()) ? m.pidx[p] : -1;
        if (pen > 0 && !(epi >= 0 && m.shared[epi])) val -= pen / std::max(an, 1e-12);
        if (bitpen > 0) val -= bitpen / std::max(an, 1e-12);
        addcol(val, ((double)g->pP[pi] - 2e9) / 1e9, 1, p, code_of(*g, eL, eU, p));
      }
      tcnt[n] = (int)cost.size() - tfirst[n];
    }
    i64 sLp[MAXNP];
    for (int k = 0; k < NP; k++) { sLp[k] = 0; for (int r = m.PI[k]; r < m.PJ[k]; r++) sLp[k] += L[r]; }
    ylo0 = (int)cost.size(); yhi0 = ylo0 + NP;
    for (int sd = 0; sd < 2; sd++)
      for (int k = 0; k < NP; k++) {
        astart.push_back((int)aidx.size());
        double ob = sd == 0 ? (double)(A[k] - sLp[k]) / SCd : (double)(sLp[k] - B[k]) / SCd;
        cost.push_back(ob); lo.push_back(0); up.push_back(m.ymax);
        for (int r = m.PI[k]; r < m.PJ[k]; r++) { aidx.push_back(r); aval.push_back(sd == 0 ? 1.0 : -1.0); }
        cols.push_back({-1, 2, -1, -1, 0.0});
      }
    yh = (int)cost.size();
    astart.push_back((int)aidx.size());
    cost.push_back((double)(L[0] - L[Q - 1]) / SCd); lo.push_back(0); up.push_back(m.ymax);
    aidx.push_back(0); aval.push_back(-1.0);
    aidx.push_back(Q - 1); aval.push_back(1.0);
    cols.push_back({-1, 3, -1, -1, 0.0});
    z0 = (int)cost.size();
    for (int r = 0; r < Q; r++) {
      astart.push_back((int)aidx.size());
      cost.push_back(-(double)(U[r] - L[r]) / SCd); lo.push_back(0); up.push_back(kHighsInf);
      aidx.push_back(r); aval.push_back(-1.0);
      cols.push_back({-1, 4, -1, -1, 0.0});
    }
    ncol = (int)cost.size();
    int nrow = Q + nT;
    std::vector<double> rlo(nrow), rup(nrow);
    for (int r = 0; r < Q; r++) {
      rlo[r] = -kHighsInf;
      rup[r] = m.tb[r] - ((tau > 0 && (U[r] - L[r]) > 64) ? tau * m.yq : 0.0);
    }
    for (int n = 0; n < nT; n++) { rlo[Q + n] = 1.0; rup[Q + n] = 1.0; }
    HighsLp lp;
    lp.num_col_ = ncol; lp.num_row_ = nrow;
    lp.col_cost_ = cost; lp.col_lower_ = lo; lp.col_upper_ = up;
    lp.row_lower_ = rlo; lp.row_upper_ = rup;
    lp.sense_ = ObjSense::kMaximize;
    lp.a_matrix_.format_ = MatrixFormat::kColwise;
    astart.push_back((int)aidx.size());
    lp.a_matrix_.start_ = astart; lp.a_matrix_.index_ = aidx; lp.a_matrix_.value_ = aval;
    lp.a_matrix_.num_col_ = ncol; lp.a_matrix_.num_row_ = nrow;
    lo0 = lo; up0 = up;
    h.clearModel();
    h.passModel(lp);
    return true;
  }
  bool solve() {
    nsolve++;
    if (cold) h.clearSolver();
    HighsStatus st = h.run();
    if (st != HighsStatus::kOk || h.getModelStatus() != HighsModelStatus::kOptimal) return false;
    x = h.getSolution().col_value;
    obj = h.getInfo().objective_function_value;
    return true;
  }
  void setb(int c, double lo, double up) { h.changeColBounds(c, lo, up); }
  void reset_bounds() {
    std::vector<int> idx(ncol);
    for (int c = 0; c < ncol; c++) idx[c] = c;
    h.changeColsBounds(ncol, idx.data(), lo0.data(), up0.data());
  }
  double yval(int key) const {   // key: 0..NP-1 ylo, NP..2NP-1 yhi, 2NP half
    return x[ylo0 + key];
  }
};

// term choice from LP weights: <= 2 (col, weight) entries (largest weights, renormalised)
struct Pick { int k1 = -1, k2 = -1; double w1 = 0, w2 = 0; };

static Pick pick(const LeafLP& lp, int n) {
  std::vector<std::pair<double, int>> nz;
  for (int c = 0; c < lp.tcnt[n]; c++) {
    double w = lp.x[lp.tfirst[n] + c];
    if (w > 1e-9) nz.push_back({w, c});
  }
  Pick p;
  if (nz.empty()) {
    int best = 0;
    for (int c = 1; c < lp.tcnt[n]; c++) if (lp.x[lp.tfirst[n] + c] > lp.x[lp.tfirst[n] + best]) best = c;
    p.k1 = best; p.w1 = 1.0;
    return p;
  }
  std::stable_sort(nz.begin(), nz.end(), [](const std::pair<double, int>& a, const std::pair<double, int>& b) { return a.first > b.first; });
  if (nz.size() == 1) { p.k1 = nz[0].second; p.w1 = 1.0; return p; }
  double tot = nz[0].first + nz[1].first;
  p.k1 = nz[0].second; p.w1 = nz[0].first / tot;
  p.k2 = nz[1].second; p.w2 = nz[1].first / tot;
  return p;
}

// quantised term n: Z term (or none) and the frozen weights (col -> weight) it stands for
struct QT { bool listed; ZT t; int c1, c2; double f1, f2; };

static QT quant(const LeafLP& lp, int n, const Pick& pk, int lamv = -1) {
  const Col* cs = &lp.cols[lp.tfirst[n]];
  QT q; q.listed = true; q.c1 = q.c2 = -1; q.f1 = q.f2 = 0;
  q.t = {n, 0, -1, -1, -1, -1, 0};
  bool lbz = lp.lbv[n] == 0;
  int k1 = pk.k1, k2 = pk.k2;
  if (k2 < 0) {
    if (cs[k1].kind == 0) {
      q.c1 = k1; q.f1 = 1.0;
      if (lbz) q.listed = false; else q.t.z = 0;
    } else {
      q.c1 = k1; q.f1 = 1.0;
      q.t.z = 1; q.t.p = cs[k1].p; q.t.jp = cs[k1].jj;
    }
    return q;
  }
  // order: constant first (const + tangent), else as picked; lambda = weight of the second
  double w2 = pk.w2;
  if (cs[k2].kind == 0) { std::swap(k1, k2); w2 = pk.w1; }
  int lam = lamv >= 0 ? lamv : (int)std::lround(1024.0 * w2);
  lam = std::min(1024, std::max(0, lam));
  if (cs[k1].kind == 0) {        // const k1 + tangent k2: (1024 - lam) lb + lam tan
    if (lam == 0) { QT r = quant(lp, n, Pick{k1, -1, 1.0, 0.0}); return r; }
    if (lam == 1024) { QT r = quant(lp, n, Pick{k2, -1, 1.0, 0.0}); return r; }
    q.c1 = k1; q.f1 = (1024 - lam) / 1024.0; q.c2 = k2; q.f2 = lam / 1024.0;
    q.t.z = lbz ? 4 : 2; q.t.p = cs[k2].p; q.t.jp = cs[k2].jj; q.t.lam = lam;
    return q;
  }
  // two tangents: (1024 - lam) tan(k1) + lam tan(k2)
  if (lam == 0) return quant(lp, n, Pick{k1, -1, 1.0, 0.0});
  if (lam == 1024) return quant(lp, n, Pick{k2, -1, 1.0, 0.0});
  q.c1 = k1; q.f1 = (1024 - lam) / 1024.0; q.c2 = k2; q.f2 = lam / 1024.0;
  q.t.z = 3; q.t.p = cs[k1].p; q.t.jp = cs[k1].jj; q.t.r = cs[k2].p; q.t.jr = cs[k2].jj; q.t.lam = lam;
  return q;
}

static std::vector<ML> mults(const G& g, const LeafLP& lp, int mode) {
  std::vector<ML> y;
  const double yq = g.e->m.yq;
  const int mx = (1 << g.X.QB) - 1;
  auto f = [&](double v) { return mode == 1 ? (int)std::floor(v) : mode == 2 ? (int)std::ceil(v) : (int)std::lround(v); };
  for (int c = 0; c < g.NP; c++)
    for (int sd = 0; sd < 2; sd++) {
      int qi = std::max(0, std::min(mx, f(lp.x[(sd ? lp.yhi0 : lp.ylo0) + c] / yq)));
      if (qi) y.push_back({c, sd, qi});
    }
  int qh = std::max(0, std::min(mx, f(lp.x[lp.yh] / yq)));
  if (qh) y.push_back({g.NP, 0, qh});
  return y;
}

// XG_WIDTHFIX=1: see Certifier::certify.  Default off (unchanged output).
static const bool g_widthfix = getenv("XG_WIDTHFIX") && atoi(getenv("XG_WIDTHFIX")) != 0;

struct CertStats { i64 calls = 0, ok = 0, lp = 0, stage[8] = {0}; double secs = 0; };

struct Certifier {
  G* g;
  LeafLP lp;
  CertStats st;
  double pen = 3e-8;
  const char* last_why = "";
  bool dbg = getenv("XGEN_DEBUG") != nullptr;
  std::map<std::string, i64> whys;

  std::vector<QT> quant_all(const std::vector<int>* fixlam = nullptr) {
    std::vector<QT> out(g->nT);
    for (int n = 0; n < g->nT; n++) out[n] = quant(lp, n, pick(lp, n), fixlam ? (*fixlam)[n] : -1);
    return out;
  }
  Leaf leaf_of(const std::vector<QT>& qt, std::vector<ML> y) {
    Leaf lf;
    for (const QT& q : qt) if (q.listed) lf.t.push_back(q.t);
    lf.y = std::move(y);
    return lf;
  }
  bool try_modes(const i64* s, const std::vector<QT>& qt, Leaf& out) {
    for (int mode = 0; mode < 3; mode++) {
      Leaf lf = leaf_of(qt, mults(*g, lp, mode));
      const char* why = nullptr;
      mpz_class mg;
      if (zcheck(*g, s, lf, &mg, &why)) { out = std::move(lf); return true; }
      last_why = why ? why : "?";
      if (dbg) fprintf(stderr, "  try mode %d fail %s margin %.3e bits %d lp %.3e\n", mode, last_why,
                       mg.get_d() / (335544320000000000.0 * 8.388608e30), leaf_bits(*g, lf), lp.cst + lp.obj);
    }
    return false;
  }
  void freeze_terms(const std::vector<QT>& qt) {
    for (int n = 0; n < g->nT; n++) {
      int f = lp.tfirst[n];
      for (int c = 0; c < lp.tcnt[n]; c++) {
        double w = (c == qt[n].c1 ? qt[n].f1 : 0.0) + (c == qt[n].c2 ? qt[n].f2 : 0.0);
        lp.setb(f + c, w, w);
      }
    }
  }
  // one attempt with the current LP settings (built and solved)
  bool attempt(const i64* s, Leaf& out) {
    std::vector<QT> qt = quant_all();
    if (try_modes(s, qt, out)) { st.stage[0]++; return true; }
    freeze_terms(qt);
    if (lp.solve() && try_modes(s, qt, out)) { st.stage[1]++; return true; }
    return false;
  }
  // fix mixed terms one at a time (most nonzero columns first) at the better of floor / ceil lambda
  bool round_terms() {
    const int nT = g->nT;
    std::vector<char> fixed(nT, 0);
    for (int it = 0; it < nT; it++) {
      int best = -1, bnz = 0;
      for (int n = 0; n < nT; n++) {
        if (fixed[n]) continue;
        int nz = 0;
        for (int c = 0; c < lp.tcnt[n]; c++) if (lp.x[lp.tfirst[n] + c] > 1e-9) nz++;
        if (nz > 1 && nz > bnz) { bnz = nz; best = n; }
      }
      if (best < 0) break;
      int n = best;
      Pick pk = pick(lp, n);
      const Col* cs = &lp.cols[lp.tfirst[n]];
      double w2 = cs[pk.k2].kind == 0 ? pk.w1 : pk.w2;   // the weight quant() turns into lambda
      int lo = (int)std::floor(1024 * w2), hi = (int)std::ceil(1024 * w2);
      double bestv = -1e300; int bestlam = -1; std::vector<double> bx;
      for (int lam : {lo, hi}) {
        if (lo == hi && bestlam >= 0) continue;
        lam = std::min(1024, std::max(0, lam));
        QT q = quant(lp, n, pk, lam);
        int f = lp.tfirst[n];
        for (int c = 0; c < lp.tcnt[n]; c++) {
          double w = (c == q.c1 ? q.f1 : 0.0) + (c == q.c2 ? q.f2 : 0.0);
          lp.setb(f + c, w, w);
        }
        std::vector<double> save = lp.x;
        if (lp.solve() && lp.obj > bestv) { bestv = lp.obj; bestlam = lam; bx = lp.x; }
        lp.x = save;
      }
      if (bestlam < 0) return false;
      QT q = quant(lp, n, pk, bestlam);
      int f = lp.tfirst[n];
      for (int c = 0; c < lp.tcnt[n]; c++) {
        double w = (c == q.c1 ? q.f1 : 0.0) + (c == q.c2 ? q.f2 : 0.0);
        lp.setb(f + c, w, w);
      }
      fixed[n] = 1;
      lp.x = bx;
    }
    return true;
  }
  // fix multipliers one at a time (largest first) at the better of floor / ceil; the rest at 0
  bool round_mults() {
    const int NP = g->NP;
    const double yq = g->e->m.yq;
    const int mx = (1 << g->X.QB) - 1;
    std::vector<char> yf(2 * NP + 1, 0);
    for (int it = 0; it < 2 * NP + 1; it++) {
      int best = -1; double bv = 1e-6;
      for (int k = 0; k < 2 * NP + 1; k++) if (!yf[k] && lp.yval(k) / yq > bv) { bv = lp.yval(k) / yq; best = k; }
      if (best < 0) break;
      double bo = -1e300; int bq = -1; std::vector<double> bx;
      for (int qi : {(int)std::floor(bv), (int)std::ceil(bv)}) {
        qi = std::max(0, std::min(mx, qi));
        lp.setb(lp.ylo0 + best, qi * yq, qi * yq);
        if (lp.solve() && lp.obj > bo) { bo = lp.obj; bq = qi; bx = lp.x; }
      }
      if (bq < 0) return false;
      lp.setb(lp.ylo0 + best, bq * yq, bq * yq);
      yf[best] = 1;
      lp.x = bx;
    }
    for (int k = 0; k < 2 * NP + 1; k++) if (!yf[k]) lp.setb(lp.ylo0 + k, 0.0, 0.0);
    return lp.solve();
  }
  // iterative rounding; yfirst: the coarse multipliers (quantum 2^-16) first, then the terms
  bool iterative(const i64* s, Leaf& out, bool yfirst) {
    lp.reset_bounds();
    if (!lp.solve()) return false;
    if (yfirst) {
      if (!round_mults() || !round_terms()) return false;
    } else {
      if (!round_terms()) return false;
      freeze_terms(quant_all());
      if (!lp.solve() || !round_mults()) return false;
    }
    std::vector<QT> qt = quant_all();
    if (try_modes(s, qt, out)) { st.stage[yfirst ? 4 : 3]++; return true; }
    return false;
  }
  bool certify(const i64* s, Leaf& out) {
    double t0 = now();
    st.calls++;
    i64 lp0 = lp.nsolve;
    bool ok = false;
    for (int pass = 0; pass < 2 && !ok; pass++) {
      double p = pass == 0 ? pen : 0.0;
      if (pass == 1 && pen <= 0) break;
      lp.build(s, p, 0.0);
      if (!lp.solve()) continue;
      double m0 = lp.cst + lp.obj;
      if (attempt(s, out)) { ok = true; break; }
      if (m0 > 0) {
        lp.build(s, p, 4.0);
        if (lp.solve() && attempt(s, out)) { st.stage[2]++; ok = true; break; }
      }
      lp.build(s, p, 0.0);
      if (iterative(s, out, true)) { ok = true; break; }
      if (iterative(s, out, false)) { ok = true; break; }
    }
    // XG_WIDTHFIX=1: when every attempt failed on the leaf window (too many listed anchors), retry with a
    // penalty on every anchor, so the LP moves terms to their lower bound (3 bits) or drops them (lb 0)
    // instead of a tangent (10+ bits).  The exact check still decides; only the leaf choice changes.
    if (!ok && g_widthfix && std::string(last_why) == "width") {
      for (double bp : {1e-6, 1e-5, 1e-4}) {
        lp.bitpen = bp;
        lp.build(s, pen, 0.0);
        bool solved = lp.solve();
        if (solved && (attempt(s, out) || iterative(s, out, true) || iterative(s, out, false))) {
          ok = true; st.stage[5]++;
        }
        lp.bitpen = 0.0;
        if (ok) break;
      }
    }
    st.lp += lp.nsolve - lp0;
    st.secs += now() - t0;
    if (ok) st.ok++; else whys[last_why]++;
    if (dbg) {
      fprintf(stderr, "certify %s", ok ? "ok" : last_why);
      if (!ok) { fprintf(stderr, " box"); for (int i = 0; i < g->NS; i++) fprintf(stderr, " %lld", (long long)s[i]); }
      fprintf(stderr, "\n");
    }
    return ok;
  }
};

// ------------------------------------------------------------------------------------------ output
static void put_leaf(std::ostream& o, const Leaf& lf) {
  o << "L " << lf.t.size();
  for (const ZT& t : lf.t) o << ' ' << t.n << ' ' << t.z << ' ' << t.jp << ' ' << t.p << ' ' << t.jr << ' ' << t.r << ' ' << t.lam;
  o << ' ' << lf.y.size();
  for (const ML& y : lf.y) o << ' ' << y.c << ' ' << y.sd << ' ' << y.q;
  o << '\n';
}

static bool parse_leaf(std::istringstream& is, Leaf& lf) {
  int nt; if (!(is >> nt)) return false;
  lf.t.resize(nt);
  for (ZT& t : lf.t) is >> t.n >> t.z >> t.jp >> t.p >> t.jr >> t.r >> t.lam;
  int nm; is >> nm;
  lf.y.resize(nm);
  for (ML& y : lf.y) is >> y.c >> y.sd >> y.q;
  return (bool)is;
}

struct Opts {
  int k = 3, threads = 1, maxdepth = 160, depth = 0;
  double stall = 0.2, pen = 3e-8;
  i64 budget = 0;
  double race_stall = -1;   // >= 0: race the stall values o.stall (A) and race_stall (B) per box (tree mode)
  i64 race_cap = 400;       // a box whose A subtree exceeds race_cap leaves is split by A, its children raced
};

// XG_FAILSCAN=1: a node whose float leaf margin is >= 0 but whose certificate fails is split by the
// scan's decision (fb::decide), not at the midpoint of its widest gap.  Default off (unchanged output).
static const bool g_failscan = getenv("XG_FAILSCAN") && atoi(getenv("XG_FAILSCAN")) != 0;
// XG_WIDE=R (R > 1): when the scan chooses a node's split (float margin < 0, or a failed certificate with
// XG_FAILSCAN=1) and some gap has hi >= R * lo, split instead the gap with the largest hi / lo, in the mode
// (0..7) whose worse child margin is largest.  The children's cut positions are linear in the gap, so a
// wide end gap (up to 2^22) is otherwise cut no lower than 1/8 of its range, the low part keeps the parent's
// margin, and the scan's min-over-children score prefers ever narrower splits of the other gaps.  Only
// existing (axis, mode) splits are emitted: node format and checkers are unchanged.  Default off.
// XG_WIDE_NARROW=T: apply XG_WIDE only when the scan's own axis has (hi - lo) / lo < T (the scan is
// splitting an axis that is already narrow).  Production: XG_WIDE=4 XG_WIDE_NARROW=0.01.
static const double g_wide = getenv("XG_WIDE") ? atof(getenv("XG_WIDE")) : 0.0;
static const double g_wnarrow = getenv("XG_WIDE_NARROW") ? atof(getenv("XG_WIDE_NARROW")) : 1e300;
struct TS { i64 leaves = 0, refl = 0, splits = 0, fails = 0, maxdepth = 0, jobs = 0, bits = 0, nlisted = 0, nmult = 0, donated = 0, nwide = 0; };

// ------------------------------------------------------------------------------------------ stealing
static std::atomic<int> g_hungry{0};          // SIGUSR1 count not yet served
static volatile std::sig_atomic_t g_term = 0;  // SIGTERM seen
static void on_usr1(int) { g_hungry.fetch_add(1); }
static void on_term(int) { g_term = 1; }

struct Steal {
  std::string dir, hungry, jobid;
  double deadline = 0;   // epoch seconds, 0 = none
  bool force = false;
  double last_flag = -1e9;
};

// relative id of the box at path p (bits '0' left / '1' right from the job's root): "p" + hex of "1" p
static std::string path_id(const std::string& p) {
  std::string b = "1" + p;
  while (b.size() % 4) b.insert(b.begin(), '0');
  std::string id = "p";
  for (size_t i = 0; i < b.size(); i += 4)
    id += "0123456789abcdef"[(b[i] - '0') * 8 + (b[i + 1] - '0') * 4 + (b[i + 2] - '0') * 2 + (b[i + 3] - '0')];
  return id;
}

struct Builder {
  G* g;
  fb::Ctx* c;
  Certifier* cert;
  Opts o;
  TS st;
  std::ostream* out;
  std::ostream* jobs = nullptr;
  double t_float = 0;
  // stealing (sl != nullptr): the right children pending on the current path, outermost first
  struct Pend { const i64* s; int depth; double m; bool have_m; std::string path, id; };
  Steal* sl = nullptr;
  std::vector<Pend*> pend;
  std::string path;
  bool handoff = false;
  std::vector<std::string> donated;    // jobs-file lines
  // racing (o.race_stall >= 0): see race()
  bool racing = false;      // at race-split levels: children go through race()
  bool in_attempt = false;  // building a race attempt in memory (no donation)
  Steal* sl_outer = nullptr;
  i64 r_races = 0, r_big = 0, r_bwins = 0, r_saved = 0, r_lost = 0;

  // write box s as job file D/<id>.job; returns the relative id
  std::string donate(const i64* s, int depth, double m, bool have_m, const std::string& p) {
    std::string id = path_id(p);
    std::ostringstream ln;
    for (int i = 0; i < g->NS; i++) ln << (i ? " " : "") << s[i];
    char buf[96];
    snprintf(buf, sizeof buf, " M %d %a %d", have_m ? 1 : 0, m, depth);
    ln << buf;
    std::string f = sl->dir + "/" + (sl->jobid.empty() ? id : sl->jobid + "." + id) + ".job";
    {
      std::ofstream q(f + ".tmp");
      q << ln.str() << '\n';
    }
    std::rename((f + ".tmp").c_str(), f.c_str());
    donated.push_back(id + " " + ln.str());
    st.donated++;
    return id;
  }
  // between boxes: deadline / SIGTERM -> handoff; requests -> donate the shallowest pending boxes
  void poll() {
    if (g_term || (sl->deadline > 0 && (double)std::time(nullptr) >= sl->deadline)) handoff = true;
    if (handoff) return;
    int want = g_hungry.exchange(0);
    if (sl->force) want = 1 << 30;
    Pend* first = nullptr;
    for (Pend* p : pend) if (p->id.empty()) { first = p; break; }
    if (!first) return;
    if (want == 0 && !sl->hungry.empty()) {
      double t = now();
      if (t - sl->last_flag >= 0.5) {
        sl->last_flag = t;
        std::string tk = sl->hungry + ".srv" + std::to_string((long)getpid());
        if (std::rename(sl->hungry.c_str(), tk.c_str()) == 0) { std::remove(tk.c_str()); want = 1; }
      }
    }
    for (Pend* p : pend) {
      if (want <= 0) break;
      if (p->id.empty()) { p->id = donate(p->s, p->depth, p->m, p->have_m, p->path); want--; }
    }
  }

  int sub(const i64* s, int depth, double m, bool have_m) {
    return racing ? race(s, depth, m, have_m) : node(s, depth, m, have_m);
  }
  void addst(const TS& a) {
    st.leaves += a.leaves; st.refl += a.refl; st.splits += a.splits; st.fails += a.fails; st.nwide += a.nwide;
    st.maxdepth = std::max(st.maxdepth, a.maxdepth); st.bits += a.bits; st.nlisted += a.nlisted; st.nmult += a.nmult;
  }
  // one policy's subtree of box s, built in memory without donation; rc 1 when it exceeds cap leaves
  int attempt(const i64* s, int depth, double m, bool have_m, double stall, i64 cap, std::string& buf, TS& ts) {
    std::ostringstream oss;
    std::ostream* o0 = out; Steal* s0 = sl; TS st0 = st; double stall0 = o.stall; i64 bud0 = o.budget; bool r0 = racing;
    out = &oss; sl = nullptr; st = TS(); o.stall = stall; o.budget = cap; racing = false; in_attempt = true;
    int rc = node(s, depth, m, have_m);
    ts = st; buf = oss.str();
    out = o0; sl = s0; st = st0; o.stall = stall0; o.budget = bud0; racing = r0; in_attempt = false;
    return rc;
  }
  // Racing (--race-stall B).  Policy A (--stall) builds the subtree of s in memory with at most race_cap
  // leaves.  If it fits, policy B (stall B) builds it with at most (A leaves - 1) leaves, and the smaller
  // tree is written (A on a tie).  If A does not fit, s is split the way A splits it (node() with racing
  // on) and each child is raced the same way.  Donation (stealing, deadline hand-off) therefore happens
  // only at these race-split levels, between whole raced subtrees.  The output depends only on
  // (s, m, have_m, depth), as node() does, so a donated box gets the subtree this process would have
  // written.  CPU: A + B per raced box, plus the discarded A attempt on each race-split box (mostly
  // scan-cache hits when XG_CACHE is large enough).
  int race(const i64* s, int depth, double m, bool have_m) {
    const int Q = g->Q;
    if (o.race_stall < 0 || s[Q + Q - 1] < s[0] || (jobs && depth >= o.depth)) return node(s, depth, m, have_m);
    if (sl) { poll(); if (handoff) return node(s, depth, m, have_m); }
    std::string ba, bb; TS ta, tb;
    int rc = attempt(s, depth, m, have_m, o.stall, o.race_cap, ba, ta);
    if (rc == 1) {
      r_big++;
      bool r0 = racing; racing = true;
      rc = node(s, depth, m, have_m);
      racing = r0;
      return rc;
    }
    if (rc) return rc;
    r_races++;
    i64 na = ta.leaves + ta.refl;
    if (na > 1) {
      int rb = attempt(s, depth, m, have_m, o.race_stall, na - 1, bb, tb);
      if (rb == 0 && tb.leaves + tb.refl < na) {   // the budget check runs before a node, so B can end at na
        r_bwins++; r_saved += na - (tb.leaves + tb.refl); r_lost += na;
        *out << bb; addst(tb); return 0;
      }
      r_lost += tb.leaves + tb.refl;
    }
    *out << ba; addst(ta);
    return 0;
  }
  int node(const i64* s, int depth, double m, bool have_m) {
    Eng* e = g->e;
    const int Q = g->Q, NS = g->NS;
    if (depth > st.maxdepth) st.maxdepth = depth;
    if (o.budget > 0 && st.leaves + st.refl > o.budget) { if (!sl) return 1; handoff = true; }
    if (in_attempt && sl_outer && (g_term || (sl_outer->deadline > 0 && (double)std::time(nullptr) >= sl_outer->deadline))) return 1;
    if (s[Q + Q - 1] < s[0]) { st.refl++; *out << "R\n"; return 0; }
    if (jobs && depth >= o.depth) {
      *out << "J " << st.jobs << '\n';
      *jobs << st.jobs;
      for (int i = 0; i < NS; i++) *jobs << ' ' << s[i];
      *jobs << '\n';
      st.jobs++;
      return 0;
    }
    if (sl) {
      poll();
      if (handoff) {
        if (path.empty()) return 5;      // nothing built yet: the whole box stays with the caller
        *out << "J " << donate(s, depth, m, have_m, path) << '\n';
        return 0;
      }
    }
    double t0 = now();
    if (!have_m) m = fb::box_margin(e, s, true);
    m = fb::leaf_margin(e, s, m);
    t_float += now() - t0;
    fb::Ent b;
    bool fallback = false;
    if (m >= 0.0) {
      Leaf lf;
      if (cert->certify(s, lf)) {
        st.leaves++;
        st.bits += leaf_bits(*g, lf); st.nlisted += lf.t.size(); st.nmult += lf.y.size();
        put_leaf(*out, lf);
        return 0;
      }
      st.fails++;
      int r = 0;
      for (int x = 1; x < Q; x++) if (s[Q + x] - s[x] > s[Q + r] - s[r]) r = x;
      if (s[Q + r] - s[r] < 2) { fprintf(stderr, "leaf fails on a box with no gap to halve\n"); return 3; }
      b = {0.0, r, 0, 0.0, 0.0};
      fallback = !g_failscan;
    }
    if (depth >= o.maxdepth) return 2;
    if (!fallback) {
      t0 = now();
      bool okd = fb::decide(c, s, m, o.k, o.stall, b);
      t_float += now() - t0;
      if (!okd) return 3;
      double rel = 0.0;   // the scan's axis: (hi - lo) / lo
      if (b.a < Q) rel = s[b.a] > 0 ? (double)(s[Q + b.a] - s[b.a]) / (double)s[b.a] : 1e300;
      else { int k = b.a - Q; rel = s[2 * Q + k] > 0 ? (double)(s[2 * Q + g->NP + k] - s[2 * Q + k]) / (double)s[2 * Q + k] : 1e300; }
      if (g_wide > 1.0 && rel < g_wnarrow) {
        int wr = -1; double best = 0.0;
        for (int x = 0; x < Q; x++)
          if (s[x] > 0 && (double)s[Q + x] >= g_wide * (double)s[x] && s[Q + x] - s[x] >= 2) {
            double ratio = (double)s[Q + x] / (double)s[x];
            if (ratio > best) { best = ratio; wr = x; }
          }
        if (wr >= 0) {
          std::vector<i64> l(NS), r(NS);
          i64 q;
          bool have = false;
          t0 = now();
          for (int md = 0; md < 8; md++) {
            e->children(s, wr, md, l.data(), r.data(), &q);
            double x = fb::box_margin(e, l.data(), true), y = fb::box_margin(e, r.data(), true);
            if (!have || std::min(x, y) > b.sc) { b = {std::min(x, y), wr, md, x, y}; have = true; }
          }
          t_float += now() - t0;
          st.nwide++;
        }
      }
    }
    std::vector<i64> l(NS), r(NS);
    i64 q;
    e->children(s, b.a, b.m, l.data(), r.data(), &q);
    st.splits++;
    *out << "S " << b.a << ' ' << b.m << '\n';
    if (!sl) {
      int rc = sub(l.data(), depth + 1, b.x, !fallback);
      if (rc) return rc;
      return sub(r.data(), depth + 1, b.y, !fallback);
    }
    Pend pr{r.data(), depth + 1, b.y, !fallback, path + '1', ""};
    pend.push_back(&pr);
    path.push_back('0');
    int rc = sub(l.data(), depth + 1, b.x, !fallback);
    path.pop_back();
    pend.pop_back();
    if (rc) return rc;
    if (!pr.id.empty()) { *out << "J " << pr.id << '\n'; return 0; }
    path.push_back('1');
    rc = sub(r.data(), depth + 1, b.y, !fallback);
    path.pop_back();
    return rc;
  }
};

// ------------------------------------------------------------------------------------------ setup
static std::vector<std::string> split_ws(const std::string& s) {
  std::istringstream is(s); std::vector<std::string> v; std::string t;
  while (is >> t) v.push_back(t);
  return v;
}

static bool load_exact(G& g, const char* path) {
  std::ifstream f(path);
  if (!f) return false;
  std::string line;
  Exact& X = g.X;
  while (std::getline(f, line)) {
    auto v = split_ws(line);
    if (v.empty()) continue;
    if (v[0] == "SIG") X.SIG = mpz_class(v[1]);
    else if (v[0] == "cN") X.cN = mpz_class(v[1]);
    else if (v[0] == "QB") X.QB = std::stoi(v[1]);
    else if (v[0] == "YFUEL") X.YFUEL = std::stoi(v[1]);
    else if (v[0] == "BS") { X.BS.clear(); for (size_t i = 1; i < v.size(); i++) X.BS.push_back(mpz_class(v[i])); }
    else if (v[0] == "TA") { X.tA.clear(); for (size_t i = 1; i < v.size(); i++) X.tA.push_back(mpz_class(v[i])); }
  }
  X.KV = 1; X.KV <<= 160;
  X.NT = (int)X.tA.size();
  int pb = 0; while ((1 << pb) <= g.NP) pb++;
  X.PB = pb;
  X.tA2e9.clear(); for (auto& a : X.tA) X.tA2e9.push_back(a * 2000000000L);
  X.BSK.clear(); for (auto& b : X.BS) X.BSK.push_back(b * mpz_class("1024000000000") + X.KV);
  return (int)X.BS.size() == g.Q && X.NT == g.nT;
}

static bool load_table(G& g, const char* path) {
  std::ifstream f(path);
  if (!f) return false;
  g.pidx.assign(g.e->m.KB + 2, -1);
  g.pV.clear(); g.pP.clear(); g.pM.clear(); g.pA.clear(); g.pB.clear();
  i64 x, V, P, M, A, B;
  while (f >> x >> V >> P >> M >> A >> B) {
    g.pidx[x] = (int)g.pV.size();
    g.pV.push_back(V); g.pP.push_back(P); g.pM.push_back(M); g.pA.push_back(A); g.pB.push_back(B);
  }
  return true;
}

// box file: NS ints, optionally followed by the trailer "M have_m m depth" of a donated box
static bool read_box(const char* path, int NS, std::vector<i64>& s, int* depth = nullptr, double* m = nullptr,
                     bool* have_m = nullptr) {
  std::ifstream f(path);
  s.assign(NS, 0);
  for (int i = 0; i < NS; i++) if (!(f >> s[i])) return false;
  std::string t, ms;
  int h, d;
  if (depth && (f >> t) && t == "M") {
    if (!(f >> h >> ms >> d)) return false;
    *have_m = h != 0; *m = std::strtod(ms.c_str(), nullptr); *depth = d;
  }
  return true;
}

// walk a node file from box s; cb(leaf line stream, box) for every leaf; returns false on a malformed
// file.  Records are consumed in preorder.
struct Walker {
  G* g;
  std::vector<std::string> lines;
  size_t pos = 0;
  std::function<bool(const std::string&, const i64*, int)> onleaf;
  std::function<void(const std::string&)> onother;
  i64 nleaf = 0, nrefl = 0, nsplit = 0, bad = 0;
  bool walk(const i64* s, int depth) {
    if (pos >= lines.size()) return false;
    const std::string& ln = lines[pos++];
    const int Q = g->Q, NS = g->NS;
    if (ln[0] == 'S') {
      int a, m; sscanf(ln.c_str() + 1, "%d %d", &a, &m);
      if (a < 0 || a >= Q + g->NP || m < 0 || m > 7) return false;
      if (onother) onother(ln);
      std::vector<i64> l(NS), r(NS); i64 q;
      g->e->children(s, a, m, l.data(), r.data(), &q);
      nsplit++;
      return walk(l.data(), depth + 1) && walk(r.data(), depth + 1);
    }
    if (ln[0] == 'R') {
      if (!(s[Q + Q - 1] < s[0])) return false;
      if (onother) onother(ln);
      nrefl++;
      return true;
    }
    if (ln[0] == 'L') {
      if (s[Q + Q - 1] < s[0]) return false;     // the checker reads a reflection leaf here
      nleaf++;
      if (!onleaf(ln, s, depth)) bad++;
      return true;
    }
    return false;
  }
};

}  // namespace xg

int main(int argc, char** argv) {
  using namespace xg;
  if (argc < 5) { fprintf(stderr, "usage: xgen MODE ENG EXACT BOX ...\n"); return 2; }
  // stealing: catch SIGUSR1 / SIGTERM before the engine load, so an early request cannot kill the process
  for (int i = 5; i < argc; i++)
    if (std::string(argv[i]) == "--steal-dir" && std::string(argv[1]) == "tree") {
      struct sigaction sa;
      memset(&sa, 0, sizeof sa);
      sa.sa_flags = SA_RESTART;
      sigemptyset(&sa.sa_mask);
      sa.sa_handler = on_usr1; sigaction(SIGUSR1, &sa, nullptr);
      sa.sa_handler = on_term; sigaction(SIGTERM, &sa, nullptr);
    }
  std::string mode = argv[1];
  Eng* e = (Eng*)eng_load(argv[2]);
  if (!e) { fprintf(stderr, "eng_load failed\n"); return 2; }
  G g; g.e = e; g.Q = e->Q; g.NP = e->NP; g.NS = 2 * g.Q + 2 * g.NP; g.nT = e->m.nT;
  g.pidx = e->m.pidx; g.pV = e->m.pV; g.pP = e->m.pP; g.pM = e->m.pM; g.pA = e->m.pA; g.pB = e->m.pB;
  if (!load_exact(g, argv[3])) { fprintf(stderr, "bad exact file\n"); return 2; }
  std::vector<i64> box;
  int depth0 = 0; double m0 = 0.0; bool have_m0 = false;
  if (!read_box(argv[4], g.NS, box, &depth0, &m0, &have_m0)) { fprintf(stderr, "bad box file\n"); return 2; }
  Opts o;
  std::string shared_path, table_path, usage_path, allowed_path, jobs_out;
  Steal steal;
  std::vector<std::string> pos;
  for (int i = 5; i < argc; i++) {
    std::string a = argv[i];
    auto nxt = [&]() { return std::string(argv[++i]); };
    if (a == "--k") o.k = std::stoi(nxt());
    else if (a == "--stall") o.stall = std::stod(nxt());
    else if (a == "--pen") o.pen = std::stod(nxt());
    else if (a == "--threads") o.threads = std::stoi(nxt());
    else if (a == "--budget") o.budget = std::stoll(nxt());
    else if (a == "--maxdepth") o.maxdepth = std::stoi(nxt());
    else if (a == "--depth") o.depth = std::stoi(nxt());
    else if (a == "--wmax") g.X.wmax = std::stoi(nxt());
    else if (a == "--shared") shared_path = nxt();
    else if (a == "--table") table_path = nxt();
    else if (a == "--usage") usage_path = nxt();
    else if (a == "--allowed") allowed_path = nxt();
    else if (a == "--steal-dir") steal.dir = nxt();
    else if (a == "--hungry") steal.hungry = nxt();
    else if (a == "--job-id") steal.jobid = nxt();
    else if (a == "--jobs-out") jobs_out = nxt();
    else if (a == "--deadline") steal.deadline = std::stod(nxt());
    else if (a == "--steal-force") steal.force = true;
    else if (a == "--race-stall") o.race_stall = std::stod(nxt());
    else if (a == "--race-cap") o.race_cap = std::stoll(nxt());
    else pos.push_back(a);
  }
  // shared anchors for the penalty (engine flags): default the grid points x % 256 == 0
  {
    std::vector<i64> xs;
    if (!shared_path.empty()) { std::ifstream f(shared_path); i64 x; while (f >> x) xs.push_back(x); }
    else for (i64 x = 0; x < (i64)e->m.pidx.size(); x += 256) if (e->m.pidx[x] >= 0) xs.push_back(x);
    eng_set_pen(e, xs.data(), (int)xs.size(), o.pen);
  }
  eng_set_opts(e, 1, 0, nullptr, 0, 1e9);          // half-space row on, variance off (fb12.setup)
  double t0 = now();
  if (mode == "tree" || mode == "frontier") {
    if (pos.empty()) { fprintf(stderr, "missing OUT\n"); return 2; }
    std::string outp = pos[0], tmp = outp + ".tmp";
    std::ofstream out(tmp);
    std::ofstream jobs;
    fb::Ctx* c = fb::ctx_of(e);
    c->nthreads = o.threads;
    Certifier cert; cert.g = &g; cert.lp.g = &g; cert.pen = o.pen;
    Builder b; b.g = &g; b.c = c; b.cert = &cert; b.o = o; b.out = &out;
    if (mode == "frontier") {
      if (pos.size() < 2) { fprintf(stderr, "missing JOBS\n"); return 2; }
      jobs.open(pos[1] + ".tmp");
      b.jobs = &jobs;
    } else if (!steal.dir.empty()) {
      b.sl = &steal;
      if (jobs_out.empty())
        jobs_out = (outp.size() > 6 && outp.compare(outp.size() - 6, 6, ".nodes") == 0 ? outp.substr(0, outp.size() - 6) : outp) + ".jobs";
    }
    b.sl_outer = b.sl;
    int rc = mode == "tree" ? b.race(box.data(), depth0, m0, have_m0) : b.node(box.data(), depth0, m0, have_m0);
    if (o.race_stall >= 0)
      fprintf(stdout, "# race stall %g cap %lld races %lld big %lld bwins %lld saved %lld discarded %lld\n", o.race_stall,
              (long long)o.race_cap, (long long)b.r_races, (long long)b.r_big, (long long)b.r_bwins, (long long)b.r_saved,
              (long long)b.r_lost);
    double secs = now() - t0;
    char buf[1024];
    snprintf(buf, sizeof buf,
             "# rc %d leaves %lld refl %lld splits %lld fails %lld maxdepth %lld jobs %lld secs %.3f float_secs %.3f "
             "cert_secs %.3f cert_lp %lld evals %lld bits %lld listed %lld mults %lld stages %lld %lld %lld %lld %lld\n",
             rc, (long long)b.st.leaves, (long long)b.st.refl, (long long)b.st.splits, (long long)b.st.fails,
             (long long)b.st.maxdepth, (long long)b.st.jobs, secs, b.t_float, cert.st.secs, (long long)cert.st.lp,
             (long long)c->evals, (long long)b.st.bits, (long long)b.st.nlisted, (long long)b.st.nmult,
             (long long)cert.st.stage[0], (long long)cert.st.stage[1], (long long)cert.st.stage[2],
             (long long)cert.st.stage[3], (long long)cert.st.stage[4]);
    if (g_wide > 1.0) {   // replace the newline: "... wide N" (N: splits chosen by the XG_WIDE rule)
      size_t n = strlen(buf);
      snprintf(buf + n - 1, sizeof buf - n + 1, " wide %lld\n", (long long)b.st.nwide);
    }
    if (b.sl) {   // replace the newline: "... donated N handoff 0|1"
      size_t n = strlen(buf);
      snprintf(buf + n - 1, sizeof buf - n + 1, " donated %lld handoff %d\n", (long long)b.st.donated, b.handoff ? 1 : 0);
    }
    out << buf;
    out.close();
    fputs(buf, stdout);
    for (auto& kv : cert.whys) fprintf(stdout, "# certify failures: %s %lld\n", kv.first.c_str(), (long long)kv.second);
    if (Eng::prof_on()) {
      Eng::Prof& P = Eng::prof();
      fprintf(stdout, "# prof lp %lld iters %lld it/lp %.2f build_s %.3f warm_s %.3f run_s %.3f ub %lld ubmiss %lld ub_s %.3f | "
              "scans %lld hits %lld look %lld lskip %lld ublp %lld dup %lld ubskip %lld ubviol %lld ref %lld refskip %lld lplook %lld lpwr %lld scanlook %lld\n",
              (long long)P.lp, (long long)P.it, P.lp ? (double)P.it / P.lp : 0.0, P.ns_build * 1e-9, P.ns_warm * 1e-9,
              P.ns_run * 1e-9, (long long)P.ub, (long long)P.ubmiss, P.ns_ub * 1e-9, (long long)c->n_scan, (long long)c->n_hit,
              (long long)c->n_look, (long long)c->n_lskip, (long long)c->n_lp0, (long long)c->n_dup,
              (long long)c->n_ubsk, (long long)c->n_ubviol, (long long)c->n_ref, (long long)c->n_refsk, (long long)c->n_lplook, (long long)c->n_lpwr, (long long)c->n_scanlook);
    }
    if (rc != 0) { fprintf(stderr, "build failed rc %d\n", rc); return rc == 5 ? 5 : 1; }
    if (mode == "frontier") { jobs.close(); std::rename((pos[1] + ".tmp").c_str(), pos[1].c_str()); }
    if (b.sl) {   // the job list goes into place before the node file (a node file implies its job list)
      if (b.donated.empty()) std::remove(jobs_out.c_str());
      else {
        {
          std::ofstream jf(jobs_out + ".tmp");
          for (auto& l : b.donated) jf << l << '\n';
        }
        std::rename((jobs_out + ".tmp").c_str(), jobs_out.c_str());
      }
    }
    std::rename(tmp.c_str(), outp.c_str());
    return 0;
  }
  if (mode == "check" || mode == "select") {
    if (pos.empty()) { fprintf(stderr, "missing IN\n"); return 2; }
    if (!table_path.empty() && !load_table(g, table_path.c_str())) { fprintf(stderr, "bad table\n"); return 2; }
    Walker w; w.g = &g;
    {
      std::ifstream f(pos[0]); std::string ln;
      while (std::getline(f, ln)) if (!ln.empty() && ln[0] != '#') w.lines.push_back(ln);
    }
    std::map<i64, std::array<i64, 3>> usage;
    mpz_class minm; bool have_min = false;
    i64 nbits = 0, maxbits = 0, nlisted = 0;
    std::vector<std::string> outl;
    i64 changed = 0, kept = 0;
    Certifier cert; cert.g = &g; cert.lp.g = &g; cert.pen = 0.0;
    if (mode == "select") {
      if (allowed_path.empty()) { fprintf(stderr, "select needs --allowed\n"); return 2; }
      g.allowed.assign(g.pV.size(), 0);
      std::ifstream f(allowed_path); i64 x;
      while (f >> x) if (x >= 0 && x < (i64)g.pidx.size() && g.pidx[x] >= 0) g.allowed[g.pidx[x]] = 1;
      w.onother = [&](const std::string& ln) { outl.push_back(ln); };
    }
    w.onleaf = [&](const std::string& ln, const i64* s, int) -> bool {
      std::istringstream is(ln.substr(1));
      Leaf lf;
      if (!parse_leaf(is, lf)) return false;
      if (mode == "select") {
        bool need = false;
        for (const ZT& t : lf.t) {
          if (t.z != 0 && (g.pidx[t.p] < 0 || !g.allowed[g.pidx[t.p]])) need = true;
          if (t.z == 3 && (g.pidx[t.r] < 0 || !g.allowed[g.pidx[t.r]])) need = true;
        }
        Leaf nl;
        if (need && cert.certify(s, nl)) { lf = nl; changed++; } else if (need) kept++;
        std::ostringstream os; put_leaf(os, lf);
        std::string t = os.str(); t.pop_back();
        outl.push_back(t);
        return true;
      }
      mpz_class mg;
      const char* why = nullptr;
      bool ok = zcheck(g, s, lf, &mg, &why);
      if (!ok) { fprintf(stderr, "leaf fails (%s): %s\n", why ? why : "?", ln.substr(0, 80).c_str()); return false; }
      if (!have_min || mg < minm) { minm = mg; have_min = true; }
      i64 lb = leaf_bits(g, lf);
      nbits += lb; maxbits = std::max(maxbits, lb); nlisted += lf.t.size();
      for (const ZT& t : lf.t) {
        if (t.z == 0) continue;
        i64 eL, eU, e0;
        ranges(g, s, t.n, eL, eU, e0);
        i64 dp = g.e->gpt(eL, eU, t.jp), dr = t.z == 3 ? g.e->gpt(eL, eU, t.jr) : (i64)-1;
        for (i64 p : {dp, dr}) {
          if (p < 0) continue;
          auto it = usage.find(p);
          if (it == usage.end()) usage[p] = {1, eL, eU};
          else { it->second[0]++; it->second[1] = std::min(it->second[1], eL); it->second[2] = std::max(it->second[2], eU); }
        }
      }
      return true;
    };
    bool ok = w.walk(box.data(), 0) && w.pos == w.lines.size();
    if (mode == "select") {
      std::string outp = pos.size() > 1 ? pos[1] : pos[0] + ".sel";
      std::ofstream out(outp + ".tmp");
      for (auto& l : outl) out << l << '\n';
      out << "# select changed " << changed << " kept " << kept << '\n';
      out.close();
      std::rename((outp + ".tmp").c_str(), outp.c_str());
      printf("# select ok %d leaves %lld changed %lld kept %lld secs %.2f\n", ok ? 1 : 0, (long long)w.nleaf,
             (long long)changed, (long long)kept, now() - t0);
      return ok ? 0 : 1;
    }
    if (!usage_path.empty()) {
      std::ofstream u(usage_path);
      for (auto& kv : usage) u << kv.first << ' ' << kv.second[0] << ' ' << kv.second[1] << ' ' << kv.second[2] << '\n';
    }
    double minf = have_min ? minm.get_d() / (335544320000000000.0 * 0.0 + 1.0) : 0.0;
    printf("# check ok %d structure %d leaves %lld refl %lld splits %lld bad %lld points %zu bits %lld maxbits %lld "
           "listed %.2f minmargin %s secs %.3f\n",
           (ok && w.bad == 0) ? 1 : 0, ok ? 1 : 0, (long long)w.nleaf, (long long)w.nrefl, (long long)w.nsplit,
           (long long)w.bad, usage.size(), (long long)nbits, (long long)maxbits,
           w.nleaf ? (double)nlisted / w.nleaf : 0.0, have_min ? minm.get_str().c_str() : "-", now() - t0);
    (void)minf;
    return (ok && w.bad == 0) ? 0 : 1;
  }
  fprintf(stderr, "unknown mode %s\n", mode.c_str());
  return 2;
}
