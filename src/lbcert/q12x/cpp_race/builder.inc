// Float tree builder in C++ (included at the end of engine.cpp, after the q9hs ABI).
//
// The q12 FloatBuilder (src/lbcert/q12/fb12.py, on q9hs treehs.TreeBuilder2) in C++, so no
// per-box work runs in Python:
//   * leaf: reflection box (U_{Q-1} < L_0), or float LP margin >= 0 (penalised margin, then the
//     unpenalised one when a penalty is set);
//   * split choice: every axis x mode scanned (both children's LP margins, threaded), entries
//     sorted by the worse child margin (stable, so ties keep the axis-major order); with lookahead
//     the top k entries are scored by min over the two children of (child margin if >= 0, else the
//     child's own best scan entry), first maximum wins; then the stall rule (best - m < stall * (-m)
//     -> the best scan entry on the widest gap, if that gap is at least 2 wide);
//   * scans are cached per box, so a lookahead child's scan is reused when the child is built.
//   * pruned scan (Ctx::keep = k > 0): only the top k entries, and the entries on the widest gap
//     (stall rule), are needed, so the scan solves every left child first and then the right
//     children in decreasing order of the left margin, stopping once a left margin (an upper bound
//     on min(left, right)) ranks below the k-th best complete entry.  The cached list holds the
//     complete entries only; its top k and its widest-gap entries are those of the full scan.
//     XG_PRUNE=0 restores the full scan.
//   * warm start (Ctx::ws): every child LP of a scan starts from the box's own optimal basis
//     (Eng::WS, mapped by column identity).  XG_WS=0 solves every LP cold.
//   * bound-ordered scan (cpp_fast, Ctx::ub, single thread; XG_UB=0 restores the scan above): each
//     child's margin is bounded by weak LP duality from the box's kappa-row duals (Eng::ub, no
//     simplex); entries are solved in decreasing bound order only while they can still enter the
//     top k (then the widest gap's best entry), identical child boxes are solved once, and bounds
//     are tightened with the duals of the last solved child on the same axis and side (XG_REFINE).
//     Same LP values, so the same top k and widest-gap entry as the full scan.
//   * lookahead scans (child_score) need only the child's best entry, and only when it beats the
//     current best lookahead score: they keep 1 entry above that threshold, skip the widest-gap
//     phase, and are cached with their LP values and bounds, so that building the chosen child
//     resumes the scan (XG_PARTIAL=0: full lookahead scans).  A lookahead child whose sibling
//     already scores below the current best is not scanned (XG_LSKIP=0: scanned).  The skipped
//     work belongs to entries that cannot be chosen, so the trees are unchanged.
// The choices are the Python builder's, so trees are identical (checked on q9 roots 71 and 23), with
// XG_WS=0; the warm start moves LP margins by up to about 2e-10 and so can flip near-tied choices.
//
//   int  eng_decide(void*, const i64* st, double m, int k, int nthreads, double stall,
//                   int* ax, int* md, double* x, double* y)          one split decision
//   int  eng_float_tree(void*, const i64* st, int k, int nthreads, double stall, i64 budget,
//                       int maxdepth, i64* stats)    whole subtree; stats = leaves, refl, splits,
//                                                    maxdepth, LP evaluations; returns 0 ok,
//                                                    1 leaf budget, 2 depth limit, 3 no split
//   double eng_leaf_margin(void*, const i64* st)    the builder's leaf margin of one box
//   void eng_cache_clear(void*)
#include <atomic>
#include <unordered_map>
#include <string>
#include <mutex>
#include <functional>

namespace fb {

struct Ent { double sc; int a, m; double x, y; };

struct Ctx {
  Eng* e;
  int nthreads;
  // scan cache: full lists (top keep + widest gap), or lookahead lists (exact best entry when it scores
  // above pthr) with the LP values and bounds so far, from which a later scan of the box resumes
  struct Scan { std::vector<Ent> out; bool full = true; double pthr = 0; std::vector<double> sv, su; };
  std::unordered_map<std::string, Scan> cache;
  i64 npart = 0;     // cached lookahead lists (they hold sv / su)
  bool partial = true;   // XG_PARTIAL: lookahead scans keep 1 above a threshold
  i64 evals = 0;
  bool prune = false;
  int keep = 0;      // > 0: pruned scan keeping the top keep entries (set by decide)
  bool ws = false;   // warm-start the child LPs from the box's basis
  bool ub = false;   // XG_UB: order and prune the scan by LP-duality upper bounds (exact top k)
  bool dedup = true; // XG_DEDUP: solve each distinct child box of a scan once
  bool lskip = true; // XG_LSKIP: skip lookahead scans that cannot change the choice
  // statistics (printed by xgen with XG_PROF=1)
  i64 n_scan = 0, n_hit = 0, n_look = 0, n_lskip = 0, n_lp0 = 0, n_lp1 = 0, n_dup = 0, n_ubviol = 0, n_ubsk = 0, n_ref = 0, n_refsk = 0, n_lplook = 0, n_lpwr = 0, n_scanlook = 0;
  bool look = false, inwr = false;
};

static std::unordered_map<void*, Ctx*> g_ctx;
static std::mutex g_mu;

static Ctx* ctx_of(void* h) {
  std::lock_guard<std::mutex> lk(g_mu);
  auto it = g_ctx.find(h);
  if (it != g_ctx.end()) return it->second;
  Ctx* c = new Ctx();
  c->e = (Eng*)h;
  c->nthreads = 1;
  const char* v = getenv("XG_WS");
  c->ws = !(v && atoi(v) == 0);
  v = getenv("XG_PRUNE");
  c->prune = !(v && atoi(v) == 0);
  v = getenv("XG_UB"); c->ub = !(v && atoi(v) == 0);
  v = getenv("XG_DEDUP"); c->dedup = !(v && atoi(v) == 0);
  v = getenv("XG_LSKIP"); c->lskip = !(v && atoi(v) == 0);
  v = getenv("XG_PARTIAL"); c->partial = !(v && atoi(v) == 0);
  g_ctx[h] = c;
  return c;
}

static std::string key_of(const i64* s, int NS) { return std::string((const char*)s, sizeof(i64) * NS); }

static double box_margin(Eng* e, const i64* s, bool pen) {
  const int Q = e->Q;
  for (int r = 0; r < Q; r++) if (s[r] > s[Q + r]) return 1.0;
  if (s[Q + Q - 1] < s[0]) return 1.0;
  thread_local std::unique_ptr<Highs> hs;
  if (!hs) { hs.reset(new Highs()); cfg(*hs); }
  return e->margin(s, *hs, pen);
}

// leaf margin as the builder uses it: penalised, then unpenalised if the penalty is on
static double leaf_margin(Eng* e, const i64* s, double m) {
  if (m < 0.0 && e->m.pen > 0.0) {
    double mr = box_margin(e, s, false);
    if (mr >= 0.0) m = mr;
  }
  return m;
}

// Pruned scan ordered by LP-duality upper bounds (Ctx::ub): every child gets an upper bound on its
// margin from the box's kappa-row duals (Eng::ub, no simplex); entries are visited in decreasing
// min(ub left, ub right) and solved only while they can still enter the top keep, then the widest
// gap's entries while they can still beat its best.  Identical child boxes are solved once.  The
// complete entries contain the full scan's top keep and its best widest-gap entry (same LP values,
// same tie order), so decide sees the same list head.
// part: a lookahead scan, which needs only the best entry and only when its score exceeds thr (keep 1,
// no widest-gap phase).  sv / su (2n per child, NaN unknown): LP values and bounds of an earlier scan
// of the same box (same warm start, so the same values), reused and updated.
static bool scan_ub(Ctx* c, const i64* st, const Eng::WS& par, int wr, std::vector<double>& ml, std::vector<double>& mr,
                    bool part, double thr, std::vector<double>& sv, std::vector<double>& su) {
  Eng* e = c->e;
  const int Q = e->Q, NP = e->NP, NS = 2 * Q + 2 * NP;
  const int n = (Q + NP) * 8;
  if (!par.ok || (int)par.y.size() != Q) return false;
  // dual sign: both signs give valid bounds; keep the one that is tighter on the box itself
  std::vector<double> yp(Q), ym(Q);
  for (int r = 0; r < Q; r++) { yp[r] = std::max(par.y[r], 0.0); ym[r] = std::max(-par.y[r], 0.0); }
  const bool pos = e->ub(st, yp) <= e->ub(st, ym);
  const std::vector<double>& y = pos ? yp : ym;
  thread_local Eng::TermCache tc;
  e->term_cache(st, true, tc);
  thread_local std::vector<i64> ch;
  ch.resize((size_t)2 * n * NS);
  std::vector<int> slot(2 * n, -1);       // child -> distinct box index
  std::vector<int> rep;                   // distinct box -> first child index
  std::vector<double> ubv, val;
  std::vector<char> done;
  std::unordered_map<std::string, int> seen;
  std::vector<char> valid(n, 0);
  for (int kk = 0; kk < n; kk++) {
    int a = kk / 8, md = kk % 8;
    i64 lo, hi;
    if (a < Q) { lo = st[a]; hi = st[Q + a]; } else { lo = st[2 * Q + a - Q]; hi = st[2 * Q + NP + a - Q]; }
    ml[kk] = mr[kk] = -1e9;
    if (hi - lo < 2) continue;
    i64 q;
    i64* L = &ch[(size_t)(2 * kk) * NS];
    i64* R = &ch[(size_t)(2 * kk + 1) * NS];
    e->children(st, a, md, L, R, &q);
    if (!(lo < q && q < hi)) continue;
    valid[kk] = 1;
    mr[kk] = -2e9;
    for (int sd = 0; sd < 2; sd++) {
      const i64* b = sd ? R : L;
      int id = (int)rep.size();
      if (c->dedup) {
        auto ins = seen.emplace(key_of(b, NS), id);
        if (!ins.second) { slot[2 * kk + sd] = ins.first->second; c->n_dup++; continue; }
      }
      slot[2 * kk + sd] = id;
      rep.push_back(2 * kk + sd);
    }
  }
  val.assign(rep.size(), 0.0);
  done.assign(rep.size(), 0);
  ubv.assign(rep.size(), 0.0);
  std::vector<char> ubd(rep.size(), 0);
  if (sv.size() != (size_t)2 * n) { sv.assign(2 * n, NAN); su.assign(2 * n, NAN); }
  for (int ch2 = 0; ch2 < 2 * n; ch2++) {
    int id = slot[ch2];
    if (id < 0) continue;
    if (!std::isnan(sv[ch2])) { val[id] = sv[ch2]; done[id] = 1; }
    if (!std::isnan(su[ch2]) && (!ubd[id] || su[ch2] < ubv[id])) { ubv[id] = su[ch2]; ubd[id] = 1; }
  }
  thread_local std::unique_ptr<Highs> hsp;
  if (!hsp) { hsp.reset(new Highs()); cfg(*hsp); }
  Highs& hs = *hsp;
  const double tol = 1e-7;    // bounds are compared with this slack (LP tolerances, rounding)
  // XG_REFINE: before an entry's LPs, tighten its children's bounds with the duals of the child solved
  // last on the same axis and side (any duals give a valid bound; the smaller one is kept)
  static const bool refine = !(getenv("XG_REFINE") && atoi(getenv("XG_REFINE")) == 0);
  std::vector<std::vector<double>> ys(refine ? rep.size() : 0);
  std::vector<int> lasty(refine ? 2 * (Q + NP) : 0, -1);
  std::vector<int> refd(refine ? rep.size() : 0, -2);
  auto solve = [&](int child) -> double {
    int id = slot[child];
    if (!done[id]) {
      val[id] = e->margin(&ch[(size_t)rep[id] * NS], hs, true, &par, nullptr, refine ? &ys[id] : nullptr);
      if (refine && !ys[id].empty()) {
        for (double& v : ys[id]) v = std::max(pos ? v : -v, 0.0);
        lasty[(rep[id] / 2 / 8) * 2 + rep[id] % 2] = id;
      }
      done[id] = 1;
      c->n_lp0++;
      c->evals++;
      if (c->look) c->n_lplook++;
      if (c->inwr) c->n_lpwr++;
      if (ubd[id] && val[id] > ubv[id] + 1e-9) c->n_ubviol++;
    }
    return val[id];
  };
  // bounds on demand; the visiting order uses both bounds (XG_UBLAZY=1: the left child's bound only, measured slower)
  auto UB = [&](int child) {
    int id = slot[child];
    if (!ubd[id]) { ubv[id] = e->ub(&ch[(size_t)rep[id] * NS], y, true, &tc); ubd[id] = 1; }
    return ubv[id] + tol;
  };
  static const bool lazy = getenv("XG_UBLAZY") && atoi(getenv("XG_UBLAZY")) != 0;
  auto refine_entry = [&](int kk) {
    if (!refine) return;
    for (int sd = 0; sd < 2; sd++) {
      int id = slot[2 * kk + sd];
      int src = lasty[(kk / 8) * 2 + sd];
      if (done[id] || src < 0 || refd[id] == src || ys[src].empty()) continue;
      UB(2 * kk + sd);
      refd[id] = src;
      double u2 = e->ub(&ch[(size_t)rep[id] * NS], ys[src], true, &tc);
      if (u2 < ubv[id]) { ubv[id] = u2; c->n_ref++; }
    }
  };
  std::vector<int> ord;
  std::vector<double> sub(n, -1e300);
  for (int kk = 0; kk < n; kk++)
    if (valid[kk]) { ord.push_back(kk); sub[kk] = lazy ? UB(2 * kk) : std::min(UB(2 * kk), UB(2 * kk + 1)); }
  std::stable_sort(ord.begin(), ord.end(), [&](int u, int v) { return sub[u] > sub[v]; });
  typedef std::pair<double, int> P;
  auto better = [](const P& u, const P& v) { return u.first > v.first || (u.first == v.first && u.second < v.second); };
  std::vector<P> top;
  const int keep = part ? 1 : c->keep;
  auto full = [&]() { return (int)top.size() == keep; };
  for (int kk : ord) {
    if (full() && !better({sub[kk], kk}, top.back())) break;
    if (part && sub[kk] <= thr) break;      // no remaining entry can score above thr
    if (lazy && full() && !better({std::min(UB(2 * kk), UB(2 * kk + 1)), kk}, top.back())) continue;
    if (refine && (full() || part)) {
      refine_entry(kk);
      double b = std::min(UB(2 * kk), UB(2 * kk + 1));
      if ((full() && !better({b, kk}, top.back())) || (part && b <= thr)) { c->n_refsk++; continue; }
    }
    // solve the child with the smaller upper bound first
    int c0 = 2 * kk, c1 = 2 * kk + 1;
    if (UB(c1) < UB(c0)) std::swap(c0, c1);
    double v0 = solve(c0);
    if (full() && !better({std::min(v0, UB(c1)), kk}, top.back())) { c->n_ubsk++; continue; }
    if (part && std::min(v0, UB(c1)) <= thr) { c->n_ubsk++; continue; }
    double v1 = solve(c1);
    ml[kk] = val[slot[2 * kk]]; mr[kk] = val[slot[2 * kk + 1]];
    P u(std::min(v0, v1), kk);
    top.insert(std::upper_bound(top.begin(), top.end(), u, better), u);
    if ((int)top.size() > keep) top.pop_back();
  }
  // widest gap: its best entry (score, then index) among all entries
  c->inwr = true;
  bool have = false; P wb(0.0, 0);
  if (!part) for (int kk : ord) if (kk / 8 == wr && mr[kk] > -1.5e9) { P u(std::min(ml[kk], mr[kk]), kk); if (!have || better(u, wb)) { wb = u; have = true; } }
  if (!part) for (int kk : ord) {
    if (kk / 8 != wr || mr[kk] > -1.5e9) continue;
    if (have && !better({sub[kk], kk}, wb)) break;
    if (have && !better({std::min(UB(2 * kk), UB(2 * kk + 1)), kk}, wb)) continue;
    if (refine && have) {
      refine_entry(kk);
      if (!better({std::min(UB(2 * kk), UB(2 * kk + 1)), kk}, wb)) { c->n_refsk++; continue; }
    }
    int c0 = 2 * kk, c1 = 2 * kk + 1;
    if (UB(c1) < UB(c0)) std::swap(c0, c1);
    double v0 = solve(c0);
    if (have && !better({std::min(v0, UB(c1)), kk}, wb)) continue;
    double v1 = solve(c1);
    ml[kk] = val[slot[2 * kk]]; mr[kk] = val[slot[2 * kk + 1]];
    P u(std::min(v0, v1), kk);
    if (!have || better(u, wb)) { wb = u; have = true; }
  }
  c->inwr = false;
  // complete entries from the earlier scan (not visited here) stay in the list
  for (int kk = 0; kk < n; kk++)
    if (valid[kk] && mr[kk] <= -1.5e9 && done[slot[2 * kk]] && done[slot[2 * kk + 1]]) {
      ml[kk] = val[slot[2 * kk]]; mr[kk] = val[slot[2 * kk + 1]];
    }
  for (int ch2 = 0; ch2 < 2 * n; ch2++) {
    int id = slot[ch2];
    if (id < 0) continue;
    if (done[id]) sv[ch2] = val[id];
    if (ubd[id]) su[ch2] = ubv[id];
  }
  return true;
}

static const std::vector<Ent>& scan(Ctx* c, const i64* st, bool part = false, double thr = -1e300) {
  Eng* e = c->e;
  const int Q = e->Q, NP = e->NP, NS = 2 * Q + 2 * NP;
  std::string k = key_of(st, NS);
  const int nth0 = std::max(1, c->nthreads);
  part = part && c->partial && c->ub && c->keep > 0 && nth0 == 1;
  auto it = c->cache.find(k);
  std::vector<double> sv, su;
  if (it != c->cache.end()) {
    Ctx::Scan& S = it->second;
    if (S.full || (part && thr >= S.pthr)) { c->n_hit++; return S.out; }
    sv.swap(S.sv); su.swap(S.su);     // resume from the earlier lookahead scan
    c->cache.erase(it);
    c->npart--;
  }
  const int n = (Q + NP) * 8;
  std::vector<double> ml(n), mr(n, -2e9);    // mr -2e9: right child not solved
  int nth = std::max(1, c->nthreads);
  Eng::WS par;
  if (c->ws) {
    Highs hs; cfg(hs);
    e->margin(st, hs, true, nullptr, &par);
    c->evals++;
  }
  const Eng::WS* wi = par.ok ? &par : nullptr;
  // widest gap (decide's stall rule): its entries are always solved completely
  int wr = 0;
  for (int x = 1; x < Q; x++) if (st[Q + x] - st[x] > st[Q + wr] - st[wr]) wr = x;
  const bool prune = c->keep > 0;
  c->n_scan++;
  if (c->look) c->n_scanlook++;
  bool ubdone = c->ub && prune && nth == 1 && scan_ub(c, st, par, wr, ml, mr, part, thr, sv, su);
  if (!ubdone) part = false;
  if (!ubdone) {
  // phase 0: all entries (both children), or the left children and the widest gap's right children
  std::atomic<int> next{0};
  auto work = [&]() {
    Highs hs; cfg(hs);
    i64 left[MAXNS], right[MAXNS], q;
    for (;;) {
      int kk = next.fetch_add(1);
      if (kk >= n) return;
      int a = kk / 8, md = kk % 8;
      i64 lo, hi;
      if (a < Q) { lo = st[a]; hi = st[Q + a]; } else { lo = st[2 * Q + a - Q]; hi = st[2 * Q + NP + a - Q]; }
      if (hi - lo < 2) { ml[kk] = mr[kk] = -1e9; continue; }
      e->children(st, a, md, left, right, &q);
      if (!(lo < q && q < hi)) { ml[kk] = mr[kk] = -1e9; continue; }
      ml[kk] = e->margin(left, hs, true, wi);
      if (!prune || a == wr) mr[kk] = e->margin(right, hs, true, wi);
    }
  };
  auto run = [&](const std::function<void()>& f) {
    if (nth == 1) f();
    else {
      std::vector<std::thread> th;
      for (int t = 0; t < nth; t++) th.emplace_back(f);
      for (auto& x : th) x.join();
    }
  };
  run(work);
  if (prune) {
    // phase 1: right children in decreasing left margin (ties: axis-major order), nth at a time
    std::vector<int> cand;
    for (int kk = 0; kk < n; kk++) if (ml[kk] > -1e8 && mr[kk] <= -1.5e9) cand.push_back(kk);
    std::stable_sort(cand.begin(), cand.end(), [&](int u, int v) { return ml[u] > ml[v]; });
    // top keep complete entries by (score desc, index asc)
    std::vector<std::pair<double, int>> top;
    auto better = [](const std::pair<double, int>& u, const std::pair<double, int>& v) {
      return u.first > v.first || (u.first == v.first && u.second < v.second);
    };
    auto add = [&](int kk) {
      std::pair<double, int> u(std::min(ml[kk], mr[kk]), kk);
      top.insert(std::upper_bound(top.begin(), top.end(), u, better), u);
      if ((int)top.size() > c->keep) top.pop_back();
    };
    for (int kk = 0; kk < n; kk++) if (ml[kk] > -1e8 && mr[kk] > -1.5e9) add(kk);
    size_t ci = 0;
    while (ci < cand.size()) {
      // cand[ci] can enter the top only if (ml, index) ranks before the keep-th best
      if ((int)top.size() == c->keep && !better({ml[cand[ci]], cand[ci]}, top.back())) break;
      size_t c1 = std::min(cand.size(), ci + (size_t)nth);
      std::atomic<size_t> nx{ci};
      run([&]() {
        Highs hs; cfg(hs);
        i64 left[MAXNS], right[MAXNS], q;
        for (;;) {
          size_t u = nx.fetch_add(1);
          if (u >= c1) return;
          int kk = cand[u];
          e->children(st, kk / 8, kk % 8, left, right, &q);
          mr[kk] = e->margin(right, hs, true, wi);
        }
      });
      for (size_t u = ci; u < c1; u++) add(cand[u]);
      ci = c1;
    }
  }
  for (int kk = 0; kk < n; kk++) c->evals += (ml[kk] > -1e8) + (mr[kk] > -1e8);   // LPs solved
  }
  std::vector<Ent> out;
  out.reserve(n);
  for (int kk = 0; kk < n; kk++) {
    if (ml[kk] <= -1e8 || mr[kk] <= -1.5e9) continue;
    out.push_back({std::min(ml[kk], mr[kk]), kk / 8, kk % 8, ml[kk], mr[kk]});
  }
  std::stable_sort(out.begin(), out.end(), [](const Ent& u, const Ent& v) { return u.sc > v.sc; });
  static const i64 cmax = getenv("XG_CACHE") ? atoll(getenv("XG_CACHE")) : 4000;   // racing keeps more scans
  if ((i64)c->cache.size() > cmax || c->npart > cmax * 3 / 8) { c->cache.clear(); c->npart = 0; }
  Ctx::Scan S;
  S.out = std::move(out);
  S.full = !part;
  if (part) { S.pthr = thr; S.sv.swap(sv); S.su.swap(su); c->npart++; }
  return c->cache.emplace(k, std::move(S)).first->second.out;
}

// the child's lookahead score; with a threshold thr only a score above thr is exact (a smaller result
// means "at most thr": the caller's entry then cannot win)
static double child_score(Ctx* c, const i64* s, double mc, double thr = -1e300) {
  if (mc >= 0.0) return mc;
  c->n_look++;
  bool lk = c->look;
  c->look = true;
  const std::vector<Ent>& sc = scan(c, s, true, thr);
  c->look = lk;
  if (sc.empty() || sc[0].sc <= thr) return thr > -1e299 ? std::min(thr, sc.empty() ? -1.0 : sc[0].sc) : -1.0;
  return sc[0].sc;
}

// returns false when no split exists
static bool decide(Ctx* c, const i64* s, double m, int k, double stall, Ent& best) {
  Eng* e = c->e;
  const int Q = e->Q;
  c->keep = c->prune ? std::max(k, 1) : 0;
  std::vector<Ent> sc = scan(c, s);     // copy: lookahead scans may rehash the cache
  if (sc.empty()) return false;
  if (k <= 0) best = sc[0];
  else {
    bool have = false;
    i64 left[MAXNS], right[MAXNS], q;
    for (int t = 0; t < k && t < (int)sc.size(); t++) {
      const Ent& u = sc[t];
      e->children(s, u.a, u.m, left, right, &q);
      double v;
      if (!c->lskip || !have) v = std::min(child_score(c, left, u.x), child_score(c, right, u.y));
      else {
        // an entry wins only with v > best.sc and v = min(left score, right score): score a child
        // with margin >= 0 first (its own score, no scan), else the smaller margin, and skip the other
        // child's scan once the entry cannot win.  The skipped scans are those of children that are
        // never built, so the tree is unchanged.
        bool lf = u.x >= 0.0 ? true : (u.y >= 0.0 ? false : u.x <= u.y);
        double v0 = lf ? child_score(c, left, u.x, best.sc) : child_score(c, right, u.y, best.sc);
        if (v0 <= best.sc) { c->n_lskip++; continue; }
        double v1 = lf ? child_score(c, right, u.y, best.sc) : child_score(c, left, u.x, best.sc);
        v = std::min(v0, v1);
      }
      if (!have || v > best.sc) { best = {v, u.a, u.m, u.x, u.y}; have = true; }
    }
  }
  if (m < 0.0 && best.sc - m < stall * (-m)) {
    int r = 0;
    for (int x = 1; x < Q; x++) if (s[Q + x] - s[x] > s[Q + r] - s[r]) r = x;
    if (s[Q + r] - s[r] >= 2) {
      for (const Ent& u : sc) if (u.a == r) { best = u; break; }
    }
  }
  return true;
}

struct TreeStats { i64 leaves = 0, refl = 0, splits = 0, maxdepth = 0; };

static int node(Ctx* c, const i64* s, int depth, double m, bool have_m, int k, double stall, i64 budget,
                int maxdepth, TreeStats& st) {
  Eng* e = c->e;
  const int Q = e->Q, NP = e->NP;
  if (depth > st.maxdepth) st.maxdepth = depth;
  if (budget > 0 && st.leaves + st.refl > budget) return 1;
  if (s[Q + Q - 1] < s[0]) { st.refl++; return 0; }
  if (!have_m) m = box_margin(e, s, true);
  m = leaf_margin(e, s, m);
  if (m >= 0.0) { st.leaves++; return 0; }
  if (depth >= maxdepth) return 2;
  Ent b;
  if (!decide(c, s, m, k, stall, b)) return 3;
  std::vector<i64> l(2 * Q + 2 * NP), r(2 * Q + 2 * NP);
  i64 q;
  e->children(s, b.a, b.m, l.data(), r.data(), &q);
  st.splits++;
  int rc = node(c, l.data(), depth + 1, b.x, true, k, stall, budget, maxdepth, st);
  if (rc) return rc;
  return node(c, r.data(), depth + 1, b.y, true, k, stall, budget, maxdepth, st);
}

}  // namespace fb

extern "C" {

int eng_decide(void* h, const i64* st, double m, int k, int nthreads, double stall,
               int* ax, int* md, double* x, double* y) {
  fb::Ctx* c = fb::ctx_of(h);
  c->nthreads = nthreads;
  fb::Ent b;
  if (!fb::decide(c, st, m, k, stall, b)) return 0;
  *ax = b.a; *md = b.m; *x = b.x; *y = b.y;
  return 1;
}

double eng_leaf_margin(void* h, const i64* st) {
  Eng* e = (Eng*)h;
  return fb::leaf_margin(e, st, fb::box_margin(e, st, true));
}

int eng_float_tree(void* h, const i64* st, int k, int nthreads, double stall, i64 budget, int maxdepth,
                   i64* stats) {
  fb::Ctx* c = fb::ctx_of(h);
  c->nthreads = nthreads;
  i64 ev0 = c->evals;
  fb::TreeStats ts;
  int rc = fb::node(c, st, 0, 0.0, false, k, stall, budget, maxdepth, ts);
  stats[0] = ts.leaves; stats[1] = ts.refl; stats[2] = ts.splits; stats[3] = ts.maxdepth;
  stats[4] = c->evals - ev0;
  return rc;
}

void eng_cache_clear(void* h) { fb::ctx_of(h)->cache.clear(); }

}  // extern "C"
