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
// The choices are the Python builder's, so trees are identical (checked on q9 roots 71 and 23).
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

namespace fb {

struct Ent { double sc; int a, m; double x, y; };

struct Ctx {
  Eng* e;
  int nthreads;
  std::unordered_map<std::string, std::vector<Ent>> cache;
  i64 evals = 0;
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

static const std::vector<Ent>& scan(Ctx* c, const i64* st) {
  Eng* e = c->e;
  const int Q = e->Q, NP = e->NP, NS = 2 * Q + 2 * NP;
  std::string k = key_of(st, NS);
  auto it = c->cache.find(k);
  if (it != c->cache.end()) return it->second;
  const int n = (Q + NP) * 8;
  std::vector<double> ml(n), mr(n);
  int nth = std::max(1, c->nthreads);
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
      ml[kk] = e->margin(left, hs);
      mr[kk] = e->margin(right, hs);
    }
  };
  if (nth == 1) work();
  else {
    std::vector<std::thread> th;
    for (int t = 0; t < nth; t++) th.emplace_back(work);
    for (auto& x : th) x.join();
  }
  c->evals += 2 * n;
  std::vector<Ent> out;
  out.reserve(n);
  for (int kk = 0; kk < n; kk++) {
    if (ml[kk] <= -1e8) continue;
    out.push_back({std::min(ml[kk], mr[kk]), kk / 8, kk % 8, ml[kk], mr[kk]});
  }
  std::stable_sort(out.begin(), out.end(), [](const Ent& u, const Ent& v) { return u.sc > v.sc; });
  if (c->cache.size() > 4000) c->cache.clear();
  return c->cache.emplace(k, std::move(out)).first->second;
}

static double child_score(Ctx* c, const i64* s, double mc) {
  if (mc >= 0.0) return mc;
  const std::vector<Ent>& sc = scan(c, s);
  return sc.empty() ? -1.0 : sc[0].sc;
}

// returns false when no split exists
static bool decide(Ctx* c, const i64* s, double m, int k, double stall, Ent& best) {
  Eng* e = c->e;
  const int Q = e->Q;
  std::vector<Ent> sc = scan(c, s);     // copy: lookahead scans may rehash the cache
  if (sc.empty()) return false;
  if (k <= 0) best = sc[0];
  else {
    bool have = false;
    i64 left[MAXNS], right[MAXNS], q;
    for (int t = 0; t < k && t < (int)sc.size(); t++) {
      const Ent& u = sc[t];
      e->children(s, u.a, u.m, left, right, &q);
      double v = std::min(child_score(c, left, u.x), child_score(c, right, u.y));
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
