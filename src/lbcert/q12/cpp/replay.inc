// Exact tree replay in C++ with GMP (included at the end of engine.cpp after builder.inc).
//
// The walk of q9hs hs.HSChecker (replay.Checker.walkC / splitAx / leafStep, mleaf with dec4QG,
// ydecH with the half-space row c = NP, mcheckGX) for Q gaps, with the split word
// 1 | ax << 1 | md << (1 + AXB) of q12/exact12.py.  Integer arithmetic is exact: positions and
// closure bounds in int64 (as the engine's closure), per-term products in __int128, every sum
// that carries a weight (tA ~ 2^104, SIG ~ 2^127, cN ~ 2^96) in GMP.  Leaf words are read through
// a WBITS-bit window like the Python walker (bits past the window read as 0).  Variance leaves
// (leaf bit 1) are rejected: the q12 trees do not use them.
//
//   void eng_replay_setup(void*, int FS, int LB, int QB, int YFUEL, int AXB, int WBITS,
//                         const uint64_t* sig, const uint64_t* cN, const uint64_t* BS,
//                         const uint64_t* tA)   128-bit integers as (lo, hi) pairs; BS has Q,
//                                               tA has nT entries in TS order
//   i64 eng_replay(void*, const uint64_t* words, i64 nwords, i64 pos, const i64* st, int fuel,
//                  i64* stats)   end position or 0; stats = leaves, refl, failed leaf position + 1
#include <gmpxx.h>

namespace rp {

struct RP {
  int FS = 3, LB = 10, QB = 14, YFUEL = 42, AXB = 7, WBITS = 1024, PB = 7;
  mpz_class SIG, cN;
  std::vector<mpz_class> BS, tA;
  const uint64_t* w = nullptr;
  i64 nw = 0;
};

static std::unordered_map<void*, RP*> g_rp;
static std::mutex g_rmu;

static RP* rp_of(void* h) {
  std::lock_guard<std::mutex> lk(g_rmu);
  auto it = g_rp.find(h);
  if (it != g_rp.end()) return it->second;
  RP* r = new RP();
  g_rp[h] = r;
  return r;
}

static mpz_class mpz128(const uint64_t* p) {
  mpz_class hi = (unsigned long)(p[1] >> 32), x;
  x = hi;
  x <<= 32; x += (unsigned long)(p[1] & 0xffffffffULL);
  x <<= 32; x += (unsigned long)(p[0] >> 32);
  x <<= 32; x += (unsigned long)(p[0] & 0xffffffffULL);
  return x;
}

static mpz_class mpz_i128(__int128 v) {
  bool neg = v < 0;
  unsigned __int128 u = neg ? (unsigned __int128)(-v) : (unsigned __int128)v;
  uint64_t p[2] = {(uint64_t)u, (uint64_t)(u >> 64)};
  mpz_class x = mpz128(p);
  return neg ? mpz_class(-x) : x;
}

// bits [pos, pos + n) of the stream, n <= 62
static inline i64 gb(const RP& R, i64 pos, int n) {
  i64 v = 0;
  for (int b = 0; b < n; b++) {
    i64 p = pos + b;
    i64 wi = p >> 6;
    if (wi < R.nw && ((R.w[wi] >> (p & 63)) & 1ULL)) v |= (i64)1 << b;
  }
  return v;
}

// bits of the leaf word read through the WBITS window starting at base
static inline i64 lw(const RP& R, i64 base, i64 off, int n) {
  i64 v = 0;
  for (int b = 0; b < n; b++) {
    i64 o = off + b;
    if (o >= R.WBITS) break;
    i64 p = base + o;
    i64 wi = p >> 6;
    if (wi < R.nw && ((R.w[wi] >> (p & 63)) & 1ULL)) v |= (i64)1 << b;
  }
  return v;
}

struct Pt { i64 V = 0, P = 0, Mv = 0, A = 0, B = 0; };

static inline Pt pt(const Eng* e, i64 x) {
  Pt r;
  if (x < 0 || x >= (i64)e->m.pidx.size()) return r;
  int i = e->m.pidx[x];
  if (i < 0) return r;
  r.V = e->m.pV[i]; r.P = e->m.pP[i]; r.Mv = e->m.pM[i]; r.A = e->m.pA[i]; r.B = e->m.pB[i];
  return r;
}

static inline bool ivIn(const Pt& v, i64 L, i64 U, i64 p) {
  return 1 <= v.B && v.A <= L && L <= p && p <= U && U <= v.B;
}

// mleaf (payload at base + 2): returns the payload length or 0 when the check fails
static i64 mleaf(const Eng* e, const RP& R, i64 base, const i64* s) {
  const int Q = e->Q, NP = e->NP, nT = e->m.nT;
  const i64* L = s; const i64* U = s + Q; const i64* A = s + 2 * Q; const i64* B = s + 2 * Q + NP;
  const i64 b0 = base + 2;
  auto W = [&](i64 off, int n) { return lw(R, base, 2 + off, n); };
  (void)b0;
  i64 o = 0;
  std::vector<int> ta(nT); std::vector<i64> tl(nT), tp(nT), tr(nT), eLv(nT), eUv(nT), e0v(nT);
  for (int n = 0; n < nT; n++) {
    int i = e->m.TI[n], j = e->m.TJ[n], kk = e->m.TK[n];
    i64 sL = 0, sU = 0;
    for (int r = i; r < j; r++) { sL += L[r]; sU += U[r]; }
    i64 eL, eU;
    if (j - i == 1) { eL = L[i]; eU = U[i]; } else { eL = std::max(A[kk], sL); eU = std::min(B[kk], sU); }
    eLv[n] = eL; eUv[n] = eU; e0v[n] = sL;
    int a = (int)W(o, 2);
    i64 lam = 0;
    if (a == 2) lam = W(o + 9, R.LB);
    else if (a == 3) lam = W(o + 16, R.LB);
    i64 p = a == 0 ? 0 : e->gpt(eL, eU, (int)W(o + 2, 7));
    i64 r = a == 3 ? e->gpt(eL, eU, (int)W(o + 9, 7)) : 0;
    ta[n] = a; tl[n] = lam << nsub(10, R.LB); tp[n] = p; tr[n] = r;
    o += a == 1 ? 9 : a == 2 ? 9 + R.LB : a == 3 ? 16 + R.LB : 2;
  }
  // ydecH
  std::vector<mpz_class> P(Q), S(Q);
  for (int r = 0; r < Q; r++) { P[r] = 0; S[r] = 0; }
  mpz_class Cp = 0, Cm = 0;
  for (int f = 0; f < R.YFUEL; f++) {
    if (W(o, 1) != 1) { o += 1; break; }
    i64 c = W(o + 1, R.PB);
    i64 o1 = o + 1 + R.PB;
    if (c > NP) { o = o1 + R.QB + 1; break; }
    mpz_class Y = R.SIG * mpz_class((unsigned long)(W(o1 + 1, R.QB) & (((i64)1 << R.QB) - 1)));
    if (c == NP) {
      P[Q - 1] += Y; S[0] += Y;
      Cp += Y * mpz_class((unsigned long)nsub(L[Q - 1], L[0]));
      Cm += Y * mpz_class((unsigned long)nsub(L[0], L[Q - 1]));
    } else {
      bool sd = W(o1, 1) == 1;
      int i = e->m.PI[c], j = e->m.PJ[c];
      i64 sL = 0;
      for (int r = i; r < j; r++) sL += L[r];
      for (int r = i; r < j; r++) { if (sd) S[r] += Y; else P[r] += Y; }
      if (sd) { Cp += Y * mpz_class((unsigned long)nsub(B[c], sL)); Cm += Y * mpz_class((unsigned long)nsub(sL, B[c])); }
      else { Cp += Y * mpz_class((unsigned long)nsub(sL, A[c])); Cm += Y * mpz_class((unsigned long)nsub(A[c], sL)); }
    }
    o = o1 + R.QB + 1;
  }
  // mcheckGX
  mpz_class smcn = 0, smcp = 0, smv = 0;
  std::vector<mpz_class> wsl(Q), ssl(Q);
  for (int r = 0; r < Q; r++) { wsl[r] = 0; ssl[r] = 0; }
  bool okterms = true;
  const i64 TWO9 = 2000000000;
  for (int n = 0; n < nT; n++) {
    int a = ta[n]; i64 lam = tl[n], p = tp[n], r = tr[n];
    i64 l1 = a == 1 ? 1024 : a == 2 ? lam : a == 3 ? nsub(1024, lam) : 0;
    i64 l2 = a == 3 ? lam : 0;
    i64 lc = a == 1 ? 0 : a == 2 ? nsub(1024, lam) : a == 3 ? 0 : 1024;
    i64 eL = eLv[n], eU = eUv[n], e0 = e0v[n];
    Pt fp = pt(e, p), fr = pt(e, r);
    bool ok = lam <= 1024;
    if (ok && l1 != 0) ok = ivIn(fp, eL, eU, p);
    if (ok && l2 != 0) ok = ivIn(fr, eL, eU, r);
    okterms = okterms && ok;
    __int128 mcn = 0, mcp = 0, mv = 0, msl = 0;
    if (l1 || l2) {
      mcn = (__int128)l1 * nsub(TWO9, fp.Mv) * nsub(p, e0) + (__int128)l2 * nsub(TWO9, fr.Mv) * nsub(r, e0);
      mcp = (__int128)l1 * nsub(fp.Mv, TWO9) * nsub(p, e0) + (__int128)l2 * nsub(fr.Mv, TWO9) * nsub(r, e0);
    }
    i64 uc = std::max(eU, eL + 1);
    mv = (__int128)lc * (lc ? e->lb(eL, uc) : 0) + (__int128)l1 * (l1 ? fp.V : 0) + (__int128)l2 * (l2 ? fr.V : 0);
    msl = (__int128)l1 * (l1 ? fp.P : 0) + (__int128)l2 * (l2 ? fr.P : 0);
    const mpz_class& t = R.tA[n];
    if (mcn) smcn += t * mpz_i128(mcn);
    if (mcp) smcp += t * mpz_i128(mcp);
    if (mv) smv += t * mpz_i128(mv);
    mpz_class wl = t * mpz_class((unsigned long)(l1 + l2)), sl = msl ? mpz_class(t * mpz_i128(msl)) : mpz_class(0);
    for (int g = e->m.TI[n]; g < e->m.TJ[n]; g++) { wsl[g] += wl; ssl[g] += sl; }
  }
  mpz_class Ngs = 0, bl = 0;
  for (int g = 0; g < Q; g++) {
    mpz_class lhsg = mpz_class((long)TWO9) * wsl[g] + P[g];
    mpz_class rhsg = mpz_class("1024000000000") * R.BS[g] + ssl[g] + S[g];
    if (lhsg > rhsg) Ngs += mpz_class((unsigned long)nsub(U[g], L[g])) * (lhsg - rhsg);
    bl += R.BS[g] * mpz_class((unsigned long)L[g]);
  }
  mpz_class lhs = mpz_class("335544320000000000") * R.cN + 10 * (smcn + Cp + Ngs);
  mpz_class rhs = mpz_class("10240000000000") * bl + 32768 * smv + 10 * (smcp + Cm);
  bool boxok = true;
  for (int g = 0; g < Q; g++) if (L[g] > U[g]) boxok = false;
  if (lhs <= rhs && okterms && boxok) return o;
  return 0;
}

struct WS { i64 leaves = 0, refl = 0, failpos = 0; };

static i64 walk(const Eng* e, const RP& R, int fuel, i64 pos, const i64* s, WS& ws) {
  if (fuel == 0) return 0;
  const int Q = e->Q, NP = e->NP;
  if (gb(R, pos, 1) == 1) {
    int ax = (int)gb(R, pos + 1, R.AXB), md = (int)gb(R, pos + 1 + R.AXB, 3);
    if (ax >= Q + NP) return 0;
    std::vector<i64> l(2 * Q + 2 * NP), r(2 * Q + 2 * NP);
    i64 q;
    e->children(s, ax, md, l.data(), r.data(), &q);
    i64 pp = walk(e, R, fuel - 1, pos + 4 + R.AXB, l.data(), ws);
    if (pp == 0) return 0;
    return walk(e, R, fuel - 1, pp, r.data(), ws);
  }
  if (s[Q + Q - 1] < s[0]) { ws.refl++; return pos + 1; }
  if (gb(R, pos + 1, 1) == 1) { ws.failpos = pos + 1; return 0; }   // variance leaf: not supported
  i64 n = mleaf(e, R, pos, s);
  ws.leaves++;
  if (n == 0) { ws.failpos = pos + 1; return 0; }
  return pos + 2 + n;
}

}  // namespace rp

extern "C" {

void eng_replay_setup(void* h, int FS, int LB, int QB, int YFUEL, int AXB, int WBITS, const uint64_t* sig,
                      const uint64_t* cN, const uint64_t* BS, const uint64_t* tA) {
  Eng* e = (Eng*)h;
  rp::RP* R = rp::rp_of(h);
  R->FS = FS; R->LB = LB; R->QB = QB; R->YFUEL = YFUEL; R->AXB = AXB; R->WBITS = WBITS;
  int pb = 0; while ((1 << pb) <= e->NP) pb++;
  R->PB = pb;                                    // NP.bit_length()
  R->SIG = rp::mpz128(sig); R->cN = rp::mpz128(cN);
  R->BS.resize(e->Q); R->tA.resize(e->m.nT);
  for (int r = 0; r < e->Q; r++) R->BS[r] = rp::mpz128(BS + 2 * r);
  for (int n = 0; n < e->m.nT; n++) R->tA[n] = rp::mpz128(tA + 2 * n);
}

i64 eng_replay(void* h, const uint64_t* words, i64 nwords, i64 pos, const i64* st, int fuel, i64* stats) {
  Eng* e = (Eng*)h;
  rp::RP R = *rp::rp_of(h);
  R.w = words; R.nw = nwords;
  rp::WS ws;
  i64 end = rp::walk(e, R, fuel, pos, st, ws);
  stats[0] = ws.leaves; stats[1] = ws.refl; stats[2] = ws.failpos;
  return end;
}

}  // extern "C"
