// wdiag ENG GFILE [d ...]: for each line of GFILE (Q gap values in SC units), the float leaf-LP margin of
// the box with integer gaps round(g * SC) +- d (pair-sum bounds A, B = sums of L, U), for each d given
// (default 0 1 4 16 64; a vector with g_{Q-1} < g_0 is reversed first, as the half rule requires); then per term: n i j E ta lb(E, E+1) lb(E-4, E+4) dist-to-nearest-table-point.
// Build in this directory (HIGHS, GMP: install prefixes, as in ../cpp_race/Makefile):
// g++ -O2 -std=c++17 -I../cpp_race -I$HIGHS/include/highs -I$HIGHS/include -I$GMP/include wdiag.cpp -o wdiag
//     -Wl,-rpath,$HIGHS/lib -L$HIGHS/lib -L$GMP/lib -lhighs -lgmpxx -lgmp -lpthread
#include "engine.cpp"
#include <fstream>
#include <sstream>
using namespace fb;
int main(int argc, char** argv) {
  Eng* e = (Eng*)eng_load(argv[1]);
  if (!e) { fprintf(stderr, "eng_load failed\n"); return 1; }
  Model& m = e->m;
  const int Q = e->Q, NP = e->NP, NS = 2 * Q + 2 * NP;
  std::vector<i64> ds;
  for (int a = 3; a < argc; a++) ds.push_back(atol(argv[a]));
  if (ds.empty()) ds = {0, 1, 4, 16, 64};
  std::ifstream f(argv[2]);
  std::string ln;
  int row = 0;
  while (std::getline(f, ln)) {
    std::istringstream is(ln);
    std::vector<double> g(Q);
    for (int r = 0; r < Q; r++) is >> g[r];
    if (!is) continue;
    std::vector<i64> gi(Q);
    for (int r = 0; r < Q; r++) gi[r] = llround(g[r] * m.SC);
    if (gi[Q - 1] < gi[0]) std::reverse(gi.begin(), gi.end());   // the half rule: g_{Q-1} >= g_0
    printf("row %d margins", row);
    for (i64 d : ds) {
      std::vector<i64> s(NS);
      for (int r = 0; r < Q; r++) { s[r] = gi[r] - d; s[Q + r] = gi[r] + d; }
      for (int k = 0; k < NP; k++) {
        i64 a = 0, b = 0;
        for (int r = m.PI[k]; r < m.PJ[k]; r++) { a += s[r]; b += s[Q + r]; }
        s[2 * Q + k] = a; s[2 * Q + NP + k] = b;
      }
      printf(" d%lld %.6e", (long long)d, eng_margin(e, s.data()));
    }
    printf("\n");
    for (int n = 0; n < m.nT; n++) {
      i64 E = 0;
      for (int r = m.TI[n]; r < m.TJ[n]; r++) E += gi[r];
      i64 dp = -1;
      for (i64 t = 0; t < 4096; t++) {
        if (E - t >= 0 && E - t < (i64)m.pidx.size() && m.pidx[E - t] >= 0) { dp = t; break; }
        if (E + t < (i64)m.pidx.size() && m.pidx[E + t] >= 0) { dp = t; break; }
      }
      printf("t %d %d %d %lld %.12g %.10e %.10e %lld\n", n, m.TI[n], m.TJ[n], (long long)E, m.ta[n],
             e->lb(E, E + 1) / 1e10, e->lb(E - 4, E + 4) / 1e10, (long long)dp);
    }
    row++;
  }
}
