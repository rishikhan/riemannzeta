// LP VARIANT (src/lbcert/q12/gmin12_cpp): gmin12/gmin_stream.cpp plus the cut-model LP of
// sep_window_search.model_ratio in the core (lp.inc, HiGHS C++ API): requests MAGIC_LPI / MAGIC_LPR /
// MAGIC_LPS.  The template search, the prescreen and their reply formats are unchanged.
//
// STREAMING VARIANT (src/lbcert/q12/gmin12): pipeline/cpp/gmin.cpp with the template starts
// generated inside the core instead of read from starts.bin, so q = 12 (16.6M half-templates)
// runs in bounded memory.
//
//   spec key `gen_half 1`: the starts are the rows of {1,2,3,4}^q U {1,2,3,5}^q with
//   r <= reverse(r) lexicographically (sep_window_search.half_templates), enumerated by their
//   base-5 code over the digits 1..5 (a code is valid when its row does not hold both a 4 and
//   a 5, and is canonical).  The base-5 code is monotone in the lexicographic order np.unique
//   sorts by, so the (F, code) selection order equals the (F, row index) order of the array path.
//   Stage 1 runs per row in worker threads, and each thread keeps only its keep_stage1 best
//   (F, code) in a bounded heap; the heaps are merged, the survivors regenerated, and stage 2
//   runs as before.  Random starts from the request get codes 5^q + r.
//   Request MAGIC_PRE (k): F at every half-template start without Newton, the k lowest
//   (F, code), returned as (F, g) rows: the warm-round prescreen of sep_score.
//
// Everything else (objective, Newton, retirement, reply format) is pipeline/cpp/gmin.cpp unchanged.
// threaded C++ core for the `the numpy gmin` inner loop.
//
// WHAT THIS REPLACES.  the profile measures one q=8 `score()`
// at 136 s with `gmin` at ~99% of it, split
//     _horner 38%  |  np.linalg.solve 14-19%  |  _idx_t 19%  |  rest small.
// Everything in that split is the batched projected damped-Newton run of
// `pipeline/objective.py newton_batch` over the 124,511 template starts plus 1,200 random
// starts, evaluated against the three cubic-spline tables of
// `pipeline/wtable.py`.  This file is that loop, and nothing else:
//
//     stage 1   newton(iters = min(20, iters))   on all starts
//     select    argsort(F, +inf for non-finite)[:keep_stage1]
//     symdup    optional: append every survivor's reversal (pipeline/parmin.py ParMin)
//     stage 2   newton(iters)                    on the survivors
//
// and it hands the survivors' (F, g) back to Python, which keeps the finite
// filter, the argsort and the 2e-3 dedup as `the numpy gmin` writes
// them.  Start generation stays in Python too, so numpy's PCG64 stream is the
// one used and nothing here has to reproduce it.
//
// DIRECTION OF ERROR.  Unchanged: the value returned is a MINIMIZATION result,
// an UPPER bound on the true infimum of F, and it is a float proxy used for
// RANKING windows.  It is not, and never becomes, a certificate.  Certificates
// come from the interval branch-and-bound in `pipeline/cpp/verify.cpp`, which this
// file does not touch and shares no code with.
//
// FOUR THINGS THIS DOES THAT NUMPY CANNOT
//
// (1) ONE ADDRESS SPACE.  The spline coefficient blob is mmap'd read-only and
//     every thread reads the same pages.  The Python path pays one ~2 GB
//     construction peak and a ~130 MB resident table PER PROCESS.
//
// (2) FUSED GATHER + HORNER.  `pipeline/wtable.py` holds twelve separate length-(n-1)
//     coefficient vectors (four per spline, three splines), so `all3` at one
//     point touches twelve cache lines out of ~130 MB.  Here the twelve
//     coefficients at one interval are one 96-byte record, so `all3` touches
//     two adjacent lines and the W-only evaluation touches one.  The index and
//     the local coordinate are computed once and consumed immediately, so the
//     (n_rows x 36) intermediate arrays numpy materializes for idx, t, w, wp,
//     wpp never exist.
//
// (3) FIXED-SIZE Q x Q SOLVE.  `np.linalg.solve` on a stack of (n, q, q) calls
//     LAPACK dgesv per matrix with its per-call overhead; here the LU with
//     partial pivoting is inlined at compile-time Q.  Rounding differs from
//     LAPACK's (right-looking unblocked here, recursive dgetrf2 there) at the
//     1e-16 level -- see the tolerance note below.
//
// (4) EARLY RETIREMENT, WHICH IS EXACT.  Two states of a Newton row are proven
//     fixed points of the iteration, so the row can be dropped from every later
//     iteration without changing a bit of its answer:
//
//       (a) mu is already at the cap 1e8 and the trial step is REJECTED.  Then
//           g, F, grad and H are unchanged and mu' = min(6*1e8, 1e8) = 1e8, so
//           the next iteration re-derives the identical A, the identical dx,
//           the identical trial point and the identical rejection, forever.
//       (b) dx is exactly the zero vector.  Then gt = max(g - 0, 0) = g (g is
//           already clamped nonnegative), Ft is the same expression on the same
//           input as Fc hence bitwise equal, and `Ft < Fc - 1e-18` is false.
//           dx = 0 requires grad = 0, which depends only on g, so it recurs
//           whatever mu does.
//
//     Both are conditions on state the loop already has.  Retirement therefore
//     only skips work; `--noretire` runs the identical arithmetic without it
//     and `pipeline/tests/test_cppgmin.py` gate 3 checks the two agree to the last bit.
//
//     (c) REJECTED-STEP MEMOIZATION, the part that actually pays.  Retirement by
//         (a) is rare inside stage 1, because mu needs THIRTEEN consecutive
//         rejections to climb 1e-2 -> 1e8 and stage 1 runs only 20 iterations;
//         measured, it skips 1.1% of the row-iterations at q=8.  But every one
//         of those rejections leaves g unchanged, and Fc, grad and H are pure
//         functions of g, so the next iteration recomputes them from identical
//         inputs and gets identical results.  They are cached instead.  A
//         rejected iteration then costs one W-only table sweep instead of a
//         full W/W'/W'' sweep plus a W-only sweep -- and near convergence
//         almost every iteration is a rejection.  This is memoization of a pure
//         function, so it is exact by construction, and `--noretire` disables
//         it together with (a) and (b) for the gate.
//
// WHAT IS *NOT* BIT-IDENTICAL TO NUMPY, AND WHY THAT IS THE RIGHT CALL
//
//   * Reduction order.  `w @ a`, `g @ b` and `(wp*a) @ U` are BLAS matvecs with
//     vectorized/blocked summation; here they are sequential.  ~1e-16 relative.
//   * The LU rounding, as above.
//   * `d = g @ U.T` is a 0/1 matmul there and a prefix-sum difference
//     y[j] - y[i] here.
//   * `np.argsort` default kind is introsort, which is NOT stable, so its order
//     among rows with exactly equal F is arbitrary; the selection here breaks
//     ties by row index.  Only observable under an exact tie at the
//     keep_stage1 boundary; the count of boundary ties is reported on stderr.
//
//   The scorer's own ranking scale is ~5e-08 (`new/04-traps.md` 8: rankings of
//   window candidates INVERT at 5e-08, which is why finalists are rescored at
//   rounds >= 45 and then certified).  A 1e-12 discrepancy in fmin is four
//   orders below that scale.  It is still a discrepancy and it is gated at
//   1e-12, not waved away.
//
// The spline coefficients are INGESTED, never re-derived: `pipeline/cppgmin.py`
// dumps `scipy.interpolate.CubicSpline`'s own `.x` and `.c` from the same
// `pipeline/wtable.py WTable` build the numpy path uses.  There is no spline
// construction anywhere in this file.
//
// USAGE
//     gmin serve   <specdir> [threads] [--noretire]   binary reply on stdout
//     gmin bench   <specdir> [threads] [--noretire]   fmin on stderr instead
//     gmin evaltab <specdir> <x.bin> <out.bin>
//
// Build (mirrors `pipeline/certspec.py VERIFY_FLAGS`; -ffast-math is NEVER used):
//     clang++ -std=c++17 -O3 -DNDEBUG -ffp-contract=off -mcpu=native -flto \
//             -DQQ=8 -o gmin_q8 pipeline/cpp/gmin.cpp
#include <algorithm>
#include <chrono>
#include <atomic>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <thread>
#include <vector>
#ifdef __ARM_NEON
#include <arm_neon.h>
#endif
#if !defined(__ARM_NEON) && defined(__AVX__)
#include <immintrin.h>
#endif

#include <fcntl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>

#ifndef QQ
#define QQ 8
#endif
static const int Q = QQ;
static const int NP = QQ * (QQ + 1) / 2;

static const double MU0 = 1e-2;
static const double MU_LO = 1e-12;
static const double MU_HI = 1e8;
static const double MU_DN = 0.4;
static const double MU_UP = 6.0;
static const double ACC_TOL = 1e-18;

// ------------------------------------------------------------------ pair index
// `pipeline/geometry.py Geom`: PAIRS = [(i,j) for i in range(q+1) for j in range(i+1,q+1)],
// i-major and j ascending.  `a` arrives in this order.
static int PI[NP], PJ[NP];
static void build_pairs() {
    int p = 0;
    for (int i = 0; i <= Q; i++)
        for (int j = i + 1; j <= Q; j++) { PI[p] = i; PJ[p] = j; p++; }
}

// ------------------------------------------------------------------- the table
struct Tab {
    const double* rec = nullptr;   // 12 * (nbrk-1), interleaved cw0..3 cp0..3 cpp0..3
    const double* brk = nullptr;   // nbrk breakpoints (CubicSpline.x)
    int64_t nbrk = 0;
    int64_t m = 0;                 // nbrk - 2, the top interval index
    double inv_h = 0.0;
    double hmax = 0.0;
    double ymax = 0.0;
};

// `pipeline/wtable.py WTable._idx_t`'s exact fallback: clip(searchsorted(b, x, 'right') - 1, 0, m).
static inline int64_t ss_right(const Tab& T, double x) {
    int64_t lo = 0, hi = T.nbrk;            // first index with brk[i] > x
    while (lo < hi) {
        int64_t mid = lo + ((hi - lo) >> 1);
        if (T.brk[mid] > x) hi = mid; else lo = mid + 1;
    }
    int64_t f = lo - 1;
    if (f < 0) f = 0;
    if (f > T.m) f = T.m;
    return f;
}

// `pipeline/wtable.py WTable._idx_t`: multiply-index guess corrected to the EXACT PPoly piece.
static inline int64_t idx_of(const Tab& T, double x, double& t) {
    int64_t idx = (int64_t)(x * T.inv_h);
    if (idx > T.m) idx = T.m;               // idx <= m => brk[idx+1] is in range
    t = x - T.brk[idx];
    // Correct against the LOCAL right edge brk[idx+1], not the global hmax.  With
    // non-uniform knots the local width can be below hmax, and an x in that band
    // (brk[idx+1] <= x < brk[idx]+hmax) would leave idx one too low -- the previous
    // piece evaluated past its right end.  Falling back unless brk[idx] <= x <
    // brk[idx+1] makes idx clip(searchsorted(brk,x,'right')-1, 0, m).
    if (t < 0.0 || x >= T.brk[idx + 1]) {
        idx = ss_right(T, x);
        t = x - T.brk[idx];
    }
    return idx;
}

// `pipeline/wtable.py WTable.W`: |x|, exactly 0.0 beyond ymax.
static inline double eval_w(const Tab& T, double x) {
    x = std::fabs(x);                       // pipeline/wtable.py WTable.W: x = np.abs(x) (W is even)
    if (!(x <= T.ymax)) return 0.0;         // NaN-safe: NaN goes to 0.0 like numpy's ~inb
    double t;
    const double* c = T.rec + 12 * idx_of(T, x, t);
    return ((c[0] * t + c[1]) * t + c[2]) * t + c[3];
}

// `pipeline/wtable.py WTable.all3`: one index computation, three Horners, 0.0 outside [0, ymax].
static inline void eval3(const Tab& T, double x, double& w, double& wp, double& wpp) {
    if (!(x <= T.ymax) || !(x >= 0.0)) { w = wp = wpp = 0.0; return; }
    double t;
    const double* c = T.rec + 12 * idx_of(T, x, t);
    w   = ((c[0] * t + c[1]) * t + c[2]) * t + c[3];
    wp  = ((c[4] * t + c[5]) * t + c[6]) * t + c[7];
    wpp = ((c[8] * t + c[9]) * t + c[10]) * t + c[11];
}

// ---------------------------------------------------------------- the objective
struct Ctx {
    const Tab* T;
    const double* a;    // NP
    const double* b;    // Q
};

// `pipeline/objective.py fbatch`: g @ b + tab.W(g @ U.T) @ a.
static inline double Fval(const Ctx& C, const double* g) {
    double y[Q + 1];
    y[0] = 0.0;
    for (int k = 0; k < Q; k++) y[k + 1] = y[k] + g[k];
    double sb = 0.0;
    for (int r = 0; r < Q; r++) sb += g[r] * C.b[r];
    double sw = 0.0;
    for (int p = 0; p < NP; p++) sw += eval_w(*C.T, y[PJ[p]] - y[PI[p]]) * C.a[p];
    return sb + sw;
}

// `pipeline/objective.py _fgh`.  grad = (wp*a) @ U + b; H = ((wpp*a) @ UU).reshape(q,q),
// both accumulated in the PAIRS order numpy sums in.
static inline void fgh(const Ctx& C, const double* g, double& F, double* grad,
                       double* H) {
    double y[Q + 1];
    y[0] = 0.0;
    for (int k = 0; k < Q; k++) y[k + 1] = y[k] + g[k];
    double sb = 0.0;
    for (int r = 0; r < Q; r++) sb += g[r] * C.b[r];
    // diff-array accumulation (reorders the grad/H reductions vs the pairs-order sums)
    double dg[Q + 1]; for (int r = 0; r <= Q; r++) dg[r] = 0.0;
    double D[(Q + 1) * (Q + 1)]; for (int k = 0; k < (Q + 1) * (Q + 1); k++) D[k] = 0.0;
    double sw = 0.0;
    for (int p = 0; p < NP; p++) {
        double w, wp, wpp;
        eval3(*C.T, y[PJ[p]] - y[PI[p]], w, wp, wpp);
        double ap = C.a[p];
        sw += w * ap;
        double gp = wp * ap, hp = wpp * ap;
        int i = PI[p], j = PJ[p];
        dg[i] += gp; dg[j] -= gp;
        D[i * (Q + 1) + i] += hp; D[i * (Q + 1) + j] -= hp;
        D[j * (Q + 1) + i] -= hp; D[j * (Q + 1) + j] += hp;
    }
    F = sb + sw;
    double c0 = 0.0;
    for (int r = 0; r < Q; r++) { c0 += dg[r]; grad[r] = c0 + C.b[r]; }
    for (int r = 0; r <= Q; r++)
        for (int c = 0; c <= Q; c++) {
            double up = r ? D[(r - 1) * (Q + 1) + c] : 0.0;
            double lf = c ? D[r * (Q + 1) + c - 1] : 0.0;
            double di = (r && c) ? D[(r - 1) * (Q + 1) + c - 1] : 0.0;
            D[r * (Q + 1) + c] += up + lf - di;
        }
    for (int r = 0; r < Q; r++)
        for (int c = 0; c < Q; c++) H[r * Q + c] = D[r * (Q + 1) + c];
}

// LU with partial pivoting at compile-time Q.  Returns false on an exactly zero
// pivot, which is what LAPACK dgesv reports as info>0 and numpy turns into
// LinAlgError; `pipeline/objective.py newton_batch` then retries with mu + 1.
static inline bool lusolve(double A[Q][Q], const double* rhs, double* x) {
    int piv[Q];
    for (int k = 0; k < Q; k++) piv[k] = k;
    double v[Q];
    for (int k = 0; k < Q; k++) v[k] = rhs[k];
    for (int k = 0; k < Q; k++) {
        int best = k;
        double bv = std::fabs(A[k][k]);
        for (int r = k + 1; r < Q; r++) {
            double t = std::fabs(A[r][k]);
            if (t > bv) { bv = t; best = r; }
        }
        if (!(bv > 0.0)) return false;
        if (best != k) {
            for (int c = 0; c < Q; c++) std::swap(A[k][c], A[best][c]);
            std::swap(v[k], v[best]);
        }
        double d = 1.0 / A[k][k];
        const double* Ak = A[k];
        for (int r = k + 1; r < Q; r++) {
            double f = A[r][k] * d;
            A[r][k] = f;
            if (f != 0.0) {
                double* Ar = A[r];
#ifdef __ARM_NEON
                float64x2_t vf = vdupq_n_f64(f);
                int c = k + 1;
                for (; c + 2 <= Q; c += 2) {         // bit-identical: fmul then fsub, no fmla
                    float64x2_t ak = vld1q_f64(Ak + c);
                    float64x2_t ar = vld1q_f64(Ar + c);
                    vst1q_f64(Ar + c, vsubq_f64(ar, vmulq_f64(vf, ak)));
                }
                for (; c < Q; c++) Ar[c] -= f * Ak[c];
#elif defined(__AVX__)                               // x86-64: 4-wide, bit-identical
                __m256d vf = _mm256_set1_pd(f);
                int c = k + 1;
                for (; c + 4 <= Q; c += 4) {         // mul then sub, NO fmadd (matches scalar)
                    __m256d ak = _mm256_loadu_pd(Ak + c);
                    __m256d ar = _mm256_loadu_pd(Ar + c);
                    _mm256_storeu_pd(Ar + c, _mm256_sub_pd(ar, _mm256_mul_pd(vf, ak)));
                }
                for (; c < Q; c++) Ar[c] -= f * Ak[c];
#else                                                // scalar fallback: identical arithmetic
                for (int c = k + 1; c < Q; c++) Ar[c] -= f * Ak[c];
#endif
            }
            v[r] -= f * v[k];
        }
    }
    for (int k = Q - 1; k >= 0; k--) {
        double s = v[k];
        for (int c = k + 1; c < Q; c++) s -= A[k][c] * x[c];
        x[k] = s / A[k][k];
    }
    return true;
}

struct alignas(64) Stats {
    uint64_t singular = 0;       // exactly-zero pivots -> mu+1 retry
    uint64_t retired = 0;        // rows dropped by the fixed-point test
    uint64_t saved_iters = 0;    // row-iterations retirement skipped
    uint64_t memo_hits = 0;      // fgh sweeps skipped after a rejected step
    uint64_t iters_run = 0;      // row-iterations actually executed
};

// `pipeline/objective.py newton_batch` for ONE row.  g is in/out and is clamped on entry by
// the caller, matching `np.maximum(g0, 0.0)`.
static inline double newton_row(const Ctx& C, double* g, int iters, bool retire,
                                Stats& st) {
    double mu = MU0;
    double F = (iters > 0) ? 0.0 : Fval(C, g);   // initial value is dead when the loop runs (overwritten before read)
    double grad[Q], H[Q * Q], A[Q][Q], dx[Q], gt[Q];
    double Fc = 0.0;
    bool cached = false;                    // g unchanged since Fc/grad/H were built
    for (int it = 0; it < iters; it++) {
        st.iters_run++;
        if (cached && retire) st.memo_hits++;
        else fgh(C, g, Fc, grad, H);
        for (int r = 0; r < Q; r++)
            for (int c = 0; c < Q; c++) A[r][c] = H[r * Q + c] + (r == c ? mu : 0.0);
        if (!lusolve(A, grad, dx)) {
            // Exactly-singular H + mu*I: bump THIS row's mu by 1 and retry, then
            // dx=0 if still singular.  `pipeline/objective.py newton_batch` instead bumps the
            // whole batched chunk (np.linalg.solve throws for the batch, so its
            // except-clause re-solves every sibling row with mu+1 that iteration).
            // The two therefore diverge on the measure-zero exactly-singular set,
            // and only on the OTHER rows of a numpy chunk; the per-row bump here is
            // the sounder choice (it never perturbs a healthy neighbor) and this
            // path is search-side (a minimizer start), never a certificate.
            st.singular++;
            for (int r = 0; r < Q; r++)
                for (int c = 0; c < Q; c++)
                    A[r][c] = H[r * Q + c] + (r == c ? (mu + 1.0) : 0.0);
            if (!lusolve(A, grad, dx))
                for (int r = 0; r < Q; r++) dx[r] = 0.0;
        }
        bool zerodx = true;
        for (int r = 0; r < Q; r++) {
            gt[r] = g[r] - dx[r];
            if (gt[r] < 0.0) gt[r] = 0.0;
            if (dx[r] != 0.0) zerodx = false;
        }
        double Ft = Fval(C, gt);
        if (Ft < Fc - ACC_TOL) {
            for (int r = 0; r < Q; r++) g[r] = gt[r];
            F = Ft;
            mu = mu * MU_DN;
            if (mu < MU_LO) mu = MU_LO;
            cached = false;
        } else {
            F = Fc;
            cached = true;                          // g is unchanged: (c) in the header
            bool fixed = (mu >= MU_HI) || zerodx;   // proven fixed points, see header
            mu = mu * MU_UP;
            if (mu > MU_HI) mu = MU_HI;
            if (retire && fixed) {
                st.retired++;
                st.saved_iters += (uint64_t)(iters - it - 1);
                return F;
            }
        }
    }
    return F;
}

// ------------------------------------------------------------------- threading
struct Job {
    double* g;          // n x Q, in/out
    double* F;          // n
    int n;
    int iters;
    const Ctx* C;
    bool retire;
    int block;
    std::atomic<int> next{0};
};

static void worker(Job* J, Stats* st) {
    for (;;) {
        int lo = J->next.fetch_add(J->block, std::memory_order_relaxed);
        if (lo >= J->n) return;
        int hi = std::min(lo + J->block, J->n);
        for (int r = lo; r < hi; r++)
            J->F[r] = newton_row(*J->C, J->g + (size_t)r * Q, J->iters, J->retire, *st);
    }
}

static void run_newton(double* g, double* F, int n, int iters, const Ctx& C,
                       bool retire, int nth, int block, Stats& out) {
    Job J;
    J.g = g; J.F = F; J.n = n; J.iters = iters; J.C = &C;
    J.retire = retire; J.block = block;
    auto add = [&out](const Stats& s) {
        out.singular += s.singular; out.retired += s.retired;
        out.saved_iters += s.saved_iters; out.memo_hits += s.memo_hits;
        out.iters_run += s.iters_run;
    };
    if (nth <= 1) { Stats s; worker(&J, &s); add(s); return; }
    std::vector<Stats> ss(nth);
    std::vector<std::thread> th;
    th.reserve(nth);
    for (int t = 0; t < nth; t++) th.emplace_back(worker, &J, &ss[t]);
    for (auto& x : th) x.join();
    for (auto& s : ss) add(s);
}

// ----------------------------------------------------------------------- I/O
static void die(const char* m) { std::fprintf(stderr, "s155: %s\n", m); std::exit(2); }

struct Map {
    const void* p = nullptr;
    size_t len = 0;
    const double* d() const { return (const double*)p; }
    size_t n() const { return len / 8; }
};

static Map map_file(const std::string& path) {
    int fd = open(path.c_str(), O_RDONLY);
    if (fd < 0) { std::fprintf(stderr, "s155: cannot open %s\n", path.c_str()); std::exit(2); }
    struct stat sb;
    if (fstat(fd, &sb) != 0) die("fstat");
    Map m;
    m.len = (size_t)sb.st_size;
    m.p = mmap(nullptr, m.len, PROT_READ, MAP_SHARED, fd, 0);
    if (m.p == MAP_FAILED) die("mmap");
    close(fd);
    return m;
}

struct Spec {
    int q = 0, np = 0, ntempl = 0, iters1 = 0, iters2 = 0, keep_stage1 = 0;
    int symdup = 0;
    int gen_half = 0;
    double ymax = 0, hmax = 0, inv_h = 0;
    Map coef, brk, starts;
};

static bool rd_all(const std::string& p, std::string& out) {
    FILE* f = fopen(p.c_str(), "rb");
    if (!f) return false;
    char buf[4096];
    size_t k;
    out.clear();
    while ((k = fread(buf, 1, sizeof buf, f)) > 0) out.append(buf, k);
    fclose(f);
    return true;
}

static Spec load(const std::string& dir) {
    std::string txt;
    if (!rd_all(dir + "/spec.txt", txt)) die("cannot read spec.txt");
    Spec S;
    size_t pos = 0;
    while (pos < txt.size()) {
        size_t e = txt.find('\n', pos);
        if (e == std::string::npos) e = txt.size();
        std::string line = txt.substr(pos, e - pos);
        pos = e + 1;
        size_t sp = line.find(' ');
        if (sp == std::string::npos) continue;
        std::string k = line.substr(0, sp), v = line.substr(sp + 1);
        if (k == "q") S.q = atoi(v.c_str());
        else if (k == "np") S.np = atoi(v.c_str());
        else if (k == "ntempl") S.ntempl = atoi(v.c_str());
        else if (k == "iters1") S.iters1 = atoi(v.c_str());
        else if (k == "iters2") S.iters2 = atoi(v.c_str());
        else if (k == "keep_stage1") S.keep_stage1 = atoi(v.c_str());
        else if (k == "symdup") S.symdup = atoi(v.c_str());
        else if (k == "gen_half") S.gen_half = atoi(v.c_str());
        else if (k == "ymax") S.ymax = strtod(v.c_str(), nullptr);
        else if (k == "hmax") S.hmax = strtod(v.c_str(), nullptr);
        else if (k == "inv_h") S.inv_h = strtod(v.c_str(), nullptr);
    }
    if (S.q != Q) { std::fprintf(stderr, "s155: spec q=%d, binary Q=%d\n", S.q, Q); std::exit(2); }
    if (S.np != NP) die("np mismatch");
    S.coef = map_file(dir + "/coef.bin");
    S.brk = map_file(dir + "/breaks.bin");
    if (!S.gen_half) {
        S.starts = map_file(dir + "/starts.bin");
        if (S.starts.n() != (size_t)S.ntempl * Q) die("starts size mismatch");
    }
    if (S.coef.n() != 12 * (S.brk.n() - 1)) die("coef/breaks size mismatch");
    return S;
}

static bool rdx(void* p, size_t n) {
    size_t got = 0;
    while (got < n) {
        ssize_t k = read(STDIN_FILENO, (char*)p + got, n - got);
        if (k <= 0) return false;
        got += (size_t)k;
    }
    return true;
}

static void wrx(const void* p, size_t n) {
    size_t put = 0;
    while (put < n) {
        ssize_t k = write(STDOUT_FILENO, (const char*)p + put, n - put);
        if (k <= 0) die("short write");
        put += (size_t)k;
    }
}


// ------------------------------------------------------------ generated half-templates
static int64_t POW5Q = 1;
// Row of base-5 code c (most significant digit first, digit d -> value d + 1); false when the
// row holds both a 4 and a 5 or is not canonical (r <= reverse(r)).
static inline bool tmpl_row(int64_t c, double* g) {
    int d[Q];
    bool has4 = false, has5 = false;
    for (int k = Q - 1; k >= 0; k--) { d[k] = (int)(c % 5); c /= 5; has4 |= d[k] == 3; has5 |= d[k] == 4; }
    if (has4 && has5) return false;
    for (int k = 0; k < Q / 2 + 1 && k < Q; k++) {
        int m = Q - 1 - k;
        if (d[k] < d[m]) break;
        if (d[k] > d[m]) return false;
    }
    for (int k = 0; k < Q; k++) g[k] = (double)(d[k] + 1);
    return true;
}

typedef std::pair<double, int64_t> Key;   // (F with +inf for non-finite, code)

struct Heap {                              // bounded max-heap of the k smallest keys
    size_t k; std::vector<Key> v;
    explicit Heap(size_t k_) : k(k_) { v.reserve(k_ + 1); }
    void push(const Key& x) {
        if (v.size() < k) { v.push_back(x); std::push_heap(v.begin(), v.end()); }
        else if (k && x < v.front()) { std::pop_heap(v.begin(), v.end()); v.back() = x; std::push_heap(v.begin(), v.end()); }
    }
};

// Stage 1 (iters > 0: Newton; iters == 0: F at the start) over every generated half-template
// and the nrand random starts in R; returns the keep smallest (F, code), sorted.
static std::vector<Key> stream_select(const Ctx& C, int iters, bool retire, int nth, size_t keep,
                                      const double* R, int nrand, Stats& out, uint64_t& nrows) {
    std::atomic<int64_t> next{0};
    const int64_t BLK = 4096, total = POW5Q + nrand;
    std::vector<Heap> hs(nth, Heap(keep));
    std::vector<Stats> ss(nth);
    std::vector<uint64_t> cnt(nth, 0);
    auto work = [&](int t) {
        double g[Q];
        for (;;) {
            int64_t lo = next.fetch_add(BLK, std::memory_order_relaxed);
            if (lo >= total) return;
            int64_t hi = std::min(lo + BLK, total);
            for (int64_t c = lo; c < hi; c++) {
                if (c < POW5Q) { if (!tmpl_row(c, g)) continue; }
                else { for (int k = 0; k < Q; k++) { double x = R[(c - POW5Q) * Q + k]; g[k] = x < 0.0 ? 0.0 : x; } }
                double F = iters > 0 ? newton_row(C, g, iters, retire, ss[t]) : Fval(C, g);
                hs[t].push({std::isfinite(F) ? F : INFINITY, c});
                cnt[t]++;
            }
        }
    };
    std::vector<std::thread> th;
    for (int t = 0; t < nth; t++) th.emplace_back(work, t);
    for (auto& x : th) x.join();
    std::vector<Key> all;
    nrows = 0;
    for (int t = 0; t < nth; t++) {
        all.insert(all.end(), hs[t].v.begin(), hs[t].v.end());
        out.singular += ss[t].singular; out.retired += ss[t].retired; out.saved_iters += ss[t].saved_iters;
        out.memo_hits += ss[t].memo_hits; out.iters_run += ss[t].iters_run; nrows += cnt[t];
    }
    std::sort(all.begin(), all.end());
    if (all.size() > keep) all.resize(keep);
    return all;
}

static void start_of(int64_t c, const double* R, double* g) {
    if (c < POW5Q) { tmpl_row(c, g); return; }
    for (int k = 0; k < Q; k++) { double x = R[(c - POW5Q) * Q + k]; g[k] = x < 0.0 ? 0.0 : x; }
}

#include "lp.inc"
static const int32_t MAGIC_LPI = 0x53314c49;  // 'S1LI', set up the cut-model LP (constraints, mode)
static const int32_t MAGIC_LPR = 0x53314c52;  // 'S1LR', append cut rows and run model_ratio
static const int32_t MAGIC_LPS = 0x53314c53;  // 'S1LS', LP counters (count, simplex iterations, seconds)
static const int32_t MAGIC_PRE = 0x53315052;  // 'S1PR', prescreen over the generated templates

static const int32_t MAGIC = 0x53313535;   // 'S155', the gmin two-stage request
static const int32_t MAGIC_DESC = 0x53315344; // 'S1SD', a single-pass descend

int main(int argc, char** argv) {
    build_pairs();
    for (int k = 0; k < Q; k++) POW5Q *= 5;
    if (argc < 3) {
        std::fprintf(stderr,
            "usage: gmin serve|bench <specdir> [threads] [--noretire]\n"
            "       gmin evaltab <specdir> <x.bin> <out.bin>\n");
        return 2;
    }
    std::string mode = argv[1], dir = argv[2];
    Spec S = load(dir);

    Tab T;
    T.rec = S.coef.d();
    T.brk = S.brk.d();
    T.nbrk = (int64_t)S.brk.n();
    T.m = T.nbrk - 2;
    T.inv_h = S.inv_h;
    T.hmax = S.hmax;
    T.ymax = S.ymax;

    if (mode == "evaltab") {
        if (argc < 5) die("evaltab needs <x.bin> <out.bin>");
        Map X = map_file(argv[3]);
        size_t n = X.n();
        std::vector<double> out(3 * n);
        for (size_t k = 0; k < n; k++) {
            double w, wp, wpp;
            eval3(T, X.d()[k], w, wp, wpp);
            out[k] = w; out[n + k] = wp; out[2 * n + k] = wpp;
        }
        // W() takes |x| first and only checks the upper bound, so it is a
        // separate call, appended.
        std::vector<double> wonly(n);
        for (size_t k = 0; k < n; k++) wonly[k] = eval_w(T, std::fabs(X.d()[k]));
        FILE* f = fopen(argv[4], "wb");
        if (!f) die("cannot open out.bin");
        fwrite(out.data(), 8, out.size(), f);
        fwrite(wonly.data(), 8, wonly.size(), f);
        fclose(f);
        return 0;
    }

    int nth = argc > 3 ? atoi(argv[3]) : 1;
    if (nth < 1) nth = 1;
    bool retire = true;
    for (int i = 3; i < argc; i++)
        if (std::string(argv[i]) == "--noretire") retire = false;

    const int nt = S.ntempl;
    std::vector<double> g;
    std::vector<double> F;
    std::vector<double> a(NP), b(Q);
    Ctx C{&T, a.data(), b.data()};

    // (key, index) pairs for the deterministic keep_stage1 selection.
    std::vector<std::pair<double, int>> ord;

    std::fprintf(stderr, "s155 q=%d np=%d ntempl=%d knots=%lld threads=%d retire=%d\n",
                 Q, NP, nt, (long long)T.nbrk, nth, (int)retire);
    std::fflush(stderr);

    LPModel LPM;
    uint64_t reqs = 0;
    Stats total;
    uint64_t bties = 0;

    for (;;) {
        int32_t hdr[2];
        if (!rdx(hdr, 8)) break;

        // DESCEND: one newton pass at `iters` over an EXPLICIT block of starts,
        // keep the top `keep_total`.  Mirrors `pipeline/parmin.py ParMin.descend` (used by
        // an adversary driver): no templates from the spec, no symdup, no
        // keep_stage1/iters2 second pass.  A candidate generator only -- every
        // value it returns is re-checked with Fexact by the adversary.
        if (hdr[0] == MAGIC_DESC) {
            int nds = hdr[1];                    // hdr = (MAGIC_DESC, nstarts)
            int32_t dh[2];
            if (!rdx(dh, 8)) die("short descend header");
            int iters = dh[0], keep_total = dh[1];
            if (nds < 0 || iters < 0 || keep_total < 0) die("bad descend request");
            if (!rdx(b.data(), 8 * Q)) die("short descend (b)");
            if (!rdx(a.data(), 8 * (size_t)NP)) die("short descend (a)");
            g.resize((size_t)nds * Q);
            F.resize(nds);
            if (nds && !rdx(g.data(), 8 * (size_t)nds * Q))
                die("short descend (starts)");
            for (size_t k = 0; k < g.size(); k++) if (g[k] < 0.0) g[k] = 0.0;
            Stats std_;
            run_newton(g.data(), F.data(), nds, iters, C, retire, nth, 512, std_);
            int nk = std::min(nds, keep_total);
            if (nds > keep_total) {
                ord.resize(nds);
                for (int r = 0; r < nds; r++)
                    ord[r] = {std::isfinite(F[r]) ? F[r] : INFINITY, r};
                std::partial_sort(ord.begin(), ord.begin() + nk, ord.end());
                if (nk < nds && ord[nk - 1].first == ord[nk].first) bties++;
                std::vector<double> sel((size_t)nk * Q), fs(nk);
                for (int r = 0; r < nk; r++) {
                    fs[r] = ord[r].first;      // descend has no 2nd pass: F must
                    std::memcpy(sel.data() + (size_t)r * Q,  // follow the sort
                                g.data() + (size_t)ord[r].second * Q, 8 * Q);
                }
                g.swap(sel);
                F.swap(fs);
            } else {                       // keep all, sorted ascending by (F, idx)
                ord.resize(nds);
                for (int r = 0; r < nds; r++)
                    ord[r] = {std::isfinite(F[r]) ? F[r] : INFINITY, r};
                std::sort(ord.begin(), ord.end());
                std::vector<double> sel((size_t)nk * Q), fs(nk);
                for (int r = 0; r < nk; r++) {
                    fs[r] = ord[r].first;
                    std::memcpy(sel.data() + (size_t)r * Q,
                                g.data() + (size_t)ord[r].second * Q, 8 * Q);
                }
                g.swap(sel);
                F.swap(fs);
            }
            total.singular += std_.singular; total.retired += std_.retired;
            total.saved_iters += std_.saved_iters;
            total.memo_hits += std_.memo_hits; total.iters_run += std_.iters_run;
            reqs++;
            int32_t out = nk;
            wrx(&out, 4);
            wrx(F.data(), 8 * (size_t)nk);
            wrx(g.data(), 8 * (size_t)nk * Q);
            continue;
        }

        if (hdr[0] == MAGIC_PRE) {
            if (!S.gen_half) die("prescreen needs gen_half");
            int kk = hdr[1];
            if (!rdx(b.data(), 8 * Q)) die("short prescreen (b)");
            if (!rdx(a.data(), 8 * (size_t)NP)) die("short prescreen (a)");
            Stats sp; uint64_t nr = 0;
            std::vector<Key> sel = stream_select(C, 0, retire, nth, (size_t)std::max(kk, 0), nullptr, 0, sp, nr);
            int32_t out = (int32_t)sel.size();
            std::vector<double> fs(out), gs((size_t)out * Q);
            for (int r = 0; r < out; r++) { fs[r] = sel[r].first; start_of(sel[r].second, nullptr, gs.data() + (size_t)r * Q); }
            wrx(&out, 4);
            wrx(fs.data(), 8 * (size_t)out);
            wrx(gs.data(), 8 * (size_t)out * Q);
            reqs++;
            continue;
        }
        if (hdr[0] == MAGIC_LPI) {
            // (MAGIC_LPI, nv) neq mode nhs | hs_ratio | Aeq[neq*nv] beq[neq] lb[nv] ub[nv] | hs_cols[nhs]
            int32_t h3[3];
            if (!rdx(h3, 12)) die("short lp init");
            LPM.nv = hdr[1]; LPM.neq = h3[0]; LPM.mode = h3[1];
            int nhs = h3[2];
            if (!rdx(&LPM.hs_ratio, 8)) die("short lp init");
            LPM.Aeq.resize((size_t)LPM.neq * LPM.nv); LPM.beq.resize(LPM.neq);
            LPM.lb.resize(LPM.nv); LPM.ub.resize(LPM.nv);
            std::vector<int32_t> hc(nhs);
            if (!rdx(LPM.Aeq.data(), 8 * LPM.Aeq.size()) || !rdx(LPM.beq.data(), 8 * LPM.beq.size()) ||
                !rdx(LPM.lb.data(), 8 * LPM.lb.size()) || !rdx(LPM.ub.data(), 8 * LPM.ub.size()) ||
                (nhs && !rdx(hc.data(), 4 * (size_t)nhs))) die("short lp init");
            LPM.hs_cols.assign(hc.begin(), hc.end());
            LPM.has_hs = nhs > 0;
            LPM.rows.clear(); LPM.nrows = 0; LPM.warm_rows = 0;
            LPM.nlp = LPM.iters = 0; LPM.secs = 0.0;
            delete LPM.warm;
            LPM.warm = LPM.mode == 1 ? new Highs() : nullptr;
            int32_t out = 0;
            wrx(&out, 4);
            continue;
        }
        if (hdr[0] == MAGIC_LPR) {
            // (MAGIC_LPR, nnew) steps | H kappa0 | rows[nnew*nv]  ->  found | kappa | x[nv]
            int nn = hdr[1];
            int32_t steps;
            double hk[2];
            if (nn < 0 || !rdx(&steps, 4) || !rdx(hk, 16)) die("short lp request");
            LPM.rows.resize((size_t)(LPM.nrows + nn) * LPM.nv);
            if (nn && !rdx(LPM.rows.data() + (size_t)LPM.nrows * LPM.nv, 8 * (size_t)nn * LPM.nv))
                die("short lp rows");
            LPM.nrows += nn;
            std::vector<double> x(LPM.nv, 0.0);
            double kappa;
            int32_t found = lp_ratio(LPM, hk[0], hk[1], steps, kappa, x.data()) ? 1 : 0;
            wrx(&found, 4);
            wrx(&kappa, 8);
            wrx(x.data(), 8 * (size_t)LPM.nv);
            continue;
        }
        if (hdr[0] == MAGIC_LPS) {
            double st[3] = {(double)LPM.nlp, (double)LPM.iters, LPM.secs};
            wrx(st, 24);
            continue;
        }
        if (hdr[0] != MAGIC) break;
        int nrand = hdr[1];
        if (nrand < 0) break;
        if (!rdx(b.data(), 8 * Q)) die("short request (b)");
        if (!rdx(a.data(), 8 * (size_t)NP)) die("short request (a)");
        if (S.gen_half) {
            std::vector<double> R((size_t)nrand * Q);
            if (nrand && !rdx(R.data(), 8 * (size_t)nrand * Q)) die("short request (starts)");
            Stats st1, st2; uint64_t nr = 0;
            std::vector<Key> sel = stream_select(C, S.iters1, retire, nth, (size_t)S.keep_stage1,
                                                 R.data(), nrand, st1, nr);
            int nk = (int)sel.size();
            // regenerate the survivors' starts and rerun their stage-1 Newton (deterministic per row),
            // so stage 2 continues from the identical stage-1 end points
            g.assign((size_t)nk * Q, 0.0);
            F.assign(nk, 0.0);
            for (int r = 0; r < nk; r++) start_of(sel[r].second, R.data(), g.data() + (size_t)r * Q);
            Stats st1b;
            run_newton(g.data(), F.data(), nk, S.iters1, C, retire, nth, 8, st1b);
            if (S.symdup) {
                g.resize((size_t)2 * nk * Q);
                for (int r = 0; r < nk; r++)
                    for (int c = 0; c < Q; c++) g[(size_t)(nk + r) * Q + c] = g[(size_t)r * Q + Q - 1 - c];
                nk *= 2;
                F.resize(nk);
            }
            run_newton(g.data(), F.data(), nk, S.iters2, C, retire, nth, 8, st2);
            total.singular += st1.singular + st2.singular;
            total.iters_run += st1.iters_run + st2.iters_run;
            reqs++;
            std::fprintf(stderr, "s155s req %llu rows %llu kept %d\n", (unsigned long long)reqs,
                         (unsigned long long)nr, nk);
            int32_t out = nk;
            wrx(&out, 4);
            wrx(F.data(), 8 * (size_t)nk);
            wrx(g.data(), 8 * (size_t)nk * Q);
            continue;
        }
        int n = nt + nrand;
        g.resize((size_t)n * Q);
        F.resize(n);
        std::memcpy(g.data(), S.starts.d(), 8 * (size_t)nt * Q);
        if (nrand && !rdx(g.data() + (size_t)nt * Q, 8 * (size_t)nrand * Q))
            die("short request (starts)");
        for (size_t k = 0; k < g.size(); k++) if (g[k] < 0.0) g[k] = 0.0;

        Stats st1, st2;
        run_newton(g.data(), F.data(), n, S.iters1, C, retire, nth, 512, st1);

        int nk = std::min(n, S.keep_stage1);
        if (n > S.keep_stage1) {
            ord.resize(n);
            for (int r = 0; r < n; r++)
                ord[r] = {std::isfinite(F[r]) ? F[r] : INFINITY, r};
            std::partial_sort(ord.begin(), ord.begin() + nk, ord.end());
            if (nk < n && ord[nk - 1].first == ord[nk].first) bties++;
            std::vector<double> sel((size_t)nk * Q);
            for (int r = 0; r < nk; r++)
                std::memcpy(sel.data() + (size_t)r * Q,
                            g.data() + (size_t)ord[r].second * Q, 8 * Q);
            g.swap(sel);
            F.resize(nk);
        }
        // `pipeline/parmin.py ParMin.gmin` carries every survivor's REVERSAL into stage 2
        // as well: F(g) = F(reverse g) whenever (a, b) are palindromic, so
        // it costs a row and cannot lose a basin.  `symdup 1` in the spec
        // reproduces that; the s152 scoring path leaves it 0.
        if (S.symdup) {
            g.resize((size_t)2 * nk * Q);
            for (int r = 0; r < nk; r++) {
                const double* src = g.data() + (size_t)r * Q;
                double* dst = g.data() + (size_t)(nk + r) * Q;
                for (int c = 0; c < Q; c++) dst[c] = src[Q - 1 - c];
            }
            nk *= 2;
            F.resize(nk);
        }
        run_newton(g.data(), F.data(), nk, S.iters2, C, retire, nth, 8, st2);

        total.singular += st1.singular + st2.singular;
        total.retired += st1.retired + st2.retired;
        total.saved_iters += st1.saved_iters + st2.saved_iters;
        total.memo_hits += st1.memo_hits + st2.memo_hits;
        total.iters_run += st1.iters_run + st2.iters_run;
        reqs++;

        if (mode == "serve") {
            int32_t out = nk;
            wrx(&out, 4);
            wrx(F.data(), 8 * (size_t)nk);
            wrx(g.data(), 8 * (size_t)nk * Q);
        } else {
            double best = INFINITY;
            for (int r = 0; r < nk; r++) if (F[r] < best) best = F[r];
            std::fprintf(stderr, "rep %llu fmin %.17g\n",
                         (unsigned long long)reqs, best);
        }
    }

    struct rusage ru;
    getrusage(RUSAGE_SELF, &ru);
    std::fprintf(stderr,
        "s155 done reqs=%llu singular=%llu retired=%llu saved_row_iters=%llu "
        "iters_run=%llu memo_hits=%llu boundary_ties=%llu maxrss_mb=%.1f\n",
        (unsigned long long)reqs, (unsigned long long)total.singular,
        (unsigned long long)total.retired, (unsigned long long)total.saved_iters,
        (unsigned long long)total.iters_run, (unsigned long long)total.memo_hits,
        (unsigned long long)bties,
#ifdef __APPLE__
        ru.ru_maxrss / 1048576.0);
#else
        ru.ru_maxrss / 1024.0);
#endif
    std::fflush(stderr);
    return 0;
}
