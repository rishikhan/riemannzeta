// Threaded C++ knot evaluation for the W-table build.
//
// WHAT THIS IS.  `pipeline/kernel.py`'s `kernel_exact` `Wall`, evaluated at the 1,360,001
// knots of the spline grid.  the knot evaluation dominated the table build once the minimizer moved to C++,
// as the bottleneck left after the gmin port: 3.04 s of a 6.4 s evaluation,
// single-threaded numpy, against 2.72 s for the whole ported gmin at 12 threads.
//
// WHAT IT IS NOT.  The scipy `CubicSpline` FIT stays in Python, untouched.  This
// file produces the three knot ARRAYS and hands them straight to the same three
// `interpolate.CubicSpline(gy, ...)` calls `pipeline/wtable.py` WTable.__init__
// already makes, so the claim that the spline coefficients are ingested from
// the same CubicSpline build, never re-derived in C++ -- holds by construction.
//
// WHY IT IS WORTH PORTING, MEASURED.  Of the 1.97 s the chunked numpy `Wall`
// costs on this window, `np.sin` and `np.cos` are 0.170 s (8.6%).  The other
// 91% is `_sinc3`'s divisions, powers and `np.where` masks, evaluated through
// about ten (chunk, 17) temporaries.  Fusing the whole per-(point, frequency)
// expression into registers deletes all of it.
//
// IT IS BIT-IDENTICAL TO NUMPY, on all 1,360,001 knots of both the record
// window and a non-sqrt(2)-carrier window -- W, W' and W'' alike.  That was not
// free, and the one thing that nearly cost it is recorded under the sin/cos
// entry below.  Every floating-point choice here is matched to numpy exactly
// and was verified, not assumed:
//
//   * `-ffp-contract=off`, as everywhere else in this repo, so no expression is
//     re-associated into an FMA.
//   * sin and cos are called through VOLATILE FUNCTION POINTERS, and that is
//     load-bearing, not defensive.  Written as adjacent `std::sin(zs)` and
//     `std::cos(zs)` calls, clang merges them into Darwin's `__sincos_stret`,
//     which does NOT round like `sin` and `cos` called separately: it disagreed
//     with numpy on 6,161 of the 46,240,034 arguments this grid produces, and
//     that single substitution was the entire deviation.  numpy calls np.sin
//     and np.cos as two separate library calls, so this file must too.  No
//     compiler flag suppresses the merge (`-fno-builtin-sincos` leaves
//     `___sincos_stret` in the import table); an indirect call through a
//     volatile pointer does, because LLVM cannot pattern-match a callee it
//     cannot name.  The volatile pointers are read ONCE per `knots_wall` call
//     and passed down as ordinary parameters: reading them per sinc3 call cost
//     70% of the single-thread runtime (0.65 s -> 1.11 s) for no extra safety,
//     since the compiler still cannot name the callee either way.
//   * `x**2` IS `x*x` in numpy; `x**3` IS NOT `x*x*x` -- numpy's float64 power
//     loop fast-cases exponents 2, 1, 0, 0.5 and -1 and sends 3 to libm `pow`.
//     So `zs**3` and `t2**3` are `std::pow(., 3.0)` here.  Nothing in the build
//     may turn those back into multiplications: no `-ffast-math`, and LLVM only
//     rewrites `pow(x, 3)` under `afn`, which is not set.
//   * `(coeff * (lv+rv) / 2).sum(-1)` reduces 17 CONTIGUOUS elements, and
//     numpy's pairwise reduction at that length is the 8-accumulator form
//     reproduced in `psum17` below -- checked bit-for-bit against `.sum(-1)`
//     on 50,000 random rows, max deviation 0.000e+00.  A plain sequential sum
//     does NOT match.
//   * `coeff * np.pi` and `coeff * np.pi**2` are single rounded arrays in numpy,
//     broadcast against the per-point factor.  They are therefore passed IN,
//     precomputed by Python, rather than recomputed here -- as are `k0` and
//     `k0**2`.  `(coeff[j]*pi)*(rd-ld)` is not `coeff[j]*(pi*(rd-ld))`.
//   * The expression association inside `_sinc3` is Python's, left to right:
//     `1 - t2/6 + t2*t2/120 - t2**3/5040` is `((1 - t2/6) + (t2*t2)/120) -
//     pow(t2,3)/5040`, and so on for d1 and d2.
//   * numpy evaluates the non-small branch on every element with
//     `zs = where(small, 1.0, z)` and then overwrites the small ones.  The
//     branch here is equivalent: it can only skip work whose result is
//     discarded.
//
// DIRECTION OF ERROR.  This table is an interpolant used only by the FLOAT
// search objective, which is a RANKING proxy whose own rankings invert at
// ~5e-08 (`new/04-traps.md` 8).  It is not part of any certificate: certificate
// tables are the outward-rounded interval ones from `pipeline/tables.py`, and
// the certificate itself comes from `pipeline/cpp/verify.cpp`.  Neither is
// touched.
// Because the knot arrays are bit-identical, this file does not create a new
// scoring engine and cannot move a rescore value -- see
// the port notes.
//
// Driven from `pipeline/cppgmin.py` through ctypes: numpy array pointers are
// passed straight in, so there is no spec file, no subprocess and no copy.
//
// Build:
//   clang++ -std=c++17 -O3 -DNDEBUG -ffp-contract=off -mcpu=native \
//           -shared -fPIC -o libknots.dylib pipeline/cpp/knots.cpp
#include <atomic>
#include <cmath>
#include <math.h>
#include <cstdint>
#include <thread>
#include <vector>

#define NFMAX 64

// See the sin/cos note in the header.  `volatile` is what stops clang folding
// the pair into `__sincos_stret`; without it the knot arrays stop being
// bit-identical to numpy's.  pipeline/tests/test_cppgmin.py fails if that regresses.
typedef double (*real_fn)(double);
static real_fn volatile LIBM_SIN = ::sin;
static real_fn volatile LIBM_COS = ::cos;

// numpy's pairwise reduction for a contiguous run of n <= 128 elements:
// eight accumulators seeded from the first eight, strided by eight, folded as
// ((r0+r1)+(r2+r3)) + ((r4+r5)+(r6+r7)), then the tail added sequentially.
static inline double psum17(const double* a, int n) {
    if (n < 8) {
        double s = 0.0;
        for (int i = 0; i < n; i++) s += a[i];
        return s;
    }
    double r[8];
    for (int j = 0; j < 8; j++) r[j] = a[j];
    int i = 8;
    for (; i < n - (n % 8); i += 8)
        for (int j = 0; j < 8; j++) r[j] += a[i + j];
    double res = ((r[0] + r[1]) + (r[2] + r[3])) + ((r[4] + r[5]) + (r[6] + r[7]));
    for (; i < n; i++) res += a[i];
    return res;
}

// pipeline/kernel.py sinc3 for one argument.
static inline void sinc3(double z, real_fn sinf, real_fn cosf,
                         double& v, double& d1, double& d2) {
    if (std::fabs(z) < 1e-3) {
        const double t = z, t2 = t * t;
        v  = 1.0 - t2 / 6.0 + t2 * t2 / 120.0 - std::pow(t2, 3.0) / 5040.0;
        d1 = -t / 3.0 + t * t2 / 30.0 - t * t2 * t2 / 840.0;
        d2 = -1.0 / 3.0 + t2 / 10.0 - t2 * t2 / 168.0;
    } else {
        const double zs = z;
        const double s = sinf(zs), c = cosf(zs);
        v  = s / zs;
        d1 = (zs * c - s) / (zs * zs);
        d2 = ((2.0 - zs * zs) * s - 2.0 * zs * c) / std::pow(zs, 3.0);
    }
}

// pipeline/kernel.py kernel_exact Wall at one point.
static inline void wall_one(double x, const double* h, const double* cf,
                            const double* cfpi, const double* cfpi2, int nf,
                            double k0, double k02, real_fn sinf, real_fn cosf,
                            double& w, double& wp, double& wpp) {
    // np.sign: +1, -1, and exactly 0.0 at 0.0 -- so W' is 0.0 at the first knot.
    const double sg = (x > 0.0) ? 1.0 : ((x < 0.0) ? -1.0 : 0.0);
    const double ax = std::fabs(x);
    const double px = M_PI * ax;
    double tk[NFMAX], tp[NFMAX], tpp[NFMAX];
    for (int j = 0; j < nf; j++) {
        double lv, ld, ldd, rv, rd, rdd;
        sinc3(h[j] - px, sinf, cosf, lv, ld, ldd);
        sinc3(h[j] + px, sinf, cosf, rv, rd, rdd);
        tk[j]  = cf[j]    * (lv + rv)   / 2.0;
        tp[j]  = cfpi[j]  * (rd - ld)   / 2.0;
        tpp[j] = cfpi2[j] * (ldd + rdd) / 2.0;
    }
    const double k   = psum17(tk, nf);
    const double kp  = psum17(tp, nf);
    const double kpp = psum17(tpp, nf);
    const double q = k / k0;
    w   = q * q;                                    // (k/k0)**2, and **2 is x*x
    wp  = (2.0 * k * kp / k02) * sg;                // 2*k*kp/k0**2, then * sg
    wpp = 2.0 * (kp * kp + k * kpp) / k02;
}

extern "C" {

// Threaded evaluation over x[0..n).  Each output element depends only on its own
// input, so the result is independent of `threads` and of the block schedule.
void knots_wall(const double* x, int64_t n,
               const double* h, const double* cf, const double* cfpi,
               const double* cfpi2, int nf, double k0, double k02,
               double* w, double* wp, double* wpp, int threads) {
    if (nf > NFMAX) nf = NFMAX;           // caller checks; clamp anyway
    if (threads < 1) threads = 1;
    const real_fn sinf = LIBM_SIN, cosf = LIBM_COS;   // one volatile read per call
    if (threads == 1 || n < 4096) {
        for (int64_t i = 0; i < n; i++)
            wall_one(x[i], h, cf, cfpi, cfpi2, nf, k0, k02, sinf, cosf,
                     w[i], wp[i], wpp[i]);
        return;
    }
    std::atomic<int64_t> next{0};
    const int64_t block = 8192;
    auto work = [&]() {
        for (;;) {
            int64_t lo = next.fetch_add(block, std::memory_order_relaxed);
            if (lo >= n) return;
            int64_t hi = lo + block < n ? lo + block : n;
            for (int64_t i = lo; i < hi; i++)
                wall_one(x[i], h, cf, cfpi, cfpi2, nf, k0, k02, sinf, cosf,
                         w[i], wp[i], wpp[i]);
        }
    };
    std::vector<std::thread> th;
    th.reserve(threads);
    for (int t = 0; t < threads; t++) th.emplace_back(work);
    for (auto& t : th) t.join();
}

// Diagnostic hooks for the tests: the platform libm sin and cos,
// vectorized, so the gate can feed numpy's OWN pipeline libm transcendentals and
// show that the residual against this file is attributable to `np.sin` alone.
void knots_sin(const double* x, int64_t n, double* o) {
    for (int64_t i = 0; i < n; i++) o[i] = std::sin(x[i]);
}
void knots_cos(const double* x, int64_t n, double* o) {
    for (int64_t i = 0; i < n; i++) o[i] = std::cos(x[i]);
}
void knots_pow3(const double* x, int64_t n, double* o) {
    for (int64_t i = 0; i < n; i++) o[i] = std::pow(x[i], 3.0);
}
// k, kp, kpp before the Wall wrapper, for bisecting a divergence.
void knots_ktrip(const double* x, int64_t n, const double* h, const double* cf,
                const double* cfpi, const double* cfpi2, int nf,
                double* k, double* kp, double* kpp) {
    for (int64_t i = 0; i < n; i++) {
        const double px = M_PI * std::fabs(x[i]);
        double tk[NFMAX], tp[NFMAX], tpp[NFMAX];
        for (int j = 0; j < nf; j++) {
            double lv, ld, ldd, rv, rd, rdd;
            sinc3(h[j] - px, LIBM_SIN, LIBM_COS, lv, ld, ldd);
            sinc3(h[j] + px, LIBM_SIN, LIBM_COS, rv, rd, rdd);
            tk[j]  = cf[j]    * (lv + rv)   / 2.0;
            tp[j]  = cfpi[j]  * (rd - ld)   / 2.0;
            tpp[j] = cfpi2[j] * (ldd + rdd) / 2.0;
        }
        k[i] = psum17(tk, nf); kp[i] = psum17(tp, nf); kpp[i] = psum17(tpp, nf);
    }
}
// _sinc3 alone, elementwise, for bisecting further.
void knots_sinc3(const double* z, int64_t n, double* v, double* d1, double* d2) {
    for (int64_t i = 0; i < n; i++)
        sinc3(z[i], LIBM_SIN, LIBM_COS, v[i], d1[i], d2[i]);
}

}  // extern "C"
