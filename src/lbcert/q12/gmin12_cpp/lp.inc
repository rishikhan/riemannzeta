// The Kelley cut-model LP of sep_window_search.model_ratio / lp_kappa, in the core process
// (HiGHS C++ API).  Included by gmin_stream.cpp.
//
//   max kappa*eps - sum b  s.t.  eps - row_i . x <= 0          (one row per cut)
//                                eps*HS_RATIO - b_gap <= 0     (end-gap floor, when set)
//                                Aeq x = beq,  lb <= x <= ub,  eps <= 1/64
//
// Mode 0 (cold, the default) rebuilds the model and a fresh Highs object for every LP, exactly as
// scipy.optimize.linprog(method="highs") hands it to HiGHS: rows in the order A_ub (cuts, then the
// two floor rows) then A_eq; the matrix column-wise with explicit zeros dropped (csc_array of the
// dense stack); options presolve on, dual simplex strategy, feasibility tolerances 1e-10, debug
// level 0, no output; then scipy's success test (model status optimal and _check_result at
// tol = sqrt(1e-9) * 10).  Linked against the HiGHS version scipy bundles, it returns the same x.
//
// Mode 1 (warm) keeps one Highs object for the whole refit: the first LP passes the model, later
// cuts are appended with addRows, kappa changes the eps cost only, and the run starts from the
// previous basis with presolve off.  Same LP, different simplex path: x agrees with mode 0 when the
// optimum is unique, up to rounding.
#include "Highs.h"

struct LPModel {
    int nv = 0;                       // weight variables (q + np); eps is column nv
    int neq = 0;
    std::vector<double> Aeq, beq, lb, ub;
    bool has_hs = false;
    double hs_ratio = 0.0;
    std::vector<int> hs_cols;         // the gap of each floor row, in scipy's order
    int mode = 0;
    std::vector<double> rows;         // cut rows, row-major, nv each
    int nrows = 0;
    Highs* warm = nullptr;
    int warm_rows = 0;                // cut rows already in the warm model
    uint64_t nlp = 0, iters = 0;
    double secs = 0.0;
};

static void lp_set_options(Highs& h, bool presolve) {
    h.setOptionValue("output_flag", false);
    h.setOptionValue("log_to_console", false);
    h.setOptionValue("presolve", std::string(presolve ? "on" : "off"));
    h.setOptionValue("highs_debug_level", 0);
    h.setOptionValue("dual_feasibility_tolerance", 1e-10);
    h.setOptionValue("primal_feasibility_tolerance", 1e-10);
    h.setOptionValue("simplex_strategy", 1);   // kSimplexStrategyDual, as scipy sets it
}

// scipy's model: A_ub = [-rows | 1; floor rows], A_eq = [Aeq | 0], column-wise, zeros dropped.
static void lp_build(const LPModel& M, double kappa, HighsLp& lp) {
    const int nc = M.nv + 1, nhs = (int)M.hs_cols.size();
    const int nub = M.nrows + nhs, nr = nub + M.neq;
    lp.num_col_ = nc;
    lp.num_row_ = nr;
    lp.col_cost_.assign(nc, 0.0);
    for (int j = 0; j < Q; j++) lp.col_cost_[j] = 1.0;
    lp.col_cost_[M.nv] = -kappa;
    lp.col_lower_ = M.lb;
    lp.col_upper_ = M.ub;
    lp.col_lower_.push_back(-kHighsInf);
    lp.col_upper_.push_back(1.0 / 64);
    lp.row_lower_.assign(nr, -kHighsInf);
    lp.row_upper_.assign(nr, 0.0);
    for (int e = 0; e < M.neq; e++) lp.row_lower_[nub + e] = lp.row_upper_[nub + e] = M.beq[e];
    lp.sense_ = ObjSense::kMinimize;
    HighsSparseMatrix& A = lp.a_matrix_;
    A.format_ = MatrixFormat::kColwise;
    A.num_col_ = nc;
    A.num_row_ = nr;
    A.start_.assign(1, 0);
    A.index_.clear();
    A.value_.clear();
    for (int j = 0; j < nc; j++) {
        for (int i = 0; i < M.nrows; i++) {
            double v = j < M.nv ? -M.rows[(size_t)i * M.nv + j] : 1.0;
            if (v != 0.0) { A.index_.push_back(i); A.value_.push_back(v); }
        }
        for (int k = 0; k < nhs; k++) {
            double v = j == M.nv ? M.hs_ratio : (j == M.hs_cols[k] ? -1.0 : 0.0);
            if (v != 0.0) { A.index_.push_back(M.nrows + k); A.value_.push_back(v); }
        }
        if (j < M.nv)
            for (int e = 0; e < M.neq; e++) {
                double v = M.Aeq[(size_t)e * M.nv + j];
                if (v != 0.0) { A.index_.push_back(nub + e); A.value_.push_back(v); }
            }
        A.start_.push_back((HighsInt)A.index_.size());
    }
}

// scipy's _check_result on an optimal HiGHS solution: no NaN, bounds, slack and equality
// residuals within tol = sqrt(1e-9) * 10.
static bool lp_check(const HighsLp& lp, const HighsSolution& s, double fun) {
    const double tol = std::sqrt(1e-9) * 10;
    if (std::isnan(fun)) return false;
    for (int j = 0; j < lp.num_col_; j++) {
        double x = s.col_value[j];
        if (std::isnan(x)) return false;
        if (!(x >= lp.col_lower_[j] - tol && x <= lp.col_upper_[j] + tol)) return false;
    }
    for (int i = 0; i < lp.num_row_; i++) {
        double r = lp.row_upper_[i] - s.row_value[i];
        if (std::isnan(r)) return false;
        bool eq = lp.row_lower_[i] == lp.row_upper_[i];
        if (eq ? std::fabs(r) > tol : r < -tol) return false;
    }
    return true;
}

// One LP at ratio kappa -> (eps, x) in e / x; false when scipy's linprog would report failure.
static bool lp_kappa(LPModel& M, double kappa, double& e, double* x) {
    auto t0 = std::chrono::steady_clock::now();
    bool ok = false;
    if (M.mode == 0) {
        HighsLp lp;
        lp_build(M, kappa, lp);
        Highs h;
        lp_set_options(h, true);
        if (h.passModel(lp) != HighsStatus::kError && h.run() != HighsStatus::kError &&
            h.getModelStatus() == HighsModelStatus::kOptimal) {
            const HighsSolution& s = h.getSolution();
            ok = lp_check(lp, s, h.getInfo().objective_function_value);
            if (ok) { std::memcpy(x, s.col_value.data(), 8 * (size_t)M.nv); e = s.col_value[M.nv]; }
            M.iters += h.getInfo().simplex_iteration_count;
        }
    } else {
        Highs& h = *M.warm;
        if (M.warm_rows == 0 && h.getNumRow() == 0) {
            HighsLp lp;
            lp_build(M, kappa, lp);
            lp_set_options(h, true);
            h.passModel(lp);
            M.warm_rows = M.nrows;
        } else {
            const int nc = M.nv + 1, nn = M.nrows - M.warm_rows;
            if (nn > 0) {
                std::vector<double> lo(nn, -kHighsInf), up(nn, 0.0), val;
                std::vector<HighsInt> st, idx;
                for (int i = 0; i < nn; i++) {
                    st.push_back((HighsInt)idx.size());
                    const double* r = M.rows.data() + (size_t)(M.warm_rows + i) * M.nv;
                    for (int j = 0; j < M.nv; j++)
                        if (r[j] != 0.0) { idx.push_back(j); val.push_back(-r[j]); }
                    idx.push_back(nc - 1);
                    val.push_back(1.0);
                }
                h.addRows(nn, lo.data(), up.data(), (HighsInt)idx.size(), st.data(), idx.data(), val.data());
                M.warm_rows = M.nrows;
            }
            h.changeColCost(M.nv, -kappa);
            h.setOptionValue("presolve", std::string("off"));
        }
        if (h.run() != HighsStatus::kError && h.getModelStatus() == HighsModelStatus::kOptimal) {
            const HighsSolution& s = h.getSolution();
            ok = lp_check(h.getLp(), s, h.getInfo().objective_function_value);
            if (ok) { std::memcpy(x, s.col_value.data(), 8 * (size_t)M.nv); e = s.col_value[M.nv]; }
        }
        M.iters += h.getInfo().simplex_iteration_count;
    }
    M.nlp++;
    M.secs += std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    return ok;
}

// numpy's float64 sum of a contiguous length-n array (pairwise_sum: n < 8 sequential, else eight
// accumulators combined ((0+1)+(2+3))+((4+5)+(6+7)) and the tail added in order; n <= 128 here).
static double np_sum(const double* a, int n) {
    if (n < 8) {
        double s = -0.0;
        for (int i = 0; i < n; i++) s += a[i];
        return s;
    }
    double r[8];
    for (int k = 0; k < 8; k++) r[k] = a[k];
    int i = 8;
    for (; i < n - (n % 8); i += 8)
        for (int k = 0; k < 8; k++) r[k] += a[i + k];
    double s = ((r[0] + r[1]) + (r[2] + r[3])) + ((r[4] + r[5]) + (r[6] + r[7]));
    for (; i < n; i++) s += a[i];
    return s;
}

// sep_window_search.model_ratio: Dinkelbach steps on the cut model -> (kappa, x, found).
static bool lp_ratio(LPModel& M, double H, double kappa0, int steps, double& kappa, double* x) {
    kappa = kappa0;
    bool found = false;
    std::vector<double> xx(M.nv);
    for (int s = 0; s < steps; s++) {
        double e;
        if (!lp_kappa(M, kappa, e, xx.data())) break;
        std::memcpy(x, xx.data(), 8 * (size_t)M.nv);
        found = true;
        double nw = (H - np_sum(xx.data(), Q)) / (1 - e);
        if (std::fabs(nw - kappa) < 1e-13) { kappa = nw; break; }
        kappa = nw;
    }
    return found;
}
