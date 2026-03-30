/*
 * Priority 6 Analysis: η Precision Measurement
 * ==============================================
 *
 * Reads n_scaling_results.json and performs:
 *   1. Power-law fit  T ~ N^(-η)  via log-log OLS (uncensored data only)
 *   2. Bootstrap confidence intervals on η (10,000 resamples)
 *   3. Bayesian model comparison: η = 2/3 exact vs η = free (BIC)
 *   4. Logarithmic correction test: T ~ N^(-η) × (1 + c/ln(N))
 *   5. Per-N-value group statistics and residual analysis
 *
 * Compile:
 *   cc -O2 -o priority6_analysis priority6_analysis.c -lm
 *
 * Usage:
 *   ./priority6_analysis [n_scaling_results.json]
 *   ./priority6_analysis                          # defaults to n_scaling_results.json
 *
 * Output:
 *   - Summary to stdout
 *   - Detailed results to priority6_analysis_results.json
 */

#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* ============================================================================
 * CONSTANTS
 * ============================================================================ */

#define MAX_DATA     2048     /* max raw data points */
#define N_BOOTSTRAP  10000   /* bootstrap resamples */
#define SEED_INIT    314159  /* RNG seed for bootstrap */

/* Theoretical predictions */
#define ETA_GLOBAL_PRED  (2.0 / 3.0)   /* 1 - 1/N_c */
#define ETA_LOCAL_PRED   0.5           /* CDP z=2 */

/* ============================================================================
 * DATA STRUCTURES
 * ============================================================================ */

typedef struct {
    int    N;
    int    pairing;    /* 0 = global, 1 = local */
    int    seed;
    int    stella_id;
    double T_emerge;
    int    censored;   /* 1 = censored (did not emerge) */
} DataPoint;

typedef struct {
    double eta;         /* power-law exponent */
    double eta_se;      /* standard error of eta */
    double log_C;       /* log intercept */
    double C;           /* prefactor */
    double R2;          /* R-squared */
    double SSR;         /* sum of squared residuals */
    int    n;           /* number of points used */
} FitResult;

typedef struct {
    double eta_mean;
    double eta_median;
    double eta_std;
    double ci_lo;       /* 2.5th percentile */
    double ci_hi;       /* 97.5th percentile */
} BootstrapResult;

/* ============================================================================
 * GLOBALS
 * ============================================================================ */

static DataPoint g_data[MAX_DATA];
static int       g_ndata = 0;

/* Simple xorshift64 PRNG for bootstrap */
static uint64_t g_rng_state;

static uint64_t xorshift64(void) {
    uint64_t x = g_rng_state;
    x ^= x << 13;
    x ^= x >> 7;
    x ^= x << 17;
    g_rng_state = x;
    return x;
}

static int rand_int(int n) {
    return (int)(xorshift64() % (uint64_t)n);
}

/* ============================================================================
 * JSON PARSER (minimal, specific to n_scaling_results.json format)
 * ============================================================================ */

/*
 * Reads the "raw_data" array from the JSON file.
 * Each entry has: N, pairing, seed, stella_id, T_emerge, censored.
 * We parse line by line looking for these fields within each {} block.
 */
static int parse_json(const char *filename) {
    FILE *fp = fopen(filename, "r");
    if (!fp) {
        fprintf(stderr, "ERROR: Cannot open %s\n", filename);
        return -1;
    }

    char line[1024];
    int in_raw_data = 0;
    int in_entry = 0;
    int idx = 0;

    DataPoint cur = {0};

    while (fgets(line, sizeof(line), fp)) {
        /* Detect "raw_data" array start */
        if (strstr(line, "\"raw_data\"")) {
            in_raw_data = 1;
            continue;
        }

        if (!in_raw_data) continue;

        /* Detect entry start/end */
        if (strchr(line, '{')) {
            in_entry = 1;
            memset(&cur, 0, sizeof(cur));
            continue;
        }

        if (strchr(line, '}')) {
            if (in_entry && idx < MAX_DATA) {
                g_data[idx++] = cur;
            }
            in_entry = 0;
            continue;
        }

        /* End of raw_data array */
        if (strstr(line, "]")) {
            if (in_raw_data && !in_entry) break;
        }

        if (!in_entry) continue;

        /* Parse fields */
        char *colon = strchr(line, ':');
        if (!colon) continue;

        if (strstr(line, "\"N\"")) {
            cur.N = atoi(colon + 1);
        } else if (strstr(line, "\"pairing\"")) {
            if (strstr(colon, "global"))
                cur.pairing = 0;
            else
                cur.pairing = 1;
        } else if (strstr(line, "\"seed\"")) {
            cur.seed = atoi(colon + 1);
        } else if (strstr(line, "\"stella_id\"")) {
            cur.stella_id = atoi(colon + 1);
        } else if (strstr(line, "\"T_emerge\"")) {
            cur.T_emerge = atof(colon + 1);
        } else if (strstr(line, "\"censored\"")) {
            cur.censored = (strstr(colon, "true") != NULL) ? 1 : 0;
        }
    }

    fclose(fp);
    g_ndata = idx;
    return idx;
}

/* ============================================================================
 * LOG-LOG OLS REGRESSION
 * ============================================================================
 *
 * Model: ln(T) = a + b * ln(N)
 * η = -b (since T ~ N^(-η))
 */
static FitResult ols_fit(const double *ln_N, const double *ln_T, int n) {
    FitResult r = {0};
    r.n = n;

    if (n < 2) return r;

    double sx = 0, sy = 0, sxx = 0, sxy = 0, syy = 0;
    for (int i = 0; i < n; i++) {
        sx  += ln_N[i];
        sy  += ln_T[i];
        sxx += ln_N[i] * ln_N[i];
        sxy += ln_N[i] * ln_T[i];
        syy += ln_T[i] * ln_T[i];
    }

    double denom = n * sxx - sx * sx;
    if (fabs(denom) < 1e-30) return r;

    double b = (n * sxy - sx * sy) / denom;
    double a = (sy - b * sx) / n;

    r.eta   = -b;
    r.log_C = a;
    r.C     = exp(a);

    /* R² and residuals */
    double ss_res = 0, ss_tot = 0;
    double y_mean = sy / n;
    for (int i = 0; i < n; i++) {
        double y_hat = a + b * ln_N[i];
        double resid = ln_T[i] - y_hat;
        ss_res += resid * resid;
        ss_tot += (ln_T[i] - y_mean) * (ln_T[i] - y_mean);
    }
    r.SSR = ss_res;
    r.R2  = (ss_tot > 0) ? 1.0 - ss_res / ss_tot : 0.0;

    /* Standard error of slope b → SE(η) = SE(b) */
    double s2 = ss_res / (n - 2);
    double var_b = s2 * n / denom;
    r.eta_se = sqrt(var_b);

    return r;
}

/* ============================================================================
 * LOG-CORRECTION FIT
 * ============================================================================
 *
 * Model: ln(T) = a + b * ln(N) + c / ln(N)
 * Three-parameter fit via normal equations (3×3 system).
 */
typedef struct {
    double eta;       /* -b */
    double log_C;     /* a */
    double c_corr;    /* c (log correction coefficient) */
    double SSR;
    double R2;
    int    n;
} LogCorrFit;

static LogCorrFit logcorr_fit(const double *ln_N, const double *ln_T, int n) {
    LogCorrFit r = {0};
    r.n = n;
    if (n < 4) return r;

    /* Design matrix columns: x0=1, x1=ln(N), x2=1/ln(N)
     * Normal equations: (X^T X) beta = X^T y
     */
    double A[3][3] = {{0}};
    double B[3]    = {0};

    for (int i = 0; i < n; i++) {
        double x[3] = {1.0, ln_N[i], 1.0 / ln_N[i]};
        for (int j = 0; j < 3; j++) {
            B[j] += x[j] * ln_T[i];
            for (int k = 0; k < 3; k++)
                A[j][k] += x[j] * x[k];
        }
    }

    /* Solve 3×3 via Gaussian elimination with partial pivoting */
    double M[3][4];
    for (int i = 0; i < 3; i++) {
        for (int j = 0; j < 3; j++) M[i][j] = A[i][j];
        M[i][3] = B[i];
    }

    for (int col = 0; col < 3; col++) {
        /* Pivot */
        int maxrow = col;
        for (int row = col + 1; row < 3; row++)
            if (fabs(M[row][col]) > fabs(M[maxrow][col]))
                maxrow = row;
        for (int j = 0; j < 4; j++) {
            double tmp = M[col][j];
            M[col][j] = M[maxrow][j];
            M[maxrow][j] = tmp;
        }
        if (fabs(M[col][col]) < 1e-30) return r;

        for (int row = col + 1; row < 3; row++) {
            double f = M[row][col] / M[col][col];
            for (int j = col; j < 4; j++)
                M[row][j] -= f * M[col][j];
        }
    }

    /* Back-substitution */
    double beta[3];
    for (int i = 2; i >= 0; i--) {
        beta[i] = M[i][3];
        for (int j = i + 1; j < 3; j++)
            beta[i] -= M[i][j] * beta[j];
        beta[i] /= M[i][i];
    }

    r.log_C  = beta[0];
    r.eta    = -beta[1];
    r.c_corr = beta[2];

    /* Residuals */
    double ss_res = 0, ss_tot = 0;
    double y_mean = 0;
    for (int i = 0; i < n; i++) y_mean += ln_T[i];
    y_mean /= n;

    for (int i = 0; i < n; i++) {
        double y_hat = beta[0] + beta[1] * ln_N[i] + beta[2] / ln_N[i];
        double resid = ln_T[i] - y_hat;
        ss_res += resid * resid;
        ss_tot += (ln_T[i] - y_mean) * (ln_T[i] - y_mean);
    }
    r.SSR = ss_res;
    r.R2  = (ss_tot > 0) ? 1.0 - ss_res / ss_tot : 0.0;

    return r;
}

/* ============================================================================
 * CONSTRAINED FIT: η FIXED
 * ============================================================================
 *
 * Model: ln(T) = a + b_fixed * ln(N), where b_fixed = -eta_fixed
 * Only fit intercept a = mean(ln(T) - b_fixed * ln(N))
 */
static double constrained_SSR(const double *ln_N, const double *ln_T,
                               int n, double eta_fixed) {
    double b = -eta_fixed;
    double a = 0;
    for (int i = 0; i < n; i++)
        a += ln_T[i] - b * ln_N[i];
    a /= n;

    double ssr = 0;
    for (int i = 0; i < n; i++) {
        double resid = ln_T[i] - (a + b * ln_N[i]);
        ssr += resid * resid;
    }
    return ssr;
}

/* ============================================================================
 * BOOTSTRAP
 * ============================================================================ */

static int cmp_double(const void *a, const void *b) {
    double da = *(const double *)a;
    double db = *(const double *)b;
    return (da > db) - (da < db);
}

static BootstrapResult bootstrap_eta(const double *ln_N, const double *ln_T,
                                      int n, int n_boot) {
    BootstrapResult br = {0};
    if (n < 3) return br;

    double *etas = malloc(n_boot * sizeof(double));
    double *boot_x = malloc(n * sizeof(double));
    double *boot_y = malloc(n * sizeof(double));

    double sum = 0;
    for (int b = 0; b < n_boot; b++) {
        /* Resample with replacement */
        for (int i = 0; i < n; i++) {
            int j = rand_int(n);
            boot_x[i] = ln_N[j];
            boot_y[i] = ln_T[j];
        }
        FitResult fr = ols_fit(boot_x, boot_y, n);
        etas[b] = fr.eta;
        sum += fr.eta;
    }

    /* Sort for percentiles */
    qsort(etas, n_boot, sizeof(double), cmp_double);

    br.eta_mean   = sum / n_boot;
    br.eta_median = etas[n_boot / 2];
    br.ci_lo      = etas[(int)(0.025 * n_boot)];
    br.ci_hi      = etas[(int)(0.975 * n_boot)];

    /* Standard deviation */
    double s2 = 0;
    for (int b = 0; b < n_boot; b++)
        s2 += (etas[b] - br.eta_mean) * (etas[b] - br.eta_mean);
    br.eta_std = sqrt(s2 / n_boot);

    free(etas);
    free(boot_x);
    free(boot_y);
    return br;
}

/* ============================================================================
 * PER-GROUP STATISTICS
 * ============================================================================ */

typedef struct {
    int    N;
    int    n_total;
    int    n_emerged;
    int    n_censored;
    double median_T;
    double mean_T;
    double std_T;
} GroupStat;

static int cmp_double_val(const void *a, const void *b) {
    double da = *(const double *)a, db = *(const double *)b;
    return (da > db) - (da < db);
}

static GroupStat compute_group(const DataPoint *pts, int n, int N_val) {
    GroupStat gs = {0};
    gs.N = N_val;
    gs.n_total = n;

    double emerged[MAX_DATA];
    int ne = 0;
    for (int i = 0; i < n; i++) {
        if (pts[i].censored)
            gs.n_censored++;
        else
            emerged[ne++] = pts[i].T_emerge;
    }
    gs.n_emerged = ne;

    if (ne == 0) return gs;

    qsort(emerged, ne, sizeof(double), cmp_double_val);
    gs.median_T = (ne % 2 == 0) ?
        (emerged[ne/2 - 1] + emerged[ne/2]) / 2.0 : emerged[ne/2];

    double sum = 0;
    for (int i = 0; i < ne; i++) sum += emerged[i];
    gs.mean_T = sum / ne;

    double s2 = 0;
    for (int i = 0; i < ne; i++)
        s2 += (emerged[i] - gs.mean_T) * (emerged[i] - gs.mean_T);
    gs.std_T = (ne > 1) ? sqrt(s2 / (ne - 1)) : 0;

    return gs;
}

/* ============================================================================
 * MAIN
 * ============================================================================ */

int main(int argc, char **argv) {
    const char *json_file = "n_scaling_results.json";
    if (argc > 1) json_file = argv[1];

    printf("Priority 6: eta Precision Analysis\n");
    printf("===================================\n\n");

    /* Parse data */
    int n = parse_json(json_file);
    if (n <= 0) {
        fprintf(stderr, "No data parsed from %s\n", json_file);
        return 1;
    }
    printf("Loaded %d raw data points from %s\n\n", n, json_file);

    /* Separate by pairing mode, filter uncensored */
    double ln_N_g[MAX_DATA], ln_T_g[MAX_DATA];
    double ln_N_l[MAX_DATA], ln_T_l[MAX_DATA];
    int ng = 0, nl = 0;

    for (int i = 0; i < g_ndata; i++) {
        if (g_data[i].censored) continue;
        double lnN = log((double)g_data[i].N);
        double lnT = log(g_data[i].T_emerge);
        if (g_data[i].pairing == 0) {  /* global */
            ln_N_g[ng] = lnN;
            ln_T_g[ng] = lnT;
            ng++;
        } else {  /* local */
            ln_N_l[nl] = lnN;
            ln_T_l[nl] = lnT;
            nl++;
        }
    }

    printf("Uncensored data: %d global, %d local\n\n", ng, nl);

    /* ---- 1. Power-law fits ---- */
    printf("========================================\n");
    printf("1. POWER-LAW FITS: T ~ N^(-eta)\n");
    printf("========================================\n\n");

    FitResult fit_g = ols_fit(ln_N_g, ln_T_g, ng);
    FitResult fit_l = ols_fit(ln_N_l, ln_T_l, nl);

    printf("  %-10s  %10s  %10s  %10s  %10s  %8s\n",
           "Pairing", "eta", "SE(eta)", "R^2", "C", "n");
    printf("  %-10s  %10.6f  %10.6f  %10.4f  %10.2e  %8d\n",
           "Global", fit_g.eta, fit_g.eta_se, fit_g.R2, fit_g.C, fit_g.n);
    printf("  %-10s  %10.6f  %10.6f  %10.4f  %10.2e  %8d\n",
           "Local", fit_l.eta, fit_l.eta_se, fit_l.R2, fit_l.C, fit_l.n);

    printf("\n  Theory comparison:\n");
    printf("  %-10s  eta_pred=%7.4f  deviation=%.2f%%  (%.2f sigma)\n",
           "Global", ETA_GLOBAL_PRED,
           100.0 * fabs(fit_g.eta - ETA_GLOBAL_PRED) / ETA_GLOBAL_PRED,
           fabs(fit_g.eta - ETA_GLOBAL_PRED) / fit_g.eta_se);
    printf("  %-10s  eta_pred=%7.4f  deviation=%.2f%%  (%.2f sigma)\n",
           "Local", ETA_LOCAL_PRED,
           100.0 * fabs(fit_l.eta - ETA_LOCAL_PRED) / ETA_LOCAL_PRED,
           fabs(fit_l.eta - ETA_LOCAL_PRED) / fit_l.eta_se);

    /* ---- 2. Bootstrap CIs ---- */
    printf("\n========================================\n");
    printf("2. BOOTSTRAP CONFIDENCE INTERVALS (%d resamples)\n", N_BOOTSTRAP);
    printf("========================================\n\n");

    g_rng_state = SEED_INIT;
    BootstrapResult bs_g = bootstrap_eta(ln_N_g, ln_T_g, ng, N_BOOTSTRAP);
    BootstrapResult bs_l = bootstrap_eta(ln_N_l, ln_T_l, nl, N_BOOTSTRAP);

    printf("  %-10s  mean=%8.5f  median=%8.5f  std=%8.5f  95%% CI=[%.4f, %.4f]\n",
           "Global", bs_g.eta_mean, bs_g.eta_median, bs_g.eta_std,
           bs_g.ci_lo, bs_g.ci_hi);
    printf("  %-10s  mean=%8.5f  median=%8.5f  std=%8.5f  95%% CI=[%.4f, %.4f]\n",
           "Local", bs_l.eta_mean, bs_l.eta_median, bs_l.eta_std,
           bs_l.ci_lo, bs_l.ci_hi);

    printf("\n  Predicted values within 95%% CI?\n");
    printf("  %-10s  eta=2/3=%.4f  in [%.4f, %.4f]?  %s\n",
           "Global", ETA_GLOBAL_PRED, bs_g.ci_lo, bs_g.ci_hi,
           (ETA_GLOBAL_PRED >= bs_g.ci_lo && ETA_GLOBAL_PRED <= bs_g.ci_hi)
               ? "YES" : "NO");
    printf("  %-10s  eta=1/2=%.4f  in [%.4f, %.4f]?  %s\n",
           "Local", ETA_LOCAL_PRED, bs_l.ci_lo, bs_l.ci_hi,
           (ETA_LOCAL_PRED >= bs_l.ci_lo && ETA_LOCAL_PRED <= bs_l.ci_hi)
               ? "YES" : "NO");

    /* ---- 3. Bayesian model comparison (BIC) ---- */
    printf("\n========================================\n");
    printf("3. BAYESIAN MODEL COMPARISON (BIC)\n");
    printf("========================================\n\n");

    /* Model 1 (free η): 2 parameters (a, b) → k=2
     * Model 2 (η fixed): 1 parameter (a) → k=1
     * BIC = n*ln(SSR/n) + k*ln(n)
     */

    /* Global */
    double ssr_g_free  = fit_g.SSR;
    double ssr_g_fixed = constrained_SSR(ln_N_g, ln_T_g, ng, ETA_GLOBAL_PRED);
    double bic_g_free  = ng * log(ssr_g_free / ng)  + 2 * log(ng);
    double bic_g_fixed = ng * log(ssr_g_fixed / ng) + 1 * log(ng);
    double dbic_g = bic_g_fixed - bic_g_free;  /* positive = free is better */

    /* Local */
    double ssr_l_free  = fit_l.SSR;
    double ssr_l_fixed = constrained_SSR(ln_N_l, ln_T_l, nl, ETA_LOCAL_PRED);
    double bic_l_free  = nl * log(ssr_l_free / nl)  + 2 * log(nl);
    double bic_l_fixed = nl * log(ssr_l_fixed / nl) + 1 * log(nl);
    double dbic_l = bic_l_fixed - bic_l_free;

    printf("  Comparing: M_fixed (eta = predicted) vs M_free (eta = fit)\n\n");
    printf("  %-10s  SSR_free=%10.4f  SSR_fixed=%10.4f  dBIC=%.2f  ",
           "Global", ssr_g_free, ssr_g_fixed, dbic_g);
    if (dbic_g < -2)
        printf("FIXED PREFERRED (strong)\n");
    else if (dbic_g < 0)
        printf("FIXED PREFERRED (weak)\n");
    else if (dbic_g < 2)
        printf("INCONCLUSIVE\n");
    else if (dbic_g < 6)
        printf("FREE PREFERRED (positive)\n");
    else
        printf("FREE PREFERRED (strong)\n");

    printf("  %-10s  SSR_free=%10.4f  SSR_fixed=%10.4f  dBIC=%.2f  ",
           "Local", ssr_l_free, ssr_l_fixed, dbic_l);
    if (dbic_l < -2)
        printf("FIXED PREFERRED (strong)\n");
    else if (dbic_l < 0)
        printf("FIXED PREFERRED (weak)\n");
    else if (dbic_l < 2)
        printf("INCONCLUSIVE\n");
    else if (dbic_l < 6)
        printf("FREE PREFERRED (positive)\n");
    else
        printf("FREE PREFERRED (strong)\n");

    printf("\n  dBIC interpretation: <-2 fixed better, [-2,2] inconclusive, >2 free better\n");

    /* F-test: fixed vs free */
    printf("\n  F-test (eta_fixed vs eta_free):\n");
    double F_g = ((ssr_g_fixed - ssr_g_free) / 1.0) / (ssr_g_free / (ng - 2));
    double F_l = ((ssr_l_fixed - ssr_l_free) / 1.0) / (ssr_l_free / (nl - 2));
    printf("  %-10s  F = %.4f  (F_crit(1,%d,0.05) ~ 3.84)\n",
           "Global", F_g, ng - 2);
    printf("  %-10s  F = %.4f  (F_crit(1,%d,0.05) ~ 3.84)\n",
           "Local", F_l, nl - 2);
    printf("  F < F_crit => cannot reject eta_fixed at 5%% level\n");

    /* ---- 4. Logarithmic corrections ---- */
    printf("\n========================================\n");
    printf("4. LOGARITHMIC CORRECTION TEST\n");
    printf("========================================\n\n");
    printf("  Model: ln(T) = a + b*ln(N) + c/ln(N)\n\n");

    LogCorrFit lc_g = logcorr_fit(ln_N_g, ln_T_g, ng);
    LogCorrFit lc_l = logcorr_fit(ln_N_l, ln_T_l, nl);

    printf("  %-10s  eta=%.5f  c=%.3f  R2=%.4f  SSR=%.4f\n",
           "Global", lc_g.eta, lc_g.c_corr, lc_g.R2, lc_g.SSR);
    printf("  %-10s  eta=%.5f  c=%.3f  R2=%.4f  SSR=%.4f\n",
           "Local", lc_l.eta, lc_l.c_corr, lc_l.R2, lc_l.SSR);

    /* AIC comparison: pure power law (k=2) vs log-corrected (k=3) */
    double aic_g_pure = ng * log(ssr_g_free / ng) + 2 * 2;
    double aic_g_logc = ng * log(lc_g.SSR / ng)   + 2 * 3;
    double daic_g = aic_g_logc - aic_g_pure;

    double aic_l_pure = nl * log(ssr_l_free / nl) + 2 * 2;
    double aic_l_logc = nl * log(lc_l.SSR / nl)   + 2 * 3;
    double daic_l = aic_l_logc - aic_l_pure;

    printf("\n  dAIC (log_corr - pure_power):\n");
    printf("  %-10s  dAIC = %+.2f  %s\n", "Global", daic_g,
           daic_g > 2 ? "(pure power law preferred)" :
           daic_g < -2 ? "(log correction preferred)" : "(inconclusive)");
    printf("  %-10s  dAIC = %+.2f  %s\n", "Local", daic_l,
           daic_l > 2 ? "(pure power law preferred)" :
           daic_l < -2 ? "(log correction preferred)" : "(inconclusive)");

    /* ---- 5. Per-group statistics ---- */
    printf("\n========================================\n");
    printf("5. PER-N-VALUE GROUP STATISTICS\n");
    printf("========================================\n\n");

    /* Collect unique N values */
    int unique_N[32];
    int n_unique = 0;
    for (int i = 0; i < g_ndata; i++) {
        int found = 0;
        for (int j = 0; j < n_unique; j++)
            if (unique_N[j] == g_data[i].N) { found = 1; break; }
        if (!found && n_unique < 32)
            unique_N[n_unique++] = g_data[i].N;
    }
    /* Sort */
    for (int i = 0; i < n_unique - 1; i++)
        for (int j = i + 1; j < n_unique; j++)
            if (unique_N[i] > unique_N[j]) {
                int tmp = unique_N[i];
                unique_N[i] = unique_N[j];
                unique_N[j] = tmp;
            }

    for (int p = 0; p < 2; p++) {
        const char *plabel = (p == 0) ? "GLOBAL" : "LOCAL";
        printf("  %s pairing:\n", plabel);
        printf("  %8s  %5s  %5s  %5s  %12s  %12s  %12s  %6s\n",
               "N", "total", "emrg", "cens", "median_T", "mean_T", "std_T", "CV");

        for (int u = 0; u < n_unique; u++) {
            DataPoint subset[MAX_DATA];
            int ns = 0;
            for (int i = 0; i < g_ndata; i++)
                if (g_data[i].N == unique_N[u] && g_data[i].pairing == p)
                    subset[ns++] = g_data[i];

            if (ns == 0) continue;
            GroupStat gs = compute_group(subset, ns, unique_N[u]);
            double cv = (gs.mean_T > 0) ? gs.std_T / gs.mean_T : 0;
            printf("  %8d  %5d  %5d  %5d  %12.0f  %12.0f  %12.0f  %6.3f\n",
                   gs.N, gs.n_total, gs.n_emerged, gs.n_censored,
                   gs.median_T, gs.mean_T, gs.std_T, cv);
        }
        printf("\n");
    }

    /* ---- 6. Summary ---- */
    printf("========================================\n");
    printf("6. SUMMARY\n");
    printf("========================================\n\n");

    printf("  eta_global = %.5f +/- %.5f (OLS SE)\n", fit_g.eta, fit_g.eta_se);
    printf("             = %.5f +/- %.5f (bootstrap SD)\n",
           bs_g.eta_mean, bs_g.eta_std);
    printf("             95%% CI: [%.4f, %.4f]\n", bs_g.ci_lo, bs_g.ci_hi);
    printf("             Predicted: 2/3 = %.5f\n", ETA_GLOBAL_PRED);
    printf("             Deviation: %.2f%% (%.2f sigma)\n",
           100.0 * fabs(fit_g.eta - ETA_GLOBAL_PRED) / ETA_GLOBAL_PRED,
           fabs(fit_g.eta - ETA_GLOBAL_PRED) / fit_g.eta_se);
    printf("             2/3 in 95%% CI: %s\n\n",
           (ETA_GLOBAL_PRED >= bs_g.ci_lo && ETA_GLOBAL_PRED <= bs_g.ci_hi)
               ? "YES" : "NO");

    printf("  eta_local  = %.5f +/- %.5f (OLS SE)\n", fit_l.eta, fit_l.eta_se);
    printf("             = %.5f +/- %.5f (bootstrap SD)\n",
           bs_l.eta_mean, bs_l.eta_std);
    printf("             95%% CI: [%.4f, %.4f]\n", bs_l.ci_lo, bs_l.ci_hi);
    printf("             Predicted: 1/2 = %.5f\n", ETA_LOCAL_PRED);
    printf("             Deviation: %.2f%% (%.2f sigma)\n",
           100.0 * fabs(fit_l.eta - ETA_LOCAL_PRED) / ETA_LOCAL_PRED,
           fabs(fit_l.eta - ETA_LOCAL_PRED) / fit_l.eta_se);
    printf("             1/2 in 95%% CI: %s\n\n",
           (ETA_LOCAL_PRED >= bs_l.ci_lo && ETA_LOCAL_PRED <= bs_l.ci_hi)
               ? "YES" : "NO");

    printf("  Log corrections: %s (global dAIC=%+.2f, local dAIC=%+.2f)\n",
           (daic_g > 2 && daic_l > 2) ? "NONE DETECTED" :
           (daic_g < -2 || daic_l < -2) ? "SIGNIFICANT" : "INCONCLUSIVE",
           daic_g, daic_l);

    printf("  BIC model comparison: %s (global dBIC=%+.2f, local dBIC=%+.2f)\n",
           (dbic_g < 2 && dbic_l < 2) ?
               "eta_fixed ADEQUATE (cannot reject exact values)" :
               "eta_free PREFERRED (exact values disfavored)",
           dbic_g, dbic_l);

    /* ---- Write JSON output ---- */
    const char *outfile = "priority6_analysis_results.json";
    FILE *fp = fopen(outfile, "w");
    if (fp) {
        fprintf(fp, "{\n");
        fprintf(fp, "  \"description\": \"Priority 6: eta precision analysis\",\n");
        fprintf(fp, "  \"data_file\": \"%s\",\n", json_file);
        fprintf(fp, "  \"n_global_uncensored\": %d,\n", ng);
        fprintf(fp, "  \"n_local_uncensored\": %d,\n", nl);
        fprintf(fp, "  \"power_law_fits\": {\n");
        fprintf(fp, "    \"global\": {\n");
        fprintf(fp, "      \"eta\": %.10f,\n", fit_g.eta);
        fprintf(fp, "      \"eta_se\": %.10f,\n", fit_g.eta_se);
        fprintf(fp, "      \"C\": %.6e,\n", fit_g.C);
        fprintf(fp, "      \"R2\": %.10f,\n", fit_g.R2);
        fprintf(fp, "      \"SSR\": %.10f,\n", fit_g.SSR);
        fprintf(fp, "      \"n_points\": %d\n", fit_g.n);
        fprintf(fp, "    },\n");
        fprintf(fp, "    \"local\": {\n");
        fprintf(fp, "      \"eta\": %.10f,\n", fit_l.eta);
        fprintf(fp, "      \"eta_se\": %.10f,\n", fit_l.eta_se);
        fprintf(fp, "      \"C\": %.6e,\n", fit_l.C);
        fprintf(fp, "      \"R2\": %.10f,\n", fit_l.R2);
        fprintf(fp, "      \"SSR\": %.10f,\n", fit_l.SSR);
        fprintf(fp, "      \"n_points\": %d\n", fit_l.n);
        fprintf(fp, "    }\n");
        fprintf(fp, "  },\n");
        fprintf(fp, "  \"bootstrap\": {\n");
        fprintf(fp, "    \"n_resamples\": %d,\n", N_BOOTSTRAP);
        fprintf(fp, "    \"global\": {\n");
        fprintf(fp, "      \"eta_mean\": %.10f,\n", bs_g.eta_mean);
        fprintf(fp, "      \"eta_median\": %.10f,\n", bs_g.eta_median);
        fprintf(fp, "      \"eta_std\": %.10f,\n", bs_g.eta_std);
        fprintf(fp, "      \"ci_lo_2.5\": %.10f,\n", bs_g.ci_lo);
        fprintf(fp, "      \"ci_hi_97.5\": %.10f\n", bs_g.ci_hi);
        fprintf(fp, "    },\n");
        fprintf(fp, "    \"local\": {\n");
        fprintf(fp, "      \"eta_mean\": %.10f,\n", bs_l.eta_mean);
        fprintf(fp, "      \"eta_median\": %.10f,\n", bs_l.eta_median);
        fprintf(fp, "      \"eta_std\": %.10f,\n", bs_l.eta_std);
        fprintf(fp, "      \"ci_lo_2.5\": %.10f,\n", bs_l.ci_lo);
        fprintf(fp, "      \"ci_hi_97.5\": %.10f\n", bs_l.ci_hi);
        fprintf(fp, "    }\n");
        fprintf(fp, "  },\n");
        fprintf(fp, "  \"model_comparison\": {\n");
        fprintf(fp, "    \"global\": {\n");
        fprintf(fp, "      \"eta_predicted\": %.10f,\n", ETA_GLOBAL_PRED);
        fprintf(fp, "      \"SSR_free\": %.10f,\n", ssr_g_free);
        fprintf(fp, "      \"SSR_fixed\": %.10f,\n", ssr_g_fixed);
        fprintf(fp, "      \"dBIC\": %.10f,\n", dbic_g);
        fprintf(fp, "      \"F_stat\": %.10f,\n", F_g);
        fprintf(fp, "      \"pred_in_95CI\": %s\n",
                (ETA_GLOBAL_PRED >= bs_g.ci_lo && ETA_GLOBAL_PRED <= bs_g.ci_hi)
                    ? "true" : "false");
        fprintf(fp, "    },\n");
        fprintf(fp, "    \"local\": {\n");
        fprintf(fp, "      \"eta_predicted\": %.10f,\n", ETA_LOCAL_PRED);
        fprintf(fp, "      \"SSR_free\": %.10f,\n", ssr_l_free);
        fprintf(fp, "      \"SSR_fixed\": %.10f,\n", ssr_l_fixed);
        fprintf(fp, "      \"dBIC\": %.10f,\n", dbic_l);
        fprintf(fp, "      \"F_stat\": %.10f,\n", F_l);
        fprintf(fp, "      \"pred_in_95CI\": %s\n",
                (ETA_LOCAL_PRED >= bs_l.ci_lo && ETA_LOCAL_PRED <= bs_l.ci_hi)
                    ? "true" : "false");
        fprintf(fp, "    }\n");
        fprintf(fp, "  },\n");
        fprintf(fp, "  \"log_corrections\": {\n");
        fprintf(fp, "    \"global\": {\n");
        fprintf(fp, "      \"eta\": %.10f,\n", lc_g.eta);
        fprintf(fp, "      \"c_corr\": %.10f,\n", lc_g.c_corr);
        fprintf(fp, "      \"SSR\": %.10f,\n", lc_g.SSR);
        fprintf(fp, "      \"R2\": %.10f,\n", lc_g.R2);
        fprintf(fp, "      \"dAIC\": %.10f\n", daic_g);
        fprintf(fp, "    },\n");
        fprintf(fp, "    \"local\": {\n");
        fprintf(fp, "      \"eta\": %.10f,\n", lc_l.eta);
        fprintf(fp, "      \"c_corr\": %.10f,\n", lc_l.c_corr);
        fprintf(fp, "      \"SSR\": %.10f,\n", lc_l.SSR);
        fprintf(fp, "      \"R2\": %.10f,\n", lc_l.R2);
        fprintf(fp, "      \"dAIC\": %.10f\n", daic_l);
        fprintf(fp, "    }\n");
        fprintf(fp, "  }\n");
        fprintf(fp, "}\n");
        fclose(fp);
        printf("\nResults written to %s\n", outfile);
    }

    return 0;
}
