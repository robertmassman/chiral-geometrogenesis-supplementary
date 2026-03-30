/*
 * Conditional Spectrum Analysis: Density-Restricted H_phys
 * =========================================================
 *
 * Tests whether removing low-density (absorbing-state-adjacent) configurations
 * reveals Z_3 Potts-like spectral structure in the stella soup.
 *
 * Hypothesis: The absorbing state (rho=0) and Directed Percolation dynamics
 * contaminate the full spectrum. By projecting H_phys onto the subspace of
 * configurations with replicator density > threshold, we may recover Potts ratios.
 *
 * Two restriction methods:
 *   A) Trit-density threshold: rho(cfg) = fraction of non-zero trits > rho_th
 *   B) NESS-weight threshold: keep top X% of states by NESS probability
 *
 * Compile: cc -O3 -o conditional_spectrum conditional_spectrum.c -lm
 * Run:     ./conditional_spectrum
 *
 * Date: 2026-03-10
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define Z3 3
#define MAX_VM_STEPS 729

/* =========================================================================
 * VM IMPLEMENTATION
 * ========================================================================= */

static void execute_tape(unsigned char *tape, int tape_len, int max_steps) {
    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;

    while (steps < max_steps && ip + 1 < tape_len) {
        int high = tape[ip], low = tape[ip + 1];

        if (high == 0) {
            if (low == 1) {
                tape[h0] = (tape[h0] + 1) % Z3;
            } else if (low == 2) {
                h0 = (h0 + 1) % tape_len;
            }
        } else if (high == 1) {
            if (low == 0) {
                h0 = (h0 - 1 + tape_len) % tape_len;
            } else if (low == 1) {
                h1 = (h1 + 1) % tape_len;
            } else if (low == 2) {
                if (tape[h0] == 0) {
                    int depth = 1, pos = ip + 2;
                    while (depth > 0 && pos + 1 < tape_len) {
                        if (tape[pos] == 1 && tape[pos+1] == 2) depth++;
                        else if (tape[pos] == 2 && tape[pos+1] == 0) depth--;
                        pos += 2;
                    }
                    if (depth == 0) ip = pos - 2;
                }
            }
        } else if (high == 2) {
            if (low == 0) {
                if (tape[h0] != 0) {
                    int depth = 1, pos = ip - 2;
                    while (depth > 0 && pos >= 0) {
                        if (tape[pos] == 2 && tape[pos+1] == 0) depth++;
                        else if (tape[pos] == 1 && tape[pos+1] == 2) depth--;
                        pos -= 2;
                    }
                    if (depth == 0) ip = pos + 2;
                }
            } else if (low == 1) {
                tape[h1] = tape[h0];
            } else if (low == 2) {
                tape[h0] = tape[h1];
            }
        }

        ip += 2;
        steps++;
    }
}

/* =========================================================================
 * CONFIGURATION SPACE
 * ========================================================================= */

static int pow3(int n) {
    int r = 1;
    for (int i = 0; i < n; i++) r *= 3;
    return r;
}

static void idx_to_trits(int idx, unsigned char *trits, int n) {
    for (int i = n - 1; i >= 0; i--) {
        trits[i] = idx % 3;
        idx /= 3;
    }
}

static int trits_to_idx(const unsigned char *trits, int n) {
    int idx = 0;
    for (int i = 0; i < n; i++) idx = idx * 3 + trits[i];
    return idx;
}

/* =========================================================================
 * DETERMINISTIC TRANSITION MAPS
 * ========================================================================= */

static void build_det_maps(int L, int *map_fwd, int *map_rev) {
    int n_prog = pow3(L);
    int n_cfg = n_prog * n_prog;
    int tape_len = 2 * L;
    unsigned char *tape = (unsigned char *)malloc(tape_len);

    for (int src = 0; src < n_cfg; src++) {
        int ia = src / n_prog, ib = src % n_prog;

        /* Forward: tape = pa || pb */
        idx_to_trits(ia, tape, L);
        idx_to_trits(ib, tape + L, L);
        execute_tape(tape, tape_len, MAX_VM_STEPS);
        int new_a = trits_to_idx(tape, L);
        int new_b = trits_to_idx(tape + L, L);
        map_fwd[src] = new_a * n_prog + new_b;

        /* Reverse: tape = pb || pa */
        idx_to_trits(ib, tape, L);
        idx_to_trits(ia, tape + L, L);
        execute_tape(tape, tape_len, MAX_VM_STEPS);
        int first = trits_to_idx(tape, L);
        int second = trits_to_idx(tape + L, L);
        map_rev[src] = second * n_prog + first;
    }

    free(tape);
}

/* =========================================================================
 * MUTATION: M_mut = M1^{otimes n_sites}
 * ========================================================================= */

static void apply_mutation(double *out, const double *in, int n_sites, double mu) {
    double p_same = 1.0 - 2.0 * mu / 3.0;
    double p_diff = mu / 3.0;
    int n = pow3(n_sites);

    double *buf_a = (double *)malloc(n * sizeof(double));
    double *buf_b = (double *)malloc(n * sizeof(double));
    memcpy(buf_a, in, n * sizeof(double));

    for (int site = 0; site < n_sites; site++) {
        int stride = pow3(n_sites - 1 - site);
        int block = pow3(site);

        for (int b = 0; b < block; b++) {
            for (int s = 0; s < stride; s++) {
                int i0 = (b * 3 + 0) * stride + s;
                int i1 = (b * 3 + 1) * stride + s;
                int i2 = (b * 3 + 2) * stride + s;

                double v0 = buf_a[i0], v1 = buf_a[i1], v2 = buf_a[i2];
                buf_b[i0] = p_same * v0 + p_diff * v1 + p_diff * v2;
                buf_b[i1] = p_diff * v0 + p_same * v1 + p_diff * v2;
                buf_b[i2] = p_diff * v0 + p_diff * v1 + p_same * v2;
            }
        }

        double *tmp = buf_a; buf_a = buf_b; buf_b = tmp;
    }

    memcpy(out, buf_a, n * sizeof(double));
    free(buf_a);
    free(buf_b);
}

/* =========================================================================
 * TRANSITION OPERATORS
 * ========================================================================= */

static void apply_T(double *out, const double *in, int n_cfg,
                    const int *map_fwd, const int *map_rev,
                    int n_sites, double mu) {
    double *tmp = (double *)calloc(n_cfg, sizeof(double));
    for (int src = 0; src < n_cfg; src++) {
        tmp[map_fwd[src]] += 0.5 * in[src];
        tmp[map_rev[src]] += 0.5 * in[src];
    }

    if (mu > 0) {
        apply_mutation(out, tmp, n_sites, mu);
    } else {
        memcpy(out, tmp, n_cfg * sizeof(double));
    }
    free(tmp);
}

static void apply_T_transpose(double *out, const double *in, int n_cfg,
                               const int *map_fwd, const int *map_rev,
                               int n_sites, double mu) {
    double *tmp = (double *)malloc(n_cfg * sizeof(double));
    if (mu > 0) {
        apply_mutation(tmp, in, n_sites, mu);
    } else {
        memcpy(tmp, in, n_cfg * sizeof(double));
    }

    for (int src = 0; src < n_cfg; src++) {
        out[src] = 0.5 * tmp[map_fwd[src]] + 0.5 * tmp[map_rev[src]];
    }
    free(tmp);
}

/* =========================================================================
 * NESS COMPUTATION
 * ========================================================================= */

static double *compute_ness(int n_cfg, const int *map_fwd, const int *map_rev,
                            int n_sites, double mu, int max_iter, double tol) {
    double *p = (double *)malloc(n_cfg * sizeof(double));
    double *p_new = (double *)malloc(n_cfg * sizeof(double));

    double inv_n = 1.0 / n_cfg;
    for (int i = 0; i < n_cfg; i++) p[i] = inv_n;

    for (int iter = 0; iter < max_iter; iter++) {
        apply_T(p_new, p, n_cfg, map_fwd, map_rev, n_sites, mu);

        double sum = 0;
        for (int i = 0; i < n_cfg; i++) sum += p_new[i];
        for (int i = 0; i < n_cfg; i++) p_new[i] /= sum;

        double diff = 0;
        for (int i = 0; i < n_cfg; i++) diff += fabs(p_new[i] - p[i]);
        if (diff < tol) {
            printf("    NESS converged in %d iterations (L1 diff = %.2e)\n", iter+1, diff);
            memcpy(p, p_new, n_cfg * sizeof(double));
            free(p_new);
            return p;
        }

        double *tmp = p; p = p_new; p_new = tmp;
    }

    printf("    NESS: max iterations reached\n");
    free(p_new);
    return p;
}

/* =========================================================================
 * H_phys MATRIX-VECTOR PRODUCT (standard, unrestricted)
 * ========================================================================= */

typedef struct {
    int n_cfg;
    int n_sites;
    double mu;
    const int *map_fwd;
    const int *map_rev;
    const double *sqrt_pi;
    const double *inv_sqrt_pi;
} HphysCtx;

static void apply_Hphys(double *out, const double *v, const HphysCtx *ctx) {
    int n = ctx->n_cfg;
    double *w = (double *)malloc(n * sizeof(double));
    double *Tw = (double *)malloc(n * sizeof(double));
    double *result1 = (double *)malloc(n * sizeof(double));
    double *result2 = (double *)malloc(n * sizeof(double));

    /* H_tilde @ v */
    for (int i = 0; i < n; i++) w[i] = ctx->sqrt_pi[i] * v[i];
    apply_T(Tw, w, n, ctx->map_fwd, ctx->map_rev, ctx->n_sites, ctx->mu);
    for (int i = 0; i < n; i++) w[i] = ctx->sqrt_pi[i] * v[i] - Tw[i];
    for (int i = 0; i < n; i++) result1[i] = ctx->inv_sqrt_pi[i] * w[i];

    /* H_tilde^T @ v */
    for (int i = 0; i < n; i++) w[i] = ctx->inv_sqrt_pi[i] * v[i];
    apply_T_transpose(Tw, w, n, ctx->map_fwd, ctx->map_rev, ctx->n_sites, ctx->mu);
    for (int i = 0; i < n; i++) w[i] = ctx->inv_sqrt_pi[i] * v[i] - Tw[i];
    for (int i = 0; i < n; i++) result2[i] = ctx->sqrt_pi[i] * w[i];

    for (int i = 0; i < n; i++) out[i] = 0.5 * (result1[i] + result2[i]);

    free(w);
    free(Tw);
    free(result1);
    free(result2);
}

/* =========================================================================
 * RESTRICTED H_phys: P @ H_phys @ P
 *
 * Apply H_phys but zero out components outside the active mask before and after.
 * ========================================================================= */

typedef struct {
    HphysCtx *hctx;
    const int *mask;  /* mask[i] = 1 if active, 0 if excluded */
    int n_active;
} RestrictedCtx;

static void apply_Hphys_restricted(double *out, const double *v, const RestrictedCtx *rctx) {
    int n = rctx->hctx->n_cfg;
    double *projected = (double *)malloc(n * sizeof(double));

    /* Project input: zero out inactive components */
    for (int i = 0; i < n; i++)
        projected[i] = rctx->mask[i] ? v[i] : 0.0;

    /* Apply full H_phys */
    apply_Hphys(out, projected, rctx->hctx);

    /* Project output: zero out inactive components */
    for (int i = 0; i < n; i++)
        if (!rctx->mask[i]) out[i] = 0.0;

    free(projected);
}

/* =========================================================================
 * Z_3 POTTS HAMILTONIAN
 * ========================================================================= */

typedef struct {
    int n_sites;
    int n_cfg;
    double J;
    double K;
} PottsCtx;

static void apply_Hpotts(double *out, const double *v, const PottsCtx *ctx) {
    int n = ctx->n_cfg;
    int ns = ctx->n_sites;
    double J = ctx->J;
    double K = ctx->K;
    unsigned char *config = (unsigned char *)malloc(ns);
    unsigned char *config2 = (unsigned char *)malloc(ns);

    memset(out, 0, n * sizeof(double));

    for (int idx = 0; idx < n; idx++) {
        if (fabs(v[idx]) < 1e-300) continue;

        idx_to_trits(idx, config, ns);

        /* Diagonal: -K * sum_bond delta(s_i, s_{i+1}) */
        double diag = 0;
        for (int s = 0; s < ns; s++) {
            int next = (s + 1) % ns;
            if (config[s] == config[next]) diag -= K;
        }
        out[idx] += diag * v[idx];

        /* Off-diagonal: -J * (tau + tau^dag) at each site */
        for (int site = 0; site < ns; site++) {
            memcpy(config2, config, ns);

            config2[site] = (config[site] + 1) % 3;
            int jdx = trits_to_idx(config2, ns);
            out[jdx] -= J * v[idx];

            config2[site] = (config[site] + 2) % 3;
            jdx = trits_to_idx(config2, ns);
            out[jdx] -= J * v[idx];
        }
    }

    free(config);
    free(config2);
}

/* Restricted Potts */
typedef struct {
    PottsCtx *pctx;
    const int *mask;
    int n_active;
} RestrictedPottsCtx;

static void apply_Hpotts_restricted(double *out, const double *v, const RestrictedPottsCtx *rctx) {
    int n = rctx->pctx->n_cfg;
    double *projected = (double *)malloc(n * sizeof(double));

    for (int i = 0; i < n; i++)
        projected[i] = rctx->mask[i] ? v[i] : 0.0;

    apply_Hpotts(out, projected, rctx->pctx);

    for (int i = 0; i < n; i++)
        if (!rctx->mask[i]) out[i] = 0.0;

    free(projected);
}

/* =========================================================================
 * QL ALGORITHM
 * ========================================================================= */

static void tql2(double *diag, double *subdiag, int n) {
    double *d = diag;
    double *e = subdiag;
    e[n-1] = 0.0;

    for (int l = 0; l < n; l++) {
        int iter = 0;
        int m;
        do {
            for (m = l; m < n - 1; m++) {
                double dd = fabs(d[m]) + fabs(d[m+1]);
                if (fabs(e[m]) + dd == dd) break;
            }
            if (m != l) {
                if (iter++ >= 300) {
                    fprintf(stderr, "tql2: too many iterations at l=%d\n", l);
                    return;
                }
                double g = (d[l+1] - d[l]) / (2.0 * e[l]);
                double r = sqrt(g * g + 1.0);
                double sign_g = (g >= 0) ? r : -r;
                g = d[m] - d[l] + e[l] / (g + sign_g);
                double s = 1.0, c = 1.0, p = 0.0;
                int i;
                for (i = m - 1; i >= l; i--) {
                    double f = s * e[i];
                    double b = c * e[i];
                    r = sqrt(f * f + g * g);
                    e[i+1] = r;
                    if (r == 0.0) {
                        d[i+1] -= p;
                        e[m] = 0.0;
                        break;
                    }
                    s = f / r;
                    c = g / r;
                    g = d[i+1] - p;
                    r = (d[i] - g) * s + 2.0 * c * b;
                    p = s * r;
                    d[i+1] = g + p;
                    g = c * r - b;
                }
                if (r == 0.0 && i >= l) continue;
                d[l] -= p;
                e[l] = g;
                e[m] = 0.0;
            }
        } while (m != l);
    }

    /* Sort ascending */
    for (int i = 1; i < n; i++) {
        double key = d[i];
        int j = i - 1;
        while (j >= 0 && d[j] > key) {
            d[j+1] = d[j];
            j--;
        }
        d[j+1] = key;
    }
}

/* =========================================================================
 * LANCZOS ALGORITHM with full reorthogonalization
 * ========================================================================= */

typedef void (*matvec_fn)(double *out, const double *in, const void *ctx);

static double *lanczos(matvec_fn matvec, const void *ctx, int n, int m, int k_want,
                       const int *mask) {
    /*
     * If mask != NULL, the starting vector is restricted to the active set
     * and reorthogonalization respects the projection.
     */
    if (m > n) m = n;

    double *V = (double *)malloc((long)n * m * sizeof(double));
    double *alpha = (double *)calloc(m, sizeof(double));
    double *beta_arr = (double *)calloc(m + 1, sizeof(double));
    double *w = (double *)malloc(n * sizeof(double));

    if (!V || !alpha || !beta_arr || !w) {
        fprintf(stderr, "Lanczos: memory allocation failed\n");
        exit(1);
    }

    /* Random starting vector (restricted to mask if provided) */
    srand(42);
    double norm = 0;
    for (int i = 0; i < n; i++) {
        double val = ((double)rand() / RAND_MAX) - 0.5;
        if (mask && !mask[i]) val = 0.0;
        V[i] = val;
        norm += val * val;
    }
    norm = sqrt(norm);
    for (int i = 0; i < n; i++) V[i] /= norm;

    int actual_m = m;

    for (int j = 0; j < m; j++) {
        double *vj = V + (long)j * n;

        matvec(w, vj, ctx);

        double a = 0;
        for (int i = 0; i < n; i++) a += vj[i] * w[i];
        alpha[j] = a;

        if (j > 0) {
            double *vjm1 = V + (long)(j-1) * n;
            for (int i = 0; i < n; i++)
                w[i] -= a * vj[i] + beta_arr[j] * vjm1[i];
        } else {
            for (int i = 0; i < n; i++)
                w[i] -= a * vj[i];
        }

        /* Full reorthogonalization (twice) */
        for (int reorth = 0; reorth < 2; reorth++) {
            for (int k = 0; k <= j; k++) {
                double *vk = V + (long)k * n;
                double dot = 0;
                for (int i = 0; i < n; i++) dot += vk[i] * w[i];
                for (int i = 0; i < n; i++) w[i] -= dot * vk[i];
            }
        }

        /* Enforce mask on w (project back into active subspace) */
        if (mask) {
            for (int i = 0; i < n; i++)
                if (!mask[i]) w[i] = 0.0;
        }

        double b = 0;
        for (int i = 0; i < n; i++) b += w[i] * w[i];
        b = sqrt(b);
        beta_arr[j+1] = b;

        if (b < 1e-14) {
            actual_m = j + 1;
            break;
        }

        if (j + 1 < m) {
            double *vjp1 = V + (long)(j+1) * n;
            double inv_b = 1.0 / b;
            for (int i = 0; i < n; i++) vjp1[i] = w[i] * inv_b;
        }

        if ((j + 1) % 50 == 0) {
            printf("      Lanczos iteration %d/%d\n", j+1, m);
        }
    }

    /* Extract eigenvalues from tridiagonal matrix */
    double *diag = (double *)malloc(actual_m * sizeof(double));
    double *subdiag = (double *)malloc(actual_m * sizeof(double));
    for (int i = 0; i < actual_m; i++) diag[i] = alpha[i];
    for (int i = 0; i < actual_m - 1; i++) subdiag[i] = beta_arr[i+1];
    if (actual_m > 0) subdiag[actual_m - 1] = 0.0;

    tql2(diag, subdiag, actual_m);

    int k_ret = (k_want < actual_m) ? k_want : actual_m;
    double *result = (double *)malloc(k_ret * sizeof(double));
    for (int i = 0; i < k_ret; i++) result[i] = diag[i];

    free(V);
    free(alpha);
    free(beta_arr);
    free(w);
    free(diag);
    free(subdiag);

    return result;
}

/* Wrapper matvecs */
static void matvec_Hphys(double *out, const double *in, const void *ctx) {
    apply_Hphys(out, in, (const HphysCtx *)ctx);
}

static void matvec_Hphys_restricted(double *out, const double *in, const void *ctx) {
    apply_Hphys_restricted(out, in, (const RestrictedCtx *)ctx);
}

static void matvec_Hpotts(double *out, const double *in, const void *ctx) {
    apply_Hpotts(out, in, (const PottsCtx *)ctx);
}

static void matvec_Hpotts_restricted(double *out, const double *in, const void *ctx) {
    apply_Hpotts_restricted(out, in, (const RestrictedPottsCtx *)ctx);
}

/* =========================================================================
 * DENSITY MEASURES
 * ========================================================================= */

/* Trit density: fraction of non-zero trits */
static double trit_density(int idx, int n_sites) {
    int nonzero = 0;
    for (int i = 0; i < n_sites; i++) {
        if (idx % 3 != 0) nonzero++;
        idx /= 3;
    }
    return (double)nonzero / n_sites;
}

/* =========================================================================
 * COMPARISON HELPER: sort doubles for NESS percentile computation
 * ========================================================================= */

static int cmp_double_desc(const void *a, const void *b) {
    double da = *(const double *)a;
    double db = *(const double *)b;
    if (da > db) return -1;
    if (da < db) return 1;
    return 0;
}

/* =========================================================================
 * RUN A SINGLE RESTRICTED ANALYSIS
 * ========================================================================= */

static void run_restricted_analysis(
    const char *label,
    const int *mask, int n_active,
    HphysCtx *hctx, PottsCtx *pctx,
    int n_cfg, int n_lanczos, int n_evals_want,
    double *unrestricted_evals)
{
    printf("\n  --- %s (n_active=%d / %d = %.1f%%) ---\n",
           label, n_active, n_cfg, 100.0 * n_active / n_cfg);

    if (n_active < 10) {
        printf("    Too few active states, skipping.\n");
        return;
    }

    clock_t t0, t1;

    /* Restricted H_phys */
    RestrictedCtx rctx;
    rctx.hctx = hctx;
    rctx.mask = mask;
    rctx.n_active = n_active;

    int lanczos_iters = n_lanczos;
    if (lanczos_iters > n_active) lanczos_iters = n_active;
    int evals_want = n_evals_want;
    if (evals_want > n_active) evals_want = n_active;

    t0 = clock();
    double *evals = lanczos(matvec_Hphys_restricted, &rctx, n_cfg, lanczos_iters,
                            evals_want, mask);
    t1 = clock();
    printf("    H_phys restricted Lanczos: %.2fs\n", (double)(t1-t0)/CLOCKS_PER_SEC);

    /* Find first positive eigenvalue (skip any near-zero from projection) */
    int i_gs = 0;
    /* The ground state of the restricted operator should be the smallest eigenvalue */
    double gs = evals[0];
    for (int i = 0; i < evals_want; i++) evals[i] -= gs;

    printf("    First %d eigenvalues (shifted):\n", evals_want < 10 ? evals_want : 10);
    for (int i = 0; i < evals_want && i < 10; i++) {
        printf("      E_%d = %.10f\n", i, evals[i]);
    }

    double gap = evals[1];
    if (gap > 1e-10 && evals_want >= 5) {
        printf("    Spectral gap E_1 = %.10f\n", gap);
        printf("    E_2/E_1 = %.8f\n", evals[2] / gap);
        printf("    E_3/E_1 = %.8f\n", evals[3] / gap);
        printf("    E_4/E_1 = %.8f\n", evals[4] / gap);
    }

    /* Restricted Potts for comparison */
    RestrictedPottsCtx rpctx;
    rpctx.pctx = pctx;
    rpctx.mask = mask;
    rpctx.n_active = n_active;

    t0 = clock();
    double *potts_evals = lanczos(matvec_Hpotts_restricted, &rpctx, n_cfg,
                                   lanczos_iters, evals_want, mask);
    t1 = clock();
    printf("    Potts restricted Lanczos: %.2fs\n", (double)(t1-t0)/CLOCKS_PER_SEC);

    double gs_p = potts_evals[0];
    for (int i = 0; i < evals_want; i++) potts_evals[i] -= gs_p;

    double gap_p = potts_evals[1];

    printf("    Potts first %d eigenvalues (shifted):\n", evals_want < 10 ? evals_want : 10);
    for (int i = 0; i < evals_want && i < 10; i++) {
        printf("      E_%d = %.10f\n", i, potts_evals[i]);
    }

    /* Ratio comparison */
    if (gap > 1e-10 && gap_p > 1e-10 && evals_want >= 5) {
        printf("\n    %-10s  %14s  %14s  %14s\n",
               "Ratio", "Soup(restr)", "Potts(restr)", "Difference");
        printf("    %s\n", "------------------------------------------------------");
        for (int i = 2; i < evals_want && i < 10; i++) {
            double r_s = evals[i] / gap;
            double r_p = potts_evals[i] / gap_p;
            printf("    E_%d/E_1    %14.6f  %14.6f  %14.6f\n",
                   i, r_s, r_p, r_s - r_p);
        }

        /* Also compare with unrestricted soup */
        double ur_gap = unrestricted_evals[1];
        if (ur_gap > 1e-10) {
            printf("\n    Comparison with UNRESTRICTED soup:\n");
            printf("    %-10s  %14s  %14s  %14s\n",
                   "Ratio", "Restricted", "Unrestricted", "Potts(restr)");
            printf("    %s\n", "------------------------------------------------------");
            for (int i = 2; i < evals_want && i < 10; i++) {
                double r_restr = evals[i] / gap;
                double r_unrestr = unrestricted_evals[i] / ur_gap;
                double r_p2 = potts_evals[i] / gap_p;
                printf("    E_%d/E_1    %14.6f  %14.6f  %14.6f\n",
                       i, r_restr, r_unrestr, r_p2);
            }
        }
    }

    free(evals);
    free(potts_evals);
}

/* =========================================================================
 * MAIN
 * ========================================================================= */

int main(int argc, char **argv) {
    printf("======================================================================\n");
    printf("CONDITIONAL SPECTRUM ANALYSIS: Density-Restricted H_phys\n");
    printf("======================================================================\n\n");

    int L = 5;
    double mu = 0.01;
    int n_sites = 2 * L;
    int n_cfg = pow3(n_sites);
    int n_lanczos = 250;
    int n_evals_want = 20;

    printf("Parameters:\n");
    printf("  L = %d, n_sites = %d, n_cfg = %d\n", L, n_sites, n_cfg);
    printf("  mu = %.4f\n", mu);
    printf("  Lanczos iterations = %d, eigenvalues wanted = %d\n", n_lanczos, n_evals_want);

    clock_t t0, t1;

    /* ===================================================================
     * Step 1: Build deterministic maps
     * =================================================================== */
    printf("\n[1] Building deterministic transition maps...\n");
    t0 = clock();
    int *map_fwd = (int *)malloc(n_cfg * sizeof(int));
    int *map_rev = (int *)malloc(n_cfg * sizeof(int));
    if (!map_fwd || !map_rev) { fprintf(stderr, "OOM\n"); exit(1); }
    build_det_maps(L, map_fwd, map_rev);
    t1 = clock();
    printf("  Done in %.2fs\n", (double)(t1 - t0) / CLOCKS_PER_SEC);

    /* ===================================================================
     * Step 2: Compute NESS
     * =================================================================== */
    printf("\n[2] Computing NESS via power iteration...\n");
    t0 = clock();
    double *ness = compute_ness(n_cfg, map_fwd, map_rev, n_sites, mu, 100000, 1e-14);
    t1 = clock();
    printf("  Done in %.2fs\n", (double)(t1 - t0) / CLOCKS_PER_SEC);

    /* NESS statistics */
    double max_ness = 0, min_ness_pos = 1.0;
    int n_nonzero = 0;
    double entropy = 0;
    for (int i = 0; i < n_cfg; i++) {
        if (ness[i] > max_ness) max_ness = ness[i];
        if (ness[i] > 1e-15) {
            if (ness[i] < min_ness_pos) min_ness_pos = ness[i];
            n_nonzero++;
            entropy -= ness[i] * log(ness[i]);
        }
    }
    printf("  NESS support: %d/%d states\n", n_nonzero, n_cfg);
    printf("  NESS max=%.6e, min(pos)=%.6e, ratio=%.2e\n",
           max_ness, min_ness_pos, max_ness/min_ness_pos);
    printf("  NESS entropy: %.4f (max: %.4f), effective dim: %.0f\n",
           entropy, log((double)n_cfg), exp(entropy));

    /* NESS weight of absorbing state (all zeros = idx 0) */
    printf("  NESS weight of all-zero state (idx=0): %.6e\n", ness[0]);

    /* Density distribution of NESS */
    printf("\n  NESS weight by trit density:\n");
    {
        double density_bins[11] = {0};  /* 0.0, 0.1, ..., 1.0 */
        int density_counts[11] = {0};
        for (int i = 0; i < n_cfg; i++) {
            double rho = trit_density(i, n_sites);
            int bin = (int)(rho * 10 + 0.5);
            if (bin > 10) bin = 10;
            density_bins[bin] += ness[i];
            density_counts[bin]++;
        }
        printf("    %-8s  %10s  %10s  %10s\n",
               "rho", "#states", "NESS_wt", "avg_wt");
        for (int b = 0; b <= 10; b++) {
            double rho_val = b / 10.0;
            double avg = density_counts[b] > 0 ?
                         density_bins[b] / density_counts[b] : 0;
            printf("    %-8.1f  %10d  %10.6f  %10.2e\n",
                   rho_val, density_counts[b], density_bins[b], avg);
        }
    }

    /* ===================================================================
     * Step 3: Prepare similarity transform
     * =================================================================== */
    printf("\n[3] Preparing similarity transform arrays...\n");
    double *sqrt_pi = (double *)malloc(n_cfg * sizeof(double));
    double *inv_sqrt_pi = (double *)malloc(n_cfg * sizeof(double));
    for (int i = 0; i < n_cfg; i++) {
        double p = (ness[i] > 1e-30) ? ness[i] : 1e-30;
        sqrt_pi[i] = sqrt(p);
        inv_sqrt_pi[i] = 1.0 / sqrt_pi[i];
    }

    HphysCtx hctx;
    hctx.n_cfg = n_cfg;
    hctx.n_sites = n_sites;
    hctx.mu = mu;
    hctx.map_fwd = map_fwd;
    hctx.map_rev = map_rev;
    hctx.sqrt_pi = sqrt_pi;
    hctx.inv_sqrt_pi = inv_sqrt_pi;

    /* Best-fit Potts parameters from previous runs */
    PottsCtx pctx;
    pctx.n_sites = n_sites;
    pctx.n_cfg = n_cfg;
    pctx.J = 1.0;
    pctx.K = 1.0;  /* will scan below */

    /* ===================================================================
     * Step 4: Unrestricted H_phys spectrum (baseline)
     * =================================================================== */
    printf("\n[4] Unrestricted H_phys spectrum (baseline)...\n");
    t0 = clock();
    double *evals_unrestricted = lanczos(matvec_Hphys, &hctx, n_cfg,
                                          n_lanczos, n_evals_want, NULL);
    t1 = clock();
    printf("  Done in %.2fs\n", (double)(t1-t0)/CLOCKS_PER_SEC);

    double gs = evals_unrestricted[0];
    for (int i = 0; i < n_evals_want; i++) evals_unrestricted[i] -= gs;

    printf("  First 10 eigenvalues (shifted):\n");
    for (int i = 0; i < 10 && i < n_evals_want; i++) {
        printf("    E_%d = %.10f\n", i, evals_unrestricted[i]);
    }

    double gap_ur = evals_unrestricted[1];
    if (gap_ur > 1e-10) {
        printf("  E_2/E_1 = %.8f\n", evals_unrestricted[2] / gap_ur);
        printf("  E_3/E_1 = %.8f\n", evals_unrestricted[3] / gap_ur);
    }

    /* ===================================================================
     * Step 5: Find best Potts beta for unrestricted comparison
     * =================================================================== */
    printf("\n[5] Finding best Potts beta (unrestricted)...\n");
    {
        double betas[] = {0.1, 0.5, 1.0, 1.5, 2.0, 3.0, 5.0};
        int n_beta = sizeof(betas) / sizeof(betas[0]);
        double best_diff = 1e10;
        double best_beta = 1.0;

        for (int bi = 0; bi < n_beta; bi++) {
            pctx.K = betas[bi];
            double *ep = lanczos(matvec_Hpotts, &pctx, n_cfg, n_lanczos,
                                  n_evals_want, NULL);
            double gs_p = ep[0];
            for (int i = 0; i < n_evals_want; i++) ep[i] -= gs_p;

            double diff = 1e10;
            if (ep[1] > 1e-10 && gap_ur > 1e-10) {
                diff = fabs(evals_unrestricted[2]/gap_ur - ep[2]/ep[1]);
            }
            printf("    beta=%.1f: E2/E1=%.6f, |diff|=%.6f\n",
                   betas[bi], ep[1] > 1e-10 ? ep[2]/ep[1] : 0.0, diff);

            if (diff < best_diff) {
                best_diff = diff;
                best_beta = betas[bi];
            }
            free(ep);
        }
        printf("  Best beta = %.1f\n", best_beta);
        pctx.K = best_beta;
    }

    /* ===================================================================
     * Step 6: METHOD A -- Trit density threshold scan
     * =================================================================== */
    printf("\n======================================================================\n");
    printf("METHOD A: TRIT DENSITY THRESHOLD\n");
    printf("======================================================================\n");
    printf("rho(cfg) = fraction of non-zero trits\n");
    printf("Mask: keep configurations with rho > rho_threshold\n\n");

    /* Precompute trit densities */
    double *densities = (double *)malloc(n_cfg * sizeof(double));
    for (int i = 0; i < n_cfg; i++) {
        densities[i] = trit_density(i, n_sites);
    }

    double rho_thresholds[] = {0.1, 0.2, 0.3, 0.4, 0.5};
    int n_rho_th = sizeof(rho_thresholds) / sizeof(rho_thresholds[0]);

    int *mask = (int *)malloc(n_cfg * sizeof(int));

    for (int ti = 0; ti < n_rho_th; ti++) {
        double rho_th = rho_thresholds[ti];
        int n_active = 0;

        for (int i = 0; i < n_cfg; i++) {
            mask[i] = (densities[i] > rho_th) ? 1 : 0;
            if (mask[i]) n_active++;
        }

        /* Also compute NESS weight in the active set */
        double ness_wt_active = 0;
        for (int i = 0; i < n_cfg; i++) {
            if (mask[i]) ness_wt_active += ness[i];
        }

        char label[128];
        snprintf(label, sizeof(label), "rho_threshold=%.1f (NESS wt=%.4f)", rho_th, ness_wt_active);

        run_restricted_analysis(label, mask, n_active, &hctx, &pctx,
                                n_cfg, n_lanczos, n_evals_want,
                                evals_unrestricted);
    }

    /* ===================================================================
     * Step 7: METHOD B -- NESS weight percentile threshold
     * =================================================================== */
    printf("\n======================================================================\n");
    printf("METHOD B: NESS WEIGHT PERCENTILE THRESHOLD\n");
    printf("======================================================================\n");
    printf("Keep top X%% of states by NESS probability mass\n\n");

    /* Sort NESS weights to find thresholds */
    double *ness_sorted = (double *)malloc(n_cfg * sizeof(double));
    memcpy(ness_sorted, ness, n_cfg * sizeof(double));
    qsort(ness_sorted, n_cfg, sizeof(double), cmp_double_desc);

    double percentiles[] = {50.0, 25.0, 10.0, 5.0};
    int n_pct = sizeof(percentiles) / sizeof(percentiles[0]);

    for (int pi = 0; pi < n_pct; pi++) {
        double pct = percentiles[pi];

        /* Find threshold: cumulative weight >= (1 - pct/100) means we
         * keep states with weight above this threshold */
        double target_weight = pct / 100.0;
        double cumsum = 0;
        double weight_threshold = 0;
        int n_active = 0;

        for (int i = 0; i < n_cfg; i++) {
            cumsum += ness_sorted[i];
            if (cumsum >= target_weight) {
                weight_threshold = ness_sorted[i];
                n_active = i + 1;
                break;
            }
        }

        /* Build mask: keep states with ness >= weight_threshold */
        int actual_active = 0;
        for (int i = 0; i < n_cfg; i++) {
            mask[i] = (ness[i] >= weight_threshold) ? 1 : 0;
            if (mask[i]) actual_active++;
        }

        /* Verify weight coverage */
        double covered_weight = 0;
        for (int i = 0; i < n_cfg; i++) {
            if (mask[i]) covered_weight += ness[i];
        }

        char label[128];
        snprintf(label, sizeof(label),
                 "Top %.0f%% NESS (threshold=%.2e, coverage=%.4f)",
                 pct, weight_threshold, covered_weight);

        run_restricted_analysis(label, mask, actual_active, &hctx, &pctx,
                                n_cfg, n_lanczos, n_evals_want,
                                evals_unrestricted);
    }

    free(ness_sorted);

    /* ===================================================================
     * Step 8: SUMMARY TABLE
     * =================================================================== */
    printf("\n======================================================================\n");
    printf("SUMMARY\n");
    printf("======================================================================\n\n");

    printf("Question: Does removing low-density / low-NESS states reveal\n");
    printf("          Z_3 Potts spectral ratios?\n\n");

    printf("The unrestricted E_2/E_1 ratio is: %.6f\n",
           gap_ur > 1e-10 ? evals_unrestricted[2] / gap_ur : 0.0);
    printf("For Z_3 Potts on n_sites=%d ring, E_2/E_1 depends on beta.\n\n", n_sites);

    printf("Key diagnostic: if restriction progressively IMPROVES the match\n");
    printf("to Potts ratios, the absorbing state / DP dynamics are indeed\n");
    printf("contaminating the spectrum. If not, the non-Potts behavior is\n");
    printf("intrinsic to the active phase as well.\n\n");

    printf("Interpretation guide:\n");
    printf("  - If restricted E_2/E_1 -> Potts E_2/E_1: DP contamination confirmed\n");
    printf("  - If restricted E_2/E_1 stays non-Potts: soup has genuinely different\n");
    printf("    universality class even in the active sector\n");
    printf("  - If restriction makes ratios WORSE: the Potts-like structure (if any)\n");
    printf("    requires the full Hilbert space including absorbing-state vicinity\n");

    /* ===================================================================
     * Cleanup
     * =================================================================== */
    free(map_fwd);
    free(map_rev);
    free(ness);
    free(sqrt_pi);
    free(inv_sqrt_pi);
    free(evals_unrestricted);
    free(densities);
    free(mask);

    printf("\n======================================================================\n");
    printf("DONE\n");
    printf("======================================================================\n");

    return 0;
}
