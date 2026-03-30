/*
 * Constructive RG Map: Soup Doi-Peliti Hamiltonian → Z₃ Potts
 * =============================================================
 *
 * Investigates whether a block-spin RG transformation can map the soup's
 * NESS-symmetrized Doi-Peliti Hamiltonian H_phys to the Z₃ Potts Hamiltonian.
 *
 * Strategy:
 *   1. Build H_phys for L=2 (81×81) and L=3 (729×729)
 *   2. Construct block-spin RG projection R: 3^(2L) → 3^(2(L-1))
 *      using majority-vote and decimation coarse-graining
 *   3. Compute R·H_phys·R^† and compare eigenspectrum with H_Potts
 *   4. Extract effective coupling and proportionality constant
 *
 * Compile: cc -O3 -o rg_map_construction rg_map_construction.c -framework Accelerate -lm
 * Run:     ./rg_map_construction
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>
#include <Accelerate/Accelerate.h>

#define Z3 3
#define MAX_VM_STEPS 729

/* =========================================================================
 * VM IMPLEMENTATION (matches soup.c exactly)
 * ========================================================================= */

static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
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
 * CONFIGURATION SPACE UTILITIES
 * ========================================================================= */

static int pow3(int n) {
    int r = 1;
    for (int i = 0; i < n; i++) r *= 3;
    return r;
}

static void idx_to_trits(int idx, uint8_t *trits, int n) {
    for (int i = n - 1; i >= 0; i--) {
        trits[i] = idx % 3;
        idx /= 3;
    }
}

static int trits_to_idx(const uint8_t *trits, int n) {
    int idx = 0;
    for (int i = 0; i < n; i++) idx = idx * 3 + trits[i];
    return idx;
}

/* =========================================================================
 * TRANSITION MATRIX CONSTRUCTION (from spectral_matching.c)
 * ========================================================================= */

static void build_det_maps(int L, int *map_fwd, int *map_rev) {
    int n_prog = pow3(L);
    int n_cfg = n_prog * n_prog;
    int tape_len = 2 * L;
    uint8_t *tape = (uint8_t *)malloc(tape_len);

    for (int src = 0; src < n_cfg; src++) {
        int ia = src / n_prog, ib = src % n_prog;

        idx_to_trits(ia, tape, L);
        idx_to_trits(ib, tape + L, L);
        execute_tape(tape, tape_len, MAX_VM_STEPS);
        int new_a = trits_to_idx(tape, L);
        int new_b = trits_to_idx(tape + L, L);
        map_fwd[src] = new_a * n_prog + new_b;

        idx_to_trits(ib, tape, L);
        idx_to_trits(ia, tape + L, L);
        execute_tape(tape, tape_len, MAX_VM_STEPS);
        int first = trits_to_idx(tape, L);
        int second = trits_to_idx(tape + L, L);
        map_rev[src] = second * n_prog + first;
    }

    free(tape);
}

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
 * BUILD FULL DENSE MATRICES
 * ========================================================================= */

static double *build_full_T(int n_cfg, const int *map_fwd, const int *map_rev,
                             int n_sites, double mu) {
    double *T_full = (double *)calloc(n_cfg * n_cfg, sizeof(double));
    double *e_j = (double *)calloc(n_cfg, sizeof(double));
    double *Tej = (double *)malloc(n_cfg * sizeof(double));

    for (int j = 0; j < n_cfg; j++) {
        memset(e_j, 0, n_cfg * sizeof(double));
        e_j[j] = 1.0;
        apply_T(Tej, e_j, n_cfg, map_fwd, map_rev, n_sites, mu);
        for (int i = 0; i < n_cfg; i++) {
            T_full[i * n_cfg + j] = Tej[i];
        }
    }

    free(e_j);
    free(Tej);
    return T_full;
}

static double *build_H_phys(int n_cfg, const double *T_full, const double *ness,
                             double *out_db_violation) {
    double *H_phys = (double *)calloc(n_cfg * n_cfg, sizeof(double));

    double *sqrt_pi = (double *)malloc(n_cfg * sizeof(double));
    double *inv_sqrt_pi = (double *)malloc(n_cfg * sizeof(double));
    for (int i = 0; i < n_cfg; i++) {
        double p = (ness[i] > 1e-30) ? ness[i] : 1e-30;
        sqrt_pi[i] = sqrt(p);
        inv_sqrt_pi[i] = 1.0 / sqrt_pi[i];
    }

    double norm_anti = 0, norm_full = 0;

    for (int i = 0; i < n_cfg; i++) {
        for (int j = 0; j < n_cfg; j++) {
            double H_ij = (i == j ? 1.0 : 0.0) - T_full[i * n_cfg + j];
            double H_ji = (i == j ? 1.0 : 0.0) - T_full[j * n_cfg + i];

            double Ht_ij = inv_sqrt_pi[i] * H_ij * sqrt_pi[j];
            double Ht_ji = inv_sqrt_pi[j] * H_ji * sqrt_pi[i];

            H_phys[i * n_cfg + j] = 0.5 * (Ht_ij + Ht_ji);

            double anti = Ht_ij - Ht_ji;
            norm_anti += anti * anti;
            norm_full += Ht_ij * Ht_ij;
        }
    }

    if (out_db_violation)
        *out_db_violation = sqrt(norm_anti / norm_full);

    free(sqrt_pi);
    free(inv_sqrt_pi);
    return H_phys;
}

/* =========================================================================
 * Z₃ POTTS HAMILTONIAN
 * ========================================================================= */

static double *build_potts_hamiltonian(int n_sites, double J, double K) {
    int n_cfg = pow3(n_sites);
    double *H = (double *)calloc(n_cfg * n_cfg, sizeof(double));

    uint8_t *config_i = (uint8_t *)malloc(n_sites);
    uint8_t *config_j = (uint8_t *)malloc(n_sites);

    for (int idx = 0; idx < n_cfg; idx++) {
        idx_to_trits(idx, config_i, n_sites);

        /* Diagonal: -K * sum_bond delta(s_i, s_{i+1}) with PBC */
        double V = 0;
        for (int s = 0; s < n_sites; s++) {
            int next = (s + 1) % n_sites;
            if (config_i[s] == config_i[next]) V -= K;
        }
        H[idx * n_cfg + idx] += V;

        /* Off-diagonal: -J * (tau + tau^dag) at each site */
        for (int site = 0; site < n_sites; site++) {
            memcpy(config_j, config_i, n_sites);
            config_j[site] = (config_i[site] + 1) % 3;
            int jdx = trits_to_idx(config_j, n_sites);
            H[idx * n_cfg + jdx] -= J;

            config_j[site] = (config_i[site] + 2) % 3;
            jdx = trits_to_idx(config_j, n_sites);
            H[idx * n_cfg + jdx] -= J;
        }
    }

    free(config_i);
    free(config_j);
    return H;
}

/* =========================================================================
 * EIGENDECOMPOSITION (LAPACK via Accelerate)
 * ========================================================================= */

static double *eigenvalues_symmetric(double *A, int n) {
    double *w = (double *)malloc(n * sizeof(double));
    int lwork = 3 * n + 1;
    double *work = (double *)malloc(lwork * sizeof(double));
    int info;
    char jobz = 'N', uplo = 'U';

    dsyev_(&jobz, &uplo, &n, A, &n, w, work, &lwork, &info);
    if (info != 0) fprintf(stderr, "dsyev failed with info=%d\n", info);

    free(work);
    return w;
}

static double *eigensystem_symmetric(double *A, int n, double **out_vectors) {
    double *w = (double *)malloc(n * sizeof(double));
    int lwork = 3 * n + 1;
    double *work = (double *)malloc(lwork * sizeof(double));
    int info;
    char jobz = 'V', uplo = 'U';

    dsyev_(&jobz, &uplo, &n, A, &n, w, work, &lwork, &info);
    if (info != 0) fprintf(stderr, "dsyev failed with info=%d\n", info);

    free(work);
    if (out_vectors) *out_vectors = A;  /* A now contains eigenvectors in columns */
    return w;
}

/* =========================================================================
 * BLOCK-SPIN RG TRANSFORMATION
 * ========================================================================= */

/*
 * Strategy 1: DECIMATION
 * Keep every other trit pair. For tape {t_0,...,t_{2L-1}} representing
 * two L-trit programs, we decimate by keeping trits at even positions.
 *
 * For L=3 → L=2: keep trits {0,1,3,4} from {0,1,2,3,4,5}
 *   i.e., drop the last trit of each program
 *
 * R is a (n_coarse × n_fine) matrix where:
 *   R[coarse, fine] = 1 if fine projects to coarse, 0 otherwise
 * Each fine state maps to exactly one coarse state, so R has one 1 per column.
 * Normalize rows: R[c,f] = 1/sqrt(count_c) where count_c = number of fine
 * states mapping to coarse state c.
 */

/* Decimation: drop the last trit of each L-trit program */
static void build_decimation_R(int L_fine, int L_coarse,
                                double **out_R, int *out_n_fine, int *out_n_coarse) {
    int n_sites_fine = 2 * L_fine;
    int n_sites_coarse = 2 * L_coarse;
    int n_fine = pow3(n_sites_fine);
    int n_coarse = pow3(n_sites_coarse);

    *out_n_fine = n_fine;
    *out_n_coarse = n_coarse;

    /* Count how many fine states map to each coarse state */
    int *count = (int *)calloc(n_coarse, sizeof(int));
    int *fine_to_coarse = (int *)malloc(n_fine * sizeof(int));

    uint8_t *trits_fine = (uint8_t *)malloc(n_sites_fine);
    uint8_t *trits_coarse = (uint8_t *)malloc(n_sites_coarse);

    for (int f = 0; f < n_fine; f++) {
        idx_to_trits(f, trits_fine, n_sites_fine);

        /*
         * Decimation map: for two programs of length L_fine each,
         * keep the first L_coarse trits of each program.
         * Fine tape: [a_0,...,a_{L_fine-1}, b_0,...,b_{L_fine-1}]
         * Coarse tape: [a_0,...,a_{L_coarse-1}, b_0,...,b_{L_coarse-1}]
         */
        for (int i = 0; i < L_coarse; i++) {
            trits_coarse[i] = trits_fine[i];                    /* first program */
            trits_coarse[L_coarse + i] = trits_fine[L_fine + i]; /* second program */
        }

        int c = trits_to_idx(trits_coarse, n_sites_coarse);
        fine_to_coarse[f] = c;
        count[c]++;
    }

    /* Build R matrix (n_coarse × n_fine) with normalized rows */
    double *R = (double *)calloc(n_coarse * n_fine, sizeof(double));
    for (int f = 0; f < n_fine; f++) {
        int c = fine_to_coarse[f];
        R[c * n_fine + f] = 1.0 / sqrt((double)count[c]);
    }

    *out_R = R;

    free(count);
    free(fine_to_coarse);
    free(trits_fine);
    free(trits_coarse);
}

/*
 * Strategy 2: MAJORITY VOTE
 * Group trits into blocks and take the majority value.
 * For L=3 → effective L=2: group consecutive trits pairwise,
 * but since 3→2 isn't evenly divisible, we use a different scheme:
 *
 * For each program of L trits, group into ceil(L/2) blocks of 2 trits
 * (last block may have 1 trit). The coarse trit is the majority/first value.
 *
 * Actually for L=3→L=2, we can group trits {0,1} → one trit (majority of 2),
 * and trit {2} → one trit (keep as is). But majority of 2 is ambiguous.
 *
 * Simpler: use "block averaging" where we group 3^1 fine states into 1 coarse
 * state by summing over the dropped trit. This gives a soft coarse-graining.
 */

/* Majority vote for 2 trits (with tie-breaking: keep first) */
static uint8_t majority2(uint8_t a, uint8_t b) {
    if (a == b) return a;
    return a; /* tie-break: keep first */
}

static void build_majority_R(int L_fine, int L_coarse,
                               double **out_R, int *out_n_fine, int *out_n_coarse) {
    int n_sites_fine = 2 * L_fine;
    int n_sites_coarse = 2 * L_coarse;
    int n_fine = pow3(n_sites_fine);
    int n_coarse = pow3(n_sites_coarse);

    *out_n_fine = n_fine;
    *out_n_coarse = n_coarse;

    int *count = (int *)calloc(n_coarse, sizeof(int));
    int *fine_to_coarse = (int *)malloc(n_fine * sizeof(int));

    uint8_t *trits_fine = (uint8_t *)malloc(n_sites_fine);
    uint8_t *trits_coarse = (uint8_t *)malloc(n_sites_coarse);

    for (int f = 0; f < n_fine; f++) {
        idx_to_trits(f, trits_fine, n_sites_fine);

        /*
         * For L_fine=3 → L_coarse=2:
         * Program A: trits {0,1,2} → coarse {majority(0,1), 2}
         * Program B: trits {3,4,5} → coarse {majority(3,4), 5}
         *
         * General: first L_coarse-1 coarse trits from majority pairs,
         * last coarse trit = last fine trit.
         */
        for (int prog = 0; prog < 2; prog++) {
            int f_off = prog * L_fine;
            int c_off = prog * L_coarse;

            /* Pair consecutive trits for majority */
            int fi = 0, ci = 0;
            while (ci < L_coarse && fi < L_fine) {
                if (fi + 1 < L_fine && ci + 1 < L_coarse) {
                    /* Take majority of pair */
                    trits_coarse[c_off + ci] = majority2(trits_fine[f_off + fi],
                                                          trits_fine[f_off + fi + 1]);
                    fi += 2;
                    ci += 1;
                } else {
                    /* Keep remaining trits directly */
                    trits_coarse[c_off + ci] = trits_fine[f_off + fi];
                    fi += 1;
                    ci += 1;
                }
            }
            /* If we still have fine trits left, the last coarse trit absorbs the last fine trit */
            if (fi < L_fine && ci == L_coarse) {
                /* Already done */
            }
        }

        int c = trits_to_idx(trits_coarse, n_sites_coarse);
        fine_to_coarse[f] = c;
        count[c]++;
    }

    double *R = (double *)calloc(n_coarse * n_fine, sizeof(double));
    for (int f = 0; f < n_fine; f++) {
        int c = fine_to_coarse[f];
        R[c * n_fine + f] = 1.0 / sqrt((double)count[c]);
    }

    *out_R = R;

    free(count);
    free(fine_to_coarse);
    free(trits_fine);
    free(trits_coarse);
}

/*
 * Strategy 3: NESS-WEIGHTED PROJECTION
 * Same as decimation but weight by sqrt(pi_fine / pi_coarse_block)
 * This preserves the NESS structure under coarse-graining.
 */
static void build_ness_weighted_R(int L_fine, int L_coarse, const double *ness,
                                    double **out_R, int *out_n_fine, int *out_n_coarse) {
    int n_sites_fine = 2 * L_fine;
    int n_sites_coarse = 2 * L_coarse;
    int n_fine = pow3(n_sites_fine);
    int n_coarse = pow3(n_sites_coarse);

    *out_n_fine = n_fine;
    *out_n_coarse = n_coarse;

    int *fine_to_coarse = (int *)malloc(n_fine * sizeof(int));
    double *block_pi = (double *)calloc(n_coarse, sizeof(double));

    uint8_t *trits_fine = (uint8_t *)malloc(n_sites_fine);
    uint8_t *trits_coarse = (uint8_t *)malloc(n_sites_coarse);

    for (int f = 0; f < n_fine; f++) {
        idx_to_trits(f, trits_fine, n_sites_fine);
        for (int i = 0; i < L_coarse; i++) {
            trits_coarse[i] = trits_fine[i];
            trits_coarse[L_coarse + i] = trits_fine[L_fine + i];
        }
        int c = trits_to_idx(trits_coarse, n_sites_coarse);
        fine_to_coarse[f] = c;
        block_pi[c] += ness[f];
    }

    double *R = (double *)calloc(n_coarse * n_fine, sizeof(double));
    for (int f = 0; f < n_fine; f++) {
        int c = fine_to_coarse[f];
        double bp = (block_pi[c] > 1e-30) ? block_pi[c] : 1e-30;
        R[c * n_fine + f] = sqrt(ness[f] / bp);
    }

    *out_R = R;

    free(fine_to_coarse);
    free(block_pi);
    free(trits_fine);
    free(trits_coarse);
}

/* =========================================================================
 * MATRIX OPERATIONS
 * ========================================================================= */

/* Compute C = A * B where A is (m × k), B is (k × n) → C is (m × n) */
static void mat_mul(const double *A, const double *B, double *C,
                    int m, int k, int n) {
    /* Use BLAS dgemm for efficiency */
    char transA = 'N', transB = 'N';
    double alpha = 1.0, beta = 0.0;
    /* BLAS uses column-major; our matrices are row-major.
     * C_row = A_row * B_row is equivalent to C_col^T = B_col^T * A_col^T
     * i.e., dgemm('N','N', n, m, k, 1, B^T, n, A^T, k, 0, C^T, n)
     * But since we store row-major, the memory layout IS the column-major transpose.
     * So: dgemm('N','N', n, m, k, alpha, B, n, A, k, beta, C, n) */
    cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasNoTrans,
                m, n, k, alpha, A, k, B, n, beta, C, n);
}

/* Compute C = A * B^T where A is (m × k), B is (n × k) → C is (m × n) */
static void mat_mul_ABt(const double *A, const double *B, double *C,
                        int m, int k, int n) {
    cblas_dgemm(CblasRowMajor, CblasNoTrans, CblasTrans,
                m, n, k, 1.0, A, k, B, k, 0.0, C, n);
}

/* =========================================================================
 * RG ANALYSIS
 * ========================================================================= */

static void analyze_rg_map(const char *name, int L_fine,
                            const double *H_phys_fine, int n_fine,
                            const double *R, int n_coarse,
                            double mu) {
    printf("\n  --- RG Strategy: %s ---\n", name);
    printf("    Fine: %d states, Coarse: %d states\n", n_fine, n_coarse);

    /* Verify R is well-formed: R * R^T should be approximately I */
    double *RRt = (double *)malloc(n_coarse * n_coarse * sizeof(double));
    mat_mul_ABt(R, R, RRt, n_coarse, n_fine, n_coarse);

    double max_offdiag = 0, min_diag = 1e30, max_diag = 0;
    for (int i = 0; i < n_coarse; i++) {
        for (int j = 0; j < n_coarse; j++) {
            if (i == j) {
                if (RRt[i * n_coarse + j] < min_diag) min_diag = RRt[i * n_coarse + j];
                if (RRt[i * n_coarse + j] > max_diag) max_diag = RRt[i * n_coarse + j];
            } else {
                double v = fabs(RRt[i * n_coarse + j]);
                if (v > max_offdiag) max_offdiag = v;
            }
        }
    }
    printf("    R*R^T: diag=[%.6f, %.6f], max_offdiag=%.6e\n",
           min_diag, max_diag, max_offdiag);
    free(RRt);

    /* Compute H_RG = R * H_phys * R^T (n_coarse × n_coarse) */
    double *RH = (double *)malloc(n_coarse * n_fine * sizeof(double));
    mat_mul(R, H_phys_fine, RH, n_coarse, n_fine, n_fine);

    double *H_RG = (double *)malloc(n_coarse * n_coarse * sizeof(double));
    mat_mul_ABt(RH, R, H_RG, n_coarse, n_fine, n_coarse);
    free(RH);

    /* Symmetrize H_RG (should be close to symmetric already) */
    double max_asym = 0;
    for (int i = 0; i < n_coarse; i++) {
        for (int j = i + 1; j < n_coarse; j++) {
            double d = fabs(H_RG[i * n_coarse + j] - H_RG[j * n_coarse + i]);
            if (d > max_asym) max_asym = d;
            double avg = 0.5 * (H_RG[i * n_coarse + j] + H_RG[j * n_coarse + i]);
            H_RG[i * n_coarse + j] = avg;
            H_RG[j * n_coarse + i] = avg;
        }
    }
    printf("    H_RG asymmetry: %.6e\n", max_asym);

    /* Diagonalize H_RG */
    double *H_RG_copy = (double *)malloc(n_coarse * n_coarse * sizeof(double));
    memcpy(H_RG_copy, H_RG, n_coarse * n_coarse * sizeof(double));
    double *evals_rg = eigenvalues_symmetric(H_RG_copy, n_coarse);
    free(H_RG_copy);

    /* Shift ground state to 0 */
    double gs_rg = evals_rg[0];
    for (int i = 0; i < n_coarse; i++) evals_rg[i] -= gs_rg;

    printf("\n    H_RG eigenvalues (shifted, first 20):\n");
    for (int i = 0; i < 20 && i < n_coarse; i++) {
        printf("      E_%d = %.8f\n", i, evals_rg[i]);
    }

    double gap_rg = (n_coarse > 1) ? evals_rg[1] : 0;
    printf("    RG spectral gap: %.8f\n", gap_rg);

    /* Now compare with Potts at various J, K values */
    printf("\n    Searching for best Potts match...\n");

    int n_sites_coarse = 2 * (L_fine - 1);

    /* Scan over J and K independently */
    double best_J = 0, best_K = 0, best_score = 1e30;
    double J_vals[] = {0.01, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0};
    double K_vals[] = {0.0, 0.01, 0.05, 0.1, 0.2, 0.5, 1.0, 2.0, 5.0};
    int nJ = sizeof(J_vals) / sizeof(J_vals[0]);
    int nK = sizeof(K_vals) / sizeof(K_vals[0]);

    for (int ji = 0; ji < nJ; ji++) {
        for (int ki = 0; ki < nK; ki++) {
            double J = J_vals[ji], K = K_vals[ki];
            double *H_potts = build_potts_hamiltonian(n_sites_coarse, J, K);
            double *evals_p = eigenvalues_symmetric(H_potts, n_coarse);
            free(H_potts);

            double gs_p = evals_p[0];
            for (int i = 0; i < n_coarse; i++) evals_p[i] -= gs_p;

            /* Score: compare gap-normalized ratios for first few levels */
            double gap_p = evals_p[1];
            if (gap_p < 1e-10 || gap_rg < 1e-10) {
                free(evals_p);
                continue;
            }

            double score = 0;
            int n_compare = (n_coarse < 10) ? n_coarse : 10;
            for (int i = 2; i < n_compare; i++) {
                double r_rg = evals_rg[i] / gap_rg;
                double r_p = evals_p[i] / gap_p;
                score += (r_rg - r_p) * (r_rg - r_p);
            }
            score = sqrt(score / (n_compare - 2));

            if (score < best_score) {
                best_score = score;
                best_J = J;
                best_K = K;
            }

            free(evals_p);
        }
    }

    printf("    Best Potts parameters: J=%.4f, K=%.4f (RMS ratio error=%.6f)\n",
           best_J, best_K, best_score);

    /* Fine-grained search around best */
    {
        double J0 = best_J, K0 = best_K;
        for (int refine = 0; refine < 3; refine++) {
            double dJ = J0 * 0.3, dK = (K0 > 0.001) ? K0 * 0.3 : 0.01;
            double local_best_J = J0, local_best_K = K0, local_best_score = 1e30;

            for (int ji = -5; ji <= 5; ji++) {
                for (int ki = -5; ki <= 5; ki++) {
                    double J = J0 + ji * dJ / 5;
                    double K = K0 + ki * dK / 5;
                    if (J <= 0) continue;
                    if (K < 0) K = 0;

                    double *H_potts = build_potts_hamiltonian(n_sites_coarse, J, K);
                    double *evals_p = eigenvalues_symmetric(H_potts, n_coarse);
                    free(H_potts);

                    double gs_p = evals_p[0];
                    for (int i = 0; i < n_coarse; i++) evals_p[i] -= gs_p;

                    double gap_p = evals_p[1];
                    if (gap_p < 1e-10) { free(evals_p); continue; }

                    double score = 0;
                    int n_compare = (n_coarse < 10) ? n_coarse : 10;
                    for (int i = 2; i < n_compare; i++) {
                        double r_rg = evals_rg[i] / gap_rg;
                        double r_p = evals_p[i] / gap_p;
                        score += (r_rg - r_p) * (r_rg - r_p);
                    }
                    score = sqrt(score / (n_compare - 2));

                    if (score < local_best_score) {
                        local_best_score = score;
                        local_best_J = J;
                        local_best_K = K;
                    }

                    free(evals_p);
                }
            }
            J0 = local_best_J;
            K0 = local_best_K;
            best_score = local_best_score;
        }
        best_J = J0;
        best_K = K0;
    }

    printf("    Refined Potts parameters: J=%.6f, K=%.6f (RMS ratio error=%.6f)\n",
           best_J, best_K, best_score);

    /* Detailed comparison at best parameters */
    {
        double *H_potts = build_potts_hamiltonian(n_sites_coarse, best_J, best_K);
        double *evals_p = eigenvalues_symmetric(H_potts, n_coarse);
        free(H_potts);

        double gs_p = evals_p[0];
        for (int i = 0; i < n_coarse; i++) evals_p[i] -= gs_p;
        double gap_p = evals_p[1];

        /* Proportionality constant: gap_rg / gap_potts */
        double f_prop = (gap_p > 1e-10) ? gap_rg / gap_p : 0;

        printf("\n    Proportionality constant f = gap_RG / gap_Potts = %.6f\n", f_prop);
        printf("    (Compare with f_rep ~ 7.2 from soup dictionary)\n");
        printf("    gap_RG = %.8f, gap_Potts = %.8f\n", gap_rg, gap_p);

        printf("\n    %6s  %14s  %14s  %14s  %14s  %10s\n",
               "Level", "E_RG", "E_Potts", "E_RG/gap_RG", "E_P/gap_P", "Ratio_err");
        printf("    %s\n",
               "--------------------------------------------------------------------------");
        int n_show = (n_coarse < 20) ? n_coarse : 20;
        for (int i = 0; i < n_show; i++) {
            double r_rg = (gap_rg > 1e-10) ? evals_rg[i] / gap_rg : 0;
            double r_p = (gap_p > 1e-10) ? evals_p[i] / gap_p : 0;
            double err = (r_p > 1e-10) ? fabs(r_rg - r_p) / r_p : fabs(r_rg - r_p);
            printf("    %6d  %14.8f  %14.8f  %14.8f  %14.8f  %10.4f%%\n",
                   i, evals_rg[i], evals_p[i], r_rg, r_p, err * 100);
        }

        /* Also compare absolute eigenvalues with rescaling */
        printf("\n    Absolute comparison with rescaling by f=%.6f:\n", f_prop);
        printf("    %6s  %14s  %14s  %10s\n",
               "Level", "E_RG", "f*E_Potts", "Rel_err");
        printf("    %s\n", "------------------------------------------------");
        for (int i = 0; i < n_show; i++) {
            double scaled = f_prop * evals_p[i];
            double err = (evals_rg[i] > 1e-10) ?
                         fabs(evals_rg[i] - scaled) / evals_rg[i] :
                         fabs(evals_rg[i] - scaled);
            printf("    %6d  %14.8f  %14.8f  %10.4f%%\n",
                   i, evals_rg[i], scaled, err * 100);
        }

        free(evals_p);
    }

    /* Also compare directly with H_RG matrix structure */
    printf("\n    Matrix structure analysis of H_RG:\n");
    {
        /* How much of H_RG is diagonal vs off-diagonal? */
        double diag_norm = 0, offdiag_norm = 0;
        for (int i = 0; i < n_coarse; i++) {
            for (int j = 0; j < n_coarse; j++) {
                double v = H_RG[i * n_coarse + j];
                if (i == j) diag_norm += v * v;
                else offdiag_norm += v * v;
            }
        }
        printf("    ||diag(H_RG)||_F = %.6f\n", sqrt(diag_norm));
        printf("    ||offdiag(H_RG)||_F = %.6f\n", sqrt(offdiag_norm));
        printf("    Ratio off/diag = %.6f\n", sqrt(offdiag_norm / diag_norm));

        /* Compare H_RG directly with best Potts Hamiltonian */
        double *H_potts = build_potts_hamiltonian(n_sites_coarse, best_J, best_K);

        /* Find optimal scaling: min_alpha ||H_RG - alpha * H_Potts||^2
         * alpha = tr(H_RG^T H_Potts) / tr(H_Potts^T H_Potts) */
        double num = 0, den = 0;
        for (int i = 0; i < n_coarse * n_coarse; i++) {
            num += H_RG[i] * H_potts[i];
            den += H_potts[i] * H_potts[i];
        }
        double alpha_opt = num / den;

        double residual = 0, total = 0;
        for (int i = 0; i < n_coarse * n_coarse; i++) {
            double d = H_RG[i] - alpha_opt * H_potts[i];
            residual += d * d;
            total += H_RG[i] * H_RG[i];
        }

        printf("    Optimal scaling alpha = %.6f\n", alpha_opt);
        printf("    ||H_RG - alpha*H_Potts||_F / ||H_RG||_F = %.6f\n",
               sqrt(residual / total));
        printf("    (1.0 = no match, 0.0 = perfect match)\n");

        free(H_potts);
    }

    free(H_RG);
    free(evals_rg);
}

/* =========================================================================
 * DIRECT SPECTRAL COMPARISON (same-size, no RG needed)
 * ========================================================================= */

static void direct_comparison(int L, const double *H_phys, int n_cfg,
                               const double *ness, double mu) {
    int n_sites = 2 * L;

    printf("\n  === Direct Spectral Comparison (L=%d, n_cfg=%d) ===\n", L, n_cfg);

    /* Diagonalize H_phys */
    double *H_copy = (double *)malloc(n_cfg * n_cfg * sizeof(double));
    memcpy(H_copy, H_phys, n_cfg * n_cfg * sizeof(double));
    double *evals = eigenvalues_symmetric(H_copy, n_cfg);
    free(H_copy);

    double gs = evals[0];
    for (int i = 0; i < n_cfg; i++) evals[i] -= gs;
    double gap = evals[1];

    printf("    H_phys spectral gap: %.8f\n", gap);
    printf("    First 10 eigenvalues: ");
    for (int i = 0; i < 10 && i < n_cfg; i++) printf("%.6f ", evals[i]);
    printf("\n");

    if (gap > 1e-10 && n_cfg > 2) {
        printf("    Ratios E_k/E_1: ");
        for (int i = 2; i < 10 && i < n_cfg; i++) printf("%.4f ", evals[i] / gap);
        printf("\n");
    }

    free(evals);
}

/* =========================================================================
 * MAIN
 * ========================================================================= */

int main(int argc, char **argv) {
    printf("======================================================================\n");
    printf("CONSTRUCTIVE RG MAP: Soup H_DP → Z₃ Potts\n");
    printf("======================================================================\n");
    printf("Investigates block-spin RG transformation mapping the soup's\n");
    printf("NESS-symmetrized Doi-Peliti Hamiltonian to the Z₃ Potts model.\n");
    printf("======================================================================\n");

    double mu = 0.01;
    clock_t t0, t1;

    /* =================================================================
     * PART 1: Build H_phys for L=2 (81×81) — baseline
     * ================================================================= */
    {
        int L = 2;
        int n_sites = 2 * L;
        int n_cfg = pow3(n_sites);

        printf("\n######################################################################\n");
        printf("# PART 1: L=%d Baseline (n_cfg=%d)\n", L, n_cfg);
        printf("######################################################################\n");

        t0 = clock();
        int *map_fwd = (int *)malloc(n_cfg * sizeof(int));
        int *map_rev = (int *)malloc(n_cfg * sizeof(int));
        build_det_maps(L, map_fwd, map_rev);

        double *ness = compute_ness(n_cfg, map_fwd, map_rev, n_sites, mu, 100000, 1e-14);

        double db_viol;
        double *T_full = build_full_T(n_cfg, map_fwd, map_rev, n_sites, mu);
        double *H_phys = build_H_phys(n_cfg, T_full, ness, &db_viol);
        printf("    Detailed balance violation: %.6e\n", db_viol);

        direct_comparison(L, H_phys, n_cfg, ness, mu);

        t1 = clock();
        printf("    L=%d total time: %.2fs\n", L, (double)(t1 - t0) / CLOCKS_PER_SEC);

        free(map_fwd); free(map_rev); free(ness); free(T_full); free(H_phys);
    }

    /* =================================================================
     * PART 2: Build H_phys for L=3 (729×729) and apply RG to get L=2
     * ================================================================= */
    {
        int L = 3;
        int n_sites = 2 * L;
        int n_cfg = pow3(n_sites);

        printf("\n######################################################################\n");
        printf("# PART 2: L=%d → L=%d RG (n_cfg=%d → %d)\n", L, L-1, n_cfg, pow3(2*(L-1)));
        printf("######################################################################\n");

        t0 = clock();
        int *map_fwd = (int *)malloc(n_cfg * sizeof(int));
        int *map_rev = (int *)malloc(n_cfg * sizeof(int));
        build_det_maps(L, map_fwd, map_rev);

        double *ness = compute_ness(n_cfg, map_fwd, map_rev, n_sites, mu, 100000, 1e-14);

        double db_viol;
        double *T_full = build_full_T(n_cfg, map_fwd, map_rev, n_sites, mu);
        double *H_phys = build_H_phys(n_cfg, T_full, ness, &db_viol);
        printf("    Detailed balance violation: %.6e\n", db_viol);
        free(T_full);

        direct_comparison(L, H_phys, n_cfg, ness, mu);

        /* --- Strategy 1: Decimation RG --- */
        {
            double *R;
            int n_fine, n_coarse;
            build_decimation_R(L, L - 1, &R, &n_fine, &n_coarse);
            analyze_rg_map("Decimation (drop last trit per program)",
                          L, H_phys, n_fine, R, n_coarse, mu);
            free(R);
        }

        /* --- Strategy 2: Majority Vote RG --- */
        {
            double *R;
            int n_fine, n_coarse;
            build_majority_R(L, L - 1, &R, &n_fine, &n_coarse);
            analyze_rg_map("Majority Vote (pair consecutive trits)",
                          L, H_phys, n_fine, R, n_coarse, mu);
            free(R);
        }

        /* --- Strategy 3: NESS-weighted RG --- */
        {
            double *R;
            int n_fine, n_coarse;
            build_ness_weighted_R(L, L - 1, ness, &R, &n_fine, &n_coarse);
            analyze_rg_map("NESS-weighted decimation",
                          L, H_phys, n_fine, R, n_coarse, mu);
            free(R);
        }

        t1 = clock();
        printf("\n    L=%d total time: %.2fs\n", L, (double)(t1 - t0) / CLOCKS_PER_SEC);

        free(map_fwd); free(map_rev); free(ness); free(H_phys);
    }

    /* =================================================================
     * PART 3: Mu-dependence study
     * ================================================================= */
    {
        printf("\n######################################################################\n");
        printf("# PART 3: Mutation Rate Dependence (L=3 → L=2 decimation)\n");
        printf("######################################################################\n");

        double mu_vals[] = {0.001, 0.005, 0.01, 0.02, 0.05, 0.1, 0.2};
        int n_mu = sizeof(mu_vals) / sizeof(mu_vals[0]);

        int L = 3;
        int n_sites = 2 * L;
        int n_cfg = pow3(n_sites);

        /* Build deterministic maps (mu-independent) */
        int *map_fwd = (int *)malloc(n_cfg * sizeof(int));
        int *map_rev = (int *)malloc(n_cfg * sizeof(int));
        build_det_maps(L, map_fwd, map_rev);

        printf("\n  %8s  %12s  %12s  %12s  %12s  %12s\n",
               "mu", "gap_Hphys", "gap_RG", "gap_Potts", "f=gRG/gP", "RMS_ratio");
        printf("  %s\n",
               "------------------------------------------------------------------------");

        for (int mi = 0; mi < n_mu; mi++) {
            double mu_val = mu_vals[mi];

            double *ness = compute_ness(n_cfg, map_fwd, map_rev, n_sites, mu_val, 100000, 1e-14);

            double db_viol;
            double *T_full = build_full_T(n_cfg, map_fwd, map_rev, n_sites, mu_val);
            double *H_phys = build_H_phys(n_cfg, T_full, ness, &db_viol);
            free(T_full);

            /* H_phys gap */
            double *Hc = (double *)malloc(n_cfg * n_cfg * sizeof(double));
            memcpy(Hc, H_phys, n_cfg * n_cfg * sizeof(double));
            double *ev_full = eigenvalues_symmetric(Hc, n_cfg);
            free(Hc);
            double gap_full = ev_full[1] - ev_full[0];

            /* Decimation RG */
            double *R;
            int n_fine, n_coarse;
            build_decimation_R(L, L - 1, &R, &n_fine, &n_coarse);

            double *RH = (double *)malloc(n_coarse * n_fine * sizeof(double));
            mat_mul(R, H_phys, RH, n_coarse, n_fine, n_fine);
            double *H_RG = (double *)malloc(n_coarse * n_coarse * sizeof(double));
            mat_mul_ABt(RH, R, H_RG, n_coarse, n_fine, n_coarse);
            free(RH);

            /* Symmetrize */
            for (int i = 0; i < n_coarse; i++)
                for (int j = i + 1; j < n_coarse; j++) {
                    double avg = 0.5 * (H_RG[i*n_coarse+j] + H_RG[j*n_coarse+i]);
                    H_RG[i*n_coarse+j] = avg;
                    H_RG[j*n_coarse+i] = avg;
                }

            double *ev_rg = eigenvalues_symmetric(H_RG, n_coarse);
            double gap_rg = ev_rg[1] - ev_rg[0];
            for (int i = 0; i < n_coarse; i++) ev_rg[i] -= ev_rg[0];

            /* Best Potts match (quick scan) */
            int n_sites_c = 2 * (L - 1);
            double best_J = 1.0, best_K = 0.5, best_score = 1e30;
            double gap_potts_best = 0;
            double f_best = 0;

            for (double J = 0.01; J <= 5.0; J *= 1.5) {
                for (double K = 0.0; K <= 5.0; K += 0.1) {
                    double *Hp = build_potts_hamiltonian(n_sites_c, J, K);
                    double *ep = eigenvalues_symmetric(Hp, n_coarse);
                    free(Hp);
                    for (int i = 0; i < n_coarse; i++) ep[i] -= ep[0];
                    double gp = ep[1];
                    if (gp < 1e-10 || gap_rg < 1e-10) { free(ep); continue; }

                    double score = 0;
                    int nc = (n_coarse < 10) ? n_coarse : 10;
                    for (int i = 2; i < nc; i++) {
                        double r1 = ev_rg[i] / gap_rg;
                        double r2 = ep[i] / gp;
                        score += (r1 - r2) * (r1 - r2);
                    }
                    score = sqrt(score / (nc - 2));
                    if (score < best_score) {
                        best_score = score;
                        best_J = J;
                        best_K = K;
                        gap_potts_best = gp;
                        f_best = gap_rg / gp;
                    }
                    free(ep);
                }
            }

            printf("  %8.3f  %12.6f  %12.6f  %12.6f  %12.6f  %12.6f\n",
                   mu_val, gap_full, gap_rg, gap_potts_best, f_best, best_score);

            free(R); free(H_RG); free(ev_rg); free(ev_full);
            free(ness); free(H_phys);
        }

        free(map_fwd); free(map_rev);
    }

    /* =================================================================
     * PART 4: Summary and f_rep extraction
     * ================================================================= */
    printf("\n######################################################################\n");
    printf("# PART 4: Summary\n");
    printf("######################################################################\n");
    printf("\n");
    printf("  The RG map R projects H_phys from the L=3 soup (729 states)\n");
    printf("  down to an effective L=2 Hamiltonian (81 states), which is then\n");
    printf("  compared with the Z₃ Potts Hamiltonian on the same space.\n");
    printf("\n");
    printf("  Key questions answered:\n");
    printf("  1. Does R·H_phys·R^† reproduce the Potts spectrum? → See ratio tables\n");
    printf("  2. What proportionality constant emerges? → See f values\n");
    printf("  3. Can f_rep ≈ 7.2 be recovered? → Compare with mu-scan\n");
    printf("\n");

    printf("\nDone.\n");
    return 0;
}
