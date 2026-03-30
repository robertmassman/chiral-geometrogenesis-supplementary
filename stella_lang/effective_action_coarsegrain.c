/*
 * Effective Action under Coarse-Graining: Block-Spin RG for Z₃ Soup
 * ===================================================================
 *
 * Tests whether the Z₃ symmetry breaking in the stella soup VM is
 * RG-relevant or RG-irrelevant by performing block-spin renormalization
 * and tracking how Z₃ asymmetry evolves under coarse-graining.
 *
 * Key question: The VM's OPEN instruction (tape[h0]==0 gate) makes
 * sector 4π/3 dominate at ~52%. Does this breaking diminish (irrelevant)
 * or persist/grow (relevant) under coarse-graining?
 *
 * Diagnostics at each RG level:
 *   1. Z₃ order parameter m = (1/N) Σ ω^{s_i}, ω = e^{2πi/3}
 *   2. Phase sector histogram (fractions in 0, 2π/3, 4π/3 sectors)
 *   3. Sector asymmetry A = max_frac - min_frac
 *   4. Nearest-neighbor and next-nearest correlations
 *   5. Correlation ratio C₁/C₂ (Potts test)
 *   6. Block trit entropy S (Z₃ symmetric → S = log3)
 *
 * Soup dynamics: well-mixed 1D soup, programs of PROG_SIZE trits,
 * random pairing, VM execution, mutation at rate μ.
 *
 * Compile: cc -O3 -o effective_action_coarsegrain effective_action_coarsegrain.c -lm
 * Run:     ./effective_action_coarsegrain
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

/* === Constants === */
#define Z3 3
#define MAX_VM_STEPS 729
#define PROG_SIZE 6           /* trits per program (tape_len = 2*PROG_SIZE = 12) */

#define MAX_BLOCK_LEVELS 4    /* original + 3 blocking steps */
#define N_BLOCK_SIZES 4       /* b = 2, 3, 5, 9 */

/* === Simulation parameters === */
#define N_SIZES 3
static const int SOUP_SIZES[N_SIZES] = {1002, 2004, 3996}; /* divisible by PROG_SIZE and block sizes */
static const double MU = 0.005;           /* mutation rate (well inside active phase) */
#define THERMALIZE_EPOCHS 50000
#define MEASURE_EPOCHS    100000
#define MEASURE_INTERVAL  100             /* measure every N epochs */

static const int BLOCK_SIZES[N_BLOCK_SIZES] = {2, 3, 5, 9};

/* ================================================================
 * PRNG (xoshiro256**)
 * ================================================================ */
static uint64_t rng_state[4];

static inline uint64_t rotl(uint64_t x, int k) {
    return (x << k) | (x >> (64 - k));
}

static uint64_t rng_next(void) {
    uint64_t result = rotl(rng_state[1] * 5, 7) * 9;
    uint64_t t = rng_state[1] << 17;
    rng_state[2] ^= rng_state[0];
    rng_state[3] ^= rng_state[1];
    rng_state[1] ^= rng_state[2];
    rng_state[0] ^= rng_state[3];
    rng_state[2] ^= t;
    rng_state[3] = rotl(rng_state[3], 45);
    return result;
}

static void rng_seed(uint64_t seed) {
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        rng_state[i] = z ^ (z >> 31);
    }
}

static inline uint32_t rng_int(uint32_t n) {
    return (uint32_t)((rng_next() >> 33) % n);
}

static inline double rng_float(void) {
    return (rng_next() >> 11) * 0x1.0p-53;
}

/* ================================================================
 * VM (identical to soup.c / universality_class_v2.c)
 * ================================================================ */
static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;
    while (steps < max_steps && ip + 1 < tape_len) {
        int op = tape[ip] * 3 + tape[ip + 1];
        switch (op) {
        case 0: break; /* NOP */
        case 1: tape[h0] = tape[h0] < 2 ? tape[h0] + 1 : 0; break; /* ROT */
        case 2: if (++h0 >= tape_len) h0 = 0; break; /* FWD0 */
        case 3: if (--h0 < 0) h0 = tape_len - 1; break; /* BCK0 */
        case 4: if (++h1 >= tape_len) h1 = 0; break; /* FWD1 */
        case 5: /* OPEN */
            if (tape[h0] == 0) {
                int depth = 1, pos = ip + 2;
                while (depth > 0 && pos + 1 < tape_len) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == 5) depth++;
                    else if (inner == 6) depth--;
                    pos += 2;
                }
                if (depth == 0) ip = pos - 2;
            }
            break;
        case 6: /* CLOSE */
            if (tape[h0] != 0) {
                int depth = 1, pos = ip - 2;
                while (depth > 0 && pos >= 0) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == 6) depth++;
                    else if (inner == 5) depth--;
                    pos -= 2;
                }
                if (depth == 0) ip = pos + 2;
            }
            break;
        case 7: tape[h1] = tape[h0]; break; /* CPY01 */
        case 8: tape[h0] = tape[h1]; break; /* CPY10 */
        }
        ip += 2;
        steps++;
    }
}

/* ================================================================
 * Soup dynamics
 * ================================================================ */

/* One epoch: N_prog/2 random pairings, VM execution, mutation */
static void soup_epoch(uint8_t *soup, int n_trits) {
    int n_progs = n_trits / PROG_SIZE;
    int interactions = n_progs / 2;
    uint8_t tape[2 * PROG_SIZE];
    int tape_len = 2 * PROG_SIZE;

    for (int k = 0; k < interactions; k++) {
        /* Pick two distinct random programs */
        int i = rng_int(n_progs);
        int j = rng_int(n_progs - 1);
        if (j >= i) j++;

        /* Concatenate into tape */
        memcpy(tape, &soup[i * PROG_SIZE], PROG_SIZE);
        memcpy(tape + PROG_SIZE, &soup[j * PROG_SIZE], PROG_SIZE);

        /* Execute VM */
        execute_tape(tape, tape_len, MAX_VM_STEPS);

        /* Write back */
        memcpy(&soup[i * PROG_SIZE], tape, PROG_SIZE);
        memcpy(&soup[j * PROG_SIZE], tape + PROG_SIZE, PROG_SIZE);
    }

    /* Mutation */
    for (int i = 0; i < n_trits; i++) {
        if (rng_float() < MU) {
            soup[i] = rng_int(Z3);
        }
    }
}

/* ================================================================
 * Block-spin transformation
 * ================================================================
 *
 * Majority vote: most common trit in block wins.
 * Ties broken randomly.
 */
static void block_spin(const uint8_t *src, int n_src, int block_size, uint8_t *dst) {
    int n_dst = n_src / block_size;
    for (int b = 0; b < n_dst; b++) {
        int counts[Z3] = {0, 0, 0};
        for (int k = 0; k < block_size; k++) {
            counts[src[b * block_size + k]]++;
        }
        /* Find max */
        int max_count = counts[0];
        int n_max = 1;
        int winner = 0;
        for (int v = 1; v < Z3; v++) {
            if (counts[v] > max_count) {
                max_count = counts[v];
                winner = v;
                n_max = 1;
            } else if (counts[v] == max_count) {
                n_max++;
            }
        }
        /* Break ties randomly */
        if (n_max > 1) {
            int pick = rng_int(n_max);
            int idx = 0;
            for (int v = 0; v < Z3; v++) {
                if (counts[v] == max_count) {
                    if (idx == pick) { winner = v; break; }
                    idx++;
                }
            }
        }
        dst[b] = winner;
    }
}

/* Iterated blocking: apply block_spin repeatedly.
 * Returns the number of sites after blocking, or 0 if too few sites. */
static int iterated_block(const uint8_t *src, int n_src, int block_size, int n_steps, uint8_t *dst) {
    /* We need two buffers for ping-pong */
    uint8_t *buf_a = (uint8_t *)malloc(n_src);
    uint8_t *buf_b = (uint8_t *)malloc(n_src);
    if (!buf_a || !buf_b) { free(buf_a); free(buf_b); return 0; }

    memcpy(buf_a, src, n_src);
    int n = n_src;

    for (int step = 0; step < n_steps; step++) {
        int n_new = n / block_size;
        if (n_new < 10) { free(buf_a); free(buf_b); return 0; } /* too few sites */
        block_spin(buf_a, n, block_size, buf_b);
        /* Swap buffers */
        uint8_t *tmp = buf_a; buf_a = buf_b; buf_b = tmp;
        n = n_new;
    }

    memcpy(dst, buf_a, n);
    free(buf_a);
    free(buf_b);
    return n;
}

/* ================================================================
 * Measurements
 * ================================================================ */

/* Z₃ order parameter: m = (1/N) Σ ω^{s_i} where ω = e^{2πi/3}
 * Returns |m|, phase of m, and sector fractions. */
typedef struct {
    double abs_m;         /* |m| */
    double phase_m;       /* arg(m) in [0, 2π) */
    double sector_frac[3]; /* fraction of sites with value 0, 1, 2 */
    double asymmetry;     /* max_frac - min_frac */
    double entropy;       /* -Σ p log p */
    double corr_1;        /* nearest-neighbor δ-correlation */
    double corr_2;        /* next-nearest δ-correlation */
    double corr_ratio;    /* corr_1 / corr_2 */
} measurements_t;

static const double OMEGA_RE[3] = {1.0, -0.5, -0.5};
static const double OMEGA_IM[3] = {0.0, 0.8660254037844387, -0.8660254037844387};
/* ω^0 = 1, ω^1 = e^{2πi/3}, ω^2 = e^{4πi/3} */

static measurements_t measure(const uint8_t *config, int n) {
    measurements_t m;
    memset(&m, 0, sizeof(m));

    /* Sector counts and order parameter */
    int counts[Z3] = {0, 0, 0};
    double re = 0.0, im = 0.0;

    for (int i = 0; i < n; i++) {
        int v = config[i];
        counts[v]++;
        re += OMEGA_RE[v];
        im += OMEGA_IM[v];
    }

    re /= n;
    im /= n;
    m.abs_m = sqrt(re * re + im * im);
    m.phase_m = atan2(im, re);
    if (m.phase_m < 0) m.phase_m += 2.0 * M_PI;

    /* Sector fractions */
    double max_f = 0.0, min_f = 1.0;
    for (int v = 0; v < Z3; v++) {
        m.sector_frac[v] = (double)counts[v] / n;
        if (m.sector_frac[v] > max_f) max_f = m.sector_frac[v];
        if (m.sector_frac[v] < min_f) min_f = m.sector_frac[v];
    }
    m.asymmetry = max_f - min_f;

    /* Entropy */
    m.entropy = 0.0;
    for (int v = 0; v < Z3; v++) {
        double p = m.sector_frac[v];
        if (p > 0.0) m.entropy -= p * log(p);
    }

    /* Nearest-neighbor correlation: fraction of same-trit adjacent pairs */
    if (n >= 2) {
        int same_1 = 0, same_2 = 0;
        for (int i = 0; i < n - 1; i++) {
            if (config[i] == config[i + 1]) same_1++;
        }
        m.corr_1 = (double)same_1 / (n - 1);

        /* Next-nearest */
        for (int i = 0; i < n - 2; i++) {
            if (config[i] == config[i + 2]) same_2++;
        }
        m.corr_2 = (double)same_2 / (n - 2);

        /* Correlation ratio */
        m.corr_ratio = (m.corr_2 > 1e-10) ? m.corr_1 / m.corr_2 : 0.0;
    }

    return m;
}

/* ================================================================
 * Accumulator for averaging measurements
 * ================================================================ */
typedef struct {
    double abs_m_sum, abs_m_sq;
    double sector_sum[3];
    double asymmetry_sum, asymmetry_sq;
    double entropy_sum;
    double corr_1_sum, corr_2_sum;
    double corr_ratio_sum;
    int count;
} accumulator_t;

static void acc_init(accumulator_t *a) {
    memset(a, 0, sizeof(*a));
}

static void acc_add(accumulator_t *a, const measurements_t *m) {
    a->abs_m_sum += m->abs_m;
    a->abs_m_sq += m->abs_m * m->abs_m;
    for (int v = 0; v < Z3; v++) {
        a->sector_sum[v] += m->sector_frac[v];
    }
    a->asymmetry_sum += m->asymmetry;
    a->asymmetry_sq += m->asymmetry * m->asymmetry;
    a->entropy_sum += m->entropy;
    a->corr_1_sum += m->corr_1;
    a->corr_2_sum += m->corr_2;
    a->corr_ratio_sum += m->corr_ratio;
    a->count++;
}

/* ================================================================
 * Main
 * ================================================================ */
int main(void) {
    printf("==========================================================\n");
    printf("  Block-Spin RG for Z_3 Soup: Effective Action Analysis\n");
    printf("==========================================================\n");
    printf("PROG_SIZE = %d trits, tape_len = %d\n", PROG_SIZE, 2 * PROG_SIZE);
    printf("Mutation rate mu = %.4f\n", MU);
    printf("Thermalization: %d epochs, Measurement: %d epochs (every %d)\n",
           THERMALIZE_EPOCHS, MEASURE_EPOCHS, MEASURE_INTERVAL);
    printf("Block sizes: ");
    for (int bi = 0; bi < N_BLOCK_SIZES; bi++) printf("%d ", BLOCK_SIZES[bi]);
    printf("\n\n");

    double log3 = log(3.0);

    for (int si = 0; si < N_SIZES; si++) {
        int n_trits = SOUP_SIZES[si];
        int n_progs = n_trits / PROG_SIZE;

        printf("==========================================================\n");
        printf("  SOUP SIZE: N = %d trits (%d programs)\n", n_trits, n_progs);
        printf("==========================================================\n\n");

        /* Allocate soup */
        uint8_t *soup = (uint8_t *)malloc(n_trits);
        if (!soup) { fprintf(stderr, "malloc failed\n"); return 1; }

        /* Random initialization */
        rng_seed(42 + si * 1000);
        for (int i = 0; i < n_trits; i++) {
            soup[i] = rng_int(Z3);
        }

        /* Thermalize */
        printf("  Thermalizing...\n");
        for (int e = 0; e < THERMALIZE_EPOCHS; e++) {
            soup_epoch(soup, n_trits);
            if ((e + 1) % 10000 == 0) {
                printf("    epoch %d / %d\r", e + 1, THERMALIZE_EPOCHS);
                fflush(stdout);
            }
        }
        printf("    Thermalization complete.                    \n\n");

        /* Prepare accumulators:
         * For each block_size, we have up to MAX_BLOCK_LEVELS levels (0=original, 1=1x, ...) */
        accumulator_t acc[N_BLOCK_SIZES][MAX_BLOCK_LEVELS];
        for (int bi = 0; bi < N_BLOCK_SIZES; bi++)
            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++)
                acc_init(&acc[bi][lv]);

        /* Also accumulate the original (level 0) once */
        accumulator_t acc_orig;
        acc_init(&acc_orig);

        /* Allocate buffer for blocked configs */
        uint8_t *blocked = (uint8_t *)malloc(n_trits);
        if (!blocked) { fprintf(stderr, "malloc failed\n"); return 1; }

        /* Measurement phase */
        printf("  Measuring...\n");
        int n_samples = 0;
        for (int e = 0; e < MEASURE_EPOCHS; e++) {
            soup_epoch(soup, n_trits);

            if ((e + 1) % MEASURE_INTERVAL == 0) {
                n_samples++;

                /* Measure original */
                measurements_t m0 = measure(soup, n_trits);
                acc_add(&acc_orig, &m0);

                /* For each block size, do iterated blocking */
                for (int bi = 0; bi < N_BLOCK_SIZES; bi++) {
                    int bs = BLOCK_SIZES[bi];

                    /* Level 0 = original (already measured in acc_orig) */
                    acc_add(&acc[bi][0], &m0);

                    /* Levels 1, 2, 3 */
                    for (int lv = 1; lv < MAX_BLOCK_LEVELS; lv++) {
                        int n_blocked = iterated_block(soup, n_trits, bs, lv, blocked);
                        if (n_blocked >= 10) {
                            measurements_t mb = measure(blocked, n_blocked);
                            acc_add(&acc[bi][lv], &mb);
                        }
                    }
                }

                if (n_samples % 100 == 0) {
                    printf("    sample %d / %d\r", n_samples,
                           MEASURE_EPOCHS / MEASURE_INTERVAL);
                    fflush(stdout);
                }
            }
        }
        printf("    Measurement complete. %d samples collected.           \n\n", n_samples);

        /* ============================================================
         * Print results: ORIGINAL (unblocked)
         * ============================================================ */
        {
            accumulator_t *a = &acc_orig;
            int c = a->count;
            if (c > 0) {
                printf("  --- ORIGINAL (unblocked, N=%d) ---\n", n_trits);
                printf("    |m|       = %.6f +/- %.6f\n",
                       a->abs_m_sum / c,
                       sqrt((a->abs_m_sq / c) - (a->abs_m_sum / c) * (a->abs_m_sum / c)));
                printf("    Sectors   = [%.4f, %.4f, %.4f]\n",
                       a->sector_sum[0] / c, a->sector_sum[1] / c, a->sector_sum[2] / c);
                printf("    Asymmetry = %.6f +/- %.6f\n",
                       a->asymmetry_sum / c,
                       sqrt(fabs((a->asymmetry_sq / c) - (a->asymmetry_sum / c) * (a->asymmetry_sum / c))));
                printf("    Entropy   = %.6f  (log3 = %.6f, ratio = %.4f)\n",
                       a->entropy_sum / c, log3, (a->entropy_sum / c) / log3);
                printf("    C_1       = %.6f\n", a->corr_1_sum / c);
                printf("    C_2       = %.6f\n", a->corr_2_sum / c);
                printf("    C_1/C_2   = %.6f\n", a->corr_ratio_sum / c);
                printf("\n");
            }
        }

        /* ============================================================
         * Print results: BLOCKED at each block size and level
         * ============================================================ */
        for (int bi = 0; bi < N_BLOCK_SIZES; bi++) {
            int bs = BLOCK_SIZES[bi];
            printf("  --- BLOCK SIZE b = %d ---\n", bs);
            printf("  %6s %8s %8s  %8s %8s %8s  %8s %8s  %8s %8s %8s\n",
                   "Level", "|m|", "err",
                   "f(0)", "f(1)", "f(2)",
                   "Asym", "err",
                   "S", "S/log3", "C1/C2");

            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) {
                accumulator_t *a = &acc[bi][lv];
                int c = a->count;
                if (c == 0) {
                    printf("  %6d   (no data — too few sites after blocking)\n", lv);
                    continue;
                }

                double mean_m = a->abs_m_sum / c;
                double std_m = sqrt(fabs((a->abs_m_sq / c) - mean_m * mean_m));
                double mean_asym = a->asymmetry_sum / c;
                double std_asym = sqrt(fabs((a->asymmetry_sq / c) - mean_asym * mean_asym));
                double mean_S = a->entropy_sum / c;

                /* Effective N after lv blockings of size bs */
                int n_eff = n_trits;
                for (int k = 0; k < lv; k++) n_eff /= bs;

                printf("  %4d(%3d) %8.5f %8.5f  %8.4f %8.4f %8.4f  %8.5f %8.5f  %8.5f %7.4f %8.4f\n",
                       lv, n_eff,
                       mean_m, std_m,
                       a->sector_sum[0] / c, a->sector_sum[1] / c, a->sector_sum[2] / c,
                       mean_asym, std_asym,
                       mean_S, mean_S / log3,
                       a->corr_ratio_sum / c);
            }
            printf("\n");
        }

        /* ============================================================
         * RG FLOW SUMMARY: Asymmetry vs blocking level
         * ============================================================ */
        printf("  === RG FLOW OF Z_3 ASYMMETRY (N=%d) ===\n", n_trits);
        printf("  Interpretation:\n");
        printf("    A -> 0 under blocking: Z_3 breaking is RG-IRRELEVANT (emergent symmetry)\n");
        printf("    A -> const > 0 or grows: Z_3 breaking is RG-RELEVANT (no emergent symmetry)\n\n");

        printf("  %6s", "b\\lv");
        for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) printf("  %8d", lv);
        printf("\n");

        for (int bi = 0; bi < N_BLOCK_SIZES; bi++) {
            printf("  %6d", BLOCK_SIZES[bi]);
            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) {
                accumulator_t *a = &acc[bi][lv];
                if (a->count > 0) {
                    printf("  %8.5f", a->asymmetry_sum / a->count);
                } else {
                    printf("       ---");
                }
            }
            printf("\n");
        }

        /* Trend analysis */
        printf("\n  Trend analysis (b=3, largest range):\n");
        {
            int bi = 1; /* b=3 */
            double prev_asym = -1.0;
            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) {
                accumulator_t *a = &acc[bi][lv];
                if (a->count > 0) {
                    double asym = a->asymmetry_sum / a->count;
                    if (prev_asym > 0) {
                        double ratio = asym / prev_asym;
                        printf("    Level %d -> %d: A changes by factor %.3f (%s)\n",
                               lv - 1, lv, ratio,
                               ratio < 0.9 ? "DECREASING (toward irrelevant)" :
                               ratio > 1.1 ? "INCREASING (toward relevant)" :
                               "STABLE");
                    }
                    prev_asym = asym;
                }
            }
        }

        /* Potts correlation test */
        printf("\n  === POTTS CORRELATION TEST ===\n");
        printf("  In Z_3 Potts model: C_n = 1/3 + (2/3)exp(-n/xi)\n");
        printf("  => C_1/C_2 = [1/3 + (2/3)e^{-1/xi}] / [1/3 + (2/3)e^{-2/xi}]\n");
        printf("  Uncorrelated random: C_1 = C_2 = 1/3, ratio = 1.0\n\n");

        printf("  %6s", "b\\lv");
        for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) printf("  %8d", lv);
        printf("\n");

        for (int bi = 0; bi < N_BLOCK_SIZES; bi++) {
            printf("  %6d", BLOCK_SIZES[bi]);
            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) {
                accumulator_t *a = &acc[bi][lv];
                if (a->count > 0) {
                    printf("  %8.4f", a->corr_ratio_sum / a->count);
                } else {
                    printf("       ---");
                }
            }
            printf("\n");
        }

        /* Entropy analysis */
        printf("\n  === ENTROPY ANALYSIS (S/log3) ===\n");
        printf("  Z_3 symmetric: S/log3 = 1.0000\n\n");

        printf("  %6s", "b\\lv");
        for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) printf("  %8d", lv);
        printf("\n");

        for (int bi = 0; bi < N_BLOCK_SIZES; bi++) {
            printf("  %6d", BLOCK_SIZES[bi]);
            for (int lv = 0; lv < MAX_BLOCK_LEVELS; lv++) {
                accumulator_t *a = &acc[bi][lv];
                if (a->count > 0) {
                    printf("  %8.4f", (a->entropy_sum / a->count) / log3);
                } else {
                    printf("       ---");
                }
            }
            printf("\n");
        }

        printf("\n");
        free(soup);
        free(blocked);
    }

    /* ============================================================
     * FINAL VERDICT
     * ============================================================ */
    printf("==========================================================\n");
    printf("  INTERPRETATION GUIDE\n");
    printf("==========================================================\n");
    printf("\n");
    printf("  1. Z_3 ASYMMETRY under coarse-graining:\n");
    printf("     - If A decreases monotonically toward 0 with blocking level,\n");
    printf("       the VM's Z_3 breaking is RG-irrelevant. The effective\n");
    printf("       long-wavelength theory has emergent Z_3 Potts symmetry.\n");
    printf("     - If A stays constant or grows, the breaking is RG-relevant\n");
    printf("       and the IR theory is NOT Z_3 Potts symmetric.\n");
    printf("\n");
    printf("  2. ENTROPY S/log3:\n");
    printf("     - Approaching 1.0 under blocking = emergent Z_3 symmetry\n");
    printf("     - Staying below 1.0 = persistent symmetry breaking\n");
    printf("\n");
    printf("  3. CORRELATION RATIO C_1/C_2:\n");
    printf("     - Converging to a value > 1 under blocking = non-trivial\n");
    printf("       correlations consistent with Potts effective action\n");
    printf("     - Staying near 1.0 = uncorrelated (trivial fixed point)\n");
    printf("\n");
    printf("  4. Combine with known results:\n");
    printf("     - Critical exponents match Directed Percolation (DP)\n");
    printf("     - Full spectrum does NOT match Potts\n");
    printf("     - Question: does the Z_3 sector of the spectrum decouple\n");
    printf("       from the non-Z_3 sector under RG?\n");
    printf("\n");

    return 0;
}
