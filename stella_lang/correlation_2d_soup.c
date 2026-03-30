/*
 * correlation_2d_soup.c — Spatial 2-point correlation functions on 2D triangular soup
 * ====================================================================================
 *
 * Measures Z₃ two-point correlator, Z₃ complex correlator, and density-density
 * correlator to extract correlation length exponent ν. Compares with:
 *   - 2D Z₃ Potts:  ν = 5/6 ≈ 0.833
 *   - 2D DP:         ν_⊥ ≈ 0.734
 *
 * Setup: L×L triangular lattice, periodic BC, L_local=3 trits per site.
 *
 * Compile: cc -O3 -o correlation_2d_soup correlation_2d_soup.c -lm
 * Run:     ./correlation_2d_soup            (uses defaults)
 *          ./correlation_2d_soup --L 40 --mu 0.005 --seed 12345
 *          ./correlation_2d_soup --scan      (runs full parameter scan)
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <getopt.h>

/* ================================================================
 * Constants
 * ================================================================ */
#define Z3            3
#define L_LOCAL       3        /* trits per site */
#define TAPE_LEN      6        /* 2 * L_LOCAL for VM interactions */
#define MAX_VM_STEPS  729
#define MAX_L         64
#define MAX_SITES     (MAX_L * MAX_L)
#define MAX_DIST_BINS 128      /* max distance bins */
#define N_NEIGHBORS   6        /* triangular lattice */

/* ================================================================
 * PRNG: xoshiro256**
 * ================================================================ */
static uint64_t s[4] = {0x12345678, 0x9abcdef0, 0x13579bdf, 0x2468ace0};

static inline uint64_t rotl(uint64_t x, int k) {
    return (x << k) | (x >> (64 - k));
}

static uint64_t xoshiro256ss(void) {
    uint64_t result = rotl(s[1] * 5, 7) * 9;
    uint64_t t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
    s[2] ^= t; s[3] = rotl(s[3], 45);
    return result;
}

static double rand_double(void) {
    return (xoshiro256ss() >> 11) * 0x1.0p-53;
}

static uint64_t rand_int(uint64_t n) {
    return xoshiro256ss() % n;
}

static void seed_rng(uint64_t seed) {
    /* SplitMix64 to seed xoshiro */
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        s[i] = z ^ (z >> 31);
    }
}

/* ================================================================
 * VM: Ternary tape computer
 * ================================================================ */
static void execute_tape(unsigned char *tape, int tape_len, int max_steps) {
    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;
    while (steps < max_steps && ip + 1 < tape_len) {
        int high = tape[ip], low = tape[ip + 1];
        if (high == 0) {
            if (low == 1) { tape[h0] = (tape[h0] + 1) % Z3; }
            else if (low == 2) { h0 = (h0 + 1) % tape_len; }
        } else if (high == 1) {
            if (low == 0) { h0 = (h0 - 1 + tape_len) % tape_len; }
            else if (low == 1) { h1 = (h1 + 1) % tape_len; }
            else if (low == 2) {
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
            }
            else if (low == 1) { tape[h1] = tape[h0]; }
            else if (low == 2) { tape[h0] = tape[h1]; }
        }
        ip += 2;
        steps++;
    }
}

/* ================================================================
 * Triangular lattice
 * ================================================================ */

static int L;                          /* lattice size */
static int N_sites;                    /* L * L */
static unsigned char lattice[MAX_SITES][L_LOCAL]; /* trits */
static int neighbors[MAX_SITES][N_NEIGHBORS];     /* neighbor table */

/* Distance table: dist_bin[i] for flattened (i,j) pair.
 * Too large to store for all pairs — compute on the fly. */

/* Precompute neighbor table for triangular lattice with PBC.
 * Site (x,y) has index y*L + x.
 * Neighbors: (x±1,y), (x,y±1), (x+1,y-1), (x-1,y+1) — all mod L. */
static void build_neighbors(void) {
    for (int y = 0; y < L; y++) {
        for (int x = 0; x < L; x++) {
            int idx = y * L + x;
            neighbors[idx][0] = y * L + ((x + 1) % L);           /* x+1, y   */
            neighbors[idx][1] = y * L + ((x - 1 + L) % L);       /* x-1, y   */
            neighbors[idx][2] = ((y + 1) % L) * L + x;           /* x,   y+1 */
            neighbors[idx][3] = ((y - 1 + L) % L) * L + x;       /* x,   y-1 */
            neighbors[idx][4] = ((y - 1 + L) % L) * L + ((x + 1) % L); /* x+1, y-1 */
            neighbors[idx][5] = ((y + 1) % L) * L + ((x - 1 + L) % L); /* x-1, y+1 */
        }
    }
}

/* Euclidean distance on triangular lattice with PBC.
 * Site (x,y) → real coords (x + y/2, y√3/2).
 * With periodic wrapping: dx, dy taken as shortest in [-L/2, L/2). */
static double site_distance(int i, int j) {
    int x1 = i % L, y1 = i / L;
    int x2 = j % L, y2 = j / L;
    int dx = x2 - x1;
    int dy = y2 - y1;
    /* Periodic wrapping */
    if (dx > L / 2) dx -= L;
    if (dx < -L / 2) dx += L;
    if (dy > L / 2) dy -= L;
    if (dy < -L / 2) dy += L;
    /* Triangular coordinates */
    double rx = (double)dx + 0.5 * (double)dy;
    double ry = (double)dy * 0.8660254037844386; /* √3/2 */
    return sqrt(rx * rx + ry * ry);
}

/* ================================================================
 * Distance binning: precompute for each pair of offsets (dx, dy)
 * ================================================================ */

/* For efficiency, precompute distance bin for offset (dx, dy) with 0 <= dx,dy < L.
 * We only need unique offsets. Store in a 2D array. */
static int dist_bin_table[MAX_L][MAX_L]; /* dist_bin_table[dy][dx] */
static int max_bin;

static void build_dist_bins(void) {
    max_bin = 0;
    for (int dy = 0; dy < L; dy++) {
        for (int dx = 0; dx < L; dx++) {
            int ddx = dx, ddy = dy;
            if (ddx > L / 2) ddx -= L;
            if (ddy > L / 2) ddy -= L;
            double rx = (double)ddx + 0.5 * (double)ddy;
            double ry = (double)ddy * 0.8660254037844386;
            double d = sqrt(rx * rx + ry * ry);
            int bin = (int)(d + 0.5); /* round to nearest int */
            if (bin < 1) bin = 0;     /* self-distance → bin 0 */
            if (bin > L / 2) bin = L / 2;
            dist_bin_table[dy][dx] = bin;
            if (bin > max_bin) max_bin = bin;
        }
    }
    if (max_bin >= MAX_DIST_BINS) max_bin = MAX_DIST_BINS - 1;
}

static inline int get_dist_bin(int i, int j) {
    int x1 = i % L, y1 = i / L;
    int x2 = j % L, y2 = j / L;
    int dx = ((x2 - x1) % L + L) % L;
    int dy = ((y2 - y1) % L + L) % L;
    return dist_bin_table[dy][dx];
}

/* ================================================================
 * Lattice initialization
 * ================================================================ */
static void init_lattice(void) {
    for (int i = 0; i < N_sites; i++) {
        for (int t = 0; t < L_LOCAL; t++) {
            lattice[i][t] = (unsigned char)(rand_int(Z3));
        }
    }
}

/* ================================================================
 * Dynamics: one sweep = N_sites interactions + mutation
 * ================================================================ */
static void do_sweep(double mu) {
    unsigned char tape[TAPE_LEN];

    /* N_sites random interactions */
    for (int step = 0; step < N_sites; step++) {
        int i = (int)rand_int(N_sites);
        int ni = (int)rand_int(N_NEIGHBORS);
        int j = neighbors[i][ni];

        /* Concatenate trits into tape */
        for (int t = 0; t < L_LOCAL; t++) {
            tape[t] = lattice[i][t];
            tape[t + L_LOCAL] = lattice[j][t];
        }

        /* Execute VM */
        execute_tape(tape, TAPE_LEN, MAX_VM_STEPS);

        /* Write back */
        for (int t = 0; t < L_LOCAL; t++) {
            lattice[i][t] = tape[t];
            lattice[j][t] = tape[t + L_LOCAL];
        }
    }

    /* Mutation: each trit flips with probability mu */
    if (mu > 0.0) {
        for (int i = 0; i < N_sites; i++) {
            for (int t = 0; t < L_LOCAL; t++) {
                if (rand_double() < mu) {
                    lattice[i][t] = (lattice[i][t] + 1 + (unsigned char)rand_int(2)) % Z3;
                }
            }
        }
    }
}

/* ================================================================
 * Observables at each site
 * ================================================================ */

/* Z₃ coarse spin: s_i = (trit_0 + trit_1 + trit_2) mod 3 */
static inline int z3_spin(int i) {
    return (lattice[i][0] + lattice[i][1] + lattice[i][2]) % Z3;
}

/* Density: ρ_i = (number of non-zero trits) / 3 */
static inline double density(int i) {
    int nz = 0;
    for (int t = 0; t < L_LOCAL; t++) {
        if (lattice[i][t] != 0) nz++;
    }
    return nz / 3.0;
}

/* ================================================================
 * Correlation measurement (all-pairs, direct)
 * ================================================================ */

/* Accumulators for correlations */
static double corr_z3_delta[MAX_DIST_BINS];   /* ⟨δ(s_i,s_j)⟩ accumulator */
static double corr_z3_complex[MAX_DIST_BINS]; /* Re⟨m_i m_j*⟩ accumulator */
static double corr_density[MAX_DIST_BINS];    /* ⟨ρ_i ρ_j⟩ accumulator */
static double corr_density_mean;              /* ⟨ρ⟩ accumulator */
static long   corr_count[MAX_DIST_BINS];      /* pair count per bin */
static long   corr_n_samples;                 /* number of samples */
static double corr_density_mean_acc;          /* running sum of ⟨ρ⟩ */

/* ω = e^{2πi/3}: Re(ω^k) and Im(ω^k) for k=0,1,2 */
static const double omega_re[3] = { 1.0, -0.5, -0.5 };
static const double omega_im[3] = { 0.0, 0.8660254037844386, -0.8660254037844386 };

static void reset_correlations(void) {
    for (int r = 0; r <= max_bin; r++) {
        corr_z3_delta[r] = 0.0;
        corr_z3_complex[r] = 0.0;
        corr_density[r] = 0.0;
        corr_count[r] = 0;
    }
    corr_n_samples = 0;
    corr_density_mean_acc = 0.0;
}

static void measure_correlations(void) {
    /* Precompute per-site observables */
    int   sp[MAX_SITES];
    double re_m[MAX_SITES], im_m[MAX_SITES];
    double rho[MAX_SITES];
    double rho_mean = 0.0;

    for (int i = 0; i < N_sites; i++) {
        sp[i] = z3_spin(i);
        re_m[i] = omega_re[sp[i]];
        im_m[i] = omega_im[sp[i]];
        rho[i] = density(i);
        rho_mean += rho[i];
    }
    rho_mean /= N_sites;
    corr_density_mean_acc += rho_mean;
    corr_n_samples++;

    /* All-pairs correlation. For each pair (i < j), accumulate into distance bin. */
    for (int i = 0; i < N_sites; i++) {
        for (int j = i + 1; j < N_sites; j++) {
            int bin = get_dist_bin(i, j);
            if (bin < 1 || bin > max_bin) continue;

            /* Z₃ delta correlator: δ(s_i, s_j) */
            corr_z3_delta[bin] += (sp[i] == sp[j]) ? 1.0 : 0.0;

            /* Z₃ complex correlator: Re(m_i * m_j*) = Re(ω^{s_i}) Re(ω^{s_j}) + Im(ω^{s_i}) Im(ω^{s_j}) */
            corr_z3_complex[bin] += re_m[i] * re_m[j] + im_m[i] * im_m[j];

            /* Density-density: ρ_i * ρ_j */
            corr_density[bin] += rho[i] * rho[j];

            corr_count[bin]++;
        }
    }
}

/* ================================================================
 * Correlation length extraction via exponential fit
 * ================================================================ */

/* Fit C(r) = A * exp(-r/ξ) using log-linear regression on bins with C(r) > 0.
 * Returns ξ. Sets *A_out if non-NULL. Returns -1 on failure. */
static double fit_correlation_length(double *corr_vals, int n_bins, double *A_out) {
    /* Use bins r = 1..n_bins where corr_vals[r] > threshold */
    double sum_r = 0, sum_y = 0, sum_rr = 0, sum_ry = 0;
    int count = 0;
    double threshold = 1e-12;

    for (int r = 1; r <= n_bins && r <= max_bin; r++) {
        if (corr_vals[r] <= threshold) continue;
        double y = log(corr_vals[r]);
        sum_r += r;
        sum_y += y;
        sum_rr += (double)r * r;
        sum_ry += (double)r * y;
        count++;
    }

    if (count < 3) return -1.0; /* not enough data */

    double denom = count * sum_rr - sum_r * sum_r;
    if (fabs(denom) < 1e-30) return -1.0;

    double slope = (count * sum_ry - sum_r * sum_y) / denom;
    double intercept = (sum_y - slope * sum_r) / count;

    if (slope >= 0) return -1.0; /* no decay → infinite or invalid */

    double xi = -1.0 / slope;
    if (A_out) *A_out = exp(intercept);
    return xi;
}

/* ================================================================
 * Output routines
 * ================================================================ */

static void print_correlations(int L_val, double mu) {
    if (corr_n_samples == 0) return;

    double rho_avg = corr_density_mean_acc / corr_n_samples;

    /* Normalize and compute connected correlators */
    double G_delta[MAX_DIST_BINS];   /* ⟨δ(s_i,s_j)⟩ - 1/3 */
    double C_complex[MAX_DIST_BINS]; /* Re⟨m_i m_j*⟩ */
    double G_rho[MAX_DIST_BINS];     /* ⟨ρ_i ρ_j⟩ - ⟨ρ⟩² */

    printf("\n=== Correlations: L=%d, mu=%.4f, samples=%ld, <rho>=%.4f ===\n",
           L_val, mu, corr_n_samples, rho_avg);
    printf("%4s  %10s  %12s  %12s  %12s  %10s\n",
           "r", "count", "G_delta(r)", "C_z3(r)", "G_rho(r)", "pairs");

    int fit_max = L_val / 2;

    for (int r = 1; r <= max_bin && r <= fit_max; r++) {
        if (corr_count[r] == 0) {
            G_delta[r] = 0;
            C_complex[r] = 0;
            G_rho[r] = 0;
            continue;
        }
        double norm = (double)corr_count[r];
        G_delta[r] = corr_z3_delta[r] / norm - 1.0 / 3.0;
        C_complex[r] = corr_z3_complex[r] / norm;
        G_rho[r] = corr_density[r] / norm - rho_avg * rho_avg;

        printf("%4d  %10ld  %12.6e  %12.6e  %12.6e  %10ld\n",
               r, (long)(norm / corr_n_samples), G_delta[r], C_complex[r], G_rho[r],
               corr_count[r]);
    }

    /* Fit correlation lengths */
    /* For C_complex, take absolute value for fitting */
    double C_abs[MAX_DIST_BINS];
    double G_rho_abs[MAX_DIST_BINS];
    double G_delta_abs[MAX_DIST_BINS];
    for (int r = 1; r <= max_bin; r++) {
        C_abs[r] = fabs(C_complex[r]);
        G_rho_abs[r] = fabs(G_rho[r]);
        G_delta_abs[r] = fabs(G_delta[r]);
    }

    double A_z3, A_rho, A_delta;
    double xi_z3 = fit_correlation_length(C_abs, fit_max, &A_z3);
    double xi_rho = fit_correlation_length(G_rho_abs, fit_max, &A_rho);
    double xi_delta = fit_correlation_length(G_delta_abs, fit_max, &A_delta);

    printf("\n--- Correlation lengths ---\n");
    printf("xi_Z3_complex = %.4f  (A = %.4e)\n", xi_z3, A_z3);
    printf("xi_Z3_delta   = %.4f  (A = %.4e)\n", xi_delta, A_delta);
    printf("xi_density    = %.4f  (A = %.4e)\n", xi_rho, A_rho);

    if (xi_z3 > 0 && xi_rho > 0) {
        printf("xi_Z3 / xi_DP = %.4f\n", xi_z3 / xi_rho);
    }

    /* Machine-readable summary line */
    printf("\nSUMMARY L=%d mu=%.4f rho=%.4f xi_z3=%.4f xi_delta=%.4f xi_rho=%.4f samples=%ld\n",
           L_val, mu, rho_avg, xi_z3, xi_delta, xi_rho, corr_n_samples);
}

/* ================================================================
 * Single run: one (L, mu) point
 * ================================================================ */

static void run_single(int L_val, double mu, int burnin, int measure_sweeps,
                        int sample_interval) {
    L = L_val;
    N_sites = L * L;

    if (N_sites > MAX_SITES) {
        fprintf(stderr, "ERROR: L=%d gives %d sites > MAX_SITES=%d\n",
                L_val, N_sites, MAX_SITES);
        return;
    }

    build_neighbors();
    build_dist_bins();
    init_lattice();

    printf("Running: L=%d (%d sites), mu=%.4f, burnin=%d, measure=%d, sample_every=%d\n",
           L_val, N_sites, mu, burnin, measure_sweeps, sample_interval);
    fflush(stdout);

    /* Burnin */
    for (int sweep = 0; sweep < burnin; sweep++) {
        do_sweep(mu);
        if ((sweep + 1) % 1000 == 0) {
            /* Quick density check */
            double rho_avg = 0;
            for (int i = 0; i < N_sites; i++) rho_avg += density(i);
            rho_avg /= N_sites;
            fprintf(stderr, "  burnin %d/%d  <rho>=%.4f\n", sweep + 1, burnin, rho_avg);
        }
    }

    /* Measurement phase */
    reset_correlations();

    for (int sweep = 0; sweep < measure_sweeps; sweep++) {
        do_sweep(mu);

        if ((sweep + 1) % sample_interval == 0) {
            measure_correlations();
            if (corr_n_samples % 10 == 0) {
                fprintf(stderr, "  measure %d/%d  samples=%ld\n",
                        sweep + 1, measure_sweeps, corr_n_samples);
            }
        }
    }

    print_correlations(L_val, mu);
}

/* ================================================================
 * Full parameter scan
 * ================================================================ */

static void run_scan(void) {
    int    L_vals[]  = {20, 40, 60};
    double mu_vals[] = {0.003, 0.005, 0.008, 0.010, 0.012};
    int n_L  = sizeof(L_vals)  / sizeof(L_vals[0]);
    int n_mu = sizeof(mu_vals) / sizeof(mu_vals[0]);

    int burnin = 5000;
    int measure_sweeps = 20000;
    int sample_interval = 100;  /* every 100 sweeps */

    printf("=== FULL PARAMETER SCAN ===\n");
    printf("Lattice sizes: ");
    for (int i = 0; i < n_L; i++) printf("%d ", L_vals[i]);
    printf("\nMutation rates: ");
    for (int i = 0; i < n_mu; i++) printf("%.4f ", mu_vals[i]);
    printf("\nBurnin=%d, Measure=%d, Sample every %d sweeps\n\n",
           burnin, measure_sweeps, sample_interval);

    /* Collect summary data for finite-size scaling */
    printf("\n======================================================\n");
    printf("Beginning scan...\n");
    printf("======================================================\n\n");

    double xi_z3_table[3][5], xi_rho_table[3][5];

    for (int iL = 0; iL < n_L; iL++) {
        for (int imu = 0; imu < n_mu; imu++) {
            /* Re-seed for reproducibility per run */
            seed_rng(42 + iL * 100 + imu);

            run_single(L_vals[iL], mu_vals[imu], burnin, measure_sweeps,
                       sample_interval);

            /* Parse the last SUMMARY line's xi values — they're already printed.
             * For in-program use, re-extract from accumulators. */
            double rho_avg = corr_density_mean_acc / corr_n_samples;
            int fit_max = L_vals[iL] / 2;

            double C_abs[MAX_DIST_BINS], G_rho_abs[MAX_DIST_BINS];
            for (int r = 1; r <= max_bin; r++) {
                double norm = (corr_count[r] > 0) ? (double)corr_count[r] : 1.0;
                C_abs[r] = fabs(corr_z3_complex[r] / norm);
                G_rho_abs[r] = fabs(corr_density[r] / norm - rho_avg * rho_avg);
            }

            xi_z3_table[iL][imu]  = fit_correlation_length(C_abs, fit_max, NULL);
            xi_rho_table[iL][imu] = fit_correlation_length(G_rho_abs, fit_max, NULL);

            printf("\n");
            fflush(stdout);
        }
    }

    /* ============================================================
     * Finite-size scaling summary
     * ============================================================ */
    printf("\n");
    printf("================================================================\n");
    printf("FINITE-SIZE SCALING SUMMARY\n");
    printf("================================================================\n\n");

    printf("--- xi_Z3 (complex correlator) ---\n");
    printf("%8s", "mu\\L");
    for (int iL = 0; iL < n_L; iL++) printf("  %8d", L_vals[iL]);
    printf("  %8s\n", "xi/L(max)");
    for (int imu = 0; imu < n_mu; imu++) {
        printf("%8.4f", mu_vals[imu]);
        double max_ratio = 0;
        for (int iL = 0; iL < n_L; iL++) {
            printf("  %8.3f", xi_z3_table[iL][imu]);
            if (xi_z3_table[iL][imu] > 0) {
                double ratio = xi_z3_table[iL][imu] / L_vals[iL];
                if (ratio > max_ratio) max_ratio = ratio;
            }
        }
        printf("  %8.3f\n", max_ratio);
    }

    printf("\n--- xi_DP (density correlator) ---\n");
    printf("%8s", "mu\\L");
    for (int iL = 0; iL < n_L; iL++) printf("  %8d", L_vals[iL]);
    printf("  %8s\n", "xi/L(max)");
    for (int imu = 0; imu < n_mu; imu++) {
        printf("%8.4f", mu_vals[imu]);
        double max_ratio = 0;
        for (int iL = 0; iL < n_L; iL++) {
            printf("  %8.3f", xi_rho_table[iL][imu]);
            if (xi_rho_table[iL][imu] > 0) {
                double ratio = xi_rho_table[iL][imu] / L_vals[iL];
                if (ratio > max_ratio) max_ratio = ratio;
            }
        }
        printf("  %8.3f\n", max_ratio);
    }

    printf("\n--- xi_Z3 / xi_DP ratio (tests if sectors decouple) ---\n");
    printf("%8s", "mu\\L");
    for (int iL = 0; iL < n_L; iL++) printf("  %8d", L_vals[iL]);
    printf("\n");
    for (int imu = 0; imu < n_mu; imu++) {
        printf("%8.4f", mu_vals[imu]);
        for (int iL = 0; iL < n_L; iL++) {
            if (xi_z3_table[iL][imu] > 0 && xi_rho_table[iL][imu] > 0) {
                printf("  %8.3f", xi_z3_table[iL][imu] / xi_rho_table[iL][imu]);
            } else {
                printf("  %8s", "N/A");
            }
        }
        printf("\n");
    }

    /* Finite-size scaling: attempt to extract ν */
    printf("\n--- Finite-size scaling: xi(L) at fixed mu ---\n");
    printf("If xi ~ L^{1/nu} at criticality, then log(xi)/log(L) → 1/nu\n\n");

    for (int imu = 0; imu < n_mu; imu++) {
        printf("mu = %.4f:\n", mu_vals[imu]);

        /* Z₃ sector */
        int valid_z3 = 1;
        for (int iL = 0; iL < n_L; iL++) {
            if (xi_z3_table[iL][imu] <= 0) valid_z3 = 0;
        }
        if (valid_z3 && n_L >= 2) {
            /* Use largest two sizes for slope */
            double logL1 = log(L_vals[n_L - 2]);
            double logL2 = log(L_vals[n_L - 1]);
            double logxi1 = log(xi_z3_table[n_L - 2][imu]);
            double logxi2 = log(xi_z3_table[n_L - 1][imu]);
            double slope = (logxi2 - logxi1) / (logL2 - logL1);
            printf("  Z3:  d(log xi)/d(log L) = %.3f", slope);
            if (slope > 0.01) {
                double nu_eff = 1.0 / slope;
                printf("  →  1/nu_eff = %.3f  →  nu_eff = %.3f", slope, nu_eff);
                if (fabs(nu_eff - 0.833) < fabs(nu_eff - 0.734))
                    printf("  [closer to Potts 5/6=0.833]");
                else
                    printf("  [closer to DP nu_perp=0.734]");
            }
            printf("\n");
        } else {
            printf("  Z3:  insufficient data\n");
        }

        /* DP sector */
        int valid_rho = 1;
        for (int iL = 0; iL < n_L; iL++) {
            if (xi_rho_table[iL][imu] <= 0) valid_rho = 0;
        }
        if (valid_rho && n_L >= 2) {
            double logL1 = log(L_vals[n_L - 2]);
            double logL2 = log(L_vals[n_L - 1]);
            double logxi1 = log(xi_rho_table[n_L - 2][imu]);
            double logxi2 = log(xi_rho_table[n_L - 1][imu]);
            double slope = (logxi2 - logxi1) / (logL2 - logL1);
            printf("  DP:  d(log xi)/d(log L) = %.3f", slope);
            if (slope > 0.01) {
                double nu_eff = 1.0 / slope;
                printf("  →  1/nu_eff = %.3f  →  nu_eff = %.3f", slope, nu_eff);
                if (fabs(nu_eff - 0.833) < fabs(nu_eff - 0.734))
                    printf("  [closer to Potts 5/6=0.833]");
                else
                    printf("  [closer to DP nu_perp=0.734]");
            }
            printf("\n");
        } else {
            printf("  DP:  insufficient data\n");
        }
        printf("\n");
    }

    /* Reference values */
    printf("================================================================\n");
    printf("REFERENCE VALUES:\n");
    printf("  2D Z3 Potts:  nu = 5/6 = 0.833,  eta = 4/15 = 0.267\n");
    printf("  2D DP:        nu_perp = 0.7338,   nu_par = 1.2950\n");
    printf("================================================================\n");
    printf("\nDIAGNOSTIC:\n");
    printf("  If xi_Z3 / xi_DP ≈ 1 at all (L, mu): sectors are locked.\n");
    printf("  If xi_Z3 / xi_DP varies or >> 1: two independent sectors.\n");
    printf("  If nu_eff ≈ 0.83: Potts universality class.\n");
    printf("  If nu_eff ≈ 0.73: Directed Percolation universality class.\n");
    printf("================================================================\n");
}

/* ================================================================
 * Main
 * ================================================================ */

static void usage(const char *prog) {
    fprintf(stderr, "Usage: %s [options]\n", prog);
    fprintf(stderr, "  --scan              Run full parameter scan (default: single run)\n");
    fprintf(stderr, "  --L <int>           Lattice size (default: 20)\n");
    fprintf(stderr, "  --mu <float>        Mutation rate (default: 0.005)\n");
    fprintf(stderr, "  --burnin <int>      Burnin sweeps (default: 5000)\n");
    fprintf(stderr, "  --measure <int>     Measurement sweeps (default: 20000)\n");
    fprintf(stderr, "  --sample <int>      Sample every N sweeps (default: 100)\n");
    fprintf(stderr, "  --seed <int>        RNG seed (default: 42)\n");
    fprintf(stderr, "\nCompile: cc -O3 -o correlation_2d_soup correlation_2d_soup.c -lm\n");
}

int main(int argc, char **argv) {
    int do_scan = 0;
    int L_val = 20;
    double mu = 0.005;
    int burnin = 5000;
    int measure_sweeps = 20000;
    int sample_interval = 100;
    uint64_t seed = 42;

    static struct option long_opts[] = {
        {"scan",    no_argument,       NULL, 'S'},
        {"L",       required_argument, NULL, 'L'},
        {"mu",      required_argument, NULL, 'm'},
        {"burnin",  required_argument, NULL, 'b'},
        {"measure", required_argument, NULL, 'M'},
        {"sample",  required_argument, NULL, 's'},
        {"seed",    required_argument, NULL, 'r'},
        {"help",    no_argument,       NULL, 'h'},
        {NULL, 0, NULL, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "SL:m:b:M:s:r:h", long_opts, NULL)) != -1) {
        switch (opt) {
            case 'S': do_scan = 1; break;
            case 'L': L_val = atoi(optarg); break;
            case 'm': mu = atof(optarg); break;
            case 'b': burnin = atoi(optarg); break;
            case 'M': measure_sweeps = atoi(optarg); break;
            case 's': sample_interval = atoi(optarg); break;
            case 'r': seed = (uint64_t)atoll(optarg); break;
            case 'h': usage(argv[0]); return 0;
            default:  usage(argv[0]); return 1;
        }
    }

    printf("correlation_2d_soup — Z3 & density correlation functions\n");
    printf("=========================================================\n");

    if (do_scan) {
        run_scan();
    } else {
        seed_rng(seed);
        run_single(L_val, mu, burnin, measure_sweeps, sample_interval);
    }

    return 0;
}
