/*
 * Wilson Loop Measurement on 2D Z_3 Soup
 * =======================================
 * Measures Wilson-loop-like observables on a flat triangular lattice
 * with periodic boundary conditions, running the Z_3 soup dynamics.
 *
 * Physics goal: detect confinement via area-law vs perimeter-law scaling
 * of Wilson loops W(R,T) = <prod_{links in C} U_link>.
 *
 * Link variables: U_{ij} = omega^{(s_i - s_j) mod 3}, omega = e^{2 pi i/3}
 * Wilson loop: product of U around a closed rectangular path R x T
 *
 * Diagnostics:
 *   - W(R,T) for R,T = 1..MAX_LOOP
 *   - Creutz ratios chi(R,T) = -ln(W(R,T)*W(R-1,T-1)/(W(R-1,T)*W(R,T-1)))
 *   - Area-law fit: -ln|W| ~ sigma * R*T
 *   - Perimeter-law fit: -ln|W| ~ mu * 2(R+T)
 *   - Scan over mutation rates to look for confinement-deconfinement transition
 *
 * CG grounding:
 *   - Z_3 trits from center symmetry (Def 0.1.2)
 *   - VM interactions same as Stella Soup (Prop 0.0.XXd)
 *   - Confinement = area law = Z_3 disorder = unbroken center symmetry
 *
 * Compile: cc -O3 -o wilson_loop_2d wilson_loop_2d.c -lm
 * Run:     ./wilson_loop_2d [--L 20] [--mu 0.005] [--scan]
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <getopt.h>
#include <time.h>

/* ================================================================
 * Constants
 * ================================================================ */

#define Z3          3
#define L_LOCAL     3       /* trits per site */
#define MAX_LOOP    5       /* max Wilson loop size */
#define MAX_L       64      /* max lattice dimension */
#define PI          3.14159265358979323846

/* Default simulation parameters */
#define DEFAULT_L           20
#define DEFAULT_BURNIN      5000
#define DEFAULT_MEASURE     10000
#define DEFAULT_SAMPLE_GAP  10
#define DEFAULT_MAX_STEPS   729
#define DEFAULT_MU          0.005

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
 * Triangular Lattice with Periodic BC
 * ================================================================
 *
 * Site (x,y) on an L x L grid. Each site has 6 neighbors:
 *   (x+1,y), (x-1,y), (x,y+1), (x,y-1), (x+1,y-1), (x-1,y+1)
 * all mod L.
 *
 * Each site holds L_LOCAL trits (a small Z_3 program).
 */

typedef struct {
    int L;                              /* lattice dimension */
    int N;                              /* L*L total sites */
    unsigned char data[MAX_L * MAX_L][L_LOCAL];   /* trit data per site */
} Lattice;

/* Flat index from (x,y) */
static inline int idx(int L, int x, int y) {
    return ((y % L + L) % L) * L + ((x % L + L) % L);
}

/* Get coordinates from flat index */
static inline void coords(int L, int i, int *x, int *y) {
    *x = i % L;
    *y = i / L;
}

/* 6 neighbor offsets for triangular lattice */
static const int dx6[6] = { 1, -1,  0,  0,  1, -1};
static const int dy6[6] = { 0,  0,  1, -1, -1,  1};

/* Get neighbor index */
static inline int neighbor(int L, int x, int y, int dir) {
    return idx(L, x + dx6[dir], y + dy6[dir]);
}

static void lattice_init(Lattice *lat, int L) {
    lat->L = L;
    lat->N = L * L;
    for (int i = 0; i < lat->N; i++)
        for (int t = 0; t < L_LOCAL; t++)
            lat->data[i][t] = rng_int(Z3);
}

/* ================================================================
 * VM (identical to Stella Soup)
 * ================================================================ */

static void execute_tape(unsigned char *tape, int tape_len, int max_steps) {
    int ip = 0;
    int h0 = 0;
    int h1 = tape_len / 2;
    int steps = 0;

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
                        if (tape[pos] == 1 && tape[pos + 1] == 2) depth++;
                        else if (tape[pos] == 2 && tape[pos + 1] == 0) depth--;
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
                        if (tape[pos] == 2 && tape[pos + 1] == 0) depth++;
                        else if (tape[pos] == 1 && tape[pos + 1] == 2) depth--;
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
 * Z_3 Link Variables and Wilson Loops
 * ================================================================
 *
 * Effective link variable from site i to site j:
 *   U_{ij} = omega^{(s_i - s_j) mod 3}
 *
 * where s_i is the "color charge" at site i, defined as the sum
 * of its L_LOCAL trits mod 3.
 *
 * Wilson loop W(C) = prod_{(i,j) in C} U_{ij}
 *   = omega^{sum_{(i,j) in C} (s_i - s_j) mod 3}
 *
 * For a closed loop the sum telescopes, BUT on a discrete lattice
 * with non-trivial field configurations, the winding can be non-zero.
 *
 * We compute the Z_3 phase: W = omega^q where q in {0,1,2}.
 * The real part Re(W) = cos(2 pi q / 3):
 *   q=0: Re(W) = 1,  q=1: Re(W) = -0.5,  q=2: Re(W) = -0.5
 *
 * For ensemble average: <W> = <Re(W)> (imaginary part vanishes by Z_3 symmetry)
 */

/* Color charge at site i: sum of its trits mod 3 */
static inline int color_charge(const Lattice *lat, int i) {
    int s = 0;
    for (int t = 0; t < L_LOCAL; t++)
        s += lat->data[i][t];
    return s % Z3;
}

/*
 * Measure Wilson loop of size R x T starting at site (x0, y0).
 *
 * Path on triangular lattice: we use the two basis vectors
 *   e1 = (1, 0)    [+x direction]
 *   e2 = (0, 1)    [+y direction]
 *
 * Rectangular loop:
 *   Bottom: (x0,y0) -> (x0+R, y0)     along e1, R steps
 *   Right:  (x0+R, y0) -> (x0+R, y0+T) along e2, T steps
 *   Top:    (x0+R, y0+T) -> (x0, y0+T)  along -e1, R steps
 *   Left:   (x0, y0+T) -> (x0, y0)      along -e2, T steps
 *
 * For each oriented link (i -> j), accumulate (s_i - s_j) mod 3.
 *
 * Returns omega^q as complex: re = cos(2 pi q/3), im = sin(2 pi q/3).
 */
static void wilson_loop(const Lattice *lat, int x0, int y0,
                         int R, int T, double *re, double *im)
{
    int L = lat->L;
    int q = 0;  /* accumulated Z_3 phase */

    /* Bottom edge: x0..x0+R-1 at y=y0, direction +x */
    for (int r = 0; r < R; r++) {
        int si = idx(L, x0 + r, y0);
        int sj = idx(L, x0 + r + 1, y0);
        q += color_charge(lat, si) - color_charge(lat, sj);
    }

    /* Right edge: y0..y0+T-1 at x=x0+R, direction +y */
    for (int t = 0; t < T; t++) {
        int si = idx(L, x0 + R, y0 + t);
        int sj = idx(L, x0 + R, y0 + t + 1);
        q += color_charge(lat, si) - color_charge(lat, sj);
    }

    /* Top edge: x0+R..x0+1 at y=y0+T, direction -x */
    for (int r = R; r > 0; r--) {
        int si = idx(L, x0 + r, y0 + T);
        int sj = idx(L, x0 + r - 1, y0 + T);
        q += color_charge(lat, si) - color_charge(lat, sj);
    }

    /* Left edge: y0+T..y0+1 at x=x0, direction -y */
    for (int t = T; t > 0; t--) {
        int si = idx(L, x0, y0 + t);
        int sj = idx(L, x0, y0 + t - 1);
        q += color_charge(lat, si) - color_charge(lat, sj);
    }

    /* Reduce q mod 3 to {0,1,2} */
    q = ((q % Z3) + Z3) % Z3;
    double angle = 2.0 * PI * q / 3.0;
    *re = cos(angle);
    *im = sin(angle);
}

/* ================================================================
 * Polyakov Loop (wrapping around y-direction)
 * ================================================================
 *
 * P(x) = prod_{y=0}^{L-1} U_{(x,y)->(x,y+1)}
 *       = omega^{sum_y (s(x,y) - s(x,y+1)) mod 3}
 *
 * For periodic BC, this telescopes to 0 in the Abelian case...
 * but with the soup dynamics, we measure it as a diagnostic.
 * Non-zero <|P|> signals deconfinement.
 */
static void polyakov_loop(const Lattice *lat, double *re_avg, double *im_avg)
{
    int L = lat->L;
    double re_sum = 0.0, im_sum = 0.0;

    for (int x = 0; x < L; x++) {
        int q = 0;
        for (int y = 0; y < L; y++) {
            int si = idx(L, x, y);
            int sj = idx(L, x, (y + 1) % L);
            q += color_charge(lat, si) - color_charge(lat, sj);
        }
        q = ((q % Z3) + Z3) % Z3;
        double angle = 2.0 * PI * q / 3.0;
        re_sum += cos(angle);
        im_sum += sin(angle);
    }

    *re_avg = re_sum / L;
    *im_avg = im_sum / L;
}

/* ================================================================
 * Soup Dynamics
 * ================================================================
 *
 * One sweep = N random pair interactions + mutations.
 * Interaction: pick random site i, pick random neighbor j,
 * concatenate their trit strings, execute VM, write back.
 */

static void soup_sweep(Lattice *lat, double mu, int max_steps)
{
    int L = lat->L;
    int N = lat->N;
    int tape_len = 2 * L_LOCAL;
    unsigned char tape[2 * L_LOCAL];

    /* N random pair interactions */
    for (int n = 0; n < N; n++) {
        int i = rng_int(N);
        int xi, yi;
        coords(L, i, &xi, &yi);

        /* Pick random neighbor */
        int dir = rng_int(6);
        int j = neighbor(L, xi, yi, dir);

        /* Build tape: site i trits | site j trits */
        memcpy(tape, lat->data[i], L_LOCAL);
        memcpy(tape + L_LOCAL, lat->data[j], L_LOCAL);

        /* Execute VM */
        execute_tape(tape, tape_len, max_steps);

        /* Write back */
        memcpy(lat->data[i], tape, L_LOCAL);
        memcpy(lat->data[j], tape + L_LOCAL, L_LOCAL);
    }

    /* Mutations: flip random trits with rate mu */
    int n_mutations = (int)(N * L_LOCAL * mu);
    for (int m = 0; m < n_mutations; m++) {
        int i = rng_int(N);
        int t = rng_int(L_LOCAL);
        lat->data[i][t] = rng_int(Z3);
    }
}

/* ================================================================
 * Measurement Accumulator
 * ================================================================ */

typedef struct {
    /* Wilson loop averages: W_re[R][T], W_im[R][T] for R,T = 1..MAX_LOOP */
    double W_re[MAX_LOOP + 1][MAX_LOOP + 1];
    double W_im[MAX_LOOP + 1][MAX_LOOP + 1];
    double W2_re[MAX_LOOP + 1][MAX_LOOP + 1];   /* for error estimation */
    int    W_count[MAX_LOOP + 1][MAX_LOOP + 1];

    /* Polyakov loop */
    double P_re, P_im;
    double P_abs;
    int P_count;

    /* Trit distribution */
    double entropy;
    int n_samples;
} Measurements;

static void meas_init(Measurements *m) {
    memset(m, 0, sizeof(Measurements));
}

/* Measure all Wilson loops on current configuration, spatially averaged */
static void meas_wilson(Measurements *m, const Lattice *lat)
{
    int L = lat->L;

    for (int R = 1; R <= MAX_LOOP && R <= L / 2; R++) {
        for (int T = 1; T <= MAX_LOOP && T <= L / 2; T++) {
            double re_sum = 0.0, im_sum = 0.0;
            int count = 0;

            /* Average over all starting positions */
            for (int x0 = 0; x0 < L; x0++) {
                for (int y0 = 0; y0 < L; y0++) {
                    double re, im;
                    wilson_loop(lat, x0, y0, R, T, &re, &im);
                    re_sum += re;
                    im_sum += im;
                    count++;
                }
            }

            double w_re = re_sum / count;
            double w_im = im_sum / count;
            m->W_re[R][T]  += w_re;
            m->W_im[R][T]  += w_im;
            m->W2_re[R][T] += w_re * w_re;
            m->W_count[R][T]++;
        }
    }

    /* Polyakov loop */
    double pre, pim;
    polyakov_loop(lat, &pre, &pim);
    m->P_re  += pre;
    m->P_im  += pim;
    m->P_abs += sqrt(pre * pre + pim * pim);
    m->P_count++;

    /* Trit entropy */
    int counts[Z3] = {0};
    for (int i = 0; i < lat->N; i++)
        for (int t = 0; t < L_LOCAL; t++)
            counts[lat->data[i][t]]++;
    int total = lat->N * L_LOCAL;
    double H = 0.0;
    for (int c = 0; c < Z3; c++) {
        if (counts[c] > 0) {
            double p = (double)counts[c] / total;
            H -= p * log2(p);
        }
    }
    m->entropy += H;
    m->n_samples++;
}

/* ================================================================
 * Analysis and Reporting
 * ================================================================ */

static void report_wilson(const Measurements *m, double mu, int L)
{
    printf("\n");
    printf("================================================================\n");
    printf("Wilson Loop Results: mu = %.4f, L = %d\n", mu, L);
    printf("================================================================\n");

    /* Print <W(R,T)> table */
    printf("\n<W(R,T)> (real part, spatially + MC averaged):\n");
    printf("%4s", "R\\T");
    for (int T = 1; T <= MAX_LOOP && T <= L / 2; T++)
        printf("  T=%-5d", T);
    printf("\n");

    double W_avg[MAX_LOOP + 1][MAX_LOOP + 1];
    double W_err[MAX_LOOP + 1][MAX_LOOP + 1];

    for (int R = 1; R <= MAX_LOOP && R <= L / 2; R++) {
        printf("R=%d ", R);
        for (int T = 1; T <= MAX_LOOP && T <= L / 2; T++) {
            int nc = m->W_count[R][T];
            if (nc > 0) {
                W_avg[R][T] = m->W_re[R][T] / nc;
                double var = m->W2_re[R][T] / nc - W_avg[R][T] * W_avg[R][T];
                W_err[R][T] = (nc > 1) ? sqrt(fabs(var) / (nc - 1)) : 0.0;
                printf(" %7.4f ", W_avg[R][T]);
            } else {
                W_avg[R][T] = 0.0;
                W_err[R][T] = 0.0;
                printf("   ---   ");
            }
        }
        printf("\n");
    }

    /* Print -ln|W(R,T)| table */
    printf("\n-ln|<W(R,T)>|:\n");
    printf("%4s", "R\\T");
    for (int T = 1; T <= MAX_LOOP && T <= L / 2; T++)
        printf("  T=%-5d", T);
    printf("\n");

    double V[MAX_LOOP + 1][MAX_LOOP + 1]; /* V = -ln|W| */

    for (int R = 1; R <= MAX_LOOP && R <= L / 2; R++) {
        printf("R=%d ", R);
        for (int T = 1; T <= MAX_LOOP && T <= L / 2; T++) {
            double absW = fabs(W_avg[R][T]);
            if (absW > 1e-12) {
                V[R][T] = -log(absW);
                printf(" %7.4f ", V[R][T]);
            } else {
                V[R][T] = 99.0; /* sentinel: loop is zero */
                printf("   inf   ");
            }
        }
        printf("\n");
    }

    /* ---- Area law fit: V(R,T) = sigma * R*T + const ---- */
    /* Linear regression: V = sigma * A + c, where A = R*T */
    double sum_A = 0, sum_V = 0, sum_AV = 0, sum_AA = 0;
    int n_pts = 0;
    int max_rt = L / 2;
    if (max_rt > MAX_LOOP) max_rt = MAX_LOOP;

    for (int R = 1; R <= max_rt; R++) {
        for (int T = 1; T <= max_rt; T++) {
            if (V[R][T] < 50.0) { /* skip sentinels */
                double A = R * T;
                sum_A  += A;
                sum_V  += V[R][T];
                sum_AV += A * V[R][T];
                sum_AA += A * A;
                n_pts++;
            }
        }
    }

    double sigma_area = 0.0, c_area = 0.0, r2_area = 0.0;
    if (n_pts >= 2) {
        double denom = n_pts * sum_AA - sum_A * sum_A;
        if (fabs(denom) > 1e-20) {
            sigma_area = (n_pts * sum_AV - sum_A * sum_V) / denom;
            c_area = (sum_V - sigma_area * sum_A) / n_pts;

            /* R^2 */
            double mean_V = sum_V / n_pts;
            double ss_tot = 0, ss_res = 0;
            for (int R = 1; R <= max_rt; R++) {
                for (int T = 1; T <= max_rt; T++) {
                    if (V[R][T] < 50.0) {
                        double pred = sigma_area * R * T + c_area;
                        ss_res += (V[R][T] - pred) * (V[R][T] - pred);
                        ss_tot += (V[R][T] - mean_V) * (V[R][T] - mean_V);
                    }
                }
            }
            r2_area = (ss_tot > 1e-20) ? 1.0 - ss_res / ss_tot : 0.0;
        }
    }

    /* ---- Perimeter law fit: V(R,T) = mu_p * 2(R+T) + const ---- */
    double sum_P = 0, sum_VP = 0, sum_PP = 0;
    sum_V = 0; n_pts = 0;

    for (int R = 1; R <= max_rt; R++) {
        for (int T = 1; T <= max_rt; T++) {
            if (V[R][T] < 50.0) {
                double P = 2.0 * (R + T);
                sum_P  += P;
                sum_V  += V[R][T];
                sum_VP += P * V[R][T];
                sum_PP += P * P;
                n_pts++;
            }
        }
    }

    double mu_perim = 0.0, c_perim = 0.0, r2_perim = 0.0;
    if (n_pts >= 2) {
        double denom = n_pts * sum_PP - sum_P * sum_P;
        if (fabs(denom) > 1e-20) {
            mu_perim = (n_pts * sum_VP - sum_P * sum_V) / denom;
            c_perim = (sum_V - mu_perim * sum_P) / n_pts;

            double mean_V = sum_V / n_pts;
            double ss_tot = 0, ss_res = 0;
            for (int R = 1; R <= max_rt; R++) {
                for (int T = 1; T <= max_rt; T++) {
                    if (V[R][T] < 50.0) {
                        double pred = mu_perim * 2.0 * (R + T) + c_perim;
                        ss_res += (V[R][T] - pred) * (V[R][T] - pred);
                        ss_tot += (V[R][T] - mean_V) * (V[R][T] - mean_V);
                    }
                }
            }
            r2_perim = (ss_tot > 1e-20) ? 1.0 - ss_res / ss_tot : 0.0;
        }
    }

    printf("\nFit: -ln|W| = sigma * Area + const\n");
    printf("  sigma = %.6f, const = %.4f, R^2 = %.4f\n",
           sigma_area, c_area, r2_area);

    printf("\nFit: -ln|W| = mu * Perimeter + const\n");
    printf("  mu    = %.6f, const = %.4f, R^2 = %.4f\n",
           mu_perim, c_perim, r2_perim);

    if (r2_area > r2_perim + 0.05)
        printf("\n  ==> AREA LAW (confinement): R^2_area=%.3f >> R^2_perim=%.3f\n",
               r2_area, r2_perim);
    else if (r2_perim > r2_area + 0.05)
        printf("\n  ==> PERIMETER LAW (deconfinement): R^2_perim=%.3f >> R^2_area=%.3f\n",
               r2_perim, r2_area);
    else
        printf("\n  ==> INCONCLUSIVE: R^2_area=%.3f ~ R^2_perim=%.3f\n",
               r2_area, r2_perim);

    /* ---- Creutz ratios ---- */
    printf("\nCreutz ratios chi(R,T) = -ln(W(R,T)*W(R-1,T-1)/(W(R-1,T)*W(R,T-1))):\n");
    printf("  (In confining phase: chi -> sigma = const > 0)\n");
    printf("  (In deconfined phase: chi -> 0)\n\n");
    printf("%4s", "R\\T");
    for (int T = 2; T <= max_rt; T++)
        printf("  T=%-5d", T);
    printf("\n");

    for (int R = 2; R <= max_rt; R++) {
        printf("R=%d ", R);
        for (int T = 2; T <= max_rt; T++) {
            double w_rt   = fabs(W_avg[R][T]);
            double w_r1t1 = fabs(W_avg[R - 1][T - 1]);
            double w_r1t  = fabs(W_avg[R - 1][T]);
            double w_rt1  = fabs(W_avg[R][T - 1]);

            if (w_rt > 1e-12 && w_r1t1 > 1e-12 &&
                w_r1t > 1e-12 && w_rt1 > 1e-12) {
                double ratio = (w_rt * w_r1t1) / (w_r1t * w_rt1);
                if (ratio > 1e-20) {
                    double chi = -log(ratio);
                    printf(" %7.4f ", chi);
                } else {
                    printf("   inf   ");
                }
            } else {
                printf("   ---   ");
            }
        }
        printf("\n");
    }

    /* Polyakov loop */
    if (m->P_count > 0) {
        printf("\nPolyakov loop: <P> = %.4f + i*%.4f, <|P|> = %.4f\n",
               m->P_re / m->P_count,
               m->P_im / m->P_count,
               m->P_abs / m->P_count);
        printf("  (|P| ~ 0 => confined, |P| ~ 1 => deconfined)\n");
    }

    /* Entropy */
    if (m->n_samples > 0) {
        printf("\nTrit entropy: %.4f / %.4f (= %.1f%% of max)\n",
               m->entropy / m->n_samples, log2(Z3),
               100.0 * (m->entropy / m->n_samples) / log2(Z3));
    }
}

/* ================================================================
 * Run simulation at a given mutation rate
 * ================================================================ */

static void run_simulation(int L, double mu, int burnin, int measure,
                           int sample_gap, int max_steps, uint64_t seed,
                           Measurements *meas)
{
    rng_seed(seed);

    Lattice lat;
    lattice_init(&lat, L);
    meas_init(meas);

    printf("  Burning in (%d sweeps)...", burnin);
    fflush(stdout);
    for (int s = 0; s < burnin; s++)
        soup_sweep(&lat, mu, max_steps);
    printf(" done.\n");

    printf("  Measuring (%d sweeps, sample every %d)...", measure, sample_gap);
    fflush(stdout);

    int n_meas = 0;
    for (int s = 0; s < measure; s++) {
        soup_sweep(&lat, mu, max_steps);
        if ((s + 1) % sample_gap == 0) {
            meas_wilson(meas, &lat);
            n_meas++;
        }
    }
    printf(" done (%d measurements).\n", n_meas);
}

/* ================================================================
 * Main
 * ================================================================ */

static void usage(const char *prog) {
    printf("Wilson Loop Measurement on 2D Z_3 Soup\n");
    printf("Usage: %s [options]\n\n", prog);
    printf("Options:\n");
    printf("  --L N            Lattice size (default: %d)\n", DEFAULT_L);
    printf("  --mu F           Mutation rate (default: %.3f)\n", DEFAULT_MU);
    printf("  --burnin N       Burnin sweeps (default: %d)\n", DEFAULT_BURNIN);
    printf("  --measure N      Measurement sweeps (default: %d)\n", DEFAULT_MEASURE);
    printf("  --sample-gap N   Sweeps between samples (default: %d)\n", DEFAULT_SAMPLE_GAP);
    printf("  --max-steps N    Max VM steps (default: %d)\n", DEFAULT_MAX_STEPS);
    printf("  --seed N         Random seed\n");
    printf("  --scan           Scan mu from 0.001 to 0.020\n");
    printf("  --help           Show this help\n");
}

int main(int argc, char *argv[])
{
    int L = DEFAULT_L;
    double mu = DEFAULT_MU;
    int burnin = DEFAULT_BURNIN;
    int measure = DEFAULT_MEASURE;
    int sample_gap = DEFAULT_SAMPLE_GAP;
    int max_steps = DEFAULT_MAX_STEPS;
    uint64_t seed = 42;
    int do_scan = 0;

    static struct option long_options[] = {
        {"L",           required_argument, 0, 'L'},
        {"mu",          required_argument, 0, 'u'},
        {"burnin",      required_argument, 0, 'b'},
        {"measure",     required_argument, 0, 'm'},
        {"sample-gap",  required_argument, 0, 'g'},
        {"max-steps",   required_argument, 0, 's'},
        {"seed",        required_argument, 0, 'S'},
        {"scan",        no_argument,       0, 'c'},
        {"help",        no_argument,       0, 'h'},
        {0, 0, 0, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "hL:u:b:m:g:s:S:c",
                               long_options, NULL)) != -1) {
        switch (opt) {
        case 'L': L = atoi(optarg); break;
        case 'u': mu = atof(optarg); break;
        case 'b': burnin = atoi(optarg); break;
        case 'm': measure = atoi(optarg); break;
        case 'g': sample_gap = atoi(optarg); break;
        case 's': max_steps = atoi(optarg); break;
        case 'S': seed = (uint64_t)atol(optarg); break;
        case 'c': do_scan = 1; break;
        case 'h': usage(argv[0]); return 0;
        default:  usage(argv[0]); return 1;
        }
    }

    if (L > MAX_L) {
        fprintf(stderr, "ERROR: L=%d exceeds MAX_L=%d\n", L, MAX_L);
        return 1;
    }

    printf("================================================================\n");
    printf("Wilson Loop Measurement on 2D Z_3 Soup\n");
    printf("================================================================\n");
    printf("Lattice:        %d x %d triangular, periodic BC\n", L, L);
    printf("Sites:          %d\n", L * L);
    printf("Trits/site:     %d (tape_len = %d)\n", L_LOCAL, 2 * L_LOCAL);
    printf("Max VM steps:   %d\n", max_steps);
    printf("Seed:           %llu\n", (unsigned long long)seed);
    printf("================================================================\n");

    struct timespec t_start, t_end;
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    if (do_scan) {
        /* Scan mutation rates to look for confinement-deconfinement transition */
        double mu_values[] = {0.001, 0.002, 0.003, 0.005, 0.007,
                              0.010, 0.012, 0.015, 0.020};
        int n_mu = sizeof(mu_values) / sizeof(mu_values[0]);

        printf("\n*** MUTATION RATE SCAN ***\n");
        printf("Scanning %d values of mu to detect confinement transition.\n\n", n_mu);

        /* Summary table header */
        printf("%-8s  %8s  %8s  %8s  %8s  %8s  %8s  %8s\n",
               "mu", "W(1,1)", "W(2,2)", "W(3,3)", "sig_area",
               "R2_area", "R2_peri", "|P|");
        printf("--------  --------  --------  --------  --------  "
               "--------  --------  --------\n");

        for (int i = 0; i < n_mu; i++) {
            Measurements meas;
            run_simulation(L, mu_values[i], burnin, measure, sample_gap,
                           max_steps, seed + i, &meas);

            /* Extract summary numbers */
            double w11 = (meas.W_count[1][1] > 0) ?
                meas.W_re[1][1] / meas.W_count[1][1] : 0.0;
            double w22 = (meas.W_count[2][2] > 0) ?
                meas.W_re[2][2] / meas.W_count[2][2] : 0.0;
            double w33 = (meas.W_count[3][3] > 0) ?
                meas.W_re[3][3] / meas.W_count[3][3] : 0.0;
            double pabs = (meas.P_count > 0) ?
                meas.P_abs / meas.P_count : 0.0;

            /* Quick area-law fit for summary */
            double sum_A = 0, sum_V = 0, sum_AV = 0, sum_AA = 0;
            int npts = 0;
            int max_rt = L / 2;
            if (max_rt > MAX_LOOP) max_rt = MAX_LOOP;

            for (int R = 1; R <= max_rt; R++) {
                for (int T = 1; T <= max_rt; T++) {
                    int nc = meas.W_count[R][T];
                    if (nc > 0) {
                        double w = meas.W_re[R][T] / nc;
                        double absw = fabs(w);
                        if (absw > 1e-12) {
                            double v = -log(absw);
                            double A = R * T;
                            sum_A += A; sum_V += v;
                            sum_AV += A * v; sum_AA += A * A;
                            npts++;
                        }
                    }
                }
            }

            double sig = 0, r2a = 0;
            if (npts >= 2) {
                double denom = npts * sum_AA - sum_A * sum_A;
                if (fabs(denom) > 1e-20) {
                    sig = (npts * sum_AV - sum_A * sum_V) / denom;
                    double c = (sum_V - sig * sum_A) / npts;
                    double mean_V = sum_V / npts;
                    double ss_tot = 0, ss_res = 0;
                    for (int R = 1; R <= max_rt; R++) {
                        for (int T = 1; T <= max_rt; T++) {
                            int nc = meas.W_count[R][T];
                            if (nc > 0) {
                                double w = meas.W_re[R][T] / nc;
                                double absw = fabs(w);
                                if (absw > 1e-12) {
                                    double v = -log(absw);
                                    double pred = sig * R * T + c;
                                    ss_res += (v - pred) * (v - pred);
                                    ss_tot += (v - mean_V) * (v - mean_V);
                                }
                            }
                        }
                    }
                    r2a = (ss_tot > 1e-20) ? 1.0 - ss_res / ss_tot : 0.0;
                }
            }

            /* Perimeter law R^2 for summary */
            double sum_P = 0, sum_VP = 0, sum_PP = 0;
            sum_V = 0; npts = 0;
            for (int R = 1; R <= max_rt; R++) {
                for (int T = 1; T <= max_rt; T++) {
                    int nc = meas.W_count[R][T];
                    if (nc > 0) {
                        double w = meas.W_re[R][T] / nc;
                        double absw = fabs(w);
                        if (absw > 1e-12) {
                            double v = -log(absw);
                            double P = 2.0 * (R + T);
                            sum_P += P; sum_V += v;
                            sum_VP += P * v; sum_PP += P * P;
                            npts++;
                        }
                    }
                }
            }
            double r2p = 0;
            if (npts >= 2) {
                double denom = npts * sum_PP - sum_P * sum_P;
                if (fabs(denom) > 1e-20) {
                    double mu_p = (npts * sum_VP - sum_P * sum_V) / denom;
                    double c_p = (sum_V - mu_p * sum_P) / npts;
                    double mean_V = sum_V / npts;
                    double ss_tot = 0, ss_res = 0;
                    for (int R = 1; R <= max_rt; R++) {
                        for (int T = 1; T <= max_rt; T++) {
                            int nc = meas.W_count[R][T];
                            if (nc > 0) {
                                double w = meas.W_re[R][T] / nc;
                                double absw = fabs(w);
                                if (absw > 1e-12) {
                                    double v = -log(absw);
                                    double pred = mu_p * 2.0 * (R + T) + c_p;
                                    ss_res += (v - pred) * (v - pred);
                                    ss_tot += (v - mean_V) * (v - mean_V);
                                }
                            }
                        }
                    }
                    r2p = (ss_tot > 1e-20) ? 1.0 - ss_res / ss_tot : 0.0;
                }
            }

            printf("%-8.4f  %8.4f  %8.4f  %8.4f  %8.5f  %8.4f  %8.4f  %8.4f\n",
                   mu_values[i], w11, w22, w33, sig, r2a, r2p, pabs);
        }

        /* Print detailed report for a few selected mu values */
        printf("\n\n========== DETAILED REPORTS ==========\n");
        double detail_mu[] = {0.001, 0.010, 0.020};
        int n_detail = 3;
        for (int i = 0; i < n_detail; i++) {
            Measurements meas;
            run_simulation(L, detail_mu[i], burnin, measure, sample_gap,
                           max_steps, seed + 100 + i, &meas);
            report_wilson(&meas, detail_mu[i], L);
        }

    } else {
        /* Single mutation rate */
        printf("\nRunning at mu = %.4f\n", mu);
        Measurements meas;
        run_simulation(L, mu, burnin, measure, sample_gap,
                       max_steps, seed, &meas);
        report_wilson(&meas, mu, L);
    }

    clock_gettime(CLOCK_MONOTONIC, &t_end);
    double elapsed = (t_end.tv_sec - t_start.tv_sec) +
                     (t_end.tv_nsec - t_start.tv_nsec) * 1e-9;

    printf("\n================================================================\n");
    printf("Total wall time: %.1f seconds\n", elapsed);
    printf("================================================================\n");
    printf("\nCG Connection:\n");
    printf("  Z_3 link variables from center symmetry phase differences (Def 0.1.2)\n");
    printf("  Wilson loops probe confinement on the computational soup\n");
    printf("  Area law W ~ exp(-sigma*A) => confined phase (Z_3 disorder)\n");
    printf("  Perimeter law W ~ exp(-mu*P) => deconfined phase (Z_3 order)\n");
    printf("  Creutz ratio chi -> sigma (confining) or chi -> 0 (deconfined)\n");
    printf("  Polyakov loop |P| ~ 0 (confined) or |P| ~ 1 (deconfined)\n");
    printf("================================================================\n");

    return 0;
}
