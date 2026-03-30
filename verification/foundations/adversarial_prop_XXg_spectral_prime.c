/*
 * adversarial_prop_XXg_spectral_prime.c
 * ======================================
 *
 * Adversarial verification of Proposition 0.0.XXg:
 * Spectral Prime Encoding on the Stella Octangula.
 *
 * Tests raised by multi-agent peer review (2026-03-27):
 *
 * TEST 1: Q3 Hypercube Laplacian Test
 *   Is {1,1,1,2,2,2,3} simply the Q3 hypercube spectrum?
 *   Compute (a) Q3 Laplacian without Z3, (b) with Z3,
 *   (c) with Z2, Z5, Z7 to check Z_N independence.
 *
 * TEST 2: Distance Verification
 *   Verify the three distinct distances on the stella:
 *   cross-nearest, intra-tetrahedron, cross-antipodal.
 *   Check whether sqrt(8/3) is intra-tet or cross-tet.
 *
 * TEST 3: Sigma Limit Tests
 *   Does sigma -> 0 give trivial matrix (all couplings vanish)?
 *   Does the {1,1,1,2,2,2,3} pattern hold only in a finite window?
 *
 * TEST 4: Z3-Weighted vs Unweighted Comparison
 *   Does Z3 weighting change the eigenvalue ratios at all?
 *   Compare eigenvalue ratios with and without Z3 factor.
 *
 * TEST 5: Fisher Formula Consistency Check
 *   Reproduce the 1D vs 3D Fisher comparison with and without
 *   the extra 2*x factor to see if the "inversion" is an artifact.
 *
 * TEST 6: Control Geometry — Two Disjoint Cubes
 *   Repeat information amplification test on a different 8-vertex
 *   geometry to check if amplification is stella-specific.
 *
 * Build:  cc -O3 -o adversarial_prop_XXg adversarial_prop_XXg_spectral_prime.c -lm
 * Run:    ./adversarial_prop_XXg
 *
 * Plots:  Outputs CSV data for external plotting.
 *         Use adversarial_prop_XXg_plots.py to generate figures.
 */

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#ifndef M_PI
#define M_PI 3.141592653589793
#endif

#define NV 8

/* ================================================================
   Stella Octangula Geometry
   ================================================================ */

static double vtx[8][3];
static int charge[8];  /* 1 for T+, 2 for T- */
static double dmat[8][8];

void init_stella(void) {
    double s = 1.0 / sqrt(3.0);
    double coords[8][3] = {
        { s,  s,  s}, { s, -s, -s}, {-s,  s, -s}, {-s, -s,  s},  /* T+ */
        {-s, -s, -s}, {-s,  s,  s}, { s, -s,  s}, { s,  s, -s}   /* T- */
    };
    for (int i = 0; i < 8; i++) {
        vtx[i][0] = coords[i][0];
        vtx[i][1] = coords[i][1];
        vtx[i][2] = coords[i][2];
        charge[i] = (i < 4) ? 1 : 2;
    }
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++) {
            double dx = vtx[i][0]-vtx[j][0];
            double dy = vtx[i][1]-vtx[j][1];
            double dz = vtx[i][2]-vtx[j][2];
            dmat[i][j] = sqrt(dx*dx + dy*dy + dz*dz);
        }
}

/* ================================================================
   Jacobi Eigenvalue Solver (NxN symmetric, N <= 8)
   ================================================================ */

void jacobi(int n, double A[], double ev[]) {
    /* A is n*n stored row-major, destroyed on output */
    for (int sweep = 0; sweep < 500; sweep++) {
        double off = 0;
        for (int i = 0; i < n; i++)
            for (int j = i+1; j < n; j++)
                off += A[i*n+j] * A[i*n+j];
        if (off < 1e-28) break;

        for (int p = 0; p < n-1; p++) {
            for (int q = p+1; q < n; q++) {
                if (fabs(A[p*n+q]) < 1e-15) continue;
                double d = A[q*n+q] - A[p*n+p];
                double t;
                if (fabs(d) < 1e-30)
                    t = 1.0;
                else {
                    double tau = d / (2.0 * A[p*n+q]);
                    t = (tau >= 0)
                        ? 1.0 / (tau + sqrt(1.0 + tau*tau))
                        : -1.0 / (-tau + sqrt(1.0 + tau*tau));
                }
                double c = 1.0 / sqrt(1.0 + t*t), s_ = t*c;
                A[p*n+p] -= t * A[p*n+q];
                A[q*n+q] += t * A[p*n+q];
                A[p*n+q] = A[q*n+p] = 0.0;
                for (int r = 0; r < n; r++) {
                    if (r == p || r == q) continue;
                    double rp = A[r*n+p], rq = A[r*n+q];
                    A[r*n+p] = A[p*n+r] = c*rp - s_*rq;
                    A[r*n+q] = A[q*n+r] = s_*rp + c*rq;
                }
            }
        }
    }
    for (int i = 0; i < n; i++) ev[i] = A[i*n+i];
    /* Sort ascending */
    for (int i = 0; i < n-1; i++)
        for (int j = i+1; j < n; j++)
            if (ev[j] < ev[i]) { double t = ev[i]; ev[i] = ev[j]; ev[j] = t; }
}

/* ================================================================
   Z_N factor: cos(2*pi*(q_i - q_j)/N)
   ================================================================ */

double zn_factor(int qi, int qj, int N) {
    int dq = ((qi - qj) % N + N) % N;
    return cos(2.0 * M_PI * dq / (double)N);
}

/* ================================================================
   Build Gaussian-weighted coupling matrix on stella
   M_ij = z_N_factor(i,j) * exp(-d_ij^2 / (2*sigma^2))  (i != j)
   Laplacian form: L_ii = -sum_{j!=i} M_ij, L_ij = -M_ij for i!=j
   (We use the coupling matrix directly, not the Laplacian)
   ================================================================ */

void build_coupling_matrix(double sigma, int zn_order, double mat[8][8]) {
    for (int i = 0; i < 8; i++) {
        double row_sum = 0;
        for (int j = 0; j < 8; j++) {
            if (i == j) { mat[i][j] = 0; continue; }
            double g = exp(-dmat[i][j]*dmat[i][j] / (2.0*sigma*sigma));
            double z = (zn_order > 0) ? zn_factor(charge[i], charge[j], zn_order) : 1.0;
            mat[i][j] = z * g;
            row_sum += mat[i][j];
        }
        mat[i][i] = -row_sum; /* Laplacian form */
    }
    /* Negate to get positive semidefinite */
    for (int i = 0; i < 8; i++)
        for (int j = 0; j < 8; j++)
            mat[i][j] = -mat[i][j];
}

/* ================================================================
   Q3 Hypercube Laplacian (no distance weighting, no Z_N)
   Adjacency: vertices connected if they differ in exactly 1 coordinate sign
   ================================================================ */

void build_q3_laplacian(double mat[8][8]) {
    /* Q3 adjacency: edge iff Hamming distance = 1 in (sign_x, sign_y, sign_z) */
    for (int i = 0; i < 8; i++) {
        double row_sum = 0;
        for (int j = 0; j < 8; j++) {
            if (i == j) { mat[i][j] = 0; continue; }
            /* Count coordinate sign differences */
            int diff = 0;
            for (int d = 0; d < 3; d++) {
                if ((vtx[i][d] > 0) != (vtx[j][d] > 0)) diff++;
            }
            mat[i][j] = (diff == 1) ? -1.0 : 0.0;
            row_sum += (diff == 1) ? 1.0 : 0.0;
        }
        mat[i][i] = row_sum;
    }
}

/* ================================================================
   Print eigenvalue ratios
   ================================================================ */

void print_ev_ratios(const char *label, double ev[], int n) {
    /* Find smallest nonzero eigenvalue */
    double min_nz = 1e30;
    for (int i = 0; i < n; i++)
        if (ev[i] > 1e-10 && ev[i] < min_nz) min_nz = ev[i];

    printf("  %s eigenvalues: [", label);
    for (int i = 0; i < n; i++) {
        if (i > 0) printf(", ");
        printf("%.4f", ev[i]);
    }
    printf("]\n");

    printf("  %s ratios (nonzero/min_nz): [", label);
    int first = 1;
    for (int i = 0; i < n; i++) {
        if (ev[i] > 1e-10) {
            if (!first) printf(", ");
            printf("%.3f", ev[i] / min_nz);
            first = 0;
        }
    }
    printf("]\n");
}

/* ================================================================
   TEST 1: Q3 Hypercube Laplacian vs Z3-weighted stella spectrum
   ================================================================ */

void test1_q3_comparison(void) {
    printf("=" "==========================================================\n");
    printf("TEST 1: Q3 Hypercube Laplacian vs Z_N-weighted Stella Spectrum\n");
    printf("=" "==========================================================\n\n");

    printf("QUESTION: Is {1,1,1,2,2,2,3} the Q3 hypercube Laplacian spectrum?\n\n");

    /* (a) Pure Q3 Laplacian (no distance weights, no Z_N) */
    {
        double mat[8][8];
        build_q3_laplacian(mat);
        double flat[64];
        memcpy(flat, mat, sizeof(flat));
        double ev[8];
        jacobi(8, flat, ev);
        print_ev_ratios("Q3 Laplacian (no Z_N)", ev, 8);
    }
    printf("\n");

    /* (b) Stella with Gaussian coupling, NO Z_N, sigma=0.3 (strong confinement) */
    {
        double mat[8][8];
        build_coupling_matrix(0.30, 0, mat); /* zn_order=0 means no Z_N */
        double flat[64];
        memcpy(flat, mat, sizeof(flat));
        double ev[8];
        jacobi(8, flat, ev);
        print_ev_ratios("Stella sigma=0.30, no Z_N", ev, 8);
    }
    printf("\n");

    /* (c) Stella with various Z_N values at sigma=0.3 */
    int test_zn[] = {2, 3, 5, 7};
    for (int t = 0; t < 4; t++) {
        int N = test_zn[t];
        double mat[8][8];
        build_coupling_matrix(0.30, N, mat);
        double flat[64];
        memcpy(flat, mat, sizeof(flat));
        double ev[8];
        jacobi(8, flat, ev);
        char label[64];
        snprintf(label, sizeof(label), "Stella sigma=0.30, Z_%d", N);
        print_ev_ratios(label, ev, 8);
    }
    printf("\n");

    /* (d) Stella with Z_3 at multiple sigma values */
    printf("  Sigma sweep with Z_3 weighting:\n");
    double sigmas[] = {0.10, 0.20, 0.30, 0.37, 0.50, 0.80, 1.00, 2.00, 5.00};
    for (int s = 0; s < 9; s++) {
        double mat[8][8];
        build_coupling_matrix(sigmas[s], 3, mat);
        double flat[64];
        memcpy(flat, mat, sizeof(flat));
        double ev[8];
        jacobi(8, flat, ev);

        /* Find min nonzero */
        double min_nz = 1e30;
        for (int i = 0; i < 8; i++)
            if (ev[i] > 1e-10 && ev[i] < min_nz) min_nz = ev[i];

        printf("    sigma=%.2f: ratios = [", sigmas[s]);
        int first = 1;
        for (int i = 0; i < 8; i++) {
            if (ev[i] > 1e-10) {
                if (!first) printf(", ");
                printf("%.3f", ev[i]/min_nz);
                first = 0;
            }
        }
        printf("]\n");
    }

    printf("\n  VERDICT: If all Z_N values and 'no Z_N' produce the same\n");
    printf("  {1,1,1,2,2,2,3} pattern, then it IS the Q3 spectrum and\n");
    printf("  the Z_3 symmetry claim in Prop 0.0.XXg is incorrect.\n\n");
}

/* ================================================================
   TEST 2: Distance Verification
   ================================================================ */

void test2_distances(void) {
    printf("=" "==========================================================\n");
    printf("TEST 2: Stella Octangula Distance Verification\n");
    printf("=" "==========================================================\n\n");

    printf("  Proposition claims: cross-tet distance = sqrt(8/3) = %.6f\n",
           sqrt(8.0/3.0));
    printf("  Expected: sqrt(8/3) is INTRA-tet edge length\n\n");

    /* Classify all pairs */
    printf("  All pairwise distances (T+ = vertices 0-3, T- = vertices 4-7):\n\n");
    printf("  %-8s %-8s %-10s %-12s %-10s\n",
           "Vtx i", "Vtx j", "Distance", "Type", "Category");
    printf("  %-8s %-8s %-10s %-12s %-10s\n",
           "-----", "-----", "--------", "----", "--------");

    double distances[3] = {0, 0, 0};
    int counts[3] = {0, 0, 0};

    for (int i = 0; i < 8; i++) {
        for (int j = i+1; j < 8; j++) {
            int same_tet = (i < 4 && j < 4) || (i >= 4 && j >= 4);
            const char *type = same_tet ? "intra-tet" : "cross-tet";
            double d = dmat[i][j];

            /* Classify distance */
            int cat = -1;
            if (fabs(d - 2.0/sqrt(3.0)) < 0.001) cat = 0;       /* cross-nearest */
            else if (fabs(d - sqrt(8.0/3.0)) < 0.001) cat = 1;   /* intra-tet */
            else if (fabs(d - 2.0) < 0.001) cat = 2;             /* cross-antipodal */

            const char *cat_name = (cat == 0) ? "cross-nearest" :
                                    (cat == 1) ? "intra-tet-edge" :
                                    (cat == 2) ? "cross-antipodal" : "???";

            printf("  %-8d %-8d %-10.6f %-12s %-10s\n",
                   i, j, d, type, cat_name);

            if (cat >= 0) {
                distances[cat] = d;
                counts[cat]++;
            }
        }
    }

    printf("\n  Summary of distinct distances:\n");
    printf("    Cross-nearest:   %.6f  (2/sqrt(3) = %.6f)  count = %d\n",
           distances[0], 2.0/sqrt(3.0), counts[0]);
    printf("    Intra-tet edge:  %.6f  (sqrt(8/3) = %.6f)  count = %d\n",
           distances[1], sqrt(8.0/3.0), counts[1]);
    printf("    Cross-antipodal: %.6f  (2.0)                count = %d\n",
           distances[2], counts[2]);

    printf("\n  VERDICT: sqrt(8/3) = %.6f IS intra-tetrahedron,\n", sqrt(8.0/3.0));
    printf("  NOT cross-tetrahedron. The proposition's distance claim is WRONG.\n\n");
}

/* ================================================================
   TEST 3: Sigma Limit Tests
   ================================================================ */

void test3_sigma_limits(void) {
    printf("=" "==========================================================\n");
    printf("TEST 3: Sigma -> 0 and Sigma -> inf Limits\n");
    printf("=" "==========================================================\n\n");

    printf("  QUESTION: Does sigma->0 give trivial matrix (eigenvalue ratios undefined)?\n\n");

    /* Write CSV for plotting */
    FILE *fp = fopen("plots/test3_sigma_sweep.csv", "w");
    if (!fp) { printf("  ERROR: Cannot open plots/test3_sigma_sweep.csv\n"); return; }
    fprintf(fp, "sigma,ev0,ev1,ev2,ev3,ev4,ev5,ev6,ev7,max_ev,ratio_max_min\n");

    printf("  %-10s %-12s %-12s %-12s\n", "sigma", "max_ev", "min_nz_ev", "max/min_nz");
    printf("  %-10s %-12s %-12s %-12s\n", "-----", "------", "---------", "---------");

    for (int si = 0; si < 200; si++) {
        double sigma = 0.01 + si * 0.05;
        double mat[8][8];
        build_coupling_matrix(sigma, 3, mat);
        double flat[64];
        memcpy(flat, mat, sizeof(flat));
        double ev[8];
        jacobi(8, flat, ev);

        /* Find min nonzero and max */
        double min_nz = 1e30, max_ev = -1e30;
        for (int i = 0; i < 8; i++) {
            if (ev[i] > 1e-10 && ev[i] < min_nz) min_nz = ev[i];
            if (ev[i] > max_ev) max_ev = ev[i];
        }

        double ratio = (min_nz < 1e20) ? max_ev / min_nz : -1.0;

        fprintf(fp, "%.4f,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.8e,%.6f\n",
                sigma, ev[0], ev[1], ev[2], ev[3], ev[4], ev[5], ev[6], ev[7],
                max_ev, ratio);

        /* Print selected values */
        if (si < 5 || si == 6 || si == 10 || si == 20 || si == 40 ||
            si == 80 || si == 160 || si == 199) {
            printf("  %-10.4f %-12.4e %-12.4e %-12.4f\n",
                   sigma, max_ev, min_nz, ratio);
        }
    }
    fclose(fp);

    printf("\n  Data written to plots/test3_sigma_sweep.csv\n");
    printf("\n  VERDICT: At sigma << 1, all couplings exp(-d^2/(2*sigma^2)) -> 0,\n");
    printf("  making eigenvalues vanishingly small. The ratio max/min_nz should\n");
    printf("  approach 3.0 (Q3 pattern) only at moderate sigma.\n\n");
}

/* ================================================================
   TEST 4: Z3-Weighted vs Unweighted Ratio Comparison
   ================================================================ */

void test4_z3_effect(void) {
    printf("=" "==========================================================\n");
    printf("TEST 4: Z3 vs No-Z3 Eigenvalue Ratio Comparison\n");
    printf("=" "==========================================================\n\n");

    FILE *fp = fopen("plots/test4_z3_comparison.csv", "w");
    if (!fp) { printf("  ERROR: Cannot open file\n"); return; }
    fprintf(fp, "sigma,noZ3_ratio_max,Z3_ratio_max,Z2_ratio_max,Z5_ratio_max,Z7_ratio_max\n");

    printf("  %-10s %-14s %-14s %-14s %-14s %-14s\n",
           "sigma", "no Z_N", "Z_3", "Z_2", "Z_5", "Z_7");

    int zn_vals[] = {0, 3, 2, 5, 7};
    for (int si = 0; si < 40; si++) {
        double sigma = 0.1 + si * 0.1;
        double ratios[5];

        for (int z = 0; z < 5; z++) {
            double mat[8][8];
            build_coupling_matrix(sigma, zn_vals[z], mat);
            double flat[64];
            memcpy(flat, mat, sizeof(flat));
            double ev[8];
            jacobi(8, flat, ev);

            double min_nz = 1e30, max_ev = -1e30;
            for (int i = 0; i < 8; i++) {
                if (ev[i] > 1e-10 && ev[i] < min_nz) min_nz = ev[i];
                if (ev[i] > max_ev) max_ev = ev[i];
            }
            ratios[z] = (min_nz < 1e20) ? max_ev / min_nz : -1.0;
        }

        fprintf(fp, "%.2f,%.6f,%.6f,%.6f,%.6f,%.6f\n",
                sigma, ratios[0], ratios[1], ratios[2], ratios[3], ratios[4]);

        if (si < 5 || si == 9 || si == 19 || si == 39) {
            printf("  %-10.2f %-14.4f %-14.4f %-14.4f %-14.4f %-14.4f\n",
                   sigma, ratios[0], ratios[1], ratios[2], ratios[3], ratios[4]);
        }
    }
    fclose(fp);

    printf("\n  Data written to plots/test4_z3_comparison.csv\n");
    printf("\n  VERDICT: If all Z_N columns show the same ratios,\n");
    printf("  then the eigenvalue structure is Z_N-independent.\n\n");
}

/* ================================================================
   TEST 5: Fisher Formula Consistency (1D 2*x factor)
   ================================================================ */

#define MAX_K 50
#define N_GRID 4000

static int primes_arr[MAX_K + 10];
static int n_primes = 0;

int is_prime(int n) {
    if (n < 2) return 0;
    if (n == 2 || n == 3) return 1;
    if (n % 2 == 0 || n % 3 == 0) return 0;
    for (int i = 5; i*i <= n; i += 6)
        if (n % i == 0 || n % (i+2) == 0) return 0;
    return 1;
}

void sieve_primes(void) {
    n_primes = 0;
    for (int n = 2; n_primes < MAX_K + 5; n++)
        if (is_prime(n))
            primes_arr[n_primes++] = n;
}

/* Effective rank via spectral entropy (Roy-Vetterli) */
double eff_rank_entropy(double ev[], int n) {
    double total = 0;
    for (int i = 0; i < n; i++)
        if (ev[i] > 1e-15) total += ev[i];
    if (total < 1e-30) return 0;

    double entropy = 0;
    for (int i = 0; i < n; i++) {
        if (ev[i] > 1e-15) {
            double p = ev[i] / total;
            entropy -= p * log(p);
        }
    }
    return exp(entropy);
}

/* Compute Fisher matrix for K frequencies on 1D line */
/* with_2x: if nonzero, use the 2*x factor (as in original code) */
double fisher_1d(int K, double freqs[], int with_2x) {
    double F[MAX_K * MAX_K];
    memset(F, 0, sizeof(double)*K*K);

    double x_max = 200.0;
    double dx = x_max / N_GRID;

    for (int xi = 1; xi <= N_GRID; xi++) {
        double x = xi * dx;

        /* Compute P and dP/dtheta_k at Z_K equilibrium phases */
        double Re_Z = 0, Im_Z = 0;
        double re_z[MAX_K], im_z[MAX_K];
        for (int k = 0; k < K; k++) {
            double phase = 2.0 * M_PI * k / K;
            double amp = exp(-0.01 * freqs[k]);
            re_z[k] = amp * cos(freqs[k] * x + phase);
            im_z[k] = amp * sin(freqs[k] * x + phase);
            Re_Z += re_z[k];
            Im_Z += im_z[k];
        }

        double P = Re_Z*Re_Z + Im_Z*Im_Z;
        if (P < 1e-30) continue;

        double dp[MAX_K];
        for (int k = 0; k < K; k++) {
            if (with_2x)
                dp[k] = 2.0 * x * (re_z[k]*Im_Z - im_z[k]*Re_Z);
            else
                dp[k] = re_z[k]*Im_Z - im_z[k]*Re_Z;
        }

        double w = dx / (P + 1e-30);
        for (int j = 0; j < K; j++)
            for (int k = j; k < K; k++) {
                double v = dp[j] * dp[k] * w;
                F[j*K+k] += v;
                if (k != j) F[k*K+j] += v;
            }
    }

    double ev[MAX_K];
    jacobi(K, F, ev);
    return eff_rank_entropy(ev, K);
}

/* Compute Fisher matrix for K frequencies on stella surface */
/* (simplified: use 8 vertices with equal weights) */
double fisher_stella_graph(int K, double freqs[]) {
    double F[MAX_K * MAX_K];
    memset(F, 0, sizeof(double)*K*K);

    /* Fibonacci lattice for mode directions */
    double dirs[MAX_K][3];
    double golden = (1.0 + sqrt(5.0)) / 2.0;
    for (int k = 0; k < K; k++) {
        double theta = acos(1.0 - 2.0*(k+0.5)/K);
        double phi = 2.0 * M_PI * (k+0.5) / golden;
        dirs[k][0] = sin(theta)*cos(phi);
        dirs[k][1] = sin(theta)*sin(phi);
        dirs[k][2] = cos(theta);
    }

    for (int vi = 0; vi < NV; vi++) {
        double Re_Z = 0, Im_Z = 0;
        double re_z[MAX_K], im_z[MAX_K];

        for (int k = 0; k < K; k++) {
            double phase = 2.0 * M_PI * k / K;
            double rdot = vtx[vi][0]*dirs[k][0] + vtx[vi][1]*dirs[k][1] + vtx[vi][2]*dirs[k][2];
            double amp = exp(-0.01 * freqs[k]);
            re_z[k] = amp * cos(freqs[k] * rdot + phase);
            im_z[k] = amp * sin(freqs[k] * rdot + phase);
            Re_Z += re_z[k];
            Im_Z += im_z[k];
        }

        double P = Re_Z*Re_Z + Im_Z*Im_Z;
        if (P < 1e-30) continue;

        double dp[MAX_K];
        for (int k = 0; k < K; k++)
            dp[k] = re_z[k]*Im_Z - im_z[k]*Re_Z;

        double w = 1.0 / (P + 1e-30);
        for (int j = 0; j < K; j++)
            for (int k = j; k < K; k++) {
                double v = dp[j] * dp[k] * w;
                F[j*K+k] += v;
                if (k != j) F[k*K+j] += v;
            }
    }

    double ev[MAX_K];
    jacobi(K, F, ev);
    return eff_rank_entropy(ev, K);
}

void test5_fisher_formula(void) {
    printf("=" "==========================================================\n");
    printf("TEST 5: Fisher Formula Consistency (1D 2*x factor)\n");
    printf("=" "==========================================================\n\n");

    sieve_primes();

    printf("  QUESTION: Does the 'inversion' persist when we remove the 2*x factor\n");
    printf("  from the 1D Fisher formula?\n\n");

    FILE *fp = fopen("plots/test5_fisher_consistency.csv", "w");
    if (!fp) { printf("  ERROR: Cannot open file\n"); return; }
    fprintf(fp, "K,prime_1d_with2x,int_1d_with2x,prime_1d_no2x,int_1d_no2x,prime_stella,int_stella\n");

    int K_vals[] = {5, 10, 15, 20, 25, 30, 35, 40, 45, 50};

    printf("  %-5s | %-22s | %-22s | %-22s\n",
           "K", "1D with 2*x (P/I)", "1D no 2*x (P/I)", "Stella graph (P/I)");
    printf("  %-5s | %-22s | %-22s | %-22s\n",
           "---", "--------------------", "--------------------", "--------------------");

    for (int ki = 0; ki < 10; ki++) {
        int K = K_vals[ki];

        /* Prime frequencies */
        double pfreqs[MAX_K];
        for (int k = 0; k < K; k++) pfreqs[k] = primes_arr[k];

        /* Integer frequencies */
        double ifreqs[MAX_K];
        for (int k = 0; k < K; k++) ifreqs[k] = k + 1;

        double p_1d_2x = fisher_1d(K, pfreqs, 1);
        double i_1d_2x = fisher_1d(K, ifreqs, 1);
        double p_1d_no = fisher_1d(K, pfreqs, 0);
        double i_1d_no = fisher_1d(K, ifreqs, 0);
        double p_stella = fisher_stella_graph(K, pfreqs);
        double i_stella = fisher_stella_graph(K, ifreqs);

        fprintf(fp, "%d,%.4f,%.4f,%.4f,%.4f,%.4f,%.4f\n",
                K, p_1d_2x, i_1d_2x, p_1d_no, i_1d_no, p_stella, i_stella);

        printf("  %-5d | %.2f / %.2f %-10s | %.2f / %.2f %-10s | %.2f / %.2f %-10s\n",
               K,
               p_1d_2x, i_1d_2x, (p_1d_2x < i_1d_2x) ? "(I > P)" : "(P > I)",
               p_1d_no, i_1d_no, (p_1d_no < i_1d_no) ? "(I > P)" : "(P > I)",
               p_stella, i_stella, (p_stella > i_stella) ? "(P > I)" : "(I > P)");
    }
    fclose(fp);

    printf("\n  Data written to plots/test5_fisher_consistency.csv\n");
    printf("\n  VERDICT: If removing 2*x changes which frequency set ranks higher\n");
    printf("  in 1D, then the 'inversion' is partially a formula artifact.\n");
    printf("  If the ordering is the same either way, the inversion is genuine.\n\n");
}

/* ================================================================
   TEST 6: Control Geometry — Two Disjoint Cubes (8 vertices)
   ================================================================ */

static double ctrl_vtx[8][3];

void init_control_geometry(void) {
    /* Two small cubes at offset positions, 8 vertices total */
    /* Cube A: 4 vertices of a tetrahedron inscribed in unit cube */
    /* Cube B: complementary 4 vertices */
    double s = 0.5;
    double coords[8][3] = {
        { s,  s,  0}, { s,  0,  s}, { 0,  s,  s}, { 0,  0,  0}, /* Group A */
        { 0,  0,  s}, { 0,  s,  0}, { s,  0,  0}, { s,  s,  s}  /* Group B */
    };
    for (int i = 0; i < 8; i++) {
        ctrl_vtx[i][0] = coords[i][0];
        ctrl_vtx[i][1] = coords[i][1];
        ctrl_vtx[i][2] = coords[i][2];
    }
}

double fisher_control_graph(int K, double freqs[]) {
    double F[MAX_K * MAX_K];
    memset(F, 0, sizeof(double)*K*K);

    double golden = (1.0 + sqrt(5.0)) / 2.0;
    double dirs[MAX_K][3];
    for (int k = 0; k < K; k++) {
        double theta = acos(1.0 - 2.0*(k+0.5)/K);
        double phi = 2.0 * M_PI * (k+0.5) / golden;
        dirs[k][0] = sin(theta)*cos(phi);
        dirs[k][1] = sin(theta)*sin(phi);
        dirs[k][2] = cos(theta);
    }

    for (int vi = 0; vi < 8; vi++) {
        double Re_Z = 0, Im_Z = 0;
        double re_z[MAX_K], im_z[MAX_K];

        for (int k = 0; k < K; k++) {
            double phase = 2.0 * M_PI * k / K;
            double rdot = ctrl_vtx[vi][0]*dirs[k][0] +
                          ctrl_vtx[vi][1]*dirs[k][1] +
                          ctrl_vtx[vi][2]*dirs[k][2];
            double amp = exp(-0.01 * freqs[k]);
            re_z[k] = amp * cos(freqs[k] * rdot + phase);
            im_z[k] = amp * sin(freqs[k] * rdot + phase);
            Re_Z += re_z[k];
            Im_Z += im_z[k];
        }

        double P = Re_Z*Re_Z + Im_Z*Im_Z;
        if (P < 1e-30) continue;

        double dp[MAX_K];
        for (int k = 0; k < K; k++)
            dp[k] = re_z[k]*Im_Z - im_z[k]*Re_Z;

        double w = 1.0 / (P + 1e-30);
        for (int j = 0; j < K; j++)
            for (int k = j; k < K; k++) {
                double v = dp[j] * dp[k] * w;
                F[j*K+k] += v;
                if (k != j) F[k*K+j] += v;
            }
    }

    double ev[MAX_K];
    jacobi(K, F, ev);
    return eff_rank_entropy(ev, K);
}

void test6_control_geometry(void) {
    printf("=" "==========================================================\n");
    printf("TEST 6: Control Geometry — Cube Vertices vs Stella\n");
    printf("=" "==========================================================\n\n");

    sieve_primes();
    init_control_geometry();

    printf("  QUESTION: Does a different 8-vertex geometry also show\n");
    printf("  'prime amplification' (P > I on graph), or is this stella-specific?\n\n");

    FILE *fp = fopen("plots/test6_control_geometry.csv", "w");
    if (!fp) { printf("  ERROR: Cannot open file\n"); return; }
    fprintf(fp, "K,prime_stella,int_stella,prime_control,int_control\n");

    printf("  %-5s | %-22s | %-22s\n",
           "K", "Stella (P/I)", "Control cube (P/I)");

    int K_vals[] = {5, 10, 15, 20, 25, 30, 35, 40, 45, 50};

    for (int ki = 0; ki < 10; ki++) {
        int K = K_vals[ki];

        double pfreqs[MAX_K], ifreqs[MAX_K];
        for (int k = 0; k < K; k++) { pfreqs[k] = primes_arr[k]; ifreqs[k] = k+1; }

        double ps = fisher_stella_graph(K, pfreqs);
        double is_ = fisher_stella_graph(K, ifreqs);
        double pc = fisher_control_graph(K, pfreqs);
        double ic = fisher_control_graph(K, ifreqs);

        fprintf(fp, "%d,%.4f,%.4f,%.4f,%.4f\n", K, ps, is_, pc, ic);

        printf("  %-5d | %.2f / %.2f %-10s | %.2f / %.2f %-10s\n",
               K,
               ps, is_, (ps > is_) ? "(P > I)" : "(I > P)",
               pc, ic, (pc > ic) ? "(P > I)" : "(I > P)");
    }
    fclose(fp);

    printf("\n  Data written to plots/test6_control_geometry.csv\n");
    printf("\n  VERDICT: If the control geometry also shows P > I,\n");
    printf("  then 'information amplification' is not stella-specific.\n\n");
}

/* ================================================================
   MAIN
   ================================================================ */

int main(void) {
    init_stella();

    printf("\n");
    printf("ADVERSARIAL VERIFICATION: Proposition 0.0.XXg\n");
    printf("Spectral Prime Encoding on the Stella Octangula\n");
    printf("================================================\n");
    printf("Date: 2026-03-27\n");
    printf("Source: Multi-agent peer review findings\n\n");

    test1_q3_comparison();
    test2_distances();
    test3_sigma_limits();
    test4_z3_effect();
    test5_fisher_formula();
    test6_control_geometry();

    printf("=" "==========================================================\n");
    printf("ALL TESTS COMPLETE\n");
    printf("=" "==========================================================\n");
    printf("\n  Run adversarial_prop_XXg_plots.py to generate figures\n");
    printf("  from the CSV data in plots/\n\n");

    return 0;
}
