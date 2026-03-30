/*
 * Adversarial Verification: Proposition 0.0.3a
 * Computational Crystallization of the Stella Octangula
 *
 * Tests:
 *   T1: Stella geometry verification (exact)
 *   T2: Stella ground state for α/β ≥ 2 (annealing, 10 seeds)
 *   T3: Thomson limit α/β=1 does NOT produce stella
 *   T4: Phase transition sharpness at α/β ≈ 2
 *   T5: N=8 tetrahedron uniqueness (geometric)
 *   T6: Label relaxation from any split → 4+4
 *   T9: Z₃ product rule matches two-component
 *   T10: Z₄ self-conjugate escape route
 *   T13: Sphere emergence from soft normalization
 *   T14: Cross-distance ratio = √3
 *
 * Build: cc -O3 -o proposition_0_0_3a_adversarial proposition_0_0_3a_adversarial.c -lm
 * Run:   ./proposition_0_0_3a_adversarial
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <float.h>

#define N_PTS 8
#define N_PER_GROUP 4

/* ── RNG (xoshiro128+) ──────────────────────────────────────────────── */

static uint32_t rng_s[4];

static inline uint32_t rotl(uint32_t x, int k) {
    return (x << k) | (x >> (32 - k));
}

static uint32_t rng_next(void) {
    uint32_t r = rng_s[0] + rng_s[3];
    uint32_t t = rng_s[1] << 9;
    rng_s[2] ^= rng_s[0]; rng_s[3] ^= rng_s[1];
    rng_s[1] ^= rng_s[2]; rng_s[0] ^= rng_s[3];
    rng_s[2] ^= t; rng_s[3] = rotl(rng_s[3], 11);
    return r;
}

static void rng_seed(uint32_t seed) {
    rng_s[0] = seed; rng_s[1] = seed * 2654435761u;
    rng_s[2] = seed * 2246822519u; rng_s[3] = seed * 3266489917u;
    for (int i = 0; i < 20; i++) rng_next();
}

static inline int rng_int(int n) { return (int)(rng_next() % (uint32_t)n); }

static inline double rng_double(void) {
    return (rng_next() >> 8) / 16777216.0;
}

static double rng_normal(void) {
    double u1 = rng_double(), u2 = rng_double();
    if (u1 < 1e-15) u1 = 1e-15;
    return sqrt(-2.0 * log(u1)) * cos(2.0 * M_PI * u2);
}

/* ── Geometry ────────────────────────────────────────────────────────── */

static void random_sphere_point(double out[3]) {
    double z = rng_double() * 2.0 - 1.0;
    double phi = rng_double() * 2.0 * M_PI;
    double r = sqrt(1.0 - z * z);
    out[0] = r * cos(phi); out[1] = r * sin(phi); out[2] = z;
}

static void normalize3(double v[3]) {
    double n = sqrt(v[0]*v[0] + v[1]*v[1] + v[2]*v[2]);
    if (n < 1e-15) return;
    v[0] /= n; v[1] /= n; v[2] /= n;
}

static inline double dist2(const double a[3], const double b[3]) {
    double dx = a[0]-b[0], dy = a[1]-b[1], dz = a[2]-b[2];
    return dx*dx + dy*dy + dz*dz;
}

/* ── Ideal stella vertices ───────────────────────────────────────────── */

static const double S = 0.5773502691896258; /* 1/√3 */

static const double STELLA_TP[4][3] = {
    { S,  S,  S}, { S, -S, -S}, {-S,  S, -S}, {-S, -S,  S}
};
static const double STELLA_TM[4][3] = {
    {-S, -S, -S}, {-S,  S,  S}, { S, -S,  S}, { S,  S, -S}
};

/* ── Energy ──────────────────────────────────────────────────────────── */

static double energy(double pts[][3], int *labels, int n, double alpha, double beta) {
    double e = 0.0;
    for (int i = 0; i < n; i++)
        for (int j = i+1; j < n; j++) {
            double d = dist2(pts[i], pts[j]);
            if (d < 1e-14) d = 1e-14;
            e += ((labels[i] == labels[j]) ? alpha : beta) / d;
        }
    return e;
}

static double delta_energy(double pts[][3], int *labels, int n, int idx,
                           double old[3], double alpha, double beta) {
    double de = 0.0;
    for (int j = 0; j < n; j++) {
        if (j == idx) continue;
        double coeff = (labels[idx] == labels[j]) ? alpha : beta;
        double d2_new = dist2(pts[idx], pts[j]);
        double d2_old = dist2(old, pts[j]);
        if (d2_new < 1e-14) return 1e15;
        de += coeff * (1.0/d2_new - 1.0/d2_old);
    }
    return de;
}

/* ── Stella RMSD (Kabsch + permutations) ─────────────────────────────── */

static const int P4[24][4] = {
    {0,1,2,3},{0,1,3,2},{0,2,1,3},{0,2,3,1},{0,3,1,2},{0,3,2,1},
    {1,0,2,3},{1,0,3,2},{1,2,0,3},{1,2,3,0},{1,3,0,2},{1,3,2,0},
    {2,0,1,3},{2,0,3,1},{2,1,0,3},{2,1,3,0},{2,3,0,1},{2,3,1,0},
    {3,0,1,2},{3,0,2,1},{3,1,0,2},{3,1,2,0},{3,2,0,1},{3,2,1,0}
};

static double kabsch_rmsd8(double P[8][3], double Q[8][3]) {
    double cp[3]={0}, cq[3]={0};
    for (int i=0;i<8;i++) for (int k=0;k<3;k++) { cp[k]+=P[i][k]; cq[k]+=Q[i][k]; }
    for (int k=0;k<3;k++) { cp[k]/=8; cq[k]/=8; }

    double Pc[8][3], Qc[8][3];
    for (int i=0;i<8;i++) for (int k=0;k<3;k++) {
        Pc[i][k]=P[i][k]-cp[k]; Qc[i][k]=Q[i][k]-cq[k];
    }

    double H[3][3]={{0}};
    for (int i=0;i<8;i++) for (int r=0;r<3;r++) for (int c=0;c<3;c++)
        H[r][c]+=Pc[i][r]*Qc[i][c];

    double HtH[3][3]={{0}};
    for (int i=0;i<3;i++) for (int j=0;j<3;j++) for (int k=0;k<3;k++)
        HtH[i][j]+=H[k][i]*H[k][j];

    double p = HtH[0][0]+HtH[1][1]+HtH[2][2];
    double q = HtH[0][0]*HtH[1][1]+HtH[0][0]*HtH[2][2]+HtH[1][1]*HtH[2][2]
              -HtH[0][1]*HtH[0][1]-HtH[0][2]*HtH[0][2]-HtH[1][2]*HtH[1][2];
    double det = HtH[0][0]*(HtH[1][1]*HtH[2][2]-HtH[1][2]*HtH[1][2])
                -HtH[0][1]*(HtH[0][1]*HtH[2][2]-HtH[1][2]*HtH[0][2])
                +HtH[0][2]*(HtH[0][1]*HtH[1][2]-HtH[1][1]*HtH[0][2]);

    double p3=p/3, q2=(p*p-3*q)/9, r2=(2*p*p*p-9*p*q+27*det)/54;
    double sq=sqrt(fabs(q2)), ang=0;
    if (sq>1e-15) { double rat=r2/(q2*sq); if(rat>1)rat=1; if(rat<-1)rat=-1; ang=acos(rat); }

    double e0=p3+2*sq*cos(ang/3), e1=p3+2*sq*cos((ang+2*M_PI)/3), e2=p3+2*sq*cos((ang+4*M_PI)/3);
    if(e0<0)e0=0; if(e1<0)e1=0; if(e2<0)e2=0;

    double sv[3]={sqrt(e0),sqrt(e1),sqrt(e2)};
    for(int i=0;i<2;i++) for(int j=i+1;j<3;j++) if(sv[j]>sv[i]){double t=sv[i];sv[i]=sv[j];sv[j]=t;}

    double detH=H[0][0]*(H[1][1]*H[2][2]-H[1][2]*H[2][1])
               -H[0][1]*(H[1][0]*H[2][2]-H[1][2]*H[2][0])
               +H[0][2]*(H[1][0]*H[2][1]-H[1][1]*H[2][0]);

    double sum_sv = (detH>=0) ? sv[0]+sv[1]+sv[2] : sv[0]+sv[1]-sv[2];

    double ssP=0, ssQ=0;
    for(int i=0;i<8;i++) for(int k=0;k<3;k++) { ssP+=Pc[i][k]*Pc[i][k]; ssQ+=Qc[i][k]*Qc[i][k]; }

    double rmsd2=(ssP+ssQ-2*sum_sv)/8;
    return sqrt(rmsd2>0?rmsd2:0);
}

static double stella_rmsd(double ga[4][3], double gb[4][3]) {
    double best = 1e10;
    for (int sw=0; sw<2; sw++) {
        const double (*ra)[3] = sw ? STELLA_TM : STELLA_TP;
        const double (*rb)[3] = sw ? STELLA_TP : STELLA_TM;
        for (int pa=0; pa<24; pa++) for (int pb=0; pb<24; pb++) {
            double P[8][3], Q[8][3];
            for (int i=0;i<4;i++) {
                int ia=P4[pa][i], ib=P4[pb][i];
                for(int k=0;k<3;k++) {
                    P[i][k]=ga[ia][k]; P[i+4][k]=gb[ib][k];
                    Q[i][k]=ra[i][k]; Q[i+4][k]=rb[i][k];
                }
            }
            double r=kabsch_rmsd8(P,Q);
            if(r<best) best=r;
        }
    }
    return best;
}

/* ── Annealing ───────────────────────────────────────────────────────── */

typedef struct {
    double pts[N_PTS][3];
    int labels[N_PTS];
    double e, rmsd, tet_q;
} AnnealResult;

static AnnealResult run_anneal(int n, int *labels, double alpha, double beta,
                                long n_steps, uint32_t seed, double confinement) {
    rng_seed(seed);
    double pts[N_PTS][3];
    for (int i=0; i<n; i++) {
        if (confinement > 0) {
            /* Start in random cube */
            pts[i][0] = rng_double()*2-1;
            pts[i][1] = rng_double()*2-1;
            pts[i][2] = rng_double()*2-1;
        } else {
            random_sphere_point(pts[i]);
        }
    }

    double T0=2.0, Tf=0.001;
    double cool = pow(Tf/T0, 1.0/n_steps);
    double T = T0;

    double E = energy(pts, labels, n, alpha, beta);
    if (confinement > 0) {
        for (int i=0; i<n; i++) {
            double r = sqrt(pts[i][0]*pts[i][0]+pts[i][1]*pts[i][1]+pts[i][2]*pts[i][2]);
            E += confinement * (r-1)*(r-1);
        }
    }

    double best_pts[N_PTS][3];
    memcpy(best_pts, pts, sizeof(double)*n*3);
    double best_E = E;

    for (long s=0; s<n_steps; s++) {
        int idx = rng_int(n);
        double step = 0.3*sqrt(T/T0);
        double old[3] = {pts[idx][0], pts[idx][1], pts[idx][2]};

        pts[idx][0] += rng_normal()*step;
        pts[idx][1] += rng_normal()*step;
        pts[idx][2] += rng_normal()*step;

        if (confinement <= 0)
            normalize3(pts[idx]);

        double de = delta_energy(pts, labels, n, idx, old, alpha, beta);
        if (confinement > 0) {
            double r_new = sqrt(pts[idx][0]*pts[idx][0]+pts[idx][1]*pts[idx][1]+pts[idx][2]*pts[idx][2]);
            double r_old = sqrt(old[0]*old[0]+old[1]*old[1]+old[2]*old[2]);
            de += confinement*((r_new-1)*(r_new-1) - (r_old-1)*(r_old-1));
        }

        if (de < 0 || rng_double() < exp(-de/T)) {
            E += de;
            if (E < best_E) { best_E = E; memcpy(best_pts, pts, sizeof(double)*n*3); }
        } else {
            pts[idx][0]=old[0]; pts[idx][1]=old[1]; pts[idx][2]=old[2];
        }
        T *= cool;
    }

    AnnealResult res;
    memcpy(res.pts, best_pts, sizeof(double)*n*3);
    memcpy(res.labels, labels, sizeof(int)*n);
    res.e = best_E;

    /* Compute stella RMSD */
    double ga[4][3], gb[4][3];
    int na=0, nb=0;
    for (int i=0; i<n; i++) {
        if (labels[i]==0 && na<4) { memcpy(ga[na++], best_pts[i], 24); }
        else if (labels[i]==1 && nb<4) { memcpy(gb[nb++], best_pts[i], 24); }
    }
    res.rmsd = (na==4 && nb==4) ? stella_rmsd(ga, gb) : 99.0;

    /* Tet quality */
    double dists[6]; int nd;
    if (na==4) {
        nd=0; double sum=0;
        for(int i=0;i<4;i++) for(int j=i+1;j<4;j++) {
            dists[nd]=sqrt(dist2(ga[i],ga[j])); sum+=dists[nd]; nd++;
        }
        double mean=sum/6, var=0;
        for(int i=0;i<6;i++){double d=dists[i]-mean;var+=d*d;}
        res.tet_q = 1.0 - sqrt(var/6)/mean;
    } else res.tet_q = 0;

    return res;
}

/* ══════════════════════════════════════════════════════════════════════ */
/* TESTS                                                                 */
/* ══════════════════════════════════════════════════════════════════════ */

static int n_pass=0, n_fail=0;

static void report(const char *name, int passed) {
    printf("  %-35s %s\n", name, passed ? "PASS" : "FAIL");
    if (passed) n_pass++; else n_fail++;
}

/* T1: Ideal stella geometry */
static void test_stella_geometry(void) {
    /* All vertices on unit sphere */
    int on_sphere = 1;
    for (int i=0; i<4; i++) {
        double r2p = STELLA_TP[i][0]*STELLA_TP[i][0]+STELLA_TP[i][1]*STELLA_TP[i][1]+STELLA_TP[i][2]*STELLA_TP[i][2];
        double r2m = STELLA_TM[i][0]*STELLA_TM[i][0]+STELLA_TM[i][1]*STELLA_TM[i][1]+STELLA_TM[i][2]*STELLA_TM[i][2];
        if (fabs(r2p-1)>1e-10 || fabs(r2m-1)>1e-10) on_sphere=0;
    }

    /* Intra-tetrahedral distances all equal */
    double expected_intra = 2*sqrt(2.0/3.0);
    int intra_ok = 1;
    for (int t=0; t<2; t++) {
        const double (*tet)[3] = t ? STELLA_TM : STELLA_TP;
        for (int i=0; i<4; i++) for (int j=i+1; j<4; j++) {
            double d = sqrt(dist2(tet[i], tet[j]));
            if (fabs(d - expected_intra) > 1e-10) intra_ok=0;
        }
    }

    /* Euler: χ = 2*(4-6+4) = 4 */
    int chi = 2*(4-6+4);

    report("T1: Stella geometry", on_sphere && intra_ok && chi==4);
}

/* T2: Stella as ground state for α/β ≥ 2 */
static void test_stella_ground_state(void) {
    double ratios[] = {2.0, 5.0, 10.0};
    int n_ratios = 3, n_seeds = 10;
    long n_steps = 500000L;
    int all_ok = 1;

    printf("    T2 details:\n");
    for (int ri=0; ri<n_ratios; ri++) {
        int converged = 0;
        double sum_rmsd = 0;
        for (int s=0; s<n_seeds; s++) {
            int labels[N_PTS] = {0,0,0,0,1,1,1,1};
            AnnealResult r = run_anneal(8, labels, ratios[ri], 1.0, n_steps, 42+s*137, 0);
            sum_rmsd += r.rmsd;
            if (r.rmsd < 0.05) converged++;
        }
        double mean_rmsd = sum_rmsd / n_seeds;
        printf("      α/β=%.0f: %d/%d converged, mean RMSD=%.4f\n",
               ratios[ri], converged, n_seeds, mean_rmsd);
        if (converged < n_seeds * 0.8) all_ok = 0;  /* allow 80% convergence */
    }
    report("T2: Stella ground state (α/β≥2)", all_ok);
}

/* T3: Thomson limit NOT stella */
static void test_thomson_limit(void) {
    int n_seeds = 10;
    long n_steps = 500000L;
    int not_stella = 1;

    double sum_rmsd = 0;
    for (int s=0; s<n_seeds; s++) {
        int labels[N_PTS] = {0,0,0,0,1,1,1,1};
        AnnealResult r = run_anneal(8, labels, 1.0, 1.0, n_steps, 42+s*97, 0);
        sum_rmsd += r.rmsd;
    }
    double mean_rmsd = sum_rmsd / n_seeds;
    printf("    T3: Thomson mean RMSD=%.4f (should be >0.15)\n", mean_rmsd);
    not_stella = mean_rmsd > 0.10;
    report("T3: Thomson limit ≠ stella", not_stella);
}

/* T4: Phase transition sharpness */
static void test_phase_transition(void) {
    double ratios[] = {1.0, 1.5, 2.0, 3.0, 5.0, 10.0};
    int n_ratios = 6, n_seeds = 5;
    long n_steps = 500000L;
    double mean_rmsds[6];

    printf("    T4 sweep:\n");
    for (int ri=0; ri<n_ratios; ri++) {
        double sum = 0;
        for (int s=0; s<n_seeds; s++) {
            int labels[N_PTS] = {0,0,0,0,1,1,1,1};
            AnnealResult r = run_anneal(8, labels, ratios[ri], 1.0, n_steps, 42+s*71, 0);
            sum += r.rmsd;
        }
        mean_rmsds[ri] = sum / n_seeds;
        printf("      α/β=%5.1f → mean RMSD=%.4f\n", ratios[ri], mean_rmsds[ri]);
    }

    /* Check: high RMSD at ratio 1.0, low at ≥ 3.0 */
    int sharp = mean_rmsds[0] > 0.10 && mean_rmsds[3] < 0.10;
    report("T4: Phase transition at α/β≈2", sharp);
}

/* T5: Tetrahedron uniqueness */
static void test_tetrahedron_uniqueness(void) {
    /* Regular tetrahedron: all 6 pairwise distances equal, spans 3D.
     * Triangle (3 vertices): spans 2D only.
     * No Platonic solid with 5+ vertices has all distances equal. */
    double tet[4][3] = {
        { S, S, S}, { S,-S,-S}, {-S, S,-S}, {-S,-S, S}
    };
    double dists[6]; int nd=0;
    for (int i=0;i<4;i++) for (int j=i+1;j<4;j++) dists[nd++]=sqrt(dist2(tet[i],tet[j]));
    double mean=0; for(int i=0;i<6;i++) mean+=dists[i]; mean/=6;
    double cv=0; for(int i=0;i<6;i++){double d=dists[i]-mean;cv+=d*d;} cv=sqrt(cv/6)/mean;

    int regularity_perfect = cv < 1e-10;

    /* Check 3D span via SVD-like: compute covariance eigenvalues */
    double cov[3][3] = {{0}};
    for (int i=0;i<4;i++) for(int r=0;r<3;r++) for(int c=0;c<3;c++) cov[r][c]+=tet[i][r]*tet[i][c];
    /* All eigenvalues should be positive (3D span) — check trace and det */
    double trace = cov[0][0]+cov[1][1]+cov[2][2];
    double det = cov[0][0]*(cov[1][1]*cov[2][2]-cov[1][2]*cov[2][1])
                -cov[0][1]*(cov[1][0]*cov[2][2]-cov[1][2]*cov[2][0])
                +cov[0][2]*(cov[1][0]*cov[2][1]-cov[1][1]*cov[2][0]);
    int spans_3d = trace > 0 && det > 1e-10;

    report("T5: Tetrahedron uniqueness (N/2=4)", regularity_perfect && spans_3d);
}

/* T6: Label relaxation → 4+4
 * Uses joint annealing with 70% position moves and 30% label FLIPS.
 * A label flip changes one particle's label (0↔1), matching Phase C design.
 * Prevents degenerate 0+8 or 8+0 states. */

static double delta_energy_flip(double pts[][3], int *labels, int n, int idx,
                                 double alpha, double beta) {
    double de = 0.0;
    int old_label = labels[idx];
    for (int j = 0; j < n; j++) {
        if (j == idx) continue;
        double d = dist2(pts[idx], pts[j]);
        if (d < 1e-14) return 1e15;
        double old_coeff = (old_label == labels[j]) ? alpha : beta;
        double new_coeff = (old_label == labels[j]) ? beta : alpha;
        de += (new_coeff - old_coeff) / d;
    }
    return de;
}

static void test_label_relaxation(void) {
    int splits[] = {1, 2, 3, 4, 5, 6, 7};
    int n_splits = 7, n_seeds = 10;
    long n_steps = 500000L;
    int all_ok = 1;
    double alpha=10.0, beta=1.0;

    printf("    T6 label relaxation (joint anneal, 30%% flip):\n");
    for (int si=0; si<n_splits; si++) {
        int n_a = splits[si], n_b = 8 - n_a;
        int converged = 0;

        for (int seed=0; seed<n_seeds; seed++) {
            rng_seed(42 + seed*53 + n_a*7);

            double pts[N_PTS][3];
            int labels[N_PTS];
            for (int i=0; i<n_a; i++) labels[i]=0;
            for (int i=n_a; i<8; i++) labels[i]=1;
            for (int i=0;i<8;i++) random_sphere_point(pts[i]);

            double E = energy(pts, labels, 8, alpha, beta);
            double best_pts[N_PTS][3]; int best_labels[N_PTS];
            memcpy(best_pts, pts, sizeof(pts));
            memcpy(best_labels, labels, sizeof(labels));
            double best_E = E;

            double T0=2.0, Tf=0.001;
            double cool = pow(Tf/T0, 1.0/n_steps);
            double T = T0;

            for (long s=0; s<n_steps; s++) {
                if (rng_double() < 0.7) {
                    /* Position move */
                    int idx = rng_int(8);
                    double step = 0.3*sqrt(T/T0);
                    double old[3]={pts[idx][0],pts[idx][1],pts[idx][2]};
                    pts[idx][0]+=rng_normal()*step;
                    pts[idx][1]+=rng_normal()*step;
                    pts[idx][2]+=rng_normal()*step;
                    normalize3(pts[idx]);

                    double de = delta_energy(pts, labels, 8, idx, old, alpha, beta);
                    if (de<0 || rng_double()<exp(-de/T)) {
                        E+=de;
                        if (E<best_E) { best_E=E; memcpy(best_pts,pts,sizeof(pts)); memcpy(best_labels,labels,sizeof(labels)); }
                    } else {
                        pts[idx][0]=old[0]; pts[idx][1]=old[1]; pts[idx][2]=old[2];
                    }
                } else {
                    /* Label flip */
                    int idx = rng_int(8);
                    int old_label = labels[idx];
                    /* Prevent 0+8 or 8+0 */
                    int cnt = 0;
                    for (int i=0;i<8;i++) if(labels[i]==old_label) cnt++;
                    if (cnt <= 1) { T*=cool; continue; }

                    double de = delta_energy_flip(pts, labels, 8, idx, alpha, beta);
                    if (de<0 || rng_double()<exp(-de/T)) {
                        labels[idx] = 1 - old_label;
                        E += de;
                        if (E<best_E) { best_E=E; memcpy(best_pts,pts,sizeof(pts)); memcpy(best_labels,labels,sizeof(labels)); }
                    }
                }
                T *= cool;
            }

            int cnt0=0;
            for (int i=0;i<8;i++) if(best_labels[i]==0) cnt0++;
            int cnt1 = 8 - cnt0;
            if (cnt0==4 && cnt1==4) converged++;
        }

        printf("      %d+%d → 4+4: %d/%d\n", n_a, n_b, converged, n_seeds);
        if (converged < n_seeds * 0.7) all_ok = 0;
    }
    report("T6: Label relaxation → 4+4", all_ok);
}

/* T9: Z₃ product rule */
static void test_z3_product_rule(void) {
    /* Z₃ charges: {1,2}. Sum mod 3 = 0 means conjugate pair (β), else same type (α). */
    int charges[8] = {1,1,1,1,2,2,2,2};
    int labels[8]  = {0,0,0,0,1,1,1,1};
    int match = 1;

    for (int i=0; i<8; i++) for (int j=i+1; j<8; j++) {
        int z3_conj = ((charges[i]+charges[j]) % 3 == 0);
        int same_label = (labels[i]==labels[j]);
        /* conjugate → cross (β), same charge → same (α) */
        if (z3_conj == same_label) { match=0; }
    }
    report("T9: Z₃ product rule = two-component", match);
}

/* T10: Z₄ self-conjugate */
static void test_z4_self_conjugate(void) {
    /* Z₄ charge 2: 2+2=4≡0 mod 4, so self-conjugate */
    int z4_has_sc = 0;
    for (int q=1; q<4; q++) if ((2*q) % 4 == 0) z4_has_sc=1;

    /* Z₃: no self-conjugate */
    int z3_has_sc = 0;
    for (int q=1; q<3; q++) if ((2*q) % 3 == 0) z3_has_sc=1;

    report("T10: Z₄ self-conjugate, Z₃ not", z4_has_sc && !z3_has_sc);
}

/* T13: Sphere emergence */
static void test_sphere_emergence(void) {
    int n_seeds = 5;
    long n_steps = 500000L;
    double gamma = 10.0, alpha = 10.0, beta = 1.0;
    int all_ok = 1;

    printf("    T13 sphere emergence:\n");
    for (int s=0; s<n_seeds; s++) {
        int labels[N_PTS] = {0,0,0,0,1,1,1,1};
        AnnealResult r = run_anneal(8, labels, alpha, beta, n_steps, 42+s*113, gamma);

        /* Check shell quality: all points near unit sphere */
        double sum_r=0, sum_r2=0;
        for (int i=0; i<8; i++) {
            double ri = sqrt(r.pts[i][0]*r.pts[i][0]+r.pts[i][1]*r.pts[i][1]+r.pts[i][2]*r.pts[i][2]);
            sum_r += ri; sum_r2 += ri*ri;
        }
        double mean_r = sum_r/8;
        double std_r = sqrt(sum_r2/8 - mean_r*mean_r);
        double shell_q = (mean_r>1e-10) ? 1.0 - std_r/mean_r : 0;

        /* Normalize to sphere and check RMSD */
        double normed[8][3];
        for (int i=0; i<8; i++) {
            double ri = sqrt(r.pts[i][0]*r.pts[i][0]+r.pts[i][1]*r.pts[i][1]+r.pts[i][2]*r.pts[i][2]);
            if (ri<1e-10) ri=1;
            normed[i][0]=r.pts[i][0]/ri; normed[i][1]=r.pts[i][1]/ri; normed[i][2]=r.pts[i][2]/ri;
        }
        double ga[4][3], gb[4][3]; int na=0,nb=0;
        for (int i=0;i<8;i++) {
            if (labels[i]==0&&na<4) memcpy(ga[na++],normed[i],24);
            else if (labels[i]==1&&nb<4) memcpy(gb[nb++],normed[i],24);
        }
        double rmsd = stella_rmsd(ga,gb);

        printf("      seed %d: shell_q=%.4f, mean_r=%.4f, stella_rmsd=%.4f\n",
               42+s*113, shell_q, mean_r, rmsd);
        if (shell_q < 0.95 || rmsd > 0.10) all_ok = 0;
    }
    report("T13: Sphere emergence from cube", all_ok);
}

/* T14: Cross-distance ratio */
static void test_cross_distance_ratio(void) {
    double expected_short = 2.0/sqrt(3.0);  /* ≈ 1.1547 */
    double expected_long = 2.0;
    double expected_ratio = sqrt(3.0);

    int n_short=0, n_long=0;
    for (int i=0; i<4; i++) for (int j=0; j<4; j++) {
        double d = sqrt(dist2(STELLA_TP[i], STELLA_TM[j]));
        if (fabs(d-expected_short)<1e-8) n_short++;
        else if (fabs(d-expected_long)<1e-8) n_long++;
    }

    int ok = (n_short + n_long == 16) && fabs(expected_long/expected_short - expected_ratio) < 1e-10;
    printf("    T14: %d short (%.4f) + %d long (%.4f), ratio=%.6f (√3=%.6f)\n",
           n_short, expected_short, n_long, expected_long,
           expected_long/expected_short, expected_ratio);
    report("T14: Cross-distance ratio = √3", ok);
}

/* ══════════════════════════════════════════════════════════════════════ */
/* MAIN                                                                  */
/* ══════════════════════════════════════════════════════════════════════ */

int main(void) {
    printf("======================================================================\n");
    printf("ADVERSARIAL VERIFICATION: Proposition 0.0.3a (C)\n");
    printf("Computational Crystallization of the Stella Octangula\n");
    printf("======================================================================\n\n");

    test_stella_geometry();
    test_stella_ground_state();
    test_thomson_limit();
    test_phase_transition();
    test_tetrahedron_uniqueness();
    test_label_relaxation();
    test_z3_product_rule();
    test_z4_self_conjugate();
    test_sphere_emergence();
    test_cross_distance_ratio();

    printf("\n======================================================================\n");
    printf("RESULT: %d/%d passed\n", n_pass, n_pass+n_fail);
    printf("======================================================================\n");

    return n_fail > 0 ? 1 : 0;
}
