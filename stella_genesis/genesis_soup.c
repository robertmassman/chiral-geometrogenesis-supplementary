/*
 * Stella Genesis: G1-Only Geometric Substrate
 *
 * Tests whether Paper 2 dynamics (inter-component coupling, arrow of time,
 * self-replication) emerge from Paper 1 (G1) foundations alone.
 *
 * Key difference from stella_lang/soup_2d.c:
 *   - No CPY01/CPY10 instructions (removes Paper 2 dependency)
 *   - No second head h1 (single-head VM)
 *   - Inter-component coupling via pressure-mediated geometric transfer
 *   - Pressure functions from Def 0.1.3: P_c(x) = 1/(|x-x_c|^2 + eps^2)
 *
 * G1 foundations used:
 *   - Def 0.1.1: Two-component dS = dT+ u dT-
 *   - Def 0.1.2: Z_3 phase structure, identity test
 *   - Def 0.1.3: Pressure functions (axioms P1-P5)
 *   - Def 0.0.0: Stella octangula vertex coordinates
 *
 * Build: cc -O3 -o genesis_soup genesis_soup.c -lm
 * Run:   ./genesis_soup [epochs] [seed] [coupling_strength] [mode]
 *        mode: 0=VM+coupling, 1=coupling-only, 2=VM-only
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

/* ── Configuration ─────────────────────────────────────────────────── */

#define MAX_SITES   135000
#define MAX_NBR     8
#define PROG_SIZE   24
#define MAX_STEPS   729

/* GenesisVM opcodes — G1 only, no CPY, no FWD1 */
enum {
    OP_NOP   = 0,  /* (0,0) identity         — Def 0.1.2 */
    OP_ROT   = 1,  /* (0,1) +1 mod 3         — Def 0.1.2 */
    OP_DROT  = 2,  /* (0,2) +2 mod 3         — Def 0.1.2 */
    OP_FWD   = 3,  /* (1,0) advance head     — computational */
    OP_BCK   = 4,  /* (1,1) retreat head     — computational */
    OP_OPEN  = 5,  /* (1,2) if h==0 skip     — Def 0.1.2 */
    OP_CLOSE = 6,  /* (2,0) if h!=0 jump     — Def 0.1.2 */
    OP_SENSE = 7,  /* (2,1) read pressure ratio — Def 0.1.3 */
    OP_COUPLE= 8,  /* (2,2) mark for enhanced coupling */
};

/* Instruction mode: 0 = classic (SENSE/COUPLE act as NOP), 1 = enhanced,
 * 2 = write (SENSE + WRITE replacing COUPLE) */
#define INSTR_MODE_CLASSIC  0
#define INSTR_MODE_ENHANCED 1
#define INSTR_MODE_WRITE    2

/* VM execution context — provides geometric awareness to enhanced opcodes */
typedef struct {
    float *pressure_ratio;  /* P_own/(P_own+P_other) per tape position */
    float *pressure_ratio_color[3]; /* per-color ratios (if color_pressure) */
    int color_pressure;     /* 0=max, 1=per-color */
    uint8_t *couple_flags;  /* set by COUPLE instruction, read by coupling */
    uint8_t *other_tape;    /* other surface's work buffer (for WRITE) */
    int other_tape_len;     /* length of other_tape */
    int instr_mode;         /* 0=classic, 1=enhanced, 2=write */
    long sense_count;       /* diagnostic: times SENSE executed */
    long couple_count;      /* diagnostic: times COUPLE executed */
    long write_count;       /* diagnostic: times WRITE succeeded */
    long write_blocked;     /* diagnostic: times WRITE blocked by pressure */
} VMContext;

/* ── RNG (xoshiro128+) ────────────────────────────────────────────── */

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
static inline float rng_float(void) { return (rng_next() >> 8) / 16777216.0f; }

/* ── Mesh (triangulated tetrahedron) ──────────────────────────────── */

typedef struct {
    int n_sites;
    float pos[MAX_SITES][3];
    int n_nbr[MAX_SITES];
    int nbr[MAX_SITES][MAX_NBR];
} Mesh;

/* T+ vertices: cube corners with s1*s2*s3 = +1 (Def 0.0.0) */
static const float TV_PLUS[4][3] = {
    { 1, 1, 1}, { 1,-1,-1}, {-1, 1,-1}, {-1,-1, 1}
};

/* T- vertices: cube corners with s1*s2*s3 = -1 (Def 0.0.0) */
static const float TV_MINUS[4][3] = {
    {-1,-1,-1}, {-1, 1, 1}, { 1,-1, 1}, { 1, 1,-1}
};

static const int FACES[4][3] = {
    {1,2,3}, {0,3,2}, {0,1,3}, {0,2,1}
};

/* Spatial hash for O(1) average-case mesh deduplication at high n_sub.
 * Positions lie in [-2, 2]³; cell size = eps so nearby points hash together. */
#define HASH_SIZE 196613 /* prime, larger than MAX_SITES */
static int hash_head[HASH_SIZE];   /* head of chain per bucket (-1 = empty) */
static int hash_next[MAX_SITES];   /* next in chain per site (-1 = end) */

static void mesh_hash_reset(void) {
    memset(hash_head, -1, sizeof(hash_head));
}

static unsigned mesh_hash_key(float x, float y, float z, float cell) {
    int ix = (int)floorf((x + 2.0f) / cell);
    int iy = (int)floorf((y + 2.0f) / cell);
    int iz = (int)floorf((z + 2.0f) / cell);
    unsigned h = (unsigned)(ix * 73856093u ^ iy * 19349663u ^ iz * 83492791u);
    return h % HASH_SIZE;
}

static int mesh_find_or_add(Mesh *m, float x, float y, float z, float eps) {
    float cell = eps * 2.0f;  /* cell ≥ eps so matching points share a cell or neighbor */
    /* Check the 3x3x3 neighborhood of cells */
    int ix0 = (int)floorf((x + 2.0f) / cell);
    int iy0 = (int)floorf((y + 2.0f) / cell);
    int iz0 = (int)floorf((z + 2.0f) / cell);
    float eps2 = eps * eps;
    for (int dx = -1; dx <= 1; dx++)
    for (int dy = -1; dy <= 1; dy++)
    for (int dz = -1; dz <= 1; dz++) {
        unsigned h = (unsigned)((ix0+dx) * 73856093u ^ (iy0+dy) * 19349663u ^ (iz0+dz) * 83492791u) % HASH_SIZE;
        for (int i = hash_head[h]; i >= 0; i = hash_next[i]) {
            float ddx = m->pos[i][0] - x;
            float ddy = m->pos[i][1] - y;
            float ddz = m->pos[i][2] - z;
            if (ddx*ddx + ddy*ddy + ddz*ddz < eps2) return i;
        }
    }
    int id = m->n_sites++;
    m->pos[id][0] = x; m->pos[id][1] = y; m->pos[id][2] = z;
    m->n_nbr[id] = 0;
    unsigned h = mesh_hash_key(x, y, z, cell);
    hash_next[id] = hash_head[h];
    hash_head[h] = id;
    return id;
}

static void mesh_add_edge(Mesh *m, int a, int b) {
    if (a == b) return;
    for (int i = 0; i < m->n_nbr[a]; i++)
        if (m->nbr[a][i] == b) return;
    if (m->n_nbr[a] < MAX_NBR) m->nbr[a][m->n_nbr[a]++] = b;
    if (m->n_nbr[b] < MAX_NBR) m->nbr[b][m->n_nbr[b]++] = a;
}

/* Warp barycentric coordinates to concentrate sites near the face incenter.
 * Uses power-law remapping: λ'_i = λ_i^α / Σ λ_j^α  with α < 1.
 * α = 1.0 → uniform (no warping), α < 1 → incenter-concentrated.
 * Preserves triangulation topology: vertices stay at vertices. */
static void warp_barycentric(float *fi, float *fj, float *fk, float alpha) {
    if (alpha >= 0.999f) return;  /* skip if uniform */
    float a = *fi, b = *fj, c = *fk;
    /* Handle exact zeros (vertices/edges) — 0^α = 0 */
    float wa = (a > 0.0f) ? powf(a, alpha) : 0.0f;
    float wb = (b > 0.0f) ? powf(b, alpha) : 0.0f;
    float wc = (c > 0.0f) ? powf(c, alpha) : 0.0f;
    float sum = wa + wb + wc;
    if (sum > 0.0f) { *fi = wa / sum; *fj = wb / sum; *fk = wc / sum; }
}

static void mesh_build_adaptive(Mesh *m, const float verts[4][3],
                                 int n_sub, float warp_alpha) {
    memset(m, 0, sizeof(*m));
    mesh_hash_reset();
    float eps = 0.01f;

    /* Temporary grid for vertex IDs per face (heap-allocated for high n_sub) */
    int stride = (n_sub+1) * (n_sub+1);
    int *grid = (int *)malloc(4 * stride * sizeof(int));
    memset(grid, -1, 4 * stride * sizeof(int));

    for (int f = 0; f < 4; f++) {
        const float *va = verts[FACES[f][0]];
        const float *vb = verts[FACES[f][1]];
        const float *vc = verts[FACES[f][2]];

        for (int i = 0; i <= n_sub; i++) {
            for (int j = 0; j <= n_sub - i; j++) {
                float fi = (float)i / n_sub;
                float fj = (float)j / n_sub;
                float fk = 1.0f - fi - fj;
                warp_barycentric(&fi, &fj, &fk, warp_alpha);
                float x = fk * va[0] + fi * vb[0] + fj * vc[0];
                float y = fk * va[1] + fi * vb[1] + fj * vc[1];
                float z = fk * va[2] + fi * vb[2] + fj * vc[2];
                int id = mesh_find_or_add(m, x, y, z, eps);
                grid[f * stride + i * (n_sub+1) + j] = id;
            }
        }

        /* Add edges within this face's triangulation */
        for (int i = 0; i <= n_sub; i++) {
            for (int j = 0; j <= n_sub - i; j++) {
                int cur = grid[f * stride + i * (n_sub+1) + j];
                if (i + 1 <= n_sub && j <= n_sub - (i+1)) {
                    int right = grid[f * stride + (i+1) * (n_sub+1) + j];
                    mesh_add_edge(m, cur, right);
                }
                if (j + 1 <= n_sub - i) {
                    int up = grid[f * stride + i * (n_sub+1) + (j+1)];
                    mesh_add_edge(m, cur, up);
                }
                if (i + 1 <= n_sub && j - 1 >= 0) {
                    int diag = grid[f * stride + (i+1) * (n_sub+1) + (j-1)];
                    mesh_add_edge(m, cur, diag);
                }
            }
        }
    }
    free(grid);
}

/* ── Pressure functions (Def 0.1.3) ──────────────────────────────── */

static float pressure_at_site(const float pos[3], const float verts[4][3],
                               float epsilon) {
    /* P(x) = max over vertices v of 1/(|x-v|^2 + eps^2)
     * Axiom P1: maximum at source vertex
     * Axiom P5: monotonically decreasing with distance */
    float p_max = 0.0f;
    for (int v = 0; v < 4; v++) {
        float dx = pos[0] - verts[v][0];
        float dy = pos[1] - verts[v][1];
        float dz = pos[2] - verts[v][2];
        float r2 = dx*dx + dy*dy + dz*dz;
        float p = 1.0f / (r2 + epsilon * epsilon);
        if (p > p_max) p_max = p;
    }
    return p_max;
}

/* ── Genesis Soup ─────────────────────────────────────────────────── */

typedef struct {
    Mesh mesh_tp;           /* T+ surface mesh (connectivity + positions) */
    Mesh mesh_tm;           /* T- surface mesh (connectivity + positions) */
    uint8_t *tp_data;       /* T+ surface trits */
    uint8_t *tm_data;       /* T- surface trits */
    float *pp_at_tp;        /* T+ pressure at T+ site positions */
    float *pm_at_tp;        /* T- pressure at T+ site positions */
    float *pp_at_tm;        /* T+ pressure at T- site positions */
    float *pm_at_tm;        /* T- pressure at T- site positions */
    int prog_size;
    int max_steps;
    double mutation_rate;
    double coupling_strength;
    float epsilon;          /* pressure regularization */
    uint8_t *work_a;        /* scratch buffer for patches */
    uint8_t *work_b;
    int *patch_a;           /* BFS patch site indices */
    int *patch_b;
    long epoch;
    int mode;               /* 0=VM+couple, 1=couple-only, 2=VM-only */
    double chirality;       /* 0=symmetric, >0 = T+ favored */
    int chirality_mode;     /* 0=pressure asymmetry, 1=coupling weight */
    int instr_mode;         /* 0=classic, 1=enhanced (SENSE/COUPLE), 2=write (SENSE/WRITE) */
    float warp_alpha;       /* mesh warping: 1.0=uniform, <1=incenter-concentrated */
    int color_pressure;     /* 0=max-vertex (classic), 1=per-color pressure (Def 0.1.3) */
    float phase_lock;       /* Thm 2.2.1 phase-lock strength (0=off, >0=nudge rate) */
    int kuramoto_mode;      /* 0=majority-vote (Z₃ discrete), 1=full Kuramoto (continuous phase) */
    float *phase_tp;        /* continuous phase per T+ site [0, 2π), for Kuramoto mode */
    float *phase_tm;        /* continuous phase per T- site [0, 2π), for Kuramoto mode */
    uint8_t *dominant_color_tp; /* precomputed: argmax_c P_c(x) for each T+ site */
    uint8_t *dominant_color_tm; /* precomputed: argmax_c P_c(x) for each T- site */
    long phase_lock_events; /* count of phase-lock nudges applied */

    /* Thm 0.2.4: Pre-geometric energy functional
     * E[χ] = Σ|a_c|² + λ(|χ_total|² - v₀²)²
     * Drives local color populations toward |a_R|=|a_G|=|a_B| */
    float energy_lambda;    /* quartic coupling strength (0=off) */
    long energy_flips;      /* count of energy-driven trit changes */

    /* Thm 3.1.1: Phase-gradient mass generation (diagnostic observable)
     * m(x) = (g_χ·ω₀/Λ) · v_χ(x) · |∇φ(x)|
     * Measures whether mass-like structure emerges from geometry. */
    int mass_mode;          /* 0=off, 1=measure mass observable each report */
    float *grad_phi_tp;     /* |∇φ| per T+ site */
    float *grad_phi_tm;     /* |∇φ| per T- site */
    float *vchi_tp;         /* v_χ(x) = VEV field at T+ sites */
    float *vchi_tm;         /* v_χ(x) = VEV field at T- sites */
    float *mass_tp;         /* mass density per T+ site */
    float *mass_tm;         /* mass density per T- site */
    float mass_couple;      /* 0=off, >0 = mass-stabilized mutation (Q3) */
    long mass_couple_blocks;/* count of mutations blocked by mass inertia */
    float mass_kuramoto;    /* 0=off, >0 = mass-modulated Kuramoto K (Q3b) */
    long mass_kuramoto_boosts; /* count of sites where mass boosted K */
    float mass_geo;         /* 0=off, >0 = mass-modulated geometric coupling (Q3c) */
    long mass_geo_boosts;   /* count of sites where mass boosted geo coupling */

    /* GG1: Snapshot mode (GPU-like parallel execution semantics).
     * When snapshot_mode=1, all reads within an epoch use state captured
     * at the epoch's start. Writes go to live arrays. This simulates
     * GPU execution where all sites see the same "old" state. */
    int snapshot_mode;      /* 0=sequential (default), 1=snapshot (GPU-like) */
    uint8_t *snap_tp;       /* snapshot of tp_data at epoch start */
    uint8_t *snap_tm;       /* snapshot of tm_data at epoch start */
    float *snap_phase_tp;   /* snapshot of phase_tp at epoch start */
    float *snap_phase_tm;   /* snapshot of phase_tm at epoch start */
    int kuramoto_sub_steps; /* GG2b: Kuramoto sub-sweeps per epoch (1=default).
                             * In snapshot mode, re-snapshots phase arrays between
                             * sub-steps to allow multi-hop diffusion within one epoch. */

    /* Scratch buffers for enhanced VM context */
    float *pressure_ratio_a;  /* P_own/(P_own+P_other) for T+ patch */
    float *pressure_ratio_b;  /* P_own/(P_own+P_other) for T- patch */
    /* Per-color pressure ratios for color-aware WRITE (color_pressure=1).
     * Color c (trit value) uses vertex TV_PLUS[c+1] and TV_MINUS[c+1].
     * Mapping: trit 0=R, 1=G, 2=B (Def 0.1.3 §2.1 vertex-color assignment) */
    float *pressure_ratio_color_a[3]; /* T+ patch, per-color */
    float *pressure_ratio_color_b[3]; /* T- patch, per-color */
    uint8_t *couple_flags_a;  /* COUPLE flags for T+ patch */
    uint8_t *couple_flags_b;  /* COUPLE flags for T- patch */

    /* Diagnostics */
    long coupling_tp_to_tm; /* count of T+ -> T- transfers */
    long coupling_tm_to_tp; /* count of T- -> T+ transfers */
    long total_couplings;   /* total coupling attempts */
    long sense_count;        /* times SENSE executed */
    long couple_count;       /* times COUPLE executed */
    long couple_enhanced;    /* coupling events at COUPLE-flagged sites */
    long write_count;        /* times WRITE succeeded (instr_mode=2) */
    long write_blocked;      /* times WRITE blocked by pressure (instr_mode=2) */

    /* COUPLE geography histograms */
    long *couple_hist_tp;   /* per-site: times site got COUPLE-flagged on T+ */
    long *couple_hist_tm;   /* per-site: times site got COUPLE-flagged on T- */
    long *visit_hist;       /* per-site: times site appeared in a BFS patch */

    /* K2: Phase wavefront diagnostics — measures whether phase perturbations
     * propagate diffusively or ballistically through the full Genesis soup.
     * Motivation: K1 showed pure Kuramoto is diffusive (exponent 0.527).
     * The full soup (VM + mass coupling + energy functional) may create
     * inertia that converts heat-equation dynamics into wave-equation. */
    int phase_diag_interval;   /* report phase shells every N epochs (0=off) */
    long phase_perturb_epoch;  /* epoch at which to inject perturbation (-1=off) */
    float phase_perturb_delta; /* perturbation amplitude (radians) */
    int *phase_bfs_dist;       /* BFS distance from perturbation site (T+) */
    int phase_bfs_max_d;       /* maximum BFS distance */
    int phase_perturb_site;    /* site index for perturbation */
    int *phase_shell_count;    /* count of sites per BFS shell */
    long *phase_arrival;       /* first epoch where shell d exceeded threshold */
    FILE *phase_diag_file;     /* output file for phase diagnostics */
    float *phase_baseline_tp;  /* saved phase state at perturbation epoch */
    float *phase_baseline_shell_dev; /* per-shell mean |Δφ| at baseline (pre-perturb) */
} GenesisSoup;

static void genesis_init(GenesisSoup *gs, int n_sub, uint32_t seed) {
    rng_seed(seed);

    /* Build separate meshes for T+ and T- (Def 0.1.1: dS = dT+ u dT-) */
    float alpha = gs->warp_alpha > 0.0f ? gs->warp_alpha : 1.0f;
    mesh_build_adaptive(&gs->mesh_tp, TV_PLUS, n_sub, alpha);
    mesh_build_adaptive(&gs->mesh_tm, TV_MINUS, n_sub, alpha);
    int n_tp = gs->mesh_tp.n_sites;
    int n_tm = gs->mesh_tm.n_sites;

    /* Both meshes should have identical site counts (same subdivision) */
    if (n_tp != n_tm) {
        fprintf(stderr, "ERROR: mesh site count mismatch: T+=%d T-=%d\n",
                n_tp, n_tm);
        exit(1);
    }
    int n = n_tp;

    printf("Mesh: %d sites per tetrahedron, %d total (dual-mesh)\n", n, 2*n);

    /* Allocate surface data */
    gs->tp_data = calloc(n, sizeof(uint8_t));
    gs->tm_data = calloc(n, sizeof(uint8_t));
    gs->pp_at_tp = calloc(n, sizeof(float));
    gs->pm_at_tp = calloc(n, sizeof(float));
    gs->pp_at_tm = calloc(n, sizeof(float));
    gs->pm_at_tm = calloc(n, sizeof(float));

    /* Random Z_3 initialization */
    for (int i = 0; i < n; i++) {
        gs->tp_data[i] = rng_int(3);
        gs->tm_data[i] = rng_int(3);
    }

    /* Precompute pressure at BOTH surface positions (Def 0.1.3)
     * Dual-mesh fix: evaluate pressure from each tetrahedron's vertices
     * at each surface's own site positions. Coupling evaluates both
     * perspectives independently, eliminating single-mesh bias.
     *
     * Chirality mode 0 (pressure asymmetry): P+ is scaled by (1+chirality),
     * making right-handed (T+) pressure intrinsically stronger. This models
     * the framework's right-handed pressure convention (Axiom P3). */
    float p_plus_scale = 1.0f;
    if (gs->chirality_mode == 0) {
        p_plus_scale = 1.0f + (float)gs->chirality;
    }
    for (int i = 0; i < n; i++) {
        gs->pp_at_tp[i] = p_plus_scale *
            pressure_at_site(gs->mesh_tp.pos[i], TV_PLUS, gs->epsilon);
        gs->pm_at_tp[i] = pressure_at_site(gs->mesh_tp.pos[i], TV_MINUS,
                                            gs->epsilon);
        gs->pp_at_tm[i] = p_plus_scale *
            pressure_at_site(gs->mesh_tm.pos[i], TV_PLUS, gs->epsilon);
        gs->pm_at_tm[i] = pressure_at_site(gs->mesh_tm.pos[i], TV_MINUS,
                                            gs->epsilon);
    }

    /* Scratch buffers */
    gs->work_a = calloc(gs->prog_size, sizeof(uint8_t));
    gs->work_b = calloc(gs->prog_size, sizeof(uint8_t));
    gs->patch_a = calloc(gs->prog_size, sizeof(int));
    gs->patch_b = calloc(gs->prog_size, sizeof(int));
    gs->pressure_ratio_a = calloc(gs->prog_size, sizeof(float));
    gs->pressure_ratio_b = calloc(gs->prog_size, sizeof(float));
    gs->couple_flags_a = calloc(gs->prog_size, sizeof(uint8_t));
    gs->couple_flags_b = calloc(gs->prog_size, sizeof(uint8_t));
    for (int c = 0; c < 3; c++) {
        gs->pressure_ratio_color_a[c] = calloc(gs->prog_size, sizeof(float));
        gs->pressure_ratio_color_b[c] = calloc(gs->prog_size, sizeof(float));
    }
    gs->couple_hist_tp = calloc(n, sizeof(long));
    gs->couple_hist_tm = calloc(n, sizeof(long));
    gs->visit_hist = calloc(n, sizeof(long));
    gs->epoch = 0;

    /* Continuous phase arrays for Kuramoto mode (Thm 2.2.1).
     * Each site's phase φ ∈ [0, 2π) maps to Z₃ trit via quantization:
     * trit = round(3φ/(2π)) mod 3. Initialized from random trit values. */
    gs->phase_tp = calloc(n, sizeof(float));
    gs->phase_tm = calloc(n, sizeof(float));
    {
        float third = 2.0f * (float)M_PI / 3.0f;
        for (int i = 0; i < n; i++) {
            gs->phase_tp[i] = gs->tp_data[i] * third;
            gs->phase_tm[i] = gs->tm_data[i] * third;
        }
    }

    /* Phase-gradient mass arrays (Thm 3.1.1) — allocated even if mass_mode=0
     * so that mass can be measured on-demand without reallocation */
    gs->grad_phi_tp = calloc(n, sizeof(float));
    gs->grad_phi_tm = calloc(n, sizeof(float));
    gs->vchi_tp = calloc(n, sizeof(float));
    gs->vchi_tm = calloc(n, sizeof(float));
    gs->mass_tp = calloc(n, sizeof(float));
    gs->mass_tm = calloc(n, sizeof(float));

    /* GG1: Snapshot buffers (allocated even if snapshot_mode=0, minimal cost) */
    gs->snap_tp = calloc(n, sizeof(uint8_t));
    gs->snap_tm = calloc(n, sizeof(uint8_t));
    gs->snap_phase_tp = calloc(n, sizeof(float));
    gs->snap_phase_tm = calloc(n, sizeof(float));

    /* Diagnostics */
    gs->coupling_tp_to_tm = 0;
    gs->coupling_tm_to_tp = 0;
    gs->total_couplings = 0;
    gs->sense_count = 0;
    gs->couple_count = 0;
    gs->couple_enhanced = 0;
    gs->phase_lock_events = 0;

    /* Precompute dominant color per site (Thm 2.2.1 phase-lock attractor).
     * For each site, find argmax_c P_c(x) = nearest own-tetrahedron vertex.
     * Color c maps to vertex index c+1 in TV arrays (Def 0.1.3). */
    gs->dominant_color_tp = calloc(n, sizeof(uint8_t));
    gs->dominant_color_tm = calloc(n, sizeof(uint8_t));
    for (int i = 0; i < n; i++) {
        /* T+ site: find nearest TV_PLUS vertex (colors 0,1,2 → vertices 1,2,3) */
        float best_d2 = 1e30f;
        uint8_t best_c = 0;
        for (int c = 0; c < 3; c++) {
            float dx = gs->mesh_tp.pos[i][0] - TV_PLUS[c+1][0];
            float dy = gs->mesh_tp.pos[i][1] - TV_PLUS[c+1][1];
            float dz = gs->mesh_tp.pos[i][2] - TV_PLUS[c+1][2];
            float d2 = dx*dx + dy*dy + dz*dz;
            if (d2 < best_d2) { best_d2 = d2; best_c = c; }
        }
        gs->dominant_color_tp[i] = best_c;
        /* T- site: find nearest TV_MINUS vertex */
        best_d2 = 1e30f;
        best_c = 0;
        for (int c = 0; c < 3; c++) {
            float dx = gs->mesh_tm.pos[i][0] - TV_MINUS[c+1][0];
            float dy = gs->mesh_tm.pos[i][1] - TV_MINUS[c+1][1];
            float dz = gs->mesh_tm.pos[i][2] - TV_MINUS[c+1][2];
            float d2 = dx*dx + dy*dy + dz*dz;
            if (d2 < best_d2) { best_d2 = d2; best_c = c; }
        }
        gs->dominant_color_tm[i] = best_c;
    }

    /* K2: Phase wavefront diagnostics — compute BFS distances from a
     * central T+ site (face centroid) for tracking phase perturbation
     * propagation. Only computed if phase_diag_interval > 0. */
    gs->phase_bfs_dist = NULL;
    gs->phase_shell_count = NULL;
    gs->phase_arrival = NULL;
    gs->phase_diag_file = NULL;
    gs->phase_bfs_max_d = 0;
    gs->phase_perturb_site = -1;

    if (gs->phase_diag_interval > 0) {
        /* Find central site: closest to face 0 centroid */
        float cx = (TV_PLUS[1][0] + TV_PLUS[2][0] + TV_PLUS[3][0]) / 3.0f;
        float cy = (TV_PLUS[1][1] + TV_PLUS[2][1] + TV_PLUS[3][1]) / 3.0f;
        float cz = (TV_PLUS[1][2] + TV_PLUS[2][2] + TV_PLUS[3][2]) / 3.0f;
        float best = 1e10f;
        gs->phase_perturb_site = 0;
        for (int i = 0; i < n; i++) {
            float dx = gs->mesh_tp.pos[i][0] - cx;
            float dy = gs->mesh_tp.pos[i][1] - cy;
            float dz = gs->mesh_tp.pos[i][2] - cz;
            float d2 = dx*dx + dy*dy + dz*dz;
            if (d2 < best) { best = d2; gs->phase_perturb_site = i; }
        }

        /* BFS from perturbation site */
        gs->phase_bfs_dist = (int *)malloc(n * sizeof(int));
        for (int i = 0; i < n; i++) gs->phase_bfs_dist[i] = -1;
        gs->phase_bfs_dist[gs->phase_perturb_site] = 0;
        gs->phase_bfs_max_d = 0;
        int *queue = (int *)malloc(n * sizeof(int));
        int qh = 0, qt = 0;
        queue[qt++] = gs->phase_perturb_site;
        while (qh < qt) {
            int u = queue[qh++];
            for (int j = 0; j < gs->mesh_tp.n_nbr[u]; j++) {
                int v = gs->mesh_tp.nbr[u][j];
                if (gs->phase_bfs_dist[v] < 0) {
                    gs->phase_bfs_dist[v] = gs->phase_bfs_dist[u] + 1;
                    if (gs->phase_bfs_dist[v] > gs->phase_bfs_max_d)
                        gs->phase_bfs_max_d = gs->phase_bfs_dist[v];
                    queue[qt++] = v;
                }
            }
        }
        free(queue);

        /* Shell counts */
        int md = gs->phase_bfs_max_d;
        gs->phase_shell_count = (int *)calloc(md + 1, sizeof(int));
        for (int i = 0; i < n; i++)
            if (gs->phase_bfs_dist[i] >= 0)
                gs->phase_shell_count[gs->phase_bfs_dist[i]]++;

        /* Arrival times (-1 = not yet arrived) */
        gs->phase_arrival = (long *)malloc((md + 1) * sizeof(long));
        for (int d = 0; d <= md; d++) gs->phase_arrival[d] = -1;

        /* Baseline arrays — filled at perturbation epoch */
        gs->phase_baseline_tp = (float *)calloc(n, sizeof(float));
        gs->phase_baseline_shell_dev = (float *)calloc(md + 1, sizeof(float));

        /* Open diagnostics file */
        gs->phase_diag_file = fopen("phase_K2_diag.jsonl", "w");
        if (gs->phase_diag_file) {
            fprintf(gs->phase_diag_file,
                    "{\"type\":\"header\", \"n_sub\":%d, \"n_sites\":%d, "
                    "\"max_bfs_d\":%d, \"perturb_site\":%d, "
                    "\"perturb_epoch\":%ld, \"perturb_delta\":%.6f, "
                    "\"diag_interval\":%d, \"shell_counts\":[",
                    n_sub, n, md, gs->phase_perturb_site,
                    gs->phase_perturb_epoch, gs->phase_perturb_delta,
                    gs->phase_diag_interval);
            for (int d = 0; d <= md; d++) {
                if (d > 0) fprintf(gs->phase_diag_file, ",");
                fprintf(gs->phase_diag_file, "%d", gs->phase_shell_count[d]);
            }
            fprintf(gs->phase_diag_file, "]}\n");
            fflush(gs->phase_diag_file);
        }
    }
}

/* ── BFS patch extraction ─────────────────────────────────────────── */

static int bfs_extract(const Mesh *m, int center, int max_count,
                       int *patch_sites) {
    /* BFS from center, collecting up to max_count sites */
    uint8_t visited[MAX_SITES];
    memset(visited, 0, m->n_sites);
    int queue[MAX_SITES];
    int head = 0, tail = 0, count = 0;

    visited[center] = 1;
    queue[tail++] = center;

    while (head < tail && count < max_count) {
        int site = queue[head++];
        patch_sites[count++] = site;

        /* Sort neighbors for deterministic BFS order */
        int sorted[MAX_NBR];
        int nn = m->n_nbr[site];
        memcpy(sorted, m->nbr[site], nn * sizeof(int));
        for (int i = 1; i < nn; i++) {
            int key = sorted[i];
            int j = i - 1;
            while (j >= 0 && sorted[j] > key) {
                sorted[j+1] = sorted[j]; j--;
            }
            sorted[j+1] = key;
        }
        for (int i = 0; i < nn; i++) {
            if (!visited[sorted[i]]) {
                visited[sorted[i]] = 1;
                queue[tail++] = sorted[i];
            }
        }
    }
    return count;
}

/* ── GenesisVM — single-head, G1-only ─────────────────────────────── */

static void genesis_execute(uint8_t *tape, int tape_len, int max_steps,
                            VMContext *ctx) {
    int ip = 0;     /* instruction pointer */
    int h = 0;      /* single head */
    int steps = 0;

    while (steps < max_steps && ip + 1 < tape_len) {
        int op = tape[ip] * 3 + tape[ip + 1];

        switch (op) {
        case OP_NOP:
            break;

        case OP_SENSE:
            if (ctx && (ctx->instr_mode == INSTR_MODE_ENHANCED ||
                        ctx->instr_mode == INSTR_MODE_WRITE) &&
                ctx->pressure_ratio) {
                /* SENSE: Read pressure ratio P_own/(P_own+P_other) at head
                 * position and encode as Z₃ trit (Def 0.1.3).
                 *   ratio > 2/3 → 0 (own-surface dominant)
                 *   ratio ∈ [1/3, 2/3] → 1 (balanced)
                 *   ratio < 1/3 → 2 (other-surface dominant)
                 * Gives programs awareness of their geometric position
                 * on the stella octangula. */
                float r = ctx->pressure_ratio[h];
                if (r > 0.6667f) tape[h] = 0;
                else if (r > 0.3333f) tape[h] = 1;
                else tape[h] = 2;
                ctx->sense_count++;
            }
            /* else: classic mode, acts as NOP */
            break;

        case OP_COUPLE:
            if (ctx && ctx->instr_mode == INSTR_MODE_WRITE &&
                ctx->other_tape && ctx->pressure_ratio) {
                /* WRITE (instr_mode=2): Copy tape[h] to other_tape[h],
                 * gated by pressure dominance (Def 0.1.3).
                 * Succeeds only if P_own > P_other at head position.
                 * This gives programs deterministic, targeted control
                 * over inter-tetrahedron information transfer, grounded
                 * entirely in G1 pressure functions. */
                if (h < ctx->other_tape_len) {
                    /* Color-aware WRITE (Def 0.1.3): OR-gate.
                     * Write succeeds if max-pressure gate OR the
                     * per-color gate (for the trit's color) is open.
                     * This preserves vertex coherence while unlocking
                     * deep-blocked sites via 2-of-3 color channels. */
                    float wr = ctx->pressure_ratio[h];
                    if (ctx->color_pressure &&
                        ctx->pressure_ratio_color[tape[h]]) {
                        float wr_c = ctx->pressure_ratio_color[tape[h]][h];
                        if (wr_c > wr) wr = wr_c;
                    }
                    if (wr > 0.5f) {
                        ctx->other_tape[h] = tape[h];
                        ctx->write_count++;
                    } else {
                        ctx->write_blocked++;
                    }
                }
            } else if (ctx && ctx->instr_mode == INSTR_MODE_ENHANCED &&
                ctx->couple_flags) {
                /* COUPLE (instr_mode=1): Mark current site for enhanced
                 * geometric coupling. During the coupling phase, flagged
                 * sites get 2× coupling probability. */
                ctx->couple_flags[h] = 1;
                ctx->couple_count++;
            }
            /* else: classic mode, acts as NOP */
            break;

        case OP_ROT:
            tape[h] = tape[h] < 2 ? tape[h] + 1 : 0;
            break;

        case OP_DROT:
            tape[h] = tape[h] > 0 ? tape[h] - 1 : 2;
            break;

        case OP_FWD:
            h = (h + 1) % tape_len;
            break;

        case OP_BCK:
            h = (h - 1 + tape_len) % tape_len;
            break;

        case OP_OPEN:
            if (tape[h] == 0) {
                int depth = 1, pos = ip + 2;
                while (depth > 0 && pos + 1 < tape_len) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == OP_OPEN) depth++;
                    else if (inner == OP_CLOSE) depth--;
                    pos += 2;
                }
                if (depth == 0) ip = pos - 2;
            }
            break;

        case OP_CLOSE:
            if (tape[h] != 0) {
                int depth = 1, pos = ip - 2;
                while (depth > 0 && pos >= 0) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == OP_CLOSE) depth++;
                    else if (inner == OP_OPEN) depth--;
                    pos -= 2;
                }
                if (depth == 0) ip = pos + 2;
            }
            break;
        }

        ip += 2;
        steps++;
    }
}

/* ── Geometric Coupling (replaces CPY01) ──────────────────────────── */

static void geometric_couple(GenesisSoup *gs, int *patch_sites, int count) {
    /* Dual-mesh coupling: evaluate pressure at BOTH surface positions
     * independently, giving each direction equal structural opportunity.
     *
     * At T+ site: P+(x_tp) > P-(x_tp) → T+ can overwrite T-
     * At T- site: P-(x_tm) > P+(x_tm) → T- can overwrite T+
     *
     * Chirality modes:
     *   Mode 0 (pressure asymmetry): P+ already scaled in precomputation,
     *     coupling formula is unchanged — asymmetry enters via pressure values.
     *   Mode 1 (coupling weight): Multiply T+→T- prob by (1+chirality),
     *     T-→T+ prob by (1-chirality). Direct coupling asymmetry.
     */
    float w_tp_to_tm = 1.0f;  /* coupling weight T+→T- */
    float w_tm_to_tp = 1.0f;  /* coupling weight T-→T+ */
    if (gs->chirality_mode == 1) {
        w_tp_to_tm = 1.0f + (float)gs->chirality;
        w_tm_to_tp = 1.0f - (float)gs->chirality;
        if (w_tm_to_tp < 0.0f) w_tm_to_tp = 0.0f;
    }

    for (int i = 0; i < count; i++) {
        int site = patch_sites[i];

        /* COUPLE enhancement: if either surface flagged this site,
         * multiply coupling probability by 2× (capped at 1.0).
         * This lets programs that SENSE their environment strategically
         * enhance coupling at specific sites. */
        float enhance = 1.0f;
        if (gs->instr_mode == INSTR_MODE_ENHANCED) {
            if (gs->couple_flags_a[i] || gs->couple_flags_b[i])
                enhance = 2.0f;
        }

        /* T+ perspective: always use max-vertex pressure for bulk coupling.
         * Per-color pressure only affects the WRITE gate, not geometric coupling. */
        float pp_tp = gs->pp_at_tp[site];
        float pm_tp = gs->pm_at_tp[site];
        float sum_tp = pp_tp + pm_tp;
        if (sum_tp > 1e-10f) {
            float delta_tp = pp_tp - pm_tp;
            if (delta_tp > 0) {
                float prob = enhance * w_tp_to_tm *
                    (float)gs->coupling_strength * delta_tp / sum_tp;
                /* Q3c: mass-modulated geometric coupling (Thm 3.1.1) */
                if (gs->mass_geo > 0.0f && gs->mass_tp) {
                    float boost = 1.0f + gs->mass_geo * gs->mass_tp[site];
                    prob *= boost;
                    if (boost > 1.01f) gs->mass_geo_boosts++;
                }
                if (prob > 1.0f) prob = 1.0f;
                gs->total_couplings++;
                if (rng_float() < prob) {
                    gs->tm_data[site] = gs->tp_data[site];
                    gs->coupling_tp_to_tm++;
                    if (enhance > 1.0f) gs->couple_enhanced++;
                }
            }
        }

        /* T- perspective: always use max-vertex pressure for bulk coupling. */
        float pp_tm = gs->pp_at_tm[site];
        float pm_tm = gs->pm_at_tm[site];
        float sum_tm = pp_tm + pm_tm;
        if (sum_tm > 1e-10f) {
            float delta_tm = pm_tm - pp_tm;
            if (delta_tm > 0) {
                float prob = enhance * w_tm_to_tp *
                    (float)gs->coupling_strength * delta_tm / sum_tm;
                /* Q3c: mass-modulated geometric coupling (Thm 3.1.1) */
                if (gs->mass_geo > 0.0f && gs->mass_tm) {
                    float boost = 1.0f + gs->mass_geo * gs->mass_tm[site];
                    prob *= boost;
                    if (boost > 1.01f) gs->mass_geo_boosts++;
                }
                if (prob > 1.0f) prob = 1.0f;
                gs->total_couplings++;
                if (rng_float() < prob) {
                    gs->tp_data[site] = gs->tm_data[site];
                    gs->coupling_tm_to_tp++;
                    if (enhance > 1.0f) gs->couple_enhanced++;
                }
            }
        }
    }
}

/* ── Mutation ─────────────────────────────────────────────────────── */

static void mutate_surface(uint8_t *data, int count, double rate) {
    for (int i = 0; i < count; i++) {
        if (rng_float() < rate) {
            data[i] = rng_int(3);
        }
    }
}

/* Forward declaration — needed because mutation code calls this before definition */
static void compute_mass_observable(GenesisSoup *gs);

/* ── One Epoch ────────────────────────────────────────────────────── */

static void genesis_epoch(GenesisSoup *gs) {
    int n = gs->mesh_tp.n_sites;

    /* GG1: Take snapshot at epoch start (GPU-like: all reads from frozen state) */
    /* Read sources: snapshot arrays if snapshot_mode, else live arrays */
    uint8_t *read_tp = gs->tp_data;
    uint8_t *read_tm = gs->tm_data;
    float *read_phase_tp = gs->phase_tp;
    float *read_phase_tm = gs->phase_tm;
    if (gs->snapshot_mode) {
        memcpy(gs->snap_tp, gs->tp_data, n * sizeof(uint8_t));
        memcpy(gs->snap_tm, gs->tm_data, n * sizeof(uint8_t));
        memcpy(gs->snap_phase_tp, gs->phase_tp, n * sizeof(float));
        memcpy(gs->snap_phase_tm, gs->phase_tm, n * sizeof(float));
        read_tp = gs->snap_tp;
        read_tm = gs->snap_tm;
        read_phase_tp = gs->snap_phase_tp;
        read_phase_tm = gs->snap_phase_tm;
    }

    /* Precompute mass if any mass coupling channel is active (Q3b/Q3c).
     * Must happen before geometric_couple() and Kuramoto loop. */
    int mass_any_coupling = gs->mass_mode &&
        (gs->mass_kuramoto > 0.0f || gs->mass_geo > 0.0f);
    if (mass_any_coupling)
        compute_mass_observable(gs);

    /* Pick random center site */
    int center = rng_int(n);

    /* Extract BFS patch */
    int count_a = bfs_extract(&gs->mesh_tp, center, gs->prog_size, gs->patch_a);

    /* Copy patch data into work buffers and prepare VM context.
     * In snapshot mode, read from frozen state (GPU semantics). */
    for (int i = 0; i < count_a; i++) {
        int site = gs->patch_a[i];
        gs->visit_hist[site]++;
        gs->work_a[i] = read_tp[site];
        gs->work_b[i] = read_tm[site];

        /* Precompute pressure ratios for SENSE/WRITE instructions */
        if (gs->instr_mode >= INSTR_MODE_ENHANCED) {
            /* T+ surface: own = P+, other = P- (at T+ positions) */
            float sum_tp = gs->pp_at_tp[site] + gs->pm_at_tp[site];
            gs->pressure_ratio_a[i] = sum_tp > 1e-10f ?
                gs->pp_at_tp[site] / sum_tp : 0.5f;
            /* T- surface: own = P-, other = P+ (at T- positions) */
            float sum_tm = gs->pm_at_tm[site] + gs->pp_at_tm[site];
            gs->pressure_ratio_b[i] = sum_tm > 1e-10f ?
                gs->pm_at_tm[site] / sum_tm : 0.5f;

            /* Per-color pressure ratios (Def 0.1.3):
             * Color c (trit value) maps to vertex c+1 in TV arrays.
             * T+ color c: own = P from TV_PLUS[c+1], other = P from TV_MINUS[c+1]
             * T- color c: own = P from TV_MINUS[c+1], other = P from TV_PLUS[c+1] */
            if (gs->color_pressure) {
                float p_plus_scale = 1.0f + (float)gs->chirality;
                for (int c = 0; c < 3; c++) {
                    /* T+ site: per-color pressure */
                    float pp_c = p_plus_scale * pressure_at_site(
                        gs->mesh_tp.pos[site], (const float(*)[3])&TV_PLUS[c+1], 1);
                    float pm_c = pressure_at_site(
                        gs->mesh_tp.pos[site], (const float(*)[3])&TV_MINUS[c+1], 1);
                    /* Use single-vertex pressure: 1/(|x-v|^2 + eps^2) */
                    float dx, dy, dz, r2;
                    dx = gs->mesh_tp.pos[site][0] - TV_PLUS[c+1][0];
                    dy = gs->mesh_tp.pos[site][1] - TV_PLUS[c+1][1];
                    dz = gs->mesh_tp.pos[site][2] - TV_PLUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    pp_c = p_plus_scale / (r2 + gs->epsilon * gs->epsilon);
                    dx = gs->mesh_tp.pos[site][0] - TV_MINUS[c+1][0];
                    dy = gs->mesh_tp.pos[site][1] - TV_MINUS[c+1][1];
                    dz = gs->mesh_tp.pos[site][2] - TV_MINUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    pm_c = 1.0f / (r2 + gs->epsilon * gs->epsilon);
                    float sum_c = pp_c + pm_c;
                    gs->pressure_ratio_color_a[c][i] = sum_c > 1e-10f ?
                        pp_c / sum_c : 0.5f;

                    /* T- site: per-color pressure (T- owns TV_MINUS, opposes TV_PLUS) */
                    dx = gs->mesh_tm.pos[site][0] - TV_MINUS[c+1][0];
                    dy = gs->mesh_tm.pos[site][1] - TV_MINUS[c+1][1];
                    dz = gs->mesh_tm.pos[site][2] - TV_MINUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pm_own = 1.0f / (r2 + gs->epsilon * gs->epsilon);
                    dx = gs->mesh_tm.pos[site][0] - TV_PLUS[c+1][0];
                    dy = gs->mesh_tm.pos[site][1] - TV_PLUS[c+1][1];
                    dz = gs->mesh_tm.pos[site][2] - TV_PLUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pp_opp = p_plus_scale / (r2 + gs->epsilon * gs->epsilon);
                    sum_c = pm_own + pp_opp;
                    gs->pressure_ratio_color_b[c][i] = sum_c > 1e-10f ?
                        pm_own / sum_c : 0.5f;
                }
            }
        }
        gs->couple_flags_a[i] = 0;
        gs->couple_flags_b[i] = 0;
    }

    /* Mode 0 or 2: Execute GenesisVM on each patch independently */
    if (gs->mode != 1) {
        VMContext ctx_a = {
            .pressure_ratio = gs->pressure_ratio_a,
            .pressure_ratio_color = {gs->pressure_ratio_color_a[0],
                                     gs->pressure_ratio_color_a[1],
                                     gs->pressure_ratio_color_a[2]},
            .color_pressure = gs->color_pressure,
            .couple_flags = gs->couple_flags_a,
            .other_tape = gs->work_b,
            .other_tape_len = count_a,
            .instr_mode = gs->instr_mode,
            .sense_count = 0, .couple_count = 0,
            .write_count = 0, .write_blocked = 0
        };
        VMContext ctx_b = {
            .pressure_ratio = gs->pressure_ratio_b,
            .pressure_ratio_color = {gs->pressure_ratio_color_b[0],
                                     gs->pressure_ratio_color_b[1],
                                     gs->pressure_ratio_color_b[2]},
            .color_pressure = gs->color_pressure,
            .couple_flags = gs->couple_flags_b,
            .other_tape = gs->work_a,
            .other_tape_len = count_a,
            .instr_mode = gs->instr_mode,
            .sense_count = 0, .couple_count = 0,
            .write_count = 0, .write_blocked = 0
        };
        /* T+ executes first — WRITE to work_b happens before T- reads it.
         * This sequential order creates a natural chirality: T+ "goes first",
         * consistent with the right-handed pressure convention.
         *
         * GG1 snapshot mode: T- must read the ORIGINAL work_b (before T+'s
         * WRITEs). Save work_b, run T+, then restore work_b for T-'s read
         * while preserving T+'s writes in a separate buffer for merge. */
        if (gs->snapshot_mode) {
            uint8_t save_b[PROG_SIZE];
            memcpy(save_b, gs->work_b, count_a * sizeof(uint8_t));
            genesis_execute(gs->work_a, count_a, gs->max_steps, &ctx_a);
            /* work_b may now contain T+'s WRITEs — save those */
            uint8_t tp_writes_to_b[PROG_SIZE];
            memcpy(tp_writes_to_b, gs->work_b, count_a * sizeof(uint8_t));
            /* Restore original work_b for T-'s execution */
            memcpy(gs->work_b, save_b, count_a * sizeof(uint8_t));
            /* T-'s other_tape (work_a) should also be the snapshot version */
            uint8_t save_a[PROG_SIZE];
            memcpy(save_a, gs->work_a, count_a * sizeof(uint8_t));
            /* Restore original work_a for T-'s read of other_tape */
            for (int si = 0; si < count_a; si++)
                gs->work_a[si] = read_tp[gs->patch_a[si]];
            genesis_execute(gs->work_b, count_a, gs->max_steps, &ctx_b);
            /* Merge: restore T+'s VM result to work_a */
            memcpy(gs->work_a, save_a, count_a * sizeof(uint8_t));
            /* Merge T+'s WRITEs to work_b: where T+ wrote, apply those */
            for (int si = 0; si < count_a; si++) {
                if (tp_writes_to_b[si] != save_b[si])
                    gs->work_b[si] = tp_writes_to_b[si];
            }
        } else {
            genesis_execute(gs->work_a, count_a, gs->max_steps, &ctx_a);
            genesis_execute(gs->work_b, count_a, gs->max_steps, &ctx_b);
        }
        gs->sense_count += ctx_a.sense_count + ctx_b.sense_count;
        gs->couple_count += ctx_a.couple_count + ctx_b.couple_count;
        gs->write_count += ctx_a.write_count + ctx_b.write_count;
        gs->write_blocked += ctx_a.write_blocked + ctx_b.write_blocked;

        /* Record COUPLE geography: map patch-local flags to global site indices
         * (only relevant in ENHANCED mode; WRITE mode doesn't use COUPLE flags) */
        if (gs->instr_mode == INSTR_MODE_ENHANCED) {
            for (int i = 0; i < count_a; i++) {
                int site = gs->patch_a[i];
                if (gs->couple_flags_a[i]) gs->couple_hist_tp[site]++;
                if (gs->couple_flags_b[i]) gs->couple_hist_tm[site]++;
            }
        }
    }

    /* Write back VM results — snap phase only if trit changed, preserving
     * accumulated Kuramoto phase in the blocked zone across visits */
    {
        float third = 2.0f * (float)M_PI / 3.0f;
        for (int i = 0; i < count_a; i++) {
            int site = gs->patch_a[i];
            uint8_t old_tp = gs->tp_data[site];
            uint8_t old_tm = gs->tm_data[site];
            gs->tp_data[site] = gs->work_a[i];
            gs->tm_data[site] = gs->work_b[i];
            if (gs->tp_data[site] != old_tp)
                gs->phase_tp[site] = gs->tp_data[site] * third;
            if (gs->tm_data[site] != old_tm)
                gs->phase_tm[site] = gs->tm_data[site] * third;
        }
    }

    /* Mode 0 or 1: Apply geometric coupling.
     * GG1 snapshot mode: coupling reads source trits from snapshot (read_tp/
     * read_tm) but writes to live arrays. Cannot use pointer swap because
     * geometric_couple both reads and writes the same arrays per site. */
    if (gs->mode != 2) {
        /* Save trits to detect coupling-induced changes */
        uint8_t saved_tp[PROG_SIZE], saved_tm[PROG_SIZE];
        for (int i = 0; i < count_a; i++) {
            saved_tp[i] = gs->tp_data[gs->patch_a[i]];
            saved_tm[i] = gs->tm_data[gs->patch_a[i]];
        }
        if (gs->snapshot_mode) {
            /* Snapshot coupling: read from frozen state, write to live.
             * Each direction is independent — both read from snapshot. */
            float w_tp_to_tm = 1.0f, w_tm_to_tp = 1.0f;
            if (gs->chirality_mode == 1) {
                w_tp_to_tm = 1.0f + (float)gs->chirality;
                w_tm_to_tp = 1.0f - (float)gs->chirality;
                if (w_tm_to_tp < 0.0f) w_tm_to_tp = 0.0f;
            }
            for (int i = 0; i < count_a; i++) {
                int site = gs->patch_a[i];
                float enhance = 1.0f;
                if (gs->instr_mode == INSTR_MODE_ENHANCED) {
                    if (gs->couple_flags_a[i] || gs->couple_flags_b[i])
                        enhance = 2.0f;
                }
                /* T+→T-: read source from snapshot tp */
                float pp_tp = gs->pp_at_tp[site];
                float pm_tp = gs->pm_at_tp[site];
                float sum_tp = pp_tp + pm_tp;
                if (sum_tp > 1e-10f) {
                    float delta_tp = pp_tp - pm_tp;
                    if (delta_tp > 0) {
                        float prob = enhance * w_tp_to_tm *
                            (float)gs->coupling_strength * delta_tp / sum_tp;
                        if (prob > 1.0f) prob = 1.0f;
                        gs->total_couplings++;
                        if (rng_float() < prob) {
                            gs->tm_data[site] = read_tp[site]; /* snapshot source */
                            gs->coupling_tp_to_tm++;
                            if (enhance > 1.0f) gs->couple_enhanced++;
                        }
                    }
                }
                /* T-→T+: read source from snapshot tm */
                float pp_tm = gs->pp_at_tm[site];
                float pm_tm = gs->pm_at_tm[site];
                float sum_tm = pp_tm + pm_tm;
                if (sum_tm > 1e-10f) {
                    float delta_tm = pm_tm - pp_tm;
                    if (delta_tm > 0) {
                        float prob = enhance * w_tm_to_tp *
                            (float)gs->coupling_strength * delta_tm / sum_tm;
                        if (prob > 1.0f) prob = 1.0f;
                        gs->total_couplings++;
                        if (rng_float() < prob) {
                            gs->tp_data[site] = read_tm[site]; /* snapshot source */
                            gs->coupling_tm_to_tp++;
                            if (enhance > 1.0f) gs->couple_enhanced++;
                        }
                    }
                }
            }
        } else {
            geometric_couple(gs, gs->patch_a, count_a);
        }
        /* Snap phase only for sites whose trit was changed by coupling */
        float third = 2.0f * (float)M_PI / 3.0f;
        for (int i = 0; i < count_a; i++) {
            int site = gs->patch_a[i];
            if (gs->tp_data[site] != saved_tp[i])
                gs->phase_tp[site] = gs->tp_data[site] * third;
            if (gs->tm_data[site] != saved_tm[i])
                gs->phase_tm[site] = gs->tm_data[site] * third;
        }
    }

    /* Phase-lock attractor (Thm 2.2.1): neighbor-based coherence,
     * gated by pressure to target the deep-blocked zone.
     *
     * Two modes:
     *   kuramoto_mode=0: Discrete Z₃ majority-vote (original implementation).
     *     Each site flips to its neighbors' majority trit with probability
     *     phase_lock. Simple but misses ties and partial alignment.
     *
     *   kuramoto_mode=1: Full Sakaguchi-Kuramoto continuous-phase dynamics.
     *     Each site has a persistent continuous phase φ ∈ [0, 2π). The
     *     coupling force is sinusoidal: dφ_i = K * mean_j(sin(φ_j - φ_i)).
     *     This faithfully implements Thm 2.2.1's oscillator coupling:
     *       - Sinusoidal force proportional to phase mismatch
     *       - Smooth phase accumulation across epochs (persistent phases)
     *       - Can break ties that majority vote cannot
     *       - Eigenvalue structure: -3K/2 exponential convergence
     *     The trit is quantized from the continuous phase after each update.
     *
     * GATING: Only activates where P_ratio < 0.5 (pressure-blocked zone).
     * Near vertices (P_ratio > 0.5), the inter-tetrahedron coupling already
     * achieves >95% coherence — the phase-lock would compete, not help.
     * In the blocked zone, coupling can't reach, so the phase-lock provides
     * the only coherence channel. */
    if (gs->phase_lock > 0.0f) {
        if (gs->kuramoto_mode == 1) {
            /* Full Kuramoto: continuous-phase sinusoidal coupling (Thm 2.2.1)
             *
             * dφ_i/dλ = (K/N_nbr) * Σ_{j∈nbr(i)} sin(φ_j - φ_i)
             *
             * This is the spatial Kuramoto model with synchronization target 0
             * (neighbors should have the same phase). The Z₃ structure emerges
             * from quantization: trit = round(3φ/(2π)) mod 3.
             *
             * Key advantages over majority vote:
             * 1. Accumulates partial alignment across epochs (persistent phase)
             * 2. Breaks ties: 3-vs-3 split still produces net force via sin()
             * 3. Coupling strength varies smoothly with phase mismatch
             * 4. Faithfully models the Sakaguchi-Kuramoto eigenvalue spectrum
             *
             * GG2b: Sub-iterations for snapshot mode. When kuramoto_sub_steps > 1,
             * we run multiple Kuramoto sweeps per epoch, re-snapshotting the phase
             * arrays between sub-steps. This allows multi-hop phase diffusion
             * within a single epoch under Jacobi semantics, compensating for the
             * 1-hop-per-epoch limitation that degrades coherence at high n_sub. */
            float K_base = gs->phase_lock;
            float TWO_PI = 2.0f * (float)M_PI;
            float THIRD = TWO_PI / 3.0f;
            int n_kur_steps = gs->snapshot_mode ? gs->kuramoto_sub_steps : 1;

            for (int sub = 0; sub < n_kur_steps; sub++) {
                /* GG2b: re-snapshot phase arrays between sub-steps to propagate
                 * intermediate results. Only phase arrays — trits, colors, and
                 * all other state remain on the original epoch snapshot. */
                if (sub > 0 && gs->snapshot_mode) {
                    memcpy(gs->snap_phase_tp, gs->phase_tp, n * sizeof(float));
                    memcpy(gs->snap_phase_tm, gs->phase_tm, n * sizeof(float));
                }

            for (int i = 0; i < count_a; i++) {
                int site = gs->patch_a[i];

                /* T+ surface: only in blocked zone (P_ratio < 0.5) */
                float sum_tp = gs->pp_at_tp[site] + gs->pm_at_tp[site];
                float pr_tp = sum_tp > 1e-10f ?
                    gs->pp_at_tp[site] / sum_tp : 0.5f;
                if (pr_tp < 0.5f) {
                    int nn = gs->mesh_tp.n_nbr[site];
                    if (nn > 0) {
                        float force = 0.0f;
                        for (int j = 0; j < nn; j++) {
                            int nb = gs->mesh_tp.nbr[site][j];
                            /* GG1: read neighbor phase from snapshot in
                             * snapshot mode (Jacobi update), else live
                             * (Gauss-Seidel update) */
                            force += sinf(read_phase_tp[nb] - read_phase_tp[site]);
                        }
                        /* Q3b: mass-modulated Kuramoto coupling (Thm 3.1.1) */
                        float K = K_base;
                        if (gs->mass_kuramoto > 0.0f && gs->mass_tp) {
                            K *= (1.0f + gs->mass_kuramoto * gs->mass_tp[site]);
                            if (gs->mass_tp[site] > 0.01f)
                                gs->mass_kuramoto_boosts++;
                        }
                        float dphi = K * force / nn;
                        gs->phase_tp[site] = read_phase_tp[site] + dphi;
                        /* Wrap to [0, 2π) */
                        gs->phase_tp[site] = fmodf(gs->phase_tp[site], TWO_PI);
                        if (gs->phase_tp[site] < 0.0f)
                            gs->phase_tp[site] += TWO_PI;
                        /* Quantize to nearest Z₃ trit */
                        int new_trit = ((int)roundf(gs->phase_tp[site] / THIRD)) % 3;
                        if (new_trit != gs->tp_data[site]) {
                            gs->tp_data[site] = new_trit;
                            gs->phase_lock_events++;
                        }
                    }
                }

                /* T- surface: only in blocked zone (P_ratio < 0.5) */
                float sum_tm = gs->pm_at_tm[site] + gs->pp_at_tm[site];
                float pr_tm = sum_tm > 1e-10f ?
                    gs->pm_at_tm[site] / sum_tm : 0.5f;
                if (pr_tm < 0.5f) {
                    int nn = gs->mesh_tm.n_nbr[site];
                    if (nn > 0) {
                        float force = 0.0f;
                        for (int j = 0; j < nn; j++) {
                            int nb = gs->mesh_tm.nbr[site][j];
                            /* GG1: snapshot read for neighbor phases */
                            force += sinf(read_phase_tm[nb] - read_phase_tm[site]);
                        }
                        /* Q3b: mass-modulated Kuramoto coupling (Thm 3.1.1) */
                        float K_tm = K_base;
                        if (gs->mass_kuramoto > 0.0f && gs->mass_tm) {
                            K_tm *= (1.0f + gs->mass_kuramoto * gs->mass_tm[site]);
                            if (gs->mass_tm[site] > 0.01f)
                                gs->mass_kuramoto_boosts++;
                        }
                        float dphi = K_tm * force / nn;
                        gs->phase_tm[site] = read_phase_tm[site] + dphi;
                        /* Wrap to [0, 2π) */
                        gs->phase_tm[site] = fmodf(gs->phase_tm[site], TWO_PI);
                        if (gs->phase_tm[site] < 0.0f)
                            gs->phase_tm[site] += TWO_PI;
                        /* Quantize to nearest Z₃ trit */
                        int new_trit = ((int)roundf(gs->phase_tm[site] / THIRD)) % 3;
                        if (new_trit != gs->tm_data[site]) {
                            gs->tm_data[site] = new_trit;
                            gs->phase_lock_events++;
                        }
                    }
                }
            }
            } /* end sub-step loop */
        } else {
            /* Discrete Z₃ majority-vote (original implementation)
             * GG1: In snapshot mode, neighbor trit reads use snapshot. */
            for (int i = 0; i < count_a; i++) {
                int site = gs->patch_a[i];
                /* T+ surface: only in blocked zone (P_ratio < 0.5) */
                float sum_tp = gs->pp_at_tp[site] + gs->pm_at_tp[site];
                float pr_tp = sum_tp > 1e-10f ?
                    gs->pp_at_tp[site] / sum_tp : 0.5f;
                if (pr_tp < 0.5f) {
                    int counts[3] = {0, 0, 0};
                    for (int j = 0; j < gs->mesh_tp.n_nbr[site]; j++)
                        counts[read_tp[gs->mesh_tp.nbr[site][j]]]++;
                    int majority = 0;
                    if (counts[1] > counts[majority]) majority = 1;
                    if (counts[2] > counts[majority]) majority = 2;
                    if (read_tp[site] != majority &&
                        counts[majority] > counts[read_tp[site]] &&
                        rng_float() < gs->phase_lock) {
                        gs->tp_data[site] = majority;
                        gs->phase_lock_events++;
                    }
                }
                /* T- surface: only in blocked zone (P_ratio < 0.5) */
                float sum_tm = gs->pm_at_tm[site] + gs->pp_at_tm[site];
                float pr_tm = sum_tm > 1e-10f ?
                    gs->pm_at_tm[site] / sum_tm : 0.5f;
                if (pr_tm < 0.5f) {
                    int counts[3] = {0, 0, 0};
                    for (int j = 0; j < gs->mesh_tm.n_nbr[site]; j++)
                        counts[read_tm[gs->mesh_tm.nbr[site][j]]]++;
                    int majority = 0;
                    if (counts[1] > counts[majority]) majority = 1;
                    if (counts[2] > counts[majority]) majority = 2;
                    if (read_tm[site] != majority &&
                        counts[majority] > counts[read_tm[site]] &&
                        rng_float() < gs->phase_lock) {
                        gs->tm_data[site] = majority;
                        gs->phase_lock_events++;
                    }
                }
            }
        }
    }

    /* Pre-geometric energy functional (Thm 0.2.4):
     * E[χ] = Σ|a_c|² + λ(|χ_total|² - v₀²)² where
     * χ_total = Σ_c a_c·e^{iφ_c} with φ = {0, 2π/3, 4π/3}.
     *
     * The amplitudes a_c are the GLOBAL color fractions across both surfaces.
     * When |a_R|=|a_G|=|a_B|=1/3, |χ_total|² = 0 (minimum).
     *
     * Two-pronged implementation:
     * 1. PAIRED FLIPS: sites where both T+ and T- share the overrepresented
     *    color are flipped together to the underrepresented color. This
     *    preserves T+↔T- correlation while rebalancing.
     * 2. MUTATION BIAS: when mutations occur, they preferentially choose
     *    the underrepresented color.
     *
     * Both use probability λ·|χ|² (self-regulating: no action when balanced). */
    int energy_under_c = -1;
    int energy_over_c = -1;
    float energy_bias_prob = 0.0f;
    if (gs->energy_lambda > 0.0f) {
        int ntot = gs->mesh_tp.n_sites;
        float third = 2.0f * (float)M_PI / 3.0f;

        /* Count combined (T+ + T-) colors.
         * GG1: In snapshot mode, count from frozen state so all sites
         * in this epoch see the same over/under-represented colors. */
        int gcomb[3] = {0, 0, 0};
        for (int i = 0; i < ntot; i++) {
            gcomb[read_tp[i]]++;
            gcomb[read_tm[i]]++;
        }

        /* Compute combined |χ|² */
        float fc[3];
        int total_sites = 2 * ntot;
        for (int c = 0; c < 3; c++)
            fc[c] = (float)gcomb[c] / total_sites;
        float re = fc[0] - 0.5f*fc[1] - 0.5f*fc[2];
        float im = 0.866025403784f * (fc[1] - fc[2]);
        float chi2 = re*re + im*im;

        /* Find over/under-represented colors */
        int over_c = 0, under_c = 0;
        for (int c = 1; c < 3; c++) {
            if (gcomb[c] > gcomb[over_c]) over_c = c;
            if (gcomb[c] < gcomb[under_c]) under_c = c;
        }

        energy_over_c = over_c;
        energy_under_c = under_c;
        energy_bias_prob = gs->energy_lambda * chi2;
        if (energy_bias_prob > 1.0f) energy_bias_prob = 1.0f;

        /* Paired flips: flip co-located overrepresented sites together */
        if (over_c != under_c) {
            for (int i = 0; i < count_a; i++) {
                int site = gs->patch_a[i];
                if (gs->tp_data[site] == over_c &&
                    gs->tm_data[site] == over_c) {
                    if (rng_float() < energy_bias_prob) {
                        gs->tp_data[site] = under_c;
                        gs->tm_data[site] = under_c;
                        gs->phase_tp[site] = under_c * third;
                        gs->phase_tm[site] = under_c * third;
                        gs->energy_flips++;
                    }
                }
            }
        }
    }

    /* Mutation on both surfaces — snap phases after mutation.
     * Energy functional (Thm 0.2.4): when energy_lambda > 0, mutations
     * are biased toward the underrepresented color.
     * Mass coupling (Thm 3.1.1, Q3): when mass_couple > 0, higher local
     * mass density reduces mutation probability: μ_eff = μ / (1 + mc·m(x)).
     * Physical interpretation: massive regions resist change (inertia). */
    {
        float third = 2.0f * (float)M_PI / 3.0f;
        /* Precompute mass if mass coupling is active (skip if already done for Q3b/Q3c) */
        int mass_active = gs->mass_couple > 0.0f && gs->mass_mode;
        if (mass_active && !mass_any_coupling)
            compute_mass_observable(gs);
        for (int i = 0; i < count_a; i++) {
            int site = gs->patch_a[i];
            /* T+ mutation */
            float mu_tp = (float)gs->mutation_rate;
            if (mass_active) {
                mu_tp /= (1.0f + gs->mass_couple * gs->mass_tp[site]);
            }
            if (rng_float() < mu_tp) {
                if (energy_under_c >= 0 && rng_float() < energy_bias_prob) {
                    gs->tp_data[site] = energy_under_c;
                    gs->energy_flips++;
                } else {
                    gs->tp_data[site] = rng_int(3);
                }
                gs->phase_tp[site] = gs->tp_data[site] * third;
            } else if (mass_active && rng_float() < (float)gs->mutation_rate) {
                /* Would have mutated but was blocked by mass inertia */
                gs->mass_couple_blocks++;
            }
            /* T- mutation */
            float mu_tm = (float)gs->mutation_rate;
            if (mass_active) {
                mu_tm /= (1.0f + gs->mass_couple * gs->mass_tm[site]);
            }
            if (rng_float() < mu_tm) {
                if (energy_under_c >= 0 && rng_float() < energy_bias_prob) {
                    gs->tm_data[site] = energy_under_c;
                    gs->energy_flips++;
                } else {
                    gs->tm_data[site] = rng_int(3);
                }
                gs->phase_tm[site] = gs->tm_data[site] * third;
            } else if (mass_active && rng_float() < (float)gs->mutation_rate) {
                gs->mass_couple_blocks++;
            }
        }
    }

    gs->epoch++;
}

/* ── Diagnostics ──────────────────────────────────────────────────── */

static void compute_entropy(const uint8_t *data, int n, float *entropy,
                            int counts[3]) {
    counts[0] = counts[1] = counts[2] = 0;
    for (int i = 0; i < n; i++) counts[data[i]]++;

    *entropy = 0.0f;
    for (int j = 0; j < 3; j++) {
        if (counts[j] > 0) {
            float p = (float)counts[j] / n;
            *entropy -= p * log2f(p);
        }
    }
}

static float compute_tp_tm_correlation(GenesisSoup *gs) {
    /* Fraction of co-located sites with matching trits */
    int n = gs->mesh_tp.n_sites;
    int match = 0;
    for (int i = 0; i < n; i++) {
        if (gs->tp_data[i] == gs->tm_data[i]) match++;
    }
    return (float)match / n;
}

static float compute_spatial_autocorrelation(const uint8_t *data,
                                              const Mesh *m) {
    /* Average trit agreement between neighbors (0.333 = random) */
    int n = m->n_sites;
    int agree = 0, total = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < m->n_nbr[i]; j++) {
            if (data[i] == data[m->nbr[i][j]]) agree++;
            total++;
        }
    }
    return total > 0 ? (float)agree / total : 0.333f;
}

/* Count how many sites on T- match T+ in a local BFS patch
 * (proxy for "replication" — geometric coupling copying patterns) */
static float compute_local_replication_density(GenesisSoup *gs) {
    int n = gs->mesh_tp.n_sites;
    int samples = 100;
    int total_match = 0, total_sites = 0;

    for (int s = 0; s < samples; s++) {
        int center = rng_int(n);
        int patch[PROG_SIZE];
        int count = bfs_extract(&gs->mesh_tp, center, gs->prog_size, patch);

        int match = 0;
        for (int i = 0; i < count; i++) {
            if (gs->tp_data[patch[i]] == gs->tm_data[patch[i]]) match++;
        }
        total_match += match;
        total_sites += count;
    }
    return total_sites > 0 ? (float)total_match / total_sites : 0.333f;
}

/* Directional bias: net fraction of coupling events that went T+→T- */
static float compute_directional_bias(GenesisSoup *gs) {
    long total = gs->coupling_tp_to_tm + gs->coupling_tm_to_tp;
    if (total == 0) return 0.5f;
    return (float)gs->coupling_tp_to_tm / total;
}

/* ── Phase-Gradient Mass Observable (Thm 3.1.1) ──────────────────── */

/* Physical constants (natural units, from R_stella = 0.44847 fm)
 * ω₀ = √σ/(N_c - 1) = 440/2 = 220 MeV   — Prop 0.0.17l
 * v_χ = √σ/5 = 88.0 MeV                   — Prop 0.0.17m
 * Λ  = 4πf_π = 4π·88.0 = 1106 MeV         — Prop 0.0.17d
 * g_χ = 4π/9 ≈ 1.3963                      — Prop 3.1.1c
 *
 * Prefactor: g_χ·ω₀/Λ = 1.3963·220/1106 ≈ 0.2778 (dimensionless on lattice)
 *
 * On the lattice we measure dimensionless ratios; the mass density is:
 *   m(x) = prefactor · v_chi_norm(x) · |∇φ(x)|
 * where v_chi_norm(x) ∈ [0,1] and |∇φ| is in radians/edge_length. */

#define MASS_PREFACTOR  (4.0f * (float)M_PI / 9.0f * 220.0f / 1106.0f)
/* = g_χ · ω₀/Λ ≈ 0.2778 */

static void compute_phase_gradient(const float *phase, const Mesh *m,
                                   float *grad_mag) {
    /* Compute |∇φ| per site via finite differences on mesh neighbors.
     * For each site i, gradient ≈ (1/N) Σ_{j∈nbr} |φ_j - φ_i| (mod π wrap).
     * We use the circular distance: min(|Δφ|, 2π - |Δφ|) */
    int n = m->n_sites;
    float TWO_PI = 2.0f * (float)M_PI;
    for (int i = 0; i < n; i++) {
        int nn = m->n_nbr[i];
        if (nn == 0) { grad_mag[i] = 0.0f; continue; }
        float sum = 0.0f;
        for (int j = 0; j < nn; j++) {
            int nb = m->nbr[i][j];
            float diff = fabsf(phase[nb] - phase[i]);
            if (diff > (float)M_PI) diff = TWO_PI - diff;
            /* Weight by inverse edge length for proper gradient scaling */
            float dx = m->pos[nb][0] - m->pos[i][0];
            float dy = m->pos[nb][1] - m->pos[i][1];
            float dz = m->pos[nb][2] - m->pos[i][2];
            float edge_len = sqrtf(dx*dx + dy*dy + dz*dz);
            if (edge_len > 1e-8f)
                sum += diff / edge_len;
            else
                sum += diff;
        }
        grad_mag[i] = sum / nn;
    }
}

static void compute_vchi_field(GenesisSoup *gs) {
    /* v_χ(x) = pressure-modulated VEV (Thm 3.0.1)
     * Normalized to [0,1]: v_chi_norm(x) = P_dominant(x) / (P_+(x) + P_-(x))
     *
     * At T+ sites, the "own" pressure P_+(x) measures how strongly the
     * chiral field is anchored. At T- sites, P_-(x) plays the same role.
     * Regions with high own-pressure → strong VEV → larger mass density. */
    int n = gs->mesh_tp.n_sites;
    for (int i = 0; i < n; i++) {
        float sum_tp = gs->pp_at_tp[i] + gs->pm_at_tp[i];
        gs->vchi_tp[i] = sum_tp > 1e-10f ?
            gs->pp_at_tp[i] / sum_tp : 0.5f;

        float sum_tm = gs->pp_at_tm[i] + gs->pm_at_tm[i];
        gs->vchi_tm[i] = sum_tm > 1e-10f ?
            gs->pm_at_tm[i] / sum_tm : 0.5f;
    }
}

static void compute_mass_observable(GenesisSoup *gs) {
    /* Compute per-site mass density: m(x) = prefactor · v_χ(x) · |∇φ(x)|
     * This is the discretized version of Thm 3.1.1 on the mesh. */
    int n = gs->mesh_tp.n_sites;

    /* Step 1: phase gradients */
    compute_phase_gradient(gs->phase_tp, &gs->mesh_tp, gs->grad_phi_tp);
    compute_phase_gradient(gs->phase_tm, &gs->mesh_tm, gs->grad_phi_tm);

    /* Step 2: VEV field (static — only recomputed if pressure changes) */
    compute_vchi_field(gs);

    /* Step 3: mass density */
    for (int i = 0; i < n; i++) {
        gs->mass_tp[i] = MASS_PREFACTOR * gs->vchi_tp[i] * gs->grad_phi_tp[i];
        gs->mass_tm[i] = MASS_PREFACTOR * gs->vchi_tm[i] * gs->grad_phi_tm[i];
    }
}

static void print_mass_diagnostics(GenesisSoup *gs) {
    int n = gs->mesh_tp.n_sites;
    compute_mass_observable(gs);

    /* Aggregate statistics */
    float sum_m = 0.0f, sum_m2 = 0.0f;
    float sum_grad = 0.0f, max_m = 0.0f;
    float sum_vchi = 0.0f;
    for (int i = 0; i < n; i++) {
        float m_tp = gs->mass_tp[i];
        float m_tm = gs->mass_tm[i];
        sum_m += m_tp + m_tm;
        sum_m2 += m_tp*m_tp + m_tm*m_tm;
        sum_grad += gs->grad_phi_tp[i] + gs->grad_phi_tm[i];
        sum_vchi += gs->vchi_tp[i] + gs->vchi_tm[i];
        if (m_tp > max_m) max_m = m_tp;
        if (m_tm > max_m) max_m = m_tm;
    }
    float mean_m = sum_m / (2 * n);
    float var_m = sum_m2 / (2 * n) - mean_m * mean_m;
    float std_m = var_m > 0.0f ? sqrtf(var_m) : 0.0f;
    float mean_grad = sum_grad / (2 * n);
    float mean_vchi = sum_vchi / (2 * n);

    /* Spatial mass correlation: do neighbors have similar mass? */
    float mass_autocorr_num = 0.0f;
    int mass_autocorr_den = 0;
    for (int i = 0; i < n; i++) {
        for (int j = 0; j < gs->mesh_tp.n_nbr[i]; j++) {
            int nb = gs->mesh_tp.nbr[i][j];
            mass_autocorr_num += gs->mass_tp[i] * gs->mass_tp[nb];
            mass_autocorr_den++;
        }
    }
    float mass_autocorr = mass_autocorr_den > 0 ?
        mass_autocorr_num / mass_autocorr_den : 0.0f;
    /* Normalize: autocorr / mean² gives correlation ratio (>1 = clustered) */
    float corr_ratio = (mean_m > 1e-10f) ?
        mass_autocorr / (mean_m * mean_m) : 0.0f;

    printf("  mass: mean=%.6f std=%.6f max=%.6f "
           "|grad_phi|=%.4f v_chi=%.4f corr_ratio=%.3f\n",
           mean_m, std_m, max_m, mean_grad, mean_vchi, corr_ratio);
}

static void dump_mass_geography(GenesisSoup *gs, const char *filename) {
    /* JSON dump of per-site mass data for topology analysis (Q2) */
    compute_mass_observable(gs);
    int n = gs->mesh_tp.n_sites;
    FILE *f = fopen(filename, "w");
    if (!f) { fprintf(stderr, "Cannot open %s\n", filename); return; }

    fprintf(f, "{\n  \"n_sites\": %d,\n  \"epoch\": %ld,\n", n, gs->epoch);

    /* Per-site arrays */
    const char *arrays[][2] = {
        {"mass_tp", NULL}, {"mass_tm", NULL},
        {"grad_phi_tp", NULL}, {"grad_phi_tm", NULL},
        {"vchi_tp", NULL}, {"vchi_tm", NULL},
        {NULL, NULL}
    };
    float *ptrs[] = {gs->mass_tp, gs->mass_tm, gs->grad_phi_tp,
                     gs->grad_phi_tm, gs->vchi_tp, gs->vchi_tm};
    for (int a = 0; arrays[a][0]; a++) {
        fprintf(f, "  \"%s\": [", arrays[a][0]);
        for (int i = 0; i < n; i++)
            fprintf(f, "%s%.6f", i ? "," : "", ptrs[a][i]);
        fprintf(f, "],\n");
    }

    /* Pressure ratios */
    fprintf(f, "  \"p_ratio_tp\": [");
    for (int i = 0; i < n; i++) {
        float sum = gs->pp_at_tp[i] + gs->pm_at_tp[i];
        float ratio = sum > 1e-10f ? gs->pp_at_tp[i] / sum : 0.5f;
        fprintf(f, "%s%.6f", i ? "," : "", ratio);
    }
    fprintf(f, "],\n");

    fprintf(f, "  \"p_ratio_tm\": [");
    for (int i = 0; i < n; i++) {
        float sum = gs->pm_at_tm[i] + gs->pp_at_tm[i];
        float ratio = sum > 1e-10f ? gs->pm_at_tm[i] / sum : 0.5f;
        fprintf(f, "%s%.6f", i ? "," : "", ratio);
    }
    fprintf(f, "],\n");

    /* Distance to nearest own vertex */
    fprintf(f, "  \"dist_vertex_tp\": [");
    for (int i = 0; i < n; i++) {
        float mind = 1e10f;
        for (int v = 0; v < 4; v++) {
            float dx = gs->mesh_tp.pos[i][0] - TV_PLUS[v][0];
            float dy = gs->mesh_tp.pos[i][1] - TV_PLUS[v][1];
            float dz = gs->mesh_tp.pos[i][2] - TV_PLUS[v][2];
            float d = sqrtf(dx*dx + dy*dy + dz*dz);
            if (d < mind) mind = d;
        }
        fprintf(f, "%s%.6f", i ? "," : "", mind);
    }
    fprintf(f, "],\n");

    fprintf(f, "  \"dist_vertex_tm\": [");
    for (int i = 0; i < n; i++) {
        float mind = 1e10f;
        for (int v = 0; v < 4; v++) {
            float dx = gs->mesh_tm.pos[i][0] - TV_MINUS[v][0];
            float dy = gs->mesh_tm.pos[i][1] - TV_MINUS[v][1];
            float dz = gs->mesh_tm.pos[i][2] - TV_MINUS[v][2];
            float d = sqrtf(dx*dx + dy*dy + dz*dz);
            if (d < mind) mind = d;
        }
        fprintf(f, "%s%.6f", i ? "," : "", mind);
    }
    fprintf(f, "],\n");

    /* Positions */
    fprintf(f, "  \"tp_pos\": [");
    for (int i = 0; i < n; i++)
        fprintf(f, "%s[%.4f,%.4f,%.4f]", i ? "," : "",
                gs->mesh_tp.pos[i][0], gs->mesh_tp.pos[i][1], gs->mesh_tp.pos[i][2]);
    fprintf(f, "],\n");

    fprintf(f, "  \"tm_pos\": [");
    for (int i = 0; i < n; i++)
        fprintf(f, "%s[%.4f,%.4f,%.4f]", i ? "," : "",
                gs->mesh_tm.pos[i][0], gs->mesh_tm.pos[i][1], gs->mesh_tm.pos[i][2]);
    fprintf(f, "],\n");

    /* Vertex references */
    fprintf(f, "  \"tv_plus\": [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],\n");
    fprintf(f, "  \"tv_minus\": [[-1,-1,-1],[-1,1,1],[1,-1,1],[1,1,-1]]\n");
    fprintf(f, "}\n");
    fclose(f);
    printf("Mass geography dumped to %s\n", filename);
}

static void print_diagnostics(GenesisSoup *gs) {
    int n = gs->mesh_tp.n_sites;
    float ent_tp, ent_tm;
    int counts_tp[3], counts_tm[3];

    compute_entropy(gs->tp_data, n, &ent_tp, counts_tp);
    compute_entropy(gs->tm_data, n, &ent_tm, counts_tm);

    float corr = compute_tp_tm_correlation(gs);
    float autocorr_tp = compute_spatial_autocorrelation(gs->tp_data, &gs->mesh_tp);
    float autocorr_tm = compute_spatial_autocorrelation(gs->tm_data, &gs->mesh_tm);
    float local_repl = compute_local_replication_density(gs);
    float dir_bias = compute_directional_bias(gs);

    /* Compute combined |χ|² — coherent field intensity (Thm 0.2.4)
     * 0 = perfectly balanced (|a_R|=|a_G|=|a_B|), max ~1 = mono-color */
    float fc[3];
    for (int c = 0; c < 3; c++)
        fc[c] = (float)(counts_tp[c] + counts_tm[c]) / (2 * n);
    float chi_re = fc[0] - 0.5f*fc[1] - 0.5f*fc[2];
    float chi_im = 0.866025403784f * (fc[1] - fc[2]);
    float chi2 = chi_re*chi_re + chi_im*chi_im;

    printf("epoch=%ld  "
           "H_tp=%.4f H_tm=%.4f  "
           "corr=%.4f  "
           "chi2=%.4f  "
           "auto_tp=%.4f auto_tm=%.4f  "
           "local_repl=%.4f  "
           "dir_bias=%.4f  "
           "tp_counts=[%d,%d,%d] tm_counts=[%d,%d,%d]  "
           "couplings_tp_tm=%ld tm_tp=%ld\n",
           gs->epoch,
           ent_tp, ent_tm,
           corr,
           chi2,
           autocorr_tp, autocorr_tm,
           local_repl,
           dir_bias,
           counts_tp[0], counts_tp[1], counts_tp[2],
           counts_tm[0], counts_tm[1], counts_tm[2],
           gs->coupling_tp_to_tm, gs->coupling_tm_to_tp);

    /* Thm 3.1.1 mass observable */
    if (gs->mass_mode)
        print_mass_diagnostics(gs);
}

/* ── Pressure landscape diagnostics ──────────────────────────────── */

static void print_pressure_landscape(GenesisSoup *gs) {
    int n = gs->mesh_tp.n_sites;

    /* Show pressure at T+ surface positions */
    float min_delta_tp = 1e10, max_delta_tp = -1e10;
    float min_delta_tm = 1e10, max_delta_tm = -1e10;
    int tp_dom_at_tp = 0, tm_dom_at_tp = 0;
    int tp_dom_at_tm = 0, tm_dom_at_tm = 0;

    for (int i = 0; i < n; i++) {
        float d_tp = gs->pp_at_tp[i] - gs->pm_at_tp[i];
        float d_tm = gs->pm_at_tm[i] - gs->pp_at_tm[i];
        if (d_tp < min_delta_tp) min_delta_tp = d_tp;
        if (d_tp > max_delta_tp) max_delta_tp = d_tp;
        if (d_tm < min_delta_tm) min_delta_tm = d_tm;
        if (d_tm > max_delta_tm) max_delta_tm = d_tm;
        if (d_tp > 0) tp_dom_at_tp++; else tm_dom_at_tp++;
        if (d_tm > 0) tm_dom_at_tm++; else tp_dom_at_tm++;
    }

    printf("\n=== Pressure Landscape (dual-mesh) ===\n");
    printf("At T+ sites: P+-P- delta range [%.4f, %.4f], "
           "T+ dominant=%d, T- dominant=%d\n",
           min_delta_tp, max_delta_tp, tp_dom_at_tp, tm_dom_at_tp);
    printf("At T- sites: P--P+ delta range [%.4f, %.4f], "
           "T- dominant=%d, T+ dominant=%d\n",
           min_delta_tm, max_delta_tm, tm_dom_at_tm, tp_dom_at_tm);
    printf("Symmetry check: T+ dom at T+ = %d, T- dom at T- = %d "
           "(should be equal)\n", tp_dom_at_tp, tm_dom_at_tm);
    printf("======================================\n\n");
}

/* ── COUPLE geography timeline (periodic snapshots) ───────────────── */

#define MAX_SNAPSHOTS 200

typedef struct {
    long epoch;
    long *couple_hist_tp;  /* cumulative at this epoch */
    long *couple_hist_tm;
    long *visit_hist;
    int n_sites;
} CoupleSnapshot;

static CoupleSnapshot snapshots[MAX_SNAPSHOTS];
static int n_snapshots = 0;

static void take_couple_snapshot(GenesisSoup *gs) {
    if (n_snapshots >= MAX_SNAPSHOTS) return;
    int n = gs->mesh_tp.n_sites;
    CoupleSnapshot *s = &snapshots[n_snapshots++];
    s->epoch = gs->epoch;
    s->n_sites = n;
    s->couple_hist_tp = malloc(n * sizeof(long));
    s->couple_hist_tm = malloc(n * sizeof(long));
    s->visit_hist = malloc(n * sizeof(long));
    memcpy(s->couple_hist_tp, gs->couple_hist_tp, n * sizeof(long));
    memcpy(s->couple_hist_tm, gs->couple_hist_tm, n * sizeof(long));
    memcpy(s->visit_hist, gs->visit_hist, n * sizeof(long));
}

static void dump_couple_timeline(GenesisSoup *gs, const char *filename) {
    FILE *f = fopen(filename, "w");
    if (!f) { fprintf(stderr, "Cannot open %s\n", filename); return; }
    int n = gs->mesh_tp.n_sites;

    fprintf(f, "{\n");
    fprintf(f, "  \"n_sites\": %d,\n", n);
    fprintf(f, "  \"n_snapshots\": %d,\n", n_snapshots);

    /* Static geometry (same for all frames) */
    fprintf(f, "  \"tp_pos\": [");
    for (int i = 0; i < n; i++)
        fprintf(f, "%s[%.4f,%.4f,%.4f]", i ? "," : "",
                gs->mesh_tp.pos[i][0], gs->mesh_tp.pos[i][1], gs->mesh_tp.pos[i][2]);
    fprintf(f, "],\n");

    fprintf(f, "  \"tm_pos\": [");
    for (int i = 0; i < n; i++)
        fprintf(f, "%s[%.4f,%.4f,%.4f]", i ? "," : "",
                gs->mesh_tm.pos[i][0], gs->mesh_tm.pos[i][1], gs->mesh_tm.pos[i][2]);
    fprintf(f, "],\n");

    fprintf(f, "  \"pp_at_tp\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.4f", i ? "," : "", gs->pp_at_tp[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pm_at_tp\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.4f", i ? "," : "", gs->pm_at_tp[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pp_at_tm\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.4f", i ? "," : "", gs->pp_at_tm[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pm_at_tm\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.4f", i ? "," : "", gs->pm_at_tm[i]);
    fprintf(f, "],\n");

    fprintf(f, "  \"tv_plus\": [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],\n");
    fprintf(f, "  \"tv_minus\": [[-1,-1,-1],[-1,1,1],[1,-1,1],[1,1,-1]],\n");

    /* Snapshots array */
    fprintf(f, "  \"snapshots\": [\n");
    for (int s = 0; s < n_snapshots; s++) {
        CoupleSnapshot *snap = &snapshots[s];
        fprintf(f, "    {\"epoch\": %ld, \"ct\": [", snap->epoch);
        for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", snap->couple_hist_tp[i]);
        fprintf(f, "], \"cm\": [");
        for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", snap->couple_hist_tm[i]);
        fprintf(f, "], \"v\": [");
        for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", snap->visit_hist[i]);
        fprintf(f, "]}%s\n", s < n_snapshots - 1 ? "," : "");
    }
    fprintf(f, "  ]\n");
    fprintf(f, "}\n");
    fclose(f);
    printf("COUPLE timeline (%d snapshots) dumped to %s\n", n_snapshots, filename);

    /* Free snapshot memory */
    for (int s = 0; s < n_snapshots; s++) {
        free(snapshots[s].couple_hist_tp);
        free(snapshots[s].couple_hist_tm);
        free(snapshots[s].visit_hist);
    }
}

/* ── COUPLE geography dump ────────────────────────────────────────── */

static void dump_couple_geography(GenesisSoup *gs, const char *filename) {
    FILE *f = fopen(filename, "w");
    if (!f) { fprintf(stderr, "Cannot open %s\n", filename); return; }
    int n = gs->mesh_tp.n_sites;

    fprintf(f, "{\n");
    fprintf(f, "  \"n_sites\": %d,\n", n);
    fprintf(f, "  \"total_epochs\": %ld,\n", gs->epoch);

    /* Site coordinates (T+ mesh) */
    fprintf(f, "  \"tp_pos\": [");
    for (int i = 0; i < n; i++) {
        fprintf(f, "%s[%.6f,%.6f,%.6f]", i ? "," : "",
                gs->mesh_tp.pos[i][0], gs->mesh_tp.pos[i][1],
                gs->mesh_tp.pos[i][2]);
    }
    fprintf(f, "],\n");

    /* Site coordinates (T- mesh) */
    fprintf(f, "  \"tm_pos\": [");
    for (int i = 0; i < n; i++) {
        fprintf(f, "%s[%.6f,%.6f,%.6f]", i ? "," : "",
                gs->mesh_tm.pos[i][0], gs->mesh_tm.pos[i][1],
                gs->mesh_tm.pos[i][2]);
    }
    fprintf(f, "],\n");

    /* Pressure arrays */
    fprintf(f, "  \"pp_at_tp\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.6f", i ? "," : "", gs->pp_at_tp[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pm_at_tp\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.6f", i ? "," : "", gs->pm_at_tp[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pp_at_tm\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.6f", i ? "," : "", gs->pp_at_tm[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"pm_at_tm\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%.6f", i ? "," : "", gs->pm_at_tm[i]);
    fprintf(f, "],\n");

    /* Histograms */
    fprintf(f, "  \"couple_hist_tp\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", gs->couple_hist_tp[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"couple_hist_tm\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", gs->couple_hist_tm[i]);
    fprintf(f, "],\n");
    fprintf(f, "  \"visit_hist\": [");
    for (int i = 0; i < n; i++) fprintf(f, "%s%ld", i ? "," : "", gs->visit_hist[i]);
    fprintf(f, "],\n");

    /* Vertex coordinates for reference */
    fprintf(f, "  \"tv_plus\": [[1,1,1],[1,-1,-1],[-1,1,-1],[-1,-1,1]],\n");
    fprintf(f, "  \"tv_minus\": [[-1,-1,-1],[-1,1,1],[1,-1,1],[1,1,-1]]\n");
    fprintf(f, "}\n");
    fclose(f);
    printf("COUPLE geography dumped to %s\n", filename);
}

/* ── Main ─────────────────────────────────────────────────────────── */

int main(int argc, char **argv) {
    long total_epochs = 5000000;
    uint32_t seed = 42;
    double coupling_strength = 0.5;
    int mode = 0;
    int n_sub = 16;
    double mutation_rate = 0.001;
    float epsilon = 0.1f;
    long report_interval = 100000;
    double chirality = 0.0;
    int chirality_mode = 0;
    int instr_mode = 0;  /* 0=classic (NOP), 1=enhanced (SENSE/COUPLE) */
    float warp_alpha = 1.0f;  /* mesh warping: 1.0=uniform, <1=adaptive */
    int color_pressure = 0;   /* 0=max-vertex, 1=per-color (Def 0.1.3) */
    float phase_lock = 0.0f;  /* Thm 2.2.1: phase-lock nudge probability */
    int kuramoto_mode = 0;    /* 0=majority-vote, 1=full Kuramoto */
    float energy_lambda = 0.0f; /* Thm 0.2.4: energy functional coupling */
    int mass_mode = 0;           /* Thm 3.1.1: 0=off, 1=measure mass observable */
    float mass_couple = 0.0f;    /* Thm 3.1.1 Q3: mass-stabilized mutation strength */
    int snapshot_mode = 0;       /* GG1: 0=sequential, 1=snapshot (GPU-like) */
    float mass_kuramoto = 0.0f;  /* Thm 3.1.1 Q3b: mass-modulated Kuramoto K */
    float mass_geo = 0.0f;       /* Thm 3.1.1 Q3c: mass-modulated geo coupling */
    int kuramoto_sub_steps = 1;  /* GG2b: Kuramoto sub-sweeps per epoch (1=default) */
    int phase_diag_interval = 0;    /* K2: phase shell diagnostics interval (0=off) */
    long phase_perturb_epoch = -1;  /* K2: epoch to inject perturbation (-1=off) */
    float phase_perturb_delta = (float)(M_PI / 3.0); /* K2: perturbation amplitude */

    if (argc > 1) total_epochs = atol(argv[1]);
    if (argc > 2) seed = (uint32_t)atoi(argv[2]);
    if (argc > 3) coupling_strength = atof(argv[3]);
    if (argc > 4) mode = atoi(argv[4]);
    if (argc > 5) n_sub = atoi(argv[5]);
    if (argc > 6) mutation_rate = atof(argv[6]);
    if (argc > 7) epsilon = (float)atof(argv[7]);
    if (argc > 8) chirality = atof(argv[8]);
    if (argc > 9) chirality_mode = atoi(argv[9]);
    if (argc > 10) instr_mode = atoi(argv[10]);
    if (argc > 11) warp_alpha = (float)atof(argv[11]);
    if (argc > 12) color_pressure = atoi(argv[12]);
    if (argc > 13) phase_lock = (float)atof(argv[13]);
    if (argc > 14) kuramoto_mode = atoi(argv[14]);
    if (argc > 15) energy_lambda = (float)atof(argv[15]);
    if (argc > 16) mass_mode = atoi(argv[16]);
    if (argc > 17) mass_couple = (float)atof(argv[17]);
    if (argc > 18) snapshot_mode = atoi(argv[18]);
    if (argc > 19) mass_kuramoto = (float)atof(argv[19]);
    if (argc > 20) mass_geo = (float)atof(argv[20]);
    if (argc > 21) kuramoto_sub_steps = atoi(argv[21]);
    if (argc > 22) phase_diag_interval = atoi(argv[22]);
    if (argc > 23) phase_perturb_epoch = atol(argv[23]);
    if (argc > 24) phase_perturb_delta = (float)atof(argv[24]);

    const char *mode_names[] = {"VM+coupling", "coupling-only", "VM-only"};
    const char *chiral_mode_names[] = {"pressure-asymmetry", "coupling-weight"};
    const char *instr_mode_names[] = {"classic (NOP1/NOP2)", "enhanced (SENSE/COUPLE)", "write (SENSE/WRITE)"};

    printf("=== Stella Genesis ===\n");
    printf("G1-only geometric substrate experiment\n");
    printf("Mode: %s\n", mode_names[mode]);
    printf("Instruction mode: %s\n", instr_mode_names[instr_mode]);
    printf("Epochs: %ld\n", total_epochs);
    printf("Seed: %u\n", seed);
    printf("Coupling strength: %.3f\n", coupling_strength);
    printf("N_sub: %d\n", n_sub);
    printf("Mutation rate: %.4f\n", mutation_rate);
    printf("Epsilon: %.3f\n", epsilon);
    printf("Chirality: %.4f (%s)\n", chirality,
           chiral_mode_names[chirality_mode]);
    if (warp_alpha < 0.999f)
        printf("Mesh warp alpha: %.3f (adaptive — incenter-concentrated)\n",
               warp_alpha);
    if (color_pressure)
        printf("Color pressure: ON (per-color WRITE gate, Def 0.1.3)\n");
    if (phase_lock > 0.0f) {
        const char *plk_mode = kuramoto_mode ? "full Kuramoto (continuous phase)" :
                                               "majority-vote (Z₃ discrete)";
        printf("Phase-lock: %.4f (%s, Thm 2.2.1)\n", phase_lock, plk_mode);
    }
    if (energy_lambda > 0.0f)
        printf("Energy functional: λ=%.4f (Thm 0.2.4, drives |a_R|=|a_G|=|a_B|)\n",
               energy_lambda);
    if (mass_mode)
        printf("Mass observable: ON (Thm 3.1.1, g_chi*w0/L=%.4f)\n",
               MASS_PREFACTOR);
    if (mass_couple > 0.0f)
        printf("Mass coupling: %.4f (mass-stabilized mutation, Thm 3.1.1 Q3)\n",
               mass_couple);
    if (mass_kuramoto > 0.0f)
        printf("Mass-Kuramoto: %.4f (K_eff = K*(1+mk*m(x)), Thm 3.1.1 Q3b)\n",
               mass_kuramoto);
    if (mass_geo > 0.0f)
        printf("Mass-geo coupling: %.4f (prob *= 1+mg*m(x), Thm 3.1.1 Q3c)\n",
               mass_geo);
    if (snapshot_mode)
        printf("Snapshot mode: ON (GG1 — GPU-like parallel execution semantics)\n");
    if (kuramoto_sub_steps > 1)
        printf("Kuramoto sub-steps: %d (GG2b — multi-sweep phase diffusion)\n",
               kuramoto_sub_steps);
    if (phase_diag_interval > 0) {
        printf("K2 phase diagnostics: every %d epochs", phase_diag_interval);
        if (phase_perturb_epoch >= 0)
            printf(", perturb at epoch %ld (δ=%.3f rad)",
                   phase_perturb_epoch, phase_perturb_delta);
        printf("\n");
    }
    printf("Prog size: %d\n", PROG_SIZE);
    printf("Max steps: %d\n", MAX_STEPS);
    printf("\n");

    GenesisSoup *gsp = (GenesisSoup *)calloc(1, sizeof(GenesisSoup));
    if (!gsp) { fprintf(stderr, "Failed to allocate GenesisSoup\n"); return 1; }
    #define gs (*gsp)
    gs.prog_size = PROG_SIZE;
    gs.max_steps = MAX_STEPS;
    gs.mutation_rate = mutation_rate;
    gs.coupling_strength = coupling_strength;
    gs.epsilon = epsilon;
    gs.mode = mode;
    gs.chirality = chirality;
    gs.chirality_mode = chirality_mode;
    gs.instr_mode = instr_mode;
    gs.warp_alpha = warp_alpha;
    gs.color_pressure = color_pressure;
    gs.phase_lock = phase_lock;
    gs.kuramoto_mode = kuramoto_mode;
    gs.energy_lambda = energy_lambda;
    gs.mass_mode = mass_mode;
    gs.mass_couple = mass_couple;
    gs.mass_kuramoto = mass_kuramoto;
    gs.mass_geo = mass_geo;
    gs.snapshot_mode = snapshot_mode;
    gs.kuramoto_sub_steps = kuramoto_sub_steps;
    gs.phase_diag_interval = phase_diag_interval;
    gs.phase_perturb_epoch = phase_perturb_epoch;
    gs.phase_perturb_delta = phase_perturb_delta;

    genesis_init(&gs, n_sub, seed);
    print_pressure_landscape(&gs);

    printf("Initial state:\n");
    print_diagnostics(&gs);
    printf("\n");

    /* Snapshot interval: ~50 snapshots over the run */
    long snap_interval = total_epochs / 50;
    if (snap_interval < 1000) snap_interval = 1000;

    /* Take initial snapshot (epoch 0) */
    if (gs.instr_mode == INSTR_MODE_ENHANCED)
        take_couple_snapshot(&gs);

    /* Main loop */
    for (long e = 0; e < total_epochs; e++) {

        /* K2: Save baseline and inject phase perturbation */
        if (gs.phase_diag_interval > 0 && e == gs.phase_perturb_epoch &&
            gs.phase_perturb_site >= 0) {
            int n_k2 = gs.mesh_tp.n_sites;
            float TWO_PI_k2 = 2.0f * (float)M_PI;

            /* Save baseline phase state BEFORE perturbation */
            memcpy(gs.phase_baseline_tp, gs.phase_tp, n_k2 * sizeof(float));

            /* Compute baseline per-shell mean change rate (noise floor).
             * We measure how much each shell drifts in one epoch by comparing
             * current phases to what they'd be without perturbation. Since we
             * can't do that yet, we'll set baseline_shell_dev to 0 and measure
             * the noise floor from the first few diagnostic epochs post-perturb
             * at distant shells (which haven't been reached by the signal yet). */

            /* Inject perturbation */
            gs.phase_tp[gs.phase_perturb_site] += gs.phase_perturb_delta;
            gs.phase_tp[gs.phase_perturb_site] =
                fmodf(gs.phase_tp[gs.phase_perturb_site], TWO_PI_k2);
            if (gs.phase_tp[gs.phase_perturb_site] < 0.0f)
                gs.phase_tp[gs.phase_perturb_site] += TWO_PI_k2;
            printf("K2: Saved baseline + injected δ=%.3f at site %d, epoch %ld\n",
                   gs.phase_perturb_delta, gs.phase_perturb_site, e);
        }

        genesis_epoch(&gs);

        if ((e + 1) % report_interval == 0) {
            print_diagnostics(&gs);
        }

        /* K2: Phase wavefront diagnostics — measure CHANGE FROM BASELINE.
         * This is the perturbation response: |φ(i,t) - φ_baseline(i)|.
         * Background dynamics also change phases, so distant shells provide
         * a noise floor. The signal is the EXCESS change near the perturbation. */
        if (gs.phase_diag_interval > 0 && gs.phase_diag_file &&
            gs.phase_perturb_epoch >= 0 && e >= gs.phase_perturb_epoch &&
            (e - gs.phase_perturb_epoch) % gs.phase_diag_interval == 0) {
            int n_k2 = gs.mesh_tp.n_sites;
            int md = gs.phase_bfs_max_d;
            float TWO_PI_k2 = 2.0f * (float)M_PI;
            long dt = e - gs.phase_perturb_epoch;

            /* Per-shell: mean |φ(t) - φ_baseline| (change from saved state) */
            fprintf(gs.phase_diag_file,
                    "{\"epoch\":%ld, \"dt\":%ld, \"shells\":[", e, dt);

            /* Compute noise floor from distant shells (d > max_d*0.7) */
            float noise_sum = 0.0f;
            int noise_count = 0;
            int noise_cutoff = (int)(md * 0.7);

            for (int d = 0; d <= md; d++) {
                if (d > 0) fprintf(gs.phase_diag_file, ",");
                int nc = gs.phase_shell_count[d];
                if (nc > 0) {
                    float sum_change = 0.0f, sum_change2 = 0.0f, max_change = 0.0f;
                    for (int i = 0; i < n_k2; i++) {
                        if (gs.phase_bfs_dist[i] != d) continue;
                        /* Circular difference: φ(now) - φ(baseline) */
                        float diff = gs.phase_tp[i] - gs.phase_baseline_tp[i];
                        while (diff > (float)M_PI) diff -= TWO_PI_k2;
                        while (diff < -(float)M_PI) diff += TWO_PI_k2;
                        float ad = fabsf(diff);
                        sum_change += ad;
                        sum_change2 += diff * diff;
                        if (ad > max_change) max_change = ad;
                    }
                    float mean_ch = sum_change / nc;
                    float rms_ch = sqrtf(sum_change2 / nc);

                    /* Accumulate noise floor from distant shells */
                    if (d >= noise_cutoff) {
                        noise_sum += sum_change;
                        noise_count += nc;
                    }

                    fprintf(gs.phase_diag_file,
                            "{\"d\":%d,\"mean_change\":%.6f,\"rms\":%.6f,"
                            "\"max\":%.6f,\"n\":%d}",
                            d, mean_ch, rms_ch, max_change, nc);
                } else {
                    fprintf(gs.phase_diag_file,
                            "{\"d\":%d,\"mean_change\":0,\"rms\":0,"
                            "\"max\":0,\"n\":0}", d);
                }
            }

            /* Noise floor and signal detection */
            float noise_floor = noise_count > 0 ? noise_sum / noise_count : 0.0f;
            /* Arrival threshold: signal must exceed noise floor by 3× perturbation/n */
            float threshold = noise_floor + 3.0f * gs.phase_perturb_delta / n_k2;
            if (threshold < noise_floor + 0.005f)
                threshold = noise_floor + 0.005f;

            fprintf(gs.phase_diag_file,
                    "], \"noise_floor\":%.6f, \"threshold\":%.6f}\n",
                    noise_floor, threshold);
            fflush(gs.phase_diag_file);

            /* Track arrival: first epoch where shell d exceeds threshold */
            for (int d = 1; d <= md; d++) {
                if (gs.phase_arrival[d] >= 0) continue;
                int nc = gs.phase_shell_count[d];
                if (nc == 0) continue;
                float sum_ch = 0.0f;
                for (int i = 0; i < n_k2; i++) {
                    if (gs.phase_bfs_dist[i] != d) continue;
                    float diff = gs.phase_tp[i] - gs.phase_baseline_tp[i];
                    while (diff > (float)M_PI) diff -= TWO_PI_k2;
                    while (diff < -(float)M_PI) diff += TWO_PI_k2;
                    sum_ch += fabsf(diff);
                }
                if (sum_ch / nc > threshold)
                    gs.phase_arrival[d] = dt;
            }
        }

        /* Periodic COUPLE geography snapshots */
        if (gs.instr_mode == INSTR_MODE_ENHANCED &&
            (e + 1) % snap_interval == 0) {
            take_couple_snapshot(&gs);
        }
    }

    printf("\n=== Final State ===\n");
    print_diagnostics(&gs);
    printf("Total coupling events: %ld\n", gs.total_couplings);
    printf("T+ → T-: %ld (%.1f%%)\n", gs.coupling_tp_to_tm,
           100.0 * gs.coupling_tp_to_tm /
           (gs.coupling_tp_to_tm + gs.coupling_tm_to_tp + 1));
    printf("T- → T+: %ld (%.1f%%)\n", gs.coupling_tm_to_tp,
           100.0 * gs.coupling_tm_to_tp /
           (gs.coupling_tp_to_tm + gs.coupling_tm_to_tp + 1));
    if (gs.instr_mode == INSTR_MODE_ENHANCED) {
        printf("SENSE executions: %ld\n", gs.sense_count);
        printf("COUPLE executions: %ld\n", gs.couple_count);
        printf("COUPLE-enhanced couplings: %ld\n", gs.couple_enhanced);
        dump_couple_geography(&gs, "couple_geography.json");
        dump_couple_timeline(&gs, "couple_timeline.json");
    }
    if (gs.instr_mode == INSTR_MODE_WRITE) {
        printf("SENSE executions: %ld\n", gs.sense_count);
        printf("WRITE succeeded: %ld\n", gs.write_count);
        printf("WRITE blocked (P_other dominant): %ld\n", gs.write_blocked);
        if (gs.write_count + gs.write_blocked > 0)
            printf("WRITE success rate: %.1f%%\n",
                   100.0 * gs.write_count /
                   (gs.write_count + gs.write_blocked));
    }

    if (gs.phase_lock > 0.0f) {
        printf("Phase-lock nudges: %ld (strength=%.4f, mode=%s)\n",
               gs.phase_lock_events, gs.phase_lock,
               gs.kuramoto_mode ? "kuramoto" : "majority-vote");
    }
    if (gs.energy_lambda > 0.0f) {
        printf("Energy functional flips: %ld (λ=%.4f, Thm 0.2.4)\n",
               gs.energy_flips, gs.energy_lambda);
    }
    if (gs.mass_mode) {
        printf("\n=== Phase-Gradient Mass Observable (Thm 3.1.1) ===\n");
        print_mass_diagnostics(&gs);
        dump_mass_geography(&gs, "mass_geography.json");
        if (gs.mass_couple > 0.0f)
            printf("Mass-coupled mutation blocks: %ld\n", gs.mass_couple_blocks);
        if (gs.mass_kuramoto > 0.0f)
            printf("Mass-Kuramoto boosts: %ld (mk=%.4f)\n",
                   gs.mass_kuramoto_boosts, gs.mass_kuramoto);
        if (gs.mass_geo > 0.0f)
            printf("Mass-geo boosts: %ld (mg=%.4f)\n",
                   gs.mass_geo_boosts, gs.mass_geo);
    }

    /* Per-site correlation binned by P_ratio — reveals coherence propagation */
    {
        int n = gs.mesh_tp.n_sites;
        int nbins = 10;
        int bin_count[10] = {0};
        int bin_match[10] = {0};
        printf("\n=== Correlation by P_ratio (at T+ sites) ===\n");
        printf("P_ratio_range     n_sites  match_rate  (WRITE gate)\n");
        for (int i = 0; i < n; i++) {
            float ratio = gs.pp_at_tp[i] / (gs.pp_at_tp[i] + gs.pm_at_tp[i]);
            int b = (int)(ratio * nbins);
            if (b >= nbins) b = nbins - 1;
            if (b < 0) b = 0;
            bin_count[b]++;
            if (gs.tp_data[i] == gs.tm_data[i]) bin_match[b]++;
        }
        for (int b = 0; b < nbins; b++) {
            if (bin_count[b] == 0) continue;
            float lo = (float)b / nbins;
            float hi = (float)(b + 1) / nbins;
            float rate = (float)bin_match[b] / bin_count[b];
            const char *gate = (lo >= 0.5f) ? "open" :
                               (hi > 0.5f)  ? "boundary" : "blocked";
            printf("[%.2f,%.2f)  %6d   %.4f   %s\n",
                   lo, hi, bin_count[b], rate, gate);
        }
        /* Also report by distance from nearest own vertex */
        printf("\n=== Correlation by distance from nearest vertex ===\n");
        printf("dist_range        n_sites  match_rate\n");
        float dist_bins[] = {0, 0.3, 0.6, 0.9, 1.2, 1.5, 2.0};
        int ndist = 6;
        for (int db = 0; db < ndist; db++) {
            int dc = 0, dm = 0;
            for (int i = 0; i < n; i++) {
                /* Distance to nearest own vertex */
                float mind = 1e10;
                const float (*verts)[3] = (const float (*)[3])TV_PLUS;
                for (int v = 0; v < 4; v++) {
                    float dx = gs.mesh_tp.pos[i][0] - verts[v][0];
                    float dy = gs.mesh_tp.pos[i][1] - verts[v][1];
                    float dz = gs.mesh_tp.pos[i][2] - verts[v][2];
                    float d = sqrtf(dx*dx + dy*dy + dz*dz);
                    if (d < mind) mind = d;
                }
                if (mind >= dist_bins[db] && mind < dist_bins[db + 1]) {
                    dc++;
                    if (gs.tp_data[i] == gs.tm_data[i]) dm++;
                }
            }
            if (dc > 0)
                printf("[%.1f,%.1f)  %6d   %.4f\n",
                       dist_bins[db], dist_bins[db + 1], dc,
                       (float)dm / dc);
        }
    }

    /* K2: Phase wavefront analysis — compute arrival times and power-law fit */
    if (gs.phase_diag_interval > 0 && gs.phase_perturb_epoch >= 0) {
        int md = gs.phase_bfs_max_d;
        printf("\n=== K2: Kuramoto Phase Wavefront Analysis ===\n");
        printf("Perturbation: δ=%.3f at site %d, epoch %ld\n",
               gs.phase_perturb_delta, gs.phase_perturb_site,
               gs.phase_perturb_epoch);
        printf("BFS max distance: %d hops\n\n", md);

        /* Print arrival times */
        int n_arrived = 0;
        printf("Shell arrivals (d → Δepoch):\n");
        for (int d = 1; d <= md; d++) {
            if (gs.phase_arrival[d] >= 0) {
                printf("  d=%2d  Δt=%6ld  (shell size=%d)\n",
                       d, gs.phase_arrival[d], gs.phase_shell_count[d]);
                n_arrived++;
            }
        }
        if (n_arrived == 0) {
            printf("  No arrivals detected.\n");
        }

        /* Power-law fit: log(d) = α·log(t) + β
         * α ≈ 0.5 → diffusive, α ≈ 1.0 → ballistic */
        if (n_arrived >= 3) {
            double sum_lnt = 0, sum_lnd = 0, sum_lnt2 = 0, sum_lntd = 0;
            int nf = 0;
            for (int d = 1; d <= md; d++) {
                if (gs.phase_arrival[d] > 0) {
                    double lt = log((double)gs.phase_arrival[d]);
                    double ld = log((double)d);
                    sum_lnt += lt; sum_lnd += ld;
                    sum_lnt2 += lt * lt; sum_lntd += lt * ld;
                    nf++;
                }
            }
            double denom = nf * sum_lnt2 - sum_lnt * sum_lnt;
            if (fabs(denom) > 1e-30) {
                double alpha = (nf * sum_lntd - sum_lnt * sum_lnd) / denom;

                /* R² for log-log fit */
                double mean_ld = sum_lnd / nf;
                double ss_tot = 0, ss_res = 0;
                double beta = (sum_lnd - alpha * sum_lnt) / nf;
                for (int d = 1; d <= md; d++) {
                    if (gs.phase_arrival[d] > 0) {
                        double lt = log((double)gs.phase_arrival[d]);
                        double ld = log((double)d);
                        double pred = alpha * lt + beta;
                        ss_res += (ld - pred) * (ld - pred);
                        ss_tot += (ld - mean_ld) * (ld - mean_ld);
                    }
                }
                double r2 = ss_tot > 0 ? 1.0 - ss_res / ss_tot : 0;

                /* Diffusion constant: d² = 2D·t → D from linear fit of d² vs t */
                double sum_t = 0, sum_d2 = 0, sum_t2 = 0, sum_td2 = 0;
                for (int d = 1; d <= md; d++) {
                    if (gs.phase_arrival[d] > 0) {
                        double t = (double)gs.phase_arrival[d];
                        double dd = (double)d;
                        sum_t += t; sum_d2 += dd*dd;
                        sum_t2 += t*t; sum_td2 += t * dd * dd;
                    }
                }
                double denom2 = nf * sum_t2 - sum_t * sum_t;
                double D_meas = 0;
                if (fabs(denom2) > 1e-30)
                    D_meas = (nf * sum_td2 - sum_t * sum_d2) / (2.0 * denom2);

                const char *verdict =
                    alpha < 0.65 ? "DIFFUSIVE" :
                    alpha > 0.85 ? "BALLISTIC" : "INTERMEDIATE";

                printf("\nPower-law fit: d ∝ t^%.3f  (R²=%.4f)  → %s\n",
                       alpha, r2, verdict);
                printf("  (α≈0.5 = diffusive/heat-equation, "
                       "α≈1.0 = ballistic/wave-equation)\n");
                printf("Diffusion constant: D = %.4f hops²/epoch\n", D_meas);

                if (alpha > 0.85) {
                    printf("\n*** WAVE-LIKE PROPAGATION DETECTED ***\n");
                    printf("The full Genesis soup dynamics produce ballistic "
                           "phase propagation,\nunlike pure Kuramoto (K1: α=0.527). "
                           "VM feedback + mass coupling create\neffective inertia "
                           "→ emergent finite propagation speed.\n");
                } else if (alpha < 0.65) {
                    printf("\nPhase propagation remains diffusive even with full "
                           "Genesis dynamics.\nThe VM/mass/energy mechanisms do not "
                           "create sufficient inertia for wave-like behavior.\n");
                } else {
                    printf("\nIntermediate regime: partial inertial effects present.\n");
                }
            }
        } else if (n_arrived > 0) {
            printf("\nInsufficient arrivals (%d) for power-law fit (need ≥3).\n",
                   n_arrived);
        }

        if (gs.phase_diag_file) {
            fclose(gs.phase_diag_file);
            printf("\nPhase diagnostic data: phase_K2_diag.jsonl\n");
        }
    }

    /* Cleanup */
    free(gs.phase_bfs_dist);
    free(gs.phase_shell_count);
    free(gs.phase_arrival);
    free(gs.phase_baseline_tp);
    free(gs.phase_baseline_shell_dev);
    free(gs.tp_data); free(gs.tm_data);
    free(gs.pp_at_tp); free(gs.pm_at_tp);
    free(gs.pp_at_tm); free(gs.pm_at_tm);
    free(gs.work_a); free(gs.work_b);
    free(gs.patch_a); free(gs.patch_b);
    free(gs.pressure_ratio_a); free(gs.pressure_ratio_b);
    free(gs.couple_flags_a); free(gs.couple_flags_b);
    for (int c = 0; c < 3; c++) {
        free(gs.pressure_ratio_color_a[c]);
        free(gs.pressure_ratio_color_b[c]);
    }
    free(gs.couple_hist_tp); free(gs.couple_hist_tm);
    free(gs.visit_hist);
    free(gs.dominant_color_tp); free(gs.dominant_color_tm);
    free(gs.phase_tp); free(gs.phase_tm);
    free(gs.grad_phi_tp); free(gs.grad_phi_tm);
    free(gs.vchi_tp); free(gs.vchi_tm);
    free(gs.mass_tp); free(gs.mass_tm);
    free(gs.snap_tp); free(gs.snap_tm);
    free(gs.snap_phase_tp); free(gs.snap_phase_tm);

    return 0;
}
