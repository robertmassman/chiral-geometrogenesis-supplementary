/*
 * G1+G2 Combined Multi-Stella FCC Lattice Soup
 * =============================================
 * Combines G1 geometric coupling (pressure-mediated T+/T- coherence, from
 * genesis_soup.c) with G2 instruction-based mechanisms (dual-head VM,
 * CPY01/CPY10, from soup_multi_stella.c) on a multi-stella FCC lattice.
 *
 * Architecture:
 *   - FCC lattice of size L: L^3/2 stellae (periodic boundary)
 *   - Each stella: triangulated T+ and T- with Voronoi tiles
 *   - G2: Intra-stella VM interactions (parallel, dual-head CPY01/CPY10)
 *   - G1: Intra-stella geometric coupling (parallel, pressure-gated)
 *   - G2: Inter-stella coupling (serial, direct or octahedral)
 *   - Per-stella RNG for deterministic parallel execution
 *
 * Three-phase epoch:
 *   Phase 1: Intra-stella VM interactions + mutation (G2, parallel)
 *   Phase 2: Intra-stella geometric coupling (G1, parallel)
 *   Phase 3: Inter-stella coupling (G2, serial)
 *
 * Key references:
 *   - Def 0.1.3: Pressure functions P_c(x) = 1/(|x-v|^2 + eps^2)
 *   - Thm 0.0.6: FCC lattice structure
 *   - Thm 0.2.1: Inter-component coupling (CPY01/CPY10)
 *
 * Compile: cc -O3 -march=native -ffast-math -flto -o soup_g1g2 soup_g1g2.c -lm -lpthread
 * Run:     ./soup_g1g2 --lattice-size 2 --n-sub 100 --epochs 5000000 --g1
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <getopt.h>

#include <pthread.h>

#ifdef _OPENMP
#include <omp.h>
#endif

#define Z3 3
#define MAX_NBR 8
#define FCC_NN 12

/* === Defaults === */
#define DEF_LATTICE_SIZE   2
#define DEF_N_SUB          100
#define DEF_PROG_SIZE      24
#define DEF_MAX_STEPS      729
#define DEF_EPOCHS         5000000L
#define DEF_CROSS_RATE     1.0
#define DEF_LOG_INTERVAL   10000
#define DEF_CHECK_INTERVAL 100000
#define DEF_CENSUS_INTERVAL 0

/* Coupling modes for inter-stella interactions */
#define COUPLING_DIRECT     0
#define COUPLING_OCTAHEDRAL 1

/* Mass-gradient coupling (Thm 3.1.1): m(x) = prefactor · v_χ(x) · |∇φ(x)| */
#define MASS_PREFACTOR 0.2778f  /* (4π/9) · (ω₀/Λ) = (4π/9) · (220/1106) */

/* === Opcodes (G2 dual-head ISA, unchanged) === */
#define OP_NOP   0
#define OP_ROT   1
#define OP_FWD0  2
#define OP_BCK0  3
#define OP_FWD1  4
#define OP_OPEN  5
#define OP_CLOSE 6
#define OP_CPY01 7
#define OP_CPY10 8

static const char *OP_NAMES[] = {
    "NOP", "ROT", "FWD0", "BCK0", "FWD1", "[", "]", "CPY01", "CPY10"
};

/* === Stella Octangula Vertices (Def 0.0.0) === */
static const float TV_PLUS[4][3] = {
    { 1, 1, 1}, { 1,-1,-1}, {-1, 1,-1}, {-1,-1, 1}
};
static const float TV_MINUS[4][3] = {
    {-1,-1,-1}, {-1, 1, 1}, { 1,-1, 1}, { 1, 1,-1}
};

/* ================================================================
 * PRNG: xoshiro256** with explicit state (thread-safe)
 * ================================================================ */

static inline uint64_t rotl(uint64_t x, int k) {
    return (x << k) | (x >> (64 - k));
}

static uint64_t rng_next(uint64_t s[4]) {
    uint64_t result = rotl(s[1] * 5, 7) * 9;
    uint64_t t = s[1] << 17;
    s[2] ^= s[0]; s[3] ^= s[1]; s[1] ^= s[2]; s[0] ^= s[3];
    s[2] ^= t; s[3] = rotl(s[3], 45);
    return result;
}

static void rng_seed(uint64_t s[4], uint64_t seed) {
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        s[i] = z ^ (z >> 31);
    }
}

static inline uint32_t rng_int(uint64_t s[4], uint32_t n) {
    return (uint32_t)((rng_next(s) >> 33) % n);
}

static inline double rng_float(uint64_t s[4]) {
    return (rng_next(s) >> 11) * 0x1.0p-53;
}

/* ================================================================
 * VM (G2 dual-head, identical to soup_multi_stella.c)
 * ================================================================ */

static void build_bracket_map(const uint8_t *tape, int tape_len, int *bracket_map) {
    int stack[512];
    int sp = 0;
    for (int ip = 0; ip + 1 < tape_len; ip += 2) {
        bracket_map[ip] = -1;
        int op = tape[ip] * 3 + tape[ip + 1];
        if (op == OP_OPEN) {
            if (sp < 512) stack[sp++] = ip;
        } else if (op == OP_CLOSE) {
            if (sp > 0) {
                int match = stack[--sp];
                bracket_map[match] = ip;
                bracket_map[ip] = match;
            }
        }
    }
}

static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
    int bracket_map[2048];
    build_bracket_map(tape, tape_len < 2048 ? tape_len : 2048, bracket_map);

    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;

    static const void *dispatch[] = {
        &&op_nop, &&op_rot, &&op_fwd0, &&op_bck0, &&op_fwd1,
        &&op_open, &&op_close, &&op_cpy01, &&op_cpy10
    };

#define NEXT() do { \
    ip += 2; steps++; \
    if (steps >= max_steps || ip + 1 >= tape_len) goto done; \
    goto *dispatch[tape[ip] * 3 + tape[ip + 1]]; \
} while (0)

    if (ip + 1 >= tape_len) goto done;
    goto *dispatch[tape[ip] * 3 + tape[ip + 1]];

op_nop:  NEXT();
op_rot:  { uint8_t v = tape[h0]; tape[h0] = v < 2 ? v + 1 : 0; } NEXT();
op_fwd0: if (++h0 >= tape_len) h0 = 0; NEXT();
op_bck0: if (--h0 < 0) h0 = tape_len - 1; NEXT();
op_fwd1: if (++h1 >= tape_len) h1 = 0; NEXT();

op_open:
    if (tape[h0] == 0) {
        int target = (ip < 2048) ? bracket_map[ip] : -1;
        if (target >= 0) { ip = target; }
        else {
            int depth = 1, pos = ip + 2;
            while (depth > 0 && pos + 1 < tape_len) {
                int inner = tape[pos] * 3 + tape[pos + 1];
                if (inner == OP_OPEN) depth++;
                else if (inner == OP_CLOSE) depth--;
                pos += 2;
            }
            if (depth == 0) ip = pos - 2;
        }
    }
    NEXT();

op_close:
    if (tape[h0] != 0) {
        int target = (ip < 2048) ? bracket_map[ip] : -1;
        if (target >= 0) { ip = target; }
        else {
            int depth = 1, pos = ip - 2;
            while (depth > 0 && pos >= 0) {
                int inner = tape[pos] * 3 + tape[pos + 1];
                if (inner == OP_CLOSE) depth++;
                else if (inner == OP_OPEN) depth--;
                pos -= 2;
            }
            if (depth == 0) ip = pos + 2;
        }
    }
    NEXT();

op_cpy01: tape[h1] = tape[h0]; NEXT();
op_cpy10: tape[h0] = tape[h1]; NEXT();

done:
    (void)0;
#undef NEXT
}

/* ================================================================
 * Mesh with 3D coordinates (extended from soup_multi_stella.c)
 * ================================================================ */

typedef struct {
    int n_sites;
    int *n_nbr;
    int (*nbr)[MAX_NBR];
    float (*tp_pos)[3];    /* T+ 3D coordinates per site */
    float (*tm_pos)[3];    /* T- 3D coordinates per site */
} Mesh;

static const int TETRA_F[4][3] = {
    {1, 2, 3}, {0, 3, 2}, {0, 1, 3}, {0, 2, 1},
};

static const int EDGE_V[6][2] = {
    {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}
};

static int edge_index(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    for (int e = 0; e < 6; e++)
        if (EDGE_V[e][0] == a && EDGE_V[e][1] == b) return e;
    return -1;
}

static void mesh_add_edge(Mesh *m, int a, int b) {
    if (a == b) return;
    for (int i = 0; i < m->n_nbr[a]; i++)
        if (m->nbr[a][i] == b) return;
    if (m->n_nbr[a] < MAX_NBR) m->nbr[a][m->n_nbr[a]++] = b;
    if (m->n_nbr[b] < MAX_NBR) m->nbr[b][m->n_nbr[b]++] = a;
}

static Mesh *mesh_build(int n_sub, int compute_positions) {
    int n = n_sub;
    int n_sites = 2 * n * n + 2;
    int n_face_int = (n - 1) * (n - 2) / 2;

    Mesh *m = calloc(1, sizeof(Mesh));
    m->n_sites = n_sites;
    m->n_nbr = calloc(n_sites, sizeof(int));
    m->nbr = calloc(n_sites, sizeof(int[MAX_NBR]));

    /* Allocate position arrays if G1 coupling is enabled */
    if (compute_positions) {
        m->tp_pos = calloc(n_sites, sizeof(float[3]));
        m->tm_pos = calloc(n_sites, sizeof(float[3]));
    } else {
        m->tp_pos = NULL;
        m->tm_pos = NULL;
    }

    int **face_vid[4];
    for (int f = 0; f < 4; f++) {
        face_vid[f] = malloc((n + 1) * sizeof(int *));
        for (int i = 0; i <= n; i++)
            face_vid[f][i] = malloc((n - i + 1) * sizeof(int));
    }

    int face_int_count[4] = {0, 0, 0, 0};

    for (int f = 0; f < 4; f++) {
        int a = TETRA_F[f][0], b = TETRA_F[f][1], c = TETRA_F[f][2];
        for (int i = 0; i <= n; i++) {
            for (int j = 0; j <= n - i; j++) {
                int id;
                if (i == 0 && j == 0) id = a;
                else if (i == n && j == 0) id = b;
                else if (i == 0 && j == n) id = c;
                else if (j == 0 && i > 0 && i < n) {
                    int va = a, vb = b, k = i;
                    if (va > vb) { k = n - i; int t = va; va = vb; vb = t; }
                    id = 4 + edge_index(va, vb) * (n - 1) + (k - 1);
                } else if (i == 0 && j > 0 && j < n) {
                    int va = a, vc = c, k = j;
                    if (va > vc) { k = n - j; int t = va; va = vc; vc = t; }
                    id = 4 + edge_index(va, vc) * (n - 1) + (k - 1);
                } else if (i + j == n && i > 0 && j > 0) {
                    int vb = b, vc = c, k = j;
                    if (vb > vc) { k = n - j; int t = vb; vb = vc; vc = t; }
                    id = 4 + edge_index(vb, vc) * (n - 1) + (k - 1);
                } else {
                    id = 4 + 6 * (n - 1) + f * n_face_int + face_int_count[f]++;
                }
                face_vid[f][i][j] = id;

                /* Compute 3D positions from barycentric coordinates */
                if (compute_positions) {
                    float fi = (float)i / n;
                    float fj = (float)j / n;
                    float fk = 1.0f - fi - fj;
                    /* T+ position */
                    for (int d = 0; d < 3; d++)
                        m->tp_pos[id][d] = fk * TV_PLUS[a][d] +
                                            fi * TV_PLUS[b][d] +
                                            fj * TV_PLUS[c][d];
                    /* T- position (same barycentric, different vertices) */
                    for (int d = 0; d < 3; d++)
                        m->tm_pos[id][d] = fk * TV_MINUS[a][d] +
                                            fi * TV_MINUS[b][d] +
                                            fj * TV_MINUS[c][d];
                }
            }
        }
    }

    /* Build adjacency edges */
    for (int f = 0; f < 4; f++) {
        for (int i = 0; i <= n; i++) {
            for (int j = 0; j <= n - i; j++) {
                int v = face_vid[f][i][j];
                if (i + 1 <= n - j)
                    mesh_add_edge(m, v, face_vid[f][i + 1][j]);
                if (j + 1 <= n - i)
                    mesh_add_edge(m, v, face_vid[f][i][j + 1]);
                if (i + 1 <= n && j >= 1 && i + 1 + j - 1 <= n)
                    mesh_add_edge(m, v, face_vid[f][i + 1][j - 1]);
            }
        }
    }

    for (int f = 0; f < 4; f++) {
        for (int i = 0; i <= n; i++) free(face_vid[f][i]);
        free(face_vid[f]);
    }
    return m;
}

static void mesh_free(Mesh *m) {
    free(m->n_nbr); free(m->nbr);
    if (m->tp_pos) free(m->tp_pos);
    if (m->tm_pos) free(m->tm_pos);
    free(m);
}

/* ================================================================
 * Tiling: Voronoi-like partition (from soup_multi_stella.c)
 * ================================================================ */

typedef struct {
    int n_tiles;
    int *tile_size;
    int **tile_sites;
    int (*tile_neighbors)[8];
    int *n_tile_nbr;
} Tiling;

static Tiling *tiling_build(const Mesh *m, int n_tiles, int prog_size,
                             uint64_t rng_s[4]) {
    Tiling *t = calloc(1, sizeof(Tiling));
    t->n_tiles = n_tiles;
    t->tile_size = calloc(n_tiles, sizeof(int));
    t->tile_sites = calloc(n_tiles, sizeof(int *));
    t->tile_neighbors = calloc(n_tiles, sizeof(int[8]));
    t->n_tile_nbr = calloc(n_tiles, sizeof(int));

    for (int i = 0; i < n_tiles; i++)
        t->tile_sites[i] = malloc(prog_size * sizeof(int));

    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int next_start = 0;
    int tiles_built = 0;

    for (int tile = 0; tile < n_tiles; tile++) {
        while (next_start < m->n_sites && owner[next_start] != -1)
            next_start++;
        if (next_start >= m->n_sites) break;

        int seed = next_start;
        owner[seed] = tile;
        t->tile_sites[tile][0] = seed;
        t->tile_size[tile] = 1;

        int qhead = 0, qtail = 0;
        queue[qtail++] = seed;

        while (qhead < qtail && t->tile_size[tile] < prog_size) {
            int site = queue[qhead++];
            for (int ni = 0; ni < m->n_nbr[site]; ni++) {
                int nb = m->nbr[site][ni];
                if (owner[nb] == -1 && t->tile_size[tile] < prog_size) {
                    owner[nb] = tile;
                    int idx = t->tile_size[tile]++;
                    if (idx < prog_size) t->tile_sites[tile][idx] = nb;
                    queue[qtail++] = nb;
                }
            }
        }
        tiles_built++;
    }

    int unowned = 0;
    for (int i = 0; i < m->n_sites; i++)
        if (owner[i] == -1) unowned++;
    int undersized = 0;
    for (int i = 0; i < n_tiles; i++)
        if (t->tile_size[i] < prog_size) undersized++;
    printf("  Tiling: %d/%d tiles built, %d undersized (<%d), %d unowned sites\n",
           tiles_built, n_tiles, undersized, prog_size, unowned);

    for (int site = 0; site < m->n_sites; site++) {
        if (owner[site] < 0) continue;
        int ti = owner[site];
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] < 0 || owner[nb] == ti) continue;
            int tj = owner[nb];
            int found = 0;
            for (int k = 0; k < t->n_tile_nbr[ti]; k++)
                if (t->tile_neighbors[ti][k] == tj) { found = 1; break; }
            if (!found && t->n_tile_nbr[ti] < 8)
                t->tile_neighbors[ti][t->n_tile_nbr[ti]++] = tj;
        }
    }

    free(owner); free(queue);
    return t;
}

static void tiling_free(Tiling *t) {
    for (int i = 0; i < t->n_tiles; i++) free(t->tile_sites[i]);
    free(t->tile_sites); free(t->tile_size);
    free(t->tile_neighbors); free(t->n_tile_nbr);
    free(t);
}

/* ================================================================
 * FCC Lattice (Theorem 0.0.6)
 * ================================================================ */

static const int FCC_DNN[12][3] = {
    {+1,+1, 0}, {+1,-1, 0}, {-1,+1, 0}, {-1,-1, 0},
    {+1, 0,+1}, {+1, 0,-1}, {-1, 0,+1}, {-1, 0,-1},
    { 0,+1,+1}, { 0,+1,-1}, { 0,-1,+1}, { 0,-1,-1},
};

typedef struct {
    int L;
    int n_sites;
    int (*coords)[3];
    int (*neighbors)[12];
    int *index_map;
} FCCLattice;

static FCCLattice *fcc_build(int L) {
    FCCLattice *f = calloc(1, sizeof(FCCLattice));
    f->L = L;
    f->index_map = malloc(L * L * L * sizeof(int));

    int count = 0;
    for (int i = 0; i < L; i++)
        for (int j = 0; j < L; j++)
            for (int k = 0; k < L; k++)
                f->index_map[i*L*L + j*L + k] =
                    ((i + j + k) % 2 == 0) ? count++ : -1;

    f->n_sites = count;
    f->coords = malloc(count * sizeof(int[3]));
    f->neighbors = malloc(count * sizeof(int[12]));

    int idx = 0;
    for (int i = 0; i < L; i++)
        for (int j = 0; j < L; j++)
            for (int k = 0; k < L; k++)
                if ((i + j + k) % 2 == 0) {
                    f->coords[idx][0] = i;
                    f->coords[idx][1] = j;
                    f->coords[idx][2] = k;
                    idx++;
                }

    for (int s = 0; s < count; s++) {
        int ci = f->coords[s][0], cj = f->coords[s][1], ck = f->coords[s][2];
        for (int d = 0; d < 12; d++) {
            int ni = ((ci + FCC_DNN[d][0]) % L + L) % L;
            int nj = ((cj + FCC_DNN[d][1]) % L + L) % L;
            int nk = ((ck + FCC_DNN[d][2]) % L + L) % L;
            f->neighbors[s][d] = f->index_map[ni*L*L + nj*L + nk];
        }
    }

    return f;
}

static int *fcc_distances(FCCLattice *f, int source) {
    int n = f->n_sites;
    int *dist = malloc(n * sizeof(int));
    for (int i = 0; i < n; i++) dist[i] = -1;
    dist[source] = 0;
    int *queue = malloc(n * sizeof(int));
    int head = 0, tail = 0;
    queue[tail++] = source;
    while (head < tail) {
        int s = queue[head++];
        for (int d = 0; d < 12; d++) {
            int nb = f->neighbors[s][d];
            if (nb >= 0 && dist[nb] < 0) {
                dist[nb] = dist[s] + 1;
                queue[tail++] = nb;
            }
        }
    }
    free(queue);
    return dist;
}

static void fcc_free(FCCLattice *f) {
    free(f->coords); free(f->neighbors); free(f->index_map); free(f);
}

/* ================================================================
 * G1 Pressure Functions (Def 0.1.3, from genesis_soup.c)
 * ================================================================ */

static float pressure_at_site(const float pos[3], const float verts[4][3],
                               float epsilon) {
    /* P(x) = max over vertices v of 1/(|x-v|^2 + eps^2) */
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

/* ================================================================
 * Multi-Stella Soup (extended with G1 fields)
 * ================================================================ */

typedef struct {
    uint8_t *tp_data;
    uint8_t *tm_data;
    uint64_t rng[4];
    /* G1 diagnostic counters (per stella, updated in parallel) */
    long geo_tp_to_tm;
    long geo_tm_to_tp;
    long mass_geo_boosts;   /* Q3c: mass-boosted coupling events */
} StellaSite;

typedef struct {
    FCCLattice *lattice;
    Mesh *mesh;
    Tiling *tp_tiling;
    Tiling *tm_tiling;
    StellaSite *sites;

    int n_tiles_per;
    int n_tiles_per_stella;
    int prog_size;
    int max_steps;
    double mutation_rate;
    double cross_rate;
    int local_interact;
    int coupling_mode;

    /* Octahedral interstitials (Mode B) */
    int n_edges;
    int *edge_map;
    uint8_t **oct_data;

    /* Replicator test tolerance (W2b: Hamming distance) */
    int hamming_tolerance;  /* 0 = strict memcmp, >0 = allow N mismatches */

    /* G1 geometric coupling fields */
    int g1_enabled;
    float coupling_strength;
    float epsilon;
    float *pp_at_tp;    /* P+ at T+ site positions [n_mesh] */
    float *pm_at_tp;    /* P- at T+ site positions [n_mesh] */
    float *pp_at_tm;    /* P+ at T- site positions [n_mesh] */
    float *pm_at_tm;    /* P- at T- site positions [n_mesh] */

    /* Chirality (Axiom P3: right-handed pressure asymmetry) */
    float chirality;        /* 0=symmetric, >0 = T+ favored */
    int chirality_mode;     /* 0=pressure-asymmetry, 1=coupling-weight */

    /* Mass-geometric coupling (Q3c: Thm 3.1.1) */
    float mass_geo;         /* 0=off, >0 = mass-boost strength */
    float *mass_tp;         /* [n_mesh] T+ mass density (work array) */
    float *mass_tm;         /* [n_mesh] T- mass density (work array) */
    float *grad_phi_tp;     /* [n_mesh] |∇φ| on T+ (work array) */
    float *grad_phi_tm;     /* [n_mesh] |∇φ| on T- (work array) */
    float *vchi_tp;         /* [n_mesh] v_χ on T+ (static, from pressure) */
    float *vchi_tm;         /* [n_mesh] v_χ on T- (static, from pressure) */

    uint64_t master_rng[4];
    uint64_t metrics_rng[4];
    long epoch;

    /* G1 global diagnostics (aggregated after parallel phase) */
    long total_geo_couplings;
    long total_geo_tp_to_tm;
    long total_geo_tm_to_tp;
} MultiStellaSoup;

/* === Tile read/write === */

static void stella_tile_read(const uint8_t *tp_data, const uint8_t *tm_data,
                              const Tiling *tp_til, const Tiling *tm_til,
                              int n_tiles_per, int tile_idx,
                              uint8_t *buf, int prog_size) {
    int is_tp = tile_idx < n_tiles_per;
    int local = is_tp ? tile_idx : tile_idx - n_tiles_per;
    const uint8_t *data = is_tp ? tp_data : tm_data;
    const Tiling *t = is_tp ? tp_til : tm_til;

    int sz = t->tile_size[local];
    for (int i = 0; i < sz && i < prog_size; i++)
        buf[i] = data[t->tile_sites[local][i]];
    for (int i = sz; i < prog_size; i++)
        buf[i] = 0;
}

static void stella_tile_write(uint8_t *tp_data, uint8_t *tm_data,
                               const Tiling *tp_til, const Tiling *tm_til,
                               int n_tiles_per, int tile_idx,
                               const uint8_t *buf, int prog_size) {
    int is_tp = tile_idx < n_tiles_per;
    int local = is_tp ? tile_idx : tile_idx - n_tiles_per;
    uint8_t *data = is_tp ? tp_data : tm_data;
    const Tiling *t = is_tp ? tp_til : tm_til;

    int sz = t->tile_size[local];
    for (int i = 0; i < sz && i < prog_size; i++)
        data[t->tile_sites[local][i]] = buf[i];
}

static int pick_partner_local(uint64_t rng[4], const Tiling *tp_til,
                               const Tiling *tm_til, int n_tiles_per,
                               int tile_idx) {
    int is_tp = tile_idx < n_tiles_per;
    int local_a = is_tp ? tile_idx : tile_idx - n_tiles_per;
    const Tiling *t = is_tp ? tp_til : tm_til;

    int nn = t->n_tile_nbr[local_a];
    int local_b = local_a;
    if (nn > 0)
        local_b = t->tile_neighbors[local_a][rng_int(rng, nn)];

    if (rng_float(rng) < 0.5) is_tp = !is_tp;
    return is_tp ? local_b : local_b + n_tiles_per;
}

/* === G1 Pressure Precomputation === */

static void precompute_pressure(MultiStellaSoup *ms) {
    int n = ms->mesh->n_sites;
    float eps = ms->epsilon;

    /* Chirality mode 0 (pressure asymmetry): P+ scaled by (1+chi),
     * making right-handed (T+) pressure intrinsically stronger.
     * This models the framework's right-handed pressure convention (Axiom P3).
     * Reference: genesis_soup.c lines 413-428. */
    float p_plus_scale = 1.0f;
    if (ms->chirality_mode == 0 && ms->chirality > 0.0f)
        p_plus_scale = 1.0f + ms->chirality;

    ms->pp_at_tp = calloc(n, sizeof(float));
    ms->pm_at_tp = calloc(n, sizeof(float));
    ms->pp_at_tm = calloc(n, sizeof(float));
    ms->pm_at_tm = calloc(n, sizeof(float));

    for (int i = 0; i < n; i++) {
        ms->pp_at_tp[i] = p_plus_scale * pressure_at_site(ms->mesh->tp_pos[i], TV_PLUS, eps);
        ms->pm_at_tp[i] = pressure_at_site(ms->mesh->tp_pos[i], TV_MINUS, eps);
        ms->pp_at_tm[i] = p_plus_scale * pressure_at_site(ms->mesh->tm_pos[i], TV_PLUS, eps);
        ms->pm_at_tm[i] = pressure_at_site(ms->mesh->tm_pos[i], TV_MINUS, eps);
    }

    /* Report pressure statistics */
    int tp_dominant = 0, tm_dominant = 0;
    for (int i = 0; i < n; i++) {
        if (ms->pp_at_tp[i] > ms->pm_at_tp[i]) tp_dominant++;
        if (ms->pm_at_tm[i] > ms->pp_at_tm[i]) tm_dominant++;
    }
    printf("  Pressure: %d/%d T+ dominant at T+ sites, %d/%d T- dominant at T- sites\n",
           tp_dominant, n, tm_dominant, n);
}

/* === Mass Observable (Thm 3.1.1, Z₃ discrete version) === */

/* Compute Z₃ phase gradient |∇φ| for one surface of one stella.
 * For Z₃ trits, |Δφ| = 0 if same trit, 2π/3 if different.
 * |∇φ(x)| = (1/N_nbr) Σ_{j∈nbr} |Δφ(x,j)| / edge_len
 * Ported from soup_multi_stella.c */
static void compute_z3_phase_gradient(const uint8_t *data, const Mesh *m,
                                        const float (*pos)[3], float *grad_mag) {
    int n = m->n_sites;
    float two_pi_3 = 2.0f * (float)M_PI / 3.0f;
    for (int i = 0; i < n; i++) {
        int nn = m->n_nbr[i];
        if (nn == 0) { grad_mag[i] = 0.0f; continue; }
        float sum = 0.0f;
        for (int j = 0; j < nn; j++) {
            int nb = m->nbr[i][j];
            if (data[nb] != data[i]) {
                float dx = pos[nb][0] - pos[i][0];
                float dy = pos[nb][1] - pos[i][1];
                float dz = pos[nb][2] - pos[i][2];
                float edge_len = sqrtf(dx*dx + dy*dy + dz*dz);
                sum += (edge_len > 1e-8f) ? two_pi_3 / edge_len : two_pi_3;
            }
        }
        grad_mag[i] = sum / nn;
    }
}

/* Compute mass observable for one stella into per-thread work arrays.
 * m(x) = MASS_PREFACTOR · v_χ(x) · |∇φ(x)|  (Thm 3.1.1) */
static void mss_compute_mass(MultiStellaSoup *ms, int stella_idx,
                              float *mass_tp, float *mass_tm,
                              float *grad_tp, float *grad_tm) {
    int n = ms->mesh->n_sites;
    const uint8_t *tp = ms->sites[stella_idx].tp_data;
    const uint8_t *tm = ms->sites[stella_idx].tm_data;

    compute_z3_phase_gradient(tp, ms->mesh, ms->mesh->tp_pos, grad_tp);
    compute_z3_phase_gradient(tm, ms->mesh, ms->mesh->tm_pos, grad_tm);

    for (int i = 0; i < n; i++) {
        mass_tp[i] = MASS_PREFACTOR * ms->vchi_tp[i] * grad_tp[i];
        mass_tm[i] = MASS_PREFACTOR * ms->vchi_tm[i] * grad_tm[i];
    }
}

/* === G1 Geometric Coupling (Per-Stella) === */

static void geo_couple_stella(MultiStellaSoup *ms, int s,
                               const float *mass_tp, const float *mass_tm) {
    StellaSite *site = &ms->sites[s];
    int n = ms->mesh->n_sites;
    float cs = ms->coupling_strength;

    /* Chirality mode 1 (coupling weight): T+→T- coupling amplified,
     * T-→T+ coupling suppressed. Reference: genesis_soup.c:775-781. */
    float w_tp_to_tm = 1.0f, w_tm_to_tp = 1.0f;
    if (ms->chirality_mode == 1 && ms->chirality > 0.0f) {
        w_tp_to_tm = 1.0f + ms->chirality;
        w_tm_to_tp = 1.0f - ms->chirality;
        if (w_tm_to_tp < 0.0f) w_tm_to_tp = 0.0f;
    }

    for (int i = 0; i < n; i++) {
        /* T+ perspective: if P+(x_tp) > P-(x_tp), T+ can overwrite T- */
        float pp_tp = ms->pp_at_tp[i];
        float pm_tp = ms->pm_at_tp[i];
        float sum_tp = pp_tp + pm_tp;
        if (sum_tp > 1e-10f) {
            float delta = pp_tp - pm_tp;
            if (delta > 0) {
                float prob = w_tp_to_tm * cs * delta / sum_tp;
                /* Q3c: mass-modulated geometric coupling (Thm 3.1.1) */
                if (ms->mass_geo > 0.0f && mass_tp) {
                    float boost = 1.0f + ms->mass_geo * mass_tp[i];
                    prob *= boost;
                    if (boost > 1.01f) site->mass_geo_boosts++;
                }
                if (prob > 1.0f) prob = 1.0f;
                if (rng_float(site->rng) < prob) {
                    site->tm_data[i] = site->tp_data[i];
                    site->geo_tp_to_tm++;
                }
            }
        }

        /* T- perspective: if P-(x_tm) > P+(x_tm), T- can overwrite T+ */
        float pp_tm = ms->pp_at_tm[i];
        float pm_tm = ms->pm_at_tm[i];
        float sum_tm = pp_tm + pm_tm;
        if (sum_tm > 1e-10f) {
            float delta = pm_tm - pp_tm;
            if (delta > 0) {
                float prob = w_tm_to_tp * cs * delta / sum_tm;
                /* Q3c: mass-modulated geometric coupling (Thm 3.1.1) */
                if (ms->mass_geo > 0.0f && mass_tm) {
                    float boost = 1.0f + ms->mass_geo * mass_tm[i];
                    prob *= boost;
                    if (boost > 1.01f) site->mass_geo_boosts++;
                }
                if (prob > 1.0f) prob = 1.0f;
                if (rng_float(site->rng) < prob) {
                    site->tp_data[i] = site->tm_data[i];
                    site->geo_tm_to_tp++;
                }
            }
        }
    }
}

/* === Coherence Metrics (G1 diagnostic) === */

static double stella_coherence(MultiStellaSoup *ms, int s) {
    int n = ms->mesh->n_sites;
    int match = 0;
    for (int i = 0; i < n; i++)
        if (ms->sites[s].tp_data[i] == ms->sites[s].tm_data[i])
            match++;
    return (double)match / n;
}

static void pressure_zone_coherence(MultiStellaSoup *ms, int s,
                                     double *coh_dominant, double *coh_blocked) {
    int n = ms->mesh->n_sites;
    int dom_match = 0, dom_total = 0;
    int blk_match = 0, blk_total = 0;
    for (int i = 0; i < n; i++) {
        float pr = ms->pp_at_tp[i] / (ms->pp_at_tp[i] + ms->pm_at_tp[i]);
        int match = (ms->sites[s].tp_data[i] == ms->sites[s].tm_data[i]);
        if (pr > 0.5f) { dom_match += match; dom_total++; }
        else            { blk_match += match; blk_total++; }
    }
    *coh_dominant = dom_total > 0 ? (double)dom_match / dom_total : 0;
    *coh_blocked  = blk_total > 0 ? (double)blk_match / blk_total : 0;
}

/* === Create / Seed / Free === */

static MultiStellaSoup *mss_create(int lattice_size, int n_sub,
                                     int prog_size, int max_steps,
                                     double mutation_rate, double cross_rate,
                                     int local_interact, int coupling_mode,
                                     int g1_enabled, float coupling_strength,
                                     float epsilon, uint64_t seed) {
    MultiStellaSoup *ms = calloc(1, sizeof(MultiStellaSoup));
    ms->prog_size = prog_size;
    ms->max_steps = max_steps;
    ms->mutation_rate = mutation_rate;
    ms->cross_rate = cross_rate;
    ms->local_interact = local_interact;
    ms->coupling_mode = coupling_mode;
    ms->g1_enabled = g1_enabled;
    ms->coupling_strength = coupling_strength;
    ms->epsilon = epsilon;
    rng_seed(ms->master_rng, seed);
    rng_seed(ms->metrics_rng, seed + 314159);

    /* Build FCC lattice */
    ms->lattice = fcc_build(lattice_size);
    printf("FCC lattice: L=%d, %d stellae\n", lattice_size, ms->lattice->n_sites);

    /* Build shared mesh (with positions if G1 enabled) */
    printf("Building shared mesh (n_sub=%d)...\n", n_sub);
    ms->mesh = mesh_build(n_sub, g1_enabled);
    printf("  %d sites per tetrahedron (expected %d)\n",
           ms->mesh->n_sites, 2*n_sub*n_sub+2);

    int n_tiles = ms->mesh->n_sites / prog_size;
    if (n_tiles < 2) n_tiles = 2;
    ms->n_tiles_per = n_tiles;
    ms->n_tiles_per_stella = 2 * n_tiles;

    /* Build shared tilings */
    uint64_t til_rng[4];
    rng_seed(til_rng, seed + 1000);
    printf("Building shared tiling (%d tiles per tetra)...\n", n_tiles);
    ms->tp_tiling = tiling_build(ms->mesh, n_tiles, prog_size, til_rng);
    ms->tm_tiling = tiling_build(ms->mesh, n_tiles, prog_size, til_rng);

    /* Precompute pressure (G1) */
    if (g1_enabled) {
        printf("Precomputing pressure fields (Def 0.1.3)...\n");
        precompute_pressure(ms);

        /* Precompute v_χ field (static, depends only on pressure) */
        int n_mesh = ms->mesh->n_sites;
        ms->vchi_tp = malloc(n_mesh * sizeof(float));
        ms->vchi_tm = malloc(n_mesh * sizeof(float));
        ms->mass_tp = malloc(n_mesh * sizeof(float));
        ms->mass_tm = malloc(n_mesh * sizeof(float));
        ms->grad_phi_tp = malloc(n_mesh * sizeof(float));
        ms->grad_phi_tm = malloc(n_mesh * sizeof(float));
        for (int i = 0; i < n_mesh; i++) {
            float sum_tp = ms->pp_at_tp[i] + ms->pm_at_tp[i];
            float sum_tm = ms->pp_at_tm[i] + ms->pm_at_tm[i];
            ms->vchi_tp[i] = sum_tp > 1e-10f ? ms->pp_at_tp[i] / sum_tp : 0.5f;
            ms->vchi_tm[i] = sum_tm > 1e-10f ? ms->pm_at_tm[i] / sum_tm : 0.5f;
            ms->mass_tp[i] = 0.0f;
            ms->mass_tm[i] = 0.0f;
            ms->grad_phi_tp[i] = 0.0f;
            ms->grad_phi_tm[i] = 0.0f;
        }
    } else {
        ms->vchi_tp = NULL; ms->vchi_tm = NULL;
        ms->mass_tp = NULL; ms->mass_tm = NULL;
        ms->grad_phi_tp = NULL; ms->grad_phi_tm = NULL;
    }

    /* Allocate per-stella data */
    int n_fcc = ms->lattice->n_sites;
    ms->sites = calloc(n_fcc, sizeof(StellaSite));
    int n_mesh = ms->mesh->n_sites;

    for (int s = 0; s < n_fcc; s++) {
        ms->sites[s].tp_data = malloc(n_mesh);
        ms->sites[s].tm_data = malloc(n_mesh);
        rng_seed(ms->sites[s].rng, seed + 7919 * (uint64_t)(s + 1));
        for (int i = 0; i < n_mesh; i++) {
            ms->sites[s].tp_data[i] = rng_int(ms->sites[s].rng, Z3);
            ms->sites[s].tm_data[i] = rng_int(ms->sites[s].rng, Z3);
        }
        ms->sites[s].geo_tp_to_tm = 0;
        ms->sites[s].geo_tm_to_tp = 0;
    }

    /* Octahedral interstitials (Mode B) */
    ms->edge_map = calloc(n_fcc * 12, sizeof(int));
    for (int i = 0; i < n_fcc * 12; i++) ms->edge_map[i] = -1;

    int n_edges = 0;
    for (int s = 0; s < n_fcc; s++) {
        for (int d = 0; d < 12; d++) {
            if (ms->edge_map[s * 12 + d] >= 0) continue;
            int nb = ms->lattice->neighbors[s][d];
            if (nb < 0) continue;
            int eid = n_edges++;
            ms->edge_map[s * 12 + d] = eid;
            for (int rd = 0; rd < 12; rd++) {
                if (ms->lattice->neighbors[nb][rd] == s) {
                    ms->edge_map[nb * 12 + rd] = eid;
                    break;
                }
            }
        }
    }
    ms->n_edges = n_edges;

    if (coupling_mode == COUPLING_OCTAHEDRAL) {
        printf("Building %d octahedral interstitials (Mode B)...\n", n_edges);
        uint64_t oct_rng[4];
        rng_seed(oct_rng, seed + 271828);
        ms->oct_data = malloc(n_edges * sizeof(uint8_t *));
        for (int e = 0; e < n_edges; e++) {
            ms->oct_data[e] = malloc(prog_size);
            for (int i = 0; i < prog_size; i++)
                ms->oct_data[e][i] = rng_int(oct_rng, Z3);
        }
    } else {
        ms->oct_data = NULL;
    }

    return ms;
}

static void mss_seed_replicator(MultiStellaSoup *ms, int stella_idx,
                                int n_tiles) {
    static const uint8_t repl[24] = {
        1,2, 1,2, 2,1, 1,1, 0,2, 2,0,
        2,1, 1,1, 0,2, 2,0, 2,0, 1,1
    };
    int ps = ms->prog_size;
    int nts = ms->n_tiles_per_stella;
    uint8_t *buf = malloc(ps);
    memcpy(buf, repl, ps < 24 ? ps : 24);
    if (ps > 24) memset(buf + 24, 0, ps - 24);

    int count = (n_tiles > 0 && n_tiles < nts) ? n_tiles : nts;
    for (int t = 0; t < count; t++)
        stella_tile_write(ms->sites[stella_idx].tp_data,
                          ms->sites[stella_idx].tm_data,
                          ms->tp_tiling, ms->tm_tiling,
                          ms->n_tiles_per, t, buf, ps);
    free(buf);
    printf("Seeded replicator into stella %d (%d/%d tiles, %.1f%%)\n",
           stella_idx, count, nts, 100.0 * count / nts);
}

static void mss_free(MultiStellaSoup *ms) {
    for (int s = 0; s < ms->lattice->n_sites; s++) {
        free(ms->sites[s].tp_data);
        free(ms->sites[s].tm_data);
    }
    free(ms->sites);
    if (ms->oct_data) {
        for (int e = 0; e < ms->n_edges; e++) free(ms->oct_data[e]);
        free(ms->oct_data);
    }
    free(ms->edge_map);
    if (ms->pp_at_tp) free(ms->pp_at_tp);
    if (ms->pm_at_tp) free(ms->pm_at_tp);
    if (ms->pp_at_tm) free(ms->pp_at_tm);
    if (ms->pm_at_tm) free(ms->pm_at_tm);
    tiling_free(ms->tp_tiling); tiling_free(ms->tm_tiling);
    mesh_free(ms->mesh); fcc_free(ms->lattice);
    free(ms);
}

/* === Intra-stella interaction (G2 VM) === */

static void mss_interact_intra(MultiStellaSoup *ms, int s, uint8_t *work) {
    StellaSite *site = &ms->sites[s];
    int nts = ms->n_tiles_per_stella;
    int ps = ms->prog_size;

    int ta = rng_int(site->rng, nts);
    int tb;
    if (ms->local_interact) {
        tb = pick_partner_local(site->rng, ms->tp_tiling, ms->tm_tiling,
                                 ms->n_tiles_per, ta);
    } else {
        tb = rng_int(site->rng, nts - 1);
        if (tb >= ta) tb++;
    }

    stella_tile_read(site->tp_data, site->tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, ta, work, ps);
    stella_tile_read(site->tp_data, site->tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, tb, work + ps, ps);

    execute_tape(work, 2 * ps, ms->max_steps);

    stella_tile_write(site->tp_data, site->tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, ta, work, ps);
    stella_tile_write(site->tp_data, site->tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, tb, work + ps, ps);
}

/* === Inter-stella interactions (G2) === */

static void mss_interact_cross(MultiStellaSoup *ms, int sa, int sb,
                                 uint8_t *work) {
    StellaSite *site_a = &ms->sites[sa];
    StellaSite *site_b = &ms->sites[sb];
    int nts = ms->n_tiles_per_stella;
    int ps = ms->prog_size;

    int ta = rng_int(ms->master_rng, nts);
    int tb = rng_int(ms->master_rng, nts);

    stella_tile_read(site_a->tp_data, site_a->tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, ta, work, ps);
    stella_tile_read(site_b->tp_data, site_b->tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, tb, work + ps, ps);

    execute_tape(work, 2 * ps, ms->max_steps);

    stella_tile_write(site_a->tp_data, site_a->tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, ta, work, ps);
    stella_tile_write(site_b->tp_data, site_b->tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, tb, work + ps, ps);
}

static void mss_interact_cross_oct(MultiStellaSoup *ms, int sa, int nb_dir,
                                     uint8_t *work) {
    int sb = ms->lattice->neighbors[sa][nb_dir];
    if (sb < 0) return;

    int eid = ms->edge_map[sa * 12 + nb_dir];
    if (eid < 0) return;

    int ps = ms->prog_size;
    int nts = ms->n_tiles_per_stella;

    int ta = rng_int(ms->master_rng, nts);
    stella_tile_read(ms->sites[sa].tp_data, ms->sites[sa].tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, ta, work, ps);
    memcpy(work + ps, ms->oct_data[eid], ps);

    execute_tape(work, 2 * ps, ms->max_steps);

    stella_tile_write(ms->sites[sa].tp_data, ms->sites[sa].tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, ta, work, ps);
    memcpy(ms->oct_data[eid], work + ps, ps);

    int tb = rng_int(ms->master_rng, nts);
    memcpy(work, ms->oct_data[eid], ps);
    stella_tile_read(ms->sites[sb].tp_data, ms->sites[sb].tm_data,
                      ms->tp_tiling, ms->tm_tiling,
                      ms->n_tiles_per, tb, work + ps, ps);

    execute_tape(work, 2 * ps, ms->max_steps);

    memcpy(ms->oct_data[eid], work, ps);
    stella_tile_write(ms->sites[sb].tp_data, ms->sites[sb].tm_data,
                       ms->tp_tiling, ms->tm_tiling,
                       ms->n_tiles_per, tb, work + ps, ps);
}

/* === Mutation === */

static void mss_mutate(MultiStellaSoup *ms, int s) {
    StellaSite *site = &ms->sites[s];
    int nts = ms->n_tiles_per_stella;
    int total_trits = nts * ms->prog_size;
    int expected = (int)(total_trits * ms->mutation_rate);

    for (int i = 0; i < expected; i++) {
        int tile = rng_int(site->rng, nts);
        int is_tp = tile < ms->n_tiles_per;
        int local = is_tp ? tile : tile - ms->n_tiles_per;
        uint8_t *data = is_tp ? site->tp_data : site->tm_data;
        const Tiling *t = is_tp ? ms->tp_tiling : ms->tm_tiling;
        int sz = t->tile_size[local];
        if (sz > 0) {
            int site_idx = t->tile_sites[local][rng_int(site->rng, sz)];
            data[site_idx] = rng_int(site->rng, Z3);
        }
    }
}

/* ================================================================
 * Persistent Thread Pool (extended for G1 coupling phase)
 * ================================================================ */

static int g_n_threads = 1;

typedef struct {
    MultiStellaSoup *ms;
    int stella_start;
    int stella_end;
    uint8_t *work;
    /* Per-thread mass work arrays (Q3c: avoid race on shared ms->mass_tp etc.) */
    float *mass_tp;
    float *mass_tm;
    float *grad_phi_tp;
    float *grad_phi_tm;
    pthread_mutex_t *start_mutex;
    pthread_cond_t *start_cond;
    pthread_mutex_t *done_mutex;
    pthread_cond_t *done_cond;
    int *generation;
    int *done_count;
    int my_gen;
    int alive;
} ThreadWorker;

static void *thread_pool_worker(void *arg) {
    ThreadWorker *w = (ThreadWorker *)arg;

    while (1) {
        pthread_mutex_lock(w->start_mutex);
        while (w->my_gen >= *w->generation && w->alive)
            pthread_cond_wait(w->start_cond, w->start_mutex);
        if (!w->alive) { pthread_mutex_unlock(w->start_mutex); break; }
        w->my_gen = *w->generation;
        pthread_mutex_unlock(w->start_mutex);

        MultiStellaSoup *ms = w->ms;
        for (int s = w->stella_start; s < w->stella_end; s++) {
            /* Phase 1: G2 VM interactions + mutation */
            int n_interact = ms->n_tiles_per_stella / 2;
            for (int k = 0; k < n_interact; k++)
                mss_interact_intra(ms, s, w->work);
            if (ms->mutation_rate > 0.0)
                mss_mutate(ms, s);

            /* Phase 2: G1 geometric coupling (if enabled) */
            if (ms->g1_enabled) {
                if (ms->mass_geo > 0.0f)
                    mss_compute_mass(ms, s, w->mass_tp, w->mass_tm,
                                     w->grad_phi_tp, w->grad_phi_tm);
                geo_couple_stella(ms, s, w->mass_tp, w->mass_tm);
            }
        }

        pthread_mutex_lock(w->done_mutex);
        (*w->done_count)++;
        pthread_cond_signal(w->done_cond);
        pthread_mutex_unlock(w->done_mutex);
    }
    return NULL;
}

typedef struct {
    int n_threads;
    pthread_t *threads;
    ThreadWorker *workers;
    uint8_t *work_tapes;
    pthread_mutex_t start_mutex;
    pthread_cond_t start_cond;
    pthread_mutex_t done_mutex;
    pthread_cond_t done_cond;
    int generation;
    int done_count;
} ThreadPool;

static ThreadPool *pool_create(MultiStellaSoup *ms, int n_threads) {
    int n_fcc = ms->lattice->n_sites;
    int nt = n_threads;
    if (nt > n_fcc) nt = n_fcc;
    if (nt < 1) nt = 1;

    ThreadPool *p = calloc(1, sizeof(ThreadPool));
    p->n_threads = nt;
    p->threads = malloc(nt * sizeof(pthread_t));
    p->workers = malloc(nt * sizeof(ThreadWorker));
    p->work_tapes = malloc(nt * 2 * ms->prog_size);
    pthread_mutex_init(&p->start_mutex, NULL);
    pthread_cond_init(&p->start_cond, NULL);
    pthread_mutex_init(&p->done_mutex, NULL);
    pthread_cond_init(&p->done_cond, NULL);
    p->generation = 0;
    p->done_count = 0;

    int per = n_fcc / nt;
    int rem = n_fcc % nt;
    int start = 0;

    for (int t = 0; t < nt; t++) {
        int count = per + (t < rem ? 1 : 0);
        ThreadWorker *w = &p->workers[t];
        w->ms = ms;
        w->stella_start = start;
        w->stella_end = start + count;
        w->work = p->work_tapes + t * 2 * ms->prog_size;
        /* Per-thread mass work arrays (Q3c thread safety) */
        if (ms->mass_geo > 0.0f && ms->g1_enabled) {
            int nm = ms->mesh->n_sites;
            w->mass_tp = malloc(nm * sizeof(float));
            w->mass_tm = malloc(nm * sizeof(float));
            w->grad_phi_tp = malloc(nm * sizeof(float));
            w->grad_phi_tm = malloc(nm * sizeof(float));
        } else {
            w->mass_tp = NULL; w->mass_tm = NULL;
            w->grad_phi_tp = NULL; w->grad_phi_tm = NULL;
        }
        w->start_mutex = &p->start_mutex;
        w->start_cond = &p->start_cond;
        w->done_mutex = &p->done_mutex;
        w->done_cond = &p->done_cond;
        w->generation = &p->generation;
        w->done_count = &p->done_count;
        w->my_gen = 0;
        w->alive = 1;
        start += count;
        pthread_create(&p->threads[t], NULL, thread_pool_worker, w);
    }

    return p;
}

static void pool_run_epoch(ThreadPool *p) {
    pthread_mutex_lock(&p->start_mutex);
    p->done_count = 0;
    p->generation++;
    pthread_cond_broadcast(&p->start_cond);
    pthread_mutex_unlock(&p->start_mutex);

    pthread_mutex_lock(&p->done_mutex);
    while (p->done_count < p->n_threads)
        pthread_cond_wait(&p->done_cond, &p->done_mutex);
    pthread_mutex_unlock(&p->done_mutex);
}

static void pool_destroy(ThreadPool *p) {
    pthread_mutex_lock(&p->start_mutex);
    for (int t = 0; t < p->n_threads; t++)
        p->workers[t].alive = 0;
    p->generation++;
    pthread_cond_broadcast(&p->start_cond);
    pthread_mutex_unlock(&p->start_mutex);

    for (int t = 0; t < p->n_threads; t++)
        pthread_join(p->threads[t], NULL);

    pthread_mutex_destroy(&p->start_mutex);
    pthread_cond_destroy(&p->start_cond);
    pthread_mutex_destroy(&p->done_mutex);
    pthread_cond_destroy(&p->done_cond);
    free(p->work_tapes); free(p->workers); free(p->threads); free(p);
}

/* Three-phase epoch: parallel intra (G2+G1) + serial inter (G2) */
static void mss_epoch(MultiStellaSoup *ms, ThreadPool *pool) {
    int n_fcc = ms->lattice->n_sites;
    int ps = ms->prog_size;

    /* Phase 1+2: Intra-stella VM + mutation + G1 coupling (parallel) */
    pool_run_epoch(pool);

    /* Phase 3: Inter-stella coupling (serial, uses master RNG) */
    double expected_cross = ms->cross_rate * n_fcc;
    int n_cross = (int)expected_cross;
    double frac = expected_cross - n_cross;
    if (frac > 0.0 && rng_float(ms->master_rng) < frac)
        n_cross++;
    uint8_t work[2 * ps];

    for (int k = 0; k < n_cross; k++) {
        int sa = rng_int(ms->master_rng, n_fcc);
        int nb_idx = rng_int(ms->master_rng, 12);
        int sb = ms->lattice->neighbors[sa][nb_idx];
        if (sb >= 0) {
            if (ms->coupling_mode == COUPLING_OCTAHEDRAL)
                mss_interact_cross_oct(ms, sa, nb_idx, work);
            else
                mss_interact_cross(ms, sa, sb, work);
        }
    }

    ms->epoch++;
}

/* ================================================================
 * Metrics & Replicator Check
 * ================================================================ */

static int prog_size_global;
static int prog_cmp(const void *a, const void *b) {
    return memcmp(a, b, prog_size_global);
}

static int is_trivial(const uint8_t *data, int size) {
    for (int i = 1; i < size; i++)
        if (data[i] != data[0]) return 0;
    return 1;
}

typedef struct {
    int unique;
    int top_count;
    double trit_entropy;
    int total_programs;
} Metrics;

static Metrics mss_metrics(MultiStellaSoup *ms) {
    Metrics m = {0};
    int n_fcc = ms->lattice->n_sites;
    int nts = ms->n_tiles_per_stella;
    int ps = ms->prog_size;
    int total = n_fcc * nts;
    m.total_programs = total;

    int sample_n = total < 2000 ? total : 2000;
    uint8_t *sample = malloc(sample_n * ps);

    for (int i = 0; i < sample_n; i++) {
        int s = rng_int(ms->metrics_rng, n_fcc);
        int t = rng_int(ms->metrics_rng, nts);
        stella_tile_read(ms->sites[s].tp_data, ms->sites[s].tm_data,
                          ms->tp_tiling, ms->tm_tiling,
                          ms->n_tiles_per, t, sample + i * ps, ps);
    }

    prog_size_global = ps;
    qsort(sample, sample_n, ps, prog_cmp);
    int unique = 1, run = 1, max_run = 1;
    for (int i = 1; i < sample_n; i++) {
        if (memcmp(sample + i*ps, sample + (i-1)*ps, ps) == 0) {
            run++; if (run > max_run) max_run = run;
        } else { unique++; run = 1; }
    }
    m.unique = unique;
    m.top_count = max_run;

    long counts[Z3] = {0};
    int tot_trits = sample_n * ps;
    for (int i = 0; i < tot_trits; i++) counts[sample[i]]++;
    for (int t = 0; t < Z3; t++) {
        if (counts[t] > 0) {
            double p = (double)counts[t] / tot_trits;
            m.trit_entropy -= p * log2(p);
        }
    }

    free(sample);
    return m;
}

static int mss_check_replicators(MultiStellaSoup *ms, int sample_size) {
    int ps = ms->prog_size;
    int tape_len = 2 * ps;
    uint8_t *tape = malloc(tape_len);
    uint8_t *orig = malloc(ps);
    int perfect = 0, perfect_nt = 0, partial = 0;
    int n_fcc = ms->lattice->n_sites;
    int nts = ms->n_tiles_per_stella;

    for (int i = 0; i < sample_size; i++) {
        int s = rng_int(ms->metrics_rng, n_fcc);
        int tile = rng_int(ms->metrics_rng, nts);
        stella_tile_read(ms->sites[s].tp_data, ms->sites[s].tm_data,
                          ms->tp_tiling, ms->tm_tiling,
                          ms->n_tiles_per, tile, orig, ps);

        memcpy(tape, orig, ps);
        memset(tape + ps, 0, ps);
        execute_tape(tape, tape_len, ms->max_steps);

        if (memcmp(tape, orig, ps) == 0 && memcmp(tape + ps, orig, ps) == 0) {
            perfect++;
            if (!is_trivial(orig, ps)) perfect_nt++;
            continue;
        }

        memcpy(tape, orig, ps);
        for (int j = 0; j < ps; j++) tape[ps + j] = rng_int(ms->metrics_rng, Z3);
        execute_tape(tape, tape_len, ms->max_steps);

        if (memcmp(tape, orig, ps) == 0 && memcmp(tape + ps, orig, ps) == 0) {
            perfect++;
            if (!is_trivial(orig, ps)) perfect_nt++;
        } else if (memcmp(tape, orig, ps) == 0 || memcmp(tape + ps, orig, ps) == 0) {
            partial++;
        }
    }

    free(tape); free(orig);

    if (perfect_nt > 0)
        printf("  REPLICATORS: %d nontrivial, %d trivial, %d partial (of %d)\n",
               perfect_nt, perfect - perfect_nt, partial, sample_size);
    else if (perfect > 0)
        printf("  trivial: %d, partial: %d (of %d)\n", perfect, partial, sample_size);
    else if (partial > 0)
        printf("  partial: %d (of %d)\n", partial, sample_size);

    return perfect_nt;
}

/* ================================================================
 * Per-Stella Census (extended with coherence)
 * ================================================================ */

static int hamming_distance(const uint8_t *a, const uint8_t *b, int n) {
    int d = 0;
    for (int i = 0; i < n; i++)
        if (a[i] != b[i]) d++;
    return d;
}

static int mss_per_stella_census(MultiStellaSoup *ms, int verbose,
                                  const int *dist, int track_stella) {
    int n_fcc = ms->lattice->n_sites;
    int nts = ms->n_tiles_per_stella;
    int ps = ms->prog_size;
    int htol = ms->hamming_tolerance;
    int stellae_with_rep = 0;
    int *colonized = calloc(n_fcc, sizeof(int));

    if (verbose)
        printf("  CENSUS epoch %ld:", ms->epoch);

    int tracked_rep = -1;
    int *rep_tp = calloc(n_fcc, sizeof(int));   /* per-stella T+ replicators */
    int *rep_tm = calloc(n_fcc, sizeof(int));   /* per-stella T- replicators */

    /* W2b: when hamming_tolerance > 0, also count near-replicators */
    int *near_tp = htol > 0 ? calloc(n_fcc, sizeof(int)) : NULL;
    int *near_tm = htol > 0 ? calloc(n_fcc, sizeof(int)) : NULL;
    long total_hamming_sum = 0;
    long total_hamming_count = 0;

    for (int s = 0; s < n_fcc; s++) {
        int nt_rep = 0, nt_rep_tp = 0, nt_rep_tm = 0;
        int nt_near = 0, nt_near_tp = 0, nt_near_tm = 0;
        uint8_t *tape = malloc(2 * ps);
        uint8_t *orig = malloc(ps);
        for (int t = 0; t < nts; t++) {
            stella_tile_read(ms->sites[s].tp_data, ms->sites[s].tm_data,
                              ms->tp_tiling, ms->tm_tiling,
                              ms->n_tiles_per, t, orig, ps);
            memcpy(tape, orig, ps);
            memset(tape + ps, 0, ps);
            execute_tape(tape, 2 * ps, ms->max_steps);

            int hd_self = hamming_distance(tape, orig, ps);
            int hd_copy = hamming_distance(tape + ps, orig, ps);
            int hd_total = hd_self + hd_copy;

            if (hd_self == 0 && hd_copy == 0 && !is_trivial(orig, ps)) {
                /* Strict replicator (exact match) */
                nt_rep++;
                if (t < ms->n_tiles_per) nt_rep_tp++;
                else nt_rep_tm++;
            }
            if (htol > 0 && hd_total <= htol && !is_trivial(orig, ps)) {
                /* Near-replicator (within Hamming tolerance) */
                nt_near++;
                if (t < ms->n_tiles_per) nt_near_tp++;
                else nt_near_tm++;
            }
            if (htol > 0 && !is_trivial(orig, ps)) {
                total_hamming_sum += hd_total;
                total_hamming_count++;
            }
        }
        free(tape); free(orig);
        rep_tp[s] = nt_rep_tp;
        rep_tm[s] = nt_rep_tm;
        if (near_tp) near_tp[s] = nt_near_tp;
        if (near_tm) near_tm[s] = nt_near_tm;
        if (nt_rep > 0) { stellae_with_rep++; colonized[s] = 1; }
        if (s == track_stella) tracked_rep = nt_rep;

        if (verbose > 1) {
            if (ms->g1_enabled) {
                double coh = stella_coherence(ms, s);
                if (htol > 0) {
                    if (dist)
                        printf("  Stella %3d (d=%d): %d/%d (%.1f%%) near=%d coh=%.3f [T+:%d T-:%d]\n",
                               s, dist[s], nt_rep, nts, 100.0*nt_rep/nts, nt_near, coh,
                               nt_rep_tp, nt_rep_tm);
                    else
                        printf("  Stella %3d: %d/%d (%.1f%%) near=%d coh=%.3f [T+:%d T-:%d]\n",
                               s, nt_rep, nts, 100.0*nt_rep/nts, nt_near, coh,
                               nt_rep_tp, nt_rep_tm);
                } else {
                    if (dist)
                        printf("  Stella %3d (d=%d): %d/%d (%.1f%%) coh=%.3f [T+:%d T-:%d]\n",
                               s, dist[s], nt_rep, nts, 100.0*nt_rep/nts, coh,
                               nt_rep_tp, nt_rep_tm);
                    else
                        printf("  Stella %3d: %d/%d (%.1f%%) coh=%.3f [T+:%d T-:%d]\n",
                               s, nt_rep, nts, 100.0*nt_rep/nts, coh,
                               nt_rep_tp, nt_rep_tm);
                }
            } else {
                if (dist)
                    printf("  Stella %3d (d=%d): %d / %d (%.1f%%) [T+:%d T-:%d]\n",
                           s, dist[s], nt_rep, nts, 100.0 * nt_rep / nts,
                           nt_rep_tp, nt_rep_tm);
                else
                    printf("  Stella %3d: %d / %d (%.1f%%) [T+:%d T-:%d]\n",
                           s, nt_rep, nts, 100.0 * nt_rep / nts,
                           nt_rep_tp, nt_rep_tm);
            }
        }
    }

    if (verbose && tracked_rep >= 0)
        printf(" stella%d=%d/%d(%.1f%%)",
               track_stella, tracked_rep, nts, 100.0 * tracked_rep / nts);
    if (verbose)
        printf(" %d/%d stellae colonized\n", stellae_with_rep, n_fcc);

    if (verbose && dist) {
        int max_d = 0;
        for (int s = 0; s < n_fcc; s++)
            if (dist[s] > max_d) max_d = dist[s];
        printf("  WAVEFRONT:");
        for (int d = 0; d <= max_d; d++) {
            int total_at_d = 0, col_at_d = 0;
            int tp_at_d = 0, tm_at_d = 0;
            for (int s = 0; s < n_fcc; s++) {
                if (dist[s] != d) continue;
                total_at_d++;
                if (colonized[s]) col_at_d++;
                tp_at_d += rep_tp[s];
                tm_at_d += rep_tm[s];
            }
            printf(" d%d=%d/%d[+%d-%d]", d, col_at_d, total_at_d,
                   tp_at_d, tm_at_d);
        }
        printf("\n");
        if (htol > 0) {
            printf("  NEAR_REP(h<=%d):", htol);
            for (int d = 0; d <= max_d; d++) {
                int ntp = 0, ntm = 0;
                for (int s = 0; s < n_fcc; s++) {
                    if (dist[s] != d) continue;
                    ntp += near_tp[s];
                    ntm += near_tm[s];
                }
                printf(" d%d=[+%d-%d]", d, ntp, ntm);
            }
            double mean_hd = total_hamming_count > 0
                ? (double)total_hamming_sum / total_hamming_count : 0;
            printf(" mean_hd=%.2f/%d\n", mean_hd, 2 * ps);
        }
    }

    free(colonized);
    free(rep_tp);
    free(rep_tm);
    free(near_tp);
    free(near_tm);
    return stellae_with_rep;
}

/* ================================================================
 * Top-N Program Dump (Q4 analysis: replicator species comparison)
 * ================================================================ */

static void mss_dump_top_programs(MultiStellaSoup *ms, int top_n) {
    int n_fcc = ms->lattice->n_sites;
    int nts = ms->n_tiles_per_stella;
    int ps = ms->prog_size;
    int total = n_fcc * nts;

    /* Collect ALL programs */
    uint8_t *all_progs = malloc(total * ps);
    int idx = 0;
    for (int s = 0; s < n_fcc; s++) {
        for (int t = 0; t < nts; t++) {
            stella_tile_read(ms->sites[s].tp_data, ms->sites[s].tm_data,
                              ms->tp_tiling, ms->tm_tiling,
                              ms->n_tiles_per, t, all_progs + idx * ps, ps);
            idx++;
        }
    }

    /* Sort to group identical programs */
    prog_size_global = ps;
    qsort(all_progs, total, ps, prog_cmp);

    /* Count runs and collect top-N */
    typedef struct { int count; int first_idx; } ProgEntry;
    int n_unique = 0;
    int cap = 4096;
    ProgEntry *entries = malloc(cap * sizeof(ProgEntry));

    int run = 1;
    for (int i = 1; i <= total; i++) {
        if (i < total && memcmp(all_progs + i*ps, all_progs + (i-1)*ps, ps) == 0) {
            run++;
        } else {
            if (n_unique >= cap) { cap *= 2; entries = realloc(entries, cap * sizeof(ProgEntry)); }
            entries[n_unique].count = run;
            entries[n_unique].first_idx = i - run;
            n_unique++;
            run = 1;
        }
    }

    /* Sort entries by count descending */
    for (int i = 0; i < top_n && i < n_unique; i++) {
        for (int j = i + 1; j < n_unique; j++) {
            if (entries[j].count > entries[i].count) {
                ProgEntry tmp = entries[i];
                entries[i] = entries[j];
                entries[j] = tmp;
            }
        }
    }

    int show = top_n < n_unique ? top_n : n_unique;
    printf("\n  TOP-%d PROGRAMS (epoch %ld, %d unique / %d total):\n", show, ms->epoch, n_unique, total);

    uint8_t *tape = malloc(2 * ps);

    for (int i = 0; i < show; i++) {
        uint8_t *prog = all_progs + entries[i].first_idx * ps;

        /* Check replicator status */
        memcpy(tape, prog, ps);
        memset(tape + ps, 0, ps);
        execute_tape(tape, 2 * ps, ms->max_steps);
        int self_preserved = (memcmp(tape, prog, ps) == 0);
        int copy_made = (memcmp(tape + ps, prog, ps) == 0);
        int trivial = is_trivial(prog, ps);

        const char *status;
        if (self_preserved && copy_made && !trivial) status = "REPLICATOR";
        else if (self_preserved && copy_made && trivial) status = "trivial";
        else if (self_preserved || copy_made) status = "partial";
        else status = "inert";

        printf("    #%d (%d copies, %.1f%%) [%s]:",
               i + 1, entries[i].count, 100.0 * entries[i].count / total, status);

        /* Decode instructions */
        for (int j = 0; j + 1 < ps; j += 2) {
            int op = prog[j] * 3 + prog[j + 1];
            printf(" %s", OP_NAMES[op]);
        }

        /* Also print raw trits for exact comparison */
        printf("  | trits:");
        for (int j = 0; j < ps; j++) printf("%d", prog[j]);
        printf("\n");

        /* Instruction profile */
        int op_counts[9] = {0};
        for (int j = 0; j + 1 < ps; j += 2) {
            int op = prog[j] * 3 + prog[j + 1];
            op_counts[op]++;
        }
        printf("      profile:");
        for (int op = 0; op < 9; op++) {
            if (op_counts[op] > 0)
                printf(" %s=%d", OP_NAMES[op], op_counts[op]);
        }
        printf("\n");
    }

    free(tape);
    free(entries);
    free(all_progs);
}

/* ================================================================
 * Main
 * ================================================================ */

static void usage(const char *prog) {
    printf("G1+G2 Combined Multi-Stella FCC Lattice Soup\n");
    printf("Usage: %s [options]\n\n", prog);
    printf("  --lattice-size L       FCC box size, L^3/2 stellae (default: %d)\n", DEF_LATTICE_SIZE);
    printf("  --n-sub N              Subdivisions per edge per stella (default: %d)\n", DEF_N_SUB);
    printf("  --prog-size N          Trits per tile/program (default: %d)\n", DEF_PROG_SIZE);
    printf("  --max-steps N          Max VM steps (default: %d)\n", DEF_MAX_STEPS);
    printf("  --epochs N             Epochs to run (default: %ld)\n", DEF_EPOCHS);
    printf("  --mutation-rate F      Per-trit mutation rate (default: 0.001)\n");
    printf("  --cross-rate F         Inter-stella interaction rate (default: %.2f)\n", DEF_CROSS_RATE);
    printf("  --global               Global random pairing within stella\n");
    printf("  --coupling-mode M      Inter-stella: direct or octahedral\n");
    printf("\n  G1 Geometric Coupling (Def 0.1.3):\n");
    printf("  --g1                   Enable G1 geometric coupling\n");
    printf("  --coupling-strength F  G1 coupling probability multiplier (default: 0.5)\n");
    printf("  --epsilon F            Pressure regularization (default: 0.1)\n");
    printf("  --chirality F          T+ pressure asymmetry, 0=symmetric (default: 0)\n");
    printf("  --chirality-mode N     0=pressure-asymmetry, 1=coupling-weight (default: 0)\n");
    printf("  --mass-geo F           Mass-geometric coupling strength, Q3c (default: 0=off)\n");
    printf("\n  Other:\n");
    printf("  --log-interval N       (default: %d)\n", DEF_LOG_INTERVAL);
    printf("  --check-interval N     (default: %d)\n", DEF_CHECK_INTERVAL);
    printf("  --census-interval N    Per-stella census (default: %d, 0=off)\n", DEF_CENSUS_INTERVAL);
    printf("  --census-fast N        Census after first replicator (default: 0=same)\n");
    printf("  --seed-replicator      Plant known replicator in stella 0\n");
    printf("  --seed-stella N        Which stella to seed (default: 0)\n");
    printf("  --seed N\n");
    printf("  --threads N            Thread pool size (default: 16)\n");
    printf("  --dump-top N           Dump top-N programs at census intervals (default: 0=off)\n");
    printf("  --hamming-tolerance N  Near-replicator Hamming distance (default: 0=strict)\n");
}

int main(int argc, char *argv[]) {
    setvbuf(stdout, NULL, _IOLBF, 0);

    int lattice_size = DEF_LATTICE_SIZE;
    int n_sub = DEF_N_SUB;
    int prog_size = DEF_PROG_SIZE;
    int max_steps = DEF_MAX_STEPS;
    long epochs = DEF_EPOCHS;
    double mutation_rate = 0.001;
    double cross_rate = DEF_CROSS_RATE;
    int global_mode = 0;
    int coupling_mode = COUPLING_DIRECT;
    int log_interval = DEF_LOG_INTERVAL;
    int check_interval = DEF_CHECK_INTERVAL;
    int census_interval = DEF_CENSUS_INTERVAL;
    int census_fast = 0;
    int seed_replicator = 0;
    int seed_n_tiles = 0;
    int seed_stella = 0;
    uint64_t seed = (uint64_t)time(NULL);
    int n_threads = 0;

    int dump_top = 0;
    int hamming_tolerance = 0;

    /* G1 parameters */
    int g1_enabled = 0;
    float coupling_strength = 0.5f;
    float epsilon = 0.1f;
    float chirality = 0.0f;
    int chirality_mode = 0;
    float mass_geo = 0.0f;

    static struct option long_options[] = {
        {"lattice-size",     required_argument, 0, 'L'},
        {"n-sub",            required_argument, 0, 'n'},
        {"prog-size",        required_argument, 0, 'p'},
        {"max-steps",        required_argument, 0, 'm'},
        {"epochs",           required_argument, 0, 'e'},
        {"mutation-rate",    required_argument, 0, 'r'},
        {"cross-rate",       required_argument, 0, 'x'},
        {"global",           no_argument,       0, 'G'},
        {"coupling-mode",    required_argument, 0, 'M'},
        {"g1",               no_argument,       0, 'g'},
        {"coupling-strength",required_argument, 0, 'k'},
        {"epsilon",          required_argument, 0, 'E'},
        {"log-interval",     required_argument, 0, 'l'},
        {"check-interval",   required_argument, 0, 'c'},
        {"census-interval",  required_argument, 0, 'C'},
        {"census-fast",      required_argument, 0, 'F'},
        {"seed-replicator",  no_argument,       0, 'R'},
        {"seed-single-tile", no_argument,       0, '1'},
        {"seed-n-tiles",     required_argument, 0, 'N'},
        {"seed-stella",      required_argument, 0, 'Z'},
        {"seed",             required_argument, 0, 'S'},
        {"threads",          required_argument, 0, 'T'},
        {"dump-top",         required_argument, 0, 'D'},
        {"chirality",        required_argument, 0, 'X'},
        {"chirality-mode",   required_argument, 0, 'Y'},
        {"hamming-tolerance",required_argument, 0, 'H'},
        {"mass-geo",         required_argument, 0, 'W'},
        {"help",             no_argument,       0, 'h'},
        {0, 0, 0, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "hL:n:p:m:e:r:x:GM:gk:E:l:c:C:F:R1N:Z:S:T:D:X:Y:H:W:",
                               long_options, NULL)) != -1) {
        switch (opt) {
        case 'L': lattice_size = atoi(optarg); break;
        case 'n': n_sub = atoi(optarg); break;
        case 'p': prog_size = atoi(optarg); break;
        case 'm': max_steps = atoi(optarg); break;
        case 'e': epochs = atol(optarg); break;
        case 'r': mutation_rate = atof(optarg); break;
        case 'x': cross_rate = atof(optarg); break;
        case 'G': global_mode = 1; break;
        case 'M':
            if (strcmp(optarg, "direct") == 0) coupling_mode = COUPLING_DIRECT;
            else if (strcmp(optarg, "octahedral") == 0) coupling_mode = COUPLING_OCTAHEDRAL;
            else { fprintf(stderr, "Error: --coupling-mode must be 'direct' or 'octahedral'\n"); return 1; }
            break;
        case 'g': g1_enabled = 1; break;
        case 'k': coupling_strength = (float)atof(optarg); break;
        case 'E': epsilon = (float)atof(optarg); break;
        case 'l': log_interval = atoi(optarg); break;
        case 'c': check_interval = atoi(optarg); break;
        case 'C': census_interval = atoi(optarg); break;
        case 'F': census_fast = atoi(optarg); break;
        case 'R': seed_replicator = 1; break;
        case '1': seed_n_tiles = 1; seed_replicator = 1; break;
        case 'N': seed_n_tiles = atoi(optarg); seed_replicator = 1; break;
        case 'Z': seed_stella = atoi(optarg); break;
        case 'S': seed = (uint64_t)atol(optarg); break;
        case 'T': n_threads = atoi(optarg); break;
        case 'D': dump_top = atoi(optarg); break;
        case 'H': hamming_tolerance = atoi(optarg); break;
        case 'W': mass_geo = (float)atof(optarg); break;
        case 'X': chirality = (float)atof(optarg); break;
        case 'Y': chirality_mode = atoi(optarg); break;
        case 'h': usage(argv[0]); return 0;
        default:  usage(argv[0]); return 1;
        }
    }

    if (lattice_size % 2 != 0) {
        fprintf(stderr, "Error: lattice-size must be even\n");
        return 1;
    }

    if (n_threads <= 0) n_threads = 16;
    g_n_threads = n_threads;

    printf("G1+G2 Combined Multi-Stella FCC Lattice Soup\n");
    printf("============================================================\n");
    printf("Geometry:       dS = T+ u T- at each FCC vertex (Thm 0.0.6)\n");

    MultiStellaSoup *ms = mss_create(lattice_size, n_sub, prog_size,
                                       max_steps, mutation_rate, cross_rate,
                                       !global_mode, coupling_mode,
                                       g1_enabled, coupling_strength,
                                       epsilon, seed);
    ms->chirality = chirality;
    ms->chirality_mode = chirality_mode;
    ms->hamming_tolerance = hamming_tolerance;
    ms->mass_geo = mass_geo;

    /* Re-precompute pressure if chirality is non-zero (precompute_pressure
     * was already called in mss_create but without chirality set) */
    if (g1_enabled && chirality > 0.0f) {
        printf("Recomputing pressure fields with chirality=%.4f (mode=%d)...\n",
               chirality, chirality_mode);
        free(ms->pp_at_tp); free(ms->pm_at_tp);
        free(ms->pp_at_tm); free(ms->pm_at_tm);
        precompute_pressure(ms);
        /* Recompute v_χ with updated pressure */
        int n_mesh = ms->mesh->n_sites;
        for (int i = 0; i < n_mesh; i++) {
            float sum_tp = ms->pp_at_tp[i] + ms->pm_at_tp[i];
            float sum_tm = ms->pp_at_tm[i] + ms->pm_at_tm[i];
            ms->vchi_tp[i] = sum_tp > 1e-10f ? ms->pp_at_tp[i] / sum_tp : 0.5f;
            ms->vchi_tm[i] = sum_tm > 1e-10f ? ms->pm_at_tm[i] / sum_tm : 0.5f;
        }
    }

    int n_fcc = ms->lattice->n_sites;
    int total_tiles = n_fcc * ms->n_tiles_per_stella;
    int track_stella = (seed_n_tiles > 0) ? seed_stella : -1;

    int *fcc_dist = NULL;
    if (seed_replicator) {
        if (seed_stella < 0 || seed_stella >= n_fcc) {
            fprintf(stderr, "Error: --seed-stella %d out of range [0, %d)\n",
                    seed_stella, n_fcc);
            return 1;
        }
        mss_seed_replicator(ms, seed_stella, seed_n_tiles);
        fcc_dist = fcc_distances(ms->lattice, seed_stella);
        printf("FCC distances from stella %d:", seed_stella);
        for (int s = 0; s < n_fcc; s++) printf(" %d", fcc_dist[s]);
        printf("\n");
    }

    ThreadPool *pool = pool_create(ms, g_n_threads);

    printf("Stellae:        %d (FCC lattice L=%d)\n", n_fcc, lattice_size);
    printf("Sites/tetra:    %d\n", ms->mesh->n_sites);
    printf("Tiles/stella:   %d (%d per tetra)\n",
           ms->n_tiles_per_stella, ms->n_tiles_per);
    printf("Total tiles:    %d (across all stellae)\n", total_tiles);
    printf("Prog size:      %d trits (%d instructions)\n", prog_size, prog_size/2);
    printf("Max steps:      %d\n", max_steps);
    printf("Mutation rate:  %.4f\n", mutation_rate);
    double expected_cross_hdr = cross_rate * n_fcc;
    printf("Cross rate:     %.4f (%.2f inter-stella interactions/epoch)\n",
           cross_rate, expected_cross_hdr);
    printf("Coupling mode:  %s\n",
           coupling_mode == COUPLING_OCTAHEDRAL
               ? "octahedral (Mode B)" : "direct (Mode A)");
    if (coupling_mode == COUPLING_OCTAHEDRAL)
        printf("Oct interstitials: %d\n", ms->n_edges);
    printf("Pairing:        %s (within stella)\n",
           global_mode ? "global random" : "local neighbors");
    if (g1_enabled) {
        printf("G1 coupling:    ENABLED (strength=%.3f, epsilon=%.3f)\n",
               coupling_strength, epsilon);
        if (mass_geo > 0.0f)
            printf("Mass-geo:       %.3f (Q3c: Thm 3.1.1 mass-boosted coupling)\n",
                   mass_geo);
        if (chirality > 0.0f) {
            const char *cm[] = {"pressure-asymmetry", "coupling-weight"};
            printf("Chirality:      %.4f (%s)\n",
                   chirality, cm[chirality_mode]);
        }
    } else {
        printf("G1 coupling:    disabled (G2-only mode)\n");
    }
    if (census_interval > 0)
        printf("Census interval: %d\n", census_interval);
    if (hamming_tolerance > 0)
        printf("Hamming tolerance: %d (near-replicator threshold)\n", hamming_tolerance);
    printf("Epochs:         %ld\n", epochs);
    printf("Seed:           %llu\n", (unsigned long long)seed);
    printf("Threads:        %d (pthreads)\n", g_n_threads);
    printf("============================================================\n\n");

    /* Header line */
    if (g1_enabled)
        printf("%10s | %6s | %5s | %7s | %5s | %7s | Notes\n",
               "Epoch", "Uniq*", "Top*", "H(trit)", "Coh", "GeoCoup");
    else
        printf("%10s | %6s | %5s | %7s | %6s | Notes\n",
               "Epoch", "Uniq*", "Top*", "H(trit)", "Progs");
    printf("------------------------------------------------------------------\n");
    printf("  * Uniq/Top from sample of min(2000, total)\n\n");

    int total_nt_replicators = 0;
    int active_census_interval = census_interval;
    struct timespec t_start;
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    for (long e = 0; e < epochs; e++) {
        mss_epoch(ms, pool);

        if (ms->epoch % log_interval == 0) {
            Metrics m = mss_metrics(ms);

            if (g1_enabled) {
                /* Compute mean coherence across all stellae */
                double total_coh = 0;
                for (int s = 0; s < n_fcc; s++)
                    total_coh += stella_coherence(ms, s);
                double mean_coh = total_coh / n_fcc;

                /* Aggregate G1 coupling stats */
                long geo_total = 0;
                for (int s = 0; s < n_fcc; s++) {
                    geo_total += ms->sites[s].geo_tp_to_tm +
                                 ms->sites[s].geo_tm_to_tp;
                }

                printf("%10ld | %6d | %5d | %7.4f | %.3f | %7ld | ",
                       ms->epoch, m.unique, m.top_count, m.trit_entropy,
                       mean_coh, geo_total);
            } else {
                printf("%10ld | %6d | %5d | %7.4f | %6d | ",
                       ms->epoch, m.unique, m.top_count, m.trit_entropy,
                       m.total_programs);
            }

            if (ms->epoch % check_interval == 0) {
                int nt = mss_check_replicators(ms, 200);
                if (nt > 0 && total_nt_replicators == 0) {
                    printf("\n*** NONTRIVIAL REPLICATORS FOUND ***");
                    if (census_fast > 0) {
                        active_census_interval = census_fast;
                        printf(" (census -> %d)", census_fast);
                    }
                }
                total_nt_replicators += nt;
            }
            printf("\n");

            if (active_census_interval > 0 && ms->epoch % active_census_interval == 0) {
                mss_per_stella_census(ms, 2, fcc_dist, track_stella);
                if (dump_top > 0)
                    mss_dump_top_programs(ms, dump_top);
            }

            if (ms->epoch % (check_interval * 10) == 0 && ms->epoch > 0)
                printf("\n");
        }
    }

    struct timespec t_end;
    clock_gettime(CLOCK_MONOTONIC, &t_end);
    double elapsed = (t_end.tv_sec - t_start.tv_sec) +
                     (t_end.tv_nsec - t_start.tv_nsec) * 1e-9;

    printf("\nCompleted %ld epochs in %.1fs (%.0f epochs/sec)\n",
           epochs, elapsed, epochs / elapsed);

    /* === Final Report === */
    printf("\n============================================================\n");
    printf("Final Report\n");
    printf("============================================================\n");
    Metrics m = mss_metrics(ms);
    printf("Stellae:          %d\n", n_fcc);
    printf("Total tiles:      %d\n", total_tiles);
    printf("Sample unique:    %d / 2000\n", m.unique);
    printf("Sample top count: %d\n", m.top_count);
    printf("Trit entropy:     %.4f (max = 1.5850)\n", m.trit_entropy);

    if (g1_enabled) {
        printf("\n--- G1 Geometric Coupling ---\n");
        long total_tp_to_tm = 0, total_tm_to_tp = 0;
        for (int s = 0; s < n_fcc; s++) {
            total_tp_to_tm += ms->sites[s].geo_tp_to_tm;
            total_tm_to_tp += ms->sites[s].geo_tm_to_tp;
        }
        long total_mg_boosts = 0;
        for (int s = 0; s < n_fcc; s++)
            total_mg_boosts += ms->sites[s].mass_geo_boosts;
        printf("Total T+->T- transfers: %ld\n", total_tp_to_tm);
        printf("Total T-->T+ transfers: %ld\n", total_tm_to_tp);
        if (mass_geo > 0.0f)
            printf("Mass-geo boosts:        %ld\n", total_mg_boosts);
        printf("Directional bias:       %.3f (1.0 = pure T+->T-)\n",
               (total_tp_to_tm + total_tm_to_tp) > 0 ?
               (double)total_tp_to_tm / (total_tp_to_tm + total_tm_to_tp) : 0.5);

        printf("\nPer-stella coherence:\n");
        double total_coh = 0;
        for (int s = 0; s < n_fcc; s++) {
            double coh = stella_coherence(ms, s);
            double coh_dom, coh_blk;
            pressure_zone_coherence(ms, s, &coh_dom, &coh_blk);
            printf("  Stella %3d: coh=%.3f (dominant=%.3f, blocked=%.3f)\n",
                   s, coh, coh_dom, coh_blk);
            total_coh += coh;
        }
        printf("  Mean coherence: %.3f\n", total_coh / n_fcc);
    }

    if (total_nt_replicators > 0)
        printf("\nNontrivial self-replicators detected!\n");
    else
        printf("\nNo nontrivial self-replicators detected.\n");

    printf("\nPer-stella replicator census:\n");
    mss_per_stella_census(ms, 2, fcc_dist, track_stella);

    if (dump_top > 0) {
        printf("\n--- Top Programs (Final) ---");
        mss_dump_top_programs(ms, dump_top);
    }

    if (coupling_mode == COUPLING_OCTAHEDRAL && ms->oct_data) {
        int oct_rep = 0, oct_total = ms->n_edges;
        int oct_ps = ms->prog_size;
        uint8_t *oct_tape = malloc(2 * oct_ps);
        uint8_t *oct_orig = malloc(oct_ps);
        for (int e_idx = 0; e_idx < ms->n_edges; e_idx++) {
            memcpy(oct_orig, ms->oct_data[e_idx], oct_ps);
            memcpy(oct_tape, oct_orig, oct_ps);
            memset(oct_tape + oct_ps, 0, oct_ps);
            execute_tape(oct_tape, 2 * oct_ps, ms->max_steps);
            if (memcmp(oct_tape, oct_orig, oct_ps) == 0 &&
                memcmp(oct_tape + oct_ps, oct_orig, oct_ps) == 0 &&
                !is_trivial(oct_orig, oct_ps))
                oct_rep++;
        }
        free(oct_tape); free(oct_orig);
        printf("\nOctahedral interstitials: %d/%d replicators (%.1f%%)\n",
               oct_rep, oct_total, 100.0 * oct_rep / oct_total);
    }

    printf("\n============================================================\n");
    printf("CG: G1+G2 combined multi-stella FCC lattice soup\n");
    printf("  %d stellae on FCC lattice (Thm 0.0.6)\n", n_fcc);
    printf("  G2: dual-head VM, CPY01/CPY10 (Thm 0.2.1)\n");
    if (g1_enabled) {
        printf("  G1: geometric coupling (Def 0.1.3), strength=%.3f, eps=%.3f\n",
               coupling_strength, epsilon);
        if (chirality > 0.0f)
            printf("  Chirality: %.4f (mode=%d)\n", chirality, chirality_mode);
    } else
        printf("  G1: disabled (G2-only baseline)\n");
    printf("============================================================\n");

    pool_destroy(pool);
    if (fcc_dist) free(fcc_dist);
    mss_free(ms);
    return 0;
}
