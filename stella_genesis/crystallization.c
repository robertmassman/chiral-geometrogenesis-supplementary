/*
 * Crystallization Experiment — Phase A: Polyhedra Competition
 *
 * Tests whether the stella octangula is the optimal geometry for Z₃ field
 * coupling. Runs the Genesis VM on different two-component geometries and
 * compares coherence metrics.
 *
 * Key experiment: Rz(θ) rotation sweep. T₋ = Rz(θ)·T₊ where:
 *   θ = 0°   → T₋ = T₊ (aligned, zero contrast, no coupling)
 *   θ = 90°  → T₋ = stella T₋ (maximum interpenetration)
 *   θ = 180° → T₋ = T₊ again (periodic)
 *
 * If stella is optimal, coherence peaks sharply at θ = 90°.
 *
 * Geometry modes:
 *   "sweep"     — Rz(θ) rotation sweep (θ from arg)
 *   "separated" — T₋ = T₊ + (0,0,offset), offset from θ arg
 *   "nested"    — T₋ = scale·T₊, scale from θ arg (0.1 to 2.0)
 *   "random"    — random vertices on circumsphere, seed from θ arg
 *
 * Build: cc -O3 -o crystallization crystallization.c -lm
 * Run:   ./crystallization epochs seed cs n_sub mu eps theta_or_param geometry
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>

/* ── Configuration ─────────────────────────────────────────────────── */

#define MAX_SITES   50000
#define MAX_NBR     8
#define PROG_SIZE   24
#define MAX_STEPS   729

enum {
    OP_NOP = 0, OP_ROT = 1, OP_DROT = 2, OP_FWD = 3,
    OP_BCK = 4, OP_OPEN = 5, OP_CLOSE = 6, OP_NOP1 = 7, OP_NOP2 = 8
};

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

/* ── Mesh ──────────────────────────────────────────────────────────── */

typedef struct {
    int n_sites;
    float pos[MAX_SITES][3];
    int n_nbr[MAX_SITES];
    int nbr[MAX_SITES][MAX_NBR];
} Mesh;

static const int FACES[4][3] = {
    {1,2,3}, {0,3,2}, {0,1,3}, {0,2,1}
};

static int mesh_find_or_add(Mesh *m, float x, float y, float z, float eps) {
    for (int i = 0; i < m->n_sites; i++) {
        float dx = m->pos[i][0] - x;
        float dy = m->pos[i][1] - y;
        float dz = m->pos[i][2] - z;
        if (dx*dx + dy*dy + dz*dz < eps*eps) return i;
    }
    int id = m->n_sites++;
    m->pos[id][0] = x; m->pos[id][1] = y; m->pos[id][2] = z;
    m->n_nbr[id] = 0;
    return id;
}

static void mesh_add_edge(Mesh *m, int a, int b) {
    if (a == b) return;
    for (int i = 0; i < m->n_nbr[a]; i++)
        if (m->nbr[a][i] == b) return;
    if (m->n_nbr[a] < MAX_NBR) m->nbr[a][m->n_nbr[a]++] = b;
    if (m->n_nbr[b] < MAX_NBR) m->nbr[b][m->n_nbr[b]++] = a;
}

static void mesh_build(Mesh *m, const float verts[4][3], int n_sub) {
    memset(m, 0, sizeof(*m));
    float eps = 0.01f;
    int grid[4][(n_sub+1) * (n_sub+1)];
    memset(grid, -1, sizeof(int) * 4 * (n_sub+1) * (n_sub+1));

    for (int f = 0; f < 4; f++) {
        const float *va = verts[FACES[f][0]];
        const float *vb = verts[FACES[f][1]];
        const float *vc = verts[FACES[f][2]];
        for (int i = 0; i <= n_sub; i++) {
            for (int j = 0; j <= n_sub - i; j++) {
                float fi = (float)i / n_sub;
                float fj = (float)j / n_sub;
                float fk = 1.0f - fi - fj;
                float x = fk*va[0] + fi*vb[0] + fj*vc[0];
                float y = fk*va[1] + fi*vb[1] + fj*vc[1];
                float z = fk*va[2] + fi*vb[2] + fj*vc[2];
                int id = mesh_find_or_add(m, x, y, z, eps);
                grid[f][i*(n_sub+1) + j] = id;
            }
        }
        for (int i = 0; i <= n_sub; i++) {
            for (int j = 0; j <= n_sub - i; j++) {
                int cur = grid[f][i*(n_sub+1) + j];
                if (i+1 <= n_sub && j <= n_sub-(i+1)) {
                    mesh_add_edge(m, cur, grid[f][(i+1)*(n_sub+1)+j]);
                }
                if (j+1 <= n_sub-i) {
                    mesh_add_edge(m, cur, grid[f][i*(n_sub+1)+(j+1)]);
                }
                if (i+1 <= n_sub && j-1 >= 0) {
                    mesh_add_edge(m, cur, grid[f][(i+1)*(n_sub+1)+(j-1)]);
                }
            }
        }
    }
}

/* ── Pressure ──────────────────────────────────────────────────────── */

static float pressure_at(const float pos[3], const float verts[4][3], float eps) {
    float p_max = 0.0f;
    for (int v = 0; v < 4; v++) {
        float dx = pos[0]-verts[v][0], dy = pos[1]-verts[v][1], dz = pos[2]-verts[v][2];
        float p = 1.0f / (dx*dx + dy*dy + dz*dz + eps*eps);
        if (p > p_max) p_max = p;
    }
    return p_max;
}

/* ── Geometry generation ───────────────────────────────────────────── */

static const float TV_PLUS[4][3] = {
    { 1, 1, 1}, { 1,-1,-1}, {-1, 1,-1}, {-1,-1, 1}
};

static void rotate_z(const float in[4][3], float out[4][3], float theta_rad) {
    float ct = cosf(theta_rad), st = sinf(theta_rad);
    for (int i = 0; i < 4; i++) {
        out[i][0] = ct * in[i][0] - st * in[i][1];
        out[i][1] = st * in[i][0] + ct * in[i][1];
        out[i][2] = in[i][2];
    }
}

static void translate(const float in[4][3], float out[4][3], float dz) {
    for (int i = 0; i < 4; i++) {
        out[i][0] = in[i][0]; out[i][1] = in[i][1]; out[i][2] = in[i][2] + dz;
    }
}

static void scale_verts(const float in[4][3], float out[4][3], float s) {
    for (int i = 0; i < 4; i++) {
        out[i][0] = s*in[i][0]; out[i][1] = s*in[i][1]; out[i][2] = s*in[i][2];
    }
}

static void random_tetrahedron(float out[4][3], uint32_t seed) {
    /* Generate 4 random vertices on circumsphere (radius √3) */
    uint32_t rs[4];
    rs[0] = seed; rs[1] = seed*2654435761u;
    rs[2] = seed*2246822519u; rs[3] = seed*3266489917u;
    for (int i = 0; i < 20; i++) {
        uint32_t r = rs[0] + rs[3];
        uint32_t t = rs[1] << 9;
        rs[2] ^= rs[0]; rs[3] ^= rs[1];
        rs[1] ^= rs[2]; rs[0] ^= rs[3];
        rs[2] ^= t; rs[3] = rotl(rs[3], 11);
        (void)r;
    }
    float circumradius = sqrtf(3.0f);
    for (int i = 0; i < 4; i++) {
        /* Marsaglia method for uniform sphere sampling */
        float x1, x2, s;
        do {
            uint32_t r1 = rs[0] + rs[3];
            uint32_t t1 = rs[1] << 9;
            rs[2] ^= rs[0]; rs[3] ^= rs[1];
            rs[1] ^= rs[2]; rs[0] ^= rs[3];
            rs[2] ^= t1; rs[3] = rotl(rs[3], 11);
            uint32_t r2 = rs[0] + rs[3];
            uint32_t t2 = rs[1] << 9;
            rs[2] ^= rs[0]; rs[3] ^= rs[1];
            rs[1] ^= rs[2]; rs[0] ^= rs[3];
            rs[2] ^= t2; rs[3] = rotl(rs[3], 11);
            x1 = (r1 >> 8) / 16777216.0f * 2.0f - 1.0f;
            x2 = (r2 >> 8) / 16777216.0f * 2.0f - 1.0f;
            s = x1*x1 + x2*x2;
        } while (s >= 1.0f || s < 1e-6f);
        float f = 2.0f * sqrtf(1.0f - s);
        out[i][0] = circumradius * x1 * f;
        out[i][1] = circumradius * x2 * f;
        out[i][2] = circumradius * (1.0f - 2.0f*s);
    }
}

/* ── Soup structure ────────────────────────────────────────────────── */

typedef struct {
    Mesh mesh_tp, mesh_tm;
    uint8_t *tp_data, *tm_data;
    float *pp_at_tp, *pm_at_tp, *pp_at_tm, *pm_at_tm;
    int prog_size, max_steps;
    double mutation_rate, coupling_strength;
    float epsilon;
    uint8_t *work_a, *work_b;
    int *patch_a;
    long epoch;
    long coupling_tp_to_tm, coupling_tm_to_tp, total_couplings;
} Soup;

static void soup_init(Soup *s, const float v_plus[4][3], const float v_minus[4][3],
                      int n_sub, uint32_t seed) {
    rng_seed(seed);
    mesh_build(&s->mesh_tp, v_plus, n_sub);
    mesh_build(&s->mesh_tm, v_minus, n_sub);
    int n_tp = s->mesh_tp.n_sites, n_tm = s->mesh_tm.n_sites;
    if (n_tp != n_tm) {
        fprintf(stderr, "ERROR: mesh mismatch %d vs %d\n", n_tp, n_tm);
        exit(1);
    }
    int n = n_tp;
    s->tp_data = calloc(n, 1); s->tm_data = calloc(n, 1);
    s->pp_at_tp = calloc(n, sizeof(float)); s->pm_at_tp = calloc(n, sizeof(float));
    s->pp_at_tm = calloc(n, sizeof(float)); s->pm_at_tm = calloc(n, sizeof(float));

    for (int i = 0; i < n; i++) {
        s->tp_data[i] = rng_int(3);
        s->tm_data[i] = rng_int(3);
    }
    for (int i = 0; i < n; i++) {
        s->pp_at_tp[i] = pressure_at(s->mesh_tp.pos[i], v_plus, s->epsilon);
        s->pm_at_tp[i] = pressure_at(s->mesh_tp.pos[i], v_minus, s->epsilon);
        s->pp_at_tm[i] = pressure_at(s->mesh_tm.pos[i], v_plus, s->epsilon);
        s->pm_at_tm[i] = pressure_at(s->mesh_tm.pos[i], v_minus, s->epsilon);
    }

    s->work_a = calloc(s->prog_size, 1); s->work_b = calloc(s->prog_size, 1);
    s->patch_a = calloc(s->prog_size, sizeof(int));
    s->epoch = 0;
    s->coupling_tp_to_tm = s->coupling_tm_to_tp = s->total_couplings = 0;
}

static void soup_free(Soup *s) {
    free(s->tp_data); free(s->tm_data);
    free(s->pp_at_tp); free(s->pm_at_tp);
    free(s->pp_at_tm); free(s->pm_at_tm);
    free(s->work_a); free(s->work_b); free(s->patch_a);
}

/* ── BFS patch extraction ─────────────────────────────────────────── */

static int bfs_extract(const Mesh *m, int center, int max_count, int *patch) {
    uint8_t visited[MAX_SITES];
    memset(visited, 0, m->n_sites);
    int queue[MAX_SITES], head = 0, tail = 0, count = 0;
    visited[center] = 1; queue[tail++] = center;
    while (head < tail && count < max_count) {
        int site = queue[head++]; patch[count++] = site;
        int sorted[MAX_NBR], nn = m->n_nbr[site];
        memcpy(sorted, m->nbr[site], nn * sizeof(int));
        for (int i = 1; i < nn; i++) {
            int key = sorted[i], j = i-1;
            while (j >= 0 && sorted[j] > key) { sorted[j+1] = sorted[j]; j--; }
            sorted[j+1] = key;
        }
        for (int i = 0; i < nn; i++) {
            if (!visited[sorted[i]]) { visited[sorted[i]] = 1; queue[tail++] = sorted[i]; }
        }
    }
    return count;
}

/* ── VM execution (G1-only, classic) ──────────────────────────────── */

static void vm_execute(uint8_t *tape, int len, int max_steps) {
    int ip = 0, h = 0, steps = 0;
    while (steps < max_steps && ip + 1 < len) {
        int op = tape[ip] * 3 + tape[ip+1];
        switch (op) {
        case OP_NOP: case OP_NOP1: case OP_NOP2: break;
        case OP_ROT:  tape[h] = tape[h] < 2 ? tape[h]+1 : 0; break;
        case OP_DROT: tape[h] = tape[h] > 0 ? tape[h]-1 : 2; break;
        case OP_FWD:  h = (h+1) % len; break;
        case OP_BCK:  h = (h-1+len) % len; break;
        case OP_OPEN:
            if (tape[h] == 0) {
                int depth = 1, pos = ip+2;
                while (depth > 0 && pos+1 < len) {
                    int inner = tape[pos]*3 + tape[pos+1];
                    if (inner == OP_OPEN) depth++;
                    else if (inner == OP_CLOSE) depth--;
                    pos += 2;
                }
                if (depth == 0) ip = pos - 2;
            }
            break;
        case OP_CLOSE:
            if (tape[h] != 0) {
                int depth = 1, pos = ip-2;
                while (depth > 0 && pos >= 0) {
                    int inner = tape[pos]*3 + tape[pos+1];
                    if (inner == OP_CLOSE) depth++;
                    else if (inner == OP_OPEN) depth--;
                    pos -= 2;
                }
                if (depth == 0) ip = pos + 2;
            }
            break;
        }
        ip += 2; steps++;
    }
}

/* ── Geometric coupling ───────────────────────────────────────────── */

static void geometric_couple(Soup *s, int *patch, int count) {
    for (int i = 0; i < count; i++) {
        int site = patch[i];

        /* T+ perspective */
        float pp_tp = s->pp_at_tp[site], pm_tp = s->pm_at_tp[site];
        float sum_tp = pp_tp + pm_tp;
        if (sum_tp > 1e-10f) {
            float delta = pp_tp - pm_tp;
            if (delta > 0) {
                float prob = (float)s->coupling_strength * delta / sum_tp;
                if (prob > 1.0f) prob = 1.0f;
                s->total_couplings++;
                if (rng_float() < prob) {
                    s->tm_data[site] = s->tp_data[site];
                    s->coupling_tp_to_tm++;
                }
            }
        }

        /* T- perspective */
        float pm_tm = s->pm_at_tm[site], pp_tm = s->pp_at_tm[site];
        float sum_tm = pm_tm + pp_tm;
        if (sum_tm > 1e-10f) {
            float delta = pm_tm - pp_tm;
            if (delta > 0) {
                float prob = (float)s->coupling_strength * delta / sum_tm;
                if (prob > 1.0f) prob = 1.0f;
                s->total_couplings++;
                if (rng_float() < prob) {
                    s->tp_data[site] = s->tm_data[site];
                    s->coupling_tm_to_tp++;
                }
            }
        }
    }
}

/* ── One epoch ─────────────────────────────────────────────────────── */

static void epoch(Soup *s) {
    int n = s->mesh_tp.n_sites;
    int center = rng_int(n);
    int count = bfs_extract(&s->mesh_tp, center, s->prog_size, s->patch_a);

    for (int i = 0; i < count; i++) {
        s->work_a[i] = s->tp_data[s->patch_a[i]];
        s->work_b[i] = s->tm_data[s->patch_a[i]];
    }

    vm_execute(s->work_a, count, s->max_steps);
    vm_execute(s->work_b, count, s->max_steps);

    for (int i = 0; i < count; i++) {
        s->tp_data[s->patch_a[i]] = s->work_a[i];
        s->tm_data[s->patch_a[i]] = s->work_b[i];
    }

    geometric_couple(s, s->patch_a, count);

    for (int i = 0; i < count; i++) {
        int site = s->patch_a[i];
        if (rng_float() < s->mutation_rate) s->tp_data[site] = rng_int(3);
        if (rng_float() < s->mutation_rate) s->tm_data[site] = rng_int(3);
    }
    s->epoch++;
}

/* ── Metrics ───────────────────────────────────────────────────────── */

static float compute_entropy(const uint8_t *data, int n) {
    int c[3] = {0,0,0};
    for (int i = 0; i < n; i++) c[data[i]]++;
    float ent = 0.0f;
    for (int j = 0; j < 3; j++) {
        if (c[j] > 0) { float p = (float)c[j]/n; ent -= p * log2f(p); }
    }
    return ent;
}

static float compute_corr(const uint8_t *tp, const uint8_t *tm, int n) {
    int match = 0;
    for (int i = 0; i < n; i++) if (tp[i] == tm[i]) match++;
    return (float)match / n;
}

static float compute_autocorr(const uint8_t *data, const Mesh *m) {
    int agree = 0, total = 0;
    for (int i = 0; i < m->n_sites; i++) {
        for (int j = 0; j < m->n_nbr[i]; j++) {
            if (data[i] == data[m->nbr[i][j]]) agree++;
            total++;
        }
    }
    return total > 0 ? (float)agree / total : 0.333f;
}

static float compute_local_repl(Soup *s) {
    int n = s->mesh_tp.n_sites, samples = 100;
    int total_match = 0, total_sites = 0;
    for (int i = 0; i < samples; i++) {
        int center = rng_int(n);
        int patch[PROG_SIZE];
        int count = bfs_extract(&s->mesh_tp, center, s->prog_size, patch);
        for (int j = 0; j < count; j++)
            if (s->tp_data[patch[j]] == s->tm_data[patch[j]]) total_match++;
        total_sites += count;
    }
    return total_sites > 0 ? (float)total_match / total_sites : 0.333f;
}

/* Compute average minimum vertex distance between T+ and T- vertices.
 * This measures how "interpenetrating" the two tetrahedra are. */
static float compute_vertex_separation(const float vp[4][3], const float vm[4][3]) {
    float total = 0.0f;
    for (int i = 0; i < 4; i++) {
        float min_d = 1e10f;
        for (int j = 0; j < 4; j++) {
            float dx = vp[i][0]-vm[j][0], dy = vp[i][1]-vm[j][1], dz = vp[i][2]-vm[j][2];
            float d = sqrtf(dx*dx + dy*dy + dz*dz);
            if (d < min_d) min_d = d;
        }
        total += min_d;
    }
    return total / 4.0f;
}

/* Compute the pressure contrast: fraction of sites where |ΔP|/(P++P-) > threshold */
static float compute_pressure_contrast(Soup *s) {
    int n = s->mesh_tp.n_sites, count = 0;
    float thresh = 0.1f;
    for (int i = 0; i < n; i++) {
        float sum = s->pp_at_tp[i] + s->pm_at_tp[i];
        if (sum > 1e-10f) {
            float ratio = fabsf(s->pp_at_tp[i] - s->pm_at_tp[i]) / sum;
            if (ratio > thresh) count++;
        }
    }
    return (float)count / n;
}

/* ── Main ──────────────────────────────────────────────────────────── */

int main(int argc, char **argv) {
    long total_epochs = 1000000;
    uint32_t seed = 42;
    double cs = 0.5;
    int n_sub = 16;
    double mu = 0.001;
    float eps = 0.1f;
    float param = 90.0f;       /* theta for sweep, offset for separated, etc. */
    const char *geometry = "sweep";

    if (argc > 1) total_epochs = atol(argv[1]);
    if (argc > 2) seed = (uint32_t)atoi(argv[2]);
    if (argc > 3) cs = atof(argv[3]);
    if (argc > 4) n_sub = atoi(argv[4]);
    if (argc > 5) mu = atof(argv[5]);
    if (argc > 6) eps = (float)atof(argv[6]);
    if (argc > 7) param = (float)atof(argv[7]);
    if (argc > 8) geometry = argv[8];

    /* Generate T- vertices based on geometry mode */
    float v_minus[4][3];

    if (strcmp(geometry, "sweep") == 0) {
        float theta_rad = param * (float)M_PI / 180.0f;
        rotate_z(TV_PLUS, v_minus, theta_rad);
    } else if (strcmp(geometry, "separated") == 0) {
        translate(TV_PLUS, v_minus, param);  /* param = z offset */
    } else if (strcmp(geometry, "nested") == 0) {
        scale_verts(TV_PLUS, v_minus, param); /* param = scale factor */
    } else if (strcmp(geometry, "random") == 0) {
        random_tetrahedron(v_minus, (uint32_t)param);
    } else if (strcmp(geometry, "stella") == 0) {
        /* Standard stella — T- = -T+ */
        for (int i = 0; i < 4; i++) {
            v_minus[i][0] = -TV_PLUS[i][0];
            v_minus[i][1] = -TV_PLUS[i][1];
            v_minus[i][2] = -TV_PLUS[i][2];
        }
    } else if (strcmp(geometry, "aligned") == 0) {
        memcpy(v_minus, TV_PLUS, sizeof(v_minus));
    } else {
        fprintf(stderr, "Unknown geometry: %s\n", geometry);
        return 1;
    }

    /* Print header to stderr (keep stdout clean for JSON) */
    fprintf(stderr, "Crystallization: geometry=%s param=%.2f epochs=%ld seed=%u "
                    "cs=%.2f n_sub=%d\n", geometry, param, total_epochs, seed, cs, n_sub);

    /* Print T- vertices to stderr */
    fprintf(stderr, "T+ vertices: ");
    for (int i = 0; i < 4; i++)
        fprintf(stderr, "(%.2f,%.2f,%.2f) ", TV_PLUS[i][0], TV_PLUS[i][1], TV_PLUS[i][2]);
    fprintf(stderr, "\nT- vertices: ");
    for (int i = 0; i < 4; i++)
        fprintf(stderr, "(%.2f,%.2f,%.2f) ", v_minus[i][0], v_minus[i][1], v_minus[i][2]);
    fprintf(stderr, "\n");

    /* Initialize soup */
    Soup s;
    memset(&s, 0, sizeof(s));
    s.prog_size = PROG_SIZE;
    s.max_steps = MAX_STEPS;
    s.mutation_rate = mu;
    s.coupling_strength = cs;
    s.epsilon = eps;
    soup_init(&s, TV_PLUS, v_minus, n_sub, seed);

    float vertex_sep = compute_vertex_separation(TV_PLUS, v_minus);
    float p_contrast = compute_pressure_contrast(&s);
    fprintf(stderr, "Mesh: %d sites/tet, vertex_sep=%.3f, pressure_contrast=%.3f\n",
            s.mesh_tp.n_sites, vertex_sep, p_contrast);

    /* Run */
    long report = total_epochs / 5;
    if (report < 1) report = 1;
    for (long e = 0; e < total_epochs; e++) {
        epoch(&s);
        if ((e+1) % report == 0) {
            float c = compute_corr(s.tp_data, s.tm_data, s.mesh_tp.n_sites);
            fprintf(stderr, "  epoch=%ld corr=%.4f\n", e+1, c);
        }
    }

    /* Compute final metrics */
    int n = s.mesh_tp.n_sites;
    float h_tp = compute_entropy(s.tp_data, n);
    float h_tm = compute_entropy(s.tm_data, n);
    float corr = compute_corr(s.tp_data, s.tm_data, n);
    float auto_tp = compute_autocorr(s.tp_data, &s.mesh_tp);
    float auto_tm = compute_autocorr(s.tm_data, &s.mesh_tm);
    float local_repl = compute_local_repl(&s);
    float dir_bias = (s.coupling_tp_to_tm + s.coupling_tm_to_tp) > 0
        ? (float)s.coupling_tp_to_tm / (s.coupling_tp_to_tm + s.coupling_tm_to_tp)
        : 0.5f;

    /* JSON output to stdout */
    printf("{\"geometry\":\"%s\",\"param\":%.4f,\"epochs\":%ld,\"seed\":%u,"
           "\"cs\":%.3f,\"n_sub\":%d,\"n_sites\":%d,"
           "\"corr\":%.6f,\"h_tp\":%.6f,\"h_tm\":%.6f,"
           "\"auto_tp\":%.6f,\"auto_tm\":%.6f,\"local_repl\":%.6f,"
           "\"dir_bias\":%.6f,"
           "\"couplings_tp_tm\":%ld,\"couplings_tm_tp\":%ld,\"total_couplings\":%ld,"
           "\"vertex_sep\":%.6f,\"pressure_contrast\":%.6f}\n",
           geometry, param, total_epochs, seed,
           cs, n_sub, n,
           corr, h_tp, h_tm,
           auto_tp, auto_tm, local_repl,
           dir_bias,
           s.coupling_tp_to_tm, s.coupling_tm_to_tp, s.total_couplings,
           vertex_sep, p_contrast);

    soup_free(&s);
    return 0;
}
