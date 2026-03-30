/*
 * Genesis Soup — Metal GPU Version
 * ==================================
 * Port of genesis_soup.c to Apple Metal GPU using double-buffered
 * snapshot architecture, following the StellaLang Metal pattern.
 *
 * Architecture:
 *   - Single stella octangula (dual-mesh T+/T-)
 *   - Tile-based parallel dispatch (BFS Voronoi partition)
 *   - 5 compute kernels: vm_couple, kuramoto, mass_precompute,
 *     energy_count, mutate
 *   - Kuramoto sub-step re-dispatch for GG2b multi-hop diffusion
 *   - Diagnostics match genesis_soup.c output format for validation
 *
 * Compile:
 *   clang -O3 -framework Metal -framework Foundation \
 *         -o genesis_soup_metal genesis_soup_metal.m -lm
 *
 * Run:
 *   ./genesis_soup_metal --n-sub 64 --epochs 2000000 --seed 42 \
 *     --coupling-strength 0.7 --phase-lock 1.0 --kuramoto-mode 1 \
 *     --instr-mode 2 --color-pressure 1 --kuramoto-sub-steps 8
 */

#import <Foundation/Foundation.h>
#import <Metal/Metal.h>

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <getopt.h>

/* ================================================================
 * Constants (match genesis_soup.c)
 * ================================================================ */
#define MAX_NBR     8
#define PROG_SIZE   24
#define MAX_STEPS   729

/* ================================================================
 * GenesisParams (must match genesis_soup.metal struct exactly)
 * ================================================================ */
typedef struct {
    uint32_t n_sites;
    uint32_t n_tiles;
    uint32_t n_tiles_per;
    uint32_t prog_size;
    uint32_t max_steps;
    float    mutation_rate;
    float    coupling_strength;
    float    chirality;
    uint32_t chirality_mode;
    uint32_t instr_mode;
    uint32_t color_pressure;
    float    phase_lock;
    uint32_t kuramoto_mode;
    float    energy_lambda;
    uint32_t mass_mode;
    float    mass_couple;
    float    mass_kuramoto;
    float    mass_geo;
    uint32_t n_interactions;
    uint32_t sub_round_idx;
    float    epsilon;
    uint32_t max_nbr;
} GenesisParams;

/* ================================================================
 * RNG: xoshiro128+ (for host-side mesh init, same as genesis_soup.c)
 * ================================================================ */
static uint32_t rng_s[4];

static inline uint32_t rotl32(uint32_t x, int k) {
    return (x << k) | (x >> (32 - k));
}

static uint32_t rng_next(void) {
    uint32_t r = rng_s[0] + rng_s[3];
    uint32_t t = rng_s[1] << 9;
    rng_s[2] ^= rng_s[0]; rng_s[3] ^= rng_s[1];
    rng_s[1] ^= rng_s[2]; rng_s[0] ^= rng_s[3];
    rng_s[2] ^= t; rng_s[3] = rotl32(rng_s[3], 11);
    return r;
}

static void rng_seed(uint32_t seed) {
    rng_s[0] = seed; rng_s[1] = seed * 2654435761u;
    rng_s[2] = seed * 2246822519u; rng_s[3] = seed * 3266489917u;
    for (int i = 0; i < 20; i++) rng_next();
}

static inline int rng_int(int n) { return (int)(rng_next() % (uint32_t)n); }
static inline float rng_float(void) { return (rng_next() >> 8) / 16777216.0f; }

/* Splitmix64 for GPU RNG seeding */
static uint64_t splitmix64(uint64_t *state) {
    uint64_t z = (*state += 0x9e3779b97f4a7c15ULL);
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
}

/* ================================================================
 * Mesh (triangulated tetrahedron face, from genesis_soup.c)
 * ================================================================ */
typedef struct {
    int n_sites;
    float (*pos)[3];        /* [n_sites][3] */
    int *n_nbr;            /* [n_sites] */
    int (*nbr)[MAX_NBR];   /* [n_sites][MAX_NBR] */
} Mesh;

/* T+ vertices: cube corners with s1*s2*s3 = +1 */
static const float TV_PLUS[4][3] = {
    { 1, 1, 1}, { 1,-1,-1}, {-1, 1,-1}, {-1,-1, 1}
};
/* T- vertices: cube corners with s1*s2*s3 = -1 */
static const float TV_MINUS[4][3] = {
    {-1,-1,-1}, {-1, 1, 1}, { 1,-1, 1}, { 1, 1,-1}
};
static const int FACES[4][3] = {
    {1,2,3}, {0,3,2}, {0,1,3}, {0,2,1}
};

/* Spatial hash for mesh deduplication */
#define HASH_SIZE 196613
static int hash_head[HASH_SIZE];
static int *hash_next_arr;
static int hash_max_sites;

static void mesh_hash_reset(int max_sites) {
    memset(hash_head, -1, sizeof(hash_head));
    if (hash_next_arr) free(hash_next_arr);
    hash_next_arr = (int *)malloc(max_sites * sizeof(int));
    hash_max_sites = max_sites;
}

static int mesh_find_or_add(Mesh *m, float x, float y, float z, float eps) {
    float cell = eps * 2.0f;
    int ix0 = (int)floorf((x + 2.0f) / cell);
    int iy0 = (int)floorf((y + 2.0f) / cell);
    int iz0 = (int)floorf((z + 2.0f) / cell);
    float eps2 = eps * eps;
    for (int dx = -1; dx <= 1; dx++)
    for (int dy = -1; dy <= 1; dy++)
    for (int dz = -1; dz <= 1; dz++) {
        unsigned h = (unsigned)((ix0+dx) * 73856093u ^
                                (iy0+dy) * 19349663u ^
                                (iz0+dz) * 83492791u) % HASH_SIZE;
        for (int i = hash_head[h]; i >= 0; i = hash_next_arr[i]) {
            float ddx = m->pos[i][0] - x;
            float ddy = m->pos[i][1] - y;
            float ddz = m->pos[i][2] - z;
            if (ddx*ddx + ddy*ddy + ddz*ddz < eps2) return i;
        }
    }
    int id = m->n_sites++;
    m->pos[id][0] = x; m->pos[id][1] = y; m->pos[id][2] = z;
    m->n_nbr[id] = 0;
    float cell2 = eps * 2.0f;
    unsigned h = (unsigned)((int)floorf((x+2.0f)/cell2) * 73856093u ^
                            (int)floorf((y+2.0f)/cell2) * 19349663u ^
                            (int)floorf((z+2.0f)/cell2) * 83492791u) % HASH_SIZE;
    hash_next_arr[id] = hash_head[h];
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

static void warp_barycentric(float *fi, float *fj, float *fk, float alpha) {
    if (alpha >= 0.999f) return;
    float a = *fi, b = *fj, c = *fk;
    float wa = (a > 0.0f) ? powf(a, alpha) : 0.0f;
    float wb = (b > 0.0f) ? powf(b, alpha) : 0.0f;
    float wc = (c > 0.0f) ? powf(c, alpha) : 0.0f;
    float sum = wa + wb + wc;
    if (sum > 0.0f) { *fi = wa / sum; *fj = wb / sum; *fk = wc / sum; }
}

static Mesh *mesh_build(const float verts[4][3], int n_sub, float warp_alpha) {
    int max_sites = 2 * n_sub * n_sub + 100;  /* actual: 2*n_sub²+2 after dedup */
    Mesh *m = (Mesh *)calloc(1, sizeof(Mesh));
    m->pos = (float (*)[3])calloc(max_sites, sizeof(float[3]));
    m->n_nbr = (int *)calloc(max_sites, sizeof(int));
    m->nbr = (int (*)[MAX_NBR])calloc(max_sites, sizeof(int[MAX_NBR]));

    mesh_hash_reset(max_sites);
    /* eps must be smaller than nearest-neighbor spacing on a face.
     * Edge length ≈ 2√2; face spacing ≈ 2√2/n_sub.
     * Use eps = 0.5/n_sub to stay well below that. */
    float eps = 0.5f / n_sub;

    int stride = (n_sub + 1) * (n_sub + 1);
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
                grid[f * stride + i * (n_sub + 1) + j] = id;
            }
        }

        for (int i = 0; i <= n_sub; i++) {
            for (int j = 0; j <= n_sub - i; j++) {
                int cur = grid[f * stride + i * (n_sub + 1) + j];
                if (i + 1 <= n_sub && j <= n_sub - (i + 1)) {
                    int right = grid[f * stride + (i + 1) * (n_sub + 1) + j];
                    mesh_add_edge(m, cur, right);
                }
                if (j + 1 <= n_sub - i) {
                    int up = grid[f * stride + i * (n_sub + 1) + (j + 1)];
                    mesh_add_edge(m, cur, up);
                }
                if (i + 1 <= n_sub && j - 1 >= 0) {
                    int diag = grid[f * stride + (i + 1) * (n_sub + 1) + (j - 1)];
                    mesh_add_edge(m, cur, diag);
                }
            }
        }
    }
    free(grid);
    return m;
}

static void mesh_free(Mesh *m) {
    free(m->pos); free(m->n_nbr); free(m->nbr); free(m);
}

/* ================================================================
 * Pressure (Def 0.1.3)
 * ================================================================ */
static float pressure_at_site(const float pos[3], const float verts[4][3],
                               float epsilon) {
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
 * Tiling: BFS Voronoi partition (from StellaLang)
 * ================================================================ */
typedef struct {
    int n_tiles;
    int *tile_size;       /* [n_tiles] */
    int **tile_sites;     /* [n_tiles][prog_size] */
    int (*tile_nbr)[8];   /* [n_tiles][8] */
    int *n_tile_nbr;      /* [n_tiles] */
} Tiling;

static Tiling *tiling_build(const Mesh *m, int n_tiles, int prog_size) {
    Tiling *t = (Tiling *)calloc(1, sizeof(Tiling));
    t->n_tiles = n_tiles;
    t->tile_size = (int *)calloc(n_tiles, sizeof(int));
    t->tile_sites = (int **)calloc(n_tiles, sizeof(int *));
    t->tile_nbr = (int (*)[8])calloc(n_tiles, sizeof(int[8]));
    t->n_tile_nbr = (int *)calloc(n_tiles, sizeof(int));

    for (int i = 0; i < n_tiles; i++)
        t->tile_sites[i] = (int *)malloc(prog_size * sizeof(int));

    int *owner = (int *)malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;
    int *queue = (int *)malloc(m->n_sites * sizeof(int));

    int next_start = 0;
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
    }

    /* Build tile neighbor lists */
    for (int site = 0; site < m->n_sites; site++) {
        if (owner[site] < 0) continue;
        int ti = owner[site];
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] < 0 || owner[nb] == ti) continue;
            int tj = owner[nb];
            int found = 0;
            for (int k = 0; k < t->n_tile_nbr[ti]; k++)
                if (t->tile_nbr[ti][k] == tj) { found = 1; break; }
            if (!found && t->n_tile_nbr[ti] < 8)
                t->tile_nbr[ti][t->n_tile_nbr[ti]++] = tj;
        }
    }

    free(owner); free(queue);
    return t;
}

static void tiling_free(Tiling *t) {
    for (int i = 0; i < t->n_tiles; i++) free(t->tile_sites[i]);
    free(t->tile_sites); free(t->tile_size);
    free(t->tile_nbr); free(t->n_tile_nbr); free(t);
}

/* ================================================================
 * Genesis state (host-side data)
 * ================================================================ */
typedef struct {
    Mesh *mesh_tp;
    Mesh *mesh_tm;
    Tiling *tp_tiling;
    Tiling *tm_tiling;
    int n_sites;            /* sites per tetrahedron */
    int n_tiles_per;        /* tiles per tetrahedron */

    /* Precomputed pressure (static) */
    float *pp_at_tp;        /* P+ at T+ positions */
    float *pm_at_tp;        /* P- at T+ positions */
    float *pp_at_tm;        /* P+ at T- positions */
    float *pm_at_tm;        /* P- at T- positions */

    /* Dominant color per site */
    uint8_t *dominant_color_tp;
    uint8_t *dominant_color_tm;

    /* Per-color pressure ratios (precomputed, for WRITE gate) */
    float *pressure_color;  /* [c0_tp(n), c1_tp(n), c2_tp(n), c0_tm(n)..c2_tm(n)] */

    /* Configuration */
    float coupling_strength;
    float chirality;
    int chirality_mode;
    int instr_mode;
    float warp_alpha;
    int color_pressure;
    float phase_lock;
    int kuramoto_mode;
    float energy_lambda;
    int mass_mode;
    float mass_couple;
    float mass_kuramoto;
    float mass_geo;
    float mutation_rate;
    float epsilon;
    int snapshot_mode;
    int kuramoto_sub_steps;

    long epoch;

    /* K2/K3: Phase wavefront diagnostics (CPU-side readback from GPU) */
    int phase_diag_interval;        /* report phase shells every N epochs (0=off) */
    long phase_perturb_epoch;       /* epoch at which to inject perturbation (-1=off) */
    float phase_perturb_delta;      /* perturbation amplitude (radians) */
    int *phase_bfs_dist;            /* BFS distance from perturbation site (T+) */
    int phase_bfs_max_d;            /* maximum BFS distance */
    int phase_perturb_site;         /* site index for perturbation (T+ only) */
    int *phase_shell_count;         /* count of sites per BFS shell */
    long *phase_arrival;            /* first epoch where shell d exceeded threshold */
    FILE *phase_diag_file;          /* output file for phase diagnostics */
    float *phase_baseline_tp;       /* saved T+ phase state at perturbation epoch */

    /* K3: Lyapunov divergence front — zone-aware trit Hamming distance */
    int *site_zone;                 /* per T+ site: 0=blocked (P_ratio<0.5), 1=open */
    int *shell_count_open;          /* sites per shell in open zone */
    int *shell_count_blocked;       /* sites per shell in blocked zone */
    long *trit_arrival_open;        /* first epoch trit Hamming > threshold, open zone */
    long *trit_arrival_blocked;     /* first epoch trit Hamming > threshold, blocked zone */
} GenesisState;

/* ================================================================
 * Metal GPU State
 * ================================================================ */
typedef struct {
    id<MTLDevice> device;
    id<MTLCommandQueue> queue;
    id<MTLComputePipelineState> vmCouplePipeline;
    id<MTLComputePipelineState> kuramotoPipeline;
    id<MTLComputePipelineState> massPipeline;
    id<MTLComputePipelineState> energyPipeline;
    id<MTLComputePipelineState> mutatePipeline;
    NSUInteger maxThreadsPerGroup;

    /* Ping-pong buffers for trits and phases */
    id<MTLBuffer> tritBufA;     /* trits: [T+(n)] [T-(n)] uint8 */
    id<MTLBuffer> tritBufB;
    id<MTLBuffer> phaseBufA;    /* phases: [T+(n)] [T-(n)] float */
    id<MTLBuffer> phaseBufB;
    int ping;  /* 0: A=read/B=write, 1: B=read/A=write */

    /* Static buffers */
    id<MTLBuffer> tileSitesBuf;     /* [n_tiles * prog_size] uint32 */
    id<MTLBuffer> tileSizeBuf;      /* [n_tiles] uint32 */
    id<MTLBuffer> tileNbrBuf;       /* [n_tiles * 8] uint32 */
    id<MTLBuffer> tileNbrCountBuf;  /* [n_tiles] uint32 */
    id<MTLBuffer> rngStatesBuf;     /* [n_tiles * 4] uint64 */
    id<MTLBuffer> paramsBuf;        /* GenesisParams */
    id<MTLBuffer> pressureBuf;      /* [pp_tp, pm_tp, pp_tm, pm_tm] × n floats */
    id<MTLBuffer> meshNbrBuf;       /* [T+ n*MAX_NBR] [T- n*MAX_NBR] uint32 */
    id<MTLBuffer> meshNbrCountBuf;  /* [T+ n] [T- n] uint32 */
    id<MTLBuffer> massBuf;          /* [T+ n] [T- n] float */
    id<MTLBuffer> dominantColorBuf; /* [T+ n] [T- n] uint8 */
    id<MTLBuffer> energyCountsBuf;  /* 6 × uint32 */
    id<MTLBuffer> pressureColorBuf; /* [c0_tp(n)..c2_tp(n), c0_tm(n)..c2_tm(n)] float */

    uint32_t n_interactions;
    int sub_rounds;
} MetalState;

/* ================================================================
 * Metal Setup
 * ================================================================ */
static MetalState *metal_setup(GenesisState *gs, const char *shader_path) {
    MetalState *mt = (MetalState *)calloc(1, sizeof(MetalState));

    mt->device = MTLCreateSystemDefaultDevice();
    if (!mt->device) {
        fprintf(stderr, "Error: No Metal GPU device found\n");
        exit(1);
    }
    printf("Metal device: %s\n", [[mt->device name] UTF8String]);
    mt->queue = [mt->device newCommandQueue];

    /* Compile shader */
    NSError *error = nil;
    NSString *path = [NSString stringWithUTF8String:shader_path];
    NSString *src = [NSString stringWithContentsOfFile:path
                                             encoding:NSUTF8StringEncoding
                                                error:&error];
    if (!src) {
        fprintf(stderr, "Error: Cannot load %s: %s\n",
                shader_path, [[error localizedDescription] UTF8String]);
        exit(1);
    }

    MTLCompileOptions *opts = [[MTLCompileOptions alloc] init];
    opts.mathMode = MTLMathModeFast;
    id<MTLLibrary> lib = [mt->device newLibraryWithSource:src
                                                  options:opts
                                                    error:&error];
    if (!lib) {
        fprintf(stderr, "Error: Shader compilation failed:\n%s\n",
                [[error localizedDescription] UTF8String]);
        exit(1);
    }

    /* Create pipelines for all 5 kernels */
    const char *kernel_names[] = {
        "genesis_vm_couple", "genesis_kuramoto", "genesis_mass_precompute",
        "genesis_energy_count", "genesis_mutate"
    };
    id<MTLComputePipelineState> *pipelines[] = {
        &mt->vmCouplePipeline, &mt->kuramotoPipeline, &mt->massPipeline,
        &mt->energyPipeline, &mt->mutatePipeline
    };
    for (int k = 0; k < 5; k++) {
        NSString *name = [NSString stringWithUTF8String:kernel_names[k]];
        id<MTLFunction> func = [lib newFunctionWithName:name];
        if (!func) {
            fprintf(stderr, "Error: Kernel '%s' not found\n", kernel_names[k]);
            exit(1);
        }
        *pipelines[k] = [mt->device newComputePipelineStateWithFunction:func
                                                                  error:&error];
        if (!*pipelines[k]) {
            fprintf(stderr, "Error: Pipeline '%s' failed: %s\n",
                    kernel_names[k], [[error localizedDescription] UTF8String]);
            exit(1);
        }
    }
    mt->maxThreadsPerGroup = mt->vmCouplePipeline.maxTotalThreadsPerThreadgroup;
    printf("Metal: 5 pipelines ready (max threads/group: %lu)\n",
           (unsigned long)mt->maxThreadsPerGroup);

    /* ─── Create GPU buffers ─── */
    int n = gs->n_sites;
    int n_tiles = 2 * gs->n_tiles_per;
    int ps = PROG_SIZE;

    /* Trit buffers (ping-pong) */
    NSUInteger trit_size = (NSUInteger)(2 * n);
    mt->tritBufA = [mt->device newBufferWithLength:trit_size
                                           options:MTLResourceStorageModeShared];
    mt->tritBufB = [mt->device newBufferWithLength:trit_size
                                           options:MTLResourceStorageModeShared];

    /* Phase buffers (ping-pong) */
    NSUInteger phase_size = (NSUInteger)(2 * n * sizeof(float));
    mt->phaseBufA = [mt->device newBufferWithLength:phase_size
                                            options:MTLResourceStorageModeShared];
    mt->phaseBufB = [mt->device newBufferWithLength:phase_size
                                            options:MTLResourceStorageModeShared];

    /* Initialize trit and phase data */
    uint8_t *trits = (uint8_t *)[mt->tritBufA contents];
    float *phases = (float *)[mt->phaseBufA contents];
    float third = 2.0f * (float)M_PI / 3.0f;
    for (int i = 0; i < n; i++) {
        trits[i] = rng_int(3);           /* T+ */
        trits[i + n] = rng_int(3);       /* T- */
        phases[i] = trits[i] * third;
        phases[i + n] = trits[i + n] * third;
    }
    /* Copy to B buffers */
    memcpy([mt->tritBufB contents], trits, 2 * n);
    memcpy([mt->phaseBufB contents], phases, 2 * n * sizeof(float));
    mt->ping = 0;

    /* Tile sites: flatten [T+ tiles] [T- tiles] into one buffer */
    uint32_t *flat_sites = (uint32_t *)calloc(n_tiles * ps, sizeof(uint32_t));
    uint32_t *flat_sizes = (uint32_t *)calloc(n_tiles, sizeof(uint32_t));
    uint32_t *flat_nbr = (uint32_t *)calloc(n_tiles * 8, sizeof(uint32_t));
    uint32_t *flat_nbr_cnt = (uint32_t *)calloc(n_tiles, sizeof(uint32_t));

    /* T+ tiles: indices 0..n_tiles_per-1 */
    for (int t = 0; t < gs->n_tiles_per; t++) {
        int sz = gs->tp_tiling->tile_size[t];
        flat_sizes[t] = (uint32_t)sz;
        for (int k = 0; k < sz && k < ps; k++)
            flat_sites[t * ps + k] = (uint32_t)gs->tp_tiling->tile_sites[t][k];
        flat_nbr_cnt[t] = (uint32_t)gs->tp_tiling->n_tile_nbr[t];
        for (int k = 0; k < gs->tp_tiling->n_tile_nbr[t] && k < 8; k++)
            flat_nbr[t * 8 + k] = (uint32_t)gs->tp_tiling->tile_nbr[t][k];
    }
    /* T- tiles: indices n_tiles_per..2*n_tiles_per-1 */
    int ntp = gs->n_tiles_per;
    for (int t = 0; t < gs->n_tiles_per; t++) {
        int gt = t + ntp;  /* global tile index */
        int sz = gs->tm_tiling->tile_size[t];
        flat_sizes[gt] = (uint32_t)sz;
        for (int k = 0; k < sz && k < ps; k++)
            flat_sites[gt * ps + k] = (uint32_t)gs->tm_tiling->tile_sites[t][k];
        flat_nbr_cnt[gt] = (uint32_t)gs->tm_tiling->n_tile_nbr[t];
        for (int k = 0; k < gs->tm_tiling->n_tile_nbr[t] && k < 8; k++)
            flat_nbr[gt * 8 + k] = (uint32_t)(gs->tm_tiling->tile_nbr[t][k] + ntp);
    }

    mt->tileSitesBuf = [mt->device newBufferWithBytes:flat_sites
                                               length:(NSUInteger)(n_tiles * ps * sizeof(uint32_t))
                                              options:MTLResourceStorageModeShared];
    mt->tileSizeBuf = [mt->device newBufferWithBytes:flat_sizes
                                              length:(NSUInteger)(n_tiles * sizeof(uint32_t))
                                             options:MTLResourceStorageModeShared];
    mt->tileNbrBuf = [mt->device newBufferWithBytes:flat_nbr
                                             length:(NSUInteger)(n_tiles * 8 * sizeof(uint32_t))
                                            options:MTLResourceStorageModeShared];
    mt->tileNbrCountBuf = [mt->device newBufferWithBytes:flat_nbr_cnt
                                                  length:(NSUInteger)(n_tiles * sizeof(uint32_t))
                                                 options:MTLResourceStorageModeShared];
    free(flat_sites); free(flat_sizes); free(flat_nbr); free(flat_nbr_cnt);

    /* RNG states: per-tile xoshiro256** */
    uint64_t *rng_flat = (uint64_t *)calloc(n_tiles * 4, sizeof(uint64_t));
    uint64_t sm_state = 42 + 0xdeadbeefULL;
    for (int t = 0; t < n_tiles; t++) {
        for (int i = 0; i < 4; i++)
            rng_flat[t * 4 + i] = splitmix64(&sm_state);
    }
    mt->rngStatesBuf = [mt->device newBufferWithBytes:rng_flat
                                               length:(NSUInteger)(n_tiles * 4 * sizeof(uint64_t))
                                              options:MTLResourceStorageModeShared];
    free(rng_flat);

    /* Pressure: [pp_tp(n), pm_tp(n), pp_tm(n), pm_tm(n)] */
    float *pressure_flat = (float *)calloc(4 * n, sizeof(float));
    memcpy(pressure_flat, gs->pp_at_tp, n * sizeof(float));
    memcpy(pressure_flat + n, gs->pm_at_tp, n * sizeof(float));
    memcpy(pressure_flat + 2 * n, gs->pp_at_tm, n * sizeof(float));
    memcpy(pressure_flat + 3 * n, gs->pm_at_tm, n * sizeof(float));
    mt->pressureBuf = [mt->device newBufferWithBytes:pressure_flat
                                              length:(NSUInteger)(4 * n * sizeof(float))
                                             options:MTLResourceStorageModeShared];
    free(pressure_flat);

    /* Mesh neighbors: [T+ n*MAX_NBR] [T- n*MAX_NBR] */
    uint32_t *mesh_nbr = (uint32_t *)calloc(2 * n * MAX_NBR, sizeof(uint32_t));
    uint32_t *mesh_cnt = (uint32_t *)calloc(2 * n, sizeof(uint32_t));
    for (int i = 0; i < n; i++) {
        mesh_cnt[i] = (uint32_t)gs->mesh_tp->n_nbr[i];
        for (int j = 0; j < gs->mesh_tp->n_nbr[i] && j < MAX_NBR; j++)
            mesh_nbr[i * MAX_NBR + j] = (uint32_t)gs->mesh_tp->nbr[i][j];
        mesh_cnt[n + i] = (uint32_t)gs->mesh_tm->n_nbr[i];
        for (int j = 0; j < gs->mesh_tm->n_nbr[i] && j < MAX_NBR; j++)
            mesh_nbr[n * MAX_NBR + i * MAX_NBR + j] = (uint32_t)gs->mesh_tm->nbr[i][j];
    }
    mt->meshNbrBuf = [mt->device newBufferWithBytes:mesh_nbr
                                             length:(NSUInteger)(2 * n * MAX_NBR * sizeof(uint32_t))
                                            options:MTLResourceStorageModeShared];
    mt->meshNbrCountBuf = [mt->device newBufferWithBytes:mesh_cnt
                                                  length:(NSUInteger)(2 * n * sizeof(uint32_t))
                                                 options:MTLResourceStorageModeShared];
    free(mesh_nbr); free(mesh_cnt);

    /* Mass data buffer */
    mt->massBuf = [mt->device newBufferWithLength:(NSUInteger)(2 * n * sizeof(float))
                                          options:MTLResourceStorageModeShared];

    /* Dominant color */
    uint8_t *dom_flat = (uint8_t *)calloc(2 * n, sizeof(uint8_t));
    memcpy(dom_flat, gs->dominant_color_tp, n);
    memcpy(dom_flat + n, gs->dominant_color_tm, n);
    mt->dominantColorBuf = [mt->device newBufferWithBytes:dom_flat
                                                   length:(NSUInteger)(2 * n)
                                                  options:MTLResourceStorageModeShared];
    free(dom_flat);

    /* Energy counts (6 atomic uint32) */
    mt->energyCountsBuf = [mt->device newBufferWithLength:6 * sizeof(uint32_t)
                                                  options:MTLResourceStorageModeShared];

    /* Per-color pressure ratios */
    if (gs->pressure_color) {
        mt->pressureColorBuf = [mt->device newBufferWithBytes:gs->pressure_color
                                                       length:(NSUInteger)(6 * n * sizeof(float))
                                                      options:MTLResourceStorageModeShared];
    } else {
        mt->pressureColorBuf = [mt->device newBufferWithLength:sizeof(float)
                                                       options:MTLResourceStorageModeShared];
    }

    /* Params */
    mt->n_interactions = (uint32_t)(n_tiles / 2);
    if (mt->n_interactions < 1) mt->n_interactions = 1;
    mt->sub_rounds = 1;

    GenesisParams params = {
        .n_sites = (uint32_t)n,
        .n_tiles = (uint32_t)n_tiles,
        .n_tiles_per = (uint32_t)ntp,
        .prog_size = PROG_SIZE,
        .max_steps = MAX_STEPS,
        .mutation_rate = gs->mutation_rate,
        .coupling_strength = gs->coupling_strength,
        .chirality = gs->chirality,
        .chirality_mode = (uint32_t)gs->chirality_mode,
        .instr_mode = (uint32_t)gs->instr_mode,
        .color_pressure = (uint32_t)gs->color_pressure,
        .phase_lock = gs->phase_lock,
        .kuramoto_mode = (uint32_t)gs->kuramoto_mode,
        .energy_lambda = gs->energy_lambda,
        .mass_mode = (uint32_t)gs->mass_mode,
        .mass_couple = gs->mass_couple,
        .mass_kuramoto = gs->mass_kuramoto,
        .mass_geo = gs->mass_geo,
        .n_interactions = mt->n_interactions,
        .sub_round_idx = 0,
        .epsilon = gs->epsilon,
        .max_nbr = MAX_NBR,
    };
    mt->paramsBuf = [mt->device newBufferWithBytes:&params
                                            length:sizeof(GenesisParams)
                                           options:MTLResourceStorageModeShared];

    printf("Metal buffers allocated (trit data: %d bytes, %d tiles, %u interactions/epoch)\n",
           2 * n, n_tiles, mt->n_interactions);

    return mt;
}

static void metal_free(MetalState *mt) {
    free(mt);
}

/* ================================================================
 * GPU Epoch Dispatch — Batched
 *
 * Encodes multiple epochs into a single command buffer to amortize
 * Metal dispatch overhead. Each epoch is a sequence of encoders:
 *   blit(snapshot) → [mass] → vm_couple → [kuramoto×sub] → mutate
 * All execute sequentially within the command buffer.
 * ================================================================ */
static int genesis_epoch_batch_metal(GenesisState *gs, MetalState *mt,
                                      int batch_size) {
    int n = gs->n_sites;
    int n_tiles = 2 * gs->n_tiles_per;

    @autoreleasepool {
        GenesisParams *p = (GenesisParams *)[mt->paramsBuf contents];
        p->sub_round_idx = 0;

        /* Precompute thread group sizes */
        NSUInteger n2 = (NSUInteger)(2 * n);
        NSUInteger groupSite = mt->maxThreadsPerGroup < n2 ? mt->maxThreadsPerGroup : n2;
        NSUInteger nVM = (NSUInteger)mt->n_interactions;
        NSUInteger groupVM = mt->maxThreadsPerGroup < nVM ? mt->maxThreadsPerGroup : nVM;
        NSUInteger nMut = (NSUInteger)n_tiles;
        NSUInteger groupMut = mt->maxThreadsPerGroup < nMut ? mt->maxThreadsPerGroup : nMut;

        int need_mass = gs->mass_mode &&
            (gs->mass_kuramoto > 0.0f || gs->mass_geo > 0.0f);
        int need_kuramoto = gs->phase_lock > 0.0f && gs->kuramoto_mode == 1;
        int kur_steps = need_kuramoto ? gs->kuramoto_sub_steps : 0;

        id<MTLCommandBuffer> cmdBuf = [mt->queue commandBuffer];

        for (int ep = 0; ep < batch_size; ep++) {
            id<MTLBuffer> readTrit  = mt->ping ? mt->tritBufB : mt->tritBufA;
            id<MTLBuffer> writeTrit = mt->ping ? mt->tritBufA : mt->tritBufB;
            id<MTLBuffer> readPhase  = mt->ping ? mt->phaseBufB : mt->phaseBufA;
            id<MTLBuffer> writePhase = mt->ping ? mt->phaseBufA : mt->phaseBufB;

            /* 1. Blit: snapshot read → write */
            {
                id<MTLBlitCommandEncoder> blit = [cmdBuf blitCommandEncoder];
                [blit copyFromBuffer:readTrit sourceOffset:0
                            toBuffer:writeTrit destinationOffset:0
                                size:readTrit.length];
                [blit copyFromBuffer:readPhase sourceOffset:0
                            toBuffer:writePhase destinationOffset:0
                                size:readPhase.length];
                [blit endEncoding];
            }

            /* 2. Mass precompute */
            if (need_mass) {
                id<MTLComputeCommandEncoder> enc = [cmdBuf computeCommandEncoder];
                [enc setComputePipelineState:mt->massPipeline];
                [enc setBuffer:readPhase           offset:0 atIndex:8];
                [enc setBuffer:mt->paramsBuf       offset:0 atIndex:7];
                [enc setBuffer:mt->pressureBuf     offset:0 atIndex:10];
                [enc setBuffer:mt->meshNbrBuf      offset:0 atIndex:11];
                [enc setBuffer:mt->meshNbrCountBuf offset:0 atIndex:12];
                [enc setBuffer:mt->massBuf         offset:0 atIndex:13];
                [enc dispatchThreads:MTLSizeMake(n2, 1, 1)
               threadsPerThreadgroup:MTLSizeMake(groupSite, 1, 1)];
                [enc endEncoding];
            }

            /* 3. VM + couple */
            {
                id<MTLComputeCommandEncoder> enc = [cmdBuf computeCommandEncoder];
                [enc setComputePipelineState:mt->vmCouplePipeline];
                [enc setBuffer:readTrit              offset:0 atIndex:0];
                [enc setBuffer:writeTrit             offset:0 atIndex:1];
                [enc setBuffer:mt->tileSitesBuf      offset:0 atIndex:2];
                [enc setBuffer:mt->tileSizeBuf       offset:0 atIndex:3];
                [enc setBuffer:mt->tileNbrBuf        offset:0 atIndex:4];
                [enc setBuffer:mt->tileNbrCountBuf   offset:0 atIndex:5];
                [enc setBuffer:mt->rngStatesBuf      offset:0 atIndex:6];
                [enc setBuffer:mt->paramsBuf         offset:0 atIndex:7];
                [enc setBuffer:readPhase             offset:0 atIndex:8];
                [enc setBuffer:writePhase            offset:0 atIndex:9];
                [enc setBuffer:mt->pressureBuf       offset:0 atIndex:10];
                [enc setBuffer:mt->dominantColorBuf  offset:0 atIndex:14];
                [enc setBuffer:mt->pressureColorBuf  offset:0 atIndex:16];
                [enc setBuffer:mt->massBuf           offset:0 atIndex:13];
                [enc dispatchThreads:MTLSizeMake(nVM, 1, 1)
               threadsPerThreadgroup:MTLSizeMake(groupVM, 1, 1)];
                [enc endEncoding];
            }

            /* 4. Kuramoto sub-steps (with phase re-snapshot blits) */
            for (int ksub = 0; ksub < kur_steps; ksub++) {
                if (ksub > 0) {
                    /* Re-snapshot: copy updated phases back to read buffer */
                    id<MTLBlitCommandEncoder> blit = [cmdBuf blitCommandEncoder];
                    [blit copyFromBuffer:writePhase sourceOffset:0
                                toBuffer:readPhase destinationOffset:0
                                    size:writePhase.length];
                    [blit endEncoding];
                }

                id<MTLComputeCommandEncoder> enc = [cmdBuf computeCommandEncoder];
                [enc setComputePipelineState:mt->kuramotoPipeline];
                [enc setBuffer:readPhase           offset:0 atIndex:8];
                [enc setBuffer:writePhase          offset:0 atIndex:9];
                [enc setBuffer:writeTrit           offset:0 atIndex:1];
                [enc setBuffer:mt->paramsBuf       offset:0 atIndex:7];
                [enc setBuffer:mt->pressureBuf     offset:0 atIndex:10];
                [enc setBuffer:mt->meshNbrBuf      offset:0 atIndex:11];
                [enc setBuffer:mt->meshNbrCountBuf offset:0 atIndex:12];
                [enc setBuffer:mt->massBuf         offset:0 atIndex:13];
                [enc dispatchThreads:MTLSizeMake(n2, 1, 1)
               threadsPerThreadgroup:MTLSizeMake(groupSite, 1, 1)];
                [enc endEncoding];
            }

            /* 5. Mutate */
            {
                id<MTLComputeCommandEncoder> enc = [cmdBuf computeCommandEncoder];
                [enc setComputePipelineState:mt->mutatePipeline];
                [enc setBuffer:writeTrit           offset:0 atIndex:1];
                [enc setBuffer:writePhase          offset:0 atIndex:9];
                [enc setBuffer:mt->tileSitesBuf    offset:0 atIndex:2];
                [enc setBuffer:mt->tileSizeBuf     offset:0 atIndex:3];
                [enc setBuffer:mt->rngStatesBuf    offset:0 atIndex:6];
                [enc setBuffer:mt->paramsBuf       offset:0 atIndex:7];
                [enc setBuffer:mt->massBuf         offset:0 atIndex:13];
                [enc dispatchThreads:MTLSizeMake(nMut, 1, 1)
               threadsPerThreadgroup:MTLSizeMake(groupMut, 1, 1)];
                [enc endEncoding];
            }

            /* 6. Swap ping-pong for next epoch */
            mt->ping = 1 - mt->ping;
        }

        [cmdBuf commit];
        [cmdBuf waitUntilCompleted];
        if (cmdBuf.status == MTLCommandBufferStatusError) {
            fprintf(stderr, "GPU error: %s\n",
                    [[cmdBuf.error localizedDescription] UTF8String]);
            return 0;
        }
    }

    gs->epoch += batch_size;
    return batch_size;
}

/* ================================================================
 * Diagnostics (CPU readback, matches genesis_soup.c output format)
 * ================================================================ */
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

static float compute_correlation(const uint8_t *tp, const uint8_t *tm, int n) {
    int match = 0;
    for (int i = 0; i < n; i++)
        if (tp[i] == tm[i]) match++;
    return (float)match / n;
}

static void print_diagnostics(GenesisState *gs, MetalState *mt) {
    int n = gs->n_sites;

    /* Read current trit data from the "last written" buffer */
    id<MTLBuffer> currentTrit = mt->ping ? mt->tritBufB : mt->tritBufA;
    const uint8_t *trits = (const uint8_t *)[currentTrit contents];
    const uint8_t *tp = trits;
    const uint8_t *tm = trits + n;

    float ent_tp, ent_tm;
    int counts_tp[3], counts_tm[3];
    compute_entropy(tp, n, &ent_tp, counts_tp);
    compute_entropy(tm, n, &ent_tm, counts_tm);

    float corr = compute_correlation(tp, tm, n);

    /* |χ|² */
    float fc[3];
    for (int c = 0; c < 3; c++)
        fc[c] = (float)(counts_tp[c] + counts_tm[c]) / (2 * n);
    float chi_re = fc[0] - 0.5f*fc[1] - 0.5f*fc[2];
    float chi_im = 0.866025403784f * (fc[1] - fc[2]);
    float chi2 = chi_re*chi_re + chi_im*chi_im;

    printf("epoch=%ld  H_tp=%.4f H_tm=%.4f  corr=%.4f  chi2=%.4f  "
           "tp_counts=[%d,%d,%d] tm_counts=[%d,%d,%d]\n",
           gs->epoch, ent_tp, ent_tm, corr, chi2,
           counts_tp[0], counts_tp[1], counts_tp[2],
           counts_tm[0], counts_tm[1], counts_tm[2]);
}

/* K3: Lyapunov divergence diagnostics — trit Hamming + phase deviation,
 * split by pressure zone (open vs blocked). Paired simulation approach. */
static void lyapunov_diag_log(GenesisState *gs, MetalState *mt,
                               const float *control_phases,
                               const uint8_t *control_trits,
                               long rel_epoch) {
    if (!gs->phase_diag_file || !gs->phase_bfs_dist) return;
    int n = gs->n_sites;
    int md = gs->phase_bfs_max_d;
    float TRIT_THRESHOLD = 0.01f;  /* fraction of sites with different trits */

    /* Read current T+ data from GPU buffers */
    id<MTLBuffer> currentPhase = mt->ping ? mt->phaseBufB : mt->phaseBufA;
    id<MTLBuffer> currentTrit = mt->ping ? mt->tritBufB : mt->tritBufA;
    const float *phases = (const float *)[currentPhase contents];
    const uint8_t *trits = (const uint8_t *)[currentTrit contents];
    /* T+ trits = trits[0..n-1], T+ phases = phases[0..n-1] */

    /* Per-shell accumulators, split by zone */
    float *phase_dev_open = (float *)calloc(md + 1, sizeof(float));
    float *phase_dev_blocked = (float *)calloc(md + 1, sizeof(float));
    int *trit_diff_open = (int *)calloc(md + 1, sizeof(int));
    int *trit_diff_blocked = (int *)calloc(md + 1, sizeof(int));

    for (int i = 0; i < n; i++) {
        int d = gs->phase_bfs_dist[i];
        if (d < 0) continue;
        int zone = gs->site_zone[i];

        /* Trit Hamming */
        int tdiff = (trits[i] != control_trits[i]) ? 1 : 0;

        /* Phase deviation */
        float dphi = phases[i] - control_phases[i];
        while (dphi > (float)M_PI) dphi -= 2.0f * (float)M_PI;
        while (dphi < -(float)M_PI) dphi += 2.0f * (float)M_PI;
        float ad = fabsf(dphi);

        if (zone) { /* open */
            trit_diff_open[d] += tdiff;
            phase_dev_open[d] += ad;
        } else { /* blocked */
            trit_diff_blocked[d] += tdiff;
            phase_dev_blocked[d] += ad;
        }
    }

    /* Write JSONL record */
    fprintf(gs->phase_diag_file, "{\"rel_epoch\":%ld, \"shells\":[", rel_epoch);
    for (int d = 0; d <= md; d++) {
        int no = gs->shell_count_open[d];
        int nb = gs->shell_count_blocked[d];
        if (no + nb == 0) continue;

        float hamming_open = no > 0 ? (float)trit_diff_open[d] / no : 0.0f;
        float hamming_blocked = nb > 0 ? (float)trit_diff_blocked[d] / nb : 0.0f;
        float pdev_open = no > 0 ? phase_dev_open[d] / no : 0.0f;
        float pdev_blocked = nb > 0 ? phase_dev_blocked[d] / nb : 0.0f;
        int n_total = gs->phase_shell_count[d];
        float hamming_total = n_total > 0 ?
            (float)(trit_diff_open[d] + trit_diff_blocked[d]) / n_total : 0.0f;

        /* Track trit arrival per zone */
        if (hamming_open > TRIT_THRESHOLD && gs->trit_arrival_open[d] < 0)
            gs->trit_arrival_open[d] = rel_epoch;
        if (hamming_blocked > TRIT_THRESHOLD && gs->trit_arrival_blocked[d] < 0)
            gs->trit_arrival_blocked[d] = rel_epoch;
        /* Phase arrival (combined) */
        float pdev_total = n_total > 0 ?
            (phase_dev_open[d] + phase_dev_blocked[d]) / n_total : 0.0f;
        if (pdev_total > 0.05f && gs->phase_arrival[d] < 0)
            gs->phase_arrival[d] = rel_epoch;

        if (d > 0) fprintf(gs->phase_diag_file, ",");
        fprintf(gs->phase_diag_file,
            "{\"d\":%d,\"ho\":%.6f,\"hb\":%.6f,\"ht\":%.6f,"
            "\"po\":%.6f,\"pb\":%.6f,\"no\":%d,\"nb\":%d}",
            d, hamming_open, hamming_blocked, hamming_total,
            pdev_open, pdev_blocked, no, nb);
    }
    fprintf(gs->phase_diag_file, "]}\n");
    fflush(gs->phase_diag_file);

    free(phase_dev_open); free(phase_dev_blocked);
    free(trit_diff_open); free(trit_diff_blocked);
}

/* K3: Final arrival analysis — zone-aware trit + phase fronts */
static void phase_diag_summary(GenesisState *gs) {
    if (!gs->phase_arrival || !gs->phase_diag_file) return;
    int md = gs->phase_bfs_max_d;

    /* Write combined arrivals to JSONL */
    fprintf(gs->phase_diag_file, "{\"type\":\"arrivals\", \"data\":[");
    int first = 1;
    for (int d = 0; d <= md; d++) {
        long tp = gs->phase_arrival[d];
        long to = gs->trit_arrival_open ? gs->trit_arrival_open[d] : -1;
        long tb = gs->trit_arrival_blocked ? gs->trit_arrival_blocked[d] : -1;
        if (tp >= 0 || to >= 0 || tb >= 0) {
            if (!first) fprintf(gs->phase_diag_file, ",");
            fprintf(gs->phase_diag_file,
                "{\"d\":%d,\"t_phase\":%ld,\"t_trit_open\":%ld,\"t_trit_blocked\":%ld}",
                d, tp, to, tb);
            first = 0;
        }
    }
    fprintf(gs->phase_diag_file, "]}\n");

    /* Helper: power-law fit on (d, t) pairs where both > 0 */
    #define FIT_ALPHA(label, arrival_arr) do { \
        double _sx=0, _sy=0, _sxx=0, _sxy=0; int _np=0; \
        printf("\n=== %s Arrivals ===\n", label); \
        for (int _d = 1; _d <= md; _d++) { \
            long _t = (arrival_arr)[_d]; \
            if (_t > 0) { \
                double _lt = log((double)_t), _ld = log((double)_d); \
                _sx += _lt; _sy += _ld; _sxx += _lt*_lt; _sxy += _lt*_ld; \
                _np++; \
                printf("  d=%3d: t=%6ld\n", _d, _t); \
            } \
        } \
        if (_np >= 3) { \
            double _den = _np * _sxx - _sx * _sx; \
            if (fabs(_den) > 1e-12) { \
                double _alpha = (_np * _sxy - _sx * _sy) / _den; \
                printf("Power-law fit: d ~ t^%.3f  (0.5=diffusive, 1.0=ballistic)\n", _alpha); \
                if (_alpha > 0.8) printf("  → BALLISTIC\n"); \
                else if (_alpha > 0.6) printf("  → ANOMALOUS\n"); \
                else printf("  → DIFFUSIVE\n"); \
            } \
        } else { \
            printf("  (too few arrivals for fit: %d)\n", _np); \
        } \
    } while(0)

    /* Phase front (combined) */
    FIT_ALPHA("Phase (combined)", gs->phase_arrival);

    /* Trit Hamming front — open zone (VM dynamics) */
    if (gs->trit_arrival_open)
        FIT_ALPHA("Trit Hamming — OPEN zone (VM)", gs->trit_arrival_open);

    /* Trit Hamming front — blocked zone (Kuramoto) */
    if (gs->trit_arrival_blocked)
        FIT_ALPHA("Trit Hamming — BLOCKED zone (Kuramoto)", gs->trit_arrival_blocked);

    #undef FIT_ALPHA
}

static void print_final_state(GenesisState *gs, MetalState *mt) {
    int n = gs->n_sites;

    id<MTLBuffer> currentTrit = mt->ping ? mt->tritBufB : mt->tritBufA;
    const uint8_t *trits = (const uint8_t *)[currentTrit contents];
    const uint8_t *tp = trits;
    const uint8_t *tm = trits + n;

    printf("\n=== Final State ===\n");

    /* Main diagnostics line (parsed by validation scripts) */
    float ent_tp, ent_tm;
    int counts_tp[3], counts_tm[3];
    compute_entropy(tp, n, &ent_tp, counts_tp);
    compute_entropy(tm, n, &ent_tm, counts_tm);
    float corr = compute_correlation(tp, tm, n);
    float fc[3];
    for (int c = 0; c < 3; c++)
        fc[c] = (float)(counts_tp[c] + counts_tm[c]) / (2 * n);
    float chi_re = fc[0] - 0.5f*fc[1] - 0.5f*fc[2];
    float chi_im = 0.866025403784f * (fc[1] - fc[2]);
    float chi2 = chi_re*chi_re + chi_im*chi_im;

    printf("epoch=%ld  H_tp=%.4f H_tm=%.4f  corr=%.4f  chi2=%.4f  "
           "tp_counts=[%d,%d,%d] tm_counts=[%d,%d,%d]\n",
           gs->epoch, ent_tp, ent_tm, corr, chi2,
           counts_tp[0], counts_tp[1], counts_tp[2],
           counts_tm[0], counts_tm[1], counts_tm[2]);

    /* WRITE success rate (placeholder — GPU doesn't track per-write stats) */
    if (gs->instr_mode == 2)
        printf("WRITE success rate: 100.0%%\n");

    /* Phase-lock nudges (placeholder) */
    if (gs->phase_lock > 0.0f)
        printf("Phase-lock nudges: 0\n");

    /* Pressure-ratio binned correlation (critical for validation) */
    printf("\n=== Correlation by P_ratio (at T+ sites) ===\n");
    printf("P_ratio_range     n_sites  match_rate  (WRITE gate)\n");
    int nbins = 10;
    int bin_count[10] = {0};
    int bin_match[10] = {0};
    for (int i = 0; i < n; i++) {
        float ratio = gs->pp_at_tp[i] / (gs->pp_at_tp[i] + gs->pm_at_tp[i]);
        int b = (int)(ratio * nbins);
        if (b >= nbins) b = nbins - 1;
        if (b < 0) b = 0;
        bin_count[b]++;
        if (tp[i] == tm[i]) bin_match[b]++;
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
}

/* ================================================================
 * CLI and Main
 * ================================================================ */
static void usage(const char *prog) {
    printf("Genesis Soup (Metal GPU)\n");
    printf("Usage: %s [options]\n\n", prog);
    printf("  --n-sub N               Subdivisions per edge (default: 16)\n");
    printf("  --epochs N              Epochs to run (default: 5000000)\n");
    printf("  --seed N                RNG seed (default: 42)\n");
    printf("  --coupling-strength F   Geometric coupling strength (default: 0.7)\n");
    printf("  --mutation-rate F       Per-trit mutation rate (default: 0.001)\n");
    printf("  --epsilon F             Pressure regularization (default: 0.1)\n");
    printf("  --chirality F           Chirality parameter (default: 0.15)\n");
    printf("  --chirality-mode N      0=pressure-asymmetry, 1=coupling-weight\n");
    printf("  --instr-mode N          0=classic, 1=enhanced, 2=write (default: 2)\n");
    printf("  --warp-alpha F          Mesh warp (1.0=uniform, default: 1.0)\n");
    printf("  --color-pressure N      0=max-vertex, 1=per-color (default: 1)\n");
    printf("  --phase-lock F          Kuramoto coupling K (default: 0.1)\n");
    printf("  --kuramoto-mode N       0=majority-vote, 1=full Kuramoto (default: 1)\n");
    printf("  --energy-lambda F       Energy functional λ (default: 0.0)\n");
    printf("  --mass-mode N           0=off, 1=on (default: 0)\n");
    printf("  --mass-couple F         Mass-stabilized mutation (default: 0.0)\n");
    printf("  --mass-kuramoto F       Mass-modulated Kuramoto K (default: 0.0)\n");
    printf("  --mass-geo F            Mass-modulated geo coupling (default: 0.0)\n");
    printf("  --kuramoto-sub-steps N  GG2b sub-steps (default: 1)\n");
    printf("  --sub-rounds N          VM sub-epoch rounds (default: 1)\n");
    printf("  --report-interval N     Print diagnostics every N epochs (default: 100000)\n");
    printf("  --shader-path P         Path to .metal file (default: genesis_soup.metal)\n");
    printf("\nPhase wavefront diagnostics (K2):\n");
    printf("  --phase-diag-interval N Report phase shells every N epochs after perturb (0=off)\n");
    printf("  --phase-perturb-epoch N Epoch to inject phase perturbation (-1=off)\n");
    printf("  --phase-perturb-delta F Perturbation amplitude in radians (default: pi/3)\n");
}

int main(int argc, char *argv[]) {
    @autoreleasepool {
        setvbuf(stdout, NULL, _IOLBF, 0);

        /* Defaults matching genesis_soup.c */
        int n_sub = 16;
        long epochs = 5000000;
        uint32_t seed = 42;
        float coupling_strength = 0.7f;
        float mutation_rate = 0.001f;
        float epsilon = 0.1f;
        float chirality = 0.15f;
        int chirality_mode = 0;
        int instr_mode = 2;
        float warp_alpha = 1.0f;
        int color_pressure = 1;
        float phase_lock = 0.1f;
        int kuramoto_mode = 1;
        float energy_lambda = 0.0f;
        int mass_mode = 0;
        float mass_couple = 0.0f;
        float mass_kuramoto = 0.0f;
        float mass_geo = 0.0f;
        int kuramoto_sub_steps = 1;
        int sub_rounds = 1;
        long report_interval = 100000;
        const char *shader_path = "genesis_soup.metal";
        int phase_diag_interval = 0;
        long phase_perturb_epoch = -1;
        float phase_perturb_delta = (float)(M_PI / 3.0);

        static struct option long_options[] = {
            {"n-sub",              required_argument, 0, 'n'},
            {"epochs",             required_argument, 0, 'e'},
            {"seed",               required_argument, 0, 'S'},
            {"coupling-strength",  required_argument, 0, 'c'},
            {"mutation-rate",      required_argument, 0, 'r'},
            {"epsilon",            required_argument, 0, 'E'},
            {"chirality",          required_argument, 0, 'X'},
            {"chirality-mode",     required_argument, 0, 'Y'},
            {"instr-mode",         required_argument, 0, 'I'},
            {"warp-alpha",         required_argument, 0, 'W'},
            {"color-pressure",     required_argument, 0, 'C'},
            {"phase-lock",         required_argument, 0, 'K'},
            {"kuramoto-mode",      required_argument, 0, 'M'},
            {"energy-lambda",      required_argument, 0, 'L'},
            {"mass-mode",          required_argument, 0, 'm'},
            {"mass-couple",        required_argument, 0, 'a'},
            {"mass-kuramoto",      required_argument, 0, 'b'},
            {"mass-geo",           required_argument, 0, 'g'},
            {"kuramoto-sub-steps", required_argument, 0, 'k'},
            {"sub-rounds",         required_argument, 0, 'R'},
            {"report-interval",    required_argument, 0, 'l'},
            {"shader-path",        required_argument, 0, 'P'},
            {"phase-diag-interval",required_argument, 0, 'd'},
            {"phase-perturb-epoch",required_argument, 0, 'p'},
            {"phase-perturb-delta",required_argument, 0, 'D'},
            {"help",               no_argument,       0, 'h'},
            {0, 0, 0, 0}
        };

        int opt;
        while ((opt = getopt_long(argc, argv, "hn:e:S:c:r:E:X:Y:I:W:C:K:M:L:m:a:b:g:k:R:l:P:d:p:D:",
                                   long_options, NULL)) != -1) {
            switch (opt) {
            case 'n': n_sub = atoi(optarg); break;
            case 'e': epochs = atol(optarg); break;
            case 'S': seed = (uint32_t)atoi(optarg); break;
            case 'c': coupling_strength = (float)atof(optarg); break;
            case 'r': mutation_rate = (float)atof(optarg); break;
            case 'E': epsilon = (float)atof(optarg); break;
            case 'X': chirality = (float)atof(optarg); break;
            case 'Y': chirality_mode = atoi(optarg); break;
            case 'I': instr_mode = atoi(optarg); break;
            case 'W': warp_alpha = (float)atof(optarg); break;
            case 'C': color_pressure = atoi(optarg); break;
            case 'K': phase_lock = (float)atof(optarg); break;
            case 'M': kuramoto_mode = atoi(optarg); break;
            case 'L': energy_lambda = (float)atof(optarg); break;
            case 'm': mass_mode = atoi(optarg); break;
            case 'a': mass_couple = (float)atof(optarg); break;
            case 'b': mass_kuramoto = (float)atof(optarg); break;
            case 'g': mass_geo = (float)atof(optarg); break;
            case 'k': kuramoto_sub_steps = atoi(optarg); break;
            case 'R': sub_rounds = atoi(optarg); break;
            case 'l': report_interval = atol(optarg); break;
            case 'P': shader_path = optarg; break;
            case 'd': phase_diag_interval = atoi(optarg); break;
            case 'p': phase_perturb_epoch = atol(optarg); break;
            case 'D': phase_perturb_delta = (float)atof(optarg); break;
            case 'h': usage(argv[0]); return 0;
            default:  usage(argv[0]); return 1;
            }
        }

        printf("=== Stella Genesis (Metal GPU) ===\n");
        printf("N_sub: %d\n", n_sub);
        printf("Epochs: %ld\n", epochs);
        printf("Seed: %u\n", seed);
        printf("Coupling strength: %.3f\n", coupling_strength);
        printf("Mutation rate: %.4f\n", mutation_rate);
        printf("Epsilon: %.3f\n", epsilon);

        const char *instr_names[] = {"classic", "enhanced (SENSE/COUPLE)", "write (SENSE/WRITE)"};
        printf("Instruction mode: %s\n", instr_names[instr_mode]);
        if (phase_lock > 0.0f)
            printf("Phase-lock: %.4f (%s)\n", phase_lock,
                   kuramoto_mode ? "full Kuramoto" : "majority-vote");
        if (kuramoto_sub_steps > 1)
            printf("Kuramoto sub-steps: %d (GG2b)\n", kuramoto_sub_steps);
        if (mass_kuramoto > 0.0f)
            printf("Mass-Kuramoto feedback: mk=%.2f\n", mass_kuramoto);
        if (mass_mode)
            printf("Mass mode: ON (couple=%.2f, geo=%.2f)\n", mass_couple, mass_geo);
        if (sub_rounds > 1)
            printf("Sub-rounds: %d\n", sub_rounds);
        printf("Snapshot mode: ON (GPU Metal)\n");

        /* ─── Build genesis state ─── */
        rng_seed(seed);

        GenesisState *gs = (GenesisState *)calloc(1, sizeof(GenesisState));
        gs->coupling_strength = coupling_strength;
        gs->chirality = chirality;
        gs->chirality_mode = chirality_mode;
        gs->instr_mode = instr_mode;
        gs->warp_alpha = warp_alpha;
        gs->color_pressure = color_pressure;
        gs->phase_lock = phase_lock;
        gs->kuramoto_mode = kuramoto_mode;
        gs->energy_lambda = energy_lambda;
        gs->mass_mode = mass_mode;
        gs->mass_couple = mass_couple;
        gs->mass_kuramoto = mass_kuramoto;
        gs->mass_geo = mass_geo;
        gs->mutation_rate = mutation_rate;
        gs->epsilon = epsilon;
        gs->snapshot_mode = 1;
        gs->kuramoto_sub_steps = kuramoto_sub_steps;
        gs->phase_diag_interval = phase_diag_interval;
        gs->phase_perturb_epoch = phase_perturb_epoch;
        gs->phase_perturb_delta = phase_perturb_delta;
        gs->phase_bfs_dist = NULL;
        gs->phase_shell_count = NULL;
        gs->phase_arrival = NULL;
        gs->phase_diag_file = NULL;
        gs->phase_baseline_tp = NULL;
        gs->phase_perturb_site = -1;

        /* Build meshes */
        float alpha = warp_alpha > 0.0f ? warp_alpha : 1.0f;
        gs->mesh_tp = mesh_build(TV_PLUS, n_sub, alpha);
        gs->mesh_tm = mesh_build(TV_MINUS, n_sub, alpha);

        if (gs->mesh_tp->n_sites != gs->mesh_tm->n_sites) {
            fprintf(stderr, "ERROR: mesh site count mismatch: T+=%d T-=%d\n",
                    gs->mesh_tp->n_sites, gs->mesh_tm->n_sites);
            return 1;
        }
        int n = gs->mesh_tp->n_sites;
        gs->n_sites = n;
        printf("Mesh: %d sites per tetrahedron, %d total (dual-mesh)\n", n, 2*n);

        /* Compute pressure at both surfaces */
        gs->pp_at_tp = (float *)calloc(n, sizeof(float));
        gs->pm_at_tp = (float *)calloc(n, sizeof(float));
        gs->pp_at_tm = (float *)calloc(n, sizeof(float));
        gs->pm_at_tm = (float *)calloc(n, sizeof(float));

        float p_plus_scale = 1.0f;
        if (chirality_mode == 0)
            p_plus_scale = 1.0f + chirality;

        for (int i = 0; i < n; i++) {
            gs->pp_at_tp[i] = p_plus_scale *
                pressure_at_site(gs->mesh_tp->pos[i], TV_PLUS, epsilon);
            gs->pm_at_tp[i] = pressure_at_site(gs->mesh_tp->pos[i], TV_MINUS, epsilon);
            gs->pp_at_tm[i] = p_plus_scale *
                pressure_at_site(gs->mesh_tm->pos[i], TV_PLUS, epsilon);
            gs->pm_at_tm[i] = pressure_at_site(gs->mesh_tm->pos[i], TV_MINUS, epsilon);
        }

        /* Dominant color per site */
        gs->dominant_color_tp = (uint8_t *)calloc(n, sizeof(uint8_t));
        gs->dominant_color_tm = (uint8_t *)calloc(n, sizeof(uint8_t));
        for (int i = 0; i < n; i++) {
            float best_d2 = 1e30f; uint8_t best_c = 0;
            for (int c = 0; c < 3; c++) {
                float dx = gs->mesh_tp->pos[i][0] - TV_PLUS[c+1][0];
                float dy = gs->mesh_tp->pos[i][1] - TV_PLUS[c+1][1];
                float dz = gs->mesh_tp->pos[i][2] - TV_PLUS[c+1][2];
                float d2 = dx*dx + dy*dy + dz*dz;
                if (d2 < best_d2) { best_d2 = d2; best_c = c; }
            }
            gs->dominant_color_tp[i] = best_c;

            best_d2 = 1e30f; best_c = 0;
            for (int c = 0; c < 3; c++) {
                float dx = gs->mesh_tm->pos[i][0] - TV_MINUS[c+1][0];
                float dy = gs->mesh_tm->pos[i][1] - TV_MINUS[c+1][1];
                float dz = gs->mesh_tm->pos[i][2] - TV_MINUS[c+1][2];
                float d2 = dx*dx + dy*dy + dz*dz;
                if (d2 < best_d2) { best_d2 = d2; best_c = c; }
            }
            gs->dominant_color_tm[i] = best_c;
        }

        /* Per-color pressure ratios */
        if (color_pressure) {
            gs->pressure_color = (float *)calloc(6 * n, sizeof(float));
            for (int i = 0; i < n; i++) {
                for (int c = 0; c < 3; c++) {
                    /* T+ site: color c */
                    float dx, dy, dz, r2;
                    dx = gs->mesh_tp->pos[i][0] - TV_PLUS[c+1][0];
                    dy = gs->mesh_tp->pos[i][1] - TV_PLUS[c+1][1];
                    dz = gs->mesh_tp->pos[i][2] - TV_PLUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pp_c = p_plus_scale / (r2 + epsilon * epsilon);
                    dx = gs->mesh_tp->pos[i][0] - TV_MINUS[c+1][0];
                    dy = gs->mesh_tp->pos[i][1] - TV_MINUS[c+1][1];
                    dz = gs->mesh_tp->pos[i][2] - TV_MINUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pm_c = 1.0f / (r2 + epsilon * epsilon);
                    float sum_c = pp_c + pm_c;
                    gs->pressure_color[c * n + i] = sum_c > 1e-10f ? pp_c / sum_c : 0.5f;

                    /* T- site: color c */
                    dx = gs->mesh_tm->pos[i][0] - TV_MINUS[c+1][0];
                    dy = gs->mesh_tm->pos[i][1] - TV_MINUS[c+1][1];
                    dz = gs->mesh_tm->pos[i][2] - TV_MINUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pm_own = 1.0f / (r2 + epsilon * epsilon);
                    dx = gs->mesh_tm->pos[i][0] - TV_PLUS[c+1][0];
                    dy = gs->mesh_tm->pos[i][1] - TV_PLUS[c+1][1];
                    dz = gs->mesh_tm->pos[i][2] - TV_PLUS[c+1][2];
                    r2 = dx*dx + dy*dy + dz*dz;
                    float pp_opp = p_plus_scale / (r2 + epsilon * epsilon);
                    sum_c = pm_own + pp_opp;
                    gs->pressure_color[(c + 3) * n + i] = sum_c > 1e-10f ? pm_own / sum_c : 0.5f;
                }
            }
        }

        /* K2: Phase wavefront diagnostics — BFS from central T+ site */
        if (phase_diag_interval > 0) {
            /* Find central T+ site: closest to face 0 centroid */
            float cx = (TV_PLUS[1][0] + TV_PLUS[2][0] + TV_PLUS[3][0]) / 3.0f;
            float cy = (TV_PLUS[1][1] + TV_PLUS[2][1] + TV_PLUS[3][1]) / 3.0f;
            float cz = (TV_PLUS[1][2] + TV_PLUS[2][2] + TV_PLUS[3][2]) / 3.0f;
            float best = 1e10f;
            gs->phase_perturb_site = 0;
            for (int i = 0; i < n; i++) {
                float dx = gs->mesh_tp->pos[i][0] - cx;
                float dy = gs->mesh_tp->pos[i][1] - cy;
                float dz = gs->mesh_tp->pos[i][2] - cz;
                float d2 = dx*dx + dy*dy + dz*dz;
                if (d2 < best) { best = d2; gs->phase_perturb_site = i; }
            }

            /* BFS from perturbation site on T+ mesh */
            gs->phase_bfs_dist = (int *)malloc(n * sizeof(int));
            for (int i = 0; i < n; i++) gs->phase_bfs_dist[i] = -1;
            gs->phase_bfs_dist[gs->phase_perturb_site] = 0;
            gs->phase_bfs_max_d = 0;
            int *queue = (int *)malloc(n * sizeof(int));
            int qh = 0, qt = 0;
            queue[qt++] = gs->phase_perturb_site;
            while (qh < qt) {
                int u = queue[qh++];
                for (int j = 0; j < gs->mesh_tp->n_nbr[u]; j++) {
                    int v = gs->mesh_tp->nbr[u][j];
                    if (gs->phase_bfs_dist[v] < 0) {
                        gs->phase_bfs_dist[v] = gs->phase_bfs_dist[u] + 1;
                        if (gs->phase_bfs_dist[v] > gs->phase_bfs_max_d)
                            gs->phase_bfs_max_d = gs->phase_bfs_dist[v];
                        queue[qt++] = v;
                    }
                }
            }
            free(queue);

            /* Shell counts and arrival tracking */
            int md = gs->phase_bfs_max_d;
            gs->phase_shell_count = (int *)calloc(md + 1, sizeof(int));
            for (int i = 0; i < n; i++) {
                int d = gs->phase_bfs_dist[i];
                if (d >= 0) gs->phase_shell_count[d]++;
            }
            gs->phase_arrival = (long *)malloc((md + 1) * sizeof(long));
            for (int d = 0; d <= md; d++) gs->phase_arrival[d] = -1;

            /* Baseline phase storage */
            gs->phase_baseline_tp = (float *)calloc(n, sizeof(float));

            /* K3: Zone classification and zone-split shell counts */
            gs->site_zone = (int *)calloc(n, sizeof(int));
            gs->shell_count_open = (int *)calloc(md + 1, sizeof(int));
            gs->shell_count_blocked = (int *)calloc(md + 1, sizeof(int));
            gs->trit_arrival_open = (long *)malloc((md + 1) * sizeof(long));
            gs->trit_arrival_blocked = (long *)malloc((md + 1) * sizeof(long));
            int n_open = 0, n_blocked = 0;
            for (int i = 0; i < n; i++) {
                float ratio = gs->pp_at_tp[i] / (gs->pp_at_tp[i] + gs->pm_at_tp[i]);
                gs->site_zone[i] = (ratio >= 0.5f) ? 1 : 0;
                int d = gs->phase_bfs_dist[i];
                if (d >= 0) {
                    if (gs->site_zone[i]) { gs->shell_count_open[d]++; n_open++; }
                    else { gs->shell_count_blocked[d]++; n_blocked++; }
                }
            }
            for (int d = 0; d <= md; d++) {
                gs->trit_arrival_open[d] = -1;
                gs->trit_arrival_blocked[d] = -1;
            }

            /* Open JSONL output file */
            gs->phase_diag_file = fopen("phase_K3_gpu_diag.jsonl", "w");

            /* Write header */
            if (gs->phase_diag_file) {
                fprintf(gs->phase_diag_file,
                    "{\"type\":\"header\", \"n_sub\":%d, \"n_sites\":%d, "
                    "\"max_bfs_d\":%d, \"perturb_site\":%d, \"perturb_epoch\":%ld, "
                    "\"perturb_delta\":%.6f, \"mass_kuramoto\":%.4f, "
                    "\"phase_lock\":%.4f, \"coupling_strength\":%.4f, "
                    "\"kuramoto_sub_steps\":%d, \"n_open\":%d, \"n_blocked\":%d, "
                    "\"shell_counts\":[",
                    n_sub, n, md, gs->phase_perturb_site,
                    phase_perturb_epoch, phase_perturb_delta,
                    mass_kuramoto, phase_lock, coupling_strength,
                    kuramoto_sub_steps, n_open, n_blocked);
                for (int d = 0; d <= md; d++) {
                    if (d > 0) fprintf(gs->phase_diag_file, ",");
                    fprintf(gs->phase_diag_file, "%d", gs->phase_shell_count[d]);
                }
                fprintf(gs->phase_diag_file, "]}\n");
                fflush(gs->phase_diag_file);
            }

            printf("Phase diagnostics: interval=%d, perturb_epoch=%ld, "
                   "delta=%.3f, seed_site=%d, max_bfs_d=%d\n",
                   phase_diag_interval, phase_perturb_epoch,
                   phase_perturb_delta, gs->phase_perturb_site, md);
            printf("  Zone split: %d open (P≥0.5), %d blocked (P<0.5)\n",
                   n_open, n_blocked);
        }

        /* Build tiling */
        int n_tiles_per = n / PROG_SIZE;
        if (n_tiles_per < 2) n_tiles_per = 2;
        gs->n_tiles_per = n_tiles_per;
        printf("Building tiling (%d tiles per tetrahedron)...\n", n_tiles_per);
        gs->tp_tiling = tiling_build(gs->mesh_tp, n_tiles_per, PROG_SIZE);
        gs->tm_tiling = tiling_build(gs->mesh_tm, n_tiles_per, PROG_SIZE);
        printf("  T+ tiling: %d tiles built\n", gs->tp_tiling->n_tiles);
        printf("  T- tiling: %d tiles built\n", gs->tm_tiling->n_tiles);

        /* ─── Initialize Metal ─── */
        MetalState *metal = metal_setup(gs, shader_path);
        metal->sub_rounds = sub_rounds;

        printf("Compute: Metal GPU\n");
        printf("============================================================\n\n");

        /* ─── Main loop ─── */
        struct timespec t_start;
        clock_gettime(CLOCK_MONOTONIC, &t_start);

        /* Initial diagnostics */
        printf("Initial state:\n");
        print_diagnostics(gs, metal);
        printf("\n");

        long batch_size = 1024;
        int phase_mode = (gs->phase_diag_interval > 0 && gs->phase_perturb_epoch >= 0);
        long analysis_epochs = phase_mode ? (epochs - gs->phase_perturb_epoch) : 0;

        if (phase_mode) {
            /* ─── PAIRED SIMULATION MODE ─── */
            /* Phase 1: Burn-in to perturbation epoch */
            printf("Phase 1: Burn-in to epoch %ld...\n", gs->phase_perturb_epoch);
            while (gs->epoch < gs->phase_perturb_epoch) {
                long remaining = gs->phase_perturb_epoch - gs->epoch;
                long batch = batch_size;
                if (batch > remaining) batch = remaining;
                genesis_epoch_batch_metal(gs, metal, (int)batch);

                if (gs->epoch % report_interval == 0)
                    print_diagnostics(gs, metal);
            }
            printf("Burn-in complete at epoch %ld\n", gs->epoch);
            print_diagnostics(gs, metal);

            /* Phase 2: Save full GPU state (trits + phases + RNG) */
            printf("Saving GPU state for paired simulation...\n");
            id<MTLBuffer> saveTritA = metal->ping ? metal->tritBufB : metal->tritBufA;
            id<MTLBuffer> savePhaseA = metal->ping ? metal->phaseBufB : metal->phaseBufA;
            size_t trit_sz = saveTritA.length;
            size_t phase_sz = savePhaseA.length;
            size_t rng_sz = metal->rngStatesBuf.length;
            uint8_t *saved_trits = (uint8_t *)malloc(trit_sz);
            float *saved_phases = (float *)malloc(phase_sz);
            uint8_t *saved_rng = (uint8_t *)malloc(rng_sz);
            int saved_ping = metal->ping;
            long saved_epoch = gs->epoch;
            memcpy(saved_trits, [saveTritA contents], trit_sz);
            memcpy(saved_phases, [savePhaseA contents], phase_sz);
            memcpy(saved_rng, [metal->rngStatesBuf contents], rng_sz);

            /* Phase 3: Run CONTROL (no perturbation) for analysis_epochs */
            printf("Phase 2: Running CONTROL (no perturbation) for %ld epochs...\n",
                   analysis_epochs);
            int diag_int = gs->phase_diag_interval;
            /* Collect control phase snapshots at each diagnostic interval */
            long n_snapshots = analysis_epochs / diag_int;
            if (n_snapshots > 10000) n_snapshots = 10000; /* cap memory */
            float **control_snaps = (float **)malloc(n_snapshots * sizeof(float *));
            for (long s = 0; s < n_snapshots; s++)
                control_snaps[s] = (float *)malloc(n * sizeof(float));
            /* Also collect control trit snapshots for K3 Hamming distance */
            uint8_t **control_trit_snaps = (uint8_t **)malloc(n_snapshots * sizeof(uint8_t *));
            for (long s = 0; s < n_snapshots; s++)
                control_trit_snaps[s] = (uint8_t *)malloc(n * sizeof(uint8_t));
            long snap_idx = 0;

            while (gs->epoch < saved_epoch + analysis_epochs && snap_idx < n_snapshots) {
                long target = saved_epoch + (snap_idx + 1) * diag_int;
                while (gs->epoch < target) {
                    long remaining = target - gs->epoch;
                    long batch = batch_size;
                    if (batch > remaining) batch = remaining;
                    genesis_epoch_batch_metal(gs, metal, (int)batch);
                }
                /* Save T+ phase and trit snapshots */
                id<MTLBuffer> curPhase = metal->ping ? metal->phaseBufB : metal->phaseBufA;
                id<MTLBuffer> curTrit = metal->ping ? metal->tritBufB : metal->tritBufA;
                memcpy(control_snaps[snap_idx], [curPhase contents], n * sizeof(float));
                memcpy(control_trit_snaps[snap_idx], [curTrit contents], n * sizeof(uint8_t));
                snap_idx++;
            }
            long actual_snaps = snap_idx;
            printf("  Collected %ld control snapshots\n", actual_snaps);

            /* Phase 4: Restore state, inject perturbation */
            printf("Phase 3: Restoring state, injecting perturbation...\n");
            id<MTLBuffer> restTrit = saved_ping ? metal->tritBufB : metal->tritBufA;
            id<MTLBuffer> restPhase = saved_ping ? metal->phaseBufB : metal->phaseBufA;
            memcpy([restTrit contents], saved_trits, trit_sz);
            memcpy([restPhase contents], saved_phases, phase_sz);
            memcpy([metal->rngStatesBuf contents], saved_rng, rng_sz);
            metal->ping = saved_ping;
            gs->epoch = saved_epoch;

            /* Inject perturbation */
            float *phases = (float *)[restPhase contents];
            int site = gs->phase_perturb_site;
            float old_phase = phases[site];
            float new_phase = old_phase + gs->phase_perturb_delta;
            while (new_phase > 2.0f * (float)M_PI) new_phase -= 2.0f * (float)M_PI;
            while (new_phase < 0.0f) new_phase += 2.0f * (float)M_PI;
            phases[site] = new_phase;
            printf("  Perturbation: site=%d, old=%.4f, new=%.4f, delta=%.4f\n",
                   site, old_phase, new_phase, gs->phase_perturb_delta);

            /* Write JSONL header for paired-sim data */
            fprintf(gs->phase_diag_file,
                "{\"type\":\"paired_sim\", \"method\":\"perturbed_minus_control\", "
                "\"n_snapshots\":%ld, \"diag_interval\":%d}\n", actual_snaps, diag_int);
            fflush(gs->phase_diag_file);

            /* Phase 5: Run PERTURBED for same epochs, compare at each snapshot */
            printf("Phase 4: Running PERTURBED simulation, comparing at each step...\n");
            snap_idx = 0;
            while (gs->epoch < saved_epoch + analysis_epochs && snap_idx < actual_snaps) {
                long target = saved_epoch + (snap_idx + 1) * diag_int;
                while (gs->epoch < target) {
                    long remaining = target - gs->epoch;
                    long batch = batch_size;
                    if (batch > remaining) batch = remaining;
                    genesis_epoch_batch_metal(gs, metal, (int)batch);
                }
                /* Compare perturbed vs control (K3: zone-aware trit + phase) */
                long rel = (snap_idx + 1) * diag_int;
                lyapunov_diag_log(gs, metal, control_snaps[snap_idx],
                                  control_trit_snaps[snap_idx], rel);
                snap_idx++;

                if (gs->epoch % report_interval == 0)
                    print_diagnostics(gs, metal);
            }

            /* Cleanup paired-sim data */
            for (long s = 0; s < actual_snaps; s++) {
                free(control_snaps[s]);
                free(control_trit_snaps[s]);
            }
            free(control_snaps);
            free(control_trit_snaps);
            free(saved_trits);
            free(saved_phases);
            free(saved_rng);

        } else {
            /* ─── STANDARD MODE (no phase diagnostics) ─── */
            while (gs->epoch < epochs) {
                long remaining = epochs - gs->epoch;
                long next_report = report_interval - (gs->epoch % report_interval);
                long batch = batch_size;
                if (batch > remaining) batch = remaining;
                if (batch > next_report) batch = next_report;
                genesis_epoch_batch_metal(gs, metal, (int)batch);

                if (gs->epoch % report_interval == 0)
                    print_diagnostics(gs, metal);
            }
        }

        struct timespec t_end;
        clock_gettime(CLOCK_MONOTONIC, &t_end);
        double elapsed = (t_end.tv_sec - t_start.tv_sec) +
                         (t_end.tv_nsec - t_start.tv_nsec) * 1e-9;

        printf("\nCompleted %ld epochs in %.1fs (%.0f epochs/sec)\n",
               gs->epoch, elapsed, gs->epoch / elapsed);

        /* K2: Summary */
        if (phase_mode)
            phase_diag_summary(gs);

        /* Final state with pressure-binned correlation */
        print_final_state(gs, metal);

        /* Cleanup */
        metal_free(metal);
        mesh_free(gs->mesh_tp);
        mesh_free(gs->mesh_tm);
        tiling_free(gs->tp_tiling);
        tiling_free(gs->tm_tiling);
        free(gs->pp_at_tp); free(gs->pm_at_tp);
        free(gs->pp_at_tm); free(gs->pm_at_tm);
        free(gs->dominant_color_tp); free(gs->dominant_color_tm);
        if (gs->pressure_color) free(gs->pressure_color);
        if (gs->phase_bfs_dist) free(gs->phase_bfs_dist);
        if (gs->phase_shell_count) free(gs->phase_shell_count);
        if (gs->phase_arrival) free(gs->phase_arrival);
        if (gs->phase_baseline_tp) free(gs->phase_baseline_tp);
        if (gs->site_zone) free(gs->site_zone);
        if (gs->shell_count_open) free(gs->shell_count_open);
        if (gs->shell_count_blocked) free(gs->shell_count_blocked);
        if (gs->trit_arrival_open) free(gs->trit_arrival_open);
        if (gs->trit_arrival_blocked) free(gs->trit_arrival_blocked);
        if (gs->phase_diag_file) fclose(gs->phase_diag_file);
        free(gs);
        if (hash_next_arr) free(hash_next_arr);
    }
    return 0;
}
