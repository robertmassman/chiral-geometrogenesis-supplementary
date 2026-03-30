/*
 * Tiling Algorithm Investigation
 * ===============================
 * Tests whether the 20% undersized tiles in the BFS Voronoi tiling are
 * a genuine geometric constraint or an algorithmic artifact.
 *
 * Strategies tested:
 *   A. Original BFS (baseline from soup_multi_stella.c)
 *   B. BFS + redistribute unowned sites to undersized neighbors
 *   C. BFS with fewer tiles (leave headroom for growth)
 *   D. BFS + merge undersized tiles into neighbors
 *   E. Greedy fill: grow tiles one-at-a-time to full size
 *   F. BFS without cap, then truncate to prog_size (cover all sites)
 *
 * Compile: cc -O2 -o tiling_improvement tiling_improvement.c -lm
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define MAX_NBR 8
#define PROG_SIZE 24
#define CORE_SIZE 19  /* minimum functional replicator size */

/* ================================================================
 * PRNG
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

/* ================================================================
 * Mesh (from soup_multi_stella.c)
 * ================================================================ */

typedef struct {
    int n_sites;
    int *n_nbr;
    int (*nbr)[MAX_NBR];
} Mesh;

static int edge_index(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    if (a == 0) return b - 1;
    if (a == 1) return b + 1;
    return 5;
}

static void mesh_add_edge(Mesh *m, int a, int b) {
    for (int i = 0; i < m->n_nbr[a]; i++)
        if (m->nbr[a][i] == b) return;
    if (m->n_nbr[a] < MAX_NBR) m->nbr[a][m->n_nbr[a]++] = b;
    if (m->n_nbr[b] < MAX_NBR) m->nbr[b][m->n_nbr[b]++] = a;
}

static const int TETRA_F[4][3] = {
    {0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}
};

static Mesh *mesh_build(int n) {
    int n_verts = 4;
    int n_edge_pts = 6 * (n - 1);
    int n_face_int = (n - 1) * (n - 2) / 2;
    int total = n_verts + n_edge_pts + 4 * n_face_int;

    Mesh *m = calloc(1, sizeof(Mesh));
    m->n_sites = total;
    m->n_nbr = calloc(total, sizeof(int));
    m->nbr = calloc(total, sizeof(int[MAX_NBR]));

    int **face_vid[4];
    int face_int_count[4] = {0};

    for (int f = 0; f < 4; f++) {
        face_vid[f] = malloc((n + 1) * sizeof(int *));
        for (int i = 0; i <= n; i++)
            face_vid[f][i] = malloc((n + 1) * sizeof(int));
    }

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
            }
        }
    }

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
    free(m->n_nbr); free(m->nbr); free(m);
}

/* ================================================================
 * Tiling result structure
 * ================================================================ */

typedef struct {
    int n_tiles;
    int *tile_size;
    int **tile_sites;   /* tile_sites[i][j] = site index */
    int max_alloc;      /* max sites allocated per tile */
} TilingResult;

static TilingResult *tr_create(int n_tiles, int max_alloc) {
    TilingResult *t = calloc(1, sizeof(TilingResult));
    t->n_tiles = n_tiles;
    t->max_alloc = max_alloc;
    t->tile_size = calloc(n_tiles, sizeof(int));
    t->tile_sites = calloc(n_tiles, sizeof(int *));
    for (int i = 0; i < n_tiles; i++)
        t->tile_sites[i] = malloc(max_alloc * sizeof(int));
    return t;
}

static void tr_free(TilingResult *t) {
    for (int i = 0; i < t->n_tiles; i++) free(t->tile_sites[i]);
    free(t->tile_sites);
    free(t->tile_size);
    free(t);
}

typedef struct {
    int n_tiles;
    int min_size, max_size;
    double mean_size;
    int under_core;    /* < CORE_SIZE */
    int under_prog;    /* < PROG_SIZE */
    int unowned;
    int total_owned;
} TilingStats;

static TilingStats compute_stats(const TilingResult *t, int n_sites) {
    TilingStats s = {0};
    s.n_tiles = t->n_tiles;
    s.min_size = t->max_alloc + 1;
    s.max_size = 0;
    long sum = 0;
    for (int i = 0; i < t->n_tiles; i++) {
        int sz = t->tile_size[i];
        if (sz < s.min_size) s.min_size = sz;
        if (sz > s.max_size) s.max_size = sz;
        sum += sz;
        if (sz < CORE_SIZE) s.under_core++;
        if (sz < PROG_SIZE) s.under_prog++;
    }
    s.total_owned = (int)sum;
    s.unowned = n_sites - (int)sum;
    s.mean_size = (double)sum / t->n_tiles;
    return s;
}

static void print_stats(const char *name, TilingStats s, int n_sites) {
    printf("  %-30s  tiles=%d  min=%d  max=%d  mean=%.1f  "
           "<%d: %d (%.1f%%)  <%d: %d (%.1f%%)  unowned=%d  "
           "max_ρ=%.1f%%\n",
           name, s.n_tiles, s.min_size, s.max_size, s.mean_size,
           CORE_SIZE, s.under_core, 100.0 * s.under_core / s.n_tiles,
           PROG_SIZE, s.under_prog, 100.0 * s.under_prog / s.n_tiles,
           s.unowned,
           100.0 * (s.n_tiles - s.under_core) / s.n_tiles);
}

static void print_histogram(const TilingResult *t) {
    int hist[200] = {0};
    int max_sz = 0;
    for (int i = 0; i < t->n_tiles; i++) {
        int sz = t->tile_size[i];
        if (sz < 200) hist[sz]++;
        if (sz > max_sz) max_sz = sz;
    }
    printf("    Size histogram: ");
    for (int sz = 0; sz <= max_sz && sz < 200; sz++) {
        if (hist[sz] > 0) printf("%d×[%d] ", hist[sz], sz);
    }
    printf("\n");
}

/* ================================================================
 * Strategy A: Original BFS (baseline)
 * ================================================================ */

static TilingResult *strategy_A(const Mesh *m, int n_tiles, uint64_t seed) {
    TilingResult *t = tr_create(n_tiles, PROG_SIZE);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    int stride = m->n_sites / n_tiles;
    for (int i = 0; i < n_tiles; i++) {
        int s = (i * stride + stride / 2) % m->n_sites;
        while (owner[s] != -1) s = (s + 1) % m->n_sites;
        owner[s] = i;
        t->tile_sites[i][0] = s;
        t->tile_size[i] = 1;
        queue[qtail] = s; qtile[qtail] = i; qtail++;
    }

    while (qhead < qtail) {
        int site = queue[qhead], tile = qtile[qhead]; qhead++;
        if (t->tile_size[tile] >= PROG_SIZE) continue;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1 && t->tile_size[tile] < PROG_SIZE) {
                owner[nb] = tile;
                t->tile_sites[tile][t->tile_size[tile]++] = nb;
                queue[qtail] = nb; qtile[qtail] = tile; qtail++;
            }
        }
    }

    free(owner); free(queue); free(qtile);
    return t;
}

/* ================================================================
 * Strategy B: BFS + redistribute unowned sites
 * After BFS, assign each unowned site to the smallest neighboring tile
 * ================================================================ */

static TilingResult *strategy_B(const Mesh *m, int n_tiles, uint64_t seed) {
    /* First do standard BFS */
    int max_alloc = PROG_SIZE + 20;  /* allow some overflow */
    TilingResult *t = tr_create(n_tiles, max_alloc);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    int stride = m->n_sites / n_tiles;
    for (int i = 0; i < n_tiles; i++) {
        int s = (i * stride + stride / 2) % m->n_sites;
        while (owner[s] != -1) s = (s + 1) % m->n_sites;
        owner[s] = i;
        t->tile_sites[i][0] = s;
        t->tile_size[i] = 1;
        queue[qtail] = s; qtile[qtail] = i; qtail++;
    }

    while (qhead < qtail) {
        int site = queue[qhead], tile = qtile[qhead]; qhead++;
        if (t->tile_size[tile] >= PROG_SIZE) continue;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1 && t->tile_size[tile] < PROG_SIZE) {
                owner[nb] = tile;
                if (t->tile_size[tile] < max_alloc)
                    t->tile_sites[tile][t->tile_size[tile]] = nb;
                t->tile_size[tile]++;
                queue[qtail] = nb; qtile[qtail] = tile; qtail++;
            }
        }
    }

    /* Redistribute: assign unowned sites to smallest neighboring tile */
    int reassigned = 0;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int site = 0; site < m->n_sites; site++) {
            if (owner[site] != -1) continue;
            /* Find smallest neighboring tile */
            int best_tile = -1, best_size = m->n_sites;
            for (int ni = 0; ni < m->n_nbr[site]; ni++) {
                int nb = m->nbr[site][ni];
                if (owner[nb] >= 0) {
                    int tile = owner[nb];
                    if (t->tile_size[tile] < best_size) {
                        best_size = t->tile_size[tile];
                        best_tile = tile;
                    }
                }
            }
            if (best_tile >= 0) {
                owner[site] = best_tile;
                if (t->tile_size[best_tile] < max_alloc)
                    t->tile_sites[best_tile][t->tile_size[best_tile]] = site;
                t->tile_size[best_tile]++;
                reassigned++;
                changed = 1;
            }
        }
    }

    /* Cap tile_size at PROG_SIZE for functional purposes */
    /* (but report actual size for statistics) */

    free(owner); free(queue); free(qtile);
    return t;
}

/* ================================================================
 * Strategy C: BFS with fewer tiles (leave headroom)
 * Use n_tiles such that avg sites/tile > PROG_SIZE
 * ================================================================ */

static TilingResult *strategy_C(const Mesh *m, int n_tiles, uint64_t seed) {
    /* Same as A but with fewer tiles */
    int max_alloc = (m->n_sites / n_tiles) + 10;
    if (max_alloc < PROG_SIZE) max_alloc = PROG_SIZE;
    TilingResult *t = tr_create(n_tiles, max_alloc);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    int stride = m->n_sites / n_tiles;
    for (int i = 0; i < n_tiles; i++) {
        int s = (i * stride + stride / 2) % m->n_sites;
        while (owner[s] != -1) s = (s + 1) % m->n_sites;
        owner[s] = i;
        t->tile_sites[i][0] = s;
        t->tile_size[i] = 1;
        queue[qtail] = s; qtile[qtail] = i; qtail++;
    }

    /* BFS with cap at PROG_SIZE still */
    while (qhead < qtail) {
        int site = queue[qhead], tile = qtile[qhead]; qhead++;
        if (t->tile_size[tile] >= PROG_SIZE) continue;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1 && t->tile_size[tile] < PROG_SIZE) {
                owner[nb] = tile;
                if (t->tile_size[tile] < max_alloc)
                    t->tile_sites[tile][t->tile_size[tile]] = nb;
                t->tile_size[tile]++;
                queue[qtail] = nb; qtile[qtail] = tile; qtail++;
            }
        }
    }

    free(owner); free(queue); free(qtile);
    return t;
}

/* ================================================================
 * Strategy D: BFS + merge undersized into neighbors
 * After BFS, dissolve tiles with size < CORE_SIZE and let their
 * sites be absorbed by neighboring tiles (up to PROG_SIZE).
 * ================================================================ */

static TilingResult *strategy_D(const Mesh *m, int n_tiles_init, uint64_t seed) {
    int max_alloc = PROG_SIZE + 5;
    TilingResult *t = tr_create(n_tiles_init, max_alloc);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    int stride = m->n_sites / n_tiles_init;
    for (int i = 0; i < n_tiles_init; i++) {
        int s = (i * stride + stride / 2) % m->n_sites;
        while (owner[s] != -1) s = (s + 1) % m->n_sites;
        owner[s] = i;
        t->tile_sites[i][0] = s;
        t->tile_size[i] = 1;
        queue[qtail] = s; qtile[qtail] = i; qtail++;
    }

    while (qhead < qtail) {
        int site = queue[qhead], tile = qtile[qhead]; qhead++;
        if (t->tile_size[tile] >= PROG_SIZE) continue;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1 && t->tile_size[tile] < PROG_SIZE) {
                owner[nb] = tile;
                if (t->tile_size[tile] < max_alloc)
                    t->tile_sites[tile][t->tile_size[tile]] = nb;
                t->tile_size[tile]++;
                queue[qtail] = nb; qtile[qtail] = tile; qtail++;
            }
        }
    }

    /* Merge: dissolve undersized tiles, re-BFS their sites into neighbors */
    int dissolved = 0;
    for (int i = 0; i < n_tiles_init; i++) {
        if (t->tile_size[i] >= CORE_SIZE) continue;
        /* Mark all sites of this tile as unowned */
        for (int j = 0; j < t->tile_size[i] && j < max_alloc; j++) {
            owner[t->tile_sites[i][j]] = -1;
        }
        t->tile_size[i] = 0;
        dissolved++;
    }

    /* Re-BFS: unowned sites get absorbed by neighboring tiles */
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int site = 0; site < m->n_sites; site++) {
            if (owner[site] != -1) continue;
            int best_tile = -1, best_size = 0;
            for (int ni = 0; ni < m->n_nbr[site]; ni++) {
                int nb = m->nbr[site][ni];
                if (owner[nb] >= 0) {
                    int tile = owner[nb];
                    /* Prefer tiles that still have room and are smallest */
                    if (t->tile_size[tile] < PROG_SIZE &&
                        (best_tile < 0 || t->tile_size[tile] < best_size)) {
                        best_tile = tile;
                        best_size = t->tile_size[tile];
                    }
                }
            }
            if (best_tile >= 0 && t->tile_size[best_tile] < max_alloc) {
                owner[site] = best_tile;
                t->tile_sites[best_tile][t->tile_size[best_tile]] = site;
                t->tile_size[best_tile]++;
                changed = 1;
            }
        }
    }

    /* Count surviving tiles */
    int surviving = 0;
    for (int i = 0; i < n_tiles_init; i++)
        if (t->tile_size[i] > 0) surviving++;

    free(owner); free(queue); free(qtile);
    return t;
}

/* ================================================================
 * Strategy E: Greedy sequential fill
 * Grow one tile at a time to full size before starting next.
 * This guarantees each tile reaches PROG_SIZE if possible.
 * ================================================================ */

static TilingResult *strategy_E(const Mesh *m, uint64_t seed) {
    int max_tiles = m->n_sites / PROG_SIZE + 100;
    TilingResult *t = tr_create(max_tiles, PROG_SIZE);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int n_tiles = 0;
    int start = 0;

    /* Pre-allocate a shared BFS queue */
    int *q = malloc(m->n_sites * sizeof(int));

    while (start < m->n_sites) {
        /* Find next unowned site */
        while (start < m->n_sites && owner[start] != -1) start++;
        if (start >= m->n_sites) break;
        if (n_tiles >= max_tiles) break;

        int tile = n_tiles++;
        owner[start] = tile;
        t->tile_sites[tile][0] = start;
        t->tile_size[tile] = 1;

        /* BFS grow this single tile to PROG_SIZE */
        int qh = 0, qt = 0;
        q[qt++] = start;

        while (qh < qt && t->tile_size[tile] < PROG_SIZE) {
            int site = q[qh++];
            for (int ni = 0; ni < m->n_nbr[site]; ni++) {
                int nb = m->nbr[site][ni];
                if (owner[nb] == -1 && t->tile_size[tile] < PROG_SIZE) {
                    owner[nb] = tile;
                    t->tile_sites[tile][t->tile_size[tile]++] = nb;
                    q[qt++] = nb;
                }
            }
        }
        start++;
    }

    free(q);
    t->n_tiles = n_tiles;
    free(owner);
    return t;
}

/* ================================================================
 * Strategy F: Uncapped BFS, then truncate
 * Let BFS fill ALL sites (no cap), then truncate read to PROG_SIZE.
 * Every tile gets at least n_sites/n_tiles sites on average.
 * ================================================================ */

static TilingResult *strategy_F(const Mesh *m, int n_tiles, uint64_t seed) {
    int max_alloc = (m->n_sites / n_tiles) + 20;
    TilingResult *t = tr_create(n_tiles, max_alloc);
    int *owner = malloc(m->n_sites * sizeof(int));
    for (int i = 0; i < m->n_sites; i++) owner[i] = -1;

    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    int stride = m->n_sites / n_tiles;
    for (int i = 0; i < n_tiles; i++) {
        int s = (i * stride + stride / 2) % m->n_sites;
        while (owner[s] != -1) s = (s + 1) % m->n_sites;
        owner[s] = i;
        t->tile_sites[i][0] = s;
        t->tile_size[i] = 1;
        queue[qtail] = s; qtile[qtail] = i; qtail++;
    }

    /* BFS with NO cap — grow until all sites owned */
    while (qhead < qtail) {
        int site = queue[qhead], tile = qtile[qhead]; qhead++;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1) {
                owner[nb] = tile;
                if (t->tile_size[tile] < max_alloc)
                    t->tile_sites[tile][t->tile_size[tile]] = nb;
                t->tile_size[tile]++;
                queue[qtail] = nb; qtile[qtail] = tile; qtail++;
            }
        }
    }

    free(owner); free(queue); free(qtile);
    return t;
}

/* ================================================================
 * Strategy G: Reduced tiles + uncapped BFS
 * Fewer tiles so each gets more room, uncapped growth
 * ================================================================ */

/* ================================================================
 * MAIN
 * ================================================================ */

int main(void) {
    printf("=== Tiling Algorithm Investigation ===\n\n");

    int n_sub = 100;
    Mesh *m = mesh_build(n_sub);
    int ns = m->n_sites;
    int n_tiles_orig = ns / PROG_SIZE;

    printf("Mesh: %d sites, original n_tiles = %d (= %d / %d)\n\n", ns, n_tiles_orig, ns, PROG_SIZE);

    /* ---- Strategy A: Original BFS ---- */
    printf("--- Strategy A: Original BFS (baseline) ---\n");
    {
        TilingResult *t = strategy_A(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        print_stats("A: Original BFS", s, ns);
        print_histogram(t);
        tr_free(t);
    }

    /* ---- Strategy B: BFS + redistribute ---- */
    printf("\n--- Strategy B: BFS + redistribute unowned sites ---\n");
    {
        TilingResult *t = strategy_B(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        print_stats("B: BFS + redistribute", s, ns);
        print_histogram(t);
        tr_free(t);
    }

    /* ---- Strategy C: Fewer tiles ---- */
    printf("\n--- Strategy C: BFS with fewer tiles ---\n");
    int fewer_counts[] = {750, 700, 650, 600, 500};
    for (int ci = 0; ci < 5; ci++) {
        int nt = fewer_counts[ci];
        TilingResult *t = strategy_C(m, nt, 42);
        TilingStats s = compute_stats(t, ns);
        char name[64];
        snprintf(name, sizeof(name), "C: BFS n_tiles=%d", nt);
        print_stats(name, s, ns);
        tr_free(t);
    }

    /* ---- Strategy D: BFS + merge undersized ---- */
    printf("\n--- Strategy D: BFS + dissolve undersized + re-absorb ---\n");
    {
        TilingResult *t = strategy_D(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        print_stats("D: BFS + merge", s, ns);

        /* Count dissolved tiles */
        int dissolved = 0, surviving = 0;
        for (int i = 0; i < t->n_tiles; i++) {
            if (t->tile_size[i] == 0) dissolved++;
            else surviving++;
        }
        printf("    Dissolved: %d tiles, surviving: %d tiles\n", dissolved, surviving);
        print_histogram(t);
        tr_free(t);
    }

    /* ---- Strategy E: Greedy sequential fill ---- */
    printf("\n--- Strategy E: Greedy sequential fill ---\n");
    {
        TilingResult *t = strategy_E(m, 42);
        TilingStats s = compute_stats(t, ns);
        print_stats("E: Greedy fill", s, ns);
        print_histogram(t);
        tr_free(t);
    }

    /* ---- Strategy F: Uncapped BFS ---- */
    printf("\n--- Strategy F: Uncapped BFS (all sites owned) ---\n");
    {
        TilingResult *t = strategy_F(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        print_stats("F: Uncapped BFS", s, ns);

        /* Show how many tiles have >= PROG_SIZE (functional) */
        int functional = 0;
        for (int i = 0; i < t->n_tiles; i++)
            if (t->tile_size[i] >= PROG_SIZE) functional++;
        printf("    Tiles with size >= %d (functional): %d (%.1f%%)\n",
               PROG_SIZE, functional, 100.0 * functional / t->n_tiles);
        int core_ok = 0;
        for (int i = 0; i < t->n_tiles; i++)
            if (t->tile_size[i] >= CORE_SIZE) core_ok++;
        printf("    Tiles with size >= %d (core OK): %d (%.1f%%)\n",
               CORE_SIZE, core_ok, 100.0 * core_ok / t->n_tiles);
        print_histogram(t);
        tr_free(t);
    }

    /* ---- Strategy F with fewer tiles ---- */
    printf("\n--- Strategy F variants: Uncapped BFS with fewer tiles ---\n");
    for (int ci = 0; ci < 5; ci++) {
        int nt = fewer_counts[ci];
        TilingResult *t = strategy_F(m, nt, 42);
        TilingStats s = compute_stats(t, ns);
        char name[64];
        snprintf(name, sizeof(name), "F: Uncapped n_tiles=%d", nt);
        print_stats(name, s, ns);

        int functional = 0;
        for (int i = 0; i < t->n_tiles; i++)
            if (t->tile_size[i] >= PROG_SIZE) functional++;
        printf("    Functional (>=%d): %d (%.1f%%)\n",
               PROG_SIZE, functional, 100.0 * functional / t->n_tiles);
        tr_free(t);
    }

    /* ---- Analysis: Where are the undersized tiles on the tetrahedron? ---- */
    printf("\n--- Analysis: Mesh topology at vertices/edges ---\n");
    {
        /* Check connectivity at tetrahedron vertices (sites 0-3) */
        printf("  Vertex connectivity (sites 0-3):\n");
        for (int v = 0; v < 4; v++) {
            printf("    Site %d: %d neighbors\n", v, m->n_nbr[v]);
        }

        /* Check connectivity distribution */
        int nbr_hist[MAX_NBR + 1] = {0};
        for (int i = 0; i < ns; i++) {
            if (m->n_nbr[i] <= MAX_NBR) nbr_hist[m->n_nbr[i]]++;
        }
        printf("  Site connectivity distribution:\n");
        for (int k = 0; k <= MAX_NBR; k++) {
            if (nbr_hist[k] > 0)
                printf("    %d neighbors: %d sites (%.1f%%)\n",
                       k, nbr_hist[k], 100.0 * nbr_hist[k] / ns);
        }

        /* Sites with exactly 3 neighbors = tetrahedron vertices */
        /* Sites with 4 neighbors = edge sites (shared between 2 faces) */
        /* Sites with 6 neighbors = face interior */
        printf("\n  Interpretation:\n");
        printf("    3 neighbors = tetrahedron vertices (4 expected)\n");
        printf("    4 neighbors = edge sites (shared between 2 faces)\n");
        printf("    6 neighbors = face-interior sites\n");
        printf("    Sites on edges/vertices have lower connectivity,\n");
        printf("    causing BFS tiles seeded there to grow slowly.\n");
    }

    /* ---- Which strategy is best for soup_multi_stella? ---- */
    printf("\n=== RECOMMENDATION ===\n\n");
    printf("Comparing max replicator density (%%tiles >= %d) across strategies:\n\n", CORE_SIZE);

    struct { const char *name; int under_core; int n_tiles; } results[10];
    int nr = 0;

    /* Re-run key strategies and collect */
    {
        TilingResult *t = strategy_A(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        results[nr].name = "A: Original BFS (833 tiles)";
        results[nr].under_core = s.under_core;
        results[nr].n_tiles = s.n_tiles;
        nr++;
        tr_free(t);
    }
    {
        TilingResult *t = strategy_E(m, 42);
        TilingStats s = compute_stats(t, ns);
        results[nr].name = "E: Greedy fill";
        results[nr].under_core = s.under_core;
        results[nr].n_tiles = s.n_tiles;
        nr++;
        tr_free(t);
    }
    {
        TilingResult *t = strategy_F(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        results[nr].name = "F: Uncapped BFS (833 tiles)";
        results[nr].under_core = s.under_core;
        results[nr].n_tiles = s.n_tiles;
        nr++;
        tr_free(t);
    }
    {
        TilingResult *t = strategy_F(m, 750, 42);
        TilingStats s = compute_stats(t, ns);
        results[nr].name = "F: Uncapped BFS (750 tiles)";
        results[nr].under_core = s.under_core;
        results[nr].n_tiles = s.n_tiles;
        nr++;
        tr_free(t);
    }
    {
        TilingResult *t = strategy_D(m, n_tiles_orig, 42);
        TilingStats s = compute_stats(t, ns);
        int surviving = 0;
        for (int i = 0; i < t->n_tiles; i++)
            if (t->tile_size[i] > 0) surviving++;
        results[nr].name = "D: BFS + merge undersized";
        results[nr].under_core = s.under_core;
        results[nr].n_tiles = surviving;
        nr++;
        tr_free(t);
    }

    printf("  %-35s  tiles  <19  max_ρ\n", "Strategy");
    printf("  %s\n", "-----------------------------------------------------------");
    for (int i = 0; i < nr; i++) {
        double max_rho = 100.0 * (results[i].n_tiles - results[i].under_core) / results[i].n_tiles;
        printf("  %-35s  %5d  %3d  %5.1f%%\n",
               results[i].name, results[i].n_tiles, results[i].under_core, max_rho);
    }

    mesh_free(m);
    printf("\n=== Investigation complete ===\n");
    return 0;
}
