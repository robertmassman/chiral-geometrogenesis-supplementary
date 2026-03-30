/*
 * Tile Size Diagnostic for Multi-Stella Geometry
 * ================================================
 * Extracts mesh_build + tiling_build from soup_multi_stella.c to analyze
 * the Voronoi tile size distribution on triangulated tetrahedra.
 *
 * Q13 hypothesis: if a significant fraction of tiles have < 20 sites
 * (the functional replicator core), those tiles can NEVER hold replicators,
 * permanently capping ρ below 100%.
 *
 * Also tests: what replication success rate does the multi-stella replicator
 * achieve on tiles of each size?
 *
 * Compile: cc -O2 -o tile_size_diagnostic tile_size_diagnostic.c -lm
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define Z3 3
#define MAX_NBR 8
#define PROG_SIZE 24
#define MAX_VM_STEPS 729

/* ================================================================
 * PRNG (from soup_multi_stella.c)
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
    /* Canonical edge index for tetrahedron: edges (0,1),(0,2),(0,3),(1,2),(1,3),(2,3) */
    if (a > b) { int t = a; a = b; b = t; }
    if (a == 0) return b - 1;          /* 0-1=0, 0-2=1, 0-3=2 */
    if (a == 1) return b + 1;          /* 1-2=3, 1-3=4 */
    return 5;                            /* 2-3=5 */
}

static void mesh_add_edge(Mesh *m, int a, int b) {
    for (int i = 0; i < m->n_nbr[a]; i++)
        if (m->nbr[a][i] == b) return;
    if (m->n_nbr[a] < MAX_NBR) m->nbr[a][m->n_nbr[a]++] = b;
    if (m->n_nbr[b] < MAX_NBR) m->nbr[b][m->n_nbr[b]++] = a;
}

static const double TETRA_V[4][3] = {
    {+1, +1, +1}, {+1, -1, -1}, {-1, +1, -1}, {-1, -1, +1}
};
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
 * Tiling (from soup_multi_stella.c)
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

    int stride = m->n_sites / n_tiles;
    int *queue = malloc(m->n_sites * sizeof(int));
    int *qtile = malloc(m->n_sites * sizeof(int));
    int qhead = 0, qtail = 0;

    for (int i = 0; i < n_tiles; i++) {
        int seed = (i * stride + stride / 2) % m->n_sites;
        while (owner[seed] != -1)
            seed = (seed + 1) % m->n_sites;
        owner[seed] = i;
        t->tile_sites[i][0] = seed;
        t->tile_size[i] = 1;
        queue[qtail] = seed;
        qtile[qtail] = i;
        qtail++;
    }

    while (qhead < qtail) {
        int site = queue[qhead];
        int tile = qtile[qhead];
        qhead++;
        if (t->tile_size[tile] >= prog_size) continue;
        for (int ni = 0; ni < m->n_nbr[site]; ni++) {
            int nb = m->nbr[site][ni];
            if (owner[nb] == -1 && t->tile_size[tile] < prog_size) {
                owner[nb] = tile;
                int idx = t->tile_size[tile]++;
                if (idx < prog_size) t->tile_sites[tile][idx] = nb;
                queue[qtail] = nb;
                qtile[qtail] = tile;
                qtail++;
            }
        }
    }

    /* Count unowned sites */
    int unowned = 0;
    for (int i = 0; i < m->n_sites; i++)
        if (owner[i] == -1) unowned++;

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
                if (t->tile_neighbors[ti][k] == tj) { found = 1; break; }
            if (!found && t->n_tile_nbr[ti] < 8)
                t->tile_neighbors[ti][t->n_tile_nbr[ti]++] = tj;
        }
    }

    printf("  Tiling: %d tiles, %d unowned sites\n", n_tiles, unowned);
    free(owner); free(queue); free(qtile);
    return t;
}

static void tiling_free(Tiling *t) {
    for (int i = 0; i < t->n_tiles; i++) free(t->tile_sites[i]);
    free(t->tile_sites); free(t->tile_size);
    free(t->tile_neighbors); free(t->n_tile_nbr);
    free(t);
}

/* ================================================================
 * VM (from soup_multi_stella.c)
 * ================================================================ */

static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;
    while (steps < max_steps && ip + 1 < tape_len) {
        int op = tape[ip] * 3 + tape[ip + 1];
        switch (op) {
        case 0: break;
        case 1: tape[h0] = tape[h0] < 2 ? tape[h0] + 1 : 0; break;
        case 2: if (++h0 >= tape_len) h0 = 0; break;
        case 3: if (--h0 < 0) h0 = tape_len - 1; break;
        case 4: if (++h1 >= tape_len) h1 = 0; break;
        case 5:
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
        case 6:
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
        case 7: tape[h1] = tape[h0]; break;
        case 8: tape[h0] = tape[h1]; break;
        }
        ip += 2;
        steps++;
    }
}

/* ================================================================
 * Replication test on a tile of given size
 * ================================================================ */

/* Multi-stella replicator (the one actually used in soup_multi_stella.c) */
static const uint8_t MULTI_STELLA_REP[24] = {
    1,2, 1,2, 2,1, 1,1, 0,2, 2,0,
    2,1, 1,1, 0,2, 2,0, 2,0, 1,1
};

/* 30M-run replicator (used in flat-tile experiments) */
static const uint8_t REP_A[24] = {
    1,2, 1,2, 2,1, 0,2, 1,1, 2,0,
    2,1, 1,1, 0,2, 2,0, 2,0, 2,0
};

/* Test replication with a tile of size `sz` (zero-padded to PROG_SIZE).
 * Returns: 0=fail, 1=partial (first sz trits match), 2=full (all 24 match) */
static int test_replication(const uint8_t *rep, int sz, const uint8_t *food,
                             int food_sz) {
    uint8_t tape[2 * PROG_SIZE];

    /* Build A-half: rep truncated to sz, zero-padded */
    memcpy(tape, rep, sz < PROG_SIZE ? sz : PROG_SIZE);
    if (sz < PROG_SIZE) memset(tape + sz, 0, PROG_SIZE - sz);

    /* Build B-half: food truncated to food_sz, zero-padded */
    memcpy(tape + PROG_SIZE, food, food_sz < PROG_SIZE ? food_sz : PROG_SIZE);
    if (food_sz < PROG_SIZE) memset(tape + PROG_SIZE + food_sz, 0, PROG_SIZE - food_sz);

    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

    /* Check if first sz trits of both halves match rep */
    int partial_ok = (memcmp(tape, rep, sz) == 0 &&
                      memcmp(tape + PROG_SIZE, rep, sz) == 0);
    if (!partial_ok) return 0;

    int full_ok = (memcmp(tape, rep, PROG_SIZE) == 0 &&
                   memcmp(tape + PROG_SIZE, rep, PROG_SIZE) == 0);
    return full_ok ? 2 : 1;
}

/* ================================================================
 * MAIN: Diagnostic experiments
 * ================================================================ */

int main(void) {
    uint64_t rng[4];
    rng_seed(rng, 42);

    printf("=== Tile Size Diagnostic for Multi-Stella Geometry ===\n\n");

    /* ---- Experiment 1: Tile size distribution for n_sub=100 ---- */
    printf("--- Exp 1: Tile size distribution (n_sub=100, prog_size=24) ---\n\n");

    int n_sub = 100;
    Mesh *m = mesh_build(n_sub);
    int n_sites = m->n_sites;
    int n_tiles = n_sites / PROG_SIZE;
    printf("Mesh: %d sites (expected %d)\n", n_sites, 2*n_sub*n_sub + 2);
    printf("Tiles: %d (n_sites/prog_size = %d/%d)\n", n_tiles, n_sites, PROG_SIZE);
    printf("Leftover sites: %d\n\n", n_sites - n_tiles * PROG_SIZE);

    uint64_t til_rng[4];
    rng_seed(til_rng, 1042);
    Tiling *tp = tiling_build(m, n_tiles, PROG_SIZE, til_rng);
    Tiling *tm = tiling_build(m, n_tiles, PROG_SIZE, til_rng);

    /* Size histogram */
    int hist[PROG_SIZE + 2];
    memset(hist, 0, sizeof(hist));
    int undersized_20 = 0, undersized_24 = 0;

    printf("T+ tiling:\n");
    for (int i = 0; i < n_tiles; i++) {
        int sz = tp->tile_size[i];
        if (sz <= PROG_SIZE) hist[sz]++;
        else hist[PROG_SIZE + 1]++;
        if (sz < 20) undersized_20++;
        if (sz < PROG_SIZE) undersized_24++;
    }

    printf("  Size distribution (T+):\n");
    for (int sz = 0; sz <= PROG_SIZE + 1; sz++) {
        if (hist[sz] > 0) {
            printf("    size=%2d: %d tiles (%.1f%%)\n",
                   sz, hist[sz], 100.0 * hist[sz] / n_tiles);
        }
    }
    printf("  Tiles with size < 20: %d (%.1f%%)\n", undersized_20, 100.0 * undersized_20 / n_tiles);
    printf("  Tiles with size < 24: %d (%.1f%%)\n\n", undersized_24, 100.0 * undersized_24 / n_tiles);

    /* Same for T- */
    memset(hist, 0, sizeof(hist));
    int tm_under20 = 0, tm_under24 = 0;
    for (int i = 0; i < n_tiles; i++) {
        int sz = tm->tile_size[i];
        if (sz <= PROG_SIZE) hist[sz]++;
        else hist[PROG_SIZE + 1]++;
        if (sz < 20) tm_under20++;
        if (sz < PROG_SIZE) tm_under24++;
    }
    printf("  Size distribution (T-):\n");
    for (int sz = 0; sz <= PROG_SIZE + 1; sz++) {
        if (hist[sz] > 0) {
            printf("    size=%2d: %d tiles (%.1f%%)\n",
                   sz, hist[sz], 100.0 * hist[sz] / n_tiles);
        }
    }
    printf("  Tiles with size < 20: %d (%.1f%%)\n", tm_under20, 100.0 * tm_under20 / n_tiles);
    printf("  Tiles with size < 24: %d (%.1f%%)\n\n", tm_under24, 100.0 * tm_under24 / n_tiles);

    /* Combined stats */
    int total_tiles = 2 * n_tiles;
    int total_under20 = undersized_20 + tm_under20;
    int total_under24 = undersized_24 + tm_under24;
    printf("Combined (T+ + T- = %d tiles per stella):\n", total_tiles);
    printf("  Tiles with size < 20: %d (%.1f%%)\n", total_under20, 100.0 * total_under20 / total_tiles);
    printf("  Tiles with size < 24: %d (%.1f%%)\n", total_under24, 100.0 * total_under24 / total_tiles);
    printf("  → Max possible replicator density (if all size>=20 tiles replicate): %.1f%%\n",
           100.0 * (total_tiles - total_under20) / total_tiles);
    printf("  → Max possible density (only full-size tiles): %.1f%%\n\n",
           100.0 * (total_tiles - total_under24) / total_tiles);

    /* Tile neighbor count distribution */
    printf("  Tile neighbor count distribution (T+):\n");
    int nbr_hist[9] = {0};
    for (int i = 0; i < n_tiles; i++) {
        int nn = tp->n_tile_nbr[i];
        if (nn <= 8) nbr_hist[nn]++;
    }
    for (int nn = 0; nn <= 8; nn++) {
        if (nbr_hist[nn] > 0)
            printf("    %d neighbors: %d tiles\n", nn, nbr_hist[nn]);
    }
    printf("\n");

    /* ---- Experiment 2: Replication success vs tile size ---- */
    printf("--- Exp 2: Replication success vs tile size ---\n\n");
    printf("Testing both replicators with zero food and random food (1000 trials each):\n\n");

    printf("  %4s  %12s  %12s  %12s  %12s\n",
           "size", "MS_zero", "MS_rand", "A_zero", "A_rand");
    printf("  %s\n", "------------------------------------------------------------");

    for (int sz = 1; sz <= 24; sz++) {
        /* Zero food test */
        uint8_t zero_food[PROG_SIZE];
        memset(zero_food, 0, PROG_SIZE);

        int ms_zero = test_replication(MULTI_STELLA_REP, sz, zero_food, sz);
        int a_zero = test_replication(REP_A, sz, zero_food, sz);

        /* Random food test (1000 trials) */
        int ms_pass = 0, a_pass = 0;
        for (int t = 0; t < 1000; t++) {
            uint8_t food[PROG_SIZE];
            for (int j = 0; j < PROG_SIZE; j++)
                food[j] = rng_int(rng, Z3);
            if (test_replication(MULTI_STELLA_REP, sz, food, sz) > 0) ms_pass++;
            if (test_replication(REP_A, sz, food, sz) > 0) a_pass++;
        }

        const char *labels[] = {"FAIL", "PARTIAL", "FULL"};
        printf("  %4d  %12s  %8d/1000  %12s  %8d/1000\n",
               sz, labels[ms_zero], ms_pass, labels[a_zero], a_pass);
    }

    printf("\n");

    /* ---- Experiment 3: How stella_tile_read handles undersized tiles ---- */
    printf("--- Exp 3: Effective replication on actual Voronoi tiles ---\n\n");
    printf("Simulating tile_read/write with actual tile sizes from Exp 1.\n");
    printf("For each tile size bucket, test replication with zero-padding as in soup_multi_stella.c:\n\n");

    /* Group tiles by size and test */
    int size_counts[PROG_SIZE + 1];
    int size_pass_zero[PROG_SIZE + 1];
    int size_pass_rand[PROG_SIZE + 1];
    memset(size_counts, 0, sizeof(size_counts));
    memset(size_pass_zero, 0, sizeof(size_pass_zero));
    memset(size_pass_rand, 0, sizeof(size_pass_rand));

    /* For each unique tile size in T+, test 100 random food trials */
    for (int i = 0; i < n_tiles; i++) {
        int sz = tp->tile_size[i];
        if (sz > PROG_SIZE) sz = PROG_SIZE;
        size_counts[sz]++;

        /* Zero food */
        uint8_t zero_food[PROG_SIZE];
        memset(zero_food, 0, PROG_SIZE);
        if (test_replication(MULTI_STELLA_REP, sz, zero_food, sz) > 0)
            size_pass_zero[sz]++;

        /* Random food (100 trials per tile) */
        int pass = 0;
        for (int t = 0; t < 100; t++) {
            uint8_t food[PROG_SIZE];
            for (int j = 0; j < PROG_SIZE; j++)
                food[j] = rng_int(rng, Z3);
            if (test_replication(MULTI_STELLA_REP, sz, food, sz) > 0)
                pass++;
        }
        size_pass_rand[sz] += pass;
    }

    printf("  %4s  %6s  %12s  %12s\n", "size", "count", "zero_food", "rand_food");
    printf("  %s\n", "----------------------------------------------");
    for (int sz = 0; sz <= PROG_SIZE; sz++) {
        if (size_counts[sz] > 0) {
            printf("  %4d  %6d  %6d/%6d  %6d/%6d\n",
                   sz, size_counts[sz],
                   size_pass_zero[sz], size_counts[sz],
                   size_pass_rand[sz], size_counts[sz] * 100);
        }
    }

    /* ---- Experiment 4: Multiple RNG seeds for tiling ---- */
    printf("\n--- Exp 4: Tiling variability across 10 RNG seeds ---\n\n");

    printf("  %6s  %6s  %6s  %6s  %6s  %8s\n",
           "seed", "tiles", "min_sz", "max_sz", "<20", "max_ρ(%)");
    printf("  %s\n", "----------------------------------------------------");

    for (int s = 0; s < 10; s++) {
        uint64_t seed_rng[4];
        rng_seed(seed_rng, 1000 + s * 137);
        Tiling *test_t = tiling_build(m, n_tiles, PROG_SIZE, seed_rng);

        int min_sz = PROG_SIZE, max_sz = 0, under20 = 0;
        for (int i = 0; i < n_tiles; i++) {
            int sz = test_t->tile_size[i];
            if (sz < min_sz) min_sz = sz;
            if (sz > max_sz) max_sz = sz;
            if (sz < 20) under20++;
        }
        double max_rho = 100.0 * (n_tiles - under20) / n_tiles;
        printf("  %6d  %6d  %6d  %6d  %6d  %8.1f\n",
               1000 + s * 137, n_tiles, min_sz, max_sz, under20, max_rho);

        tiling_free(test_t);
    }

    /* ---- Experiment 5: Interaction asymmetry with tile-size effects ---- */
    printf("\n--- Exp 5: Combined effect — tile size + interaction asymmetry ---\n\n");

    /* Simulate a mini-soup on one stella with actual tile sizes.
     * Each tile: replicator or food. Track density over 10000 epochs.
     * Use multi-stella replicator and local pairing from tile neighbor lists. */

    int n_total = 2 * n_tiles;  /* T+ and T- combined */
    uint8_t *is_rep = calloc(n_total, sizeof(uint8_t));

    /* Seed all tiles as replicators initially */
    for (int i = 0; i < n_total; i++) is_rep[i] = 1;

    /* Mark undersized tiles as permanently food */
    int perm_food = 0;
    for (int i = 0; i < n_tiles; i++) {
        if (tp->tile_size[i] < 20) { is_rep[i] = 0; perm_food++; }
        if (tm->tile_size[i] < 20) { is_rep[n_tiles + i] = 0; perm_food++; }
    }
    printf("Permanently food tiles (size < 20): %d / %d (%.1f%%)\n",
           perm_food, n_total, 100.0 * perm_food / n_total);

    /* Interaction asymmetry rates (from Q13 Exp 2 measurements):
     * Rep(A)||Food(B): both become rep with p=1.0
     * Food(A)||Rep(B): rep destroyed with p_kill=0.6935
     * Rep(A)||Rep(B): both survive with p=1.0 */
    double p_kill = 0.6935;
    double mu_rate = 0.001;  /* mutation rate */

    /* Run simulation with local pairing */
    printf("Running 50000-epoch single-stella simulation with local pairing...\n");
    printf("(Using interaction asymmetry: p_kill=0.6935, mu=0.001)\n\n");

    printf("  %8s  %8s  %8s\n", "epoch", "n_rep", "density");
    printf("  %s\n", "------------------------------");

    for (int epoch = 0; epoch < 50000; epoch++) {
        /* Pick a random tile */
        int a = rng_int(rng, n_total);

        /* Pick a local neighbor */
        int is_tp_a = a < n_tiles;
        int local_a = is_tp_a ? a : a - n_tiles;
        const Tiling *t_a = is_tp_a ? tp : tm;
        int nn = t_a->n_tile_nbr[local_a];
        if (nn == 0) continue;

        int local_b = t_a->tile_neighbors[local_a][rng_int(rng, nn)];
        /* 50% chance to cross T+/T- (as in soup_multi_stella.c) */
        int b_is_tp = is_tp_a;
        if ((rng_next(rng) & 1)) b_is_tp = !b_is_tp;
        int b = b_is_tp ? local_b : local_b + n_tiles;

        /* Get tile sizes */
        int sz_a = is_tp_a ? tp->tile_size[local_a] : tm->tile_size[local_a];
        int sz_b = b_is_tp ? tp->tile_size[local_b] : tm->tile_size[local_b];

        /* Interaction */
        if (is_rep[a] && !is_rep[b]) {
            /* Rep(A) || Food(B): B becomes rep if sz_b >= 20 */
            if (sz_b >= 20) is_rep[b] = 1;
        } else if (!is_rep[a] && is_rep[b]) {
            /* Food(A) || Rep(B): rep destroyed with p_kill */
            if ((rng_next(rng) >> 33) < (uint64_t)(p_kill * (1ULL << 31)))
                is_rep[b] = 0;
        }
        /* Rep || Rep: both survive */
        /* Food || Food: nothing happens */

        /* Mutation: random tile loses replicator status */
        if ((rng_next(rng) >> 33) < (uint64_t)(mu_rate * n_total * (1ULL << 31) / n_total)) {
            int victim = rng_int(rng, n_total);
            int v_local = victim < n_tiles ? victim : victim - n_tiles;
            int v_sz = victim < n_tiles ? tp->tile_size[v_local] : tm->tile_size[v_local];
            if (v_sz >= 20) is_rep[victim] = 0;
        }

        if (epoch % 5000 == 0 || epoch == 49999) {
            int n_rep = 0;
            for (int i = 0; i < n_total; i++) n_rep += is_rep[i];
            printf("  %8d  %8d  %7.1f%%\n", epoch, n_rep,
                   100.0 * n_rep / n_total);
        }
    }

    /* ---- Experiment 6: Start from low density (seeded) ---- */
    printf("\n--- Exp 6: Growth from 10%% seed with local pairing + tile sizes ---\n\n");

    /* Reset: only seed 10% of viable tiles */
    for (int i = 0; i < n_total; i++) is_rep[i] = 0;
    int viable = n_total - perm_food;
    int n_seed = viable / 10;
    int seeded = 0;
    for (int i = 0; i < n_total && seeded < n_seed; i++) {
        int local = i < n_tiles ? i : i - n_tiles;
        int sz = i < n_tiles ? tp->tile_size[local] : tm->tile_size[local];
        if (sz >= 20 && rng_int(rng, 10) == 0) {
            is_rep[i] = 1;
            seeded++;
        }
    }

    printf("Seeded %d / %d viable tiles (%.1f%%)\n", seeded, viable,
           100.0 * seeded / viable);
    printf("Running 200000 epochs...\n\n");
    printf("  %8s  %8s  %8s  %10s\n", "epoch", "n_rep", "density", "viable_ρ");
    printf("  %s\n", "-------------------------------------------");

    for (int epoch = 0; epoch < 200000; epoch++) {
        int a = rng_int(rng, n_total);
        int is_tp_a = a < n_tiles;
        int local_a = is_tp_a ? a : a - n_tiles;
        const Tiling *t_a = is_tp_a ? tp : tm;
        int nn = t_a->n_tile_nbr[local_a];
        if (nn == 0) continue;

        int local_b = t_a->tile_neighbors[local_a][rng_int(rng, nn)];
        int b_is_tp = is_tp_a;
        if ((rng_next(rng) & 1)) b_is_tp = !b_is_tp;
        int b = b_is_tp ? local_b : local_b + n_tiles;

        int sz_b = b_is_tp ? tp->tile_size[local_b] : tm->tile_size[local_b];

        if (is_rep[a] && !is_rep[b]) {
            if (sz_b >= 20) is_rep[b] = 1;
        } else if (!is_rep[a] && is_rep[b]) {
            if ((rng_next(rng) >> 33) < (uint64_t)(p_kill * (1ULL << 31)))
                is_rep[b] = 0;
        }

        /* Mutation */
        if ((rng_next(rng) >> 33) < (uint64_t)(mu_rate * (1ULL << 31))) {
            int victim = rng_int(rng, n_total);
            is_rep[victim] = 0;
        }

        if (epoch % 20000 == 0 || epoch == 199999) {
            int n_rep = 0;
            for (int i = 0; i < n_total; i++) n_rep += is_rep[i];
            printf("  %8d  %8d  %7.1f%%  %9.1f%%\n", epoch, n_rep,
                   100.0 * n_rep / n_total,
                   100.0 * n_rep / viable);
        }
    }

    free(is_rep);
    tiling_free(tp);
    tiling_free(tm);
    mesh_free(m);

    printf("\n=== Diagnostic complete ===\n");
    return 0;
}
