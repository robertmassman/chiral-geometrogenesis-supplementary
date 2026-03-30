/*
 * Error Threshold ↔ Confinement Connection
 * ==========================================
 *
 * Investigates whether the critical mutation rate μ_c ≈ 0.011 (Eigen error
 * catastrophe, 10% density threshold) has a formal analog in dynamical
 * confinement (Thm 2.5.2).
 *
 * Three sub-questions:
 *
 *   (a) Map μ_c to a physical parameter.
 *       Strategy: measure μ_c at multiple prog_sizes. If μ_c × prog_size = const,
 *       this is the classic Eigen threshold and μ_c maps to 1/L (inverse
 *       information length). In lattice QCD, the confinement scale maps to
 *       the lattice coupling β_c — we identify μ_c ↔ 1/β_c.
 *
 *   (b) Check whether the error threshold scales with prog_size the same way
 *       the confinement scale depends on N_c.
 *       Strategy: sweep prog_size ∈ {12, 18, 24, 36, 48} and find μ_c for each.
 *       Eigen predicts: μ_c × L = ln(σ) where σ = selective advantage.
 *       If the product μ_c × L is constant, this confirms Eigen scaling.
 *
 *   (c) Determine if the ~35% "interaction noise floor" at zero mutation has
 *       a confinement analog.
 *       Strategy: measure zero-mutation equilibrium density at each prog_size.
 *       If constant (~65%), the noise floor is geometric (VM instruction set);
 *       if prog_size-dependent, it reflects an information-capacity effect.
 *
 * Method: Flat-tile soup (no 2D mesh — faster) with seeded replicators.
 * For each (prog_size, mutation_rate), seed all tiles with a known replicator,
 * evolve for E epochs, measure final replicator density.
 *
 * Related:
 *   - Thm 2.5.2: Dynamical confinement from pressure mechanism
 *   - Prop 2.5.2c: Transfer matrix phase structure, β_c
 *   - Eigen quasispecies theory: μ_c × L ≈ ln(σ)
 *   - Prop 0.0.XXe: Phase 1 2D Soup Results (mutation sweep at prog_size=24)
 *
 * Compile: cc -O3 -o error_threshold_confinement error_threshold_confinement.c -lm
 * Run:     ./error_threshold_confinement
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>

#define Z3 3
#define MAX_PROG_SIZE 64

/* ================================================================
 * PRNG (xoshiro256** with explicit state)
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
 * Opcodes
 * ================================================================ */

#define OP_NOP   0
#define OP_ROT   1
#define OP_FWD0  2
#define OP_BCK0  3
#define OP_FWD1  4
#define OP_OPEN  5
#define OP_CLOSE 6
#define OP_CPY01 7
#define OP_CPY10 8

/* ================================================================
 * VM
 * ================================================================ */

static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
    int ip = 0, h0 = 0, h1 = tape_len / 2, steps = 0;
    while (steps < max_steps && ip + 1 < tape_len) {
        int op = tape[ip] * 3 + tape[ip + 1];
        switch (op) {
        case OP_NOP: break;
        case OP_ROT: { uint8_t v = tape[h0]; tape[h0] = v < 2 ? v + 1 : 0; break; }
        case OP_FWD0: if (++h0 >= tape_len) h0 = 0; break;
        case OP_BCK0: if (--h0 < 0) h0 = tape_len - 1; break;
        case OP_FWD1: if (++h1 >= tape_len) h1 = 0; break;
        case OP_OPEN:
            if (tape[h0] == 0) {
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
            if (tape[h0] != 0) {
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
        case OP_CPY01: tape[h1] = tape[h0]; break;
        case OP_CPY10: tape[h0] = tape[h1]; break;
        }
        ip += 2;
        steps++;
    }
}

/* ================================================================
 * Replicator Construction
 * ================================================================
 *
 * The canonical replicator core is 12 instructions (24 trits):
 *   [ [ CPY+ FWD1 FWD0 ] CPY+ FWD1 FWD0 ] ] FWD1
 *
 * For prog_size > 24: pad with NOP (0,0) after the core
 * For prog_size < 24: use a shorter replicator core
 *
 * The minimal replicator needs: [ CPY+ FWD1 FWD0 ] (5 instructions = 10 trits)
 * with a wrapping outer loop to repeat: [ [ CPY+ FWD1 FWD0 ] ] (7 instr = 14 trits)
 *
 * For prog_size = 12: [ CPY+ FWD1 FWD0 ] NOP = 6 instructions
 * For prog_size >= 14: full nested replicator + NOP padding
 */

/* The 24-trit canonical replicator */
static const uint8_t REPL_CORE[24] = {
    1,2, 1,2, 2,1, 1,1, 0,2, 2,0, 2,1, 1,1, 0,2, 2,0, 2,0, 1,1
};

/* Minimal 12-trit replicator: [ CPY+ FWD1 FWD0 ] NOP */
static const uint8_t REPL_MINI[12] = {
    1,2, 2,1, 1,1, 0,2, 2,0, 0,0
};

static void build_replicator(uint8_t *prog, int prog_size) {
    memset(prog, 0, prog_size);  /* NOP padding */
    if (prog_size <= 12) {
        int copy = prog_size < 12 ? prog_size : 12;
        memcpy(prog, REPL_MINI, copy);
    } else if (prog_size <= 24) {
        memcpy(prog, REPL_CORE, prog_size < 24 ? prog_size : 24);
    } else {
        /* Core + NOP padding */
        memcpy(prog, REPL_CORE, 24);
    }
}

/* Test if a program is a replicator: execute prog + zeros, check if
 * the second half matches the first half */
static int is_replicator(const uint8_t *prog, int prog_size, int max_steps) {
    int tape_len = 2 * prog_size;
    uint8_t tape[2 * MAX_PROG_SIZE];
    memcpy(tape, prog, prog_size);
    memset(tape + prog_size, 0, prog_size);
    execute_tape(tape, tape_len, max_steps);
    return memcmp(tape + prog_size, prog, prog_size) == 0;
}

static int is_trivial(const uint8_t *data, int size) {
    for (int i = 1; i < size; i++)
        if (data[i] != data[0]) return 0;
    return 1;
}

/* ================================================================
 * Flat-tile Soup (simplified, no 2D mesh)
 * ================================================================ */

typedef struct {
    uint8_t *tiles;     /* n_tiles * prog_size */
    int n_tiles;
    int prog_size;
    int max_steps;
    double mutation_rate;
    uint64_t rng[4];
} FlatSoup;

static FlatSoup *soup_create(int n_tiles, int prog_size, int max_steps,
                               double mutation_rate, uint64_t seed) {
    FlatSoup *s = calloc(1, sizeof(FlatSoup));
    s->n_tiles = n_tiles;
    s->prog_size = prog_size;
    s->max_steps = max_steps;
    s->mutation_rate = mutation_rate;
    s->tiles = malloc(n_tiles * prog_size);
    rng_seed(s->rng, seed);
    return s;
}

static void soup_free(FlatSoup *s) {
    free(s->tiles); free(s);
}

/* Seed ALL tiles with the known replicator */
static void soup_seed_all(FlatSoup *s) {
    uint8_t repl[MAX_PROG_SIZE];
    build_replicator(repl, s->prog_size);
    for (int t = 0; t < s->n_tiles; t++)
        memcpy(s->tiles + t * s->prog_size, repl, s->prog_size);
}

/* Run one epoch: n_tiles/2 random pairings + mutations */
static void soup_epoch(FlatSoup *s) {
    int ps = s->prog_size;
    int nt = s->n_tiles;
    int n_interact = nt / 2;
    uint8_t work[2 * MAX_PROG_SIZE];

    for (int i = 0; i < n_interact; i++) {
        int ta = rng_int(s->rng, nt);
        int tb = rng_int(s->rng, nt - 1);
        if (tb >= ta) tb++;

        memcpy(work, s->tiles + ta * ps, ps);
        memcpy(work + ps, s->tiles + tb * ps, ps);
        execute_tape(work, 2 * ps, s->max_steps);
        memcpy(s->tiles + ta * ps, work, ps);
        memcpy(s->tiles + tb * ps, work + ps, ps);
    }

    /* Mutations */
    if (s->mutation_rate > 0.0) {
        int total_trits = nt * ps;
        int expected = (int)(total_trits * s->mutation_rate);
        for (int i = 0; i < expected; i++) {
            int pos = rng_int(s->rng, total_trits);
            s->tiles[pos] = rng_int(s->rng, Z3);
        }
    }
}

/* Measure replicator density: fraction of tiles that are non-trivial replicators */
static double soup_density(FlatSoup *s) {
    int ps = s->prog_size;
    int nt = s->n_tiles;
    int sample_n = nt < 500 ? nt : 500;
    int repl_count = 0;

    /* Use separate RNG for sampling to not perturb dynamics */
    uint64_t met_rng[4];
    rng_seed(met_rng, s->rng[0] ^ 0xdeadbeef);

    for (int i = 0; i < sample_n; i++) {
        int t = rng_int(met_rng, nt);
        uint8_t *prog = s->tiles + t * ps;
        if (!is_trivial(prog, ps) && is_replicator(prog, ps, s->max_steps))
            repl_count++;
    }
    return (double)repl_count / sample_n;
}

/* ================================================================
 * Experiment (a): Mutation rate sweep at multiple prog_sizes
 * ================================================================ */

static void experiment_a(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("EXPERIMENT (a): μ_c vs prog_size — Eigen scaling test\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    /* prog_size >= 24 required (canonical replicator core = 24 trits).
     * Larger sizes: same 24-trit core + NOP padding.
     * Key test: does μ_c scale with prog_size (Eigen) or stay constant (core-only)? */
    int prog_sizes[] = {24, 30, 36, 42, 48};
    int n_ps = 5;

    /* Mutation rates to sweep — denser near expected μ_c */
    double mut_rates[] = {
        0.0, 0.0005, 0.001, 0.002, 0.003, 0.004, 0.005, 0.006,
        0.007, 0.008, 0.010, 0.012, 0.015, 0.020
    };
    int n_mut = 14;

    int n_tiles = 1666;
    int n_epochs = 5000;  /* Enough for equilibrium from seeded state */
    int n_trials = 3;

    /* First, verify replicators work at each prog_size */
    printf("Replicator verification:\n");
    for (int p = 0; p < n_ps; p++) {
        int ps = prog_sizes[p];
        int max_steps = 729;  /* scale max_steps with prog_size */
        uint8_t repl[MAX_PROG_SIZE];
        build_replicator(repl, ps);
        int works = is_replicator(repl, ps, max_steps);
        printf("  prog_size=%2d  max_steps=%4d  replicator_works=%s  ",
               ps, max_steps, works ? "YES" : "NO");
        /* Print first few instructions */
        printf("[");
        for (int i = 0; i + 1 < ps && i < 24; i += 2) {
            int op = repl[i] * 3 + repl[i + 1];
            static const char *names[] = {"NOP","ROT","FWD","BCK","FW1","[","]","CP+","CP-"};
            printf("%s ", names[op]);
        }
        if (ps > 24) printf("...");
        printf("]\n");
    }
    printf("\n");

    /* Header */
    printf("%-6s", "μ \\ L");
    for (int p = 0; p < n_ps; p++)
        printf("  L=%-4d", prog_sizes[p]);
    printf("\n");
    printf("------");
    for (int p = 0; p < n_ps; p++)
        printf("  ------");
    printf("\n");

    /* Storage for μ_c extraction */
    double densities[14][5];  /* [mut_idx][ps_idx] */

    for (int m = 0; m < n_mut; m++) {
        double mu = mut_rates[m];
        printf("%-6.4f", mu);
        fflush(stdout);

        for (int p = 0; p < n_ps; p++) {
            int ps = prog_sizes[p];
            int max_steps = 729;
            double total_density = 0;

            for (int trial = 0; trial < n_trials; trial++) {
                FlatSoup *s = soup_create(n_tiles, ps, max_steps, mu,
                                           42 + trial * 1000 + m * 100 + p * 10);
                soup_seed_all(s);
                for (int e = 0; e < n_epochs; e++)
                    soup_epoch(s);
                total_density += soup_density(s);
                soup_free(s);
            }

            double avg = total_density / n_trials;
            densities[m][p] = avg;
            printf("  %5.1f%%", avg * 100);
            fflush(stdout);
        }
        printf("\n");
    }

    /* Extract μ_c (density drops below 10%) for each prog_size */
    printf("\n--- Error threshold extraction (density < 10%%) ---\n\n");
    printf("  prog_size   μ_c      μ_c × L    Eigen pred (1/L)\n");
    printf("  ---------   ------   --------   ----------------\n");

    for (int p = 0; p < n_ps; p++) {
        int ps = prog_sizes[p];
        double mu_c = -1;
        /* Find first mutation rate where density < 10% */
        for (int m = 1; m < n_mut; m++) {
            if (densities[m][p] < 0.10 && densities[m - 1][p] >= 0.10) {
                /* Linear interpolation */
                double d0 = densities[m - 1][p];
                double d1 = densities[m][p];
                double m0 = mut_rates[m - 1];
                double m1 = mut_rates[m];
                mu_c = m0 + (m1 - m0) * (d0 - 0.10) / (d0 - d1);
                break;
            }
        }
        if (mu_c < 0) {
            /* Check if always above or always below */
            if (densities[n_mut - 1][p] >= 0.10)
                printf("  L=%-4d      >%.4f  >%.3f     %.5f\n",
                       ps, mut_rates[n_mut - 1], mut_rates[n_mut - 1] * ps,
                       1.0 / ps);
            else
                printf("  L=%-4d      <%.4f  <%.3f     %.5f\n",
                       ps, mut_rates[1], mut_rates[1] * ps, 1.0 / ps);
        } else {
            printf("  L=%-4d      %.4f   %.3f      %.5f\n",
                   ps, mu_c, mu_c * ps, 1.0 / ps);
        }
    }
    printf("\n");
    printf("If μ_c × L ≈ const across prog_sizes, this confirms Eigen scaling.\n");
    printf("The product μ_c × L = ln(σ) where σ is the selective advantage\n");
    printf("of the replicator over random programs.\n\n");
}

/* ================================================================
 * Experiment (b): Transition shape characterization
 * ================================================================ */

static void experiment_b(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("EXPERIMENT (b): Transition shape — sharp or smooth?\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    /* Fine-grained sweep around μ_c for prog_size=24 */
    double mut_rates[] = {
        0.002, 0.0025, 0.003, 0.0035, 0.004, 0.0042, 0.0044, 0.0046,
        0.0048, 0.005, 0.0055, 0.006, 0.007, 0.008
    };
    int n_mut = 14;

    int ps = 24;
    int max_steps = 729;
    int n_tiles = 1666;
    int n_epochs = 5000;
    int n_trials = 5;  /* More trials for finer statistics */

    printf("Fine sweep around μ_c for prog_size=%d, %d tiles, %d epochs, %d trials\n\n",
           ps, n_tiles, n_epochs, n_trials);
    printf("  μ         avg_density  std_dev    μ×L     order_param\n");
    printf("  --------  ----------   --------   ------  -----------\n");

    for (int m = 0; m < n_mut; m++) {
        double mu = mut_rates[m];
        double sum = 0, sum2 = 0;

        for (int trial = 0; trial < n_trials; trial++) {
            FlatSoup *s = soup_create(n_tiles, ps, max_steps, mu,
                                       42 + trial * 7919 + m * 31);
            soup_seed_all(s);
            for (int e = 0; e < n_epochs; e++)
                soup_epoch(s);
            double d = soup_density(s);
            sum += d;
            sum2 += d * d;
            soup_free(s);
        }

        double avg = sum / n_trials;
        double var = sum2 / n_trials - avg * avg;
        double std = var > 0 ? sqrt(var) : 0;

        /* Order parameter: normalize to [0,1] using zero-mutation baseline ~0.65 */
        double order = avg / 0.65;

        printf("  %.4f    %5.1f%%       ±%4.1f%%    %.3f   %.3f\n",
               mu, avg * 100, std * 100, mu * ps, order);
        fflush(stdout);
    }

    printf("\n");
    printf("Interpretation:\n");
    printf("  - Sharp transition (order_param drops ~1→0 over narrow Δμ):\n");
    printf("    First-order-like, analogous to Potts deconfinement at T_c.\n");
    printf("  - Smooth crossover (gradual decline):\n");
    printf("    Second-order or crossover, analogous to QCD with light quarks.\n");
    printf("  - Large std_dev at μ_c (critical fluctuations):\n");
    printf("    Indicates a genuine phase transition, not a crossover.\n\n");
}

/* ================================================================
 * Experiment (c): Zero-mutation noise floor vs prog_size
 * ================================================================ */

static void experiment_c(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("EXPERIMENT (c): Zero-mutation noise floor vs prog_size\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    int prog_sizes[] = {24, 30, 36, 42, 48};
    int n_ps = 5;
    int n_tiles = 1666;
    int n_epochs = 5000;
    int n_trials = 3;

    printf("Fully seeded, mutation_rate=0, measure equilibrium density.\n\n");
    printf("  prog_size  max_steps  density    noise_floor  interp\n");
    printf("  ---------  ---------  --------   -----------  ------\n");

    for (int p = 0; p < n_ps; p++) {
        int ps = prog_sizes[p];
        int max_steps = 729;
        double total = 0;

        for (int trial = 0; trial < n_trials; trial++) {
            FlatSoup *s = soup_create(n_tiles, ps, max_steps, 0.0,
                                       42 + trial * 1000 + p * 10);
            soup_seed_all(s);
            for (int e = 0; e < n_epochs; e++)
                soup_epoch(s);
            total += soup_density(s);
            soup_free(s);
        }

        double avg = total / n_trials;
        double noise = 1.0 - avg;

        const char *interp;
        if (noise < 0.25)
            interp = "low noise";
        else if (noise < 0.40)
            interp = "moderate";
        else
            interp = "high noise";

        printf("  L=%-4d     %-4d       %5.1f%%      %5.1f%%       %s\n",
               ps, max_steps, avg * 100, noise * 100, interp);
        fflush(stdout);
    }

    printf("\n");
    printf("NOTE: Flat-tile soup (no geometric overlap between tiles) gives\n");
    printf("100%% density at zero mutation. The ~35%% noise floor from the Phase 1\n");
    printf("results comes from BFS-patch overlap on the 2D triangulated mesh,\n");
    printf("where writing back overlapping patches creates interference.\n\n");
    printf("Interpretation of noise floor:\n");
    printf("  - Flat tiles (this experiment): noise floor = 0%% (no overlap)\n");
    printf("  - 2D soup (Phase 1): noise floor ≈ 35%% (patch overlap)\n");
    printf("  The 35%% noise floor is a GEOMETRIC property of the 2D tiling,\n");
    printf("  not an intrinsic VM property. Analogous to how the gluon\n");
    printf("  condensate <G²> depends on the lattice geometry, not just the\n");
    printf("  gauge group.\n\n");
}

/* ================================================================
 * Summary and Physics Mapping
 * ================================================================ */

static void print_summary(void) {
    printf("═══════════════════════════════════════════════════════════════\n");
    printf("PHYSICS MAPPING: Error Threshold ↔ Confinement\n");
    printf("═══════════════════════════════════════════════════════════════\n\n");

    printf("Structural parallel:\n\n");
    printf("  Soup quantity           QCD analog              Role\n");
    printf("  ─────────────────────   ─────────────────────   ────────────────\n");
    printf("  Mutation rate μ         Temperature T           Disorder parameter\n");
    printf("  μ_c (error threshold)   T_c (deconfinement)     Critical point\n");
    printf("  Replicator density      String tension σ(T)     Order parameter\n");
    printf("  prog_size L             Genome length / N_c     Information capacity\n");
    printf("  ~35%% noise floor        Gluon condensate <G²>   Vacuum fluctuations\n");
    printf("  Replicator (μ<μ_c)      Hadron (T<T_c)          Coherent structure\n");
    printf("  Random soup (μ>μ_c)     QGP (T>T_c)             Dissolved state\n");
    printf("  Eigen threshold μ_c×L   Confinement β_c(N_c)    Critical coupling\n\n");

    printf("QCD confinement (Thm 2.5.2):\n");
    printf("  - Below T_c = 154 MeV: hadrons persist (σ > 0)\n");
    printf("  - Above T_c: deconfinement (σ → 0, QGP)\n");
    printf("  - String tension σ(T) = σ₀(1 - T/T_c)^{2ν}, ν ≈ 0.63 (3D Ising)\n");
    printf("  - Gluon condensate <G²> ≈ 0.012 GeV⁴ (nonzero vacuum fluctuation)\n\n");

    printf("Soup error threshold:\n");
    printf("  - Below μ_c ≈ 0.011: replicators persist (density > 0)\n");
    printf("  - Above μ_c: error catastrophe (density → 0, 10%% threshold)\n");
    printf("  - Density vs μ: smooth decline, not sharp transition\n");
    printf("  - ~35%% noise floor (nonzero even at μ=0)\n\n");

    printf("Potts connection (Prop 2.5.2c):\n");
    printf("  The 3-state Potts model on FCC lattice has a deconfinement\n");
    printf("  transition at β_c with u_3(β_c) = 3^{-3/8} ≈ 0.662. The\n");
    printf("  order-disorder transition (entropy vs energy) is structurally\n");
    printf("  identical to the error threshold (mutation vs selection):\n\n");
    printf("  Potts: Z = Σ_R d_R^{3N} [a_R(β)]^{8N}  at β_c: entropy wins\n");
    printf("  Soup:  density(μ) = selection(L) - mutation(μ×L)  at μ_c: mutation wins\n\n");

    printf("Key question answered by experiments above:\n");
    printf("  Does μ_c × L = const? If yes: Eigen scaling confirmed,\n");
    printf("  and μ_c ↔ 1/β_c is a precise mapping (both are inverse\n");
    printf("  coupling constants controlling coherent-structure persistence).\n\n");
}

/* ================================================================
 * Main
 * ================================================================ */

int main(void) {
    printf("\n");
    printf("╔═══════════════════════════════════════════════════════════════╗\n");
    printf("║  Error Threshold ↔ Confinement Connection                   ║\n");
    printf("║  Prop 0.0.XXe / Thm 2.5.2 / Eigen Quasispecies             ║\n");
    printf("╚═══════════════════════════════════════════════════════════════╝\n\n");

    experiment_c();   /* Fast: zero-mutation noise floor */
    experiment_b();   /* Medium: fine-grained transition shape */
    experiment_a();   /* Slowest: multi-prog_size sweep */
    print_summary();

    return 0;
}
