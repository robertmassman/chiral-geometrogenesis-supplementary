/*
 * Stella Soup: Ternary Computational Life (C Implementation)
 * ===========================================================
 * High-performance C port of the Python soup.py simulation.
 *
 * Inspired by "Computational Life" (Aguera y Arcas et al., 2024)
 * adapted to StellaLang's ternary (Z_3) building blocks.
 *
 * Every operation grounded in Chiral Geometrogenesis proofs:
 *   - Trit cells from Z_3 center symmetry (Def 0.1.2)
 *   - Two heads from T+, T- tetrahedra (Def 0.1.1)
 *   - Copy = info transfer between T+ and T- (Thm 0.2.1)
 *   - Loops = Z_3 superselection gates (Prop 0.0.17h)
 *   - Head movement = pointer advance (computational primitive)
 *
 * Compile: cc -O3 -o stella_soup soup.c -lm
 * Run:     ./stella_soup --epochs 30000000 --seed 42
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>
#include <getopt.h>

/* === Ternary constants === */
#define Z3 3

/* === Default parameters === */
#define DEFAULT_SOUP_SIZE    4096
#define DEFAULT_PROG_SIZE   24
#define DEFAULT_MAX_STEPS   729
#define DEFAULT_EPOCHS      2000000
#define DEFAULT_LOG_INTERVAL   10000
#define DEFAULT_CHECK_INTERVAL 100000

/* === Instruction encoding (trit pairs) === */
/* (high, low) -> high * 3 + low */
#define OP_NOP   0  /* (0,0) */
#define OP_ROT   1  /* (0,1) Def 0.1.2: phase rotate */
#define OP_FWD0  2  /* (0,2) advance h0 */
#define OP_BCK0  3  /* (1,0) retreat h0 (cyclic) */
#define OP_FWD1  4  /* (1,1) Def 0.1.1: T- traversal */
#define OP_OPEN  5  /* (1,2) Prop 0.0.17h: gate open */
#define OP_CLOSE 6  /* (2,0) Prop 0.0.17h: gate close */
#define OP_CPY01 7  /* (2,1) Thm 0.2.1: T+ -> T- */
#define OP_CPY10 8  /* (2,2) Thm 0.2.1: T- -> T+ */

/* === PRNG (xoshiro256**) === */
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
    /* SplitMix64 to initialize state */
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        rng_state[i] = z ^ (z >> 31);
    }
}

/* Random integer in [0, n) */
static inline uint32_t rng_int(uint32_t n) {
    return (uint32_t)((rng_next() >> 33) % n);
}

/* Random float in [0, 1) */
static inline double rng_float(void) {
    return (rng_next() >> 11) * 0x1.0p-53;
}

/* === Core VM === */

static void execute_tape(uint8_t *tape, int tape_len, int max_steps) {
    int ip = 0;
    int h0 = 0;
    int h1 = tape_len / 2;
    int steps = 0;
    /* Precompute for branchless modular increment */
    int tl_mask = tape_len; /* Not a power of 2, need real mod */

    while (steps < max_steps && ip + 1 < tape_len) {
        int op = tape[ip] * 3 + tape[ip + 1];

        switch (op) {
        case OP_NOP:
            break;

        case OP_ROT: {
            /* Branchless mod-3 increment: if val<2, val+1; else 0 */
            uint8_t v = tape[h0];
            tape[h0] = v < 2 ? v + 1 : 0;
            break;
        }

        case OP_FWD0:
            if (++h0 >= tl_mask) h0 = 0;
            break;

        case OP_BCK0:
            if (--h0 < 0) h0 = tl_mask - 1;
            break;

        case OP_FWD1:
            if (++h1 >= tl_mask) h1 = 0;
            break;

        case OP_OPEN:
            if (tape[h0] == 0) {
                int depth = 1;
                int pos = ip + 2;
                while (depth > 0 && pos + 1 < tape_len) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == OP_OPEN) depth++;
                    else if (inner == OP_CLOSE) depth--;
                    pos += 2;
                }
                if (depth == 0)
                    ip = pos - 2;
            }
            break;

        case OP_CLOSE:
            if (tape[h0] != 0) {
                int depth = 1;
                int pos = ip - 2;
                while (depth > 0 && pos >= 0) {
                    int inner = tape[pos] * 3 + tape[pos + 1];
                    if (inner == OP_CLOSE) depth++;
                    else if (inner == OP_OPEN) depth--;
                    pos -= 2;
                }
                if (depth == 0)
                    ip = pos + 2;
            }
            break;

        case OP_CPY01:
            tape[h1] = tape[h0];
            break;

        case OP_CPY10:
            tape[h0] = tape[h1];
            break;
        }

        ip += 2;
        steps++;
    }
}

/* === Soup simulation === */

typedef struct {
    uint8_t *data;       /* soup_size * prog_size flat array */
    int soup_size;
    int prog_size;
    int max_steps;
    double mutation_rate;
    uint8_t *work_tape;  /* 2 * prog_size scratch buffer */
    long epoch;
} Soup;

static Soup *soup_create(int soup_size, int prog_size, int max_steps,
                          double mutation_rate) {
    Soup *s = calloc(1, sizeof(Soup));
    s->soup_size = soup_size;
    s->prog_size = prog_size;
    s->max_steps = max_steps;
    s->mutation_rate = mutation_rate;
    s->data = malloc(soup_size * prog_size);
    s->work_tape = malloc(2 * prog_size);
    s->epoch = 0;

    /* Initialize with random trits */
    for (int i = 0; i < soup_size * prog_size; i++)
        s->data[i] = rng_int(Z3);

    return s;
}

static void soup_free(Soup *s) {
    free(s->data);
    free(s->work_tape);
    free(s);
}

static inline uint8_t *soup_prog(Soup *s, int idx) {
    return s->data + idx * s->prog_size;
}

static void soup_interact(Soup *s, int a, int b) {
    int psize = s->prog_size;
    int tape_len = 2 * psize;

    /* Concatenate A + B into work tape */
    memcpy(s->work_tape, soup_prog(s, a), psize);
    memcpy(s->work_tape + psize, soup_prog(s, b), psize);

    /* Execute */
    execute_tape(s->work_tape, tape_len, s->max_steps);

    /* Split back */
    memcpy(soup_prog(s, a), s->work_tape, psize);
    memcpy(soup_prog(s, b), s->work_tape + psize, psize);
}

static void soup_mutate(Soup *s) {
    if (s->mutation_rate <= 0.0) return;

    int total = s->soup_size * s->prog_size;
    /* Expected mutations per epoch */
    int expected = (int)(total * s->mutation_rate);
    /* Poisson approximation: do exactly expected mutations at random positions */
    for (int i = 0; i < expected; i++) {
        int pos = rng_int(total);
        s->data[pos] = rng_int(Z3);
    }
}

static void soup_epoch(Soup *s) {
    int n_interactions = s->soup_size / 2;
    for (int i = 0; i < n_interactions; i++) {
        int a = rng_int(s->soup_size);
        int b = rng_int(s->soup_size - 1);
        if (b >= a) b++;  /* Avoid self-interaction */
        soup_interact(s, a, b);
    }
    soup_mutate(s);
    s->epoch++;
}

/* === Metrics === */

/* Compare two programs for qsort */
static int prog_size_global;

static int prog_cmp(const void *a, const void *b) {
    return memcmp(a, b, prog_size_global);
}

typedef struct {
    int unique;
    int top_count;
    double trit_entropy;
} Metrics;

static Metrics soup_metrics(Soup *s) {
    Metrics m = {0};
    int n = s->soup_size;
    int psize = s->prog_size;

    /* Sort a copy to count uniques */
    uint8_t *sorted = malloc(n * psize);
    memcpy(sorted, s->data, n * psize);
    prog_size_global = psize;
    qsort(sorted, n, psize, prog_cmp);

    int unique = 1;
    int run = 1;
    int max_run = 1;
    for (int i = 1; i < n; i++) {
        if (memcmp(sorted + i * psize, sorted + (i - 1) * psize, psize) == 0) {
            run++;
            if (run > max_run) max_run = run;
        } else {
            unique++;
            run = 1;
        }
    }
    m.unique = unique;
    m.top_count = max_run;
    free(sorted);

    /* Trit entropy */
    long counts[Z3] = {0};
    int total = n * psize;
    for (int i = 0; i < total; i++)
        counts[s->data[i]]++;

    m.trit_entropy = 0.0;
    for (int t = 0; t < Z3; t++) {
        if (counts[t] > 0) {
            double p = (double)counts[t] / total;
            m.trit_entropy -= p * log2(p);
        }
    }

    return m;
}

/* === Self-replicator check === */

static int check_replicators(Soup *s, int sample_size) {
    int psize = s->prog_size;
    int tape_len = 2 * psize;
    uint8_t *tape = malloc(tape_len);
    uint8_t *food = malloc(psize);
    int perfect = 0;
    int partial = 0;

    for (int i = 0; i < sample_size; i++) {
        int idx = rng_int(s->soup_size);
        uint8_t *prog = soup_prog(s, idx);

        /* Test with zero food */
        memcpy(tape, prog, psize);
        memset(tape + psize, 0, psize);
        execute_tape(tape, tape_len, s->max_steps);

        if (memcmp(tape, prog, psize) == 0 &&
            memcmp(tape + psize, prog, psize) == 0) {
            perfect++;
            continue;
        }

        /* Test with random food */
        for (int j = 0; j < psize; j++)
            food[j] = rng_int(Z3);
        memcpy(tape, prog, psize);
        memcpy(tape + psize, food, psize);
        execute_tape(tape, tape_len, s->max_steps);

        if (memcmp(tape, prog, psize) == 0 &&
            memcmp(tape + psize, prog, psize) == 0) {
            perfect++;
        } else if (memcmp(tape, prog, psize) == 0 ||
                   memcmp(tape + psize, prog, psize) == 0) {
            partial++;
        }
    }

    free(tape);
    free(food);

    if (perfect > 0)
        printf("  REPLICATORS: %d perfect, %d partial (of %d sampled)\n",
               perfect, partial, sample_size);
    else if (partial > 0)
        printf("  partial: %d (of %d sampled)\n", partial, sample_size);

    return perfect;
}

/* Print a program as instruction mnemonics */
static void print_program(const uint8_t *prog, int psize) {
    static const char *names[] = {
        "NOP", "ROT", "FWD0", "BCK0", "FWD1", "[", "]", "CPY+", "CPY-"
    };
    printf("  Instructions: ");
    for (int i = 0; i + 1 < psize; i += 2) {
        int op = prog[i] * Z3 + prog[i + 1];
        printf("%s ", names[op]);
    }
    printf("\n  Raw trits:    [");
    for (int i = 0; i < psize; i++) {
        printf("%d%s", prog[i], i < psize - 1 ? ", " : "");
    }
    printf("]\n");
}

/* Find and print top N most common programs */
static void print_top_programs(Soup *s, int top_n) {
    int n = s->soup_size;
    int psize = s->prog_size;

    uint8_t *sorted = malloc(n * psize);
    memcpy(sorted, s->data, n * psize);
    prog_size_global = psize;
    qsort(sorted, n, psize, prog_cmp);

    /* Find runs */
    typedef struct { int count; int start; } Run;
    Run *runs = malloc(n * sizeof(Run));
    int n_runs = 0;
    int run_start = 0;
    int run_count = 1;

    for (int i = 1; i < n; i++) {
        if (memcmp(sorted + i * psize, sorted + (i - 1) * psize, psize) == 0) {
            run_count++;
        } else {
            runs[n_runs++] = (Run){run_count, run_start};
            run_start = i;
            run_count = 1;
        }
    }
    runs[n_runs++] = (Run){run_count, run_start};

    /* Sort runs by count descending (simple selection for small top_n) */
    for (int i = 0; i < top_n && i < n_runs; i++) {
        int max_idx = i;
        for (int j = i + 1; j < n_runs; j++) {
            if (runs[j].count > runs[max_idx].count)
                max_idx = j;
        }
        Run tmp = runs[i];
        runs[i] = runs[max_idx];
        runs[max_idx] = tmp;
    }

    printf("\nTop %d most common programs:\n", top_n < n_runs ? top_n : n_runs);
    for (int i = 0; i < top_n && i < n_runs; i++) {
        double pct = 100.0 * runs[i].count / n;
        printf("  count=%5d (%5.1f%%): [", runs[i].count, pct);
        uint8_t *p = sorted + runs[i].start * psize;
        for (int j = 0; j < psize; j++)
            printf("%d%s", p[j], j < psize - 1 ? ", " : "");
        printf("]\n");
    }

    free(runs);
    free(sorted);
}

/* === Main === */

static void usage(const char *prog) {
    printf("Stella Soup: Ternary Computational Life\n");
    printf("Usage: %s [options]\n\n", prog);
    printf("Options:\n");
    printf("  --soup-size N       Programs in soup (default: %d)\n", DEFAULT_SOUP_SIZE);
    printf("  --program-size N    Trits per program (default: %d)\n", DEFAULT_PROG_SIZE);
    printf("  --max-steps N       Max steps per interaction (default: %d)\n", DEFAULT_MAX_STEPS);
    printf("  --epochs N          Epochs to run (default: %d)\n", DEFAULT_EPOCHS);
    printf("  --mutation-rate F   Per-trit mutation rate (default: 0.001)\n");
    printf("  --no-mutations      Disable mutations\n");
    printf("  --log-interval N    Epochs between logs (default: %d)\n", DEFAULT_LOG_INTERVAL);
    printf("  --check-interval N  Epochs between replicator checks (default: %d)\n", DEFAULT_CHECK_INTERVAL);
    printf("  --seed N            Random seed\n");
    printf("  --help              Show this help\n");
}

int main(int argc, char *argv[]) {
    int soup_size = DEFAULT_SOUP_SIZE;
    int prog_size = DEFAULT_PROG_SIZE;
    int max_steps = DEFAULT_MAX_STEPS;
    long epochs = DEFAULT_EPOCHS;
    double mutation_rate = 0.001;
    int log_interval = DEFAULT_LOG_INTERVAL;
    int check_interval = DEFAULT_CHECK_INTERVAL;
    uint64_t seed = (uint64_t)time(NULL);
    int no_mutations = 0;

    static struct option long_options[] = {
        {"soup-size",      required_argument, 0, 's'},
        {"program-size",   required_argument, 0, 'p'},
        {"max-steps",      required_argument, 0, 'm'},
        {"epochs",         required_argument, 0, 'e'},
        {"mutation-rate",  required_argument, 0, 'r'},
        {"no-mutations",   no_argument,       0, 'n'},
        {"log-interval",   required_argument, 0, 'l'},
        {"check-interval", required_argument, 0, 'c'},
        {"seed",           required_argument, 0, 'S'},
        {"help",           no_argument,       0, 'h'},
        {0, 0, 0, 0}
    };

    int opt;
    while ((opt = getopt_long(argc, argv, "hs:p:m:e:r:nl:c:S:", long_options, NULL)) != -1) {
        switch (opt) {
        case 's': soup_size = atoi(optarg); break;
        case 'p': prog_size = atoi(optarg); break;
        case 'm': max_steps = atoi(optarg); break;
        case 'e': epochs = atol(optarg); break;
        case 'r': mutation_rate = atof(optarg); break;
        case 'n': no_mutations = 1; break;
        case 'l': log_interval = atoi(optarg); break;
        case 'c': check_interval = atoi(optarg); break;
        case 'S': seed = (uint64_t)atol(optarg); break;
        case 'h': usage(argv[0]); return 0;
        default:  usage(argv[0]); return 1;
        }
    }

    if (no_mutations) mutation_rate = 0.0;
    rng_seed(seed);

    printf("Stella Soup: Ternary Computational Life (C)\n");
    printf("============================================================\n");
    printf("Soup size:     %d programs\n", soup_size);
    printf("Program size:  %d trits (%d instruction pairs)\n", prog_size, prog_size / 2);
    printf("Max steps:     %d per interaction\n", max_steps);
    printf("Mutation rate: %.4f\n", mutation_rate);
    printf("Epochs:        %ld\n", epochs);
    printf("Seed:          %llu\n", (unsigned long long)seed);
    printf("============================================================\n\n");

    printf("%10s | %6s | %5s | %7s | Notes\n", "Epoch", "Unique", "Top", "H(trit)");
    printf("--------------------------------------------------------------\n");

    Soup *soup = soup_create(soup_size, prog_size, max_steps, mutation_rate);
    int total_perfect = 0;

    struct timespec t_start, t_now;
    clock_gettime(CLOCK_MONOTONIC, &t_start);

    for (long e = 0; e < epochs; e++) {
        soup_epoch(soup);

        if (soup->epoch % log_interval == 0) {
            Metrics m = soup_metrics(soup);
            printf("%10ld | %6d | %5d | %7.4f | ",
                   soup->epoch, m.unique, m.top_count, m.trit_entropy);

            if (soup->epoch % check_interval == 0) {
                int p = check_replicators(soup, 200);
                total_perfect += p;
                if (p > 0) {
                    printf("PERFECT REPLICATORS FOUND!");
                }
            }
            printf("\n");
            fflush(stdout);
        }
    }

    clock_gettime(CLOCK_MONOTONIC, &t_now);
    double elapsed = (t_now.tv_sec - t_start.tv_sec) +
                     (t_now.tv_nsec - t_start.tv_nsec) * 1e-9;

    printf("\nCompleted %ld epochs in %.1fs\n", epochs, elapsed);
    printf("(%.2f us per epoch, %.0f epochs/sec)\n",
           elapsed / epochs * 1e6, epochs / elapsed);

    /* Final report */
    printf("\n============================================================\n");
    printf("Final Report\n");
    printf("============================================================\n");

    Metrics final_m = soup_metrics(soup);
    printf("Unique programs: %d / %d\n", final_m.unique, soup_size);
    printf("Most common:     %d copies\n", final_m.top_count);
    printf("Trit entropy:    %.4f (max = %.4f)\n", final_m.trit_entropy, log2(Z3));

    if (total_perfect > 0)
        printf("\nTotal perfect replicators detected: %d\n", total_perfect);
    else
        printf("\nNo perfect self-replicators detected.\n");

    print_top_programs(soup, 5);

    printf("\n============================================================\n");
    printf("CG Connection: All operations grounded in proven theorems.\n");
    printf("  Z_3 trits (Def 0.1.2), T+/T- heads (Def 0.1.1),\n");
    printf("  Superselection gates (Prop 0.0.17h),\n");
    printf("  Head movement (computational primitive)\n");
    printf("============================================================\n");

    soup_free(soup);
    return 0;
}
