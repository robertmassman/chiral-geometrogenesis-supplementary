/*
 * Diagnostic: Why are seeded replicators dying?
 * Tracks density epoch-by-epoch to find the failure point.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>

#define Z3 3
#define MAX_VM_STEPS 729
#define PROG_SIZE 24

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
    for (int i = 0; i < 4; i++) {
        seed += 0x9e3779b97f4a7c15ULL;
        uint64_t z = seed;
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
        z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
        rng_state[i] = z ^ (z >> 31);
    }
}

static inline uint32_t rng_int(uint32_t n) {
    return (uint32_t)((rng_next() >> 33) % n);
}

/* === VM === */
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

/* === Test single replicator === */
void test_replicator(void) {
    uint8_t replicator[PROG_SIZE] = {
        0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,1, 0,0, 0,0
    };

    printf("=== Test 1: Replicator + zero food ===\n");
    uint8_t tape[2 * PROG_SIZE];
    memcpy(tape, replicator, PROG_SIZE);
    memset(tape + PROG_SIZE, 0, PROG_SIZE);

    printf("  Before: prog=[");
    for (int i = 0; i < PROG_SIZE; i++) printf("%d", tape[i]);
    printf("] food=[");
    for (int i = PROG_SIZE; i < 2*PROG_SIZE; i++) printf("%d", tape[i]);
    printf("]\n");

    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

    printf("  After:  prog=[");
    for (int i = 0; i < PROG_SIZE; i++) printf("%d", tape[i]);
    printf("] food=[");
    for (int i = PROG_SIZE; i < 2*PROG_SIZE; i++) printf("%d", tape[i]);
    printf("]\n");

    int prog_preserved = memcmp(tape, replicator, PROG_SIZE) == 0;
    int food_copied = memcmp(tape + PROG_SIZE, replicator, PROG_SIZE) == 0;
    printf("  Program preserved: %s\n", prog_preserved ? "YES" : "NO");
    printf("  Food became copy:  %s\n", food_copied ? "YES" : "NO");

    printf("\n=== Test 2: Replicator + random food ===\n");
    rng_seed(42);
    memcpy(tape, replicator, PROG_SIZE);
    for (int i = 0; i < PROG_SIZE; i++) tape[PROG_SIZE + i] = rng_int(Z3);

    printf("  Before: prog=[");
    for (int i = 0; i < PROG_SIZE; i++) printf("%d", tape[i]);
    printf("] food=[");
    for (int i = PROG_SIZE; i < 2*PROG_SIZE; i++) printf("%d", tape[i]);
    printf("]\n");

    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

    printf("  After:  prog=[");
    for (int i = 0; i < PROG_SIZE; i++) printf("%d", tape[i]);
    printf("] food=[");
    for (int i = PROG_SIZE; i < 2*PROG_SIZE; i++) printf("%d", tape[i]);
    printf("]\n");

    prog_preserved = memcmp(tape, replicator, PROG_SIZE) == 0;
    food_copied = memcmp(tape + PROG_SIZE, replicator, PROG_SIZE) == 0;
    printf("  Program preserved: %s\n", prog_preserved ? "YES" : "NO");
    printf("  Food became copy:  %s\n", food_copied ? "YES" : "NO");

    printf("\n=== Test 3: Replicator + replicator (self-interaction) ===\n");
    memcpy(tape, replicator, PROG_SIZE);
    memcpy(tape + PROG_SIZE, replicator, PROG_SIZE);

    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

    printf("  After:  prog=[");
    for (int i = 0; i < PROG_SIZE; i++) printf("%d", tape[i]);
    printf("] food=[");
    for (int i = PROG_SIZE; i < 2*PROG_SIZE; i++) printf("%d", tape[i]);
    printf("]\n");

    int half1_ok = memcmp(tape, replicator, PROG_SIZE) == 0;
    int half2_ok = memcmp(tape + PROG_SIZE, replicator, PROG_SIZE) == 0;
    printf("  First half preserved:  %s\n", half1_ok ? "YES" : "NO");
    printf("  Second half preserved: %s\n", half2_ok ? "YES" : "NO");

    /* Check what changed */
    if (!half1_ok) {
        printf("  First half diffs: ");
        for (int i = 0; i < PROG_SIZE; i++)
            if (tape[i] != replicator[i])
                printf("[%d: %d->%d] ", i, replicator[i], tape[i]);
        printf("\n");
    }
    if (!half2_ok) {
        printf("  Second half diffs: ");
        for (int i = 0; i < PROG_SIZE; i++)
            if (tape[PROG_SIZE+i] != replicator[i])
                printf("[%d: %d->%d] ", i, replicator[i], tape[PROG_SIZE+i]);
        printf("\n");
    }
}

/* === Soup simulation === */
typedef struct {
    uint8_t *data;
    int N;
    double mu;
    uint8_t *tape;
} Soup;

static Soup *soup_create_seeded(int N, double mu) {
    Soup *s = calloc(1, sizeof(Soup));
    s->N = N;
    s->mu = mu;
    s->data = malloc(N * PROG_SIZE);
    s->tape = malloc(2 * PROG_SIZE);
    uint8_t replicator[PROG_SIZE] = {
        0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,1, 0,0, 0,0
    };
    for (int i = 0; i < N; i++)
        memcpy(s->data + i * PROG_SIZE, replicator, PROG_SIZE);
    return s;
}

static inline uint8_t *prog(Soup *s, int i) {
    return s->data + i * PROG_SIZE;
}

static void soup_epoch(Soup *s) {
    int n_inter = s->N / 2;
    for (int i = 0; i < n_inter; i++) {
        int a = rng_int(s->N);
        int b = rng_int(s->N - 1);
        if (b >= a) b++;

        memcpy(s->tape, prog(s, a), PROG_SIZE);
        memcpy(s->tape + PROG_SIZE, prog(s, b), PROG_SIZE);
        execute_tape(s->tape, 2 * PROG_SIZE, MAX_VM_STEPS);
        memcpy(prog(s, a), s->tape, PROG_SIZE);
        memcpy(prog(s, b), s->tape + PROG_SIZE, PROG_SIZE);
    }

    if (s->mu > 0) {
        int total = s->N * PROG_SIZE;
        int n_mut = (int)(total * s->mu);
        for (int i = 0; i < n_mut; i++) {
            int pos = rng_int(total);
            s->data[pos] = rng_int(Z3);
        }
    }
}

static double measure_density(Soup *s) {
    int count = 0;
    uint8_t tape[2 * PROG_SIZE];

    for (int i = 0; i < s->N; i++) {
        uint8_t *p = prog(s, i);

        int trivial = 1;
        for (int j = 1; j < PROG_SIZE; j++) {
            if (p[j] != p[0]) { trivial = 0; break; }
        }
        if (trivial) continue;

        /* Test with zero food */
        memcpy(tape, p, PROG_SIZE);
        memset(tape + PROG_SIZE, 0, PROG_SIZE);
        execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

        if (memcmp(tape, p, PROG_SIZE) == 0 &&
            memcmp(tape + PROG_SIZE, p, PROG_SIZE) == 0) {
            count++;
            continue;
        }

        /* Test with random food */
        memcpy(tape, p, PROG_SIZE);
        for (int j = 0; j < PROG_SIZE; j++)
            tape[PROG_SIZE + j] = rng_int(Z3);
        execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);

        if (memcmp(tape, p, PROG_SIZE) == 0 &&
            memcmp(tape + PROG_SIZE, p, PROG_SIZE) == 0) {
            count++;
        }
    }
    return (double)count / s->N;
}

/* Count how many tiles exactly match the original replicator */
static double measure_exact_match(Soup *s) {
    uint8_t replicator[PROG_SIZE] = {
        0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,1, 0,0, 0,0
    };
    int count = 0;
    for (int i = 0; i < s->N; i++)
        if (memcmp(prog(s, i), replicator, PROG_SIZE) == 0) count++;
    return (double)count / s->N;
}

/* Count average Hamming distance from original replicator */
static double measure_avg_hamming(Soup *s) {
    uint8_t replicator[PROG_SIZE] = {
        0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,1, 0,0, 0,0
    };
    double sum = 0;
    for (int i = 0; i < s->N; i++) {
        uint8_t *p = prog(s, i);
        int d = 0;
        for (int j = 0; j < PROG_SIZE; j++)
            if (p[j] != replicator[j]) d++;
        sum += d;
    }
    return sum / s->N;
}

int main(void) {
    printf("=== DIAGNOSTIC: Seeded Replicator Behavior ===\n\n");

    test_replicator();

    printf("\n=== Test 4: Epoch-by-epoch density tracking ===\n\n");

    double mu_values[] = {0.0, 0.001, 0.005, 0.01};
    int n_mu = 4;
    int N = 200;

    for (int mi = 0; mi < n_mu; mi++) {
        double mu = mu_values[mi];
        printf("--- mu=%.4f, N=%d ---\n", mu, N);

        rng_seed(42);
        Soup *s = soup_create_seeded(N, mu);

        printf("  %6s  %8s  %8s  %10s  %8s\n",
               "epoch", "rho_rep", "exact_f", "avg_hamm", "n_triv");

        for (int e = 0; e <= 200; e++) {
            if (e == 0 || e <= 10 || (e <= 50 && e % 5 == 0) ||
                (e <= 200 && e % 20 == 0)) {
                double rho = measure_density(s);
                double exact = measure_exact_match(s);
                double hamm = measure_avg_hamming(s);

                /* Count trivial */
                int n_triv = 0;
                for (int i = 0; i < s->N; i++) {
                    int trivial = 1;
                    for (int j = 1; j < PROG_SIZE; j++)
                        if (prog(s, i)[j] != prog(s, i)[0]) { trivial = 0; break; }
                    if (trivial) n_triv++;
                }

                printf("  %6d  %8.4f  %8.4f  %10.2f  %8d\n",
                       e, rho, exact, hamm, n_triv);
            }
            soup_epoch(s);
        }
        printf("\n");
        free(s->data); free(s->tape); free(s);
    }

    return 0;
}
