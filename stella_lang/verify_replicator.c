/*
 * Quick test: verify which programs from the 30M run are actual replicators.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define Z3 3
#define MAX_VM_STEPS 729
#define PROG_SIZE 24

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

static void test_prog(const char *label, uint8_t *prog) {
    uint8_t tape[2 * PROG_SIZE];
    static const char *names[] = {
        "NOP", "ROT", "FWD0", "BCK0", "FWD1", "[", "]", "CPY+", "CPY-"
    };

    printf("--- %s ---\n  Trits: [", label);
    for (int i = 0; i < PROG_SIZE; i++) printf("%d%s", prog[i], i<PROG_SIZE-1?",":"");
    printf("]\n  Ops:   ");
    for (int i = 0; i+1 < PROG_SIZE; i += 2)
        printf("%s ", names[prog[i]*3+prog[i+1]]);
    printf("\n");

    /* Test with zero food */
    memcpy(tape, prog, PROG_SIZE);
    memset(tape + PROG_SIZE, 0, PROG_SIZE);
    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);
    int preserved_zero = memcmp(tape, prog, PROG_SIZE) == 0;
    int copied_zero = memcmp(tape + PROG_SIZE, prog, PROG_SIZE) == 0;
    printf("  Zero food:   self=%s copy=%s\n",
           preserved_zero ? "YES" : "no", copied_zero ? "YES" : "no");

    /* Test with random food (all 1s) */
    memcpy(tape, prog, PROG_SIZE);
    memset(tape + PROG_SIZE, 1, PROG_SIZE);
    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);
    int preserved_ones = memcmp(tape, prog, PROG_SIZE) == 0;
    int copied_ones = memcmp(tape + PROG_SIZE, prog, PROG_SIZE) == 0;
    printf("  Ones food:   self=%s copy=%s\n",
           preserved_ones ? "YES" : "no", copied_ones ? "YES" : "no");

    /* Test with random food (all 2s) */
    memcpy(tape, prog, PROG_SIZE);
    memset(tape + PROG_SIZE, 2, PROG_SIZE);
    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);
    int preserved_twos = memcmp(tape, prog, PROG_SIZE) == 0;
    int copied_twos = memcmp(tape + PROG_SIZE, prog, PROG_SIZE) == 0;
    printf("  Twos food:   self=%s copy=%s\n",
           preserved_twos ? "YES" : "no", copied_twos ? "YES" : "no");

    /* Test self-interaction */
    memcpy(tape, prog, PROG_SIZE);
    memcpy(tape + PROG_SIZE, prog, PROG_SIZE);
    execute_tape(tape, 2 * PROG_SIZE, MAX_VM_STEPS);
    int self1 = memcmp(tape, prog, PROG_SIZE) == 0;
    int self2 = memcmp(tape + PROG_SIZE, prog, PROG_SIZE) == 0;
    printf("  Self-inter:  half1=%s half2=%s\n",
           self1 ? "YES" : "no", self2 ? "YES" : "no");

    int is_replicator = (preserved_zero && copied_zero) ||
                         (preserved_ones && copied_ones) ||
                         (preserved_twos && copied_twos);
    printf("  REPLICATOR: %s\n\n", is_replicator ? "YES" : "NO");
}

int main(void) {
    printf("=== Verifying replicators from 30M-epoch run ===\n\n");

    /* Top 5 from soup_30M_results.txt */
    uint8_t p1[PROG_SIZE] = {1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 2,0, 2,0};
    uint8_t p2[PROG_SIZE] = {1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 1,0, 2,1};
    uint8_t p3[PROG_SIZE] = {1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 2,0, 2,2};
    uint8_t p4[PROG_SIZE] = {1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 1,1, 1,2};
    uint8_t p5[PROG_SIZE] = {1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0, 1,1, 2,2};

    /* The WRONG replicator from the workplan */
    uint8_t wrong[PROG_SIZE] = {0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,2, 2,1, 1,1, 0,1, 0,0, 0,0};

    test_prog("Top-1 (394 copies)", p1);
    test_prog("Top-2 (381 copies)", p2);
    test_prog("Top-3 (256 copies)", p3);
    test_prog("Top-4 (252 copies)", p4);
    test_prog("Top-5 (203 copies)", p5);
    test_prog("WRONG (workplan)", wrong);

    return 0;
}
