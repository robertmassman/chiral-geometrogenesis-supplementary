# Stella Soup 30M Epoch Results

**Date:** 2026-03-06 | **Seed:** 42 | **Runtime:** ~17 hours

## Key Finding

Self-replicating programs emerge at epoch ~3.5M from random Z_3 interactions.
By epoch 11M, ~88% of the soup consists of perfect self-replicators.

## The Dominant Replicator (20-trit conserved core)

```
Trits: [1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0]

Decoded:
  [  [  CPY+  FWD0  FWD1  ]  CPY+  FWD1  FWD0  ]

Pseudocode:
  while tape[h0] != 0:         # outer loop
      while tape[h0] != 0:     # inner loop
          tape[h1] = tape[h0]  # copy T+ -> T-
          h0++; h1++            # advance both heads
      tape[h1] = tape[h0]      # copy the zero
      h1++; h0++                # skip past zero
```

A copy machine that reads from h0 (T+) and writes to h1 (T-).
Last 4 trits are unreachable junk -- varies across the family (5 variants).

## CG Primitives Used by the Replicator

| Primitive | CG Proof | Role in Replicator |
|-----------|----------|-------------------|
| CPY01 | Thm 0.2.1 (T+ -> T- transfer) | **Core mechanism** -- copies program |
| [ ] | Prop 0.0.17h (superselection) | Loop control for copy |
| FWD0, FWD1 | Computational primitive | Advance read/write heads |

NOT used: ROT, BCK0, CPY10. The replicator is forward-only, copy-only.

## Reproduce

```bash
cc -O3 -o stella_soup soup.c -lm
./stella_soup --epochs 30000000 --seed 42 --log-interval 100000 --check-interval 500000
```

Full output: `soup_30M_results.txt`
Verification report: `docs/proofs/verification-records/StellaLang-Computational-Life-Verification-2026-03-06.md`
