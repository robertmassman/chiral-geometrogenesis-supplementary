# StellaLang Computational Life: Verification Report

**Date:** 2026-03-06
**Type:** Computational Verification
**Status:** COMPLETE

---

## Summary

Self-replicating programs emerge spontaneously from random ternary interactions
using Chiral Geometrogenesis building blocks. A primordial soup simulation
(adapted from Aguera y Arcas et al., "Computational Life", arXiv:2406.19108)
demonstrates that the CG framework's primitives are sufficient not only for
universal computation but for **computational life** -- self-organizing,
self-replicating structures arising from pure Z_3 interactions with no
fitness landscape.

---

## Experimental Setup

| Parameter | Value |
|-----------|-------|
| Soup size | 4096 programs |
| Program size | 24 trits (12 instruction pairs) |
| Max steps per interaction | 729 (3^6) |
| Mutation rate | 0.001 per trit per epoch |
| Total epochs | 30,000,000 |
| Random seed | 42 |
| Runtime | 61,083 seconds (~17 hours) |
| Implementation | C (soup.c), compiled with -O3 |

### Instruction Set (Soup VM)

The soup VM extends base StellaLang with two heads (h0 for T+, h1 for T-)
and 9 trit-pair instructions:

| Trit Pair | Opcode | Operation | Grounding |
|-----------|--------|-----------|-----------|
| (0,0) | NOP | No operation | -- |
| (0,1) | ROT | tape[h0] = (tape[h0]+1) % 3 | (P) Def 0.1.2 |
| (0,2) | FWD0 | h0 += 1 | (M) advance h0 |
| (1,0) | BCK0 | h0 -= 1 | (M) retreat h0 |
| (1,1) | FWD1 | h1 += 1 | (M) advance h1 |
| (1,2) | OPEN | if tape[h0]==0: skip to ] | (P) Prop 0.0.17h |
| (2,0) | CLOSE | if tape[h0]!=0: jump to [ | (P) Prop 0.0.17h |
| (2,1) | CPY01 | tape[h1] = tape[h0] | (P) Thm 0.2.1 |
| (2,2) | CPY10 | tape[h0] = tape[h1] | (P) Thm 0.2.1 |

(P) = Proof-grounded, (M) = Proof-motivated design choice.

### Interaction Model

Each epoch: N/2 random pairs interact via concatenation-execution-split:

```
Program A (24 trits) + Program B (24 trits)
    -> concatenate into 48-trit tape
    -> execute (h0 at position 0, h1 at position 24)
    -> split: first 24 trits -> A', last 24 trits -> B'
```

---

## Results

### Phase Transition Timeline

| Epoch Range | Unique Programs | Replicators (per 200) | Phase |
|-------------|-----------------|----------------------|-------|
| 0 -- 3.4M | ~3950 / 4096 | 0 perfect, ~90 partial | Random soup |
| 3.5M | 1527 / 4096 | 75 perfect | **Phase transition** |
| 3.5M -- 10.8M | ~900-1400 | ~80-110 perfect | Replicator expansion |
| 11M -- 30M | ~300-420 | ~175-193 perfect | **Steady state** |

### Final State (Epoch 30,000,000)

- **Unique programs:** 418 / 4096 (10.2%)
- **Perfect replicators:** 176 / 200 sampled (88%)
- **Total perfect replicators detected:** 8,416 across all checks
- **Trit entropy:** 1.5209 (max 1.5850) -- non-trivial structure
- **Most common program:** 394 copies (9.6% of soup)

### The Dominant Replicator

All top 5 programs share a conserved 20-trit core with variable 4-trit tail:

```
Core: [1,2, 1,2, 2,1, 0,2, 1,1, 2,0, 2,1, 1,1, 0,2, 2,0]
```

Decoded into instructions:

```
[        Superselection open (outer loop)
[        Superselection open (inner loop)
CPY+     tape[h1] = tape[h0]   -- copy T+ to T-
FWD0     h0++                   -- advance read head
FWD1     h1++                   -- advance write head
]        Superselection close (inner: loop while tape[h0] != 0)
CPY+     tape[h1] = tape[h0]   -- copy the terminating zero
FWD1     h1++                   -- advance write head past zero
FWD0     h0++                   -- advance read head past zero
]        Superselection close (outer: loop while tape[h0] != 0)
```

**Mechanism:** This is a trit-by-trit copy machine. h0 reads from position 0
(the program itself), h1 writes to position 24 (the food half). The inner loop
copies contiguous non-zero runs; the outer loop advances past zeros and
continues. When the tape splits after execution, both halves contain the
program.

**Tail variation:** The last 4 trits (2 instructions) vary across the family.
These are unreachable "junk" after the outer loop exits -- analogous to
non-coding DNA. The replicator's function is entirely in the 20-trit core.

### Top 5 Programs

| Rank | Count | % | Tail (last 4 trits) | Decoded tail |
|------|-------|---|---------------------|-------------|
| 1 | 394 | 9.6% | [2,0, 2,0] | ] ] |
| 2 | 381 | 9.3% | [1,0, 2,1] | BCK0 CPY+ |
| 3 | 256 | 6.2% | [2,0, 2,2] | ] CPY- |
| 4 | 252 | 6.2% | [1,1, 1,2] | FWD1 [ |
| 5 | 203 | 5.0% | [1,1, 2,2] | FWD1 CPY- |

---

## Connection to CG Proofs

### Primary Claims Supported

**1. Prop 0.0.XXb (Bootstrap Computability)**

The emergence of self-replicators from random Z_3 interactions demonstrates
that the CG framework's building blocks are computationally rich enough to
support self-organizing structures. StellaLang is Turing-complete, and the
soup simulation shows this completeness manifests in practice: given enough
interactions, self-replicating fixed points emerge spontaneously.

**2. Thm 0.2.1 (Total Field Superposition) -- T+ to T- Transfer**

The dominant replicator's core mechanism is CPY01: copying information from
h0 (T+ tetrahedron) to h1 (T- tetrahedron). This is the computational analog
of the field superposition theorem -- information transfer between the two
interpenetrating tetrahedra of the stella octangula. The replicator
independently "discovered" that T+ -> T- transfer is the essential operation
for self-replication, mirroring the physical framework's information flow.

**3. Prop 0.0.17h (Z_3 Superselection Gate)**

The replicator uses nested superselection gates ([ and ]) as its control
structure. The gate tests for identity phase (value 0), providing the
conditional branching needed for the copy loop. Without Z_3 superselection,
the copy machine cannot terminate properly.

**4. G11 (Bootstrap & Uniqueness)**

The replicator family represents a computational fixed point: a self-consistent
structure that reproduces itself through interaction. This parallels the
bootstrap mechanism in G11, where the framework's parameters are
self-consistently determined. The convergence to a single dominant replicator
family (with variable junk tail) suggests a form of computational uniqueness.

### Proof Grounding Audit

The replicator uses only these CG-grounded primitives:
- CPY01 (P): Thm 0.2.1 -- the essential replication operation
- [ and ] (P): Prop 0.0.17h -- control flow via superselection
- FWD0, FWD1 (M): pointer advance -- computational primitives

It does NOT use:
- ROT (phase rotation) -- replication doesn't require phase changes
- BCK0 (retreat) -- forward-only head movement suffices
- CPY10 (T- -> T+) -- information flows one way: T+ to T-

The one-directional information flow (T+ -> T- only) is consistent with
the chirality selection of Thm 2.2.4 and the arrow of time (Prop 0.0.17c).

---

## Comparison with BFF (Aguera y Arcas et al., 2024)

| Aspect | BFF | Stella Soup |
|--------|-----|-------------|
| Cell size | 256 (byte) | 3 (trit) |
| Instructions | ~20 | 9 |
| Tape heads | 2 | 2 (T+, T-) |
| Program size | 64 bytes | 24 trits (12 instr) |
| Soup size | 4096+ | 4096 |
| Replicator emergence | ~millions of epochs | ~3.5M epochs |
| Replicator mechanism | Copy loop | Copy loop |
| Grounded in physics | No | Yes (CG proofs) |

The qualitative dynamics match: random soup -> partial replicators -> phase
transition -> dominant replicator family with junk variation. The key
difference is that Stella Soup's primitives are derived from (or motivated by)
physical theorems, not arbitrary engineering choices.

---

## Reproducibility

```bash
cd stella_lang
cc -O3 -o stella_soup soup.c -lm
./stella_soup --epochs 30000000 --seed 42 \
    --log-interval 100000 --check-interval 500000 \
    2>&1 | tee soup_30M_results.txt
```

Full output: `stella_lang/soup_30M_results.txt`

---

## Files

| File | Description |
|------|-------------|
| `stella_lang/soup.c` | C implementation (production) |
| `stella_lang/soup.py` | Python implementation (reference) |
| `stella_lang/spec.md` | StellaLang specification (v1.1) |
| `stella_lang/interpreter.py` | Base StellaLang interpreter |
| `stella_lang/test_interpreter.py` | Test suite (23 tests) |
| `stella_lang/examples.py` | Example programs |
| `stella_lang/soup_30M_results.txt` | Full 30M epoch output |

---

## References

1. Aguera y Arcas, B. et al. (2024). "Computational Life: How Well-formed,
   Self-replicating Programs Emerge from Simple Interaction." arXiv:2406.19108.
2. Definition 0.1.1: Stella Octangula Boundary Topology
3. Definition 0.1.2: Three Color Fields and Relative Phases
4. Theorem 0.2.1: Total Field Superposition
5. Proposition 0.0.17h: Information Horizon Derivation
6. Proposition 0.0.17c: Arrow of Time from Information Geometry
7. Proposition 0.0.XXb: Bootstrap Computability
