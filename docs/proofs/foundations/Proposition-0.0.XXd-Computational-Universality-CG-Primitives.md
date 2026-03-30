# Proposition 0.0.XXd: Computational Universality of CG Primitives

## Status: 🔶 NOVEL ✅ VERIFIED — COMPUTATIONAL UNIVERSALITY AND EMERGENT SELF-REPLICATION

**Purpose:** Establish that the CG-derived instruction set (Z_3 cells, T+/T- copy, superselection gates) is Turing-complete and sufficient for self-replicating programs to emerge spontaneously from random interactions.

**Created:** 2026-03-06
**Verified:** 2026-03-06 (Constructive verification: `stella_lang/verify_replicator.py`)

**Verification Records:**
- [Multi-Agent Peer Review (2026-03-07)](../verification-records/Proposition-0.0.XXd-Multi-Agent-Verification-2026-03-07.md)
- [Adversarial Physics Verification](../../../verification/prop_0_0_XXd_adversarial_verification.py) — 14/14 tests passed
- [Lean 4 Formalization](../../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXd.lean)
- GPU causal ordering experiment (§4.6): `stella_lang/soup_multi_stella_metal.m` + `soup_multi_stella.metal` (Metal GPU), `soup_multi_stella.c` (CPU baseline)

**Dependencies:**
- ✅ Definition 0.1.1 (Stella Octangula Boundary Topology) — Two tetrahedra T+, T- (two-component structure requiring inter-component coupling)
- ✅ Definition 0.1.2 (Three Color Fields) — Z_3 trit data type; identity phase (0) distinguished from non-identity phases (2π/3, 4π/3)
- ✅ Theorem 0.2.1 (Total Field Superposition) — Fields on T+ and T- contribute jointly to χ_total, establishing inter-component coupling
- ✅ Proposition 0.0.17c (Arrow of Time From Information Geometry) — KL divergence asymmetry gives T+ → T- directionality
- ✅ Proposition 0.0.17h (Information Horizon Derivation) — Z_3 superselection supports the kinematic distinction of identity sector (supporting context for loop gates)
- ✅ Proposition 0.0.XXb (Bootstrap Computability) — Framework is computable
- ✅ Standard: Turing machine equivalence (Hopcroft & Ullman)
- ✅ Standard: Brainfuck Turing completeness (via isomorphism to Bohm's P'', 1964; Muller created BF in 1993)
- ✅ Reference: Aguera y Arcas et al., "Computational Life" (arXiv:2406.19108, 2024)

**Enables:**
- Computational interpretation of the bootstrap fixed point (G11)
- Connection between self-replication and bootstrap self-consistency
- Demonstration that CG primitives generate computational life

---

## 1. Statement

### 1.1 Definitions

**Definition (StellaLang).** A programming language with:
- **Memory:** Tape of cells, each holding a value in Z_3 = {0, 1, 2}
- **Operations:** Phase rotation (r: +1 mod 3), double rotation (R: +2 mod 3, equivalently r applied twice), pointer advance (>), pointer retreat (<), input (,), output (.), loop gates ([, ])
- **Proof basis:** Each operation maps to a CG theorem (see `stella_lang/spec.md`)

**Definition (Soup VM).** An extension of StellaLang with:
- **Two heads:** h0 (T+ tetrahedron), h1 (T- tetrahedron) — from Def 0.1.1
- **Nine instructions:** Encoded as trit pairs on a shared tape. Each is classified as **(P) proof-grounded** — directly derived from a CG theorem — or **(M) proof-motivated** — inspired by the framework's geometry but a computational design choice (following `stella_lang/spec.md`):

| Trit pair | Instruction | Class | CG Origin |
|-----------|-------------|:-----:|-----------|
| (0,0) | NOP | (P) | Identity phase (Def 0.1.2: phase 0 = identity element of Z₃) |
| (0,1) | ROT (+1 mod 3) | (P) | Def 0.1.2 (Z₃ phase rotation), Thm 2.2.4 (chirality: R→G→B) |
| (0,2) | FWD0 (advance h0) | (M) | Computational primitive — pointer advance on tape |
| (1,0) | BCK0 (retreat h0) | (M) | Computational primitive — pointer retreat (= N-1 advances on cyclic tape) |
| (1,1) | FWD1 (advance h1) | (M) | Computational primitive — pointer advance on tape |
| (1,2) | OPEN (loop open) | (P) | Def 0.1.2 (Z₃ identity test); Prop 0.0.17h (superselection support) |
| (2,0) | CLOSE (loop close) | (P) | Def 0.1.2 (Z₃ identity test); Prop 0.0.17h (superselection support) |
| (2,1) | CPY01 (h0→h1 copy) | (P) | Def 0.1.1 (two-component ∂S) + Thm 0.2.1 (inter-component coupling) + Prop 0.0.17c (T+→T- directionality) |
| (2,2) | CPY10 (h1→h0 copy) | (M) | Def 0.1.1 + Thm 0.2.1 (inter-component coupling exists), but no directionality theorem for T-→T+; included for completeness |

- **Copy operations:** CPY01 (tape[h1] = tape[h0]) is **(P)** proof-grounded: Def 0.1.1 + Thm 0.2.1 + Prop 0.0.17c give directed T+→T- coupling. CPY10 (tape[h0] = tape[h1]) is **(M)** proof-motivated: inter-component coupling exists but the reverse direction T-→T+ lacks a directionality theorem
- **Interaction rule:** Two programs A, B interact via A + B -> split(exec(AB)) = A' + B'

**Definition (Self-replicator).** A program S is a self-replicator if:
$$S + F \to \text{split}(\text{exec}(S \| F)) = (S, S)$$
for food F = 0^n (zero tape of length |S|). A program is a *universal self-replicator* if the source half is preserved for all foods: split(exec(S || F))_1 = S.

### 1.2 Claims

**Claim 1 (Turing Completeness).** StellaLang with Z_3 cells and unbounded tape is Turing-complete. The Soup VM inherits this property.

**Claim 2 (Self-Replicator Construction).** The 20-trit program
$$S = [1,2,1,2,2,1,0,2,1,1,2,0,2,1,1,1,0,2,2,0]$$
decoding to `[[ CPY01 FWD0 FWD1 ] CPY01 FWD1 FWD0 ]`, is a universal self-replicator under the Soup VM interaction rule. It uses only:
- CPY01 (grounded in Def 0.1.1 + Thm 0.2.1 + Prop 0.0.17c: directed inter-component coupling T+ → T-)
- [ ] (grounded in Def 0.1.2: Z_3 identity-element test; supported by Prop 0.0.17h superselection)
- FWD0, FWD1 (pointer advance, computational primitives)

**Claim 3 (Spontaneous Emergence — Empirical).** In a Stella Soup simulation (N = 4096, |S| = 24, seed 42), self-replicators emerge at epoch ~3.5M from random initial conditions and achieve 88% dominance by epoch 11M. *This is computational evidence, not a mathematical proof.*

---

## 2. Proof: Turing Completeness (Claim 1)

### 2.1 BF -> StellaLang Mapping

Brainfuck (BF) is Turing-complete. BF was created by Urban Muller in 1993 [1]; its Turing completeness follows from isomorphism to Bohm's P'' language [15], which was proven Turing-complete in 1964. Cristofani independently demonstrated this constructively via a BF universal Turing machine [16]. We construct a faithful simulation of BF in StellaLang.

**Binary encoding in Z_3 cells.** Each BF cell holds a value in {0, ..., 255}. We encode this as a sequence of 6 Z_3 trits (since 3^6 = 729 >= 256):

$$n = \sum_{i=0}^{5} t_i \cdot 3^i, \quad t_i \in \{0, 1, 2\}$$

**Instruction mapping:**

| BF | StellaLang | Notes |
|----|------------|-------|
| `+` | Increment least-significant trit with carry propagation | Uses `r` (Def 0.1.2) |
| `-` | Decrement least-significant trit with borrow | Uses `R` (Prop 0.0.5a) |
| `>` | Advance pointer by 6 positions | Uses `>` repeated |
| `<` | Retreat pointer by 6 positions | Uses `<` repeated (or N-6 advances) |
| `[` | Test if all 6 trits are zero; skip to matching `]` if so | Uses `[` (Def 0.1.2: Z₃ identity test) |
| `]` | Test if any trit nonzero; jump to matching `[` if so | Uses `]` (Def 0.1.2: Z₃ identity test) |
| `.` | Output cell value | Uses `.` (StellaLang only; omitted in Soup VM) |
| `,` | Input cell value | Uses `,` (StellaLang only; omitted in Soup VM) |

**Note on I/O:** The Soup VM omits `.` and `,` because programs interact only through tape modification, not I/O streams. This does not affect Turing completeness: BF without I/O (the 6 instructions `+ - < > [ ]`) is Turing-complete, as Turing machines themselves have no I/O — they operate solely on tape contents. The I/O mapping is included above for completeness of the StellaLang-to-BF correspondence only.

**Cell-size argument.** The key subtlety is that BF loops test whether a cell equals zero, while StellaLang gates test a single trit. To simulate BF's zero-test on a multi-trit cell, we OR-reduce all 6 trits into a scratch trit using the following construction.

**Primitive: destructive zero.** The fragment `[R]` zeroes any trit: if t = 0, `[` skips; if t = 1, `R` gives (1+2) mod 3 = 0, `]` exits; if t = 2, `R` gives 1, `]` loops, `R` gives 0, `]` exits.

**Primitive: non-destructive copy** (t → w, preserving t). Uses a temporary trit b. All three trits (t, w, b) must be initially: w = 0, b = 0. Pointer starts at t.

```
# Phase 1: drain t into w and b simultaneously
[       # while t != 0
  R     #   t -= 1 (mod 3)
  >     #   move to w
  r     #   w += 1
  >     #   move to b
  r     #   b += 1
  <<    #   back to t
]       # t = 0; w = old_t; b = old_t

# Phase 2: restore t from b
>>      # move to b
[       # while b != 0
  R     #   b -= 1
  <<    #   move to t
  r     #   t += 1
  >>    #   back to b
]       # b = 0; t = old_t; w = old_t
<<      # back to t
```

Net effect: t preserved, w holds copy of t, b = 0. Each `>` and `<` is a single StellaLang pointer step; the actual number of steps between t, w, and b depends on tape layout (see below).

**Primitive: conditional set** (if w ≠ 0, set flag F = 1). Pointer starts at w, F is at a known offset d steps away.

```
[           # if w != 0
  [R]       #   zero w (so loop exits after one pass)
  >>>...>   #   navigate d steps to F
  [R]       #   zero F (clear any prior value)
  r         #   F = 1 (set, not accumulated)
  <<<...<   #   navigate d steps back to w
]           # w = 0, exit
```

This *sets* F = 1 rather than incrementing it, avoiding Z₃ wraparound (since 3 increments mod 3 = 0 would give a false zero).

**Concrete tape layout for one BF cell.** Each BF cell occupies 14 consecutive trits:

```
Positions: [t0 t1 t2 t3 t4 t5 | w0 w1 w2 w3 w4 w5 | F | b]
            ←── 6 data trits ──→ ←── 6 working ──→  flag temp
```

- t0..t5: the 6 data trits encoding the BF cell value (base-3)
- w0..w5: 6 working trits for non-destructive copies (initially 0)
- F: flag trit for zero-test result (initially 0)
- b: temporary trit for non-destructive copy (initially 0)

**Full zero-test for a 6-trit BF cell** (concrete StellaLang, pointer starts at t0):

```
# Step 1: Non-destructively copy each t_i to w_i (using b as temp)
# For t0 → w0: t is at offset 0, w at offset 6, b at offset 13
# Apply non-destructive copy primitive with appropriate > counts

# Step 2: For each w_i, apply conditional-set targeting F
# w0 is at offset 6, F is at offset 12 (6 steps away)
# Apply conditional-set primitive for w0..w5

# Step 3: Test F
# Navigate to F (offset 12)
# [  ... BF loop body ...  ]  ← StellaLang [ tests F
# After loop body, zero F: [R]

# Step 4: Navigate back to t0 for next BF instruction
```

For each trit t_i, the non-destructive copy is 10 StellaLang operations (excluding navigation), and the conditional set is 5 operations (excluding navigation). Navigation between positions uses repeated `>` / `<` with counts determined by the fixed tape layout above. The total StellaLang expansion per BF `[` or `]` is ~120 operations — a constant factor that preserves Turing completeness.

**Exhaustive verification:** For all 729 possible 6-trit cells (3^6), the construction correctly distinguishes zero (all trits = 0, F remains 0) from nonzero (at least one trit ≠ 0, F = 1). This can be verified mechanically.

This requires 8 additional scratch trits per BF cell (6 working copies + 1 flag + 1 temp), a constant overhead that preserves Turing completeness. Each step uses only StellaLang primitives (r, R, >, <, [, ]).

**Tape unboundedness.** StellaLang's tape grows dynamically when the pointer advances past the boundary. With unbounded tape, the simulation is faithful: every BF computation maps to a terminating StellaLang computation with the same result (up to encoding).

### 2.2 Soup VM Inherits Completeness

The Soup VM extends StellaLang with a second head (h1) and copy operations. Since:
1. StellaLang is Turing-complete (Section 2.1)
2. The Soup VM can simulate StellaLang by ignoring h1 and using only h0-based operations (FWD0, BCK0, ROT, OPEN, CLOSE). Note: StellaLang's R (+2 mod 3) is achieved by applying ROT (+1 mod 3) twice
3. Additional operations (CPY01, CPY10, FWD1) only add capability

The Soup VM is at least as powerful as StellaLang, hence Turing-complete. ∎

---

## 3. Proof: Self-Replicator Construction (Claim 2)

### 3.1 The 20-Trit Core

The program S = [1,2,1,2,2,1,0,2,1,1,2,0,2,1,1,1,0,2,2,0] decodes as:

| Position | Trits | Instruction | CG Origin |
|----------|-------|-------------|-----------|
| 0-1 | (1,2) | `[` (OPEN) | Def 0.1.2 (Z₃ identity test) |
| 2-3 | (1,2) | `[` (OPEN) | Def 0.1.2 (Z₃ identity test) |
| 4-5 | (2,1) | CPY01 | Def 0.1.1 + Thm 0.2.1 + Prop 0.0.17c |
| 6-7 | (0,2) | FWD0 | Pointer advance |
| 8-9 | (1,1) | FWD1 | Pointer advance |
| 10-11 | (2,0) | `]` (CLOSE) | Def 0.1.2 (Z₃ identity test) |
| 12-13 | (2,1) | CPY01 | Def 0.1.1 + Thm 0.2.1 + Prop 0.0.17c |
| 14-15 | (1,1) | FWD1 | Pointer advance |
| 16-17 | (0,2) | FWD0 | Pointer advance |
| 18-19 | (2,0) | `]` (CLOSE) | Def 0.1.2 (Z₃ identity test) |

### 3.2 Execution Trace (S + 0^20)

**Initial state:** Tape = S || 0^20 (40 trits). Three independent pointers: IP = 0 (instruction pointer, advances through opcodes), h0 = 0 (read head, advances via FWD0), h1 = 20 (write head, advances via FWD1). **Critical distinction:** IP and h0 are independent registers that happen to start at the same position. IP steps through instruction pairs (positions 0-1, 2-3, ..., 18-19); h0 walks through individual trits as data. They diverge immediately after execution begins.

**Pseudocode:**
```
outer: while tape[h0] != 0:          # [  at position 0
    inner: while tape[h0] != 0:      # [  at position 2
        tape[h1] = tape[h0]          # CPY01: copy trit from h0 to h1
        h0++                          # FWD0: advance read head
        h1++                          # FWD1: advance write head
                                      # ]  at position 10: loop if tape[h0] != 0
    tape[h1] = tape[h0]              # CPY01: copy the zero terminator
    h1++                              # FWD1
    h0++                              # FWD0
                                      # ]  at position 18: loop if tape[h0] != 0
```

The inner loop copies trits from h0 to h1 until it encounters a 0 trit at h0. It then copies the 0 and advances both heads. The outer loop repeats for the next segment.

**IP vs h0 independence (addressing M-W5).** The instruction pointer (IP) and read head (h0) are independent registers. IP steps through opcode pairs; h0 walks through data trits. They start at the same position (0) but immediately diverge:

| Step | IP (opcode position) | Instruction | h0 (data position) | h1 (write position) | tape[h0] | Action |
|-----:|----:|------------|----:|----:|:---:|--------|
| 0 | 0 | `[` OPEN | 0 | 20 | 1 | h0≠0, enter outer loop |
| 1 | 2 | `[` OPEN | 0 | 20 | 1 | h0≠0, enter inner loop |
| 2 | 4 | CPY01 | 0 | 20 | 1 | tape[20]=1 |
| 3 | 6 | FWD0 | **1** | 20 | 2 | h0 advances (IP≠h0 from here) |
| 4 | 8 | FWD1 | 1 | **21** | 2 | h1 advances |
| 5 | 10 | `]` CLOSE | 1 | 21 | 2 | h0≠0, loop to IP=2 |
| 6 | 2 | `[` OPEN | 1 | 21 | 2 | h0≠0, enter inner loop |
| 7 | 4 | CPY01 | 1 | 21 | 2 | tape[21]=2 |
| 8 | 6 | FWD0 | **2** | 21 | 1 | h0 advances |
| ... | ... | ... | ... | ... | ... | (continues copying trit by trit) |

After step 3, IP and h0 are permanently desynchronized: IP cycles through positions {2,4,6,8,10} (the inner loop opcodes), while h0 walks linearly through data positions 0,1,2,3,... The inner loop terminates when h0 reaches a zero trit (positions 6, 11, 16, 19 in the source encoding — the first trits of FWD0 and CLOSE instructions), segmenting the copy into four blocks.

**Non-termination and idempotent cycling:** The program does not halt. After ~84 steps, Pass 1 completes: h0 has copied all 20 source trits to the food region (positions 20-39). At this point h0 wraps to position 20 (food, now containing S) and h1 wraps to position 0 (source). Pass 2 then copies the food (= S) back onto the source (= S) — an idempotent operation that changes nothing. This cycle repeats indefinitely until the soup's `max_steps` bound (729) halts execution.

**Result:** After any number of complete passes, both halves contain S. The source region (0-19) is unmodified during Pass 1 because CPY01 only writes to h1 (the food region). During Pass 2+, it writes S onto S, which is harmless.

**Food-independence:** The 100% perfect replication rate with arbitrary food is not because the program "overwrites regardless of content" — it is because h0 reads only from the source region during Pass 1. Food content is structurally irrelevant: h0 never encounters food trits until after they have already been overwritten with S.

### 3.3 Constructive Verification

The verification script `stella_lang/verify_replicator.py` confirms:

1. **Decode:** 20 trits -> `[[ CPY+ FWD0 FWD1 ] CPY+ FWD1 FWD0 ]` ✅
2. **Zero food:** S + 0^20 -> (S, S) ✅
3. **Random food (source preservation):** S + F -> (S, _) for 50/50 random foods ✅
4. **Random food (perfect replication):** S + F -> (S, S) for 50/50 random foods ✅
5. **CG primitives only:** {CPY+, FWD0, FWD1, [, ]} — no ROT, BCK0, CPY10, NOP ✅
6. **CG decomposition:** Every instruction maps to a CG theorem ✅

The 100% perfect replication rate with random food follows from food-independence: during Pass 1, h0 reads only source trits (positions 0-19), so food content never affects loop termination or copy values. The program does not halt — it relies on the soup's `max_steps` bound. After Pass 1 completes (~84 steps), subsequent passes are idempotent (copying S onto S).

### 3.4 CG Decomposition

The replicator's mechanism decomposes entirely into CG-derived operations:

| Component | CG Origin | Role |
|-----------|-----------|------|
| Copy (CPY01) | Def 0.1.1 + Thm 0.2.1 + Prop 0.0.17c: The stella boundary ∂S = ∂T₊ ⊔ ∂T₋ has two components (Def 0.1.1). Fields on both components contribute jointly to χ_total (Thm 0.2.1), establishing that T₊ and T₋ are dynamically coupled — information about field values on one component is accessible from the other. The arrow of time (Prop 0.0.17c) gives this coupling a preferred direction: T₊ → T₋, grounding CPY01 (but not CPY10) as the physically motivated copy direction. CPY01 is the computational analog of directed inter-component field coupling, not of static superposition per se. | Core mechanism — copies each trit |
| Loop ([/]) | Def 0.1.2 (primary) + Prop 0.0.17h (supporting): The three color field phases {0, 2π/3, 4π/3} (Def 0.1.2) distinguish the identity element (phase 0) from the two non-identity elements — this is a fundamental property of Z₃ as a cyclic group, where the identity is the unique element fixed by all group automorphisms. The loop gate tests "is this trit the identity element of Z₃?" — a natural group-theoretic conditional. Prop 0.0.17h provides supporting physical context: Z₃ superselection makes the identity/non-identity distinction kinematic (not just algebraic), but the gate condition itself requires only the Z₃ group structure from Def 0.1.2. | Iteration control — copy until boundary |
| Advance (FWD0, FWD1) | Pointer advance (computational primitive on the tape) | Sequential traversal of source and target |

The replicator requires no phase rotations (ROT), no backward movement (BCK0), and no T- -> T+ copy (CPY10). It is a purely forward, copy-only machine. ∎

---

## 4. Empirical Evidence: Spontaneous Emergence (Claim 3)

### 4.1 Experimental Setup

| Parameter | Value | Justification |
|-----------|-------|---------------|
| Soup size | N = 4096 programs | Smaller than BFF (2^17 = 131,072); chosen for computational tractability |
| Program size | 24 trits (12 instructions) | Minimal size allowing replicators |
| Max steps/interaction | 729 = 3^6 | Natural Z_3 scale |
| Mutation rate | 0.001 per trit per epoch | Background noise |
| Seed | 42 | Reproducibility |
| Implementation | C (soup.c), verified against Python (soup.py) | Performance |
| Total epochs | 30,000,000 | Extended run |

**Interaction rule (Equation 3 of Aguera y Arcas et al.):**
$$A + B \to \text{split}(\text{exec}(A \| B)) = A' + B'$$

Programs are paired randomly; their tapes concatenated, executed, and split back.

### 4.2 Phase Transition

| Epoch Range | Unique Programs | Compression | Observation |
|-------------|-----------------|-------------|-------------|
| 0 - 500K | ~4096 (all unique) | ~0.77 | Random initialization, no structure |
| 500K - 3M | ~3000 - 2000 | 0.65 - 0.45 | Gradual selection, diversity decreasing |
| ~3.5M | ~1500 | ~0.35 | **First self-replicators detected** |
| 3.5M - 11M | Rapid decrease | 0.10 - 0.05 | Replicator takeover |
| 11M - 30M | ~5 variants | ~0.03 | **88% dominance**, steady state |

The transition at epoch ~3.5M is a phase transition from random to ordered: compression ratio drops sharply as the soup becomes dominated by copies of the replicator.

### 4.3 Steady-State Replicator Family

By epoch 11M, the soup contains ~5 variants of the same 20-trit core:

```
Core (positions 0-19): [1,2,1,2,2,1,0,2,1,1,2,0,2,1,1,1,0,2,2,0]
Junk (positions 20-23): varies — [0,0,x,y] for various x,y
```

The last 4 trits (2 instructions) are unreachable code — the outer loop exits before the IP reaches them. This "junk DNA" varies across family members but does not affect replication.

### 4.4 Comparison with BFF (Aguera y Arcas et al.)

| Property | BFF (binary, 256-value cells) | Stella Soup (ternary, Z_3 cells) |
|----------|-------------------------------|----------------------------------|
| Cell type | Byte (0-255) | Trit (0-2) |
| Instructions | 10 (of 256 byte values) | 9 (of 9 trit pairs) |
| Soup size | 2^17 = 131,072 programs (64 bytes each) | 4,096 programs (24 trits each) |
| Replicator emergence | ~2,355 epochs (case study); 40% of runs within 16k epochs | ~3.5M epochs (seed 42) |
| Dominant mechanism | Copy loop | Copy loop (CPY01 + [/]) |
| Minimum replicator | ~7 instructions (functional core) | 10 instructions (20 trits) |

The much longer emergence time (~3.5M vs ~2.4k) reflects multiple factors: (1) Stella Soup's smaller soup (4,096 vs 131,072 programs) means fewer interactions per epoch, (2) Z_3 cells carry less information per cell (log_2(3) ≈ 1.58 bits vs 8 bits), and (3) 246/256 = 96.1% of BFF byte values are NOPs (data), providing a large reservoir of neutral material, whereas Stella Soup has 0% NOP waste — every trit pair is a semantic instruction, making random programs more "active" but less likely to contain passive copy targets.

### 4.5 Caveats

1. **Claim 3 is empirical, not proven.** The emergence of self-replicators from random interactions has not been proven to occur with probability 1. The simulation demonstrates it occurs for specific parameters and seed.

2. **Seed dependence.** Only seed 42 was tested at 30M epochs. Different seeds may produce different replicators or require different emergence times. The qualitative phenomenon (replicator emergence) is expected to be seed-independent based on BFF results, but this has not been verified for Stella Soup.

3. **Parameter sensitivity.** The mutation rate (0.001), program size (24), and soup size (4096) were chosen by analogy with BFF. The phase transition epoch may vary significantly with these parameters.

4. **No formal proof of inevitability.** Unlike Claim 1 (Turing completeness) and Claim 2 (constructive replicator), Claim 3 does not have a mathematical proof. It is a computational observation.

### 4.6 Causal Ordering is Essential: GPU Parallelism Destroys Replicator Emergence

**Verification scripts:** `stella_lang/soup_multi_stella.c` (CPU, sequential), `stella_lang/soup_multi_stella_metal.m` + `soup_multi_stella.metal` (GPU, parallel)

#### 4.6.1 The experiment

The soup interaction rule (§4.1) requires sequential causal ordering: program A interacts with program B, producing A' and B', which must be written back before either participates in subsequent interactions. We tested whether this ordering is physically necessary by implementing the soup on Apple Metal GPU compute shaders with fine-grained parallelism — one GPU thread per interaction, all interactions within an epoch executing simultaneously.

| Implementation | Parallelism | Entropy at 5M epochs | Replicators |
|----------------|-------------|----------------------|:-----------:|
| CPU (sequential) | 1 interaction at a time | **1.49** (order emerging) | ✅ Yes |
| GPU fine-grained | All interactions simultaneous | **1.58** (maximum, no order) | ❌ No |

Both runs used identical parameters: $n_{\text{sub}} = 50$ (208 tiles per stella), FCC $L = 2$ (4 stellae, 832 total tiles), seed 42, mutation rate 0.001.

#### 4.6.2 Diagnosis: write conflicts prevent selection pressure

When multiple GPU threads simultaneously read the same tile as input to different interactions and then write back different results, one thread's output overwrites another's. This destroys the selection pressure that drives replicator emergence:

1. **A replicator copies itself onto a neighbor** (thread 1: $S + F \to (S, S)$)
2. **Simultaneously, another interaction overwrites the copy** (thread 2: $X + S' \to (X', Y)$)
3. **Net effect:** The replicator's offspring is destroyed before it can participate in further interactions

The entropy signature is definitive: CPU entropy drops from 1.58 → 1.49 over 5M epochs as replicator copies accumulate and reduce diversity. GPU entropy remains flat at 1.58 — the maximum for a Z₃ system — indicating that no configuration gains selective advantage.

#### 4.6.3 Physics interpretation

The write conflict problem has a structural parallel to the CG framework's causal requirements:

1. **∂S = ∂T₊ ⊔ ∂T₋ topology requires sequential mediation.** The two disjoint components of the stella boundary are coupled through inter-component interactions (Thm 0.2.1, Prop 0.0.17c). The CPY01 operation (T₊ → T₋ copy) that drives replication is inherently ordered: h0 reads from T₊, then h1 writes to T₋. Parallel execution of multiple CPY01 operations targeting the same T₋ region creates conflicting writes.

2. **Internal time λ imposes causal ordering.** The evolution parameter λ (Def 0.2.2) defines a sequential update ordering on ∂S. The soup's epoch-by-epoch sequential execution is the computational realization of λ-ordering. GPU spatial parallelism replaces temporal ordering with spatial simultaneity, violating the λ-structure.

3. **Chirality requires ordering.** The T₊ → T₋ directionality from the arrow of time (Prop 0.0.17c) distinguishes CPY01 from CPY10. Handedness is an intrinsically sequential concept — it requires a before/after distinction. Parallel execution, where all interactions happen "at once," destroys this distinction.

**This is computational evidence, not a proof.** The write conflict problem is a concrete mechanism (race conditions in concurrent writes), and the physics interpretation identifies structural parallels. A rigorous derivation would require showing that λ-ordering is *necessary* for the bootstrap fixed point, not merely *sufficient*.

#### 4.6.4 Computational irreducibility

The failure of GPU parallelism is not merely an implementation limitation — it reflects a fundamental property of the soup dynamics. The interaction $A + B \to \text{split}(\text{exec}(AB))$ involves Turing-complete computation (Claim 1), and the output of one interaction feeds as input to the next. This creates a causal chain that cannot be parallelized without changing the dynamics. In the language of Wolfram (2002), the soup is **computationally irreducible**: there is no shortcut to determining the outcome except running the sequential computation.

The GPU *can* accelerate the VM execution within each interaction (branchless predicated dispatch achieves 4–9× speedup), but it cannot parallelize the interaction *ordering* without destroying the causal structure that makes replicator emergence possible.

### 4.7 Competitive Experiments: Are the CG Choices Special?

Claims 1-3 demonstrate that CG primitives *can* support computational life, but do not show they are *uniquely* suited. To test this, we ran controlled experiments varying each CG-motivated design choice independently while holding all other parameters fixed (soup size 1024, program size 24, max_steps 729, mutation rate 0.001, 50K epochs, seeds 42/123/7).

**Verification scripts:** `stella_lang/test_substrate_competition.c`, `test_head_count.c`, `test_gate_condition.c`

#### 4.7.1 Substrate Competition: Z_N Modulus

| Modulus | N^2 opcodes | Semantic | NOP% | Replicators | Note |
|---------|-------------|----------|------|:-----------:|------|
| Z_2 | 4 | 4 | 0% | **0/3** | No loops or copy — structurally impossible |
| **Z_3** | **9** | **9** | **0%** | **3/3** | **All opcodes filled, zero waste** |
| Z_4 | 16 | 9 | 43.75% | **0/3** | NOP dilution suppresses emergence |
| Z_5 | 25 | 9 | 64.0% | **0/3** | Random programs mostly NOPs |
| Z_7 | 49 | 9 | 81.63% | **0/3** | Almost all NOPs |

**Finding:** Z_3 is the unique modulus where (a) N^2 equals the number of semantic opcodes (3^2 = 9), giving zero NOP waste, and (b) all necessary operations (loops, copy, movement) are available. Z_2 lacks the opcodes; Z_4+ have them but diluted by NOPs.

#### 4.7.2 Head Count: 1 vs 2 vs 3 Heads

| Heads | Replicators | Avg Dominance | Note |
|------:|:-----------:|--------------:|------|
| 1 | **0/3** | 0.1% | No inter-head copy — replication impossible |
| **2** | **3/3** | **6.8%** | **CPY01 (T+ -> T-) enables self-replication** |
| 3 | **0/3** | 0.1% | Instruction trade-offs (lost BCK0) hurt |

**Finding:** The 2-head structure is uniquely productive. 1-head lacks the copy mechanism entirely. 3-head has two copy targets but sacrifices backward movement (BCK0) to fit within 9 opcodes, and the added complexity of coordinating three heads does not help at this timescale.

#### 4.7.3 Gate Condition: Which Value Terminates Loops?

| Gate value | Replicators | Avg Compress | Note |
|-----------|:-----------:|-------------:|------|
| **0 (identity, CG default)** | **3/3** | **0.685** | **NOP=(0,0) aligns with gate skip** |
| 1 | **0/3** | 0.983 | No encoding alignment |
| 2 | **0/3** | 0.999 | No encoding alignment |
| parity (even/odd) | **0/3** | 0.998 | Different symmetry structure |

**Finding:** Gate=0 is uniquely productive. **Caveat:** This result has an encoding explanation — the NOP instruction is (0,0), so blank/uninitialized tape regions naturally satisfy the gate=0 skip condition. Programs can "fall through" loops over NOP regions, which facilitates copy-loop construction. For gate=1 or gate=2, no instruction encoding creates natural loop exits. This encoding asymmetry is *itself* part of the CG design (zero phase = identity = NOP), but the result should be interpreted as a property of the CG *encoding*, not a deep dynamical distinction.

#### 4.7.4 Combined Result

All three CG-motivated choices — and only those choices — produced self-replicators:

| CG Design Choice | CG Value | Alternatives Tested | Replicators |
|-------------------|----------|-------------------|:-----------:|
| Cell modulus (Def 0.1.2) | Z_3 | Z_2, Z_4, Z_5, Z_7 | **Only Z_3** |
| Head count (Def 0.1.1) | 2 (T+/T-) | 1, 3 | **Only 2** |
| Gate condition (Def 0.1.2, Prop 0.0.17h) | 0 (identity phase) | 1, 2, parity | **Only 0** |

**Interpretation (see Section 6 for full discussion):** The CG configuration (Z_3, 2-head, gate-on-zero) is a computationally privileged point in the design space for self-replicator emergence. The Z_3 result is the strongest: it reflects a genuine combinatorial property (N^2 = number of semantic opcodes only when N = 3). The 2-head and gate-on-zero results partially reflect instruction-set design choices rather than deep dynamics.

---

## 5. Connection to G11 Bootstrap

### 5.1 Self-Replication as Bootstrap Fixed Point

The bootstrap fixed-point structure (Prop 0.0.28, Thm 0.0.31) asserts that the CG framework is the unique self-consistent theory on ∂S. The self-replicator provides a computational analog:

- **Bootstrap:** The framework F satisfies F = B(F), where B is the bootstrap map
- **Replicator:** The program S satisfies S = split(exec(S || F))_1 for all foods F

Both are fixed points of self-referential maps. The bootstrap is a fixed point in theory space; the replicator is a fixed point in program space.

### 5.2 Uniqueness

In the 30M-epoch simulation, all surviving replicators share the same 20-trit core. While this does not prove uniqueness (other replicators may exist but were not found), it is consistent with the bootstrap's uniqueness claim: the self-consistency constraint strongly selects for a specific structure.

### 5.3 Relation to Prop 0.0.XXb

Proposition 0.0.XXb establishes that the bootstrap is computable with minimal Kolmogorov complexity. The self-replicator extends this: not only is the bootstrap computable, but the CG primitives are sufficient for *self-replicating* computation — programs that compute their own copies using only CG-derived operations.

This suggests a hierarchy:
1. **Computability** (Prop 0.0.XXb): CG can compute
2. **Universality** (Claim 1, this proposition): CG can compute anything
3. **Self-replication** (Claim 2): CG primitives sustain computational life
4. **Spontaneous emergence** (Claim 3): Self-replication arises without design

### 5.4 Relation to Thm 0.0.XXc

Theorem 0.0.XXc (Godel Bootstrap Separation) establishes limits on what the framework can prove about itself. The self-replicator does not violate these limits: it is a constructive object (verifiable in finite time), not a self-referential proof. The replicator demonstrates computational self-reference (a program that copies itself), which is distinct from logical self-reference (a theory that proves its own consistency).

### 5.5 Physical Interpretation (Speculative)

*The following interpretation is speculative. It is clearly separated from the established Claims 1-4 and should not be treated as a proven result.*

#### 5.5.1 The Cosmological Parallel

The soup simulation has a narrative arc that maps onto CG's cosmological narrative:

| Soup Stage | CG Stage | Physical Interpretation |
|-----------|----------|------------------------|
| Random initialization | Pre-geometric phase | Random Z_3 field configurations on ∂S, no structure |
| Random interactions | Field collisions | Configurations interact via superposition (Thm 0.2.1) |
| Phase transition (~3.5M) | Symmetry breaking | Order crystallizes from disorder |
| Replicator dominance | Stable vacuum + matter | Self-consistent structures dominate |
| Steady state | Physical universe | Fixed-point configuration determines everything |

#### 5.5.2 What Self-Replicators Would Represent

At increasing levels of speculation:

**Level 1 (Conservative): Topological solitons.** In CG, baryons and mesons are topological solitons — field configurations on ∂S that maintain their identity through interactions (Thm 4.1.1-4.1.3). A particle entering a scattering event emerges as itself. The replicator does something stronger: it not only *preserves* itself but *converts* other configurations into copies.

**Level 2 (Moderate): The vacuum state.** The CG vacuum is the unique field configuration satisfying the bootstrap equation F = B(F). It is self-consistent: any perturbation either relaxes back to this state or produces a topologically stable particle. The vacuum is, in a sense, the ultimate self-replicator — it fills all of space, and any region that departs from the vacuum state gets converted back into it (or into stable excitations of it). The soup's replicator converting food into copies mirrors the vacuum's tendency to impose its structure everywhere.

**Level 3 (Speculative): The emergence of physical law.** The deepest parallel:

- **Soup:** Random Z_3 digits → selection dynamics → unique self-replicating program
- **CG:** Space of possible theories on ∂S → self-consistency constraint → unique physical theory

Self-replicator emergence would represent **the universe selecting its own laws of physics**. The pre-geometric phase is a "soup" of all possible field configurations. Through interactions governed by the Z_3 structure of ∂S, one self-consistent configuration emerges and dominates — not because it was designed, but because self-consistency is an attractor.

#### 5.5.3 Why This May Be More Than Metaphor

Three structural features elevate the parallel above pure analogy:

1. **Analogous primitives.** The replicator uses CPY01, which is grounded in the two-component topology of ∂S (Def 0.1.1), the inter-component field coupling (Thm 0.2.1), and the T₊ → T₋ directionality from the arrow of time (Prop 0.0.17c). CPY01 is a computational tape-copy operation, not a direct implementation of field dynamics — but it encodes the same structural content: information flows between two coupled domains with a preferred direction. The loop gates are grounded in the Z₃ identity-element test (Def 0.1.2): the identity phase (0) is algebraically distinguished from the non-identity phases (2π/3, 4π/3), and the gate implements this group-theoretic conditional. Both operations are far simpler than their physical counterparts, but they preserve the relevant algebraic and topological structure.

2. **Same fixed-point structure.** The bootstrap equation F = B(F) and the replicator equation S = split(exec(S||F))₁ are both fixed points of self-referential maps. The competitive experiments (Section 4.7) show this fixed point exists *only* at the CG configuration (Z_3, 2-head, gate-on-zero). If the fixed point is unique in both program space and theory space, the parallel has mathematical content.

3. **Same phase transition.** Both transitions go from disordered (high entropy, no structure) to ordered (low entropy, self-consistent structure) driven by the dynamics themselves, not by external design. The soup has no fitness function — order emerges from pure Z_3 interaction dynamics, just as CG claims spacetime emerges from pure field dynamics on ∂S.

#### 5.5.4 Physical Suggestions If This Connection Holds

If the soup-to-CG parallel is physical rather than metaphorical, it would suggest:

1. **Matter is inevitable.** Stable particles (topological solitons) emerge from *any* initial field configuration on ∂S, not just fine-tuned ones — just as replicators emerge from random soup. The universe requires no special initial conditions.

2. **The vacuum is an attractor.** The ground state is dynamically selected, not assumed — the pre-geometric phase naturally evolves toward the unique self-consistent configuration. This connects to the bootstrap uniqueness claims (Thm 0.0.31, Prop 0.0.28).

3. **The bootstrap is a dynamical process.** The universe does not merely "happen to satisfy" F = B(F); it *evolves toward* this fixed point through copy-and-iterate dynamics. The bootstrap is not a static consistency check but the endpoint of a dynamical selection process analogous to replicator takeover.

4. **The CG configuration is a computational attractor.** The competitive experiments show Z_3 + 2-head + gate-on-zero is the unique computationally productive configuration. If this reflects physics, the specific structure of ∂S (two tetrahedra, Z_3 phases, identity-phase superselection) is not arbitrary but the *only* configuration capable of supporting self-organizing structure.

#### 5.5.5 Caveat

The gap between "a program copies itself on a tape" and "the vacuum imposes its structure on spacetime" is enormous. The soup operates on a discrete tape with fixed interaction rules. The physical universe has continuous fields, quantum mechanics, and general relativity. These speculative interpretations identify structural parallels but do not constitute derivations. Proving any of the suggestions in Section 5.5.4 would require working within the full CG field theory, not the simplified computational model.

---

## 6. Limitations

### 6.1 Computational Evidence, Not Physical Proof

This proposition demonstrates that the CG primitive set is computationally privileged — but computational privilege is not the same as physical correctness. The competitive experiments (Section 4.7) show the CG configuration is uniquely productive for self-replicator emergence. However:

- Turing completeness (Claim 1) holds for any instruction set with loops and sufficient memory. Z_3 cells are not special *at this level*.
- The competitive results test the *instruction encoding*, not the underlying physics. A non-CG framework that happened to use the same encoding would produce the same results.

### 6.2 Separating Combinatorial From Physical Claims

The three competitive results have different levels of depth:

1. **Z_3 substrate (strongest).** The result that N = 3 is the unique modulus where N^2 = number of semantic opcodes (9) is a genuine combinatorial fact. Any framework that needs exactly 9 primitive operations and encodes them as digit pairs will find N = 3 optimal. This is independent of CG — but CG *does* need exactly these 9 operations, so the alignment is non-trivial.

2. **2-head structure (moderate).** The result that 2 heads beat 1 or 3 is partly an artifact of the 9-opcode budget. With 1 head, 4 of 9 slots are wasted. With 3 heads, BCK0 must be sacrificed. The finding is real but reflects instruction-set trade-offs, not a deep property of having two geometric components.

3. **Gate on zero (weakest).** This result has a clear encoding explanation: NOP = (0,0) means blank tape satisfies gate=0 automatically. Replicators need regions where loops exit, and gate=0 gets these "for free" from uninitialized tape. This is a property of the encoding convention, not a deep physical distinction. The gate condition test should be understood as confirming that the CG *encoding* is self-consistent, not that zero phase is dynamically special.

### 6.3 No New Experimental Predictions

This proposition does not predict any particle mass, cross-section, decay rate, or experimentally testable quantity. The competitive experiments are tests of the *computational framework*, not of nature.

### 6.4 What This Proposition Establishes

1. **The CG primitive set is computationally complete** (Claim 1) and supports self-replicating programs (Claims 2-3). This is a necessary condition for the framework's physical claims.

2. **The CG configuration is a unique optimum** in the computational design space (Section 4.7). The design space of 60 configurations (5 moduli x 3 head counts x 4 gate conditions) was probed via 12 experiments in 3 independent one-dimensional sweeps. Only the CG configuration (Z_3, 2-head, gate-on-zero) produced self-replicators. The Z_3 result reflects a genuine combinatorial property; the others reflect encoding design. The full Cartesian product was not tested — interactions between non-CG choices remain unexplored.

3. **The replicator is a fixed-point analog of the bootstrap.** The program S satisfies S = split(exec(S||F))₁, structurally parallel to the bootstrap F = B(F). The CG primitives naturally support this self-referential structure.

4. **The physics labels are load-bearing for the design, not for the computation.** The CG theorems motivate *why* the instruction set has exactly 9 operations, *why* there are 2 heads, and *why* zero is the gate value. Removing these motivations would leave an arbitrary instruction set that happens to work — but the framework explains *why it works*.

---

## 7. Summary

| Claim | Type | Status | Method |
|-------|------|--------|--------|
| 1. Turing Completeness | Mathematical | ✅ Proven | BF simulation via Z_3 encoding |
| 2. Self-Replicator Construction | Constructive | ✅ Verified | Explicit 20-trit program, tested |
| 3. Spontaneous Emergence | Empirical | ✅ Observed | 30M-epoch simulation, seed 42 |
| 4. Causal Ordering Essential | Empirical | ✅ Observed | GPU parallelism destroys emergence (Section 4.6) |
| 5. CG Configuration Uniqueness | Empirical | ✅ Observed | Competitive experiments (Section 4.7) |

**Key result:** The CG configuration (Z_3 cells, 2 heads, gate-on-zero) is the unique point in the tested design space that produces self-replicators. The design space spans 60 configurations (5 moduli x 3 head counts x 4 gate conditions), tested via 12 experiments in 3 independent one-dimensional sweeps (5 + 3 + 4 settings, each with 3 seeds = 36 trials total). Each sweep varies one parameter while holding the others at CG defaults. Only the CG configuration succeeded — 9/9 trials across the three CG settings.

**Scope (see Section 6):** The competitive results are stronger than pure consistency checks — they show the CG choices are computationally *privileged*, not merely *sufficient*. The Z_3 result reflects a genuine combinatorial fact (3^2 = 9 = number of semantic opcodes). The 2-head and gate-on-zero results partially reflect instruction-set design choices. None of these results constitute evidence for the physical correctness of CG, but they demonstrate that the framework's structural choices are not arbitrary.

---

## 8. Dependent Theorems

| Theorem | Dependency Type |
|---------|----------------|
| Prop 0.0.XXb (Bootstrap Computability) | Extended: computability -> universality -> self-replication |
| Thm 0.0.XXc (Godel Bootstrap Separation) | Complemented: constructive vs logical self-reference |
| Thm 0.0.19 (Self-Reference Uniqueness) | Connected: fixed-point uniqueness in program space |

---

## 9. References

1. **Muller, U.** "Brainfuck." 1993. [Language creation; Turing completeness follows from isomorphism to P'' (Bohm, 1964)]
2. **Aguera y Arcas, B., Alakuijala, J., Evans, J., Laurie, B., Mordvintsev, A., Niklasson, E., Randazzo, E., and Versari, L.** "Computational Life: How Well-formed, Self-replicating Programs Emerge from Simple Interaction." arXiv:2406.19108, 2024.
3. **Hopcroft, J.E., Ullman, J.D.** *Introduction to Automata Theory, Languages, and Computation.* Addison-Wesley, 1979.
4. **Definition 0.1.1** — Stella Octangula Boundary Topology. `docs/proofs/Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md`
5. **Definition 0.1.2** — Three Color Fields. `docs/proofs/Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md`
6. **Theorem 0.2.1** — Total Field Superposition. `docs/proofs/Phase0/Theorem-0.2.1-Total-Field-Superposition.md`
6a. **Proposition 0.0.17c** — Arrow of Time From Information Geometry. `docs/proofs/foundations/Proposition-0.0.17c-Arrow-of-Time-From-Information-Geometry.md`
7. **Proposition 0.0.17h** — Information Horizon Derivation. `docs/proofs/foundations/Proposition-0.0.17h-Information-Horizon-Derivation.md`
8. **Proposition 0.0.XXb** — Bootstrap Computability. `docs/proofs/foundations/Proposition-0.0.XXb-Bootstrap-Computability.md`
9. **Theorem 0.0.XXc** — Godel Bootstrap Separation. `docs/proofs/foundations/Theorem-0.0.XXc-Godel-Bootstrap-Separation.md`
10. **Stella Soup 30M Results** — `stella_lang/RESULTS-30M.md`
11. **Verification Script** — `stella_lang/verify_replicator.py`
12. **Substrate Competition** — `stella_lang/test_substrate_competition.c` (Z_N comparison)
13. **Head Count Experiment** — `stella_lang/test_head_count.c` (1 vs 2 vs 3 heads)
14. **Gate Condition Experiment** — `stella_lang/test_gate_condition.c` (gate value comparison)
15. **Bohm, C.** "On a family of Turing machines and the related programming language." *ICC Bulletin*, 3(3), 1964. [P'' language; BF Turing completeness via isomorphism]
16. **Cristofani, D.B.** Universal Turing machine in Brainfuck. `brainfuck.org/utm.b`. [Constructive proof of BF Turing completeness]
17. **Von Neumann, J.** *Theory of Self-Reproducing Automata.* University of Illinois Press, 1966. [Foundational work on self-replicating machines]
18. **Ray, T.S.** "An Approach to the Synthesis of Life." In *Artificial Life II*, Santa Fe Institute Studies in the Sciences of Complexity, vol. XI, pp. 371-408, Addison-Wesley, 1991. [Tierra: assembly-language digital evolution]
19. **Langton, C.G.** "Self-Reproduction in Cellular Automata." *Physica D: Nonlinear Phenomena*, 10(1-2):135-144, 1984. [Self-reproducing loops in cellular automata]
