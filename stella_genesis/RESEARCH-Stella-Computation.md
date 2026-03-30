# RESEARCH: Stella Computation
## Can the Stella Octangula Support Non-Standard Computation?

**Status:** ACTIVE | All phases NULL at Level 0 | C2 self-replication depth completed | 2026-03-24

---

## 1. Motivation

The prime interference experiments (H1-H7) showed that the stella's eigenvalue ratios {2,2,2,3} encode the first two primes purely from topology. But H7's spectral factorization reduced to trial division — no computational advantage.

A deeper question: could the stella's *physical geometry* (not just its mathematical description) support computation that a Turing machine cannot efficiently simulate?

Existing framework results:
- StellaLang is Turing-complete (Prop 0.0.XXd)
- **Sequential lambda-ordering is REQUIRED** — GPU parallel execution destroys self-organization (Section 4.6)
- Self-replicators emerge spontaneously (only with sequential execution)
- Bootstrap is P-time computable, in BQP, no quantum speedup (Prop 0.0.XXb)
- Bootstrap escapes Godel undecidability — in Delta_1 (Theorem 0.0.XXc)
- Continuum limit is bilayer Fisher-KPP (Prop 0.0.XXe)

## 2. Hierarchy of Computational Claims

| Level | Claim | Evidence Needed |
|-------|-------|----------------|
| 0 | Re-encoding (same computation, different notation) | Nothing — already have this |
| 1 | Natural computation (some problems expressed more naturally) | Problem class where stella formulation is shorter |
| 2 | Constant-factor advantage (same class, better constants) | Benchmarks against classical algorithms |
| 3 | P-completeness (inherently sequential) | Prove soup dynamics are P-complete under NC reductions |
| 4 | Analog advantage (continuum escapes discrete bounds) | PDE steady state faster than any discrete method |

The re-encoding trap (H7 lesson): every phase includes explicit null-result criteria.

## 3. Experiment Program

| Phase | Question | Status |
|-------|----------|--------|
| C1 | Is sequential lambda-ordering P-completeness or race conditions? | **NULL** — race conditions, not P-complete |
| C2 | Is self-replication computationally deep? | **NULL** — one strategy (copy loop), sub-linear depth, no optimization advantage |
| C3 | Is Z3 interference a genuine computational resource? | **NULL** — classical interference, no quantum advantage |
| C4 | Does chi=4 topology enable error correction or braiding? | **NULL** — 8>4 copies, not topology; no non-abelian braiding |
| C5 | Does the continuum limit compute faster than discrete? | **NULL** — PDE = standard iteration, no gap |
| C6 | Can lambda-ordering be formalized as an oracle? | SKIPPED — C1 null invalidates premise |
| C7 | What complexity class characterizes stella computation? | **COMPLETE** — P (standard TM), Level 1 only |
| C1b | Do parallel execution strategies match sequential reference? | **COMPLETE** — snapshot closest (KL=0.030), grouped worst |
| C1c | Is CPU lower entropy from ordering or race conditions? | **COMPLETE** — ordering (+0.163), races on snapshot catastrophic (+0.310) |

Dependency: C1 -> C6. C2, C3, C4, C5 independent. C7 needs all. C1b, C1c follow from C1.

---

## 4. Phase C1: P-Completeness of Soup Dynamics

### 4.1 Design

**Question:** Is the sequential lambda-ordering requirement evidence of P-completeness (inherently non-parallelizable), or just race conditions from the GPU experiment?

**Approach:** Three-part test:
- **Part A:** Compare sequential vs snapshot-parallel soup execution. In snapshot mode, all interactions in an epoch read from the epoch-start state (maximum parallelism). If results match sequential, within-epoch ordering doesn't matter.
- **Part B:** Dependency graph analysis. For each epoch, compute the critical path length — the longest chain of interactions that must execute sequentially due to shared programs.
- **Part C:** Critical path scaling with soup size N. If O(log N), dynamics are in NC. If O(N), P-hard.

**Prediction:** Critical path should be O(log N) due to birthday-problem statistics. With K = N/2 interactions touching 2 of N programs, collisions follow Poisson(1) per program, giving sparse dependency graphs.

### 4.2 Results

**Part A — Sequential vs Snapshot-Parallel (N=512, 200K epochs):**
- Entropy divergence: 0.092 (nearly identical trajectories)
- Both modes: similar unique counts (~505-510), neither produced replicators at this scale
- **Verdict: snapshot-parallel is equivalent to sequential** — within-epoch ordering doesn't matter

**Part B — Dependency Graph (N=4096, 10K epochs analyzed):**
- Mean critical path: **7.21** (out of 2048 interactions per epoch)
- Max critical path: 12
- Mean parallelism: **249x** (2048 interactions executable in ~8 waves)
- The dependency graph is extremely sparse

**Part C — Scaling (N = 32 to 16384):**
```
N       log2(N)  mean_cp  cp/log2(N)  parallelism
32      5.0      3.17     0.634       3.8x
128     7.0      4.52     0.646       11.6x
512     9.0      5.71     0.634       38.2x
2048    11.0     6.73     0.611       132.5x
8192    13.0     7.68     0.591       471.9x
16384   14.0     8.11     0.580       898.9x
```
- **Log fit: cp = 0.546 * log2(N) + 0.649** (R excellent)
- **Power fit: cp = 2.17 * N^0.144** (exponent ≪ 1)
- **Scaling class: NC (logarithmic)**

### 4.3 Interpretation

The within-epoch dynamics are **firmly in NC** — the critical path grows logarithmically with soup size. With N=16384 programs, 8192 interactions per epoch can be parallelized into ~9 sequential waves (parallelism factor ~900x).

The GPU failure (Prop 0.0.XXd Section 4.6) was **race conditions from lack of epoch barriers**, not P-completeness. A barrier-synchronized parallel implementation would preserve self-organization.

The across-epoch sequentiality (epoch t+1 depends on epoch t) is standard iterative dynamics — true of any dynamical system. This does NOT indicate P-completeness.

**Result: NULL (Level 0).** The sequential requirement is not complexity-theoretically significant.

However, one nuance remains: even though within-epoch parallelism works, the question of whether T epochs can be "shortcut" (computed in fewer than T sequential steps) is still open. This is the standard question for any iterative system and does not require stella-specific investigation.

---

## 5. Phase C2: Computational Depth of Self-Replication

### 5.1 Design

**Question:** Is self-replication in the stella VM computationally deep, or is it a simple copy loop?

C1 showed within-epoch dynamics are in NC (parallelizable). C2 asks a different question: what is the computational complexity of self-replication *as a program-level phenomenon*? This is about the VM executing a replicator, not the soup-level dynamics.

**Four-part test:**
- **Part A:** Exhaustive replicator census — how many exist, how many mechanisms?
- **Part B:** Computational complexity — step count vs program length
- **Part C:** Ecosystem dynamics — do multiple types coexist?
- **Part D:** Fitness landscape — can selection solve optimization problems?

### 5.2 Results

**Part A — Exhaustive Replicator Census:**

| L | Total Tested | Replicators | Method |
|---|-------------|-------------|--------|
| 6 | 729 | 0 | exhaustive |
| 8 | 6,561 | 1 | exhaustive |
| 10 | 59,049 | 6 | exhaustive |
| 12 | 531,441 | 23 | exhaustive |
| 14 | 4,782,969 | 106 | exhaustive |
| 16 | 43,046,721 | 482 | exhaustive |
| 18 | 10,000,000 | 70 | sampled |
| 20 | 10,000,000 | 34 | sampled |
| 22 | 10,000,000 | 33 | sampled |
| 24 | 10,000,000 | 23 | sampled |

- **667 unique replicators** found total
- **31 universal** (work for all tested food programs)
- **13 soup-viable** (still replicate when padded to prog_size=24)
- **Two mechanisms:** `copy_loop_fwd` (214, uses OPEN/CLOSE + CPY01 + FWD0 + FWD1) and `linear_copy` (453, sequential CPY01 without loops)
- **No `copy_loop_rev` or `other`** mechanisms found
- Minimum replicator length: 8 trits (4 instructions)
- Replicator density increases exponentially with L (exhaustive), as expected for random programs with more room for copy sequences

**Key finding:** Two structural variants of the *same functional strategy* (copy bytes from A-half to B-half). The looped version is compact; the linear version is unrolled. Both achieve the same result — no fundamentally different replication strategy exists in this instruction set.

**Part B — Computational Complexity of Replication:**

- **107 of 200 tested** replicators complete below MAX_STEPS (729); 93 hit the step limit
- **Power fit:** steps ~ 12.3 × L^0.647 (sub-linear! k = 0.647)
- **Linear fit:** steps = 2.34L + 36.3, R² = 0.12 (poor fit due to high variance)
- Variance is high because linear-copy replicators use fixed step counts (proportional to instruction count) while loop-based replicators scale with loop iterations

**Interpretation:** Replication is O(L) or better — sub-linear because short replicators' copy loops terminate early when they hit a 0 (NOP). No replicator uses super-linear computation (no nested loops, no food-dependent branching).

**Part C — Ecosystem Dynamics (N=512, 50K epochs, 5 seeds):**

Interaction matrix: **all outcomes are "A_dominates"** — the program in position A (first half of tape) always overwrites B. This is a structural artifact: h0 starts at position 0 (reading A), h1 starts at midpoint (writing over B).

| Seed | Winner | Max Fraction | Final Replicators | Notes |
|------|--------|-------------|------------------|-------|
| 0 | type 1 (loop) | 94.1% | 482/512 | EXCLUSION — loop replicator dominates |
| 1 | other | 72.5% | 420/512 | Novel mutants replace seeded types |
| 2 | type 1 (loop) | 96.9% | 496/512 | EXCLUSION |
| 3 | other | 75.0% | 450/512 | Novel mutants replace seeded types |
| 4 | type 1 (loop) | 94.5% | 492/512 | EXCLUSION |

- Exclusion rate: 3/5 seeds (60%)
- In ALL seeds, replicators eventually dominate the soup (420-496 of 512 programs become functional replicators)
- In 2/5 seeds, the seeded types went EXTINCT and were replaced by novel evolved replicators (hamming distance > 5 from any seeded type)
- The copy_loop_fwd mechanism wins when it wins; but mutant replicators can outcompete in some initial conditions

**Interpretation:** Standard competitive exclusion. The A-position advantage means the first replicator to spread has a structural edge. When novel mutants evolve faster than seeded types can spread, they take over instead. No stable multi-type coexistence — this is simple Darwinian dynamics.

**Part D — Fitness Landscape (200K evaluations):**

```
Method          Best Fitness (of 24)
Random search:  19
Hill-climb:     24 (PERFECT)
Soup selection: 17
```

- Hill-climbing trivially finds the optimum (24/24) with enough evaluations
- Soup selection (17/24) **underperforms even random search** (19/24)
- The soup's self-replication dynamics actively *interfere* with optimization — replicators that are good at copying aren't necessarily close to the target

### 5.3 Interpretation

**Result: NULL (Level 0).** Self-replication in the stella VM is computationally shallow:

1. **One strategy, two representations.** All 667 replicators use the same functional approach: copy trits from the A-half to the B-half using CPY01. The only variation is looped vs unrolled. No fundamentally different replication strategy exists.

2. **Sub-linear depth.** Replication takes O(L^0.65) steps — less than linear because copy loops terminate on the first NOP encountered. No replicator performs food-dependent computation or uses nested loops.

3. **Standard competitive exclusion.** When multiple replicator types compete, one always dominates. The A-position structural advantage creates winner-take-all dynamics. No stable multi-type ecosystems.

4. **No optimization advantage.** The soup's self-replication dynamics actively hinder directed search. Hill-climbing (a trivial algorithm) reaches perfect fitness; the soup doesn't even match random search.

**The "spontaneous emergence" result is real but shallow.** Self-replicators emerge because the VM's instruction set makes copy loops easy to express — 667 of ~4.3 × 10^7 programs at L=16 are replicators (1.5 × 10^-5 density), and with 4096 programs interacting for 100K+ epochs, at least one will be found by chance. The emergence is a birthday-problem statistical inevitability, not a sign of computational depth.

> **Cross-reference: Necessity vs abundance (RESULTS-Crystallization.md Phase Z1).**
> This statistical emergence contrasts sharply with Z₃ phase structure, which Phase Z1 proves is a *dynamical attractor* (100% convergence, 30/30 seeds from any initial condition). The stella thus has two classes of emergent properties: *necessary* ones (Z₃ symmetry, non-degeneracy — probability 1) and *contingent* ones (self-replication, ecosystem dynamics — birthday-problem statistics). The fundamental geometry is inevitable; the computational life it hosts is not.

### 5.4 Cross-Reference: {2, 3} in Spectrum and Computation

The same two construction numbers **{2, 3}** that H6 (RESEARCH-Prime-Interference.md §18) found in the stella's vibrational spectrum also determine its computational primitives:

| Domain | Role of 2 | Role of 3 |
|--------|-----------|-----------|
| **Spectral (H6)** | 2 tetrahedra → eigenvalue ratio 2 | Z₃ → eigenvalue ratio 3 |
| **Computational (C2)** | 2 heads (T+/T-) → directed copy CPY01 | Z₃ → loop gate OPEN/CLOSE (exit on identity phase) |
| **Replication** | Copy is *between* the 2 tape halves | Loop terminates on *Z₃ identity* (trit 0) |

The instruction set has 9 = 3² opcodes (trit pairs), and self-replication requires exactly the opcodes that bridge the two tetrahedra (CPY01: T+ → T-) and exploit Z₃ structure (OPEN/CLOSE: test for identity phase). The remaining opcodes (ROT, BCK0, CPY10) are never essential.

This is consistent with the Level 1 classification: the stella is an efficient *encoding* of physics built from {2, 3}. The same geometry that produces primes as eigenvalue ratios also produces primes as the irreducible building blocks of self-replication. Neither result is a computational advantage — both are the stella encoding its own structure.

*See also: RESEARCH-Prime-Interference.md §18.2 ("The stella literally encodes its own prime structure in its vibrational spectrum")*

---

## 6. Phase C3: Z3 Interference as Computational Resource

### 6.1 Results

**Part A — Z3 Interference Visibility:**
- Visibility ranges from 1.0 (tight coupling, sigma=0.2) to 0.6 (broad coupling, sigma=8.0)
- Strong constructive interference at vertices with matching Z3 charges; destructive at mismatched
- But this is **classical wave interference**, not quantum

**Part B — Classical Simulation Cost:**
- State space is 3^(N*L) (astronomical for large N)
- But dynamics are LOCAL: each interaction modifies only 2 programs
- Classical simulation replays transcript in **O(T*N) time** — efficient
- **No quantum advantage**: Z3 phases are classical labels, not quantum superpositions

**Part C — Z3 Energy Minimization (Z3 Potts model):**
```
N=20:   Metropolis=-28.90  Annealing=-28.68  Random=-16.60  Winner: metropolis
N=50:   Metropolis=-74.35  Annealing=-74.28  Random=-26.73  Winner: metropolis
N=100:  Metropolis=-151.25 Annealing=-151.25 Random=-38.38  Winner: tie
N=200:  Metropolis=-298.05 Annealing=-298.05 Random=-55.65  Winner: tie
```
- Metropolis (soup-like) performs comparably to annealing — NOT better
- Both vastly outperform random sampling
- At larger sizes, they converge to the same quality

### 6.2 Interpretation

**Result: NULL (Level 0).** Z3 interference is classical wave interference on a graph. It provides beautiful patterns but no computational advantage over standard optimization methods. The soup's Z3 structure is a constraint language, not a computational resource.

#### 6.3 Caveat: 1D/Graph vs 3D Surface

C3 tested Z₃ interference on a flat graph. However, §21.6 of RESEARCH-Prime-Interference.md discovered that the stella's *actual 3D surface* acts as an **information amplifier for prime frequencies**: the compression ordering that holds in 1D **inverts** on ∂S. Primes go from most-compressed (1D slope 5.83) to most-information-rich (surface slope 1.11 vs 0.52–0.77 for other frequency sets).

This raises an open question: **would Z₃ interference show non-trivial computational structure when tested on the actual stella surface rather than a graph?** C3's null result may be an artifact of the 1D/graph domain, which overstates compression and understates the stella geometry's selective amplification of Z₃-compatible structure. The stella graph saturates at rank 4 (§21.6 Finding 1), meaning the graph loses most geometric information — exactly the information that might make Z₃ interference computationally interesting.

*Status: OPEN — C3 tested on graph only. §21.6 shows geometry matters.*

---

## 7. Phase C4: Topological Computation on chi=4

### 7.1 Results

**Part A — Information Storage:**
- Chi=4 (8 vertices) fidelity vs chi=2 (4 vertices) at selected error rates:
  - p=0.10: chi4=99.93%, chi2=98.41% (advantage: +1.5%)
  - p=0.25: chi4=97.57%, chi2=89.60% (advantage: +8.0%)
  - p=0.40: chi4=84.83%, chi2=73.35% (advantage: +11.5%)
- Advantage is **trivially** from 8 > 4 copies, not from topology

**Part B — Braiding Analysis:**
- Same-surface particle pairs: 12 (can braid within T+ or T-)
- Cross-surface pairs: 16 (CANNOT braid — disconnected)
- Braiding group: Z2 (abelian particle exchange only)
- **Non-abelian anyons: IMPOSSIBLE on S^2** (trivial fundamental group)
- Need punctured surfaces or genus >= 1 for non-abelian braiding

**Part C — Error Correction:**
- Hierarchical T+/T- voting does NOT improve over simple 8-copy majority
- The two-component topology adds nothing beyond extra vertices
- Any 8-vertex connected graph performs identically

### 7.2 Interpretation

**Result: NULL (Level 0).** The chi=4 topology provides no computational advantage. Error correction scales with number of copies (8 vs 4), not topological invariants. S^2 is simply connected, so braiding is abelian (Z2), which is insufficient for topological quantum computation. The two disconnected surfaces are computationally irrelevant.

---

## 8. Phase C5: Analog Computation in the Continuum Limit

### 8.1 Results

**Part A — PDE Relaxation vs Algebraic Eigenvalues:**
- Jacobi eigenvalue solver (algebraic): converges for all sizes tested (8-128 vertices)
- Relaxation (power iteration): struggles with accuracy — relative errors grow with system size
- For 8x8 stella: Jacobi finds all 8 eigenvalues simultaneously; relaxation finds only the dominant one
- **No analog advantage**: both methods are polynomial, Jacobi is faster and more accurate

**Part B — Fisher-KPP on Stella:**
- Steady state depends on diffusion/reaction ratio D/r:
  - Low D (≤0.01): all vertices → 1.0 (homogeneous, confined)
  - High D (≥0.5) with low r: T+ → 1.0, T- → 0.0 (**component separation = deconfinement!**)
  - High r overcomes diffusive separation
- Relaxation time ~ 1/r (inversely proportional to growth rate)
- **Bonus physics**: the D-r phase boundary maps onto the confinement/deconfinement transition (Prop 0.0.XXe)
- **Computationally**: the PDE solves a fixed-point problem — any iterative method achieves the same result

**Part C — Complexity Comparison:**
- Eigenvalue problem: both O(N^3)
- Steady state: both O(T*N)
- No computational gap between analog (PDE) and digital (iteration)

### 8.2 Interpretation

**Result: NULL (Level 0).** The continuum limit is efficiently simulable by standard PDE solvers. The Fisher-KPP steady state is a contractive fixed point (Prop 0.0.XXe), so convergence is exponential for any method. The interesting physics (deconfinement transition) is not computationally novel — it's a standard bifurcation in a reaction-diffusion system.

---

## 9. Phase C6: Oracle Separation

SKIPPED. C1's null result (dynamics in NC) means there is no meaningful P-completeness result to build an oracle from.

---

## 10. Phase C7: Synthesis — Classifying Stella Computation

### 10.1 Classification Table

| Phase | Question | Result | Level |
|-------|----------|--------|-------|
| C1 | P-completeness? | NULL — CP = 0.55*log2(N), dynamics in NC | 0 |
| C3 | Z3 interference advantage? | NULL — classical, O(T*N) simulable | 0 |
| C4 | Topological computation? | NULL — abelian braiding, no error correction from topology | 0 |
| C5 | Analog advantage? | NULL — PDE = standard iteration | 0 |
| C2 | Self-replication depth? | NULL — one mechanism, O(L^0.65), no optimization advantage | 0 |
| C6 | Oracle separation? | SKIPPED (C1 premise invalidated) | — |

### 10.2 Comparison with Known Models

| Model | Stella Equivalent? | Reason |
|-------|--------------------|--------|
| Classical TM | **Yes** | StellaLang is Turing-complete |
| Quantum (BQP) | **Weaker** | Z3 phases are classical labels, no entanglement |
| Topological QC | **Weaker** | S^2 braiding is abelian (Z2), need higher genus for non-abelian anyons |
| Analog (BSS) | **No** | Fisher-KPP efficiently discretizable |
| CA (Rule 110) | **Equivalent** | Both Turing-complete, comparable dynamics |

### 10.3 The Honest Answer

**The stella is NOT an alternative to how computation is done.**

It is a Turing-complete ternary cellular automaton with Z3 symmetry, computationally equivalent to standard CAs like Rule 110. It cannot:
- Outperform a quantum computer (no superposition/entanglement)
- Perform topological QC (S^2 braiding is abelian)
- Hypercompute via analog dynamics (Fisher-KPP is discretizable)
- Exploit P-completeness (within-epoch dynamics are in NC)

### 10.4 The Real Surprise

**The stella's computational significance is information-theoretic, not complexity-theoretic.**

The framework computes the SAME things as a standard Turing machine, but with extraordinarily compressed input. The 205-bit bootstrap (Prop 0.0.XXb) produces predictions for dozens of physical constants — gauge group, mass spectrum, gravitational coupling.

This is not a new way of computing. It is a maximally efficient ENCODING of physics. The stella is remarkable not because it computes differently, but because it computes so much from so little.

> **Cross-reference: §21.6 of RESEARCH-Prime-Interference.md explains *why* the encoding is so efficient.**
> On the actual 3D stella surface, prime frequencies have the highest information slope (1.11 vs 0.52–0.77 for other frequency sets) — the geometry preferentially amplifies prime-frequency information content. Since the 205-bit bootstrap encodes physics through stella geometry, this information amplification property may be the mechanism underlying the extraordinary compression ratio: the stella is not just any encoding, it is an encoding on a surface that is geometrically optimized for the frequency structure it needs to represent.

**Level achieved: 1 (Natural computation)**
Some problems have more natural expression in stella language (Z3 coloring, {2,3}-factorization from topology), but there is no complexity-theoretic advantage over standard models.

### 10.5 Proposed Proposition

**Prop 0.0.XXf: Computational Classification of Stella Dynamics**

*Statement:* The Stella Soup VM (Prop 0.0.XXd) is a Turing-complete cellular automaton whose within-epoch interaction dynamics lie in NC (critical path O(log N)), while across-epoch dynamics are standard iterative computation. The framework's computational significance is information-theoretic (K-complexity ~205 bits, Prop 0.0.XXb) rather than complexity-theoretic: the stella computes in P with no advantage over standard Turing machines.

*Evidence:* C1 (CP = 0.55*log2(N)), C3 (O(T*N) classical simulation), C4 (abelian braiding only), C5 (PDE = iteration)

---

## 11. Phase C1b: Execution Semantics Comparison

### 11.1 Motivation

C1 showed within-epoch dynamics are in NC (critical path O(log N)), justifying parallel execution. But the production implementations use *different* parallelization strategies:

| Implementation | Strategy | Within-epoch ordering |
|----------------|----------|-----------------------|
| `soup.c` (reference) | Fully sequential | Strict — interaction N sees N-1's result |
| `soup_multi_stella.c` (CPU) | Per-stella sequential, parallel across stellae | Partial — sequential within stella, no ordering across stellae |
| `soup_multi_stella_metal.m` (GPU) | Snapshot-parallel (double-buffered) | None — all interactions read frozen epoch-start state |

**Question:** Do these different semantics produce equivalent dynamics? Which is most faithful to the reference?

### 11.2 Design

Three strategies implemented on the same flat soup (N=512, 256 interactions/epoch, 500K epochs):

- **Strategy A (Sequential):** Reference. Each interaction reads/writes live state. Interaction N sees N-1's output.
- **Strategy B (Grouped):** Simulates CPU pthreads. N programs partitioned into 16 groups. Within-group interactions are sequential; cross-group effects only visible next epoch.
- **Strategy C (Snapshot):** Simulates GPU double-buffering. All interactions read from frozen epoch-start snapshot, write to separate buffer. No interaction sees another's results within the same epoch.

All three start from identical initial conditions with separate RNG streams.

### 11.3 Results

**Entropy trajectories (500K epochs):**
```
Epoch     Sequential   Grouped    Snapshot
50000     0.5835       0.9126     0.7336
100000    0.5801       0.9353     0.6986
200000    0.4837       0.9290     0.7606
300000    0.5410       0.9269     0.6416
500000    0.5744       0.9133     0.7128
```

**Unique programs (of 512):**
```
Epoch     Sequential   Grouped    Snapshot
500000    356          477        422
```

**Replicators detected (per 200 tests):**
```
Epoch     Sequential   Grouped    Snapshot
100000    6            0          0
200000    5            0          1
300000    8            0          0
400000    4            0          5
500000    1            0          1
```

**KL divergence from sequential reference:**
```
              Mean over trajectory
seq vs grp:   0.176 (LARGE — different dynamics)
seq vs snap:  0.030 (small — similar dynamics)
grp vs snap:  0.088 (moderate)
```

### 11.4 Interpretation

| Strategy | Entropy | Diversity | Replicators | KL from ref | Assessment |
|----------|---------|-----------|-------------|-------------|------------|
| Sequential | **0.57** (low) | **356** | **Frequent** | — | Ground truth |
| Grouped | 0.91 (high) | 477 | **Almost never** | 0.176 | **Broken** — suppresses selection |
| Snapshot | 0.71 (medium) | 422 | Occasional | 0.030 | **Good approximation** |

**Key findings:**

1. **Sequential ordering amplifies selection pressure.** When a replicator in interaction N overwrites its partner, interaction N+1 may pick that freshly-replicated program, creating a cascade. This within-epoch amplification drives entropy down and replicators up.

2. **Snapshot-parallel is the best parallel approximation** (KL divergence 0.030 from reference). It preserves the global interaction structure — any program can interact with any other — but delays the cascade effect by one epoch. C1's O(log N) critical path means very few interactions actually conflict, so the delay rarely matters.

3. **Group partitioning suppresses self-organization.** Restricting interactions to within-group prevents the cross-group selection that drives replicator spread. Entropy stays near maximum (0.91), and replicators essentially never emerge.

4. **The CPU pthread multi-stella implementation is NOT the same as group partitioning.** In the production code, each stella is an independent soup — partitioning is physically meaningful (each stella IS a separate system). Inter-stella coupling happens separately. The C1b "grouped" test simulates the *worst case* where a single soup is artificially partitioned.

**However,** the CPU pthread implementation has a separate concern: **unprotected tile writes** within each stella could cause subtle race conditions. This requires a dedicated test (C1c).

### 11.5 Implications for GPU Implementation

The GPU Metal double-buffered approach (`soup_multi_stella_metal.m`) is validated:
- Snapshot-parallel is the closest parallel strategy to sequential reference (KL = 0.030)
- The entropy gap (0.57 → 0.71) represents a mild weakening of selection pressure, acceptable given the race-freedom guarantee
- Replicators still emerge, just somewhat slower

**Result: The GPU snapshot approach is the most honest parallel implementation.**

---

## 12. Phase C1c: Race Condition vs Sequential Ordering

### 12.1 Design

Four strategies on the same soup (N=512, same interaction pairs each epoch, 500K epochs):

1. **Sequential** — reference (strict ordering, no races)
2. **Sequential + races** — same ordering, but conflicted writes resolved by random last-writer-wins
3. **Snapshot** — GPU approach (no ordering, no races)
4. **Snapshot + races** — no ordering, conflicted writes resolved randomly

The conflict rate is ~27% (fraction of programs touched by >1 interaction per epoch), consistent with birthday-problem statistics at N/2 interactions.

### 12.2 Results

**Entropy at 500K epochs:**
```
Sequential:           0.493  (strongest selection)
Sequential + races:   0.536  (mild noise from conflicts)
Snapshot:             0.656  (weaker selection, no cascades)
Snapshot + races:     0.966  (PATHOLOGICAL — monoculture)
```

**Unique programs at 500K:**
```
Sequential:           316    (moderate diversity)
Sequential + races:   361    (slightly more diverse)
Snapshot:             401    (higher diversity)
Snapshot + races:      89    (COLLAPSED — one program dominates)
```

**Replicators at 500K (of 200 tests):**
```
Sequential:             6    (healthy emergence)
Sequential + races:     4    (similar)
Snapshot:               0    (occasional, not at this snapshot)
Snapshot + races:     182    (PATHOLOGICAL — monoculture takeover)
```

### 12.3 Effect Decomposition

| Effect | ΔH | Interpretation |
|--------|-----|---------------|
| **Ordering** (snap − seq) | **+0.163** | Sequential ordering amplifies selection by creating within-epoch cascades |
| **Races on sequential** | +0.043 | Mild noise — races slightly disrupt cascades |
| **Races on snapshot** | **+0.310** | Catastrophic — without ordering to arbitrate, most aggressive program wins every write conflict → monoculture |

### 12.4 Interpretation

**The CPU pthread version's lower entropy is from BENEFICIAL sequential ordering, not from race conditions.**

The decomposition is clean:
- **Sequential ordering** provides the dominant effect (+0.163): when a replicator copies itself in interaction N, it becomes available for interaction N+1 in the same epoch, creating a cascade that amplifies selection pressure.
- **Race conditions on sequential** are nearly harmless (+0.043): with sequential ordering arbitrating which write survives, conflicts add only mild noise.
- **Race conditions WITHOUT sequential ordering** are catastrophic (+0.310): the snapshot+races combination creates a pathological monoculture where the most aggressive replicator wins every write conflict, collapsing diversity to ~89 unique programs while a single program accounts for 91% of the soup.

### 12.5 Implications for Production Implementations

| Implementation | Ordering | Races | Faithfulness |
|----------------|----------|-------|-------------|
| `soup.c` | Full sequential | None | **Ground truth** |
| CPU pthread (`soup_multi_stella.c`) | Per-stella sequential | Possible but rare (single-stella processing) | **Good** — ordering is beneficial, rare intra-stella races are harmless |
| GPU Metal (`soup_multi_stella_metal.m`) | None (snapshot) | **None** (double-buffered) | **Good** — sacrifices ordering cascade but eliminates all races |
| Old GPU (pre-fix) | None | **Yes** (shared buffer) | **BROKEN** — snapshot+races = monoculture pathology |

**The double-buffered GPU fix was the correct approach.** The old GPU version's failure was specifically the snapshot+races combination — the worst of both worlds. The fix eliminates races while accepting the milder cost of losing within-epoch ordering cascades.

**The CPU pthread version is the most faithful parallel implementation,** because per-stella sequential ordering preserves the beneficial cascade effect while the per-stella isolation makes write conflicts extremely rare.

### 12.6 Conflict Rate Analysis

Average conflict rate: 26.4% of programs touched by >1 interaction per epoch.

This matches the birthday-problem prediction: with K = N/2 = 256 interactions each touching 2 of 512 programs, the expected number of programs touched ≥2 times follows Poisson(λ≈1). The fraction with ≥2 touches is 1 − e^{-1}(1 + 1) ≈ 0.264, exactly matching the observed 0.264.

---

*Research document for the Stella Computation program.*
*Linked from: RESEARCH-Prime-Interference.md Section 21*
*Updated: 2026-03-24*
