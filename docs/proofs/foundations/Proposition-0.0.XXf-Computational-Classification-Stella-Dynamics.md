# Proposition 0.0.XXf: Computational Classification of Stella Dynamics

## Status: 🔶 NOVEL ✅ VERIFIED — STELLA COMPUTATION IS STANDARD (P), SIGNIFICANCE IS INFORMATION-THEORETIC

**Purpose:** Classify the computational complexity of the Stella Soup VM dynamics, establishing that the stella computes in P with no advantage over standard Turing machines, and that the framework's computational significance is information-theoretic (K-complexity ~205 bits) rather than complexity-theoretic.

**Created:** 2026-03-22
**Origin:** C-series experiments (C1–C7) in [RESEARCH-Stella-Computation.md](../../../stella_genesis/RESEARCH-Stella-Computation.md)

**Dependencies:**
- ✅ Proposition 0.0.XXd (Computational Universality of CG Primitives) — StellaLang is Turing-complete; Soup VM definition
- ✅ Proposition 0.0.XXb (Bootstrap Computability) — K-complexity ~205 bits; bootstrap in P
- ✅ Theorem 0.0.XXc (Gödel-Bootstrap Separation) — Bootstrap in Δ₁
- ✅ Proposition 0.0.XXe (Continuum Self-Replicating Fields) — Fisher-KPP continuum limit
- ✅ Definition 0.1.1 (Stella Octangula Boundary Topology) — χ = 4, two S² components
- ✅ Definition 0.1.2 (Three Color Fields) — Z₃ phase assignment
- ✅ Standard: Circuit complexity (NC, P, BQP) — Arora & Barak
- ✅ Standard: Cellular automata universality (Rule 110) — Cook 2004
- ✅ Standard: Topological quantum computation — Kitaev 2003, Nayak et al. 2008
- ✅ Standard: Spherical braid groups — Fadell & Van Buskirk 1962
- ✅ Standard: Fisher-KPP equation — Fisher 1937, Kolmogorov-Petrovsky-Piskunov 1937
- ✅ Standard: Potts model — Potts 1952
- ✅ Standard: Random intersection graphs — Karoński, Scheinerman & Singer-Cohen 1999

**Enables:**
- Definitive answer to whether the stella supports non-standard computation
- Clarification that the framework's power lies in information compression, not computational speedup
- Formal separation between the stella's information-theoretic efficiency and complexity-theoretic ordinariness

**Verification:**
- C1: `stella_genesis/phase_c1.c` → `phase_c1_results.json`
- C3: `stella_genesis/phase_c3.c` → `phase_c3_results.json`
- C4: `stella_genesis/phase_c4.c` → `phase_c4_results.json`
- C5: `stella_genesis/phase_c5.c` → `phase_c5_results.json`
- C7: `stella_genesis/phase_c7.c` → `phase_c7_results.json`

---

## Executive Summary

The C-series experiments tested five independent routes by which the stella's geometry might support non-standard computation. All five returned null results at Level 0 (re-encoding only). The stella is computationally equivalent to a standard Turing machine.

| Route Tested | Experiment | Result | Level |
|:-------------|:----------:|:------:|:-----:|
| P-completeness of soup dynamics | C1 | NULL — dynamics in NC | 0 |
| Z₃ interference as resource | C3 | NULL — classical, O(T·N) simulable | 0 |
| Topological computation on χ = 4 | C4 | NULL — genus 0, no TQC | 0 |
| Analog advantage via continuum limit | C5 | NULL — PDE = standard iteration | 0 |
| Overall classification | C7 | P (standard TM), Level 1 only | 0 |

**The honest answer:** The stella is a Turing-complete ternary cellular automaton with Z₃ symmetry, in the same complexity class (P) as Rule 110 and standard Turing machines. Its significance is not that it computes *differently*, but that it computes *so much from so little* — ~205 bits of input (Prop 0.0.XXb) yields dozens of physical constants.

---

## 1. Statement

**Proposition 0.0.XXf (Computational Classification of Stella Dynamics).**

Let $\mathcal{V}$ be the Stella Soup VM (Prop 0.0.XXd) operating on $N$ programs over $T$ epochs.

**(a) Within-epoch dynamics lie in NC.**
The critical path of the interaction dependency graph within any single epoch satisfies:

$$\text{CP}(N) \;=\; (0.55 \pm 0.03)\,\log_2 N + O(1)$$

Consequently, each epoch is parallelizable with a parallelism factor of $\Theta(N / \log N)$.

**(b) Classical simulation is efficient.**
The Z₃ interference pattern on $\partial\mathcal{S}$ with $N$ vertices over $T$ time steps is classically simulable in $O(T \cdot N)$ time. The Z₃ phases are classical labels, not quantum superpositions; no entanglement is generated.

**(c) Topological computation is unavailable.**
The spherical braid group $B_n(S^2)$ on each component $S^2$ of $\partial\mathcal{S}$ is nontrivial but cannot support topological quantum computation: the genus-0 surface has non-degenerate ground state ($\mathcal{D}^{2g} = 1$ for $g = 0$), and the stella's vertices are fixed geometric points, not mobile quasiparticle excitations. The χ = 4 topology provides 8-copy redundancy but no topological error correction beyond simple majority voting.

**(d) No analog advantage.**
The Fisher-KPP continuum limit (Prop 0.0.XXe) is efficiently discretizable. Its steady state is a contractive fixed point with exponential convergence. The eigenvalue problem and PDE relaxation are both $O(N^3)$ and $O(T \cdot N)$ respectively — no computational gap between analog and digital.

**(e) Overall classification.**
$\mathcal{V}$ is a Turing-complete cellular automaton in the complexity class **P**. It is in the same complexity class as Rule 110 and standard Turing machines, though it differs in internal structure: within-epoch dynamics are in NC (more parallel than Rule 110's P-complete steps), while across-epoch dynamics are sequential. The framework achieves **Level 1 (Natural computation)** only: some problems have more natural expression in stella language (Z₃ coloring, {2,3}-factorization from topology), but there is no complexity-theoretic advantage.

---

## 2. Hierarchy of Computational Claims

The proposition is organized against a five-level hierarchy, testing each level explicitly:

| Level | Claim | Evidence Needed | Verdict |
|:-----:|:------|:----------------|:-------:|
| 0 | Re-encoding (same computation, different notation) | Nothing — already have this | ✅ Confirmed |
| 1 | Natural computation (some problems expressed more naturally) | Problem class where stella formulation is shorter | ✅ Confirmed |
| 2 | Constant-factor advantage (same class, better constants) | Benchmarks against classical algorithms | ❌ Not found |
| 3 | P-completeness (inherently sequential) | Prove soup dynamics are P-complete under NC reductions | ❌ Refuted (C1) |
| 4 | Analog advantage (continuum escapes discrete bounds) | PDE steady state faster than any discrete method | ❌ Refuted (C5) |

The stella reaches Level 1 but no higher.

---

## 3. Proof of (a): Within-Epoch Dynamics in NC

### 3.1 Setup

In each epoch of $\mathcal{V}$, $K = N/2$ interactions are drawn uniformly at random, each touching 2 of $N$ programs. An interaction $I_j$ depends on $I_i$ (within the same epoch) if and only if they share at least one program.

### 3.2 Dependency graph analysis

The dependency graph $G = (V, E)$ has $|V| = K$ interaction nodes and an edge $(I_i, I_j)$ when $I_i$ and $I_j$ share a program. Since each interaction touches 2 programs, the expected degree of each node is:

$$\mathbb{E}[\deg] = 2 \cdot \frac{2(K-1)}{N} \approx 2$$

for $K = N/2$. The graph is sparse (constant average degree), so by standard results on random intersection graphs (Karoński, Scheinerman & Singer-Cohen 1999), the longest path (critical path) scales as $O(\log N)$.

### 3.3 Numerical verification (C1)

| N | log₂(N) | Mean CP | CP/log₂(N) | Parallelism |
|------:|:-------:|:-------:|:----------:|:-----------:|
| 32 | 5.0 | 3.17 | 0.634 | 3.8× |
| 128 | 7.0 | 4.52 | 0.646 | 11.6× |
| 512 | 9.0 | 5.71 | 0.634 | 38.2× |
| 2,048 | 11.0 | 6.73 | 0.611 | 132.5× |
| 8,192 | 13.0 | 7.68 | 0.591 | 471.9× |
| 16,384 | 14.0 | 8.11 | 0.580 | 898.9× |

Log fit: $\text{CP} = 0.546 \cdot \log_2 N + 0.649$ with excellent R².

### 3.4 Implication

Snapshot-parallel execution (all interactions read from epoch-start state) produces entropy divergence of only 0.092 from sequential execution (N = 512, 200K epochs). The GPU failure reported in Prop 0.0.XXd §4.6 was caused by **race conditions from lack of epoch barriers**, not P-completeness. A barrier-synchronized parallel implementation preserves self-organization.

---

## 4. Proof of (b): Classical Simulation of Z₃ Interference

### 4.1 Z₃ phases are classical in the Soup VM

The color phases $\omega_k = e^{2\pi i c(k)/3}$ assigned to vertices are **deterministic classical labels** derived from the Z₃ center of SU(3) (Def 0.1.2). In the Soup VM computational model, they do not exist in superposition — they are fixed algebraic assignments determined by the geometric structure. The coupling matrix $M_{ij} = \omega_i \bar\omega_j \exp(-d_{ij}^2/2\sigma^2)$ is computed by classical matrix operations.

**Important distinction:** The Z₃ phases in the Soup VM are pre-geometric labels encoding the stella's algebraic structure. The quantum nature of QCD color charge — where color states genuinely superpose and entangle — emerges at a later stage of the framework (Phases 1–3, after spacetime and gauge fields are constructed). The Soup VM operates before this emergence, at the level where color is a discrete geometric assignment, not a quantum degree of freedom.

### 4.2 No quantum speedup

The Z₃ Potts energy minimization (C3, Part C) shows that soup-like Metropolis dynamics perform comparably to simulated annealing — not better:

| N | Metropolis | Annealing | Random | Winner |
|----:|:---------:|:---------:|:------:|:------:|
| 20 | −28.90 | −28.68 | −16.60 | Metropolis |
| 50 | −74.35 | −74.28 | −26.73 | Metropolis |
| 100 | −151.25 | −151.25 | −38.38 | Tie |
| 200 | −298.05 | −298.05 | −55.65 | Tie |

Z₃ interference provides structure (visibility 0.6–1.0 depending on σ) but this is classical wave interference, not a quantum resource.

### 4.3 Simulation cost

A classical computer replays the interaction transcript in $O(T \cdot N)$ time — each of $T$ epochs processes $N/2$ interactions, each modifying 2 programs in $O(1)$.

---

## 5. Proof of (c): No Topological Quantum Computation

### 5.1 Braiding group on S²

Each component of $\partial\mathcal{S}$ is homeomorphic to $S^2$ (Def 0.1.1). The **spherical braid group** $B_n(S^2)$ is the quotient of the Artin braid group $B_n$ by the sphere relation (Fadell & Van Buskirk 1962):

$$(\sigma_1 \sigma_2 \cdots \sigma_{n-1})(\sigma_{n-1} \cdots \sigma_2 \sigma_1) = 1$$

This relation arises because the "full twist" — dragging one strand around all others — can be contracted by sliding over the back of the sphere. For the stella's 4 vertices per component, $B_4(S^2)$ is infinite but torsion-rich (elements of order 2n = 8, 2(n-1) = 6, and 2(n-2) = 4). Crucially, $B_n(S^2)$ is **not** the symmetric group $S_n$; there is a surjection $B_n(S^2) \twoheadrightarrow S_n$ with nontrivial kernel $P_n(S^2)$ (the pure spherical braid group).

Despite this nontrivial braid structure, the stella cannot support topological quantum computation for two independent reasons:

1. **No ground state degeneracy (genus 0).** On a closed surface of genus $g$, a topological phase with total quantum dimension $\mathcal{D}$ has ground state degeneracy $\mathcal{D}^{2g}$ (Kitaev 2003). For $S^2$ ($g = 0$), this gives $\mathcal{D}^0 = 1$ — exactly one ground state, no room to store quantum information topologically. TQC requires genus $\geq 1$ (e.g., a torus gives $\mathcal{D}^2$ states).

2. **Vertices are fixed geometric points, not quasiparticles.** The stella's vertices are fixed positions in $\mathbb{R}^3$, not mobile quasiparticle excitations of a topological Hamiltonian. Braiding requires adiabatic transport of anyonic excitations around each other; fixed lattice sites cannot braid.

### 5.2 Error correction from χ = 4

The stella's two disconnected S² components provide 8 vertices total. Error correction by hierarchical T₊/T₋ voting does NOT improve over simple 8-copy majority voting (C4, Part C). The topology contributes nothing beyond extra copies.

| Error rate | χ = 4 fidelity | χ = 2 fidelity | Advantage |
|:----------:|:--------------:|:--------------:|:---------:|
| 0.10 | 99.93% | 98.41% | +1.5% (from 8 > 4 copies) |
| 0.25 | 97.57% | 89.60% | +8.0% (from 8 > 4 copies) |
| 0.40 | 84.83% | 73.35% | +11.5% (from 8 > 4 copies) |

### 5.3 Cross-surface braiding impossible

The 16 cross-surface particle pairs (one particle on T₊, one on T₋) **cannot braid** because the components are topologically disconnected ($\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$). Only the 12 same-surface pairs can exchange. While these same-surface exchanges generate the spherical braid group $B_4(S^2)$ (which is infinite and non-abelian), neither the genus-0 ground-state degeneracy obstruction nor the fixed-vertex obstruction is removed by the braid structure alone.

---

## 6. Proof of (d): No Analog Advantage

### 6.1 Fisher-KPP discretization

The continuum limit (Prop 0.0.XXe) is a bilayer Fisher-KPP reaction-diffusion equation (Fisher 1937, KPP 1937) on the stella graph. The steady state depends on the diffusion/reaction ratio $D/r$:

- Low $D$ ($\leq 0.01$): homogeneous confinement (all vertices → 1.0)
- High $D$ ($\geq 0.5$) with low $r$: component separation (T₊ → 1.0, T₋ → 0.0) — structurally analogous to a confinement/deconfinement transition
- High $r$ overcomes diffusive separation

**Universality caveat:** This confinement/deconfinement mapping is **structural, not quantitative**. Prop 0.0.XXe §5.3 establishes that the soup's error catastrophe is in the **Directed Percolation (DP)** universality class, not the equilibrium Z₃ Potts class relevant for SU(3) deconfinement via Svetitsky-Yaffe. The Z₃ symmetry and transition topology are shared, but the critical exponents differ.

### 6.2 Convergence

The steady state is a contractive fixed point (Prop 0.0.XXe, Claim 3). Any iterative method converges exponentially with relaxation time $\sim 1/r$.

### 6.3 Complexity comparison

| Problem | Algebraic | Iterative | Gap? |
|:--------|:---------:|:---------:|:----:|
| Eigenvalue | $O(N^3)$ (Jacobi) | $O(N^3)$ (power iteration) | No |
| Steady state | N/A | $O(T \cdot N)$ | No |

The PDE is efficiently simulable by standard numerical methods. The interesting physics (deconfinement transition) is a standard bifurcation in a reaction-diffusion system, not a novel computational phenomenon.

---

## 7. Proof of (e): Classification in P

### 7.1 Turing completeness

StellaLang is Turing-complete (Prop 0.0.XXd). The Soup VM extends StellaLang with two heads (T₊, T₋) and 9 instructions encoded as trit pairs. It simulates any Turing machine.

### 7.2 Comparison with Rule 110

The stella soup is a ternary (3-state) cellular automaton with local update rules. Rule 110 is a binary (2-state) CA that is also Turing-complete (Cook 2004). Both are in the complexity class **P** and both are Turing-complete. However, they are not computationally equivalent in the circuit complexity sense:

| Property | Stella Soup | Rule 110 |
|:---------|:-----------|:---------|
| Turing-complete | Yes (Prop 0.0.XXd) | Yes (Cook 2004) |
| Complexity class | P | P |
| Within-step parallelism | **NC** (CP = O(log N)) | P-complete (inherently sequential per step) |
| Alphabet | Ternary (Z₃) | Binary (Z₂) |
| Interaction topology | Random | Fixed 1D lattice |
| Self-organization | Yes (from random ICs) | Yes (from random ICs) |

The stella's within-epoch dynamics are **more parallel** than Rule 110: each epoch's interaction graph has logarithmic critical path (NC), whereas a single Rule 110 step on $N$ cells is P-complete. However, across-epoch dynamics are sequential in both systems (epoch $t+1$ depends on epoch $t$). Both systems occupy the same overall complexity class **P**, but their internal structure differs.

### 7.3 Comparison with known models

| Model | Same Class? | Reason |
|:------|:----------:|:-------|
| Classical TM | **Yes (P)** | StellaLang is Turing-complete |
| Quantum (BQP) | **Weaker** | Z₃ phases are classical, no entanglement |
| Topological QC | **Weaker** | S² has genus 0 (non-degenerate ground state); vertices are fixed, not mobile anyons |
| Analog (BSS) | **No** | Fisher-KPP efficiently discretizable |
| CA (Rule 110) | **Same class (P)** | Both Turing-complete; stella within-epoch is NC, Rule 110 within-step is P-complete |

---

## 8. The Information-Theoretic Significance

### 8.1 The real surprise

The stella computes the SAME things as a standard Turing machine, but with extraordinarily compressed input. The 205-bit bootstrap (Prop 0.0.XXb) produces predictions for dozens of physical constants — gauge group, mass spectrum, gravitational coupling.

This is not a new way of computing. It is a maximally efficient **encoding** of physics.

### 8.2 Level 1: Natural computation

Some problems have more natural expression in stella language:

- **Z₃ coloring problems** map directly to the stella's trit alphabet
- **{2, 3}-factorization** is encoded in the stella's eigenvalue ratios (H6, [RESEARCH-Prime-Interference.md](../../../stella_genesis/RESEARCH-Prime-Interference.md) §18)
- **Confinement/deconfinement transitions** are native to the bilayer Fisher-KPP dynamics

These are notational advantages (shorter formulations), not computational advantages (faster solutions).

### 8.3 What the stella cannot do

- Outperform a quantum computer (no superposition or entanglement)
- Perform topological quantum computation (S² genus 0: non-degenerate ground state; fixed vertices cannot braid)
- Hypercompute via analog dynamics (Fisher-KPP is discretizable)
- Exploit P-completeness for sequential advantage (within-epoch dynamics are in NC)

---

## 9. Consistency Checks

### 9.1 Dimensional analysis

All complexity claims are stated in terms of the natural parameters: $N$ (soup size), $T$ (epochs), $K$ (interactions per epoch = $N/2$). No dimensional inconsistencies.

### 9.2 Limiting cases

- **$N = 1$:** Trivial — single program, no interactions, CP = 0. ✓
- **$N \to \infty$:** CP grows as $0.55 \log_2 N$, parallelism as $N/\log N$. ✓
- **$T = 0$:** No evolution, simulation cost = 0. ✓
- **$\sigma \to 0$:** Z₃ coupling becomes nearest-neighbor, visibility → 1. ✓
- **$\sigma \to \infty$:** Uniform coupling, visibility → 0, no Z₃ structure. ✓

### 9.3 Cross-verification

- C1 null result consistent with Prop 0.0.XXd's GPU failure diagnosis (race conditions, not P-hardness)
- C3 null result consistent with Prop 0.0.XXb's finding that bootstrap is in P (no quantum speedup needed)
- C5 null result consistent with Prop 0.0.XXe's contractive fixed-point structure

---

## 10. Open Questions

1. **Across-epoch shortcuts:** Can $T$ epochs ever be computed in fewer than $T$ sequential steps? This is a standard question for iterative dynamical systems and does not require stella-specific investigation.

2. **Quantum stella:** If the Z₃ phases were promoted to genuine quantum superpositions (qutrit amplitudes), would the resulting system gain BQP power? This would require a fundamentally different physical setup — the current framework's Z₃ phases are classical.

3. **Information-theoretic lower bound:** Is 205 bits provably minimal for the bootstrap, or could further geometric derivations compress it further? (See Prop 0.0.XXb §9.11 for current K-tracking.)

---

## References

1. **Cook, M.** (2004). "Universality in Elementary Cellular Automata." *Complex Systems* 15(1): 1–40.
2. **Kitaev, A.** (2003). "Fault-tolerant quantum computation by anyons." *Annals of Physics* 303(1): 2–30. arXiv: quant-ph/9707021.
3. **Nayak, C., Simon, S. H., Stern, A., Freedman, M., & Das Sarma, S.** (2008). "Non-Abelian anyons and topological quantum computation." *Rev. Mod. Phys.* 80: 1083–1159.
4. **Arora, S. & Barak, B.** (2009). *Computational Complexity: A Modern Approach.* Cambridge University Press.
5. **Agüera y Arcas, B., et al.** (2024). "Computational Life: How Well-formed, Self-replicating Programs Emerge from Simple Interaction." arXiv:2406.19108.
6. **Fadell, E. & Van Buskirk, J.** (1962). "The braid groups of E² and S²." *Duke Math. J.* 29: 243–257.
7. **Fisher, R. A.** (1937). "The wave of advance of advantageous genes." *Annals of Eugenics* 7: 355–369.
8. **Kolmogorov, A. N., Petrovsky, I. G., & Piskunov, N. S.** (1937). "A study of the diffusion equation with increase in the amount of substance." *Bull. Moscow Univ. Math. Mech.* 1: 1–26.
9. **Potts, R. B.** (1952). "Some generalized order-disorder transformations." *Math. Proc. Cambridge Phil. Soc.* 48(1): 106–109.
10. **Karoński, M., Scheinerman, E. R., & Singer-Cohen, K. B.** (1999). "On random intersection graphs: The subgraph problem." *Combinatorics, Probability and Computing* 8(1-2): 131–159.

---

**Multi-Agent Verification:** [Proposition-0.0.XXf-Multi-Agent-Verification-2026-03-22.md](../verification-records/Proposition-0.0.XXf-Multi-Agent-Verification-2026-03-22.md) — Verdict: ✅ VERIFIED (all five fixes applied)

**Adversarial Physics Verification:** [proposition_0_0_XXf_adversarial_verification.py](../../../verification/foundations/proposition_0_0_XXf_adversarial_verification.py) — All 7 tests PASSED | [Plot](../../../verification/plots/Prop_0_0_XXf_adversarial_verification.png)

**Lean 4 Formalization:** [Proposition_0_0_XXf.lean](../../../lean/ChiralGeometrogenesis/Foundations/Proposition_0_0_XXf.lean) — 9 parts, 2 `sorry` remaining (limit theorems)

*Proposition 0.0.XXf — Computational Classification of Stella Dynamics*
*Evidence: C-series experiments C1, C3, C4, C5, C7 (2026-03-22)*
*Linked from: [RESEARCH-Stella-Computation.md](../../../stella_genesis/RESEARCH-Stella-Computation.md) §10.5*
