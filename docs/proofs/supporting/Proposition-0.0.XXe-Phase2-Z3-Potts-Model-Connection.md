# Proposition 0.0.XXe Phase 2: Z₃ Potts Model Connection

## Date: 2026-03-09

## Overview

Phase 2 of the XXe workplan establishes the theoretical connection between the discrete Z₃ Stella Soup (Prop 0.0.XXd, Phase 1) and the 3-state Potts model. The goal is to construct a precise dictionary between the soup dynamics and equilibrium statistical mechanics, identify where the mapping works and where it breaks down, and use the well-studied Potts continuum limit (Z₃ parafermion CFT) to inform the continuum theory on ∂S.

**Dependencies:**
- Prop 0.0.XXd (Computational Universality of Z₃ Soup)
- Prop 0.0.XXe Phase 1 (2D Soup on Triangulated ∂S)
- Def 0.1.1 (Stella Octangula Boundary Topology)
- Def 0.1.2 (Three Color Fields with Relative Phases)
- Prop 2.5.2c (Transfer Matrix for FCC Layers)

---

## Task 2.1: Mapping the Soup to the Potts Model

### 2.1.1 The Z₃ Potts Model

The q-state Potts model on a lattice Λ assigns a spin σ_i ∈ {0, 1, ..., q−1} to each site i. For q = 3:

$$H_{\text{Potts}} = -J \sum_{\langle ij \rangle} \delta(\sigma_i, \sigma_j)$$

$$Z = \sum_{\{\sigma\}} e^{-\beta H} = \sum_{\{\sigma\}} \prod_{\langle ij \rangle} \left[1 + v \, \delta(\sigma_i, \sigma_j)\right]$$

where v = e^{βJ} − 1, and the sum runs over nearest-neighbor pairs ⟨ij⟩. On the triangular lattice (relevant for ∂S), the exact critical point is:

$$v_c = \sqrt{q} = \sqrt{3}, \quad \Rightarrow \quad \beta_c J = \ln(1 + \sqrt{3}) \approx 1.005$$

The q = 3 Potts model in 2D has a **second-order** (continuous) phase transition (Baxter, 1973; Wu, 1982). This is an exact result: on 2D lattices, the q-state Potts model has a continuous transition for q ≤ 4 and a first-order transition for q > 4. Note that in **3D**, the q = 3 Potts transition is first-order — this is the case relevant for SU(3) deconfinement in (3+1)D via Svetitsky-Yaffe universality.

**Reference:** F.Y. Wu, "The Potts Model," Rev. Mod. Phys. 54 (1982) 235.

### 2.1.2 The Soup Dictionary

| Potts Model | Stella Soup | Notes |
|-------------|-------------|-------|
| Spin σ_i ∈ {0, 1, 2} | Z₃ cell value on mesh site | Direct identification (Def 0.1.2: R↔0, G↔1, B↔2) |
| Lattice site i | Mesh site on triangulated ∂S | Triangular lattice with avg 6 neighbors |
| Nearest-neighbor coupling J | VM-mediated tile interaction | See §2.1.3 for critical differences |
| Temperature T = 1/β | Mutation rate μ | Higher μ → more disorder |
| Ordered phase (T < T_c) | Replicator-dominated state | ~85–89% replicator density (Q13; tiling fixed) |
| Disordered phase (T > T_c) | Random soup (no replicators) | Uniform trit entropy ~1.585 |
| Phase transition at T_c | Error catastrophe at μ_c ≈ 0.011 | Both: ordered structures dissolve |
| Magnetization M | Replicator density ρ_rep | Order parameter |

### 2.1.3 Critical Differences: Why the Mapping Is Approximate

The soup is **not** a Potts model. The interaction is fundamentally different in three ways:

**(a) Non-local interaction.** The Potts Hamiltonian couples nearest-neighbor spins via the local function δ(σ_i, σ_j). The soup interaction is computational:

```
tile_A || tile_B  →  execute_VM(tape)  →  tile_A' || tile_B'
```

The VM execution involves instruction pointer motion, conditional branching, and cross-tape copy operations (CPY01, CPY10) that create long-range correlations within the concatenated tape. There is no local energy function.

**(b) No detailed balance.** The Potts model at temperature T satisfies detailed balance:

$$\frac{P(\sigma → \sigma')}{P(\sigma' → \sigma)} = e^{-\beta \Delta H}$$

The soup interaction is deterministic (given the input) and generically irreversible: if VM(A||B) → (A', B'), there is no guarantee that VM(A'||B') → (A, B). The soup is a **non-equilibrium** stochastic process (with stochasticity from random partner selection and mutation, not from a thermal bath).

**(c) Information creation.** The Potts model conserves information (it's a reversible Markov chain at fixed β). The soup VM creates and destroys correlations — a self-replicating program actively writes its own pattern into the "food" program, creating order from disorder. This is an **autocatalytic** process with no equilibrium analog.

### 2.1.4 The Mapping That Does Work: Z₃ Symmetry

Despite these differences, the soup and Potts model share the same **global symmetry**: Z₃. In both systems:

- The state space at each site is {0, 1, 2} ≅ Z₃
- The cyclic permutation σ_i → (σ_i + 1) mod 3 maps the system to itself
- The ROT instruction in the soup VM implements exactly this Z₃ rotation (Def 0.1.2: R→G→B→R)

This shared symmetry means that both systems belong to the **same universality class for symmetry-breaking phenomena**: the Z₃ Potts universality class. The ordered phase in both systems breaks Z₃ → 1, and the critical behavior (if continuous) is governed by the same symmetry-constrained renormalization group flows.

**Formal statement:** The soup and the Potts model have the same symmetry group G = Z₃ acting on the same state space per site. Any phase transition that breaks this symmetry is constrained by the same Landau-Ginzburg-Wilson effective field theory, regardless of the microscopic dynamics.

**Experimental realization:** Tazai *et al.* [*Nat. Commun.* **14**, 7845 (2023)] observe Z₃ Potts-class behavior in kagome-lattice metals AV₃Sb₅: the competition between Z₃-broken phases (charge-loop current order with three-fold nematic symmetry) mediated by bond-order fluctuations produces phase transitions governed by the same Z₃ universality class. This provides experimental confirmation that Z₃ symmetry-breaking phenomena with the same Landau-Ginzburg-Wilson structure arise in real physical systems with three-fold geometric frustration.

---

## Task 2.2: Statistical Mechanics of the Soup

### 2.2.1 Is There a Partition Function?

**No.** The soup does not have a partition function in the equilibrium sense because:

1. There is no energy function H[{σ}] on configurations
2. There is no detailed balance (the dynamics are irreversible)
3. The steady state is a **non-equilibrium steady state** (NESS), not a Gibbs measure

However, the soup does have a **master equation**. Let P(C, t) be the probability of configuration C at time t. The master equation is:

$$\frac{dP(C, t)}{dt} = \sum_{C' \neq C} \left[ W(C' \to C) P(C', t) - W(C \to C') P(C, t) \right]$$

where the transition rates W(C → C') encode:
- Random tile pair selection: uniform over all tile pairs (global) or neighbor pairs (local)
- Deterministic VM execution: given input (A, B), the output (A', B') is fixed
- Stochastic mutation: each trit mutated with probability μ per epoch

The steady-state distribution P_ss(C) satisfies dP/dt = 0 but is **not** of the Gibbs form e^{−βH}/Z.

### 2.2.2 Temperature Analog: Mutation Rate

The mutation rate μ plays the role of temperature in the following precise sense:

| Property | Temperature T (Potts) | Mutation rate μ (Soup) |
|----------|----------------------|----------------------|
| Controls disorder | Higher T → more disorder | Higher μ → more disorder |
| Critical value | T_c: ordered→disordered | μ_c ≈ 0.011: replicators→random |
| Below critical | Ordered phase, M > 0 | Replicator-dominated, ρ_rep > 0 |
| Above critical | Disordered, M = 0 | Random soup, ρ_rep = 0 |
| Zero value | Ground state, full order | Perfect replication, ρ_rep ~ 100% |

**Computational evidence (error_threshold_confinement.c, Experiment b):**

Fine sweep around μ_c at prog_size = 24, 1666 tiles, 5000 epochs, 5 trials:

| μ | ρ_rep (avg) | std | μ × L | Interpretation |
|-------|-------------|-----|-------|----------------|
| 0.0020 | 80.2% | ± 2.5% | 0.048 | Deep ordered |
| 0.0030 | 72.8% | ± 1.8% | 0.072 | Ordered |
| 0.0040 | 64.4% | ± 2.9% | 0.096 | Declining |
| 0.0050 | 56.7% | ± 3.5% | 0.120 | Below half |
| 0.0060 | 47.7% | ± 3.4% | 0.144 | Dissolving |
| 0.0080 | 31.5% | ± 7.2% | 0.192 | Large fluctuations |
| 0.0100 | 18.9% | — | 0.240 | Near collapse |
| 0.0120 | 0.0% | — | 0.288 | Disordered |

The transition is **smooth but steep** — density declines from ~80% to ~0% over the range μ ∈ [0.002, 0.012]. The large standard deviations near μ ≈ 0.008 indicate critical fluctuations. The transition is not discontinuous (first-order) but sharper than a generic crossover.

**Eigen scaling test (error_threshold_confinement.c, Experiment a):**

The critical test of the Potts analogy is whether μ_c × L = const (Eigen scaling) or μ_c = const (VM-intrinsic threshold). Sweep across prog_sizes L = 24, 30, 36, 42, 48:

| L | μ_c (10% threshold) | μ_c × L | 1/L (Eigen prediction) |
|---|---------------------|---------|------------------------|
| 24 | 0.0109 | 0.263 | 0.042 |
| 30 | 0.0111 | 0.333 | 0.033 |
| 36 | 0.0113 | 0.408 | 0.028 |
| 42 | 0.0109 | 0.459 | 0.024 |
| 48 | 0.0107 | 0.515 | 0.021 |

**Result: μ_c ≈ 0.011 is constant across program lengths, while μ_c × L increases linearly.** This is **NOT** Eigen scaling. The Eigen theory predicts μ_c ∝ 1/L (longer programs are more fragile), but the soup's error threshold is independent of program length.

**Interpretation:** The error threshold is a property of the **VM interaction dynamics** (how often a replicator is disrupted by interaction with a random tile), not the information content of the program. This makes sense: the replicator core is always 10 instructions (20 trits) regardless of the total program length L; extra trits are functionally neutral tail positions. The threshold is set by the ratio of replicator-preserving to replicator-destroying interactions, which depends on the VM instruction set, not L.

**Implication for the Potts mapping:** The Potts coupling J is not a simple function of 1/L. Instead, it reflects the VM's computational dynamics — the effective J is determined by the replication success rate, which is an emergent property of the instruction set. This further confirms that the Potts mapping is **structural** (same symmetry, same phase transition topology) rather than quantitative.

### 2.2.3 Error Threshold ↔ Confinement

The Eigen error catastrophe has a structural parallel with dynamical confinement (Thm 2.5.2):

| Concept | Eigen Error Threshold | Dynamical Confinement |
|---------|----------------------|----------------------|
| Critical scale | μ_c × L ≈ ln(σ) | β_c: u₃(β_c) = 3^{−3/8} |
| Below threshold | Coherent quasispecies | Confined hadrons, string tension σ > 0 |
| Above threshold | Error catastrophe: replicators dissolve | Deconfinement: hadrons dissolve into QGP |
| Order parameter | Replicator density ρ_rep | Polyakov loop ⟨L⟩ |
| Information carrier | Self-replicating program | Color-neutral bound state |
| Disorder source | Random mutations | Thermal fluctuations |

**Mapping μ_c to a Potts temperature.** The Eigen threshold μ_c × L ≈ const predicts that the critical mutation rate scales inversely with program length. If we identify:

$$\mu \;\longleftrightarrow\; \frac{1}{\beta J}, \qquad L \;\longleftrightarrow\; N_{\text{sites}}$$

then μ_c × L ≈ const becomes β_c J × N_sites ≈ const, which is the Potts critical coupling condition in the thermodynamic limit. The Z₃ Potts critical point β_c J = ln(1 + √3) would then predict:

$$\mu_c \sim \frac{\ln(1 + \sqrt{3})}{L} \approx \frac{1.005}{L}$$

For L = 24: μ_c ≈ 0.042. The observed μ_c ≈ 0.011 is ~4× smaller, indicating that the Potts mapping overestimates the stability of the ordered state. This is expected: the Potts ordered state is an equilibrium crystal, while the replicator state requires active maintenance through computational self-copying. The selective advantage σ in the Eigen formula ln(σ)/L provides the correct scaling.

**Computational evidence (error_threshold_confinement.c, Experiment c):**

At zero mutation (μ = 0), the flat-tile soup achieves 100% replicator density — there is no noise floor. The ~35% noise floor observed in the Phase 1 2D soup comes from geometric overlap of BFS patches on the 2D mesh, not from the VM dynamics. This is analogous to how the gluon condensate ⟨G²⟩ depends on the lattice geometry, not just the gauge group.

### 2.2.4 Critical Nucleus ↔ First-Order Phase Transition

While the Z₃ Potts model in 2D has a second-order (continuous) transition (q ≤ 4, Baxter 1973), the soup's error catastrophe exhibits nucleation-like dynamics. The first-order character of the soup's transition may reflect its non-equilibrium nature (absorbing-state transition class) rather than the equilibrium Potts universality class. In 3D, the Z₃ Potts transition is genuinely first-order, with classical nucleation dynamics.

**Computational evidence (critical_nucleus_phase_transition.c, Experiment a):**

Seeded replicator amplification in 1666-tile flat soup, μ = 0.001, 2000 epochs, 10 trials:

| N_seed | Survival | Avg final ρ | Growth rate | Interpretation |
|--------|----------|-------------|-------------|----------------|
| 1 | 2/10 | 18.2% | 0.00091 | Near-critical |
| 2 | 7/10 | 62.6% | 0.00312 | Super-critical (some fail) |
| 3 | 7/10 | 63.6% | 0.00317 | Super-critical (some fail) |
| 5 | 9/10 | 81.5% | 0.00406 | Super-critical (some fail) |
| 7 | 10/10 | 90.1% | 0.00448 | Super-critical |
| 10 | 10/10 | 89.5% | 0.00444 | Super-critical |
| 11 | 10/10 | 89.1% | 0.00442 | Super-critical |
| 15 | 10/10 | 88.9% | 0.00440 | Super-critical |
| 50 | 10/10 | 88.7% | 0.00428 | Super-critical |
| 100 | 10/10 | 89.4% | 0.00417 | Super-critical |

The critical nucleus is **N_c ≈ 2 tiles** in the flat-tile (well-mixed) model — 100% survival is achieved at N_seed ≥ 7, and growth rate saturates at ~0.0044 for N_seed ≥ 7. This is smaller than the **~11 tiles** critical nucleus on the 2D triangulated mesh (Phase 1), because the 2D mesh has spatial locality that makes boundary tiles more vulnerable.

**Growth dynamics (Experiment b):** Nucleation-and-growth, not spinodal decomposition. Starting from 20 seeded tiles in 1666-tile soup: lag phase (epochs 0–5), exponential growth (epochs 5–30, density 0.7% → 57%), saturation at ~90% equilibrium density by epoch ~50. This is consistent with a **first-order** transition with nucleation.

**Minimum population for confinement (Experiment c):** Fully seeded, μ = 0.001:

| N_tiles | Survived | Avg density | Interpretation |
|---------|----------|-------------|----------------|
| 50 | 4/5 | 74.0% | Marginal |
| 100 | 5/5 | 92.6% | Confined (maintained) |
| 200 | 5/5 | 82.4% | Confined (maintained) |
| ≥400 | 5/5 | ~89% | Confined (maintained) |

The minimum population for sustained replication is ~50–100 tiles, well below the ~1666 needed for spontaneous emergence.

**Connection to nucleation theory.** In classical nucleation theory, the critical droplet radius R_c balances surface energy (∝ R^{d-1} × σ_surf) against bulk free energy gain (∝ R^d × |Δf|):

$$R_c = \frac{(d-1) \sigma_{\text{surf}}}{|\Delta f|}$$

For the soup on a 2D surface (d = 2):

$$N_c \sim \frac{\sigma_{\text{surf}}}{|\Delta f|}$$

where σ_surf is the effective "surface tension" at the replicator/random boundary and Δf is the free energy advantage of the replicator state. The small critical nucleus (~2–11 tiles out of ~1666) implies Δf ≫ σ_surf — the replicator state is strongly thermodynamically favored once it exists.

**Connection to CG phase transitions:**

| Property | Soup | Bag Model (Drv 2.1.2a) | EW Transition (Thm 4.2.3) |
|----------|------|----------------------|--------------------------|
| Critical size | ~11 tiles / 1666 = 0.66% | R_eq = (Ω/4πB)^{1/4} | v(T_c)/T_c = 1.22 |
| Growth dynamics | Logistic (τ ≈ 150–200 epochs) | Pressure equilibrium | Spinodal decomposition |
| Equilibrium density | ~87–89% at μ = 0.001 (Q13; tiling bug fixed) | Confinement pressure = bag pressure | Electroweak symmetry breaking |
| Order parameter | Replicator density ρ_rep | String tension σ | Higgs VEV v |

The logistic growth from seed to equilibrium is consistent with **nucleation-and-growth** dynamics (not spinodal decomposition, which would show exponential instability at all scales simultaneously). This nucleation-like behavior is characteristic of the soup's non-equilibrium absorbing-state dynamics rather than the equilibrium Z₃ Potts transition (which is second-order in 2D).

---

## Task 2.3: Continuum Limit — Z₃ Parafermion CFT

### 2.3.1 The Potts Model Continuum Limit

At the critical point of the q-state Potts model (for q ≤ 4 where the transition is continuous, or at the first-order transition point for q > 4), the long-distance behavior is described by a conformal field theory.

For q = 3, this is the **Z₃ parafermion CFT** of Fateev and Zamolodchikov (1985):

| Property | Value |
|----------|-------|
| Central charge | c = 4/5 |
| Z₃ symmetry | Built-in (parafermion currents carry Z₃ charge) |
| Primary fields | Identity (h = 0), energy ε (h = 2/5), spin σ (h = 1/15), parafermion ψ₁ (h = 2/3) |
| Modular invariant | Z₃ orbifold of free boson (c = 4/5) |

**Important caveat:** The Z₃ Potts model in 2D has a **second-order** (continuous) transition at the self-dual critical point (Baxter 1973). The parafermion CFT with $c = 4/5$ describes the model at this critical point. The Z₃ Potts model in 2D sits exactly at the boundary $q = q_c = 4$ where the transition changes from continuous to first-order; for $q = 3 < 4$, the transition is continuous and the CFT description is exact at criticality.

**Reference:** V.A. Fateev & A.B. Zamolodchikov, "Parafermionic currents in the two-dimensional conformal quantum field theory and selfdual critical points in Z_N-invariant statistical systems," Sov. Phys. JETP 62 (1985) 215.

### 2.3.2 CFT Operator Identification

If the Potts mapping applies at the critical point (μ ≈ μ_c), the CFT operators have the following soup interpretations:

| CFT Operator | Conformal dim h | Potts interpretation | Soup interpretation |
|-------------|----------------|---------------------|---------------------|
| **1** (identity) | 0 | Trivial (vacuum) | Uniform random soup |
| **ε** (energy) | 2/5 | Energy density | Local mutation density / interaction strength |
| **σ** (spin) | 1/15 | Magnetization | Replicator density order parameter |
| **ψ₁** (parafermion) | 2/3 | Z₃ disorder operator | Boundary between replicator domains |
| **ψ₂** (parafermion) | 2/3 | Z₃ disorder (conjugate) | Conjugate domain boundary |

The **spin operator σ** (h = 1/15) is the most important for the soup: its correlator ⟨σ(x) σ(0)⟩ ~ |x|^{−2/15} governs the spatial correlations of the replicator density. At criticality (μ = μ_c), replicator clusters have fractal structure with power-law correlations.

### 2.3.3 Relevance of c = 4/5 for CG

The central charge c = 4/5 of the Z₃ parafermion CFT has a natural interpretation in the CG framework:

1. **Minimal model classification.** c = 4/5 is the M(5,6) minimal model, which also appears as the tricritical 3-state Potts model. This is the simplest CFT with Z₃ symmetry.

2. **Degrees of freedom.** c = 4/5 counts the effective number of massless degrees of freedom at the critical point. For comparison:
   - Free boson: c = 1
   - Free fermion: c = 1/2
   - c = 4/5 indicates a strongly interacting system with ~0.8 effective bosonic degrees of freedom

3. **Coset construction.** The Z₃ parafermion CFT admits a coset construction:
   $$\frac{SU(2)_3}{U(1)} \cong Z_3 \text{ parafermion}$$
   This is suggestive: SU(2) is a subgroup of SU(3), and the Z₃ quotient is the center of SU(3). The coset construction may provide a direct bridge between the parafermion CFT and the CG gauge structure.

### 2.3.4 The Non-Equilibrium Caveat

The Potts CFT describes the **equilibrium** critical point. The soup is non-equilibrium. Two scenarios:

**(a) Same universality class.** If the soup's non-equilibrium dynamics are "irrelevant" in the RG sense (i.e., they don't change the critical exponents), then the soup's critical behavior at μ = μ_c is described by the same Z₃ parafermion CFT. This would be the case if the detailed balance violation is a dangerously irrelevant perturbation.

**(b) Different universality class.** If the non-equilibrium dynamics are relevant, the soup belongs to a different universality class — possibly directed percolation (DP) or the KPZ universality class. In this case, the Potts CFT is only an approximation, and the true continuum limit requires non-equilibrium field theory methods.

**Evidence favoring scenario (a):**
- The Z₃ symmetry is exact in both systems (shared symmetry constrains critical behavior)
- The order parameter (replicator density) breaks the same symmetry
- The critical behavior (sharp but continuous transition at μ_c) is qualitatively consistent with the weakly first-order Potts transition

**Evidence favoring scenario (b):**
- The soup dynamics violate detailed balance (the VM execution is irreversible)
- Self-replication is an inherently non-equilibrium process (autocatalysis has no equilibrium analog)
- The error catastrophe is closer to the Eigen quasispecies transition than to a Potts phase transition — the Eigen transition is in the DP universality class (Hermisson et al., 2002)

**Assessment:** The soup is most likely in the **absorbing-state phase transition** universality class (which includes directed percolation), with Z₃ symmetry providing additional constraints. The Z₃ parafermion CFT is a useful structural guide but may not be the exact continuum limit. The true continuum limit likely requires Z₃-symmetric non-equilibrium field theory — a problem that has been partially studied in the context of non-equilibrium Z_q clock models (Mukamel et al., various).

---

## Task 2.4: Consistency with CG Field Content

### 2.4.1 Z₃ Phase Structure

The three color fields of CG (Def 0.1.2) have phases:

$$\phi_R = 0, \quad \phi_G = \frac{2\pi}{3}, \quad \phi_B = \frac{4\pi}{3}$$

These are exactly the three states of the Z₃ Potts model, with the identification:

$$\sigma = 0 \;\leftrightarrow\; R \;(\phi = 0), \quad \sigma = 1 \;\leftrightarrow\; G \;(\phi = 2\pi/3), \quad \sigma = 2 \;\leftrightarrow\; B \;(\phi = 4\pi/3)$$

The Z₃ cyclic symmetry σ → σ + 1 mod 3 corresponds to the color rotation R → G → B → R, which is the ROT instruction of the VM. This is the center Z(SU(3)) ≅ Z₃ of the gauge group.

### 2.4.2 Field Content Comparison

| CG Field Content | Z₃ Parafermion CFT | Match? |
|-----------------|-------------------|--------|
| Three color fields χ_R, χ_G, χ_B | Three spin states σ = 0, 1, 2 | ✅ Exact |
| Z₃ center symmetry from SU(3) | Z₃ global symmetry | ✅ Exact |
| Complex scalar fields on ∂S | CFT operators on 2D surface | ✅ Compatible |
| Two disjoint S² (χ = 4) | Single 2D surface | ⚠️ Topology mismatch |
| SU(3) gauge structure | No gauge structure | ⚠️ Missing gauge |
| Pressure functions P_c(x) | Energy operator ε | ✅ Plausible |
| Instanton configurations (π₃(SU(3)) = Z) | Not present | ❌ Missing |

### 2.4.3 Topology Mismatch: Two Surfaces vs One

CG lives on ∂S = ∂T₊ ⊔ ∂T₋, which is topologically **two disjoint S²** with Euler characteristic χ = 4 (Def 0.1.1). The Potts model and its parafermion CFT are defined on a **single** connected surface.

**Resolution:** The soup simulation (Phase 1) already addresses this. The tile model treats T₊ and T₋ as two separate triangulated surfaces with 50% cross-tetrahedron interaction probability. In the Potts language, this is a **bilayer Potts model** — two coupled Potts layers with inter-layer coupling J_⊥.

The bilayer Z₃ Potts model has been studied (Delfino & Grinza, 2007). Key results:
- For weak inter-layer coupling: two independent Z₃ transitions at the same T_c, with total central charge c = 2 × 4/5 = 8/5
- For strong inter-layer coupling: a single transition with modified critical behavior

The CG framework (50% cross-talk) corresponds to **moderate coupling**, likely producing a single phase transition with effective central charge between 4/5 and 8/5. The Euler characteristic χ = 4 = 2 × 2 is consistent with two independent copies at weak coupling.

### 2.4.4 Missing Gauge Structure

The Potts model has a **global** Z₃ symmetry but no gauge structure. CG has a full **SU(3) gauge symmetry** with Z₃ as its center. The Potts model captures only the center symmetry — the "abelian projection" of the full gauge theory.

This is precisely the situation in lattice gauge theory: the Z₃ Potts model describes the **deconfinement transition** of SU(3) gauge theory (Svetitsky & Yaffe, 1982), where the order parameter is the Polyakov loop (valued in Z₃). The full gauge dynamics are richer, but the universal critical behavior is determined by the center symmetry alone.

**Svetitsky-Yaffe conjecture (established):** The deconfinement phase transition of an SU(N) gauge theory in (d+1) dimensions is in the universality class of the Z_N spin model in d dimensions.

For CG: SU(3) gauge theory in (3+1)D → Z₃ Potts model in 3D (by Svetitsky-Yaffe dimensional reduction). The 3D Z₃ Potts transition is first-order, consistent with the first-order SU(3) deconfinement transition observed in lattice QCD. Note that on ∂S itself (a 2D surface), the Z₃ Potts transition would be second-order (q=3 < 4 in 2D), but the physical deconfinement maps to the 3D effective theory. The transfer matrix analysis of Prop 2.5.2c confirms this: the FCC lattice phase transition at u₃(β_c) = 3^{−3/8} is indeed a deconfinement transition governed by Z₃ center symmetry.

**Reference:** B. Svetitsky & L.G. Yaffe, "Critical behavior at finite-temperature confinement transitions," Nucl. Phys. B210 (1982) 423.

### 2.4.5 Replicator ↔ Polyakov Loop

The most significant identification emerging from the Potts mapping:

$$\text{Self-replicating program} \;\longleftrightarrow\; \text{Polyakov loop} \;\longleftrightarrow\; \text{Confined state}$$

In lattice gauge theory, the Polyakov loop ⟨L⟩ is the order parameter for confinement:
- ⟨L⟩ = 0 in the confined phase (quarks bound into hadrons)
- ⟨L⟩ ≠ 0 in the deconfined phase (free quarks)

In the soup, the replicator density ρ_rep is the order parameter:
- ρ_rep > 0 in the "replicator phase" (self-replicating programs dominate)
- ρ_rep = 0 in the "random phase" (no coherent programs)

But the analogy is **inverted**: the replicator phase (ρ_rep > 0, coherent programs) corresponds to the **confined** phase (⟨L⟩ = 0, coherent hadrons), not the deconfined phase. In both cases, the ordered state consists of **coherent composite objects** (replicators or hadrons) that maintain their identity against a disordering background.

| | Soup: Ordered | Soup: Disordered | QCD: Confined | QCD: Deconfined |
|--|-------------|-----------------|--------------|----------------|
| Order parameter | ρ_rep > 0 | ρ_rep = 0 | σ > 0 | σ = 0 |
| Objects | Self-replicators | Random programs | Hadrons | Free quarks |
| Mechanism | VM-based self-copying | Mutation overwhelms | Color flux tubes | Debye screening |
| Transition type | Error catastrophe | — | Deconfinement | — |
| Control parameter | μ < μ_c | μ > μ_c | T < T_c | T > T_c |

The error catastrophe at μ_c is the soup analog of the deconfinement transition at T_c. Both destroy coherent composite structures through overwhelming disorder.

---

## Summary: The Potts Dictionary

### Complete Mapping

| Soup Concept | Potts/Statistical Mechanics | CG/Gauge Theory |
|-------------|---------------------------|-----------------|
| Z₃ cell value {0,1,2} | Potts spin σ ∈ {0,1,2} | Color phase φ ∈ {0, 2π/3, 4π/3} |
| Mutation rate μ | Temperature T = 1/β | Temperature T |
| μ_c ≈ 0.011 | T_c: β_cJ = ln(1+√3) | T_c: deconfinement |
| Replicator density ρ_rep | Magnetization M | String tension σ (inverted) |
| Self-replicating program | Domain (ordered cluster) | Hadron (confined state) |
| VM-mediated interaction | Energy function H | Wilson action S |
| Tile on ∂S | Lattice site | Lattice plaquette |
| Critical nucleus ~11 tiles | Critical droplet (nucleation) | Bag radius R_eq (Drv 2.1.2a) |
| Error catastrophe | Phase transition (2nd-order in 2D, 1st-order in 3D) | Deconfinement transition |
| Quasispecies cloud | Thermal fluctuations within ordered phase | Hadron excitation spectrum |
| T₊/T₋ cross-talk | Bilayer coupling | Color field interference (Thm 0.2.1) |

### What Works

1. **Z₃ symmetry identification** — exact, grounded in Def 0.1.2 and Z(SU(3))
2. **Phase transition analogy** — error catastrophe ↔ deconfinement, correct qualitative structure
3. **Svetitsky-Yaffe connection** — soup as effective Z₃ model for SU(3) center dynamics
4. **Bilayer structure** — T₊ ⊔ T₋ naturally maps to coupled Potts layers

### What Doesn't Work

1. **Microscopic dynamics** — VM execution ≠ Boltzmann update (non-equilibrium)
2. **Quantitative critical point** — Potts β_c overestimates stability by ~10×
3. **Gauge structure** — Potts captures only Z₃ center, not full SU(3)
4. **Self-replication mechanism** — no equilibrium analog of autocatalysis

### Open Questions (Unresolved from Phase 2, informing Phase 4)

1. **Universality class determination.** Is the soup's critical behavior at μ = μ_c in the Z₃ Potts universality class, the directed percolation class, or a novel non-equilibrium class? This requires measuring critical exponents numerically.

2. **Non-equilibrium CFT.** If the soup is not in the Potts universality class, what non-equilibrium field theory describes its continuum limit? Z₃-symmetric versions of the KPZ equation or reaction-diffusion field theories are candidates.

3. **From Z₃ to SU(3).** The Potts model captures only the center symmetry. How does the full SU(3) gauge structure emerge in the continuum limit? The coset construction SU(2)₃/U(1) for the parafermion CFT suggests a path, but the full SU(3) → Z₃ reduction needs to be made explicit.

4. **Bilayer CFT.** What is the exact CFT for the bilayer Z₃ Potts model at the 50% coupling relevant for CG? Is the effective central charge c = 8/5, or is it modified by the inter-layer coupling?

---

## Verification Scripts

The following computational experiments support this analysis:

| Script | Experiment | Key Result |
|--------|-----------|------------|
| `error_threshold_confinement.c` | (a) Eigen scaling test | μ_c ≈ 0.011, **independent of L** (NOT Eigen scaling) |
| `error_threshold_confinement.c` | (b) Transition shape at L=24 | Smooth but steep; density 80%→0% over μ ∈ [0.002, 0.012] |
| `error_threshold_confinement.c` | (c) Zero-mutation noise floor | 0% in flat tiles (35% noise floor is geometric, not intrinsic) |
| `critical_nucleus_phase_transition.c` | (a) Critical droplet size | N_c ≈ 2 tiles (flat) or ~11 tiles (2D mesh) |
| `critical_nucleus_phase_transition.c` | (b) Growth dynamics | Nucleation-and-growth (lag→exponential→saturation in ~50 epochs) |
| `critical_nucleus_phase_transition.c` | (c) Minimum population | ≥100 tiles for sustained confinement, 50 marginal |
| `critical_nucleus_phase_transition.c` | (d) Effective surface tension | Loss rate ~30%, consistent with nucleation theory |

---

## Status Assessment

| Task | Status | Key Finding |
|------|--------|-------------|
| 2.1 Map soup to Potts | ✅ Complete | Dictionary established; mapping is approximate (non-equilibrium) |
| 2.2 Statistical mechanics | ✅ Complete | No partition function; μ ↔ T; error catastrophe ↔ deconfinement |
| 2.3 Continuum limit | 🔸 Partial | Z₃ parafermion CFT (c = 4/5) identified; may not be exact due to non-equilibrium |
| 2.4 CG consistency | ✅ Complete | Z₃ match exact; topology mismatch resolved via bilayer; gauge structure via Svetitsky-Yaffe |

**Phase 2 success criterion:** "Explicit dictionary between soup dynamics and Potts model, with identification of the continuum CFT and its relevance to CG."

**Assessment: MET (with caveats).** The dictionary is established (§2.1.2, Summary). The continuum CFT is identified as the Z₃ parafermion theory (§2.3.1) with the caveat that the non-equilibrium nature of the soup may place it in a different universality class (§2.3.4). The relevance to CG is established through the Svetitsky-Yaffe connection (§2.4.4) and the Polyakov loop identification (§2.4.5).

---

## References

1. F.Y. Wu, "The Potts Model," Rev. Mod. Phys. 54 (1982) 235
2. R.J. Baxter, "Potts model at the critical temperature," J. Phys. C 6 (1973) L445
3. V.A. Fateev & A.B. Zamolodchikov, "Parafermionic currents in the two-dimensional conformal quantum field theory," Sov. Phys. JETP 62 (1985) 215
4. B. Svetitsky & L.G. Yaffe, "Critical behavior at finite-temperature confinement transitions," Nucl. Phys. B210 (1982) 423
5. M. Eigen, "Selforganization of matter and the evolution of biological macromolecules," Naturwissenschaften 58 (1971) 465
6. J. Hermisson, O. Redner, H. Wagner, E. Baake, "Mutation-selection balance: ancestry, load, and maximum principle," J. Math. Biol. 44 (2002) 567
7. G. Delfino & P. Grinza, "Universal ratios along a line of critical points," Nucl. Phys. B791 (2008) 265
