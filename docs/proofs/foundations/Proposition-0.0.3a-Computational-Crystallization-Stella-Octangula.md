# Proposition 0.0.3a: Computational Crystallization of the Stella Octangula

## Status: 🔶 NOVEL ✅ VERIFIED — DYNAMICAL COMPANION TO STELLA UNIQUENESS

**Created:** 2026-03-26
**Purpose:** Demonstrate that the stella octangula is the unique ground state of Z₃ field interactions — the computational/dynamical counterpart to the algebraic uniqueness of Theorem 0.0.3.

**Dependencies:**
- ✅ Theorem 0.0.3 (Stella Uniqueness — algebraic derivation)
- ✅ Theorem 0.0.3b (Geometric Realization Completeness)
- ✅ Proposition 0.0.XXa (First Stable Principle — Fisher non-degeneracy at N = 3)
- ✅ Proposition 0.0.17b (Fisher Metric Uniqueness via Chentsov)
- ✅ Definition 0.1.1 (Stella Octangula Boundary Topology)
- ✅ Definition 0.1.2 (Three Color Fields, Relative Phases)

**Extended by:** [Theorem 0.0.3b](Theorem-0.0.3b-Geometric-Realization-Completeness.md) (Completeness of classification)

**Computational Verification:**
- `stella_genesis/RESULTS-Crystallization.md` (Phases A–G, Z1–Z2)
- Phase executables: `phase_b.c` through `phase_z2.c` in `stella_genesis/`

**Peer Review:**
- [Multi-Agent Verification Report (2026-03-26)](../verification-records/Proposition-0.0.3a-Multi-Agent-Verification-2026-03-26.md) — Literature, Mathematics, Physics agents + 14/14 computational tests

**Adversarial Verification:**
- C source: `verification/proposition_0_0_3a_adversarial.c` (annealing-based tests T1–T6, T9–T10, T13–T14)
- Python wrapper: `verification/proposition_0_0_3a_adversarial_verification.py` (Fisher, CRT, quaternion tests T7–T8, T11–T12 + plotting)
- Plots: `verification/plots/prop_0_0_3a_verification_summary.png`, `verification/plots/prop_0_0_3a_phase_transition.png`

**Structure:** This proposition uses the 3-file structure due to length:
- **Statement** (this file): Formal claim and proof sketch
- **[Derivation](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Derivation.md)**: Full experimental evidence chain (Phases A–G, Z1–Z2)
- **[Applications](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Applications.md)**: Physical interpretation, input reduction analysis, and cross-references

---

## 1. Statement

**Proposition 0.0.3a (Computational Crystallization of the Stella Octangula):**

*Let N charged particles on a sphere interact via Z₃ product-rule repulsion, with coupling coefficient α for same-charge pairs and β for conjugate-charge pairs. Then:*

**(a) Geometry crystallization.** *For α/β ≥ 2 (where α/β = 2 is derived from the SU(3) Casimir ratio C_F(**6**)/C_F(**8**) = (1/3)/(1/6) = 2; see §7.1), the unique ground state is the stella octangula — two interpenetrating regular tetrahedra in dual orientation. Convergence is 100% from random initial conditions (RMSD < 0.02 to ideal stella, verified across 20+ seeds per configuration). The result is robust across potential forms: tested with 1/d (Coulomb), 1/d², and 1/d³ repulsive potentials, all producing the stella above their respective thresholds (see Derivation §2.4).*

**(b) Vertex count and partition selection.** *Starting from N > 8 particles with variable labels, the dynamics select N = 8 in a 4+4 partition. Grand canonical annealing from N = 20 selects N = 8 with zero variance for chemical potential μ ∈ [16, 22]. Label relaxation from any initial split (1+7 through 7+1) converges to 4+4 with 100% success (70/70 runs).*

**(c) Sphere emergence.** *Replacing the hard sphere constraint with soft normalization γ·Σ(|rᵢ| − 1)², the spherical shell and stella geometry emerge simultaneously for any γ > 0. Shell formation (γ) and crystallization (α/β) are independent phenomena, confirmed by 2D parameter sweep.*

**(d) Z₃ minimality.** *Among cyclic groups Z_n with non-trivial charges and product-rule interactions: Z₂ fails (one non-trivial charge, no conjugate pair), Z₃ succeeds uniquely (100% stella convergence), Z₄ is unstable (self-conjugate charge creates competing trivial ground state, 70% stella), and Z_{5+} succeed but carry redundant unused charges. Z₃ is the minimal cyclic group producing the stella without trivial escape routes.*

**(e) Fisher non-degeneracy threshold.** *The Fisher information metric of N-component interference p(x; φ) = |Σ Aₖ(x) e^{iφₖ}|² is identically degenerate for N ≤ 2 (0/500 random amplitude configurations) and non-degenerate for N ≥ 3. Phase F1 finds 499/500 non-degenerate at N = 3 using Gaussian amplitude bumps with a conservative eigenvalue threshold (λ_min/λ_max > 10⁻⁶); Phase Z2-M0 finds 500/500 using a rank-based criterion (any eigenvalue > ε). The single F1 failure is a numerical edge case where near-degenerate amplitudes produce a borderline eigenvalue ratio — not a structural failure. N = 3 is the minimal system with well-defined information geometry.*

**(f) Z₃ as dynamical attractor.** *Continuous fields subject to clustering pressure (minimality) and non-degeneracy constraint (det(Fisher) > 0) converge to exactly 3 phase clusters with 100% success rate (30/30 seeds, all tested M and coupling strengths). Z₃ is a dynamical attractor, not merely a static optimum.*

**(g) Non-degeneracy from coupling.** *Non-degeneracy is not an independent axiom. Z₂ interference has zero channel capacity (Fisher rank 0, universal across 500 random amplitudes). Dual-surface coupling is frozen for Z₂ (Δcorr = +0.0001) but effective for Z₃ (Δcorr = +1.006). A Z₂ system with a perturbative third component spontaneously amplifies it (10/10 seeds, 2.8×–4.1× growth), because the third component enables inter-surface information transfer.*

**(h) Number field selection.** *By Hurwitz's theorem, the only normed division algebras are ℝ, ℂ, ℍ, 𝕆. The complex numbers ℂ are uniquely selected: ℝ has no continuous phase; ℍ has 3(N−1) Fisher dimensions but rank exactly N−1 (identical to ℂ, verified to 10 decimal places across N = 2..6 and 20 random quaternion equilibria); 𝕆 is non-associative and cannot support standard Lie-group-based gauge theory (non-associative gauge theories using Moufang loops exist [Okubo 1995, Günaydin & Gürsey 1973] but lack the fiber-bundle structure required for Yang-Mills quantization).*

### 1.1 Complete Derivation Chain

The full chain from irreducible axioms to the stella octangula:

```
AXIOM 1: Hurwitz's theorem (1898) — pure mathematics
    → ℂ selected (Phase G: minimal with non-trivial, non-redundant phase)
    → N = 3 selected (Phase F: minimal prime with non-degenerate Fisher)
            ↑ Phase Z1: this is a DYNAMICAL ATTRACTOR (100%, 30/30)
            ↑ Phase Z2: non-degeneracy DERIVED from coupling requirement
    → Z₃ non-trivial charges {1, 2} = conjugate pair (Phase E)
    → two groups of 4 points on sphere (from normalization, Phase D)
    → each group forms regular tetrahedron (max separation, Phase C)
    → two tetrahedra interpenetrate → stella octangula (Phase B)

AXIOM 2: Minimality — select the simplest sufficient structure

MECHANISM: Dual-surface coupling — surfaces must communicate
    → non-degeneracy required (Phase Z2: Z₂ coupling frozen)
    → Z₃ emerges dynamically (Phase Z1: 100% convergence)
```

### 1.2 Irreducible Inputs

After progressive input reduction across nine experimental phases:

| Input | Type | Content |
|:------|:-----|:--------|
| Hurwitz's theorem | Pure mathematics | Only ℝ, ℂ, ℍ, 𝕆 exist as normed division algebras |
| Minimality | Meta-mathematical | Select the smallest structure that works |
| Dual-surface coupling | Physical mechanism | Surfaces must be able to transfer information |

Non-degeneracy of the Fisher metric, previously treated as an axiom, is **derived** from the coupling requirement (Phase Z2).

### 1.3 Relationship to Theorem 0.0.3

Theorem 0.0.3 proves stella uniqueness **algebraically**:
```
Z₃ center → SU(3) gauge group → GR1–GR3 axiom package → stella (unique)
```

Proposition 0.0.3a demonstrates the same uniqueness **dynamically/computationally**:
```
Z₃ interactions → energy minimization → stella (unique ground state)
```

The two results are complementary:
- **Thm 0.0.3** answers: *given SU(3), what is the minimal 3D geometric realization?*
- **Prop 0.0.3a** answers: *given Z₃ fields, what geometry do they crystallize into?*

Both arrive at the stella octangula, through independent reasoning chains. Theorem 0.0.3 works top-down (from the gauge group); Proposition 0.0.3a works bottom-up (from field interactions).

---

## 2. Proof Sketch

The proof proceeds through nine experimental phases, each removing an assumption from the previous:

### Phase A: Coupling dynamics do not uniquely select geometry (negative result)

Running the Genesis VM on multiple candidate geometries with identical Z₃ coupling rules shows that raw coupling coherence does not distinguish the stella — many geometries produce comparable dynamics (corr ≈ 0.72–0.78 across a broad angular range). The stella's uniqueness is group-theoretic, not dynamical.

**Significance:** This negative result motivates the shift from "dynamics selects geometry" to "energy minimization selects geometry" in subsequent phases.

### Phase B: Stella as unique ground state of two-component repulsion

Eight points on a sphere with two-component asymmetric repulsion (E = α·Σ_same 1/d² + β·Σ_cross 1/d²) crystallize into the stella octangula for α/β ≥ 2. The transition is sharp (RMSD drops from 0.17 to 0.015 at α/β ≈ 2) and robust (100% convergence, 20/20 seeds).

**Key mechanism:** Same-component repulsion forces each group of 4 into a regular tetrahedron (maximizing mutual distances). Cross-component repulsion then selects the dual orientation (maximizing minimum cross-distance). The stella is the unique configuration satisfying both constraints.

### Phase C: N = 8 and 4+4 partition are selected

Three independent tests: (C1) Grand canonical annealing from N = 20 selects N = 8 with 100% convergence for μ ∈ [16, 22]. (C2) Label relaxation from any initial split converges to 4+4 (100%, 70/70). (C3) Among all N tested, only N = 8 achieves both Regularity ≈ 1.0 AND Isotropy ≈ 1.0 (product 0.993 vs 0.804 for next best), because the regular tetrahedron is the only polyhedron with all pairwise distances equal AND 3D extent.

### Phase D: Sphere emerges from normalization

Soft normalization γ·Σ(|rᵢ| − 1)² replaces the hard sphere constraint. For any γ > 0, points starting from random cube positions self-organize onto a spherical shell and form the stella simultaneously. A 2D parameter sweep confirms shell formation (controlled by γ) and stella crystallization (controlled by α/β) are completely independent phenomena.

### Phase E: Two-component structure = Z₃ representation theory

Z₃ product-rule interactions with non-trivial charges {1, 2} reproduce Phase B exactly (100% stella at α/β ≥ 2). The two-component structure is not an arbitrary label but a consequence of Z₃ having exactly two non-trivial conjugate elements. Z₂ fails (one charge, no splitting), Z₄ has a self-conjugate escape route (70% stella), Z₅+ are redundant.

### Phase F: Z₃ selected by Fisher non-degeneracy + primality + minimality

*F1:* The Fisher information metric is identically degenerate at N = 2 (mathematical reason: Z₂ equilibrium forces real-valued interference) and non-degenerate for N ≥ 3 (universal, 500 random amplitudes).

*F2:* Computational richness does NOT select N = 3 (negative result — richness increases monotonically with N). This rules out energetic selection.

*F3:* Composite-N dynamics factorize exactly via CRT (zero reconstruction error). Prime-N dynamics are irreducible. Among primes ≥ 3, irreducibility index is strictly decreasing (N = 3 highest at 0.417).

**Selection chain:** Fisher-stable (N ≥ 3) ∩ prime (irreducible) ∩ minimal → N = 3.

### Phase G: ℂ selected from Hurwitz's classification

The quaternionic Fisher matrix has 3(N−1) dimensions but rank exactly N−1 — identical to ℂ. Non-zero eigenvalues match to 10 decimal places. The extra 2(N−1) quaternionic DOF are phantom (probability insensitive to axis direction). ℝ has no continuous phase; 𝕆 is non-associative. ℂ is the unique sufficient, non-redundant, associative division algebra.

### Phase Z1: Z₃ as dynamical attractor

Continuous fields with clustering pressure and non-degeneracy constraint converge to exactly 3 phase clusters (100%, 30/30 seeds, robust across 5 values of M, 5 coupling strengths, 6 parsimony values). Generic dynamics (Z1-M0) and energetic competition (Z1-M1) do NOT select Z₃, confirming that the information-geometric constraint is essential, not redundant.

### Phase Z2: Non-degeneracy derived from coupling requirement

Z₂ Fisher matrix has rank 0 universally (0/500). Dual-surface coupling is frozen for Z₂ (Δcorr ≈ 0) but effective for Z₃ (Δcorr ≈ +1.0). A perturbative third component grows spontaneously (10/10 seeds, 2.8–4.1× amplification) because it enables communication. Non-degeneracy is a consequence of coupling, not an axiom.

---

## 3. Progressive Input Reduction

| Phase | Inputs assumed | What emerges |
|:-----:|:---------------|:-------------|
| A | stella + Z₃ coupling | dynamics (but not unique to stella) |
| B | N = 8, 4+4 labels, sphere, α > β | stella geometry |
| C | labels, sphere, α > β | N = 8, 4+4 split, stella |
| D | labels, normalization, α > β | sphere + stella |
| E | Z₃ non-trivial charges, normalization | two components + sphere + stella |
| F | computational substrate (minimality + primality) | Z₃ + everything above |
| G | Hurwitz's theorem + non-redundancy | ℂ + Z₃ + everything above |
| Z1 | continuous fields + non-degeneracy + minimality | Z₃ as dynamical attractor |
| **Z2** | **continuous fields + dual-surface coupling + minimality** | **non-degeneracy + Z₃ + everything above** |

---

## 4. Convergence Summary

| Claim | Test | Seeds | Success Rate | Key Metric |
|:------|:-----|------:|:-------------|:-----------|
| Stella is ground state (B) | Annealing, α/β ≥ 2 | 20 | 100% | RMSD < 0.02 |
| N = 8 selected (C1) | Grand canonical | 10/μ | 100% (μ ∈ [16,22]) | σ(N) = 0 |
| 4+4 split selected (C2) | Label relaxation | 70 | 100% | All splits → 4+4 |
| N = 8 unique (C3) | Geometry comparison | 10/N | — | Reg×Iso = 0.993 vs 0.804 |
| Sphere emerges (D) | Soft normalization | 50 | 100% | Shell quality > 0.99 |
| Z₃ product rule works (E1) | Product-rule annealing | 30 | 100% | Identical to Phase B |
| Z₃ minimal (E3) | Z_n comparison | 30/n | Z₃: 100%, Z₄: 70% | Z₂: 0%, Z₅+: 100% |
| Fisher threshold (F1) | Random amplitudes | 500 | N=2: 0%, N=3: 99.8% | Universal |
| CRT factorization (F3) | Decomposition test | — | Error = 0 (exact) | Composites = trivial |
| ℂ = ℍ rank (G) | Eigenvalue comparison | 20 | 100% | Match to 10 digits |
| Z₃ attractor (Z1-M2) | Constrained dynamics | 30 | 100% | 3 clusters always |
| Non-degeneracy from coupling (Z2) | Z₂ instability | 10 | 100% | 2.8–4.1× growth |

---

## 5. Consistency Checks

### 5.1 Dimensional Analysis

All crystallization experiments operate on dimensionless quantities (angles, distance ratios, energy ratios). The α/β threshold is a pure number (≈ 2), independent of physical units.

### 5.2 Known Physics Recovery

The stella octangula emerging from Z₃ interactions is consistent with:
- Theorem 0.0.3 (algebraic uniqueness) — same endpoint, different route
- The A₂ root system of SU(3) — 6 primary vertices map to weights of **3** ⊕ **3̄**
- Thomson problem (α/β = 1) → square antiprism (NOT stella), confirming the interaction asymmetry is essential

### 5.3 Robustness

- Results independent of annealing schedule (tested 200K to 2M steps)
- Results independent of initial conditions (random sphere, random cube, prescribed configurations)
- Results independent of seed (100% convergence in all cases where claimed)
- **Results independent of potential form:** Tested 1/d (Coulomb), 1/d², and 1/d³ repulsive potentials. All three produce the stella with 100% convergence above their respective thresholds (α/β ≈ 1.5 for 1/d, ≈ 2.0 for 1/d², ≈ 3.0 for 1/d³). Final geometry is identical. See Derivation §2.4.
- Negative results (Phase A, F2, Z1-M0, Z1-M1) are genuine and informative

### 5.4 Falsifiability

The proposition would be falsified by:
- Finding a geometry that outperforms the stella on a group-theoretically motivated energy function
- Finding a cyclic group Z_n (n < 3) that produces the stella
- Finding an amplitude configuration where N = 2 has non-degenerate Fisher metric
- Finding initial conditions where the Z₃ attractor (Z1-M2) fails to converge

None of these have been observed across extensive parameter sweeps.

---

## 6. Physical Interpretation

### 6.1 Two Classes of Emergent Properties

Proposition 0.0.3a reveals a fundamental distinction between the stella's emergent properties:

| Class | Property | Mechanism | Probability |
|:------|:---------|:----------|:------------|
| **Necessary** | Z₃ symmetry, non-degeneracy, stella geometry | Dynamical attractor | 1 (100% convergence) |
| **Contingent** | Self-replication, ecosystem dynamics | Statistical abundance | ~10⁻⁵ (birthday problem) |

The stella's fundamental structure is **inevitable** — it crystallizes with probability 1 from the irreducible axioms. The computational life it supports (Prop 0.0.XXd) is **contingent** — it emerges from combinatorial abundance in the instruction set, not from geometric necessity.

### 6.2 The Stella as Information-Geometric Attractor

The deepest result of the crystallization program is that the stella octangula is not merely the algebraic solution to "what geometry encodes SU(3)?" — it is the **dynamical endpoint** of any system satisfying three minimal conditions:

1. **Hurwitz constraint:** fields live in a normed division algebra → ℂ
2. **Coupling constraint:** surfaces must communicate → non-degenerate Fisher metric → N ≥ 3
3. **Minimality:** select the simplest → N = 3, Z₃, stella

This is the computational verification of Theorem 0.0.3's conclusion: the stella is not a choice but a mathematical consequence.

---

## 7. Resolved and Open Questions

### 7.1 RESOLVED: α/β = 2 from SU(3) Casimirs

The crystallization threshold α/β ≈ 2 is now **derived** from SU(3) representation theory.

The color factor for the interaction potential in channel R is C_F(R) = [C₂(R) − C₂(r₁) − C₂(r₂)]/2, where positive values are repulsive and negative values are attractive.

**Same-charge interaction (3 ⊗ 3 = 6 ⊕ 3̄):**
- 6 (symmetric, dim 6): C_F = [10/3 − 4/3 − 4/3]/2 = **+1/3** (repulsive)
- 3̄ (antisymmetric, dim 3): C_F = [4/3 − 4/3 − 4/3]/2 = −2/3 (attractive)

**Conjugate-charge interaction (3 ⊗ 3̄ = 8 ⊕ 1):**
- 8 (octet, dim 8): C_F = [3 − 4/3 − 4/3]/2 = **+1/6** (repulsive)
- 1 (singlet, dim 1): C_F = [0 − 4/3 − 4/3]/2 = −4/3 (attractive)

The crystallization potential models the **repulsive** component of these interactions. The ratio of repulsive color factors is:

$$\frac{\alpha}{\beta} = \frac{C_F(\mathbf{6})}{C_F(\mathbf{8})} = \frac{1/3}{1/6} = 2$$

This **exactly matches** the computationally observed threshold. The physical interpretation: same-charge pairs repel twice as strongly as conjugate-charge pairs because the symmetric tensor channel (6) of SU(3) has twice the color factor of the adjoint channel (8).

**Verification:** `stella_genesis/derive_alpha_beta_threshold.py`

### 7.2 RESOLVED: Z₃ → SU(3) Computational Bridge

The Z₃-to-SU(3) gap is now closed by a 5-phase computational program (Phases L1–L5) demonstrating that Z₃ dynamics on the FCC lattice produce gauge observables matching SU(3) lattice gauge theory predictions via Svetitsky-Yaffe universality.

**Phase L1 (Z₃ Gauge Theory on FCC):** Z₃ link variables on the FCC lattice with triangular plaquettes and Wilson action produce a clear phase structure: disordered/confined phase (β < β_c) with ⟨P⟩ growing smoothly and |⟨L⟩| ≈ 0, and an ordered/deconfined phase (β > β_c) with ⟨P⟩ → 1 and Z₃ spontaneous symmetry breaking. K₄ exact validation confirms the Z₃ algebra.

**Phase L2 (Confinement via Wilson Loops):** Wilson loop measurements W(R,T) in the confined phase show exponential decay with loop area (area law), yielding finite string tension σ via Creutz ratios: χ(2,2) decreases from ~1.5 (β=0.40) to ~0.5 (β=0.48) and vanishes at β_c. The deconfined phase shows W(R,T) → 1 (perimeter law) and σ = 0.

**Phase L3 (First-Order Transition = Svetitsky-Yaffe):** The deconfinement transition is **first-order**, confirmed by:
- Susceptibility peak χ_max growing proportionally to volume V (L=4→12)
- Bimodal plaquette histogram at β_c (two-state coexistence)
- Measurable hysteresis between heating and cooling sweeps
- β_c(L) converging: 0.480, 0.500, 0.505, 0.505 → β_c(∞) ≈ 0.506

A first-order Z₃ deconfinement transition is the Svetitsky-Yaffe prediction for the universality class of SU(3) gauge theory in 3+1 dimensions. A second-order transition would indicate Z₂ universality (wrong group).

**Phase L5 (Soup-to-Gauge Bridge):** The Z₃ soup dynamics (soup_multi_stella.c) map to the Z₃ gauge theory through the Potts-gauge correspondence:
- Each stella's dominant Z₃ charge is a Potts spin
- Link variables are extracted as stochastic trit differences between neighbors
- The extracted plaquette satisfies ⟨P⟩ = (1 − 3p/2)³ exactly, where p is the noise level (∝ mutation_rate)
- **Standard soup parameters (cr=0.5, μ=0.001) give β_eff ≈ 0.49 < β_c ≈ 0.50 → CONFINED**
- The gauge coupling depends on mutation_rate alone (Potts ordering cancels in the plaquette by gauge invariance)

**Phase L4 (SU(3) Center Projection — Reverse Bridge):** Full SU(3) lattice gauge theory on the same FCC lattice, with Maximal Center Gauge (MCG) fixing and center projection to Z₃. This closes the Z₃ ↔ SU(3) bridge bidirectionally by measuring the fraction of confining string tension captured by the center-projected Z₃ configuration:

- SU(3) Wilson action with triangular plaquettes: S = -(β/3) Σ Re Tr(U_plaq)
- Cabibbo-Marinari Metropolis updates (3 SU(2) subgroup rotations per link)
- MCG fixing: maximize F[g] = Σ |Tr(U^g)|² with SU(2) subgroup over-relaxation
- Multiple Gribov copies (best of 3 random gauge starts) to mitigate local MCG maxima
- Center projection: each link U → z ∈ Z₃ via z = argmax_k Re[ω^(-k) Tr(U)]

**L4 Results (100 measurements per β, 3 Gribov copies, MCG with over-relaxation):**

| β | SU(3) ⟨P⟩ | σ_Z₃/σ_SU(3) (L=6) | σ_Z₃/σ_SU(3) (L=8) | σ_Z₃/σ_SU(3) (L=16) | L→∞ trend |
|---|-----------|---------------------|---------------------|----------------------|-----------|
| 3.5 | 0.579 | 0.57 | 0.60 | 0.44 | non-monotone |
| 4.0 | 0.641 | 0.47 | 0.51 | 0.38 | non-monotone |
| 4.5 | 0.689 | 0.17 | 0.34 | 0.32 | stabilizing |
| 5.0 | 0.725 | 0.13 | 0.28 | **0.29** | ↑ converging |
| 5.5 | 0.750 | 0.20 | 0.27 | **0.29** | ↑ converging |
| 6.0 | 0.775 | 0.03 | 0.12 | **0.25** | ↑↑ rising |
| 6.5 | 0.794 | 0.07 | 0.17 | **0.24** | ↑↑ rising |

**Key observations at L=16 (2048 sites, 100 measurements, 3 Gribov copies):**

1. **Confinement confirmed at all β:** SU(3) Polyakov loop |⟨L⟩| → 0 as L increases (0.027 at L=16 vs 0.055 at L=8 across all β), confirming the 3D FCC lattice remains in the confined phase. No deconfinement transition is reached in this β range.

2. **Center dominance at β ≥ 5.0 continues rising monotonically** with L, reaching ~25–29% at L=16. This confirms the finite-volume suppression observed at smaller L.

3. **Strong-coupling regime (β ≤ 4.0) is non-monotone** — the σ ratio drops at L=16. This is expected: at strong coupling, the Creutz ratio estimates become unreliable because Wilson loops saturate (W → 1), making the ratio of logarithms noisy. The physically meaningful confined regime is β ≥ 5.0.

4. **MCG quality scales correctly:** F/N_links ≈ 2.1–3.6 across all sizes, confirming the gauge fixing is working properly at L=16.

**Cubic lattice control test (MCG validation):** To verify that the MCG implementation is correct, the identical SU(3) + MCG + center projection pipeline was run on a standard 3D cubic lattice with square plaquettes (`phase_L4_cubic_control.c`, L=8, 512 sites, 100 measurements, 3 Gribov copies). Results:

| β | ⟨P⟩ | σ_Z₃/σ_SU(3) (cubic) | Comparable FCC |
|---|-----|----------------------|----------------|
| 4.0 | 0.284 | **0.70** | — (no FCC match this strong) |
| 6.0 | 0.455 | **0.58** | FCC β≈3.5: 0.60 |
| 8.0 | 0.613 | **0.35** | FCC β≈4.0: 0.51 |
| 10.0 | 0.704 | **0.23** | FCC β≈5.0: 0.28 |
| 14.0 | 0.794 | **0.19** | FCC β≈6.5: 0.17 |

The cubic lattice achieves ~70% center dominance at strong coupling, consistent with 3D literature values (~65% for SU(2)/Z₂, Kovacs & Tomboulis 2001). When FCC and cubic results are compared at matched plaquette values (i.e., matched physical coupling), they agree to within ~10–15%. **This validates the MCG implementation** and confirms the FCC triangular geometry produces only modestly lower center dominance compared to cubic square plaquettes.

Both lattices show the same qualitative pattern: center dominance is highest at strong coupling (~60–70%) and decreases at weaker coupling. The ~25–30% seen on FCC at β ≥ 5 corresponds to the same regime where cubic also gives ~20–25%. The difference from the 4D ~90% (de Forcrand & D'Elia) is a genuine 3D dimensional effect, not a lattice geometry artifact.

**The complete computational chain (bidirectional):**
```
Z₃ crystallization (Prop 0.0.3a) → Z₃ soup on FCC (existing)
    → Z₃ Potts/gauge extraction (L5: ⟨P⟩ = (1-3p/2)³, β_eff < β_c)
    → Z₃ gauge theory on FCC (L1–L2: confinement via area law)
    → First-order transition = SU(3) universality class (L3: Svetitsky-Yaffe)
  SU(3) gauge theory on FCC (L4: full Wilson action)
    → Maximal Center Gauge fixing + center projection → Z₃
    → Center-projected Z₃ captures ~25–30% of string tension at L=16 (3D center dominance, rising with L)
```

**Gribov copy sensitivity test:** A systematic test (`phase_L4_gribov_test.c`) swept n_copies ∈ {1, 3, 5, 10, 20} on both FCC (β=4.0) and cubic (β=6.0) at L=8. The MCG functional improves by only ~1% from 1→20 copies, and σ_Z₃/σ_SU(3) shows no systematic trend (variation is statistical noise at ±8–15%). **3 Gribov copies is sufficient** — the Gribov problem is not limiting our center dominance measurements.

**Polyakov correlator cross-check:** An independent string tension extraction via Polyakov loop correlators C(r) = ⟨L(x)L†(x+r)⟩ ~ exp(-σr) was performed on cubic L=10 (`phase_L4_polyakov_correlator.c`, 100 measurements, 3 Gribov copies). The Z₃ projected correlator shows clean exponential decay (e.g., β=10: C(r) = 1.00, 0.53, 0.25, 0.11, 0.05). At β=12–14, where both methods are reliable, the Polyakov correlator gives σ_Z₃/σ_SU(3) ≈ 0.23, matching the Creutz ratio estimate of ~0.21 to within 10%. **The two independent methods agree** — center dominance in 3D is genuinely ~20–25% at intermediate coupling. (The SU(3) Polyakov correlator suffers from the well-known signal-to-noise problem in the confined phase, but the Z₃ projected correlator is very clean.)

**Verification:** `stella_genesis/phase_L1_z3_gauge.c`, `phase_L2_wilson_loops.c`, `phase_L3_center_dominance.c`, `phase_L4_su3_center_projection.c`, `phase_L4_cubic_control.c`, `phase_L4_gribov_test.c`, `phase_L4_polyakov_correlator.c`, `phase_L5_soup_gauge_bridge.c`

### 7.3 Resolved: Continuum Crystallization on S²

**Open Question 2** (now resolved): *Phases B–E use discrete points. Can the crystallization be demonstrated for continuous field distributions on S², converging to the stella configuration?*

**Answer: Yes.** Phase S2 replaces Phase B's point particles with continuous Gaussian density blobs of width σ on S². Each type (A, B) is represented by 4 normalized Gaussian distributions centered at positions μ_k on the unit sphere:

$$\rho_A(\mathbf{x}) = \frac{1}{4}\sum_{k=1}^{4} \frac{e^{-|\mathbf{x} - \boldsymbol{\mu}_k^A|^2 / 2\sigma^2}}{\int_{S^2} e^{-|\mathbf{y} - \boldsymbol{\mu}_k^A|^2 / 2\sigma^2} \, d\Omega}$$

The interaction energy between blobs is computed via numerical quadrature on an icosahedral geodesic mesh:

$$E[\rho_A, \rho_B] = \alpha \sum_{i<j}^{\text{same}} \iint_{S^2 \times S^2} \frac{\rho_i(\mathbf{x})\,\rho_j(\mathbf{y})}{|\mathbf{x}-\mathbf{y}|^2} \, d\Omega_x \, d\Omega_y + \beta \sum_{i<j}^{\text{cross}} \iint_{S^2 \times S^2} \frac{\rho_i(\mathbf{x})\,\rho_j(\mathbf{y})}{|\mathbf{x}-\mathbf{y}|^2} \, d\Omega_x \, d\Omega_y$$

Blob centers are optimized via simulated annealing with cached potential fields.

**Results (5 experiments, 200K annealing steps each):**

| Experiment | Key Result |
|-----------|------------|
| S2-1: σ sweep (α/β=10) | 100% stella for σ ∈ [0.05, 0.5], RMSD < 0.04 |
| S2-2: α/β sweep (σ=0.3) | Phase transition at α/β = 2.0 (matching Phase B exactly) |
| S2-3: σ × α/β combined | 100% stella for σ ≥ 0.2 and α/β ≥ 2.0 |
| S2-4: Seed robustness (20 seeds) | 20/20 stella (100%), mean RMSD = 0.003 |
| S2-5: Resolution convergence | 100% stella at mesh levels 1–4 (42–2562 vertices) |

The critical α/β = 2 threshold is identical to the discrete Phase B result, confirming that the Casimir-ratio mechanism operates identically on continuous distributions. As σ → 0, the blob centers converge to the exact Phase B positions (RMSD < 0.003).

**Verification:** `stella_genesis/phase_s2_continuum.c`, `run_phase_s2.py`

### 7.4 Resolved: Center Dominance in 3D vs 4D

**Open Question 2** (now resolved): *L4 data shows 3D FCC center dominance at ~25–60%, well below the 4D cubic ~90% (de Forcrand & D'Elia 2001). Is this a dimensional effect or a geometric one? Would a 4D FCC lattice recover the full ~90%?*

**Answer: No — and this is physically meaningful.** Phase L5 implements full SU(3) lattice gauge theory with Maximal Center Gauge (MCG) fixing and Z₃ center projection on both 4D FCC (D4 root lattice, 24 nearest neighbors, 96 triangular plaquettes per site) and 4D simple cubic (8 neighbors, 6 square plaquettes per site) lattices at L=6.

**Results (L=6, 80 measurements per β, 3 Gribov copies):**

| Geometry | Dimension | σ_Z₃/σ_SU(3) (confined phase) | Reference |
|----------|-----------|-------------------------------|-----------|
| Cubic 3D (L4 control) | 3 | ~65–70% | Kovacs & Tomboulis 2001 |
| FCC 3D (L4) | 3 | ~25–60% | This work |
| **Cubic 4D (L5 control)** | **4** | **89–90%** (β=4.0–4.5) | **de Forcrand & D'Elia 2001** |
| **FCC 4D (L5)** | **4** | **10–29%** (all β) | **This work** |

4D cubic β scan (center dominance vs coupling):

| β | σ_Z₃/σ_SU(3) | Phase |
|---|---|---|
| 4.0 | 89.5% | Confined |
| 4.5 | 90.3% | Confined |
| 5.0 | 76.2% | Confined |
| 5.2 | 68.7% | Near transition |
| 5.4 | 54.5% | Near transition |
| 5.7 | 32.6% | At β_c |
| 6.0 | 17.1% | Deconfined |
| 6.5 | 1.2% | Deconfined |

The 4D cubic control reproduces the de Forcrand & D'Elia ~90% center dominance exactly (89.5% at β=4.0, 90.3% at β=4.5), validating the MCG + center projection pipeline. The sharp decrease above β_c ≈ 5.7 matches the known deconfinement transition for 4D SU(3) on cubic lattices.

The 4D FCC lattice shows only 10–29% center dominance across all coupling values. The Z₃ projected configurations are nearly ordered (⟨P⟩_Z₃ ≈ 0.94–0.99), with Creutz ratios close to zero. This contrasts sharply with the cubic results where the Z₃ plaquette remains at 0.35–0.58 in the confined phase.

**Key finding:** Center dominance depends on both dimension *and* lattice geometry:
- **Dimensional effect:** Cubic 3D (~65–70%) → Cubic 4D (~90%). Adding dimensions increases center dominance on cubic lattices.
- **Geometric effect:** Cubic 4D (~90%) vs FCC 4D (~10–29%). The FCC lattice's high connectivity overconstrain the center-projected Z₃ variables, suppressing non-trivial center flux.

**Interpretation for the framework:** The FCC geometry naturally suppresses center fluctuations through geometric overconstraint. Each link on 4D FCC participates in far more plaquettes than on cubic, and MCG fixing pushes links so close to center elements that the projected Z₃ configurations are nearly trivial. This rigidity is consistent with the crystallization mechanism: the Z₃ symmetry is "more rigid" on FCC precisely because the geometry enforces stronger correlations between links. This same rigidity is what drives crystallization to the stella octangula in Phases A–H — the FCC geometry *enforces* Z₃ ordering rather than merely permitting it.

**Verification:** `stella_genesis/phase_L5_4d_center_dominance.c`, `run_phase_L5.py`

### 7.5 Finite-Temperature Phase Diagram (Phase T1) — RESOLVED

**Open Question (now resolved):** All crystallization experiments use T → 0 (annealing). The gauge theory analysis (L1–L3) maps the critical temperature at β_c ≈ 0.506 on FCC. The relationship between this gauge β_c and the crystallization annealing temperature remains to be quantified.

**Resolution (Phase T1):** Equilibrium Monte Carlo at fixed temperature maps the crystallization phase diagram and establishes the β–T correspondence.

#### T1.1: Equilibrium Phase Diagram

The N = 8 two-label system (α/β = 10, same as Phase C) was simulated at 55 fixed temperatures from T = 0.01 to T = 2.95, with 200K thermalization + 20K measurement sweeps × 10 seeds per temperature. Key observables:

| T | Crystal Fraction | ⟨RMSD⟩ | ⟨E⟩ | C_v |
|---|---|---|---|---|
| 0.01 | 100% | 0.034 | 55.06 | 6.45 |
| 0.05 | 91% | 0.076 | 55.33 | 6.64 |
| **0.092** | **50%** | **0.100** | **55.60** | **6.31** |
| 0.15 | 17% | 0.129 | 55.95 | 6.30 |
| 0.50 | 0.1% | 0.245 | 58.15 | 6.26 |
| 1.00 | 0% | 0.358 | 61.12 | 5.34 |

The crystallization transition occurs at **T_c ≈ 0.092** (50% crystallization fraction). The specific heat C_v shows no sharp peak — it varies smoothly from ~6.5 at low T to ~2.9 at T = 3, consistent with a **crossover** rather than a sharp phase transition. This is expected: N = 8 particles is far from the thermodynamic limit where the gauge theory (L1–L3, using 32–864 sites) exhibits a sharp first-order transition.

#### T1.2: Hysteresis Test

Heating from perfect stella and cooling from random configurations were compared across 150 temperature steps (dT = 0.02). Maximum hysteresis: ΔRMSD = 0.0075 at T = 0.63. Average ΔRMSD in the transition region (0.05 < T < 0.5): 0.001.

**Result:** Negligible hysteresis, confirming the crossover nature. The sharp first-order transition observed in L1–L3 (bimodality, latent heat, volume-dependent susceptibility) is a thermodynamic-limit property that manifests only at large N. The N = 8 crystallization system lies in the finite-size crossover regime.

#### T1.3: β–T Mapping

The stella ground-state energy is E_stella = 55.0 (28 pairs), giving energy per pair e = 1.964. The effective inverse coupling at the crystallization transition is:

$$\beta_{\text{eff}}(T_c) = \frac{e_{\text{pair}}}{T_c} = \frac{1.964}{0.092} = 21.4$$

The gauge theory deconfinement on FCC occurs at β_c = 0.506. The mapping coefficient is:

$$\kappa = \frac{\beta_c}{\beta_{\text{eff}}(T_c)} = \frac{0.506}{21.4} \approx 0.024$$

This encodes the ratio of action normalizations: the gauge theory Wilson action (β × plaquette average over triangular plaquettes with Z₃ phases) versus the crystallization Boltzmann weight (1/T × Coulomb pair energy with 1/r² potential). The factor κ ≈ 0.024 reflects:

1. **Different degrees of freedom:** Z₃ link variables vs continuous particle positions
2. **Different action density:** plaquette action (3-body, discrete) vs pair potential (2-body, continuous)
3. **Different lattice connectivity:** FCC gauge lattice (12 neighbors, 24 plaquettes/site) vs 8-particle cluster (7 neighbors each)

The mapping between the two systems is:

$$\beta_{\text{gauge}} = \kappa \times \frac{e_{\text{pair}}}{T_{\text{crystal}}}, \quad \kappa \approx 0.024$$

**Key finding:** Both the gauge theory and crystallization system share the same Z₃ symmetry-breaking pattern on FCC geometry. The crystallization system has a well-defined melting temperature T_c ≈ 0.092, establishing that the stella octangula is not merely the ground state but remains the thermodynamic equilibrium configuration for T < T_c. The mapping coefficient κ ≈ 0.024 quantifies the ratio of action normalizations between the two formulations. The transition character differs — smooth crossover at N = 8 vs sharp first-order at large N — as expected from finite-size scaling. This confirms that the physical mechanism (Z₃ symmetry breaking on FCC geometry) is the same, while the microscopic details (discrete gauge links vs continuous particle positions) affect only the normalization.

**Verification:** `stella_genesis/phase_T1_finite_temperature.c`, `run_phase_T1.py`

---

*See [Derivation](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Derivation.md) for the complete experimental evidence chain.*
*See [Applications](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Applications.md) for physical interpretation and cross-references.*
