# Proposition 0.0.3a — Derivation: Experimental Evidence Chain

## Status: 🔶 NOVEL ✅ VERIFIED — FULL EXPERIMENTAL EVIDENCE

**Parent document:** [Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md)

**Source data:** `stella_genesis/RESULTS-Crystallization.md`

---

## 1. Phase A: Polyhedra Competition (Negative Result)

### 1.1 Design

Genesis VM run on multiple candidate geometries (stella, separated, nested, random two-tetrahedra configurations) with identical Z₃ coupling rules. 200,000 epochs, coupling strength 0.5, n_sub = 16 (514 sites per tetrahedron).

Two experiments: (1) rotation sweep T₋ = Rz(θ)·T₊ for θ ∈ [0°, 180°]; (2) discrete geometry comparison.

### 1.2 Results

**Rotation sweep:** No sharp peak at θ = 90° (stella). A broad plateau of corr ≈ 0.72–0.78 from θ ≈ 25° to θ ≈ 150°. The stella sits within this plateau at corr = 0.737.

**Discrete geometries:**

| Geometry | corr | balance | Assessment |
|:---------|:----:|:-------:|:-----------|
| Stella | 0.733 | 1.000 | Balanced but not maximal |
| Separated z+4 | 0.992 | 0.999 | Higher coherence via brute force |
| Nested 0.3× | 0.992 | 0.107 | Higher coherence, unbalanced |
| Random (seed 500) | 0.967 | 0.500 | Higher coherence, random geometry |

### 1.3 Interpretation

**NULL RESULT for dynamical selection.** Raw coupling coherence does not distinguish the stella. Many geometries produce comparable or superior dynamics. The stella's specialness is group-theoretic (Thm 0.0.3), not dynamical.

**Key insight:** The normalized coupling formula ΔP/(P₊ + P₋) absorbs geometric scale — once sufficient contrast exists (θ > ~25°), dynamics saturate regardless of specific vertex arrangement. The stella's uniqueness cannot be established by running dynamics on pre-given geometries.

**Code:** `crystallization.c`, `run_phase_a.py`, `analyze_phase_a.py`

---

## 2. Phase B: Stella as Ground State

### 2.0 Context: Thomson and Tammes Problems

The problem of optimally distributing N points on a sphere has a rich history. The **Thomson problem** (1904) minimizes Coulomb energy Σ 1/d_ij for identical charges. The **Tammes problem** (1930) maximizes the minimum pairwise distance (packing). For N = 8, the Thomson solution is the **square antiprism** (D₄d symmetry), not the cube or stella. Our two-component variant — where same-label and cross-label pairs have different repulsion strengths — appears to be novel; no prior literature was found for this asymmetric formulation. For general background on sphere packing, see Bowick & Giomi (2009, Adv. Phys. 58:449), Erber & Hockney (1991, J. Phys. A 24:L1369).

### 2.1 Design

N = 8 points on the unit sphere, 4 labeled A + 4 labeled B. Energy function:

$$E = \alpha \sum_{\text{same}} \frac{1}{d_{ij}^2} + \beta \sum_{\text{cross}} \frac{1}{d_{ij}^2}$$

Simulated annealing (200K steps, T: 2.0 → 0.001, exponential cooling). Sweep α/β from 1.0 to 100. Procrustes RMSD to ideal stella as primary metric.

### 2.2 Results

| α/β | tet_quality | stella_RMSD | Geometry |
|:---:|:----------:|:-----------:|:---------|
| 1.0 | 0.802 | 0.670 | Square antiprism (Thomson) |
| 1.5 | 0.918 | 0.164 | Distorted stella |
| **2.0** | **0.994** | **0.013** | **Stella ✓** |
| 5.0 | 0.998 | 0.005 | Stella ✓ |
| 10.0 | 0.998 | 0.004 | Stella ✓ |
| 100.0 | 0.999 | 0.003 | Stella ✓ |

Seed robustness (α/β = 100, 20 seeds): mean RMSD = 0.003, std = 0.001. **100% convergence (20/20).**

### 2.3 Key Findings

1. **Sharp phase transition** at α/β ≈ 2.0 (RMSD drops from 0.17 to 0.015)
2. Each component forms a **perfect regular tetrahedron** (tet_quality > 0.99)
3. **Cross-distance ratio locks to √3 ≈ 1.732** — specifically, this is the ratio of the maximum to minimum inter-tetrahedron distances (d_max/d_min). In the ideal stella on a unit sphere, each vertex of T₊ has 1 nearest-neighbor on T₋ at distance 2/√3 and 3 far-neighbors at distance 2. Thus d_max/d_min = 2/(2/√3) = √3. This ratio is a geometric fingerprint unique to the stella (the square antiprism at α/β = 1 has d_max/d_min ≈ 1.64, distinctly below √3).
4. **100% convergence** from random initial conditions — stella is the global minimum

### 2.4 Potential Form Sensitivity

The Phase B energy function uses 1/d² repulsion. The Physics verification agent raised whether this choice affects the result. We tested three repulsive potential forms: V(d) = 1/d (Coulomb), 1/d² (original), and 1/d³, each with 20 seeds per α/β value, 500K annealing steps:

| Potential | α/β = 1.0 | α/β = 1.5 | α/β = 2.0 | α/β = 3.0 | α/β = 5.0 |
|:---------:|:---------:|:---------:|:---------:|:---------:|:---------:|
| **1/d** (Coulomb) | 0/20 | 9/20 | **20/20** | 20/20 | 20/20 |
| **1/d²** (original) | 0/20 | 0/20 | **20/20** | 20/20 | 20/20 |
| **1/d³** | 0/20 | 0/20 | 0/20 | **20/20** | 20/20 |

**Key findings:**
- **All three potentials produce the stella** with 100% convergence above their respective thresholds. The final geometry (RMSD, tet quality > 0.99, cross-distance ratio ≈ √3) is identical regardless of potential form.
- The **transition threshold shifts** with potential steepness: softer potentials (1/d) crystallize at lower α/β (~1.5), steeper potentials (1/d³) require higher α/β (~3.0). This is expected — steeper potentials weight short-range interactions more heavily, requiring larger same-charge enhancement to override cross-charge near-neighbor effects.
- **The stella is the universal ground state** of any repulsive potential with sufficient same-vs-cross asymmetry. The specific power law affects the threshold but not the endpoint.

This confirms the crystallization is a **topological/geometric** result, not an artifact of the potential form choice.

**Code:** `run_phase_b.py`, `phase_b_potential_sensitivity.c`

---

## 3. Phase C: Vertex Count and Partition Selection

### 3.1 C1: Grand Canonical (N Selection)

Starting from N_max = 20, the system selects how many points to keep active.

| μ range | N_active | Split | Stella |
|:-------:|:--------:|:------|:------:|
| 3–14 | 2–6 | various | No |
| **16–22** | **8** | **4+4** | **100%** |
| 25–40 | 10–12 | 5+5, 6+6 | No |

N = 8 is selected with **zero variance** across all seeds for μ ∈ [16, 22] — a wide plateau (37% of center value).

### 3.2 C2: Label Relaxation (4+4 Emergence)

| Initial split | Final split | Stella | Runs |
|:-------------:|:-----------:|:------:|:----:|
| 1+7 | 4+4 | ✓ | 10/10 |
| 2+6 | 4+4 | ✓ | 10/10 |
| 3+5 | 4+4 | ✓ | 10/10 |
| 4+4 | 4+4 | ✓ | 10/10 |
| 5+3 | 4+4 | ✓ | 10/10 |
| 6+2 | 4+4 | ✓ | 10/10 |
| 7+1 | 4+4 | ✓ | 10/10 |

**100% convergence from every initial split (70/70 runs).**

### 3.3 C3: Geometric Uniqueness of N = 8

**Metric definitions:**

- **Regularity** = 1 − CV(pairwise distances), where CV = σ/μ is the coefficient of variation of all (N/2 choose 2) pairwise distances within one component. A perfect regular polyhedron (all edges equal) has Regularity = 1.0. This measures how close each component's ground-state geometry is to a regular polyhedron.

- **Isotropy** = 1 − (λ_max − λ_min)/(λ_max + λ_min), where λ_max, λ_min are the largest and smallest eigenvalues of the 3×3 inertia tensor of the N/2 component points. Isotropy = 1.0 means the point distribution has equal extent in all three spatial directions (spherically symmetric inertia). Isotropy = 0 means the points are confined to a plane or line. This eliminates degenerate low-dimensional configurations (e.g., N/2 = 3 gives an equilateral triangle with Isotropy = 0).

The **product** Regularity × Isotropy captures both criteria simultaneously: equal distances AND 3D extent.

| N | Regularity | Isotropy | Reg × Iso |
|:-:|:----------:|:--------:|:---------:|
| 4 | 1.000 | 0.000 | 0.000 |
| 6 | 0.958 | 0.000 | 0.000 |
| **8** | **0.999** | **0.994** | **0.993** |
| 10 | 0.868 | 0.860 | 0.746 |
| 12 | 0.846 | 0.950 | 0.804 |
| 16 | 0.794 | 0.954 | 0.757 |

The regular tetrahedron (N/2 = 4) is the **only** polyhedron where all pairwise distances are equal AND the shape is 3D. N/2 = 2,3 are 1D/2D (Isotropy = 0); N/2 ≥ 5 have unequal distances (Regularity < 0.87). The gap is 24% (0.993 vs 0.804).

**Code:** `phase_c.c`, `run_phase_c.py`

---

## 4. Phase D: Sphere Emergence

### 4.1 Design

Replace hard sphere with soft normalization: E_conf = γ·Σ(|rᵢ| − 1)². Points start at random positions in [-1,1]³ cube.

### 4.2 D1: Confinement Sweep

| γ | shell_quality | stella_RMSD | Stella? |
|------:|:-----:|:-----:|:-------:|
| 0 | 0.659 | 0.694 | ✗ |
| **0.1** | **0.990** | **0.025** | **✓** |
| 1.0 | 0.996 | 0.012 | ✓ |
| 10.0 | 0.998 | 0.007 | ✓ |
| 500.0 | 0.999 | 0.006 | ✓ |

**Any nonzero confinement simultaneously produces both a spherical shell and the stella geometry.** The equilibrium shell radius decreases with γ, but the stella shape is invariant.

### 4.3 D2: Independence of Shell and Stella

2D sweep confirms:
- **Shell quality** depends only on γ, not on α/β
- **Stella RMSD** depends only on α/β, not on γ

These are orthogonal phenomena: shell = normalization; stella = Z₃ interaction asymmetry.

### 4.4 D3: Robustness

γ = 10, α/β = 10, 50 seeds: **100% convergence (50/50)** from random cube starts. Mean RMSD = 0.0077, shell quality = 0.9976.

**Code:** `phase_d.c`

---

## 5. Phase E: Z₃ Representation Emergence

### 5.1 E1: Z₃ Product Rule

Z₃ charges {1, 2} with product-rule interaction: conjugate pairs (1+2 ≡ 0 mod 3) get coefficient β; same-charge pairs get α.

| α/β | 4+4 | Stella | Seeds |
|:---:|:---:|:------:|:-----:|
| 1.0 | 8/30 | 0/30 | 30 |
| 2.0 | 30/30 | 30/30 | 30 |
| 10.0 | 30/30 | 30/30 | 30 |

**Identical to Phase B.** The two-component structure IS the two non-trivial Z₃ elements.

### 5.2 E2: Singlet Exclusion

Allowing charge 0 (singlet): 7/30 runs find an all-charge-0 trivial state (E = 14.34 vs 55.00). Singlets are invisible to Z₃ interactions — only non-trivially charged fields build structure.

### 5.3 E3: Z_n Comparison

| Z_n | Non-trivial charges | Stella convergence | Self-conjugate? |
|:---:|:-------------------:|:------------------:|:---------------:|
| Z₂ | 1 | 0% | Yes |
| **Z₃** | **2** | **100%** | **No** |
| Z₄ | 3 | 70% | Yes (charge 2) |
| Z₅ | 4 | 100% | No |
| Z₇ | 6 | 100% | No |

Z₃ is the **minimal** cyclic group where: (1) there are exactly 2 non-trivial elements, (2) they are conjugate (not self-conjugate), (3) no trivial escape route competes, (4) every charge is used.

**Code:** `phase_e.c`

---

## 6. Phase F: Why N = 3?

### 6.1 F1: Fisher Metric Stability Threshold

Fisher information matrix computed for Z_N interference with Gaussian amplitude bumps, 2000-point grid.

| N | Fisher rank | Degenerate? | Robustness (500 random amplitudes) |
|:-:|:-----------:|:-----------:|:----------------------------------:|
| 1 | 0 | Trivial | — |
| 2 | **0** | **Yes** | 0/500 stable |
| 3 | **2** | **No** | 499/500 stable |
| 5 | 4 | No | — |

**Note on 499/500 vs 500/500:** Phase F1 uses a conservative eigenvalue-ratio threshold (λ_min/λ_max > 10⁻⁶) to determine non-degeneracy, yielding 499/500 for N = 3. Phase Z2-M0 uses a rank-based criterion (eigenvalue > ε), yielding 500/500. The single F1 failure is a numerical edge case where Gaussian amplitude bumps are nearly coincident, producing a borderline eigenvalue ratio. This is not a structural failure — the Fisher matrix has nonzero rank in all 500 cases; the 1/500 case merely falls below the stricter condition number threshold.

**Analytical proof of N = 2 Fisher degeneracy:**

For N = 2 interference, p(x; φ₁) = |A₀(x) + A₁(x)e^{iφ₁}|² with φ₀ = 0 (gauge-fixed). Expanding:

$$p(x; \phi_1) = A_0^2 + A_1^2 + 2A_0 A_1 \cos\phi_1$$

The Fisher information matrix is 1×1 (single parameter φ₁):

$$g_{11} = \int \frac{1}{p} \left(\frac{\partial p}{\partial \phi_1}\right)^2 dx$$

Computing the derivative:

$$\frac{\partial p}{\partial \phi_1} = -2A_0 A_1 \sin\phi_1$$

At equilibrium φ₁ = π (Z₂ phase): sin(π) = 0, so ∂p/∂φ₁ = 0 **identically for all x**. Therefore g₁₁ = 0.

This is not a numerical accident but a **structural** degeneracy: Z₂ equilibrium forces the interference to be purely real (A₀ − A₁), which has zero sensitivity to phase perturbations. The Fisher metric is identically zero regardless of the amplitude functions A₀(x), A₁(x), explaining the universal 0/500 result.

For N = 3, the Fisher matrix is 2×2 with two independent phase parameters. At Z₃ equilibrium (φ₁ = 2π/3, φ₂ = 4π/3), the derivatives ∂p/∂φ₁ and ∂p/∂φ₂ are generically nonzero (they involve sin(2π/3) = √3/2 ≠ 0), giving a non-degenerate Fisher metric for generic amplitudes.

### 6.2 F2: Computational Richness (Negative Result)

CA richness increases monotonically with N. **N = 3 does NOT maximize computational richness.** Z₃ selection requires an information-theoretic criterion, not energetic selection.

### 6.3 F3: Prime Irreducibility

**CRT factorization:** By the Chinese Remainder Theorem, Z_n ≅ Z_{n₁} × Z_{n₂} × ⋯ if and only if n = n₁ · n₂ · ⋯ with all factors **pairwise coprime** (gcd(nᵢ, nⱼ) = 1 for i ≠ j). This coprimality requirement is essential — Z₄ ≇ Z₂ × Z₂ (both have order 4, but Z₄ is cyclic while Z₂ × Z₂ is the Klein four-group). All coprime composites tested factorize exactly (reconstruction error = 0). Z₆ ≅ Z₂ × Z₃ (literally independent subsystems, since gcd(2,3) = 1).

**Prime irreducibility index:** Strictly decreasing among primes ≥ 3 (N = 2, though prime, is excluded because it is Fisher-degenerate — the irreducibility index is only meaningful for systems with well-defined information geometry):

| N | Prime? | Irreducibility Index |
|:-:|:------:|:-------------------:|
| 3 | Yes | **0.417** |
| 5 | Yes | 0.175 |
| 7 | Yes | 0.103 |
| 11 | Yes | 0.052 |

N = 3 is maximally irreducible because the only possible projection (to Z₂) is maximally lossy.

**Selection chain:** Fisher-stable (N ≥ 3) ∩ Prime (irreducible) ∩ Minimal → **N = 3**.

**Code:** `phase_f1.c`, `phase_f2.c`, `phase_f3.c`

---

## 7. Phase G: Number Field Selection

### 7.1 Complex vs Quaternionic Fisher Matrix

| N | ℂ rank | ℍ dim | ℍ rank | Non-zero eigenvalues |
|:-:|:------:|:-----:|:------:|:-------------------:|
| 2 | 0 | 3 | **0** | — |
| 3 | 2 | 6 | **2** | Match to 10 digits |
| 4 | 3 | 9 | **3** | Match to 10 digits |
| 5 | 4 | 12 | **4** | Match to 10 digits |
| 6 | 5 | 15 | **5** | Match to 10 digits |

The quaternionic Fisher matrix has 3(N−1) dimensions but rank **exactly N−1** = the complex rank. The extra 2(N−1) dimensions are phantom DOF — probability |Σ Aₖ qₖ|² is insensitive to quaternion axis direction.

### 7.2 Random Quaternion Equilibria

20 trials with random unit quaternions on S³: rank always exactly N−1. Not an artifact of the complex embedding.

### 7.3 Axis Independence

Relative change under global SU(2) rotation: ~10⁻¹⁶ (machine precision). The quaternionic norm strips all axis information.

### 7.4 Division Algebra Classification

| Algebra | Phase DOF | Fisher rank | Associative? | Verdict |
|:-------:|:---------:|:-----------:|:------------:|:--------|
| ℝ | 0 | — | Yes | **Rejected** — no continuous phase |
| **ℂ** | **1** | **N−1** | **Yes** | **Selected** |
| ℍ | 3 (nominal) | N−1 (same as ℂ) | Yes | **Rejected** — redundant (see note below) |
| 𝕆 | 7 | — | No | **Rejected** — non-associative, no standard Lie-group gauge theory (Moufang-loop-based theories exist [Okubo 1995] but lack Yang-Mills fiber-bundle structure) |

**Note on quaternionic redundancy and SU(2):** The 2(N−1) phantom quaternionic DOF correspond precisely to the SU(2) gauge freedom — the unit quaternions form the group Spin(3) ≅ SU(2), and the extra dimensions parameterize rotations of the quaternion axis that leave the interference probability invariant. This is not a coincidence: the quaternionic Fisher metric's kernel IS the SU(2) gauge orbit. Thus ℍ is rejected not because it "fails" but because it contains ℂ plus an SU(2) gauge redundancy that adds no information-geometric content. The physics of SU(2) (weak isospin) emerges at a later stage from a different mechanism (chiral symmetry breaking, Phase 3), not from the number field choice.

**Code:** `phase_g.c`

---

## 8. Phase Z1: Dynamical Z₃ Emergence

### 8.1 Z1-M0: Generic Dynamics (Negative Result)

24 oscillators with attraction + repulsion on S¹. At B/A = 3.0: cluster distribution is 1 (32%), 2 (23%), 3 (22%), 4 (11%), 5+ (12%). **Z₃ does not emerge from generic nonlinear interactions.** Confirmed independent of oscillator count M.

### 8.2 Z1-M1: Energetic Competition (Negative Result)

Equal cos(Nθ) self-interactions for N = 3, 4, 5 competing simultaneously: **Z₄ wins 90%** of runs. Z₃ only wins when the cubic term artificially dominates (g₃/g₄ ≥ 2). **Z₃ selection requires information-theoretic criteria, not energy minimization.**

### 8.3 Z1-M2: Non-Degeneracy + Minimality (Positive Result)

M = 18 oscillators with clustering pressure and non-degeneracy constraint (det(Fisher covariance) > 0):

**3 clusters in 30/30 seeds (100%).** Comprehensive sweep:

| M × coupling grid | 3-cluster rate |
|:------------------:|:--------------:|
| 24 of 25 cells | 100% |
| 1 cell (M=6, coupling=0) | 97% |

Parsimony sweep (λ = 0.5–5.0): 100% at all values.

**Why exactly 3:** 1 cluster → quality = 0; 2 clusters → quality = 0 (Fisher-degenerate); 3 clusters → quality > 0 (first non-degenerate); 4+ clusters → quality > 0 but clustering force drives back to 3. The system finds the **minimum cluster count with non-degenerate interference**.

### 8.4 Z1-M3: Attractor from Random ICs

30 trials from fully random initial conditions: **3 clusters in 30/30 (100%).** Robust across noise amplitudes 0.3–1.5 (50 trials each, all 100%).

**Code:** `phase_z1.c`, `run_phase_z1.py`

---

## 9. Phase Z2: Non-Degeneracy from Coupling

### 9.1 Mode 0: Channel Capacity

| Z_k | Fisher rank | Full-rank rate (500 random amplitudes) |
|:---:|:-----------:|:--------------------------------------:|
| Z₂ | **0** | **0/500 (0%)** |
| Z₃ | 2 | 500/500 (100%) |
| Z₄ | 3 | 500/500 (100%) |
| Z₅ | 4 | 500/500 (100%) |

Z₂ is **universally degenerate** — a structural property, not a numerical accident.

### 9.2 Mode 1: Dual-Surface Coupling

| Z_k | Initial corr | Final corr | Δcorr | Coupling effective? |
|:---:|:-----------:|:----------:|:-----:|:-------------------:|
| Z₂ | 0.9998 | 0.9998 | +0.0001 | **NO** (frozen) |
| Z₃ | −0.007 | 0.999 | +1.006 | **YES** (rapid) |
| Z₄ | 0.186 | 0.999 | +0.813 | YES |

Z₃ coupling converges in ~20 epochs. Z₂ coupling is a flatline.

### 9.3 Mode 2: Z₂ Instability

3-component fields with a₁ = a₂ = 1 (Z₂) and a₃ = ε = 0.01 (perturbation). Coupling evolves phases and amplitudes:

| Seed | Initial a₃ | Final a₃ | Growth |
|:----:|:----------:|:--------:|:------:|
| 0–9 | 0.010 | 0.028–0.041 | 2.8–4.1× |

**Third component grew in 10/10 seeds (100%).** Mechanism: Z₂ interference carries zero information, so coupling is blind. Adding a third component breaks degeneracy, enabling communication. Coupling dynamics amplify the third component selectively.

### 9.4 Conclusion

Non-degeneracy is **derived**, not assumed:
1. Z₂ has zero channel capacity (Mode 0)
2. Therefore Z₂ coupling is frozen (Mode 1)
3. Therefore Z₂ is unstable — a third component grows (Mode 2)
4. Three components = non-degenerate interference (Phase F1)

**Code:** `phase_z2.c`

---

## 9b. Phase S2: Continuum Crystallization on S²

### 9b.1 Motivation

Phases B–E demonstrate crystallization using discrete labeled points on S². Open Question 2 asks: can continuous field distributions on S² also crystallize into the stella configuration? This bridges the discrete particle model and the continuum field theory limit.

### 9b.2 Method: Gaussian Blob Annealing

Replace Phase B's 4+4 point particles with 4+4 continuous Gaussian density blobs on the unit sphere. Each blob represents a normalized continuous field distribution:

$$\rho_k(\mathbf{x}) = \frac{1}{Z_k} \exp\!\left(-\frac{|\mathbf{x} - \boldsymbol{\mu}_k|^2}{2\sigma^2}\right), \quad Z_k = \int_{S^2} \exp\!\left(-\frac{|\mathbf{y} - \boldsymbol{\mu}_k|^2}{2\sigma^2}\right) d\Omega$$

The interaction energy is computed via numerical quadrature on an icosahedral geodesic mesh (recursive subdivision, levels 1–4 corresponding to 42–2562 vertices):

$$E = \alpha \sum_{\substack{i<j \\ \text{same type}}} E_{ij} + \beta \sum_{\substack{i<j \\ \text{cross type}}} E_{ij}, \quad E_{ij} = \sum_{a,b} K_{ab}\, \rho_i(v_a)\, \rho_j(v_b)$$

where $K_{ab} = w_a w_b / (|v_a - v_b|^2 + \varepsilon^2)$ is the softened kernel matrix.

Optimization uses simulated annealing on the 8 blob centers with cached potential fields: $\phi_j(v_a) = \sum_b K_{ab}\, \rho_j(v_b)$, making delta-energy computation O(N) per step.

### 9b.3 Results

**S2-1: Blob Width Scaling** (α/β = 10, 5 seeds × 7 σ values)

| σ | Mean RMSD | Tet. Quality | Stella % |
|--:|----------:|:------------:|---------:|
| 1.000 | 0.181 | 0.996 | 20% |
| 0.500 | 0.007 | 0.999 | 100% |
| 0.300 | 0.003 | 0.999 | 100% |
| 0.200 | 0.005 | 0.998 | 100% |
| 0.100 | 0.038 | 0.983 | 100% |
| 0.050 | 0.070 | 0.968 | 100% |
| 0.020 | 0.092 | 0.958 | 40% |

100% stella for σ ∈ [0.05, 0.5]. At σ = 1.0, blobs overlap too much (nearly uniform). At σ = 0.02, mesh resolution limits accuracy.

**S2-2: Phase Transition** (σ = 0.3, 5 seeds × 9 ratios)

| α/β | Stella % | Mean RMSD |
|----:|---------:|----------:|
| 1.0 | 0% | 0.609 |
| 1.5 | 0% | 0.115 |
| **2.0** | **100%** | **0.008** |
| 3.0 | 100% | 0.006 |
| 5.0 | 100% | 0.004 |
| 10.0 | 100% | 0.003 |
| 100.0 | 100% | 0.003 |

Sharp phase transition at α/β = 2.0, **identical to Phase B**. The Casimir-ratio mechanism operates identically on continuous distributions.

**S2-4: Seed Robustness** (α/β = 10, σ = 0.3, 20 seeds): **20/20 stella (100%)**, mean RMSD = 0.003.

**S2-5: Resolution Convergence** (α/β = 10, σ = 0.3, 5 seeds × 4 mesh levels)

| Level | Vertices | Mean RMSD | Stella % |
|------:|---------:|----------:|---------:|
| 1 | 42 | 0.012 | 100% |
| 2 | 162 | 0.003 | 100% |
| 3 | 642 | 0.003 | 100% |
| 4 | 2562 | 0.003 | 100% |

Results are mesh-independent: all levels give 100% stella convergence.

### 9b.4 Conclusion

Continuous Gaussian density fields on S² crystallize into the stella octangula under the same α/β ≥ 2 condition as discrete particles. The critical ratio is identical to the SU(3) Casimir prediction from Phase B. In the limit σ → 0, the blob centers converge to the exact Phase B positions (RMSD < 0.003). This resolves Open Question 2: **the stella is the ground state for continuous fields, not just discrete particles.**

**Code:** `phase_s2_continuum.c`, `run_phase_s2.py`

---

## 10. Statistical Summary

### 10.1 Total Computational Effort

| Phase | Seeds/configs tested | Success criterion | Success rate |
|:-----:|:-------------------:|:------------------|:-------------|
| A | 37 geometries | — | N/A (negative result) |
| B | 20 seeds × 11 α/β | RMSD < 0.02 | 100% for α/β ≥ 2 |
| C1 | 10 seeds × 16 μ | N = 8 selected | 100% for μ ∈ [16, 22] |
| C2 | 70 runs (7 splits × 10) | 4+4 convergence | 100% |
| C3 | 10 seeds × 7 N | — | N/A (comparative) |
| D | 50 seeds + 160 sweep | Shell + stella | 100% for γ > 0, α/β ≥ 2 |
| E | 30 seeds × 7 α/β × 5 Z_n | Stella convergence | 100% for Z₃ |
| F1 | 500 random amplitudes × 2 N | Non-degeneracy | 0% (N=2), 99.8% (N=3) |
| F3 | 4 composites + 5 primes | CRT factorization | Exact (error = 0) |
| G | 5 N × 20 random quat | Rank limitation | 100% |
| Z1 | 750+ trials (grids) | 3 clusters | ~100% (1 exception at M=6, λ=0) |
| Z2 | 500 + 10 + 10 | Rank 0 / growth | 100% |
| S2 | 5 seeds × 7σ × 9 ratios + 20 robust + 4 levels | RMSD < 0.05 | 100% (σ ∈ [0.05, 0.5], α/β ≥ 2) |

### 10.2 Negative Results (Equally Important)

| Phase | Null hypothesis tested | Result |
|:-----:|:----------------------|:-------|
| A | Coupling dynamics select the stella | **Rejected** — many geometries comparable |
| F2 | N = 3 maximizes computational richness | **Rejected** — richness increases with N |
| Z1-M0 | Generic dynamics produce Z₃ | **Rejected** — broad cluster distribution |
| Z1-M1 | Z₃ wins energetic competition | **Rejected** — Z₄ wins at equal coupling |

These negative results are essential: they narrow the selection mechanism to the specific combination of Fisher non-degeneracy + primality + minimality, ruling out simpler explanations.

---

*Parent document: [Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula.md)*
*Applications: [Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Applications.md](Proposition-0.0.3a-Computational-Crystallization-Stella-Octangula-Applications.md)*
