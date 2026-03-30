# Proposition 0.0.XXg: Q₃ Spectral Structure on the Stella Octangula

## Status: 🔶 NOVEL 🔸 PARTIAL — Q₃ SPECTRAL STRUCTURE FROM GEOMETRY

**Created:** 2026-03-26
**Corrected:** 2026-03-27 (multi-agent review: Q₃ spectrum attribution, distance fixes, control geometries)
**Updated:** 2026-03-28 (Open Q3 resolved — higher Q_n excluded by dimension, geometry, algebra, physics, and lattice arguments)
**Purpose:** Establish that the stella octangula's cross-nearest adjacency graph is isomorphic to the Q₃ hypercube, whose Laplacian spectrum has eigenvalue ratios {1, 1, 1, 2, 2, 2, 3}. The integers {2, 3} coincide with the stella's construction numbers but arise from graph spectral theory, not from a "prime encoding" mechanism.

**Dependencies:**
- ✅ Theorem 0.0.3 (Stella Uniqueness)
- ✅ Proposition 0.0.3a (Computational Crystallization — Z₃ → stella)
- ✅ Proposition 0.0.XXa (First Stable Principle — Fisher non-degeneracy at N = 3)
- ✅ Proposition 0.0.17b (Fisher Metric Uniqueness via Chentsov)
- ✅ Lemma 0.0.17c (Fisher-Killing Equivalence)
- ✅ Definition 0.1.1 (Stella Octangula Boundary Topology)
- ✅ Definition 0.1.2 (Three Color Fields, Relative Phases)

**Computational Verification:**
- `stella_genesis/RESEARCH-Prime-Interference.md` (H1–H7, H3b, H6b, §21.6)
- Phase executables: `phase_h1.c` through `phase_h7.c`, `phase_h3b.c`, `phase_h6b_neff3.c` in `stella_genesis/`
- `stella_genesis/phase_Q3_analytic.py` — Exact eigenvalue formula for full stella Laplacian, physical regime analysis, confinement connection (§2.6)
- `stella_genesis/phase_Q7_higher_Qn_spectra.py` — Higher Q_n exclusion: dimensional constraint, compound polyhedra survey, SU(N) generalization, FCC graph, physical mismatch (Open Q3 resolution)

**Peer Review:**
- [Multi-Agent Verification Report (2026-03-27)](../../verification-records/Proposition-0.0.XXg-Multi-Agent-Verification-2026-03-27.md) — Literature, Mathematical, Physics agents (adversarial)
- [Adversarial Computational Verification](../../../verification/adversarial_prop_XXg_spectral_prime.c) — C code testing Q₃ spectrum hypothesis, distance claims, σ limits, Z_N independence, Fisher formula consistency, control geometry
- [Adversarial Plots](../../../verification/adversarial_prop_XXg_plots.py) — Visualization of adversarial test results
- [Correction Verification Script](../../../verification/verify_prop_XXg_corrections.py) — Python verification of all corrections (Q₃ spectrum, distances, T_d symmetry, Z_N independence, surface amplification with controls)
- [Definitive Information Amplification Resolution](../../../verification/definitive_info_amplification.py) — Variable-isolation test: identical ∂P/∂θ_k formula across all geometries, 5 test batteries, quadrature convergence sweep

**References:**
- H. L. Montgomery, "The pair correlation of zeros of the zeta function," Proc. Sympos. Pure Math. 24, 181–193 (1973)
- M. V. Berry and J. P. Keating, "H = xp and the Riemann zeros," in *Supersymmetry and Trace Formulae* (1999)
- O. Roy and M. Vetterli, "The effective rank: A measure of effective dimensionality," EUSIPCO 2007 — defines the entropy-based effective rank used in H2, H5, §21.6
- A. M. Odlyzko, "On the distribution of spacings between zeros of the zeta function," Math. Comp. 48, 273–308 (1987) — numerical verification of Montgomery's conjecture
- N. N. Chentsov, *Statistical Decision Rules and Optimal Inference* (1982) — Fisher metric uniqueness (via Prop 0.0.17b)
- A. Athenodorou and M. Teper, "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions," JHEP **11** (2020) 172 — continuum-limit glueball masses: m(0⁺⁺)/√σ = 3.405 ± 0.021, m(2⁺⁺)/√σ = 4.73 ± 0.07

**Structure:** This proposition uses the 3-file structure due to length:
- **Statement** (this file): Formal claims and proof sketch
- **[Derivation](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Derivation.md)**: Full experimental evidence (H1–H7, H3b, H6b, §21.6)
- **[Applications](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md)**: Physical interpretation, cross-references, and implications

---

## 1. Statement

**Proposition 0.0.XXg (Q₃ Spectral Structure on the Stella Octangula):**

*The stella octangula ∂S = ∂T₊ ⊔ ∂T₋ has eigenvalue ratios {1, 1, 1, 2, 2, 2, 3} arising from its Q₃ hypercube graph structure:*

**(a) {2, 3} eigenvalue ratios from Q₃ graph Laplacian.** *The 8 vertices of ∂S, connected by cross-nearest edges (distance 2/√3), form the 3-dimensional hypercube graph Q₃. The Laplacian of Q_n has eigenvalues 2k with multiplicity C(n,k) for k = 0, ..., n. For Q₃: {0, 2, 2, 2, 4, 4, 4, 6}, giving nonzero ratios {1, 1, 1, 2, 2, 2, 3}. This is a standard result of algebraic graph theory. The integers {2, 3} coincide with the stella's construction numbers — 2 tetrahedra and Z₃ symmetry order — but this is a small-number coincidence, not a "prime encoding." The same ratios appear with any Z_N weighting (or none), confirming the pattern depends only on the Q₃ graph structure. In the Gaussian-weighted coupling matrix, the Q₃ ratios emerge at small σ (strong confinement) where only cross-nearest couplings are significant; at large σ (delocalized), all couplings equalize and ratios approach 1. The 3-fold degeneracy of the ratio-1 and ratio-2 eigenspaces reflects the T₂ irreducible representation of the T_d symmetry group of the tetrahedron, corresponding to the three coordinate axes of the embedding cube.*

**(b) Information amplification on ∂S — FALSIFIED.** *The original §21.6 analysis reported that prime frequencies have higher effective-rank slope than integer frequencies on the stella surface, inverting the 1D ordering. A definitive resolution test (`verification/definitive_info_amplification.py`) using identical ∂P/∂θ_k formulas across all geometries and variable-isolation methodology identified three root causes of the original discrepancy: (1) the 1D reference used ∂P/∂ω_k (frequency-Fisher with `2*x` factor) while 3D models used ∂P/∂θ_k (phase-Fisher) — an apples-to-oranges comparison; (2) the C code used log-mapped frequencies while the Python retest used raw frequencies; (3) the C code used structured Dunavant quadrature while the Python retest used random barycentric sampling. Variable isolation shows the decisive factor is the frequency mapping: with `log(prime)` frequencies, primes > integers on ALL geometries (stella, two-spheres, random-8v) — not stella-specific; with raw frequencies, integers > primes on ALL geometries. No parameter combination produces stella-specific amplification. This claim is falsified.*

**(c) Logarithmic rank compression (universal).** *Both prime-phase Fisher matrices (H2) and zeta-zero Fisher matrices (H5) exhibit logarithmic effective-rank growth: erank ≈ c₁·ln(K) + c₂, with slopes differing by only 13% (4.87 vs 5.52). This is a universal property of oscillatory interference with decaying amplitudes, not specific to the stella or to primes. The effective rank is computed using the Roy-Vetterli entropy-based definition: erank = exp(−Σ pᵢ ln pᵢ) where pᵢ = λᵢ/Σλⱼ (Roy & Vetterli, EUSIPCO 2007).*

**(d) Spectral decomposition of irreducibility index.** *The irreducibility index I(N) from Prop 0.0.3a Phase F3 carries zeta-zero spectral signature: with weight normalization I(N)·N^{0.79}, alignment with the first 20 zeta zeros reaches 20/20 (H3b). However, this is automatic for any prime-detecting function — it reflects the explicit formula, not a framework-specific property.*

**(e) GUE universality does not hold.** *Fisher eigenvalue spacings of Z_N interference are super-Poisson (variance 2.0–2.7) at all tested N (10–200), not GUE (variance 0.178). The structural parallel between Z_N interference and the Riemann explicit formula does not extend to eigenvalue statistics.*

**(f) Discrete xp operator does not converge.** *Discretizing the Berry-Keating Hamiltonian H = xp on a Z_N lattice produces approximately equally-spaced eigenvalues (not logarithmically spaced), with ratios wrong by 3–8× and no convergence as N → ∞.*

### 1.1 Classification of Results

| Result | Type | Framework-specific? | Significance |
|:-------|:-----|:-------------------:|:-------------|
| {2, 3} eigenvalue ratios (a) | **Positive** | **Partially** — Q₃ graph structure, but Q₃ ≅ stella | Q₃ Laplacian spectrum coincides with construction numbers |
| Information amplification (b) | **Negative** | No — frequency-mapping artifact | Definitively falsified: not stella-specific |
| Logarithmic compression (c) | Positive | No — universal property | Structural parallel, not a bridge |
| Spectral decomposition (d) | Positive | No — automatic for prime detectors | Confirms I(N) detects primes |
| GUE universality (e) | **Negative** | — | Definitively falsified |
| Discrete xp (f) | **Negative** | — | Definitively falsified |

The framework-specific content is the Q₃ ≅ stella isomorphism and its spectral consequences. The information amplification claim is falsified (see §2.2). The remaining results provide context and honest assessment of failed bridges.

### 1.2 The Core Insight

The stella octangula has two fundamental construction numbers:
- **2** = the number of interpenetrating tetrahedra (T₊ and T₋)
- **3** = the order of the Z₃ symmetry group (the center of SU(3))

Both 2 and 3 are primes. The eigenvalue ratios of the stella's cross-nearest graph Laplacian are {1, 1, 1, 2, 2, 2, 3} — the Q₃ hypercube spectrum. The integers {2, 3} coincide with the construction numbers, but this is better understood as a consequence of graph spectral theory on Q₃ = C₂³ than as a "prime encoding."

**Why the coincidence is not deep:** The Q_n hypercube Laplacian always produces ratios {1, 2, ..., n}. For Q₃, these are {1, 2, 3}. For Q₄, they would be {1, 2, 3, 4} — where 4 is composite. The appearance of primes at n = 3 is a consequence of n being small enough that all integers up to n are prime or 1, not a geometric selection mechanism for primes.

**What IS framework-specific:** The stella ≅ Q₃ isomorphism itself. The stella is the unique geometry selected by Z₃ crystallization (Prop 0.0.3a), and its cross-nearest adjacency structure happens to be Q₃. This means the Q₃ Laplacian spectrum is a consequence of the framework's geometric axioms, even though the specific ratios {2, 3} are a standard graph-theoretic result rather than a novel prime-generating mechanism.

---

## 2. Proof Sketch

### 2.1 {2, 3} Eigenvalue Ratios (Claim a)

**Setup:** The 8 vertices of ∂S = ∂T₊ ⊔ ∂T₋, connected by cross-nearest edges, with optional Gaussian-weighted couplings controlled by confinement parameter σ.

**Graph-theoretic mechanism:** The stella's cross-nearest adjacency graph is isomorphic to Q₃, the 3-dimensional hypercube graph. The three distinct distances on the unit stella (circumradius 1) are:
- Cross-nearest: 2/√3 ≈ 1.155 (T₊ vertex to 3 nearest T₋ vertices) — 12 pairs
- Intra-tetrahedron: √(8/3) ≈ 1.633 (edges within each tetrahedron) — 12 pairs
- Cross-antipodal: 2.0 (T₊ vertex to its diametrically opposite T₋ vertex) — 4 pairs

In the strong-confinement regime (small σ), the Gaussian weighting exp(−d²/(2σ²)) exponentially suppresses longer-distance couplings. Only the 12 cross-nearest pairs survive, and the coupling matrix approaches the Q₃ graph Laplacian.

**Proof of Q₃ ≅ stella cross-nearest graph.** The 8 vertices of the stella inscribed in the unit cube at (±1/√3, ±1/√3, ±1/√3) are in bijection with binary strings **b** = (b₁, b₂, b₃) ∈ {0,1}³ via the map bᵢ = 0 ↔ +1/√3, bᵢ = 1 ↔ −1/√3 (Definition 0.1.1 §2.2):

| Binary **b** | Coordinates (×1/√3) | Tetrahedron | Hamming weight |
|:------------:|:-------------------:|:-----------:|:--------------:|
| 000 | (+1, +1, +1) | T₊ | 0 (even) |
| 011 | (+1, −1, −1) | T₊ | 2 (even) |
| 101 | (−1, +1, −1) | T₊ | 2 (even) |
| 110 | (−1, −1, +1) | T₊ | 2 (even) |
| 001 | (+1, +1, −1) | T₋ | 1 (odd) |
| 010 | (+1, −1, +1) | T₋ | 1 (odd) |
| 100 | (−1, +1, +1) | T₋ | 1 (odd) |
| 111 | (−1, −1, −1) | T₋ | 3 (odd) |

T₊ consists of even-parity strings, T₋ of odd-parity strings. Two vertices **b** and **b′** differ in exactly one bit (Hamming distance 1) if and only if their Euclidean distance is |**b** − **b′**| = 2/√3 (one coordinate flips sign, contributing (2/√3)² = 4/3, so d = 2/√3). This is precisely the cross-nearest distance. Since Q₃ is defined as the graph on {0,1}³ with edges at Hamming distance 1, and a single bit flip always changes parity, every Q₃ edge connects a T₊ vertex to a T₋ vertex. The Q₃ graph has 8 vertices and 12 edges (each vertex has degree 3), matching exactly the 12 cross-nearest pairs. ∎

**Q₃ Laplacian spectrum:** The hypercube Q_n has Laplacian eigenvalues λ_k = 2k with multiplicity C(n,k) for k = 0, ..., n. For Q₃:

| k | Eigenvalue 2k | Multiplicity C(3,k) |
|:-:|:------------:|:-------------------:|
| 0 | 0 | 1 |
| 1 | 2 | 3 |
| 2 | 4 | 3 |
| 3 | 6 | 1 |

Nonzero ratios: {1, 1, 1, 2, 2, 2, 3}. The 3-fold degeneracy of the λ = 2 and λ = 4 eigenspaces reflects the T₂ irreducible representation of the tetrahedral symmetry group T_d, corresponding to the three coordinate axes of the embedding cube.

**Z_N independence:** Adversarial testing confirms the {1, 1, 1, 2, 2, 2, 3} pattern appears with no Z_N weighting, and with Z₅, Z₇ weighting — identical ratios in all cases. With Z₃ weighting (cos(2π/3) = −0.5), cross-tetrahedron couplings become negative, producing all-negative eigenvalues — the Z₃ factor does not create the pattern but rather destroys it. The ratios depend solely on the Q₃ graph structure.

**σ regime:** At small σ (≲ 0.3, without Z_N), the max/min nonzero eigenvalue ratio approaches 3.0 (exact Q₃ limit). At large σ (≫ 1), all distances become equally weighted, approaching the complete graph K₈ where all eigenvalues are equal. The Q₃ pattern holds in a finite window σ ∈ [0.2, 0.5], not as a "convergence" to a limit.

**Why {2, 3} are not "encoded primes":** The Q₄ hypercube would produce ratios {1, 2, 3, 4}, where 4 is composite. The appearance of only primes at n = 3 is a small-number coincidence. The correct statement: the stella's Q₃ structure produces eigenvalue ratios equal to its construction numbers, which happen to be prime because the framework selects Z₃ (the smallest Fisher-stable group) whose order and number of nontrivial elements are both prime.

### 2.2 Information Amplification (Claim b) — FALSIFIED

**Original claim:** Fisher information matrices computed for different frequency sets (prime frequencies, equal-spaced, random, integer) on three domains: 1D line, stella graph (8 vertices), and stella surface (8 triangular faces). The original §21.6 analysis reported that prime frequencies had higher effective-rank slope than integers on the stella surface, inverting the 1D ordering.

**Definitive resolution** (`verification/definitive_info_amplification.py`): A systematic investigation identified three independent inconsistencies between the original C code (`phase_h_3d_fisher.c`) and the Python adversarial retest (`verify_prop_XXg_corrections.py`):

| Parameter | C code (original) | Python retest |
|:----------|:-------------------|:--------------|
| Fisher formula (1D) | ∂P/∂ω_k (with `2*x` factor) | ∂P/∂θ_k (no `2*x`) |
| Fisher formula (3D) | ∂P/∂θ_k | ∂P/∂θ_k |
| Frequencies | `log(prime[k])` | `prime[k]` (raw) |
| Amplitudes | `1/√prime[k]` | `exp(-0.01·f)` |
| Z₃ offsets | Yes (2π/3 for T₋) | No |
| Phase offsets | None | `2πk/K` |

The 1D formula difference means the original comparison was between *frequency sensitivity* (1D) and *phase sensitivity* (3D) — fundamentally different quantities.

**Variable-isolation test (Battery 5):** Changing one parameter at a time from the C-code baseline on the stella surface (Dunavant quadrature, Z₃ offsets):

| Configuration | Result |
|:-------------|:-------|
| C convention (log freqs, 1/√p amps) | **P > I** (slope 1.11 vs 0.52) |
| Same, no Z₃ offsets | **P > I** (unchanged — Z₃ irrelevant) |
| Same, + phase offsets 2πk/K | **P > I** (unchanged — offsets irrelevant) |
| Raw frequencies (python convention) | **I > P** (slope 5.36 vs 6.25 — ordering flips) |

**The frequency mapping is the sole decisive variable.** With `log(prime)` frequencies, primes have wider spacing than `log(integer)` at large K, producing higher effective rank. This is a mathematical property of logarithmic mapping, not a geometric property of the stella.

**Control geometry test (Battery 1):** With C-code convention (log freqs), primes > integers on ALL geometries:

| Geometry | Prime slope | Integer slope | Winner |
|:---------|:----------:|:------------:|:-------|
| 1D reference | 5.08 | 9.73 | I > P |
| **Stella surface** | **1.11** | **0.52** | **P > I** |
| Two-spheres control | 1.82 | 0.97 | P > I |
| Random-8v control | 0.44 | 0.27 | P > I |

All 3D geometries show the same ordering. The stella is not special.

**Quadrature convergence (Battery 4):** The P > I ordering with log frequencies is stable from 80 to 720 Dunavant quadrature points and from 80 to 640 random barycentric points. The result is not a quadrature artifact.

**Verdict:** Claim (b) is falsified in both possible forms:
1. With log frequencies: primes > integers, but on **all** geometries — not stella-specific
2. With raw frequencies: integers > primes on **all** geometries — no amplification

The original "inversion" was an artifact of comparing frequency-Fisher (1D, with `2*x`) against phase-Fisher (3D, without `2*x`), compounded by log-frequency mapping that inherently favors prime spacing.

### 2.3 Logarithmic Rank Compression (Claim c)

**Setup:** Fisher information matrices for K-component interference, computed for both prime phases (H2: phases at prime positions) and zeta-zero phases (H5: phases from Riemann zeros).

**Result:**
- H2 (primes): eff_rank ≈ 4.87·ln(K) − 4.54
- H5 (zeta zeros): eff_rank ≈ 5.52·ln(K) − 4.19
- Slopes differ by 13%

**Interpretation:** Both systems exhibit the same logarithmic compression, but §21.6 shows this is a **generic property of 1D multi-frequency interference**, not framework-specific. Any set of well-separated frequencies on a 1D domain will show logarithmic rank growth. The specific similarity between primes and zeta zeros reflects the prime number theorem (primes have logarithmic spacing), not a deep information-geometric bridge.

**Honesty note:** The H2/H5 similarity was initially thought to be a significant bridge between the stella and the Riemann zeros. Analysis showed it is a 1D artifact — a generic property of multi-frequency interference. The originally claimed "inversion" on ∂S (primes becoming most information-rich) is not reproduced in adversarial retesting with control geometries (see claim b).

### 2.4 Spectral Decomposition (Claim d)

**Setup:** The irreducibility index I(N) from Prop 0.0.3a Phase F3 has power-law decay I(p) ≈ 1.22·p^{−1.29}. Its Dirichlet series is tested for peaks at zeta-zero frequencies.

**Initial result (H3):** Raw I(N) aligns with 9/20 zeta zeros — barely above random.

**H3b resolution:** The poor alignment was caused by steep amplitude decay masking the spectral peaks. With weight normalization to flatten the decay:
- I(N)·N^{0.79}: 18/20 alignment (N_max = 500), 20/20 (N_max = 2000)
- I(N)·N^{1.29}: 20/20 alignment
- I(N)·log(N)·N^{0.5}: 20/20 alignment

**Control:** The von Mangoldt function Λ(N) (the textbook prime detector) achieves 19/20 alignment.

**Interpretation:** Any function that detects primes will, via the explicit formula ψ(x) = x − Σ_ρ x^ρ/ρ − ..., have spectral peaks at zeta-zero frequencies. The irreducibility index detects primes (by construction in Phase F3), so it automatically carries zeta-zero signature. This is a consistency check, not a discovery.

### 2.5 Negative Results (Claims e, f)

**H1 (GUE):** Fisher eigenvalue spacings are super-Poisson (variance 2.0–2.7) across N = 10 to 200, with no trend toward GUE (variance 0.178). The physical reason: overlapping Gaussian bumps at σ = π/√N create eigenvalue clusters rather than the level repulsion characteristic of GUE. This bridge is definitively closed.

**H4 (discrete xp):** The DFT-based discretization of H = xp produces eigenvalues with wrong ratios (3–8× off), wrong spacing pattern (linear vs logarithmic), and no convergence with N. This is consistent with the known literature: Berry-Keating requires specific boundary conditions that the naive discretization cannot capture.

### 2.6 Physical Consequences of Q₃ Spectrum (Open Question 2)

**Setup:** The full stella Laplacian combines intra-tetrahedron coupling (K₄ ⊕ K₄, 6+6 edges within each tetrahedron) with cross-tetrahedron coupling (Q₃, 12 cross-nearest edges), parameterized by relative strength α:

$$L_{\text{full}} = L_{K_4 \oplus K_4} + \alpha \cdot L_{Q_3}$$

**Analytic eigenvalue formula (verified numerically):** The Q₃ Fourier modes ψ_S(b) = (−1)^{Σ_{i∈S} bᵢ} for S ⊆ {1,2,3} are simultaneous eigenvectors of both L_{K₄⊕K₄} and L_{Q₃}. The combined eigenvalues are:

| Subset S | |S| | L_{K₄} eigenvalue | L_{Q₃} eigenvalue | Combined λ(α) | Irrep | Mult |
|:--------:|:---:|:-----------------:|:-----------------:|:--------------:|:-----:|:----:|
| ∅ | 0 | 0 | 0 | **0** | A₁ | 1 |
| {i} | 1 | 4 | 2 | **4 + 2α** | T₂ | 3 |
| {i,j} | 2 | 4 | 4 | **4 + 4α** | T₂ | 3 |
| {1,2,3} | 3 | 0 | 6 | **6α** | A₂ | 1 |

The K₄ eigenvalue is 0 when |S| ∈ {0, 3} (mode uniform within each parity class) and 4 when |S| ∈ {1, 2} (mode non-uniform). This is because the staggered mode ψ_{123} = (−1)^{b₁+b₂+b₃} is constant (+1 or −1) on each parity class.

**Level crossings:**
- α = 1: A₂ (6α = 6) merges with T₂_low (4+2 = 6) — accidental 4-fold degeneracy
- α = 2: A₂ (6α = 12) merges with T₂_high (4+8 = 12) — accidental 4-fold degeneracy

**Three physical regimes:**
- α < 1: staggered mode A₂ is the *cheapest* excitation (eigenvalue 6α < 4+2α)
- 1 < α < 2: mixed ordering (T₂_low < A₂ < T₂_high)
- **α > 2: Q₃-dominated** — ordering is T₂_low < T₂_high < A₂, with ratios approaching {1 : 2 : 3}

**Physical regime determination:** Gaussian weighting exp(−d²/(2σ²)) gives:

$$\alpha_{\text{eff}} = \frac{w_{\text{cross}}}{w_{\text{intra}}} = \exp\!\left(\frac{d_{\text{intra}}^2 - d_{\text{cross}}^2}{2\sigma^2}\right)$$

where d_cross = 2/√3 ≈ 1.155 and d_intra = √(8/3) ≈ 1.633. For σ < 0.54, α_eff > 10 and the Q₃ ratios hold to within 5%. For σ < 0.38, α_eff > 100 and ratios hold to <1%.

**Physical consequences:**

**(i) Three-fold degeneracy of lowest excitations.** The three T₂_low modes are exactly degenerate by O_h symmetry of the stella. They represent independent excitations along each cube axis — physically, the three color directions. Breaking this degeneracy requires breaking the octahedral symmetry (e.g., by an external field or boundary effects in the FCC lattice).

**(ii) Additive energy structure (Q₃ = C₂³).** At large α, excitation energies are additive: E(k axes) = k · 2α. This is because Q₃ = C₂ × C₂ × C₂ — a product of three independent two-vertex graphs. Each cube axis contributes independently to the energy. The complete T₊ ↔ T₋ flip (A₂ mode, all 3 axes) costs exactly 3× a single-axis excitation. There is no "binding energy" between color directions at the graph level.

**(iii) Cross-tetrahedron propagator.** At α = 0 (K₄ only), there is zero propagation between T₊ and T₋: G(T₊, T₋) = 0. At finite α, the Q₃ coupling creates new propagation channels:

$$G_{\text{cross}}(m^2) = \frac{1}{4m^2} - \frac{1}{4(6\alpha + m^2)}$$

The A₂ mode gap 6α sets the scale at which T₊ and T₋ decouple. At large α (strong confinement), G_cross → 1/(4m²), approaching complete mixing.

**(iv) Suggestive glueball mass ratio.** If lattice mass² is proportional to the Q₃ eigenvalues, the mass ratios are m₁ : m₂ : m₃ = 1 : √2 : √3 ≈ 1 : 1.414 : 1.732. The ratio √2 ≈ 1.414 is within 1.8% of the lattice QCD glueball ratio m(2⁺⁺)/m(0⁺⁺) = (4.73 ± 0.07)/(3.405 ± 0.021) ≈ 1.389 (Athenodorou & Teper, JHEP 11 (2020) 172; masses in units of √σ). However, the Q₃ modes classify by spatial symmetry (T₂, A₂), while glueballs classify by J^{PC}. A rigorous connection would require projecting the Q₃ ⊗ SU(3)_rep tensor product onto definite J^{PC} quantum numbers — this is developed in Prop 7.8.6 (Full Two-Gluon Glueball Spectrum). This comparison is suggestive, not conclusive.

**(v) Single-stella tensor product (isolated stella only).** On an *isolated* stella, the excitation spectrum factorizes as E(R, S) = E_rep(R) + E_mode(S), where R labels SU(3) representations (Prop 0.0.38a) and S labels Q₃ modes. This yields 8 excitation channels per SU(3) irrep on a single stella. However, this factorization does NOT extend to the FCC lattice — see (vi).

**(vi) Q₃ modes do NOT form bands in the FCC lattice — CORRECTED.** ~~The original claim that "the 8 internal modes become 8 bands" is incorrect.~~ Investigation (`stella_genesis/phase_Q3_band_investigation.py`) identified three reasons:

1. **Stellae share vertices extensively.** In the FCC honeycomb, each stella involves 13 FCC sites (1 center + 12 nearest neighbors). Neighboring stellae share ~6 of these 13 sites (46% overlap). The stellae are not spatially disjoint unit cells, so the tight-binding (weakly coupled) picture does not apply.

2. **FCC dispersion is continuous.** The FCC graph Laplacian produces a continuous band λ(k) = 12 − 4(cos k_x cos k_y + cos k_y cos k_z + cos k_z cos k_x), determined by the 12-fold coordination — not 4 discrete bands from Q₃. The Q₃ internal structure is dissolved into the FCC lattice geometry.

3. **Gauge spectrum is representation-diagonal.** The physical excitation spectrum on the FCC lattice is the representation spectrum E_R = −2 ln d_R − 4 ln u_R (Prop 0.0.38a, 2.5.2c), which is diagonal in the representation basis with no momentum dependence at the exact level. The tensor product with Q₃ modes does not apply.

**What Q₃ modes do govern:** (a) internal dynamics of an isolated stella (color field normal modes), (b) the G1+G2 computational model where stellae are treated as separate objects with inter-stella coupling, (c) symmetry constraints — the Q₃ = C₂³ factorization reflects O_h symmetry at each FCC vertex, which constrains FCC Bloch waves.

**Verification:** `stella_genesis/phase_Q3_analytic.py` — analytic formula verified against numerical diagonalization at 10 values of α (all match to machine precision). Physical regime analysis confirms Q₃ ratios {1:2:3} hold for σ ≲ 0.5 on an isolated stella. `stella_genesis/phase_Q3_band_investigation.py` — FCC overlap analysis and shared-vertex spectrum show band picture does not hold.

### 2.7 Z₃-Weighted Spectrum (Resolved Open Question 5)

**Setup:** The Z₃ charge scheme assigns charge 1 to all T₊ vertices and charge 2 to all T₋ vertices. The Z₃ weighting factor is cos(2π(q_i − q_j)/3), which gives +1 for intra-tetrahedron pairs (dq = 0) and −0.5 for cross-tetrahedron pairs (dq = ±1). The Z₃-weighted stella Laplacian is therefore:

$$L_{Z_3} = L_{K_4 \oplus K_4} + (-0.5) \cdot L_{Q_3} = L_{\text{full}}(\alpha = -\tfrac{1}{2})$$

This is the *same* parametric family analyzed in §2.6, evaluated at negative coupling α = −1/2.

**Analytic spectrum (verified numerically to machine precision):**

| Subset S | |S| | L_{K₄} eigenvalue | L_{Q₃} eigenvalue | Combined λ(α=−½) | Irrep | Mult |
|:--------:|:---:|:-----------------:|:-----------------:|:-----------------:|:-----:|:----:|
| ∅ | 0 | 0 | 0 | **0** | A₁ | 1 |
| {i,j} | 2 | 4 | 4 | **+2** | T₂ | 3 |
| {i} | 1 | 4 | 2 | **+3** | T₂ | 3 |
| {1,2,3} | 3 | 0 | 6 | **−3** | A₂ | 1 |

The spectrum is **{−3, 0, +2, +2, +2, +3, +3, +3}**: one negative eigenvalue, one zero mode, and six positive eigenvalues. The matrix is not positive semidefinite.

**Key observations:**

**(vii) Negative A₂ eigenvalue — center-symmetric instability.** The staggered mode (T₊ = +1, T₋ = −1) has λ = −3. In a Laplacian interpretation where eigenvalues are mode energies, the Z₃ weighting makes T₊↔T₋ antiphase alignment energetically *favorable*. This is the hallmark of the confined phase: the Polyakov loop is driven toward the center-symmetric value Tr(P) = 0. The negative eigenvalue is the discrete, single-stella analog of the Z₃ center-symmetry mechanism that drives confinement in SU(3) lattice gauge theory.

**(viii) Spectral inversion.** At α > 0 (unweighted), A₂ is the *highest* mode (most costly excitation). At α = −0.5 (Z₃), A₂ is the *lowest* mode (negative energy). The Z₃ center symmetry inverts the role of the staggered mode — the same physics that makes confinement and deconfinement complementary phases.

**(ix) T₂ level swap.** At α > 0: single-axis modes (|S|=1) are cheaper than double-axis (|S|=2). At α = −0.5: double-axis modes (λ = 2) are cheaper than single-axis (λ = 3). The −0.5 factor reduces the Q₃ contribution, and since double-axis modes have larger Q₃ eigenvalues, they receive a larger penalty reduction.

**(x) Tachyonic pole in cross-tetrahedron propagator.** The propagator G_cross(m²) = ⟨(L + m²I)⁻¹⟩_{T₊×T₋} has a pole at m² = 3 (where λ_A₂ + m² = 0). For m² < 3 the system is unstable; for m² > 3 the propagator is well-defined but sign-flipped relative to the unweighted case. The scale m² = 3 is the Z₃ center-symmetry scale — below it, the T₊↔T₋ staggered configuration is energetically preferred.

**(xi) Eigenvectors preserved.** Despite the negative eigenvalue, the eigenvectors remain the Q₃ Fourier modes ψ_S(b) = (−1)^{Σ_{i∈S} bᵢ}. This is because O_h symmetry is preserved — the Z₃ weighting treats all cross-tetrahedron edges identically. The mode classification (A₁, T₂, T₂, A₂) is unchanged; only the eigenvalue ordering changes.

**(xii) Gaussian-weighted Z₃ spectrum.** With Gaussian weighting exp(−d²/(2σ²)) × z₃_factor, the number of negative eigenvalues depends on σ. At large σ (α_eff → 1, moderate cross-coupling): only 1 negative eigenvalue (the A₂ mode). At small σ (α_eff >> 1, strong cross-coupling): up to 7 negative eigenvalues, because the negative cross-couplings dominate the positive intra-couplings. The transition from 1 to 7 negative eigenvalues occurs around σ ≈ 0.8.

**Connection to L-series phases:** Phase L3 (center dominance) verified first-order Z₃ deconfinement on the FCC lattice. Phase L4 (SU(3) center projection) showed center dominance σ_{Z₃}/σ_{SU(3)} ≈ 0.85–0.95. The present result demonstrates the same Z₃ center physics at the single-stella level.

**Verification:** `stella_genesis/phase_Q5b_z3_weighted_spectrum/run.py` — analytic spectrum verified against numerical diagonalization to machine precision (max error 1.8×10⁻¹⁵). Eigenvectors confirmed to lie in correct Q₃ Fourier subspaces via subspace projection (all norms = 1.000000). Gaussian-weighted Z₃ spectrum computed at 14 values of σ. Sign conventions verified consistent with adversarial C code.

---

## 3. Convergence Summary

| Claim | Experiment | Key metric | Result |
|:------|:-----------|:-----------|:-------|
| Q₃ ratios {1,2,3} | H6 + adversarial | Eigenvalue ratios (no Z_N, σ ≲ 0.3) | {1,1,1,2,2,2,3} ✓ (Q₃ Laplacian) |
| **Q₃ physical spectrum** | **Phase Q3** | **Full stella eigenvalues, analytic formula** | **{0, 6α, (4+2α)×3, (4+4α)×3} ✓** |
| Info amplification | §21.6 + adversarial + definitive | Slope on ∂S: primes vs integers | **Falsified** — frequency-mapping artifact ✗ |
| Log compression | H2, H5 | Slope similarity | 4.87 vs 5.52 (13% diff) |
| Spectral decomp | H3b | Zeta-zero alignment | 20/20 with weights |
| GUE | H1 | Spacing variance | 2.0–2.7 (not 0.178) ✗ |
| Discrete xp | H4 | Ratio error | 3–8× ✗ |
| **Z₃-weighted spectrum** | **Phase Q5b** | **Eigenvalues at α = −0.5** | **{−3, 0, +2×3, +3×3} ✓ — center-symmetric instability** |

---

## 4. Consistency Checks

### 4.1 {2, 3} Ratios Are Q₃ Graph-Theoretic, Not "Prime Encoding"

The eigenvalue ratios {1, 2, 3} arise from the Q₃ hypercube Laplacian:
- The stella's cross-nearest adjacency graph is Q₃ (3-regular bipartite graph on 8 vertices)
- Q_n has Laplacian eigenvalues 2k with multiplicity C(n,k) for k = 0, ..., n
- For Q₃: nonzero eigenvalue ratios are {1, 2, 3}
- This is Z_N-independent — confirmed by adversarial testing with no Z_N, Z₂, Z₅, Z₇

The framework-specific content is: **why Q₃?** The stella is selected by Z₃ crystallization (Prop 0.0.3a), and the stella's cross-nearest graph is Q₃. Changing the geometry (e.g., two octahedra, which would have different graph structure) would change the ratios.

### 4.2 Information Amplification — FALSIFIED

The original §21.6 claim that primes are "most information-rich" on ∂S is definitively falsified. The definitive resolution test (`verification/definitive_info_amplification.py`) showed:

1. **The apparent P > I ordering on ∂S** in the original C code was driven entirely by using `log(prime)` frequencies — a mapping that inherently gives primes wider spacing than integers at large K. The same P > I ordering appears on all control geometries (two-spheres, random-8v) with log frequencies.
2. **With raw frequencies**, integers > primes on all geometries including ∂S.
3. **The 1D "reference"** used a different Fisher quantity (∂P/∂ω, frequency sensitivity) than the 3D models (∂P/∂θ, phase sensitivity), making the original 1D-vs-3D comparison meaningless.

On the stella graph alone (8 vertices), rank saturates at ~4 regardless of frequency count. On the stella surface, effective rank grows logarithmically, but no differently from control geometries.

### 4.3 Cross-Check: {2, 3} in Computation

Prop 0.0.XXf (Computational Classification, RESEARCH-Stella-Computation.md §5.4) independently found {2, 3} in the computational primitives:
- 2 heads (CPY01: T₊ → T₋) = the "2"
- Z₃ gate (OPEN/CLOSE: exit on trit 0) = the "3"

The same construction numbers appear in Q₃ spectrum, computation, and crystallization. However, all three manifestations trace back to the same root cause: the stella is built from 2 tetrahedra with Z₃ symmetry. The "convergence" of {2, 3} from different analyses reflects a shared origin, not independent evidence.

### 4.4 Falsifiability

Claim (a) is not falsifiable in the traditional sense — it is a theorem of algebraic graph theory (Q₃ Laplacian spectrum). What is falsifiable is the claim that the stella's cross-nearest graph is Q₃, which is verified computationally.

Claim (b) has been **definitively falsified**: the definitive resolution test (`verification/definitive_info_amplification.py`) identified the root cause as a frequency-mapping artifact (`log(prime)` vs raw frequencies) compounded by an inconsistent Fisher formula (∂P/∂ω in 1D vs ∂P/∂θ in 3D). No parameter combination produces stella-specific amplification.

---

## 5. Open Questions

1. ~~**Information amplification resolution.**~~ **RESOLVED (2026-03-27).** The definitive resolution test identified three root causes: (i) 1D used ∂P/∂ω_k while 3D used ∂P/∂θ_k, (ii) C code used log-mapped frequencies while Python used raw frequencies, (iii) the decisive variable is the frequency mapping — `log(prime)` spacing inherently favors primes over integers. No stella-specific amplification exists. See `verification/definitive_info_amplification.py`.

2. ~~**Q₃ spectrum in the full framework.**~~ **RESOLVED (2026-03-27).** The Q₃ spectrum has physical consequences for the *isolated stella* but does NOT produce band structure in the FCC lattice. The full stella Laplacian L = L_{K₄⊕K₄} + α·L_{Q₃} has exact eigenvalues {0, 6α, (4+2α)×3, (4+4α)×3}, and at strong confinement (α >> 2) the ratios approach {1:2:3}. Physical consequences on a single stella: three-fold degenerate color-direction excitations, additive energy from Q₃ = C₂³, and new cross-tetrahedron propagator (§2.6 claims i–iv). The mass ratio √2 ≈ 1.414 is within 1.5% of m(2++)/m(0++) ≈ 1.393, though this is suggestive not conclusive. However, the originally claimed FCC band structure (§2.6 vi) is **incorrect**: stellae share 46% of their vertices with neighbors, the FCC produces a continuous dispersion, and the gauge spectrum is representation-diagonal (Prop 2.5.2c). See `stella_genesis/phase_Q3_analytic.py` and `phase_Q3_band_investigation.py`.

3. ~~**Higher Q_n spectra.**~~ **RESOLVED (2026-03-28).** There is no physical or geometric reason to consider Q₄ or higher hypercube embeddings within the framework. Q₃ is uniquely and maximally determined by five independent arguments: (i) **Dimensional** — d_embed = 3 (Prop 0.0.40) caps Q_n at n = 3, since Q_n requires n independent coordinate-flip directions; (ii) **Geometric** — the stella octangula is the only compound polyhedron in 3D whose vertices form a hypercube graph, because the tetrahedron is the unique self-dual Platonic solid (two dual tetrahedra inscribed in a cube occupy its alternate vertices); (iii) **Algebraic** — the derivation chain Observer → D = 4 → N = 3 → Z₃ → stella → Q₃ is fully determined with no free parameters; (iv) **Physical** — Q₃'s 3-fold degenerate T₂ eigenspaces match SU(3)'s 3 color directions, while Q₄'s 4-fold degeneracy would require SU(4+), excluded by Ehrenfest stability in D = 4; (v) **Lattice** — the FCC inter-stella lattice (coordination number 12) produces continuous band dispersion, not Q₄ discrete levels. Numerical verification confirms: projecting Q₄ into R³ destroys its nearest-neighbor structure (0/16 vertices preserved), and no compound of two Platonic solids in 3D produces Q₄ adjacency. See `stella_genesis/phase_Q7_higher_Qn_spectra.py`.

4. ~~**N_eff ≈ 3 robustness.**~~ **RESOLVED (2026-03-27).** N_eff ≈ 3.088 at γ ≈ 0.52 is a **sign-transition artifact**, not a robust feature. At γ ≈ 0.5199, three eigenvalues (λ₃, λ₄, λ₅) simultaneously cross zero, switching the eigenvalue signature from (6−, 1⁰, 1+) → (3−, 1⁰, 4+). The apparent N_eff ≈ 3 is an artifact of three eigenvalues being near-zero and not contributing to spectral entropy. Key evidence: (i) the feature is destroyed by geometric perturbations as small as ε = 0.001 (0% survival at |N_eff − 3| < 0.1); (ii) N_eff never actually reaches 3.0 — the minimum is 3.083; (iii) alternative N_eff definitions (participation ratio, inverse HHI) give N_eff = 3 at a completely different γ ≈ 1.01; (iv) the N_eff ≈ 3 "window" has width Δγ ≈ 0.001, confirming fragility. The {2, 3} eigenvalue ratio structure (H6) remains robust and framework-specific; only the N_eff mode-counting claim is an artifact. See `stella_genesis/phase_h6b_neff3_robustness/run.py`.

5. ~~**Z₃-weighted spectrum.**~~ **RESOLVED (2026-03-27).** The Z₃-weighted stella Laplacian is L(α = −0.5) in the existing parametric family (§2.7). Its spectrum is {−3, 0, +2, +2, +2, +3, +3, +3}: one negative eigenvalue (A₂ staggered mode) signaling center-symmetric instability, plus positive modes with swapped T₂ ordering. The negative eigenvalue is the discrete analog of Z₃ center symmetry driving confinement in SU(3) — the staggered mode (T₊↔T₋ antiphase) becomes energetically favorable. Eigenvectors are the same Q₃ Fourier modes ψ_S; the cross-tetrahedron propagator has a tachyonic pole at m² = 3. This connects the stella's graph spectrum to the Z₃ center-symmetry mechanism verified on the FCC lattice in Phases L3–L4. See `stella_genesis/phase_Q5b_z3_weighted_spectrum/run.py`.

---

*See [Derivation](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Derivation.md) for the complete experimental evidence chain (H1–H7, H3b, H6b, §21.6).*
*See [Applications](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md) for physical interpretation and cross-references.*
