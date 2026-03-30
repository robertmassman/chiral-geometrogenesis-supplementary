# Proposition 0.0.XXg — Derivation: Experimental Evidence Chain

## Status: 🔶 NOVEL 🔸 PARTIAL — EXPERIMENTAL EVIDENCE (CLAIM b FALSIFIED)

**Parent document:** [Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md)

**Source data:** `stella_genesis/RESEARCH-Prime-Interference.md`

---

## 1. Experiment H1: Fisher Eigenvalue Statistics (GUE Test)

### 1.1 Design

Compute the Fisher information matrix g^F of Z_N interference p(x; φ) = |Σ A_c(x) e^{iφ_c}|² at Z_N equilibrium phases for large N (10–200). Test whether eigenvalue spacings match GUE (Gaussian Unitary Ensemble) — the same universality class as Riemann zeros (Montgomery 1973).

GUE diagnostics: normalized nearest-neighbor spacings should follow the Wigner surmise p(s) = (32/π²)s² e^{−4s²/π}, with variance ≈ 0.178 and level repulsion (p(0) = 0).

### 1.2 Results

| N | Non-zero eigenvalues | Spacing variance | GUE variance | Assessment |
|:-:|:-------------------:|:----------------:|:------------:|:-----------|
| 10 | 9 | 2.03 | 0.178 | Super-Poisson |
| 20 | 19 | 2.47 | 0.178 | Super-Poisson |
| 50 | 49 | 2.15 | 0.178 | Super-Poisson |
| 100 | 99 | 2.68 | 0.178 | Super-Poisson |
| 200 | 199 | 2.31 | 0.178 | Super-Poisson |

**Physical explanation:** With Gaussian amplitude bumps at σ = π/√N spacing, neighboring bumps overlap increasingly with N, creating eigenvalue **clusters** rather than the level repulsion characteristic of GUE. The Fisher matrix develops block structure (groups of strongly-correlated nearby components), producing super-Poisson statistics.

Rank grows sub-linearly (approximately √N), indicating progressive degeneracy — opposite to the full-rank behavior expected for GUE.

### 1.3 Verdict

**CLOSED.** GUE universality does not hold for Z_N Fisher eigenvalues at any tested N. The structural parallel between Z_N interference and the Riemann explicit formula does not extend to eigenvalue statistics.

**Code:** `phase_h1` in `stella_genesis/`

---

## 2. Experiment H2: Arithmetic Fisher Matrix (Prime Phases)

### 2.1 Design

Replace Z_N equilibrium phases with **prime phases**: K primes p₁, p₂, ..., p_K have phases φₖ = 2πpₖ/P where P = p_K (largest prime). Compute the Fisher information matrix and analyze its eigenvalue structure.

### 2.2 Results

**Finding 1: Rank = K − 1.** Global phase symmetry (shift all φₖ by constant) removes one dimension, identical to the Z_N case.

**Finding 2: Extreme eigenvalue hierarchy.** Condition numbers grow exponentially with K:

| K | Condition number | Top eigenvalue | Bottom eigenvalue |
|:-:|:----------------:|:--------------:|:-----------------:|
| 10 | ~10² | ~5 | ~0.05 |
| 50 | ~10⁵ | ~8 | ~10⁻⁴ |
| 100 | ~10⁸ | ~8.3 | ~10⁻⁶ |

**Finding 3: Logarithmic effective rank.** The effective rank (Roy-Vetterli entropy-based: erank = exp(−Σ pᵢ ln pᵢ) where pᵢ = λᵢ/Σλⱼ; see Roy & Vetterli, EUSIPCO 2007) grows as:

$$\text{eff\_rank} \approx 4.87 \cdot \ln(K) - 4.54$$

This means K = 100 primes compress to ~20.7 effective dimensions — a ~5× compression.

**Finding 4: Super-Poisson spacings (variance 23.2).** Not GUE (variance 0.178). Consistent with H1.

**Finding 5: Eigenvalue ratio pattern.** The top eigenvalue ratios stabilize:
- λ₁/λ₂ ≈ 2.21
- λ₂/λ₃ ≈ 1.42
- λ₃/λ₄ ≈ 1.25

This same pattern reappears in H5 (zeta zeros).

**Code:** `phase_h2` in `stella_genesis/`

---

## 3. Experiment H3 + H3b: Irreducibility Index Spectral Decomposition

### 3.1 H3 Design

The irreducibility index I(N) from Prop 0.0.3a Phase F3 is nonzero only for primes and decreasing among them: I(3) = 0.417, I(5) = 0.175, I(7) = 0.103, .... Its Dirichlet series D(s) = Σ I(n) n^{−s} is computed and tested for peaks at zeta-zero frequencies γ_ρ.

### 3.2 H3 Initial Results

- Power-law decay: I(p) ≈ 1.22·p^{−1.29} (steeper than the p^{−0.5} expected for alignment)
- Alignment with first 20 zeta zeros: **9/20** at initial N_max (barely above random; H3b retest at N_max=500 gives 10/20 — see table below)
- Enhancement at zeta zeros vs random frequencies: 1.12× (negligible)
- Von Mangoldt control Λ(N): 19/20 alignment

### 3.3 H3b Follow-Up: Weight Normalization (2026-03-23)

**Key insight:** The poor 9/20 alignment was a measurement artifact. The steep p^{−1.29} decay of I(N) causes the Dirichlet series to be dominated by small primes, drowning out the oscillatory zeta-zero signature at larger scales.

Applying weight normalization to flatten the decay:

| Weight function | N_max = 500 | N_max = 2000 |
|:----------------|:-----------:|:------------:|
| Raw I(N) | 10/20 | 11/20 |
| I(N)·N^{0.50} | 14/20 | 16/20 |
| **I(N)·N^{0.79}** | **18/20** | **20/20** |
| **I(N)·N^{1.29}** | **20/20** | **19/20** |
| **I(N)·log(N)·N^{0.5}** | **20/20** | **20/20** |
| Von Mangoldt Λ(N) | 19/20 | 17/20 |

With appropriate normalization, alignment reaches **20/20** — matching or exceeding the von Mangoldt control.

### 3.4 Interpretation

Any function that detects primes (is nonzero on primes and zero/small on composites) will, via the Riemann explicit formula, have spectral peaks at zeta-zero frequencies. The irreducibility index detects primes by construction, so it automatically carries this signature.

**This is a consistency check, not a discovery.** It confirms I(N) is a genuine prime detector but does not establish a special connection between the stella and the zeta function beyond what any prime-detecting function provides.

**Code:** `phase_h3b` in `stella_genesis/`

---

## 4. Experiment H4: Discrete xp Operator (Berry-Keating)

### 4.1 Design

Berry and Keating conjectured that the Riemann zeros are eigenvalues of a quantization of H = xp. Discretize this on a Z_N lattice using DFT-based position and momentum operators and compute eigenvalues.

### 4.2 Results

| N | First 5 eigenvalue ratios | Zeta-zero ratios | Assessment |
|:-:|:------------------------:|:----------------:|:-----------|
| 50 | 1.0, 4.9, 8.7, 12.5, 16.2 | 1.0, 1.49, 1.77, 2.15, 2.33 | Wrong by 3–8× |
| 100 | 1.0, 4.7, 8.4, 12.1, 15.8 | (same) | No improvement |
| 200 | 1.0, 4.8, 8.5, 12.2, 15.9 | (same) | No convergence |

- Eigenvalues are approximately **equally spaced**, not logarithmically spaced like zeta zeros
- RMS error on first 5 zeros: ~8%, bottoms at N ≈ 50, then **increases** (divergence)
- Prime vs composite N: no meaningful difference
- Log-position variant: improves error to ~3%, but still wrong ratios and no convergence

### 4.3 Verdict

**CLOSED.** The naive DFT-based discretization fails completely. This is consistent with the literature: the Berry-Keating conjecture requires specific (unknown) boundary conditions that simple lattice discretization cannot capture. The Z_N structure adds nothing.

**Code:** `phase_h4` in `stella_genesis/`

---

## 5. Experiment H5: Fisher Rank of Zeta-Zero Interference

### 5.1 Design

Compute the Fisher information matrix for K-component interference where the phases are set to the first K Riemann zeta zeros: φₖ = γₖ (imaginary parts of non-trivial zeros). Compare the eigenvalue structure to H2 (prime phases).

### 5.2 Results

**Finding 1: Full rank K** (unlike H2's K − 1). The constant "1" term in the explicit formula ψ(x) = x − Σ x^ρ/ρ − ... breaks the global phase symmetry.

**Finding 2: Top eigenvalues stabilize.** λ₁ ≈ 8.33, λ₂ ≈ 3.77, λ₃ ≈ 2.65 — constant regardless of K.

**Finding 3: Gentle condition number growth.** Condition ≈ 2K (linear), vs H2's exponential. Zeta zeros are more "evenly distributed" in information space.

**Finding 4: Logarithmic effective rank — SAME law as H2:**

| System | Fit | Slope |
|:-------|:----|:-----:|
| H2 (primes) | eff_rank ≈ 4.87·ln(K) − 4.54 | 4.87 |
| **H5 (zeta zeros)** | **eff_rank ≈ 5.52·ln(K) − 4.19** | **5.52** |

**Slopes differ by only 13%.** Both compress logarithmically with nearly identical rates.

**Finding 5: Identical eigenvalue ratio pattern:**

| Ratio | H2 (primes) | H5 (zeta zeros) |
|:------|:-----------:|:----------------:|
| λ₁/λ₂ | 2.21 | 2.21 |
| λ₂/λ₃ | 1.42 | 1.42 |
| λ₃/λ₄ | 1.25 | 1.24 |

The top eigenvalue ratios match to within 1% — a striking structural parallel.

**Finding 6: Super-Poisson spacings (variance 15.6).** Not GUE, consistent with H1/H2.

**Finding 7: Domain robustness.** Effective rank is stable across 20× range of integration domains — the logarithmic compression is not an artifact of domain choice.

### 5.3 Interpretation

The H2/H5 logarithmic compression similarity is genuine but §21.6 shows it is a **universal property of 1D multi-frequency interference** with decaying amplitudes — not specific to primes or zeta zeros. The prime number theorem ensures primes have ~logarithmic spacing, which produces the same compression behavior as the (also roughly log-spaced) zeta zeros.

**Code:** `phase_h5` in `stella_genesis/`

---

## 6. Experiment H6 + H6b: Scale-Tuned Z₃ Prime Resonance

### 6.1 Design

The stella's Z₃ interference depends on a confinement parameter σ (width of Gaussian amplitude bumps at vertices). Sweep σ and track eigenvalue ratios to find "prime crossings" — values of σ where an eigenvalue ratio passes through a prime number.

### 6.2 H6 Results

#### Finding 1: {1, 1, 1, 2, 2, 2, 3} Eigenvalue Ratios (Core Result)

In the strong-confinement regime (σ ≲ 0.37, without Z_N weighting), eigenvalue ratios converge to:

$$\{1, 1, 1, 2, 2, 2, 3\}$$

**Corrected mechanism (Q₃ graph Laplacian):** The stella's 8 vertices connected by cross-nearest edges (distance 2/√3 ≈ 1.155) form the 3-dimensional hypercube graph Q₃. The Q_n graph Laplacian has eigenvalues 2k with multiplicity C(n,k) for k = 0, ..., n. For Q₃, the nonzero eigenvalue ratios are {1(×3), 2(×3), 3(×1)}.

**Three distinct distances on the unit stella:**
- Cross-nearest: 2/√3 ≈ 1.155 (T₊ vertex to 3 nearest T₋ vertices) — 12 pairs
- Intra-tetrahedron edge: √(8/3) ≈ 1.633 (within each tetrahedron) — 12 pairs
- Cross-antipodal: 2.0 (T₊ vertex to diametrically opposite T₋ vertex) — 4 pairs

At small σ, only the cross-nearest pairs (shortest distance) have significant Gaussian coupling. These form the Q₃ graph, giving the {1,1,1,2,2,2,3} ratio pattern.

**Z_N independence:** Adversarial testing confirms identical ratios with no Z_N, Z₅, and Z₇ weighting. With Z₃ weighting (cos(2π/3) = −0.5), all cross-tetrahedron couplings become negative, producing all-negative eigenvalues — the Z₃ factor destroys rather than creates the pattern. The ratios depend solely on the Q₃ graph structure, not Z₃ symmetry.

**Why {2, 3} coincide with construction numbers:** 2 = number of tetrahedra, 3 = |Z₃|. But this is a consequence of Q₃ being 3-dimensional (the stella has 8 = 2³ vertices arranged as a 3-cube). The Q₄ hypercube would give ratios {1, 2, 3, 4}, where 4 is composite — demonstrating that the "prime" aspect is a small-number coincidence.

#### Finding 2: 3-fold Degeneracy

Eigenvalue crossings come in triples (plus occasional singlets), reflecting the T₂ irreducible representation of the tetrahedral symmetry group T_d. This corresponds to the three C₂ axes (edge-midpoint to opposite edge-midpoint) of the tetrahedron, or equivalently, the three coordinate directions of the embedding cube.

#### Finding 3: 130 Prime Crossings Cluster

| σ range | Crossings | Fraction |
|:--------|:---------:|:--------:|
| [0.20, 0.59] | 4 | 3% |
| **[0.59, 0.98]** | **91** | **70%** |
| [0.98, 1.37] | 34 | 26% |
| [1.37, 8.00] | 1 | 1% |

Crossings cluster overwhelmingly in the transition zone σ ∈ [0.59, 0.98] between intra-tetrahedron and cross-tetrahedron coupling regimes.

#### Finding 4: Each Prime Has a σ "Note"

Primes 2 and 3 appear via the triple channel (3-fold degenerate modes). Primes ≥ 5 appear via singlet channels. Higher primes crowd together, reflecting the logarithmic spacing of primes.

#### Finding 5: Ring Mode Counting

Z₃ ring modes produce prime mode counts at 28% of scales — consistent with the prime number theorem prediction of ~20–30%, indicating no preferential selection beyond the PNT baseline.

### 6.3 H6b: N_eff Resolution (2026-03-24, updated 2026-03-27)

The effective number of independent modes (N_eff) reaches ~3.088 at γ ≈ 0.52. The definitive robustness investigation (six independent tests, 2026-03-27) confirms this is a **sign-transition artifact**:

1. **Mechanism identified:** At γ ≈ 0.5199, three eigenvalues (λ₃, λ₄, λ₅) simultaneously cross through zero, switching the eigenvalue signature from (6−, 1⁰, 1+) → (3−, 1⁰, 4+). The spectrum at γ = 0.52 is {−0.375, −0.375, −0.375, 0, +0.0002, +0.0002, +0.0002, +1.625}: three eigenvalues near zero means only ~3 modes contribute to spectral entropy.

2. **Not robust under perturbation:** Even ε = 0.001 geometric perturbations destroy the feature — 0% of 50 trials have |N_eff − 3| < 0.1. By ε = 0.05, the best N_eff shifts to ~3.66.

3. **N_eff never reaches 3.0:** The Shannon-entropy minimum is N_eff ≈ 3.083, with |N_eff − 3| ≈ 0.083.

4. **Definition-dependent:** Participation ratio and inverse HHI both give N_eff = 3.0007 but at γ ≈ 1.01 (not 0.52), with a wide window Δγ ≈ 0.57. The three definitions disagree on location by Δγ ≈ 0.49.

5. **Narrow window confirmed:** The Shannon-entropy window |N_eff − 3| < 0.1 has width Δγ ≈ 0.001, consistent with the original estimate.

6. **Analytic explanation:** N_eff(γ) is non-monotonic with a local minimum at γ ≈ 0.52 coinciding precisely with the eigenvalue sign transition. The slope dN_eff/dγ ≈ 5.2 at the crossing means the N_eff ≈ 3 feature spans only Δγ ≈ 0.019 even at ΔN_eff = 0.1 tolerance.

**Verdict:** The {2, 3} eigenvalue ratio structure is robust and framework-specific. The N_eff ≈ 3 feature is a **sign-transition artifact** — it occurs because three eigenvalues simultaneously pass through zero at a specific γ, not because the stella has an intrinsic three-mode structure. This claim should not be relied upon.

**Code:** `phase_h6`, `phase_h6b_neff3`, `phase_h6b_neff3_robustness/run.py` in `stella_genesis/`

---

## 7. Experiment H7: Spectral Factorization

### 7.1 Design

Use the stella's prime-encoding mode structure to detect divisibility. If eigenvalue ratios at a given σ are (r₁, r₂, ...), check whether a target integer N is divisible by the nearest prime to each rᵢ.

### 7.2 Results

The stella acts as a factorization device for 2 and 3:
- Z₃ stella detects factors {2, 3} via its {1, 1, 1, 2, 2, 2, 3} eigenvalue structure
- A cascade of Z_p resonators (Z₃, Z₅, Z₇, ...) could in principle extend to arbitrary primes

**However:** This factorization-by-eigenvalue-ratio is computationally equivalent to trial division:
- Reading an eigenvalue ratio costs at least O(1) per ratio
- Checking if N is divisible by 2, then by 3, etc. is trial division
- No speedup over the simplest classical algorithm

### 7.3 Verdict

Conceptually interesting — the stella "knows" about 2 and 3 through its geometry — but computationally trivial. Consistent with Prop 0.0.XXf's classification of stella computation as Level 1 (natural encoding, no complexity advantage).

**Code:** `phase_h7` in `stella_genesis/`

---

## 8. Section 21.6: Information Amplification on ∂S (3D Fisher Analysis) — FALSIFIED

### 8.1 Motivation

Experiments H2 and H5 found that prime-phase interference shows maximum compression (lowest effective rank per component) in 1D. But these were all computed on a 1D line segment. How does the stella's actual 3D surface change the story?

### 8.2 Design

Compute Fisher information matrices on three domains:
1. **Stella graph** (8 vertices, adjacency-weighted)
2. **Stella surface** (8 triangular faces with interior sample points)
3. **1D reference** (line segment [0, 200])

For four frequency sets:
- **Prime frequencies:** {2, 3, 5, 7, 11, 13, ...}
- **Equal-spaced:** {1, 2, 3, 4, 5, ...}
- **Random:** uniform random in [1, 200]
- **Integer:** {1, 2, 3, ..., K}

Measure effective rank (Roy-Vetterli entropy-based) as a function of K for each (domain, frequency set) pair.

### 8.3 Original Results (from `phase_h_3d_fisher.c`)

| Domain | Prime slope | Equal slope | Random slope | Integer slope |
|:-------|:----------:|:----------:|:------------:|:------------:|
| **Stella surface** | **1.11** | 0.77 | 0.65 | 0.52 |
| Stella graph | 0.48 | 0.40 | 0.35 | 0.31 |
| 1D line | 4.89 | 10.65 | 8.76 | 8.65 |

The original analysis claimed an "inversion": primes most compressed in 1D but most information-rich on ∂S.

### 8.4 Adversarial Retest with Control Geometries (2026-03-27)

**Note:** This section documents the initial adversarial retest that raised the discrepancy. The definitive resolution is in §8.5.

When the analysis is repeated with control geometries (two disjoint spheres, random 8-vertex polyhedra) and consistent Fisher formulas, the claimed inversion does **not** reproduce:

| Domain | Prime slope | Integer slope | Which is higher? |
|:-------|:----------:|:------------:|:-----------------|
| 1D line | ~11.0 | ~13.1 | Integers |
| Stella surface | ~9.5 | ~11.8 | **Integers** |
| Two-spheres control | ~9.2 | ~11.9 | Integers |
| Random 8-vertex | ~9.3 | ~12.6 | Integers |

Integer frequencies consistently have higher effective-rank slope than primes on **all** tested geometries.

**Sources of discrepancy identified (resolved in §8.5):**
1. **Fisher formula inconsistency:** The original `phase_h_3d_fisher.c` computed `dp[k] = 2.0 * x * (...)` for the 1D Model C but `dp[k] = (...)` (without `2*x`) for 3D Models A/B — comparing frequency-Fisher (1D) against phase-Fisher (3D).
2. **Different absolute scales:** Original slopes (0.5–11) vs retest slopes (9–13) differ by ~10×, suggesting different normalization or integration domains.
3. **Different surface sampling:** Original may have used a different surface discretization for the stella.

### 8.5 Definitive Resolution (2026-03-27)

A systematic variable-isolation test (`verification/definitive_info_amplification.py`) identified three independent inconsistencies between the original C code and the Python adversarial retest:

| Parameter | C code (original) | Python retest |
|:----------|:-------------------|:--------------|
| Fisher formula (1D) | ∂P/∂ω_k (with `2*x` factor) | ∂P/∂θ_k (no `2*x`) |
| Fisher formula (3D) | ∂P/∂θ_k | ∂P/∂θ_k |
| Frequencies | `log(prime[k])` | `prime[k]` (raw) |
| Amplitudes | `1/√prime[k]` | `exp(-0.01·f)` |

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

### 8.6 Status

**This section's results are FALSIFIED.** The definitive resolution test resolved all three outstanding items from §8.4. No stella-specific amplification exists under any parameter combination.

### 8.7 What IS Confirmed

The stella graph (8 vertices) saturates at effective rank ~4 for all frequency sets when K > 7, regardless of frequency type. This is a genuine limitation of the discrete graph — it cannot distinguish between different frequency sets at scale. The stella surface retains more capacity, but no geometry-specific frequency ordering exists.

**Code:** `phase_h_3d_fisher` in `stella_genesis/` (original); `verify_prop_XXg_corrections.py` and `adversarial_prop_XXg_spectral_prime.c` (retest); `verification/definitive_info_amplification.py` (definitive resolution)

---

## 9. Statistical Summary

### 9.1 Negative Results (Bridges Closed)

| Bridge | Experiment | Diagnostic | Expected | Observed | Verdict |
|:-------|:-----------|:-----------|:---------|:---------|:--------|
| GUE universality | H1 | Spacing variance | 0.178 | 2.0–2.7 | **Closed** |
| GUE (prime phases) | H2 | Spacing variance | 0.178 | 23.2 | **Closed** |
| GUE (zeta zeros) | H5 | Spacing variance | 0.178 | 15.6 | **Closed** (Fisher-level) |
| Zeta zeros ARE GUE | H5 (control) | Spacing variance | 0.178 | **0.174** (finite-sample) | ✓ Confirmed |
| Discrete xp | H4 | Eigenvalue ratios | ~1.5 | ~5.0 | **Closed** |

### 9.2 Positive Results (Framework-Specific)

| Result | Experiment | Metric | Value |
|:-------|:-----------|:-------|:------|
| Q₃ ratios {1,2,3} | H6 + adversarial | Eigenvalue ratios (no Z_N, σ ≲ 0.3) | {1,1,1,2,2,2,3} (Q₃ Laplacian) |
| Info amplification | §21.6 | Prime slope on ∂S | **FALSIFIED** (frequency-mapping artifact; see `definitive_info_amplification.py`) |
| {2, 3} in computation | Prop 0.0.XXf §5.4 | Essential opcodes | CPY01 (2), OPEN/CLOSE (3) |

### 9.3 Positive Results (Universal, Not Framework-Specific)

| Result | Experiments | Metric | Value |
|:-------|:-----------|:-------|:------|
| Log rank compression | H2, H5 | Slope comparison | 4.87 vs 5.52 (13% diff) |
| Eigenvalue ratio pattern | H2, H5 | λ₁/λ₂ | 2.21 (both) |
| Spectral decomposition | H3b | Zeta-zero alignment | 20/20 with weights |

---

*Parent document: [Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula.md)*
*Applications: [Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md](Proposition-0.0.XXg-Q3-Spectral-Structure-Stella-Octangula-Applications.md)*
