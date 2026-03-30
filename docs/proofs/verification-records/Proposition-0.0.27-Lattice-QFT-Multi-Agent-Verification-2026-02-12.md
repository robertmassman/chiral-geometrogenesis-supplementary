# Proposition 0.0.27: Lattice QFT Formalization on ∂S
# Multi-Agent Adversarial Verification Report

**Date:** 2026-02-12
**Document:** `docs/proofs/foundations/Proposition-0.0.27-Lattice-QFT-On-Stella.md`
**Verification Agents:** 4 independent adversarial agents (Core Framework, Coefficient Matching, Advanced Formalism, Simulations & Numerics)
**Model:** Claude Opus 4.6
**Overall Verdict:** **FAILED** — 24 errors found (15 CRITICAL), 22 warnings. Core claims not supported by calculations presented.

---

## Executive Summary

| Agent | Section Range | Verdict | Confidence | Errors | Warnings |
|-------|--------------|---------|------------|--------|----------|
| **1: Core Framework** | §10.3.1–10.3.11 | **FAILED** | High | 8 (5 critical) | 5 (3 high) |
| **2: Coefficient Matching** | §10.3.12.1–10.3.12.10.10 | **FAILED** | High | 5 (5 critical) | 5 (3 major) |
| **3: Advanced Formalism** | §10.3.12.10.11–10.3.12.10.15 | **FAILED** | High | 6 (4 critical) | 7 (2 high) |
| **4: Simulations & Numerics** | §10.3.12.10.16–10.3.12.10.21 | **PARTIAL** | High | 5 (2 critical) | 5 (2 high) |

**Consensus:** The document contains genuine mathematical content (graph Laplacian calculations, simplicial topology, working Monte Carlo code) but the central novel claims — that Feynman diagrams "emerge" from K₄, that Symanzik improvement coefficients are "geometrically derived," and that the stella supports full QFT — are not supported by the evidence presented. The main issues are:

1. **K₄ is a 4-site toy model with no continuum limit** — this is acknowledged late in the document but contradicted by earlier sections
2. **Numerology mistaken for derivation** — simplex count ratios coinciding with known lattice coefficients are post-hoc identifications, not derivations
3. **Multiple mathematical errors** — propagator normalization, coupling power inconsistencies, false 4-cycle claim, wrong deficit angle calculation
4. **Verification scripts do not test what is claimed** — several tests verify standard lattice theory or use mock data, not stella-specific physics

---

## 1. Core Framework (§10.3.1–10.3.11) — Agent 1

### Verdict: FAILED | Confidence: High

### Critical Errors

**E1.1 [CRITICAL]: Triangle paths are vacuum diagrams, not self-energy (§10.3.4, §10.3.7)**
The closed triangular path (v₁→v₂→v₃→v₁) is labeled as a "one-loop self-energy." In standard QFT, a one-loop self-energy is a bubble diagram (2 vertices, 2 propagators). A closed triangle with 3 vertices and 3 propagators with no external legs is a vacuum diagram at O(λ₃³). The paper conflates these throughout.

**E1.2 [CRITICAL]: Coupling power inconsistency (§10.3.4 vs §10.3.12.2)**
- §10.3.4 (Theorem 10.3.4.2): Γ_triangle = (−λ₃)³/6 · G³ — three powers of coupling
- §10.3.12.2 (Step 3): Σ_triangle = λ₃²/2 · G³ · (1/3!) — two powers of coupling

Both cannot be correct. If there are 3 vertices, the result should be λ₃³; if it's a self-energy with 2 vertices, it should be λ₃² with 2 propagators.

**E1.3 [CRITICAL]: Cubic vs quartic coupling conflation (§10.3.4 vs §10.3.12.6)**
- §10.3.2–10.3.7 compute using cubic coupling λ₃ (triangle diagrams)
- §10.3.12.6 matches against quartic coupling formula: δm²/m² = λ/(16π²)·ln(μ²/m²) where λ = 1/8

The standard one-loop Higgs mass correction from quartic self-coupling is a tadpole (1 vertex, 1 loop), not a triangle. The paper switches between cubic and quartic without justification.

**E1.4 [CRITICAL]: K₄ has no continuum limit (§10.3.6)**
Theorem 10.3.6.1 claims discrete path sums reproduce continuum Feynman integrals as a→0. But K₄ has 4 fixed vertices, no Brillouin zone, no lattice spacing to vary, no spatial extent. The invocation of Prop 0.0.6b (FCC lattice) is a non-sequitur — calculations are done on K₄, not FCC.

**E1.5 [CRITICAL]: Dimensional mismatch ad hoc resolution (§10.3.12.4)**
The discrete result has dimension [mass]⁻⁶ while the continuum has [mass]⁻². The normalization factor 1/a⁴ · (1/n_modes) is introduced without first-principles derivation. Standard lattice matching uses the Brillouin zone Fourier transform, which doesn't exist for K₄.

**E1.6 [MEDIUM]: False claim about 4-cycles on K₄ (§10.3.12.9.2)**
The table states "K₄ has no 4-cycles." This is false. K₄ has (4−1)!/2 = 3 Hamiltonian cycles (length-4 closed paths).

**E1.7 [MEDIUM]: Mass parameter confusion (§10.3.7)**
Uses m_H² = 0.258 (dimensionless ratio) directly in the lattice propagator formula, but the lattice propagator uses dimensionless lattice mass m̃² = m_H²a²/(ℏc)² ~ 10⁻³⁴. These differ by 33 orders of magnitude.

**E1.8 [LOW]: Edge count description error (§10.3.1)**
Table states "12 edges (per tetrahedron)" — each K₄ has 6 edges. Should say "12 edges total (6 per tetrahedron)."

### Warnings

**W1.1 [HIGH]: Feynman rule replacement is dimensionally wrong (§10.3.5(c))**
The replacement ∫d⁴k/(2π)⁴ → (1/|V|)Σ equates [mass]⁴ with a dimensionless quantity. Standard lattice replacement requires a Brillouin zone.

**W1.2 [HIGH]: "ESTABLISHED" status for unreviewed sections (§10.3.9)**
Status table marks items as "ESTABLISHED" by forward-referencing §10.3.13–10.3.16. Claims like "Local gauge invariance ESTABLISHED" and "Full RG flow ESTABLISHED" are extraordinary.

**W1.3 [HIGH]: 40% discrepancy rationalized, not explained (§10.3.12.9)**
The lattice QCD comparison (30–50% before improvement) applies to infinite-volume lattices with millions of sites, not a 4-site toy model.

**W1.4 [MEDIUM]: Symmetry factor inconsistencies (§10.3.4 vs §10.3.12.2)**
Inconsistent bookkeeping of |Aut(triangle)| between sections.

**W1.5 [MEDIUM]: Beta function claim without derivation (§10.3.10(e))**
Claims β(λ) = 3λ²/(16π²) is "reproduced from discrete path sums" but no supporting calculation appears in these sections.

### Independent Re-Derivations

| Quantity | Paper | Independent | Match? |
|----------|-------|-------------|--------|
| K₄ Laplacian eigenvalues | {0, 4, 4, 4} | {0, 4, 4, 4} | **YES** |
| G(v,v) at m² | (1+m²)/(m²(4+m²)) | (1+m²)/(m²(4+m²)) | **YES** |
| G(v≠w) at m² | 1/(m²(4+m²)) | 1/(m²(4+m²)) | **YES** |
| Continuum C_finite | ~0.19 | 2 − π/√3 = 0.186 | **YES** |
| Triangle count on K₄ | 4 | C(4,3) = 4 | **YES** |
| 4-cycle count on K₄ | 0 | 3 | **NO** |

### Circular Reasoning

The coefficient matching normalization has too many adjustable factors (1/a⁴, 1/n_modes, symmetry factors) relative to the single quantity being compared. The agreement between λ = 1/8 and 1/n_modes = 1/8 is presented as "deep consistency" but is a numerical coincidence (8 vertices = 1/λ).

---

## 2. Coefficient Matching (§10.3.12.1–10.3.12.10.10) — Agent 2

### Verdict: FAILED | Confidence: High

### Critical Errors

**E2.1 [CRITICAL]: Arithmetic error in discrete one-loop formula (§10.3.12.6)**
The document simplifies 8·(1/8)³/(8·16π²) to (1/8)²/(16π²), silently dropping the n_modes = 8 denominator. Correct result: 1/(8192π²) ≈ 0.047%, not the claimed 0.15%. This makes the actual discrepancy with continuum (0.11%) approximately **57%**, not 40%.

**E2.2 [CRITICAL]: Incompatible parametric structure (§10.3.12.2–6)**
- Discrete result: δm²/m² ∝ **λ²** · ln(Λ_UV/m)
- Continuum result: δm²/m² ∝ **λ¹** · ln(μ²/m²)

Different powers of λ and different logarithmic arguments. Approximate numerical agreement arises from λ²·38.2 ≈ λ·1.39 coincidentally at λ = 1/8. This is not structural matching.

**E2.3 [CRITICAL]: c₁ = 1/12 conflates unrelated mathematical facts (§10.3.12.10.7)**
Standard Symanzik c₁ = 1/12 comes from Taylor-expanding the hypercubic dispersion relation (4/a²)sin²(pa/2). K₄ has no dispersion relation, no momentum variable, and no lattice spacing. The "derivation" via Tr(L_{K₄}) = 12 is a graph-theoretic identity that numerically coincides with the hypercubic value. Alternative matching calculations on K₄ give different values (1/4, 1/8, 1/48), which the document dismisses as "convention-dependent."

**E2.4 [CRITICAL]: Propagator normalization error invalidates Euler characteristic connection (§10.3.12.10.9)**
The document uses G(v,v) = 1/m² + 3/(4+m²). The correct matrix inverse gives G(v,v) = **1/(4m²)** + 3/(4(4+m²)) — a factor of 4 too large. This doesn't affect ratios, but critically affects the geometric ratio r = 3/4 and its claimed connection to the Euler characteristic. With correct normalization: finite part → 3/16 (not 3/4), and the formula r = 1 − χ/(2n_v) **fails**.

**E2.5 [CRITICAL]: c_SW = 2/3 is a category error (§10.3.12.10.10)**
The Sheikholeslami-Wohlert clover coefficient is defined for Wilson fermions on hypercubic lattices through on-shell improvement matching. The document derives c_SW = n_f/n_e = 2/3 as a topological ratio — a correct combinatorial identity (from 3n_f = 2n_e for triangulated surfaces) that has no mathematical connection to the clover coefficient. Furthermore, the choice of when to use K₄ vs. full stella is made post-hoc to obtain the desired answer.

### Warnings

**W2.1 [MAJOR]: c₂ = 1/8 is a conjecture, not a derivation (§10.3.12.10.8)**
The document itself acknowledges (line 1127): "c₂ = 1/8 result... should be understood as a conjecture supported by the pattern, rather than an independent derivation." Direct calculation gives c₂ = 3/4.

**W2.2 [MAJOR]: Non-standard self-energy formula (§10.3.12.10.9b)**
The one-loop self-energy involves a product of three propagators. Standard φ⁴ one-loop tadpole is δm² = (λ/2)·G(v,v). The document's formula is not a standard Feynman diagram topology.

**W2.3 [MAJOR]: Misleading lattice QCD comparison (§10.3.12.9.4)**
"30–50% precision at one-loop without improvement is standard" applies to large lattices approximating continuum theory, not to 4-site toy models.

**W2.4 [MODERATE]: Alternative derivations give different values (§10.3.12.10.7b)**
Direct matching on K₄ gives c₁ = 1/4, 1/8, or 1/48 depending on convention. No argument given for why Tr(L) is convention-independent.

**W2.5 [MODERATE]: Geometric series pattern asserted, not derived (§10.3.12.10.9e)**
The pattern f_p = r^p follows trivially from the chosen definition f₂ = f₁², not from independent derivation.

### Numerology vs Derivation Assessment

**Honest assessment: These are numerology, not derivations.**

| Coefficient | Claimed derivation | Actual status |
|---|---|---|
| c₁ = 1/12 | From Tr(L_{K₄}) = 12 | Graph identity coinciding with hypercubic value |
| c₂ = 1/8 | From n_faces = 8 | Self-acknowledged conjecture; direct calc gives 3/4 |
| r = 3/4 | Euler characteristic | Based on wrong propagator normalization |
| c_SW = 2/3 | From n_f/n_e | Combinatorial identity, not the clover coefficient |

---

## 3. Advanced Formalism (§10.3.12.10.11–10.3.12.10.15) — Agent 3

### Verdict: FAILED | Confidence: High

### Critical Errors

**E3.1 [CRITICAL]: Ginsparg-Wilson proof uses false intermediate (§10.3.12.10.15l)**
Step 2 claims γ₅Sγ₅ = −S because "H_W = γ₅D_W anti-commutes with γ₅." This is **false** — H_W does NOT anti-commute with γ₅ when D_W contains the Wilson term. The GW relation still holds (provable from S² = I alone), but the proof as written is mathematically invalid — it arrives at the right answer through compensating errors.

**E3.2 [CRITICAL]: Deficit angle confuses dihedral and face angles (§10.3.12.10.13b)**
Uses dihedral angle arccos(1/3) = 70.53° in the deficit formula. For 2D Regge calculus, the correct angle is the face angle at the vertex (π/3 = 60° for equilateral triangle). Correct deficit: ε = 2π − 3(π/3) = π, consistent with Gauss-Bonnet. The "extrinsic vs intrinsic" resolution is wrong — it's simply using the wrong angle.

**E3.3 [CRITICAL]: Instanton claims on 2D surface are dimensionally wrong (§10.3.12.10.14j)**
Instantons are classified by π₃(G) on 4-manifolds. The stella boundary ∂S is a 2D surface. The relevant homotopy group for bundles over S² is π₁(G), which is trivial for SU(3). You cannot have instantons on a 2D surface. The formula n_inst = Q/8 is physically meaningless here.

**E3.4 [CRITICAL]: Wilson-Dirac matrix has uncorrected numerical error (§10.3.12.10.15g)**
Diagonal blocks shown as −9/2·I₄. Self-correction notes they should be −9/4·I₄, but the displayed matrix was never updated.

**E3.5 [SERIOUS]: "Gravity-matter duality" is a tautology (§10.3.12.10.13g)**
The relation r · c_{R,Δ} = (n_e/n_v)·(n_v/n_e) = 1 is algebraically trivial — any ratio times its inverse equals 1. This is not a physical duality.

**E3.6 [SERIOUS]: H¹ dimension counting is garbled (§10.3.12.10.14i)**
States dim(G⁶) = 48, flatness = 32, gauge = 32, then jumps to "48−24−24 = 0" without explaining where the 24s come from. Result H¹ = 0 is correct but the proof has unjustified leaps.

### Warnings

**W3.1 [HIGH]: "Completeness Theorem" is tautological (§10.3.12.10.11)**
States improvement coefficients can be expressed in terms of simplex counts — but the axioms define them as simplex counts. The theorem restates the assumptions.

**W3.2 [HIGH]: No continuum limit on K₄ (§10.3.12.10.15q)**
D_ov = iγ^μ∂_μ + O(a) cannot be verified on 4 sites with no lattice spacing parameter.

**W3.3 [MEDIUM]: SM gauge group "accommodation" is numerology (§10.3.12.10.14l)**
"8 gluons ↔ 8 vertices" and "3 W bosons ↔ 3 edges per face" are numerical coincidences. No mathematical mapping is constructed.

**W3.4 [MEDIUM]: Anomaly coefficient interpretation is numerology (§10.3.12.10.14m)**
1/(16π²) = [1/(4π)]² with "two factors for T₊ and T₋" is a factorization of a number, not a derivation.

**W3.5 [MEDIUM]: r = 3/2 Wilson parameter is a convention (§10.3.12.10.12c)**
Defined as n_e/n_v = 6/4 = 3/2. This is a normalization choice presented as a geometric derivation.

**W3.6 [LOW]: One-loop formula only verified for K₄ (§10.3.12.10.11g)**
Generalization to arbitrary simplicial complexes is a conjecture, not a theorem.

**W3.7 [LOW]: Hodge Laplacian notation conflation (§10.3.12.10.11d)**
Mixes chain boundary and cochain coboundary operators ambiguously.

### Scope Inflation Assessment

**Severe.** K₄ can meaningfully support simplicial cohomology and finite-dimensional linear algebra. It cannot meaningfully support: continuum limits, fermion physics, gravitational dynamics (2D surface, no bulk), instanton physics (wrong dimension), or the full SM gauge group.

---

## 4. Simulations & Numerics (§10.3.12.10.16–10.3.12.10.21) — Agent 4

### Verdict: PARTIAL | Confidence: High

### Critical Errors

**E4.1 [CRITICAL]: Continuum extrapolation on K₄ is incoherent (§10.3.12.10.18p)**
K₄ has 4 fixed vertices and no lattice spacing. The verification script generates **mock data** with hand-inserted O(a²) coefficients and known answer λ = 0.125, then "extrapolates" to recover 0.125. This is circular. The document acknowledges K₄ has no continuum limit (§10.3.12.10.19d) but then presents a full extrapolation table (§10.3.12.10.18p) — a direct contradiction.

**E4.2 [CRITICAL]: Improvement scaling test uses wrong lattice (§10.3.12.10.18j)**
The verification script tests the dispersion relation (4/a²)sin²(pa/2) on a **1D periodic lattice**, not K₄. K₄ has no momentum modes and no dispersion relation. The test verifies standard textbook lattice theory, not anything stella-specific.

**E4.3 [MAJOR]: "Fermion doublers" conflation (§10.3.12.10.16e)**
Claims K₄ has "3 doublers" vs hypercubic "15 doublers." The document later correctly notes (§10.3.12.10.20f) that Nielsen-Ninomiya doesn't apply to K₄ and "doublers" is undefined for finite non-periodic graphs. Earlier sections use this misleading terminology.

**E4.4 [MODERATE]: Plaquette test does not test plaquettes (§10.3.12.10.18c)**
The Monte Carlo script samples a **single SU(2) link** from the Haar measure, not a plaquette (3-link triangle) on K₄.

**E4.5 [MODERATE]: Deficit angle interpretation (§10.3.12.10.16h)**
Connection between 1/n_f and the Regge action coefficient 1/(8πG) is asserted without derivation.

### Warnings

**W4.1 [HIGH]: Higgs quartic comparison is tautological (§10.3.12.10.16l)**
λ = 1/8 as input → m_H = √(2λ)v as output is not a prediction. The 3.4% deviation of λ from PDG is interesting, but the m_H comparison adds no information.

**W4.2 [HIGH]: Four-point function test does not verify λ = 1/8 (§10.3.12.10.18g)**
The script runs Monte Carlo with λ = 1/8 **as input** and checks consistency with perturbation theory for that λ. This tests the code, not the physics.

**W4.3 [MEDIUM]: Statistical analysis uses synthetic data (§10.3.12.10.18o)**
Script generates an AR(1) process with ρ = 0.9, verifying standard statistical methods — not stella-specific autocorrelation.

**W4.4 [MEDIUM]: "No free parameters" is overstated (§10.3.12.10.17g)**
Simulations still require β, m², κ, leapfrog steps, step size, etc. Only improvement coefficients are "geometric."

**W4.5 [MEDIUM]: c₁ = 1/12 "universality" is misleading (§10.3.12.10.16f)**
Hypercubic c₁ = 1/12 comes from Wilson loop Feynman rules. Stella c₁ = 1/12 is defined as 1/n_edges. Numerical coincidence, not universality.

### Verification Script Grades

| Script | Grade | Assessment |
|--------|-------|------------|
| `verify_prop_0_0_27_improvement_coefficients.py` | **C** | Correct but trivial (verifies arithmetic like 1/12 × 12 = 1) |
| `verify_prop_0_0_27_lattice_cg_simulations.py` | **C+** | Tests textbook graph theory and free-field QM on 4 sites |
| `verify_prop_0_0_27_monte_carlo_stella.py` | **D** | Multiple tests misrepresented: plaquette ≠ plaquette, uses periodic lattice not K₄, mock data |
| `stella_production_simulation.py` | **B+** | Solid HMC implementation, honest about limitations |
| `hypercubic_lattice_simulation.py` | **B** | Correct standard implementation |
| `stella_vs_hypercubic_comparison.py` | **C+** | Correct comparison, overstated conclusions in output text |

### Finite-Size Honesty

**Grade: B+.** Sections §10.3.12.10.19–20 are commendably honest (SSB can't occur on 4 sites, K₄ has no continuum limit, Higgs mass is tautological). But earlier sections §10.3.12.10.16–18 lack these caveats and make claims that §10.3.12.10.19 explicitly retracts.

### Quantum Computing (§10.3.12.10.21)

**Mostly speculation.** K₄ is trivially solvable by exact diagonalization — there is no quantum advantage scenario. The valid point (K₄ is small enough for near-term hardware) could be stated in one paragraph.

---

## 5. Cross-Agent Consensus: What Is Genuinely Novel

All 4 agents converge on a consistent assessment:

### What IS valid
- Graph Laplacian calculations for K₄ (eigenvalues, propagators) — standard graph theory, correctly applied
- Simplicial topology of K₄ (Betti numbers, Euler characteristic, chain complexes) — standard combinatorial topology
- Working Monte Carlo / HMC code (`stella_production_simulation.py`) — solid implementation
- The *observation* that simplex count ratios produce numbers resembling lattice QCD coefficients — an interesting pattern worth noting
- Honest self-criticism in later sections (§10.3.12.10.19–20)

### What is NOT supported
- "Feynman diagrams emerge intrinsically" from K₄ — this is the definition of a path integral on any graph, not an achievement
- Symanzik coefficients are "geometrically derived" — they are post-hoc identifications of simplex ratios with known values
- K₄ supports a continuum limit — it does not (4 fixed sites)
- Instanton physics on ∂S — requires 4D, not 2D
- Full SM gauge group from stella geometry — numerology (8 vertices ↔ 8 gluons)
- The Euler characteristic connection (r = 3/4) — based on incorrect propagator normalization

---

## 6. Consolidated Error Summary

### Critical Errors (15)

| # | Section | Error | Agent |
|---|---------|-------|-------|
| 1 | §10.3.4 | Triangle = vacuum diagram, not self-energy | 1 |
| 2 | §10.3.4/12.2 | Coupling power λ³ vs λ² inconsistency | 1 |
| 3 | §10.3.4/12.6 | Cubic/quartic coupling conflation | 1 |
| 4 | §10.3.6 | K₄ has no continuum limit | 1 |
| 5 | §10.3.12.4 | Dimensional mismatch ad hoc resolution | 1 |
| 6 | §10.3.12.6 | Arithmetic error: 0.047% not 0.15% (discrepancy is 57%, not 40%) | 2 |
| 7 | §10.3.12.2-6 | Discrete ∝ λ² vs continuum ∝ λ incompatible | 2 |
| 8 | §10.3.12.10.7 | c₁ = 1/12 conflates K₄ identity with hypercubic result | 2 |
| 9 | §10.3.12.10.9 | Propagator normalization 4× too large → r = 3/4 Euler connection invalid | 2 |
| 10 | §10.3.12.10.10 | c_SW = 2/3 is category error (combinatorics ≠ clover coefficient) | 2 |
| 11 | §10.3.12.10.15l | GW proof: false claim γ₅Sγ₅ = −S | 3 |
| 12 | §10.3.12.10.13b | Deficit angle: uses dihedral, should use face angle | 3 |
| 13 | §10.3.12.10.14j | Instantons on 2D surface: wrong dimension | 3 |
| 14 | §10.3.12.10.18p | Continuum extrapolation on K₄ using mock data | 4 |
| 15 | §10.3.12.10.18j | Improvement scaling test uses 1D periodic lattice, not K₄ | 4 |

### Serious/Major Errors (5)

| # | Section | Error | Agent |
|---|---------|-------|-------|
| 16 | §10.3.12.9.2 | False: "K₄ has no 4-cycles" (has 3) | 1 |
| 17 | §10.3.12.10.13g | "Gravity-matter duality" is tautology (a/b × b/a = 1) | 3 |
| 18 | §10.3.12.10.14i | H¹ dimension counting garbled | 3 |
| 19 | §10.3.12.10.15g | Wilson-Dirac matrix diagonal uncorrected (−9/2 should be −9/4) | 3 |
| 20 | §10.3.12.10.16e | "Fermion doublers" undefined for K₄ | 4 |

### Moderate/Low Errors (4)

| # | Section | Error | Agent |
|---|---------|-------|-------|
| 21 | §10.3.7 | Mass parameter unit confusion | 1 |
| 22 | §10.3.1 | Edge count: "12 per tetrahedron" should be "6 per" | 1 |
| 23 | §10.3.12.10.18c | Plaquette test samples single links, not plaquettes | 4 |
| 24 | §10.3.12.10.16h | Regge 1/n_f ↔ 1/(8πG) asserted without derivation | 4 |

---

## 7. Recommendations

### Immediate Fixes Required

1. **Fix the arithmetic error** (E2.1): Correct the discrete one-loop result from 0.15% to 0.047%
2. **Fix the 4-cycle claim** (E1.6): K₄ has 3 Hamiltonian cycles, not 0
3. **Fix the deficit angle** (E3.2): Use face angle π/3, not dihedral arccos(1/3)
4. **Fix the GW proof** (E3.1): Use S² = I directly; remove false γ₅Sγ₅ = −S claim
5. **Fix the Wilson-Dirac matrix** (E3.4): Correct diagonal from −9/2 to −9/4
6. **Fix the edge count** (E1.8): "6 per tetrahedron, 12 total"
7. **Fix the propagator normalization** (E2.4): Include 1/n_v factor consistently
8. **Fix Monte Carlo scripts** (E4.2, E4.4): Replace misrepresented tests

### Structural Changes Required

9. **Remove instanton claims** (E3.3): Instantons require 4D gauge fields; ∂S is 2D
10. **Remove or relabel "gravity-matter duality"** (E3.5): Acknowledge as algebraic identity
11. **Harmonize honesty level**: Earlier sections (§10.3.12.10.16–18) should carry the same caveats as §10.3.12.10.19–20
12. **Reduce quantum computing section** to 1–2 paragraphs of honest assessment
13. **Clearly distinguish** numerology (observed patterns) from derivation (proven results)

### Framing Changes Required

14. **Remove "Feynman diagrams emerge"**: Replace with "path integral on K₄ generates closed-path sums analogous to loop diagrams"
15. **Remove "geometrically derived"** for Symanzik coefficients: Replace with "simplex count ratios that numerically coincide with known improvement coefficients"
16. **Add prominent caveat**: "K₄ is a 4-site toy model with no continuum limit. Results here are suggestive patterns, not proofs."
17. **Downgrade c₁, c₂, c_SW claims** from "DERIVED" to "CONJECTURED (numerical coincidence)"
18. **Downgrade r = 3/4 Euler connection** from "ESTABLISHED" to "INCORRECT (normalization error)"

### Status Assessment

**Current status:** 🔶 NOVEL — "Framework established, coefficient matching verified"

**Recommended status:** 🔸 PARTIAL — "Interesting toy-model calculations with mathematical errors requiring correction. Core claims (geometric derivation of improvement coefficients, emergence of Feynman diagrams) are not supported by calculations presented. Contains genuine mathematical content (graph theory, simplicial topology, working Monte Carlo code) that could form basis for future work if claims are appropriately scoped."

---

## 8. What Would Be Needed for Status Upgrade

To reach 🔶 NOVEL (all errors fixed, claims properly scoped):
1. Fix all 15 critical errors
2. Restructure document with honest framing throughout
3. Clearly separate established results (graph theory) from conjectures (coefficient identification)
4. Remove unsupported claims (instantons, SM gauge group, continuum limit on K₄)

To reach 🔶 NOVEL ✅ VERIFIED:
1. All of the above
2. Independent re-derivation of surviving claims
3. Lean 4 formalization of key results
4. 3-file restructuring (currently ~81K tokens)

---

*Report generated by 4 independent adversarial verification agents*
*Model: Claude Opus 4.6*
*Date: 2026-02-12*
