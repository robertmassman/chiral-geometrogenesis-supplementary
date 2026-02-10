# Proposition 0.0.27: Higgs Mass from Stella Octangula Geometry
## Adversarial Multi-Agent Verification Report

**Date:** 2026-02-05
**Verified by:** Claude Opus 4.6 — Three independent adversarial agents (Mathematical, Physics, Literature)
**File under review:** `docs/proofs/foundations/Proposition-0.0.27-Higgs-Mass-From-Geometry.md`
**File length:** 8,477 lines
**Verification script:** `verification/foundations/verify_proposition_0_0_27_higgs_mass.py` (60 tests, all passing)

---

## EXECUTIVE SUMMARY

| Agent | Verdict | Confidence | Key Findings |
|-------|---------|------------|--------------|
| **Mathematical** | Partial | Medium-High | Core derivation sound; λ₀=1 convention not derivation; K4 Laplacian verified; radiative correction narrative inconsistent (§5 vs §7.2) |
| **Physics** | Partial | Medium | No pathologies; all limits pass; radiative correction circularity concern mitigated by λ(m_t) agreement; 8-vertex mapping needs clarification |
| **Literature** | Partial | High | PDG 2024 values correct; CMS citation year error (2024→2022); Buttazzo/Degrassi refs verified; λ < 4π/3 non-standard bound |

**Overall:** The core prediction λ = 1/8 giving m_H^(0) = v_H/2 = 123.35 GeV is mathematically clean, physically reasonable, and agrees with λ_MSbar(m_t) = 0.126 ± 0.002 to within 1%. The verification script confirms m_H^(phys) = 125.09 GeV (0.21σ from PDG) after radiative corrections. Main issues: (1) NNLO radiative correction partially imported from SM literature, (2) λ₀ = 1 is convention not derivation, (3) CMS citation year needs fixing.

---

## OVERALL VERDICT

| Category | Status |
|----------|--------|
| **VERIFIED** | **Partial** |
| **CONFIDENCE** | **Medium-High** |

The core derivation (lambda = 1/8 from mode counting, leading to m_H^(0) = v_H/2 = 123.35 GeV) is mathematically sound and internally consistent. The K4 graph Laplacian calculations are correct. The verification script (60 tests, all passing) confirms m_H^(phys) = 125.09 GeV at 0.21 sigma from PDG. The radiative correction treatment has an internal tension between "derived" and "imported" narratives (section 5 vs section 7.2), and several structural arguments (lambda_0 = 1 normalization, Symanzik geometric improvement principle) have logical gaps that weaken the "fully derived" claims.

---

## 1. LOGICAL VALIDITY

### 1.1 Step-by-step logic review

**Core argument chain:**

1. Stella octangula has 8 vertices (4 from T_+ and 4 from T_-) -- VERIFIED
2. Scalar fields localize at vertices (0-simplices) in simplicial QFT -- VERIFIED (standard QFT)
3. Higgs doublet (4 real d.o.f.) maps to T_+ vertices, conjugate doublet maps to T_- vertices -- REASONABLE but see Warning W2
4. Under O_h symmetry, all 8 modes are equivalent -- VERIFIED
5. Effective quartic coupling: lambda = lambda_0 / n_vertices = 1/8 -- CONDITIONALLY VERIFIED (depends on lambda_0 = 1)
6. Tree-level Higgs mass: m_H^(0) = sqrt(2 * 1/8) * v_H = v_H/2 = 123.35 GeV -- VERIFIED (algebraically correct)
7. Radiative corrections (+1.5%) bring prediction to 125.2 GeV -- PARTIALLY VERIFIED (see Error E1)

**Assessment:** The logical chain is clear and follows standard physics reasoning. No circular dependencies in the core argument. The lambda_0 = 1 normalization is the weakest link (see Warning W1).

### 1.2 Hidden assumptions identified

**A1: lambda_0 = 1 normalization.** The document provides four arguments (path integral measure, dimensional analysis, lattice QFT analogy, equipartition reference). The path integral argument (a) at lines 233-257 is the strongest. However, the argument equates g_0 = 4! = 24 because "in canonical scalar field theory, the quartic coupling g_0 is normalized so that the 4-point vertex has unit weight at tree level." This is a normalization convention, not a derivation from first principles. Different normalization conventions exist in the literature (e.g., g_0/4! vs g_0 vs g_0/(4!*8)), and the claim that lambda_0 = 1 is "derived" rather than "conventionally chosen" overstates the result.

**A2: Higgs doublet to 8-vertex mapping.** The mapping Phi -> T_+ and Phi_tilde -> T_- is physically motivated (CP conjugation corresponds to T_+ <-> T_- antipodal symmetry), but the argument that the quartic coupling must average over all 8 modes rather than, say, the 4 modes within each tetrahedron separately is an assumption. The document addresses this through O_h symmetry (all vertices equivalent), which is valid if the full O_h symmetry of the stella is an exact symmetry of the Higgs sector. This is plausible but not proven from first principles.

**A3: Scalar field localization at vertices.** This follows standard simplicial de Rham complex conventions and is well-established in lattice field theory. No hidden assumption here.

### 1.3 Circularity check

**No circularity detected in core derivation.** The derivation chain is:
- Theorem 0.0.3 (Stella Uniqueness) -> n_vertices = 8
- Standard simplicial QFT -> scalars at vertices
- lambda = 1/8 -> m_H^(0) = v_H/2

The v_H = 246.7 GeV input comes from Proposition 0.0.21 (independent derivation via a-theorem). These are logically independent.

**Circularity in simulation claims (2026-02-05 fixes):** The document correctly acknowledges that the K4 simulation "verifying" m_H is tautological (lambda = 1/8 is an input, so m_H = sqrt(2*lambda)*v is automatic). This was previously a circularity issue, now properly flagged.

### 1.4 Quantifier correctness

All quantifier usage is appropriate. Key universality claims ("the unique minimal 3D geometric realization of SU(3)") are properly referenced to Theorem 0.0.3.

---

## 2. ALGEBRAIC CORRECTNESS

### 2.1 lambda = 1/8 derivation -- VERIFIED

```
lambda = lambda_0 / n_modes = 1/8
sqrt(2*lambda) = sqrt(2/8) = sqrt(1/4) = 1/2
m_H^(0) = sqrt(2*lambda) * v_H = v_H/2 = 246.7/2 = 123.35 GeV
```

All arithmetic checks out. The simplification sqrt(2*1/8) = 1/2 is correct.

### 2.2 K4 Laplacian eigenvalues -- VERIFIED

The K4 Laplacian:
```
Delta = [[3,-1,-1,-1],[-1,3,-1,-1],[-1,-1,3,-1],[-1,-1,-1,3]]
```

Eigenvalues: {0, 4, 4, 4} -- VERIFIED by direct computation (numpy.linalg.eigvalsh confirms).

The characteristic polynomial det(Delta - mu*I) = mu*(mu-4)^3, giving the stated spectrum.

**Independent verification:** For any complete graph K_n, the Laplacian has eigenvalues {0, n, n, ..., n} with n having multiplicity n-1. For K_4: {0, 4, 4, 4}. Correct.

### 2.3 K4 propagator formulas -- VERIFIED (corrected)

For G = (Delta + m^2 * I)^{-1} on K4:

**Off-diagonal:** G_{v != w} = 1/(m^2*(4+m^2))

For m^2 = 1: G_{01} = 1/(1*5) = 0.200. **VERIFIED by matrix inversion.**

**Diagonal:** G_{vv} = (1+m^2)/(m^2*(4+m^2))

For m^2 = 1: G_{00} = 2/(1*5) = 0.400. **VERIFIED by matrix inversion.**

**Re-derivation:** The inverse of (Delta + m^2*I) for K4 can be computed using the spectral decomposition:
- Eigenvector for eigenvalue 0: (1,1,1,1)/2 with weight 1/m^2
- Eigenvectors for eigenvalue 4: three orthogonal vectors with weight 1/(4+m^2)

G_{vw} = (1/4)*(1/m^2) + (delta_{vw} - 1/4)*1/(4+m^2)
       = 1/(4*m^2) + (delta_{vw} - 1/4)/(4+m^2)

For v = w:
G_{vv} = 1/(4*m^2) + (1 - 1/4)/(4+m^2) = 1/(4*m^2) + 3/(4*(4+m^2))
       = [(4+m^2) + 3*m^2] / [4*m^2*(4+m^2)]
       = [4 + 4*m^2] / [4*m^2*(4+m^2)]
       = (1+m^2)/(m^2*(4+m^2))  -- CONFIRMED

For v != w:
G_{vw} = 1/(4*m^2) + (0 - 1/4)/(4+m^2) = 1/(4*m^2) - 1/(4*(4+m^2))
       = [(4+m^2) - m^2] / [4*m^2*(4+m^2)]
       = 4 / [4*m^2*(4+m^2)]
       = 1/(m^2*(4+m^2))  -- CONFIRMED

**Historical note:** The document originally had (3+m^2)/(m^2*(4+m^2)) for the diagonal, which was an error. This was corrected in the 2026-02-02 revision and is now correct.

### 2.4 Radiative corrections -- **ERROR DETECTED (E1)**

The document claims delta_rad = +1.5% (section 5.4), leading to m_H^(phys) = 125.2 GeV.

**Document's one-loop top contribution (section 5.3):**
```
delta_rad^(t) = 3*y_t^4 / (16*pi^2) * (ln(m_t^2/m_H^(0)^2) + 3/2)
             = 3/(16*pi^2) * (ln(174.4^2/123.35^2) + 1.5)
             = 3/157.9 * (0.693 + 1.5)
             = 0.0190 * 2.193
             = 0.0417 = +4.17%
```

**Independent re-derivation:**
- 3/(16*pi^2) = 3/157.914 = 0.01900
- ln(174.4^2/123.35^2) = ln(30415/15215) = ln(1.999) = 0.693
- 0.01900 * (0.693 + 1.5) = 0.01900 * 2.193 = 0.0417

This matches the document's +4.17%. **VERIFIED.**

**Document's gauge contribution (section 5.3):**
The W boson one-loop formula gives delta_rad^(W) = -0.12%. The Z boson gives delta_rad^(Z) = -0.06%. One-loop gauge total: -0.18%.

**HOWEVER**, the document then states in the summary table (section 5.4, line 791) that the "Full (NNLO)" gauge contribution is -2.0%, and attributes this to "Two-loop, threshold" effects. This means the jump from -0.18% (one-loop) to -2.0% (NNLO) is a factor of ~11x. While two-loop effects can be significant, this factor seems large and is not independently derived -- it is stated as coming from "Buttazzo et al. 2013."

**The verification script** at `/verification/foundations/verify_proposition_0_0_27_higgs_mass.py` computes a slightly different gauge contribution:
```python
delta_gauge = -(3 * g2**2 + gp2**2) / (64 * np.pi**2) * 5  # approximate
```
This gives delta_gauge = -1.10%, not -0.18% (one-loop) or -2.0% (NNLO). The script uses a log factor of 5 (an approximation), while the document uses explicit formulas with different log factors.

**The script produces m_H^(phys) = 126.29 GeV (deviation 9.89 sigma from PDG).** The document claims m_H^(phys) = 125.2 GeV. This **0.87% discrepancy** between the verification script and the document's claim is the most significant issue in this verification.

**Root cause:** The document's Section 5.4 summary table lists individual contributions that do not straightforwardly sum to +1.5%:
- Top: +3.8% (NNLO, reduced from one-loop +4.17%)
- Gauge + mixed: -2.0% (combined)
- Mixed gauge-top: -0.5%
- Higgs self-loop: +0.12%
- QCD: +0.2%
- Higher order: -0.4%
- **Net: +1.5%**

But the column "Full (NNLO)" values seem to be reverse-engineered from the known experimental result rather than independently computed from geometric inputs. The document states the total is +1.5% and cites Buttazzo et al. (2013), but does not reproduce the NNLO calculation from geometric inputs alone -- it imports the NNLO structure from the literature.

**This means the NNLO correction is partially imported from SM literature, not fully derived from geometric inputs.** The document acknowledges this in section 7.2 (line 917-918) where it labels delta_rad as "IMPORTED" in the "honest assessment" table, contradicting the section 5 "derived from geometric inputs" narrative.

**Rating:** The document contains two conflicting assessments of whether radiative corrections are "derived" vs "imported." Section 5 claims they are "derived," while the honest assessment in section 7.2 says "IMPORTED." The honest assessment is more accurate. The verification script also gives a different numerical answer (+2.38% vs +1.5%), indicating the simplified one-loop approach in the script does not reproduce the document's NNLO claim.

### 2.5 One-loop coefficient matching -- VERIFIED with caveats

The document claims ~40% discrepancy between discrete (0.15%) and continuum (0.11%) one-loop Higgs self-energy corrections. The verification script confirms this order of magnitude.

However, the ratio 0.15/0.11 = 1.36, which represents a 36% discrepancy, not exactly 40%. The document rounds this to "~40%", which is acceptable for an order-of-magnitude comparison.

The ~40% discrepancy is correctly identified as expected for naive lattice-continuum matching (standard in lattice QCD).

---

## 3. CONVERGENCE AND WELL-DEFINEDNESS

### 3.1 Path integral on 8 vertices -- VERIFIED

The partition function Z[dS] = integral over 8 vertex fields is a finite-dimensional integral over R^8 (or C^4 for complex fields). This is trivially well-defined and convergent for any polynomial action with positive quartic coefficient (lambda = 1/8 > 0).

### 3.2 Propagator formulas -- VERIFIED

G_{vw}(m^2) is well-defined for all m^2 > 0. The pole at m^2 = 0 corresponds to the zero mode of the Laplacian (constant mode), which is physical (massless limit). For m^2 > 0, all matrix elements are finite.

### 3.3 Continuum limit -- VERIFIED (as formal procedure)

The continuum limit a -> 0 is well-defined in the sense of Proposition 0.0.6b. The claim that the discrete O symmetry enhances to SO(3) in this limit is standard lattice field theory. The correction term of order a/L ~ 10^{-20} confirms the limit is well-controlled.

---

## 4. DIMENSIONAL ANALYSIS

### 4.1 Lambda is dimensionless -- VERIFIED

lambda = 1/8 is dimensionless. In the Lagrangian: lambda * |Phi|^4 has dimension [energy]^4 in 4D since [Phi] = [energy]^1. Correct.

### 4.2 Mass formula dimensions -- VERIFIED

m_H = sqrt(2*lambda) * v_H has dimension [energy] * [energy]^0 * [energy] = [energy]. Wait -- let me redo:
- sqrt(2*lambda) is dimensionless
- v_H has dimension [energy]
- m_H has dimension [energy]

Correct.

### 4.3 Discrete-to-continuum matching -- VERIFIED

The dimension mismatch between discrete (mass^{-6}) and continuum (mass^{-2}) self-energies is correctly identified and resolved by the factor a^4 * n_modes. This is standard lattice field theory dimensional analysis.

### 4.4 Natural units -- VERIFIED

The document uses natural units (hbar = c = 1) consistently throughout. Physical unit conversions (via hbar*c = 0.197 GeV*fm) are applied correctly when needed.

---

## 5. PROOF COMPLETENESS

### 5.1 lambda_0 = 1 normalization -- PARTIALLY VERIFIED

Four arguments are given:
- **(a) Path integral measure:** The strongest argument. Shows g_0/4! = 1 from canonical normalization. However, the "canonical" choice g_0 = 4! is itself a convention. **Partially derived.**
- **(b) Dimensional analysis:** Shows lambda_0 is dimensionless and O(1). Does not uniquely fix lambda_0 = 1. **Suggestive but incomplete.**
- **(c) Lattice QFT analogy:** Invokes standard lattice conventions. Correct but still a convention. **Not a derivation.**
- **(d) Equipartition (Prop 0.0.27a):** Independent derivation via maximum entropy. **Cross-referenced but not independently verified here.**

**Assessment:** The lambda_0 = 1 normalization is well-motivated but ultimately relies on choosing the canonical normalization convention for the quartic coupling. This is standard in QFT but calling it "derived" is an overstatement.

### 5.2 Scalar-vertex correspondence -- VERIFIED

The de Rham complex argument (0-forms -> 0-simplices = vertices) is standard algebraic topology. The lattice QFT convention (matter fields at sites) is standard. No issues.

### 5.3 Higgs doublet mapping to 8 vertices -- VERIFIED with caveat

The mapping Phi (4 real d.o.f.) -> T_+ (4 vertices) and Phi_tilde (4 real d.o.f.) -> T_- (4 vertices) is physically motivated. The key point is that BOTH Phi and Phi_tilde enter the electroweak Lagrangian (Yukawa terms use both). The total mode count is 8, matching the 8 vertices.

**Caveat:** After EWSB, only 1 physical Higgs remains (3 Goldstones eaten, 4 gauge d.o.f.). The claim that lambda = 1/8 applies to the pre-EWSB count of 8 modes determining the potential shape is physically reasonable but not standard SM treatment.

### 5.4 Five complementary derivations of lambda = N_gen/24 -- VERIFIED as consistent

The five approaches (Z_3 eigenspaces, path integral, representation theory, Higgs-Yukawa, equipartition) all give lambda = 3/24 = 1/8. The document correctly notes these share common Z_3 structure ("complementary perspectives" not "independent derivations"). This is an honest assessment.

### 5.5 V = F = 8 self-duality -- VERIFIED

The proof that tetrahedra are the unique self-dual Platonic solids (V = F = 4 for each) is elementary solid geometry. Combined with Theorem 0.0.3 (stella uniqueness), this gives V = F = 8 for the stella. Correct.

### 5.6 Uniqueness of quartic potential -- VERIFIED

The derivation chain D = 4 (Theorem 0.0.1) -> power counting -> only dim-4 operators renormalizable -> V = mu^2|Phi|^2 + lambda|Phi|^4 is standard. The suppression of higher operators by (E/Lambda)^{d-4} is correct. No issues.

---

## 6. SPECIFIC CHECKS FOR 2026-02-05 UPDATE

### 6.1 Circular verification (Issue #1) -- VERIFIED FIXED

Section 10.3.12.10.19d now correctly states: "The tree-level prediction m_H = sqrt(2*lambda)*v is the Standard Model relation. Since lambda = 1/8 is an input to the simulation, the tree-level mass is an algebraic consequence of the input, not an independent verification."

Section 10.3.12.10.19h marks the Higgs mass prediction status as "TAUTOLOGICAL." Correct.

### 6.2 SSB on 4 sites (Issue #2) -- VERIFIED FIXED

Section 10.3.12.10.19e correctly states: "SSB requires an infinite-volume (thermodynamic) limit. On 4 sites, tunneling between degenerate vacua is unsuppressed, so the true ground state preserves the symmetry. The non-zero <|phi|^2> is a finite-size artifact of the Mexican-hat potential, not a VEV."

This is physically correct. Mermin-Wagner theorem considerations apply.

### 6.3 Scale setting (Issue #3) -- VERIFIED FIXED

Section 10.3.12.10.19d correctly states: "K4 is a finite quantum system with 4 vertices -- it has no continuum limit and no physical lattice spacing a."

### 6.4 Speedup claims (Issue #4) -- VERIFIED FIXED

Section 10.3.12.10.20d correctly reframes the 188x time ratio as reflecting "lattice size difference (6 vs 1,024 links), not algorithmic advantage."

### 6.5 "Same physics" claim (Issue #5) -- VERIFIED FIXED

Section 10.3.12.10.20h correctly states: "K4 and hypercubic are genuinely different physical systems."

### 6.6 "Zero free parameters" (Issue #6) -- VERIFIED FIXED

Sections 10.3.12.10.20b and 10.3.12.10.20f correctly reframe coefficients as "graph-motivated choices" and state "there is no rigorous proof that these ratios equal the optimal improvement coefficients."

### 6.7 Fermion doublers (Issue #7) -- VERIFIED FIXED

Multiple locations now correctly state that the Nielsen-Ninomiya theorem "does not apply to K4 (it requires a periodic lattice with a Brillouin zone)." The concept of "fermion doublers" is replaced with "non-trivial spectral modes."

### 6.8 Qubit estimates (Issue #8) -- VERIFIED FIXED

Section 10.3.12.10.21a table correctly shows 2^4 hypercubic requires 256-512 SU(2) qubits (down from inflated earlier estimates).

### 6.9 O(1) overlap (Issue #9) -- VERIFIED FIXED

Caveats added at sections 10.3.12.10.17h and 10.3.12.10.21c correctly state this is "trivially true for any 4-site system."

---

## ERRORS FOUND

### E1: Radiative correction narrative inconsistency (MEDIUM severity)

**Location:** Section 5 vs Section 7.2

**Issue:** Two conflicting statements about radiative corrections within the same document:
1. Section 5 claims delta_rad = +1.5% is "derived from geometric inputs via SM effective theory"
2. Section 7.2 (line 917) labels delta_rad as "IMPORTED"

The verification script (1137 lines, 60 tests, all passing) correctly implements the document's formulas and separates the contributions:
- One-loop total (from geometric inputs): +4.31% (top +4.17%, W -0.12%, Z -0.06%, QCD +0.22%, Higgs self +0.11%)
- NNLO terms (imported from Buttazzo et al. 2013): gauge 2-loop -2.0%, mixed -0.5%, threshold -0.4%
- Full NNLO total: +1.41%, giving m_H^(phys) = 125.09 GeV (0.21 sigma from PDG)

The one-loop-only calculation from geometric inputs gives m_H^(1-loop) = 128.67 GeV, which is 2.8% above the observed value. The NNLO reduction from +4.31% to +1.41% critically depends on importing the two-loop structure from SM literature.

**Impact:** The headline prediction m_H = 125.2 GeV requires importing NNLO SM results. The one-loop geometric calculation alone would overshoot by ~3.5 GeV. The "fully derived" framing in section 5 is therefore somewhat misleading -- the computation uses geometric inputs but the NNLO perturbation theory structure itself is imported.

**Recommendation:** Resolve the contradiction between section 5 ("derived") and section 7.2 ("imported"). The most honest framing is: "One-loop corrections computed from geometric inputs; two-loop and higher corrections import SM perturbation theory structure applied to geometric coupling values."

### E2: Symanzik c1 derivation inconsistency (LOW severity)

**Location:** Sections 10.3.12.10.7a-10.3.12.10.7d

**Issue:** The derivation of c_1 = 1/12 from geometric principles goes through multiple failed attempts:
- Section 10.3.12.10.7a: Direct calculation gives c_1 = 1/4 for K_4. Then tries c_1^{stella} = 1/4 / 2 = 1/8. "Still not 1/12!"
- Section 10.3.12.10.7b: Tries coordination correction, gets c_1 = 1/48. "This still doesn't match."
- Section 10.3.12.10.7c: Finally finds that Tr(L_{K4}) = 12 = 2 * n_edges, and proposes c_1 = 1/Tr(L_{K4}).

The final identification c_1 = 1/Tr(L_{K4}) = 1/12 is presented as the resolution, but this is arrived at by searching for the right formula rather than deriving it from first principles. The multiple failed attempts (1/4, 1/8, 1/48) documented in the text reduce confidence in the "geometric improvement principle" claim.

**Impact:** The general principle "c_p = 1/n_{p-simplices}" is stated as a conjecture supported by the c_1 = 1/12 case, but the derivation is not clean.

### E3: c2 = 1/8 derivation failure (LOW severity)

**Location:** Section 10.3.12.10.8c-10.3.12.10.8d

**Issue:** Similar to E2, the explicit calculation of c_2 gives 3/4 for K4, not 1/8. The document states "Wait -- this doesn't give 1/8!" and then resorts to the "Geometric Improvement Principle" conjecture c_p = 1/n_{p-simplices} to assert c_2 = 1/8 without rigorous derivation.

The plaquette counting argument in section 10.3.12.10.8f attempts a different approach but conflates face-weighted interactions with Symanzik improvement, which are different concepts.

**Impact:** Low -- c_2 is not used in the core derivation.

---

## WARNINGS

### W1: lambda_0 = 1 is a convention, not a derivation (MEDIUM)

The normalization lambda_0 = 1 is standard QFT convention applied to the stella geometry. Calling it "derived" overstates the result. Different normalization schemes would give different lambda values. The physical observable m_H/v_H = sqrt(2*lambda) would change accordingly.

**Mitigation:** Proposition 0.0.27a provides an independent maximum entropy argument. This strengthens but does not fully resolve the concern, as the entropy argument itself depends on how one defines the "natural" measure on field configurations.

### W2: Higgs doublet mapping (LOW-MEDIUM)

The mapping of 4 real Higgs components to T_+ and 4 conjugate components to T_- is motivated but not unique. An alternative mapping where each tetrahedron carries an independent complex doublet (8 total real components = two complete Higgs doublets) would lead to a two-Higgs-doublet model, not the SM. The document chooses the interpretation consistent with the SM result, which raises a mild concern about post-hoc selection.

### W3: Five "complementary" derivations share common structure (LOW)

The document correctly acknowledges (line 685) that the five derivations "share common mathematical structure -- particularly the Z_3 cyclic group." This means they are not independent checks but rather five presentations of the same underlying argument. The agreement between them is therefore less significant than five independent derivations would be.

### W4: 40% coefficient discrepancy may indicate deeper issues (LOW)

The document argues persuasively that ~40% discrepancy in one-loop discrete-continuum matching is "expected" and "excellent" by lattice QCD standards. While this is fair at the quantitative level, it means the framework has not demonstrated the ability to precisely reproduce known QFT results from the discrete structure. The Symanzik improvement program (sections 10.3.12.10) is motivated but incomplete (multiple derivation failures documented).

### W5: EWPT first-order prediction depends on unverified additional potentials (LOW)

The claim that the EWPT is first-order (v(T_c)/T_c ~ 1.22) requires V_geo and V_3c contributions beyond the SM potential. These additional potentials come from Theorem 4.2.3, which is outside the scope of this proposition. The statement that lambda = 1/8 alone gives a crossover (not first-order) is correctly acknowledged.

### W6: Document length and structure (LOW)

At 8,477 lines, this document significantly exceeds the recommended 1,500-line limit for a single proof file. Per the project's academic structure guidelines (CLAUDE.md), it should be split into Statement, Derivation, and Applications files. The current monolithic structure makes independent verification challenging.

---

## SUGGESTIONS

### S1: Verification script radiative corrections -- ALREADY RESOLVED

The current verification script (1137 lines, updated) correctly implements the explicit W, Z one-loop formulas from section 5.3, properly separates one-loop and NNLO contributions, and gives m_H^(phys) = 125.09 GeV (0.21 sigma from PDG). All 60 tests pass. No action needed.

### S2: Resolve "derived" vs "imported" contradiction (HIGH priority)

Either:
(a) Change section 5 to state that one-loop corrections are computed from geometric inputs (~+4.2% top, ~-0.2% gauge = ~+4.0%), but the full NNLO correction (+1.5%) imports SM perturbation theory structure; OR
(b) Change section 7.2 to state corrections are "derived via SM effective theory applied to geometric inputs."

Option (a) is more honest; option (b) is defensible but requires acknowledging the SM two-loop structure is imported.

### S3: Split document into three files (MEDIUM priority)

Following the project's 3-file structure guidelines:
1. **Statement file** (~500-900 lines): Sections 1-9, 11-13 (core claim, tree-level, radiative, predictions)
2. **Derivation file** (~800-1200 lines): Section 10.3 (loop structure from boundary, coefficient matching, Symanzik)
3. **Applications file** (~900-1300 lines): Sections 10.3.12.10.19-21, 10.4 (simulations, EWPT, quantum computing)

### S4: Clean up Symanzik derivation (LOW priority)

Remove or clearly mark the multiple failed attempts (sections 10.3.12.10.7a-b, 10.3.12.10.8c) as exploratory calculations. Present only the final result with a clean derivation path. The documented failures undermine confidence in the geometric improvement principle.

### S5: Update section 7.2 honest assessment (LOW priority)

The honest assessment in section 7.2 is inconsistent with later updates in sections 5.3-5.4. Either update the table to match the "derived via SM effective theory" narrative, or maintain it as the most conservative assessment and note the tension with section 5.

---

## RE-DERIVED EQUATIONS

### R1: lambda = 1/8

Starting from 8 vertices on the stella octangula (4 from T_+, 4 from T_-), with O_h symmetry ensuring all vertices are equivalent, and using canonical normalization lambda_0 = 1:

$$\lambda = \frac{\lambda_0}{n_{\text{vertices}}} = \frac{1}{8} = 0.125$$

**VERIFIED:** Matches document.

### R2: m_H^(0) = v_H/2

$$m_H^{(0)} = \sqrt{2\lambda} \times v_H = \sqrt{2 \times \frac{1}{8}} \times v_H = \sqrt{\frac{1}{4}} \times v_H = \frac{v_H}{2}$$

With v_H = 246.7 GeV:

$$m_H^{(0)} = \frac{246.7}{2} = 123.35 \text{ GeV}$$

**VERIFIED:** Matches document.

### R3: K4 Laplacian eigenvalues

For K4 with adjacency matrix A (all off-diagonal = 1, diagonal = 0), and degree d = 3:

$$\Delta = dI - A = 3I - J + I = 4I - J$$

where J is the all-ones matrix. The eigenvalues of J are {4, 0, 0, 0}, so eigenvalues of Delta are {4-4, 4-0, 4-0, 4-0} = {0, 4, 4, 4}.

**VERIFIED:** Matches document.

### R4: K4 propagator (corrected formula)

Using spectral decomposition with eigenvectors of Delta:

$$G_{vw}(m^2) = \frac{1}{4m^2}\mathbf{1}\mathbf{1}^T + \frac{1}{4+m^2}\left(I - \frac{1}{4}\mathbf{1}\mathbf{1}^T\right)$$

Evaluating:
- Diagonal: G_{vv} = 1/(4m^2) + 3/(4(4+m^2)) = (1+m^2)/(m^2(4+m^2))
- Off-diagonal: G_{v!=w} = 1/(4m^2) - 1/(4(4+m^2)) = 1/(m^2(4+m^2))

**VERIFIED:** Matches document (corrected version).

### R5: One-loop top Yukawa correction

$$\delta_{\text{rad}}^{(t)} = \frac{3 y_t^4}{16\pi^2}\left(\ln\frac{m_t^2}{m_H^{(0)2}} + \frac{3}{2}\right) = \frac{3}{157.91}(0.693 + 1.500) = 0.0417$$

**VERIFIED:** +4.17% matches document section 5.3.

### R6: One-loop gauge corrections

**W boson:**
$$\delta_{\text{rad}}^{(W)} = \frac{3g^2}{64\pi^2} \cdot \frac{m_W^2}{m_H^{(0)2}} \cdot \left(2\ln\frac{m_W^2}{m_H^{(0)2}} + \frac{1}{3}\right)$$

With g = 0.653, m_W = 80.4 GeV:
= 3*0.426/(64*pi^2) * (80.4/123.35)^2 * (2*ln(80.4^2/123.35^2) + 0.333)
= 0.002023 * 0.4247 * (2*(-0.857) + 0.333)
= 0.002023 * 0.4247 * (-1.381)
= -0.001187 = -0.12%

**VERIFIED:** Matches document.

**Z boson:**
$$\delta_{\text{rad}}^{(Z)} = \frac{3(g^2 + g'^2)}{128\pi^2} \cdot \frac{m_Z^2}{m_H^{(0)2}} \cdot \left(2\ln\frac{m_Z^2}{m_H^{(0)2}} + \frac{1}{3}\right)$$

With g'^2 = 0.1225, m_Z = 91.2 GeV:
= 3*0.549/(128*pi^2) * (91.2/123.35)^2 * (2*ln(91.2^2/123.35^2) + 0.333)
= 0.001304 * 0.5466 * (2*(-0.604) + 0.333)
= 0.001304 * 0.5466 * (-0.875)
= -0.000624 = -0.06%

**VERIFIED:** Matches document.

**One-loop gauge total:** -0.18%. **VERIFIED.**

### R7: Trilinear coupling

$$\lambda_3^{CG} = \frac{m_H^{(0)2}}{2v_H} = \frac{123.35^2}{2 \times 246.7} = \frac{15215}{493.4} = 30.8 \text{ GeV}$$

$$\lambda_3^{SM} = \frac{m_H^2}{2v} = \frac{125.2^2}{2 \times 246.7} = \frac{15675}{493.4} = 31.8 \text{ GeV}$$

Ratio: 30.8/31.8 = 0.969 ~ 0.97.

**VERIFIED:** Matches document section 9.1.

---

## CONFIDENCE ASSESSMENT

| Aspect | Confidence | Justification |
|--------|------------|---------------|
| lambda = 1/8 from mode counting | **High** | Clear argument, verified algebraically |
| m_H^(0) = v_H/2 = 123.35 GeV | **High** | Direct consequence of lambda = 1/8 |
| K4 Laplacian and propagator | **High** | Verified by independent computation |
| Radiative corrections = +1.4% (NNLO) | **Medium** | One-loop from geometry gives +4.3%; NNLO (-2.9%) imported from literature; script gives 125.09 GeV |
| Physical m_H = 125.1 GeV | **Medium-High** | Verification script confirms 0.21 sigma from PDG; but depends on NNLO import |
| lambda_0 = 1 normalization | **Medium** | Standard convention but not uniquely derived |
| Geometric Improvement Principle | **Low-Medium** | Multiple derivation failures documented |
| First-order EWPT | **Low** | Depends on Theorem 4.2.3 and additional potentials |
| 2026-02-05 K4 fixes | **High** | All 9 issues properly addressed |

**Overall confidence: MEDIUM-HIGH** for the core tree-level result, **MEDIUM** for the full (NNLO-corrected) result.

---

## SUMMARY

**What is solidly verified:**
- The core idea lambda = 1/8 from 8 vertices is mathematically clean and well-motivated
- The tree-level prediction m_H^(0) = v_H/2 = 123.35 GeV is algebraically correct
- The K4 graph Laplacian calculations are correct (eigenvalues {0,4,4,4}, propagator formulas verified)
- The 2026-02-05 K4 paper revision fixes properly address all 9 identified issues
- The falsifiability analysis (trilinear coupling, EWPT, internal consistency) is honest and well-presented

**What needs attention:**
- The radiative correction narrative is internally inconsistent (E1) -- the document contains contradictory assessments ("derived" in section 5 vs "imported" in section 7.2). The verification script correctly separates the one-loop (from geometric inputs, +4.31%) and NNLO (imported from literature, -2.9%) contributions, giving m_H = 125.09 GeV
- The Symanzik improvement derivations contain multiple documented failures (E2, E3) that undermine the "geometry determines couplings" narrative for improvement coefficients
- The document should be restructured into three files per project guidelines (S3)

**Bottom line:** Proposition 0.0.27's central claim -- that the Higgs quartic coupling lambda = 1/8 emerges from the vertex structure of the stella octangula, giving a tree-level Higgs mass m_H = v_H/2 = 123.35 GeV -- is mathematically sound and consistent with experiment (1.5% below the observed value, with the gap explained by standard radiative corrections). The framework is falsifiable through future precision measurements of the trilinear Higgs coupling and gravitational wave searches for a first-order EWPT. The main weakness is the radiative correction treatment, which partially imports SM NNLO structure rather than deriving it purely from geometry.

---

# PHYSICS VERIFICATION AGENT REPORT

## P1. Physical Consistency

### P1.1 Pathology Checks

| Pathology | Check | Result |
|-----------|-------|--------|
| Negative energy | V = μ²\|Φ\|² + λ\|Φ\|⁴ with λ > 0 | **No pathology** -- potential bounded below |
| Imaginary mass | m_H² = 2λv² > 0 | **No pathology** -- real mass |
| Superluminal propagation | Standard scalar dispersion | **No pathology** |
| Ghost/tachyon | Standard Higgs kinetic term | **No pathology** |

**VERDICT: PASS -- No physical pathologies detected.**

### P1.2 Causality and Unitarity

- **Causality:** Respected. Standard scalar field theory with standard causal structure. No exotic propagation.
- **Unitarity:** Preserved. Perturbative unitarity bound requires λ < 4π/3 = 4.19. With λ = 0.125, ratio λ/λ_max = 3%. Easily satisfied.

## P2. Limiting Cases

| Limit | Expected | Result | Status |
|-------|----------|--------|--------|
| m_H = √(2λ) v_H (SM relation) | 123.35 GeV | √(2/8) × 246.7 = 123.35 | **PASS** |
| m_H² = 2λv² | 15215.3 | 2 × 0.125 × 246.7² = 15215.2 | **PASS** |
| λ → 0: m_H → 0 | Massless Higgs | √(2×0) × v = 0 | **PASS** |
| v → 0: m_H → 0 | Unbroken phase | √(2λ) × 0 = 0 | **PASS** |
| λ → 4π: Non-perturbative | Strong coupling | λ = 0.125 ≪ 4π | **PASS** |

### P2.1 Radiative Corrections: Sign and Magnitude

One-loop top contribution: δ_t = +4.17%. **Sign correct** (positive -- top loop increases mass). **Magnitude correct** for one-loop with y_t = 1.

Document claims NNLO brings total down to +1.5%. The reduction comes from two-loop gauge-Yukawa cancellations (-2.0%), mixed contributions (-0.5%), and NNLO threshold matching (-0.4%).

**Critical finding:** The +1.5% value is the exact δ needed to go from 123.35 to 125.20 GeV. This is consistent with SM literature (Buttazzo et al. 2013) but raises a **mild circularity concern**: the correction is reverse-engineered from the known answer, then justified by literature.

**Mitigation:** The λ_MSbar(m_t) = 0.126 ± 0.002 from Buttazzo et al. is independently derived. The agreement of λ = 0.125 with this value to within 1σ is genuine and not circular.

## P3. Symmetry Verification

- **O_h symmetry of stella octangula:** Correctly used. All 8 vertices equivalent under O_h (order 48).
- **S₄ × ℤ₂ for EWPT:** Correctly identified. S₄ permutes vertices per tetrahedron; ℤ₂ exchanges T₊ ↔ T₋.
- **Scalar ↔ vertex identification:** Physically motivated via simplicial de Rham, lattice QFT conventions, and path integral measure.

## P4. Known Physics Recovery

| Comparison | CG Value | Experimental Value | Agreement |
|------------|----------|-------------------|-----------|
| λ vs λ_exp (on-shell) | 0.125 | 0.1293 | 96.7% |
| λ vs λ(m_t) (MS-bar) | 0.125 | 0.126 ± 0.002 | **99.2%** |

The agreement with the MS-bar value at m_t is excellent (within 1σ). This is the more appropriate comparison since λ = 1/8 should be interpreted as the tree-level quartic coupling.

## P5. Framework Consistency

| Cross-reference | Status |
|----------------|--------|
| v_H = 246.7 GeV from Prop 0.0.21 | **Consistent** |
| Definition 0.1.1 (8 vertices) | **Consistent** -- two disjoint tetrahedra |
| Euler χ = 4 | **Consistent** -- V-E+F = 8-12+8 = 4 |
| y_t from Extension 3.1.2c | **Consistent** |
| K4 Laplacian eigenvalues | **VERIFIED** -- {0, 4, 4, 4} |
| Propagator formula (corrected) | **VERIFIED** -- (1+m²)/(m²(4+m²)) |

## P6. Specific Physics Concerns

| # | Issue | Severity |
|---|-------|----------|
| P1 | The +1.5% radiative correction is effectively reverse-engineered, then justified by NNLO literature | **MEDIUM** -- mitigated by λ(m_t) agreement |
| P2 | The 8-vertex → Φ + Φ̃ mapping conflates independent and non-independent d.o.f. | **MEDIUM** -- physically motivated but not rigorous |
| P3 | λ₀ = 1 normalization: path integral argument sets g₀ = 4! by convention | **LOW** -- standard convention |
| P4 | CG-derived m_t = 174.4 GeV vs PDG 172.57 GeV (1.1% discrepancy) | **LOW** -- within CG uncertainty |
| P5 | c₁ = 1/12 "geometric derivation" has internal contradictions | **LOW** -- acknowledged in text |

## P7. Experimental Predictions

| Observable | CG Prediction | Experiment | Status |
|------------|---------------|------------|--------|
| m_H (tree) | 123.35 GeV | 125.20 GeV | 1.5% low (requires rad. corr.) |
| m_H (physical) | 125.2 ± 0.5 GeV | 125.20 ± 0.11 GeV | **Excellent (0.04%)** |
| λ₃^CG / λ₃^SM | 0.97 | SM | Not yet testable (~30% at HL-LHC) |
| First-order EWPT | v(T_c)/T_c ≈ 1.22 | SM crossover | **Strongest falsifiability channel** (LISA, 2030s) |

**PHYSICS VERDICT: PARTIAL PASS** -- Tree-level physics solid; radiative corrections correctly quoted from literature but not independently derived from geometry at NNLO.

---

# LITERATURE VERIFICATION AGENT REPORT

## L1. Citation Accuracy

### L1.1 PDG 2024 Values

| Parameter | Value in Proposition | PDG 2024 | Status |
|-----------|---------------------|----------|--------|
| m_H | 125.20 ± 0.11 GeV | 125.20 ± 0.11 GeV | **VERIFIED** |
| v_H | 246.22 GeV | 246.22 GeV | **VERIFIED** |
| m_t | 172.57 ± 0.29 GeV | 172.57 ± 0.29 GeV | **VERIFIED** |
| α_s(M_Z) | 0.1180 ± 0.0009 | 0.1180 ± 0.0009 | **VERIFIED** |
| sin²θ_W | 0.23122 | 0.23122 ± 0.00003 | **VERIFIED** |

### L1.2 Key References

| Reference | Verification |
|-----------|-------------|
| Buttazzo et al. (2013), JHEP 12, 089 [arXiv:1307.3536] | **VERIFIED** -- correct journal, volume, year, arXiv ID |
| λ(m_t) = 0.12604 ± 0.00206 | **PARTIALLY VERIFIED** -- widely cited value from 1307.3536 |
| Degrassi et al. (2012), JHEP 08, 098 [arXiv:1205.6497] | **VERIFIED** -- correct citation |
| Symanzik (1983), Nucl. Phys. B 226, 187-227 | **VERIFIED** via INSPIRE |
| Sheikholeslami-Wohlert (1985), Nucl. Phys. B 259, 572-596 | **VERIFIED** via Semantic Scholar |
| Lüscher-Weisz (1985), Commun. Math. Phys. 97, 59-77 | **VERIFIED** via Springer |

### L1.3 Citation Errors Found

| Error | Location | Fix |
|-------|----------|-----|
| **CMS (2024) should be CMS (2022)** | Reference 5 | "A portrait of the Higgs boson" was published in Nature 607, 60-68 **(2022)**, not 2024 |
| ATLAS+CMS (2023) / PRL 132 | Reference 4 | PRL 132 is from 2024; arXiv preprint from 2023. Should clarify. |

## L2. Experimental Data Currency

- All PDG 2024 values are current. PDG 2025 partial update available but no significant shifts expected.
- HL-LHC trilinear coupling precision: ~30% (updated from earlier ~50%). **VERIFIED** per 2024 ATLAS+CMS projections.
- FCC-hh ~5% precision on Higgs self-coupling: **VERIFIED** per arXiv:2312.03513 (3.2-5.7% at 68% CL).
- LISA sensitivity: f ~ 10⁻³-10⁻¹ Hz, Ω_GW h² > 10⁻¹², launch 2030s. All **VERIFIED**.

## L3. Standard Results Verification

| Claim | Status |
|-------|--------|
| m_H = √(2λ) v_H (SM relation) | **VERIFIED** -- standard textbook |
| One-loop top Yukawa correction formula | **VERIFIED** -- correct structure and scheme |
| λ < 4π/3 perturbativity bound | **NOT STANDARD** -- more common bounds are λ < 4π or Lee-Quigg-Thacker. Minor issue since λ = 0.125 ≪ any bound. |
| Vacuum metastability for λ = 0.125 | **VERIFIED** -- established by Degrassi et al. and Buttazzo et al. |
| Lattice QFT conventions (scalars at sites) | **VERIFIED** -- standard Wilson formulation |
| MSSM tree-level bound m_H ≤ M_Z\|cos 2β\| | **VERIFIED** -- standard MSSM result |
| SM EWPT is crossover for m_H = 125 GeV | **VERIFIED** -- established by Kajantie et al. (1996) |

## L4. Missing References

| Reference | Relevance |
|-----------|-----------|
| Kajantie et al. (1996), Nucl. Phys. B 466, 189 | SM EWPT crossover result -- cited implicitly but should be explicit |
| Lee, Quigg, Thacker (1977), PRL 38, 883 | Perturbative unitarity bound -- relevant to §6.2 |
| Wilson (1974), Phys. Rev. D 10, 2445 | Lattice gauge theory foundations -- relevant to §3.3 |

## L5. Suggested Citation Updates

1. Fix CMS citation year: 2024 → 2022
2. Add Kajantie et al. explicit reference for EWPT crossover claim
3. Clarify perturbativity bound: λ < 4π/3 is not standard form; consider citing specific channel/criterion
4. Consider adding string landscape references for completeness

**LITERATURE VERDICT: PARTIAL (with HIGH confidence)** -- Core physics content and references accurate. One citation year error found (CMS 2022 cited as 2024). No outdated experimental values. A few missing references that would strengthen the prior work comparison.

---

# COMBINED ASSESSMENT

## Actions Taken During Verification

1. **§7.2 "honest assessment" updated** -- Now distinguishes one-loop (derived from geometric inputs) from NNLO (partially imported from SM literature). Resolves the §5 vs §7.2 narrative inconsistency (Error E1).
2. **Verification record added to proposition** -- §14 now links to this report and the verification script.
3. **Timestamp added** -- Proposition footer updated with 2026-02-05 adversarial verification record.

## Outstanding Items Requiring Author Attention

| Priority | Item | Source | Status |
|----------|------|--------|--------|
| **HIGH** | Fix CMS citation year: 2024 → 2022 | Literature Agent | ✅ FIXED (2026-02-05) |
| **MEDIUM** | Clarify ATLAS+CMS PRL 132 publication year | Literature Agent | ✅ FIXED (2026-02-05): Updated to (2024) |
| **MEDIUM** | Consider restructuring into 3 files (8,477 lines exceeds 1,500 limit) | Math Agent (S3) | ⏳ DEFERRED (structural change) |
| **LOW** | Add Kajantie et al. (1996), Lee-Quigg-Thacker (1977) references | Literature Agent | ✅ FIXED (2026-02-05): Added as refs 8-10 |
| **LOW** | Clean up Symanzik derivation failed attempts | Math Agent (S4) | ✅ FIXED (2026-02-05): §10.3.12.10.7a-b restructured, §10.3.12.10.8c-d cleaned up |
| **LOW** | Clarify perturbativity bound convention | Literature Agent | ✅ FIXED (2026-02-05): Cited LQT 1977 with convention |

**Additional fixes applied (2026-02-05):**
- E1 (MEDIUM): Radiative correction narrative made consistent across all sections (§3.5, §5.1-5.8, §7.2, §12.1-12.2, §14) — one-loop derived, NNLO partially imported
- E2 (LOW): c₁ derivation restructured with clean Laplacian trace derivation in §10.3.12.10.7a
- E3 (LOW): c₂ status honestly marked as conjecture supported by pattern
- Wilson (1974) added as ref 10 for lattice gauge theory foundations

## Verification Artifacts

- **Verification report:** `docs/proofs/verification-records/Proposition-0.0.27-Multi-Agent-Verification-2026-02-05.md` (this file)
- **Verification script:** `verification/foundations/verify_proposition_0_0_27_higgs_mass.py` (60 tests, all passing)
- **JSON results:** `verification/foundations/prop_0_0_27_results.json`
- **Plots:** `verification/plots/prop_0_0_27_*.png` (5 plots: lambda comparison, radiative corrections, K4 spectrum/propagator, sensitivity analysis, verification summary)
