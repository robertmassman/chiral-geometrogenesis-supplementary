# Proposition 0.0.XXe: Physics Verification Report

## Adversarial Physics Review — Continuum Limit of Self-Replicating Fields on dS

> **⚠️ CORRECTION NOTE (2026-03-13):** The "47% discrepancy" (SP-1) between PDE prediction (0.810) and discrete soup (~55%) discussed in this report was caused by a BFS Voronoi tiling bug, not a fundamental PDE-soup disagreement. Corrected runs show ~87% equilibrium density, reducing the discrepancy to ~8% (within mean-field accuracy). SP-1 is now resolved. See WORKPLAN Q13 and `stella_lang/RERUN_PLAN.md`.

**Date:** 2026-03-10
**Reviewer:** Independent Physics Verification Agent (Adversarial)
**File Reviewed:** `docs/proofs/foundations/Proposition-0.0.XXe-Continuum-Self-Replicating-Fields.md`
**Supporting Files Reviewed:**
- Phase 2: Z3 Potts Model Connection
- Phase 3: Reaction-Diffusion Formulation
- Phase 4: Continuum Fixed-Point Identification
- Phase 5: Soliton Classification
- Definition 0.1.1 (Stella Octangula Boundary Topology)
- Definition 0.1.2 (Three Color Fields)
- Theorem 0.2.1 (Total Field Superposition)

---

## VERDICT

- **VERIFIED:** Partial
- **CONFIDENCE:** Medium
- **Overall Assessment:** The proposition is internally consistent and intellectually honest about its limitations. The mathematical content (Fisher-KPP dynamics, fixed-point analysis, stability) is sound. The physical interpretations range from well-motivated structural analogies to speculative identifications. Several important physics issues are identified below that require attention.

---

## 1. PHYSICAL CONSISTENCY

### 1.1 Fisher-KPP on dS as a Pre-Geometric Model

**Assessment: REASONABLE WITH CAVEATS**

The Fisher-KPP equation is well-established for population dynamics with linear autocatalysis. Its application to a Z3 soup on dS is a legitimate coarse-graining. The derivation in Phase 3 (SS3.2) follows standard mean-field procedures. The key steps -- discrete Laplacian to Laplace-Beltrami convergence (Wardetzky et al. 2007), logistic growth from R + F -> 2R, mutation as linear death -- are all standard.

**Issue P-1 (Minor): Pre-geometric status unclear.** The proposition uses the Laplace-Beltrami operator on S^2, which requires a metric on the tetrahedron surfaces. This is not fully "pre-geometric" in the sense of Definition 0.1.1 SS3.3, which emphasizes that no bulk metric is needed. The PDE simulation uses explicit vertex coordinates in R^3. The proposition should clarify that the Fisher-KPP dynamics operate at the "computational scaffolding" level (Def 0.1.1 terminology), not at the purely combinatorial level.

**Location:** SS3.1, SS3.2 of main file; Phase 3 SS3.2.4.

### 1.2 Bilayer Coupling (50% T+/T- Cross-Talk)

**Assessment: PHYSICALLY MOTIVATED BUT NEEDS STRONGER JUSTIFICATION**

The 50% cross-tetrahedron interaction probability is attributed to Theorem 0.2.1 (Total Field Superposition). I verified that Thm 0.2.1 establishes the superposition chi_total = sum of three color fields, which naturally involves contributions from both tetrahedra. However, the precise "50%" figure appears to be a modeling choice in the soup simulation rather than a derived consequence of Thm 0.2.1.

**Issue P-2 (Moderate): The 50% coupling is not derived from first principles.** Theorem 0.2.1 establishes that fields on T+ and T- superpose, but the equal-weight (50/50) split between intra- and inter-tetrahedron interactions is a simulation parameter. In the bilayer Fisher-KPP equation (Claim 2), the coupling kappa/2 controls inter-layer equilibration. The specific value kappa = 1 (50% cross-talk) should be marked as a modeling assumption, not a theorem consequence.

**Location:** SS1.1 "Bilayer decomposition" definition; SS3.2 derivation; Phase 3 SS3.2.5.

### 1.3 Catalytic/Non-Catalytic Dichotomy -> Vacuum/Matter

**Assessment: WELL-MOTIVATED STRUCTURAL ANALOGY**

The identification is physically sensible:
- Vacuum as a self-replicating (catalytic) attractor that fills space via Fisher-KPP fronts is a compelling picture. The hair-trigger effect (Aronson & Weinberger 1978) on compact manifolds is correctly applied.
- Matter as topologically protected non-catalytic excitations classified by pi_3(SU(3)) = Z is standard Skyrme model physics.

The dichotomy cleanly explains why vacuum fills space (catalytic = self-replicating attractor) while particles are localized (non-catalytic = topological protection). This is one of the strongest conceptual contributions of the proposition.

**No issues identified.**

### 1.4 Replicator Density as Vacuum State

**Assessment: REASONABLE BUT WITH A GAP**

**Issue P-3 (Moderate): The replicator density rho lives in [0,1] (scalar), but the QCD vacuum is characterized by non-perturbative condensates in SU(3) gauge theory.** The identification rho* <-> QCD vacuum is at the level of a structural analogy (both are attractors of their respective dynamics). The proposition correctly acknowledges this in SS8.1: "The mapping between soup parameters and QCD observables is structural, not first-principles quantitative." However, the claim that "self-replication IS bootstrap self-consistency" (SS4.5, SS9) is stated more strongly than the evidence supports. The structural isomorphism between the three fixed-point equations (discrete R(S)=S, continuum F[rho*]=0, bootstrap Phi(T)=T) is suggestive but does not constitute a proof of physical equivalence.

**Location:** SS4.5 "Bootstrap identification"; SS9 Summary.

---

## 2. LIMITING CASES

### Limit Check Table

| Limit | Expected Behavior | Proposition's Treatment | Verified? | Issues |
|-------|-------------------|------------------------|-----------|--------|
| mu -> 0 | Pure Fisher-KPP, no mutation; rho* = k_eff/(k_eff + gamma) ~ 0.89 | SS4.1: rho* -> k_eff/(k_eff+gamma) | YES | None |
| mu -> mu_c | Error catastrophe; rho* -> 0 | SS5.1: rho* -> 0 at mu_eff = k_eff | YES | Transition sharpness not rigorously characterized |
| kappa -> 0 | Layers decouple; two independent Fisher-KPP systems | Implied in Phase 3 SS3.2.5 | YES (implicit) | Should be stated explicitly |
| D -> 0 | No spatial diffusion; purely local ODE dynamics | Not explicitly discussed | NOT CHECKED | See Issue L-1 |
| Large N (continuum) | Discrete -> PDE convergence | Phase 3 SS3.2.4, Phase 4 SS4.1 | PARTIAL | Convergence rate not established |
| mu_eff >> k_eff | rho* = 0 (disordered) | Follows from SS4.1 formula | YES | None |
| Flat space limit (R -> infinity) | Front speed -> 2*sqrt(D*k_eff) | Phase 3 SS3.4.3: measured 51% of flat value | YES | Curvature correction well-explained |

**Issue L-1 (Minor): D -> 0 limit not explicitly discussed.** When D = 0, the Fisher-KPP equation becomes a purely local ODE at each point, and the hair-trigger effect on compact manifolds no longer applies (disconnected local dynamics). The proposition should note that spatial coupling (D > 0) is essential for the global attractor property.

**Location:** SS4.4 "Hair trigger effect."

---

## 3. SYMMETRY VERIFICATION

### 3.1 Z3 Symmetry Preservation in Continuum Limit

**Assessment: CORRECTLY HANDLED**

The Z3 symmetry of the discrete soup (trit values {0,1,2}) maps to the Z3 Fourier order parameter psi = phi_0 + omega*phi_1 + omega^2*phi_2 in the continuum (Phase 3 SS3.1.2). The Fisher-KPP equation for rho (total replicator density) is Z3-invariant by construction -- it tracks the total density regardless of which Z3 family dominates. The Z3 symmetry breaking (one family dominates) is correctly identified as spontaneous.

**No issues identified.**

### 3.2 T+ <-> T- Exchange Symmetry

**Assessment: CORRECTLY PRESERVED**

The bilayer Fisher-KPP equation (Claim 2) is symmetric under T+ <-> T- exchange (rho+ <-> rho-). The coupling term kappa/2*(rho_mp - rho_pm) changes sign under exchange, which is correct for a diffusive coupling that equilibrates the two layers. The PDE simulation (Phase 3 SS3.4.3) confirms that both layers converge to the same rho* with a transient lag of ~300 epochs.

**No issues identified.**

### 3.3 Topological Classification by pi_3(SU(3)) = Z

**Assessment: CORRECT BUT WITH AN IMPORTANT CAVEAT**

The homotopy group pi_3(SU(3)) = Z is standard algebraic topology (correct). The identification of skyrmions as baryons via this winding number is standard Skyrme model physics.

**Issue S-1 (Moderate): The proposition conflates two different uses of pi_3.** In SS6.1 and the Claim 5 table, skyrmions are described as "field configurations on dS" classified by pi_3(SU(3)). However, Phase 5 SS5.1.2 correctly notes that skyrmions are solitons in 3D space (classified by pi_3), while solitons ON dS (a 2D surface) are classified by pi_2. The 2D solitons are Z3 vortices (from pi_2(SU(3)/Z3) = Z3), not skyrmions. The proposition should be more careful to distinguish:
- Solitons ON dS: classified by pi_2, giving Z3 vortices
- Solitons in the emergent 3D space: classified by pi_3, giving skyrmions/baryons

Phase 5 (SS5.3.4) does address this distinction, but the main proposition file (SS6.1, Claim 5) conflates them.

**Location:** SS6.1 "Topological sectors"; Claim 5 table; Phase 5 SS5.1.2.

---

## 4. QCD CORRESPONDENCE

### 4.1 Svetitsky-Yaffe Mapping

**Assessment: STRUCTURALLY SOUND WITH IMPORTANT NUANCES**

The Svetitsky-Yaffe universality hypothesis (1982) states that the deconfinement transition of SU(N) gauge theory in (d+1) dimensions belongs to the universality class of the Z_N spin model in d dimensions, *provided the transition is second-order*. For SU(3), the deconfinement transition is **first-order** (both in pure gauge theory and in the Z3 Potts model in 2D). The Svetitsky-Yaffe conjecture technically does not apply to first-order transitions in its original formulation.

However, lattice QCD studies have shown that even though the SU(3) transition is weakly first-order, the Polyakov-loop correlation functions are in excellent agreement with Z3 Potts model predictions using conformal perturbation theory. So the structural mapping remains useful.

**The proposition correctly identifies this nuance in SS5.3:** "The mapping is structural, not quantitative" and notes that both transitions are first-order. This is appropriately cautious.

**No additional issues beyond what is already acknowledged.**

### 4.2 T_c ~ 155 MeV

**Assessment: IMPORTANT DISTINCTION MISSING**

**Issue Q-1 (Significant): The proposition conflates two different T_c values.**

- **Pure SU(3) gauge theory (quenched):** T_c ~ 270 MeV. This is the deconfinement temperature in the absence of dynamical quarks.
- **Full QCD with physical quark masses:** T_pc ~ 155 +/- 2 MeV (lattice QCD crossover pseudocritical temperature). This is a **crossover**, not a true phase transition.

The Svetitsky-Yaffe mapping relates to the **pure gauge** deconfinement transition (T_c ~ 270 MeV), which is genuinely first-order. The T_c ~ 155 MeV quoted in the proposition (SS5.2 table, Phase 5 SS5.4.2) is the full QCD crossover temperature, which involves fundamentally different physics (chiral symmetry restoration with dynamical quarks, not center symmetry breaking).

The proposition should either:
(a) Use T_c ~ 270 MeV for the pure-gauge Svetitsky-Yaffe analogy, or
(b) Explicitly note that 155 MeV is the full QCD crossover temperature and explain why it is more appropriate than the pure-gauge value for the CG framework.

The rough estimate in Phase 5 SS5.4.2 ($T_c ~ 0.011 * 440/0.03 ~ 161$ MeV) appears tuned to match 155 MeV, but the proportionality factor "0.03" is not derived from any principle.

**Location:** SS5.2 table; Phase 5 SS5.4.2.

### 4.3 First-Order Nature of Z3 Potts in 2D

**Assessment: CORRECT**

The q=3 Potts model on a 2D lattice (including the triangular lattice relevant for dS) has a first-order phase transition. This is well-established (Wu 1982, Baxter 1973) and confirmed by the web search results. The proposition correctly states this in SS5.3 caveat 2.

The SU(3) pure gauge deconfinement transition in 3+1 dimensions is also first-order. The match in transition order between the Z3 Potts model and SU(3) deconfinement is a nontrivial consistency check, correctly noted in the proposition.

**No issues identified.**

### 4.4 Skyrme Model Mass Prediction

**Assessment: BROADLY CORRECT BUT OVERSIMPLIFIED**

The classical skyrmion mass formula M = 73*f_pi/e (with the numerical coefficient ~73 for the SU(2) hedgehog ansatz) gives:
- With f_pi = 88 MeV (CG value), e = 5.45: M_classical ~ 1180 MeV
- With f_pi = 93 MeV (PDG value), e = 5.45: M_classical ~ 1240 MeV

The claim that "~20% quantum corrections" reduce this to ~940 MeV requires examination.

**Issue Q-2 (Moderate): The quantum corrections in the Skyrme model are not a simple ~20% reduction.** The original Adkins-Nappi-Witten (1983) treatment fits f_pi and e simultaneously to the nucleon and Delta masses, obtaining f_pi ~ 108 MeV and e ~ 5.45, which gives M_N ~ 940 MeV by construction. With the physical f_pi ~ 93 MeV, the classical mass is ~1240 MeV and the quantum rotational correction (zero-mode quantization) gives additional terms. More recent work (e.g., nonlinear rigid-body quantization, vibrational mode corrections) shows that the quantum corrections involve a subtle cancellation between classical binding energy and zero-point vibrational energy. The "~20% correction" stated in the proposition oversimplifies this; the actual correction depends on the specific treatment and can range from 15-30%.

Using the CG value f_pi = 88 MeV (which is ~4.5% below the PDG value of ~92.2 MeV) makes the classical skyrmion lighter, which may make the quantum corrections easier to accommodate. But this should be stated more carefully.

**Location:** SS6.3; Phase 5 SS5.3.2, SS5.4.2.

---

## 5. FRAMEWORK CONSISTENCY

### 5.1 Consistency with Definition 0.1.1

**Assessment: CONSISTENT**

The proposition correctly uses dS = dT+ disjoint union dT- throughout. The bilayer structure is explicitly maintained. The Euler characteristic chi = 4 is not directly used in the Fisher-KPP analysis but is implicitly respected by treating the two S^2 surfaces separately. The triangulation scheme (n_sub divisions per edge, 2*n_sub^2 + 2 vertices per tetrahedron) is consistent with Def 0.1.1's construction.

**No issues identified.**

### 5.2 Consistency with Definition 0.1.2

**Assessment: CONSISTENT**

The Z3 phase structure (R <-> 0, G <-> 1, B <-> 2 with phases 0, 2pi/3, 4pi/3) is correctly used in the trit-level description (Phase 3 SS3.1.2) and the Z3 Fourier order parameter. The spontaneous Z3 symmetry breaking (one replicator family dominates) is consistent with the three color fields having distinct phases.

**No issues identified.**

### 5.3 Consistency with Theorem 0.2.1

**Assessment: CONSISTENT WITH CAVEAT**

The bilayer coupling is attributed to Thm 0.2.1's field superposition. As noted in Issue P-2, the specific 50% value is a modeling choice rather than a derived consequence. However, the general principle that fields on T+ and T- interact through superposition is consistent with Thm 0.2.1.

### 5.4 SU(3) -> Z3 Center Symmetry

**Assessment: CORRECTLY USED**

The identification Z3 = Z(SU(3)) (center of the gauge group) is standard. The Polyakov loop taking values in Z3 in the confined phase is standard lattice gauge theory. The proposition correctly uses this relationship in SS7.1-7.2.

**No issues identified.**

---

## 6. SPECIFIC PHYSICS CONCERNS

### 6.1 PDE Steady State (0.810) vs Discrete Soup (~55%)

**Assessment: THIS IS A GENUINE DISCREPANCY THAT DESERVES MORE ATTENTION**

**Issue SP-1 (Significant): The 47% discrepancy between the PDE prediction (rho* = 0.810 at mu = 0.001) and the discrete soup (~55%) is large.** The proposition attributes this to "quasispecies diversity" -- multiple competing replicator families in the soup reduce the effective density of any single family. Phase 3 SS3.2.7 provides a more detailed discussion, noting that the binary replicator/food classification oversimplifies the quasispecies cloud.

This explanation is plausible but not verified. The discrepancy could also indicate:
(a) The mean-field coarse-graining misses important correlations
(b) The parameter extraction (k_eff = 0.22, gamma = 0.027) is fit to the mu = 0 and mu = mu_c endpoints but does not correctly interpolate
(c) The Fisher-KPP framework may not be the correct continuum limit

The proposition should present a more systematic comparison across the full mutation range (as done in Phase 3 SS3.4.3 Experiment 1, which shows a systematic ~7-10% underprediction in mid-range). The 0.810 vs 0.55 discrepancy at mu = 0.001 is the worst case and should not be dismissed as a minor detail.

**Location:** SS3.4 table; Phase 3 SS3.2.6-3.2.7.

### 6.2 Front Speed Discrepancy (51% of Flat-Space Value)

**Assessment: ADEQUATELY EXPLAINED**

The measured front speed (0.046) being 51% of the flat-space KPP prediction (0.089) is explained by three effects: (i) bilayer coupling diverts density to T-, slowing the T+ front; (ii) curvature of S^2 modifies the Laplacian; (iii) the compact geometry means fronts wrap around. These are all expected effects on compact curved surfaces and collectively could account for a factor-of-2 reduction. The qualitative behavior (front propagation, saturation) matches.

**No additional issues.**

### 6.3 Non-Hermitian Doi-Peliti Hamiltonian

**Assessment: CORRECTLY IDENTIFIED AS AN OPEN PROBLEM**

The Doi-Peliti Hamiltonian being non-Hermitian (|Im(lambda)| ~ 0.59 for L=4) is generic for non-equilibrium processes. The physical implications are:
- The NESS (non-equilibrium steady state) is not a ground state in the quantum mechanical sense
- The spectral gap may be complex, affecting relaxation dynamics
- Relating H_DP to the physical SU(3) Yang-Mills Hamiltonian requires a similarity transformation

The proposition correctly identifies this as an open problem (SS7.3 caveat, SS8.4 item 4). This is the honest assessment.

**Issue SP-2 (Minor): The proposition should note that non-Hermitian Hamiltonians are standard in the Doi-Peliti formalism and do not indicate a pathology.** The non-Hermiticity reflects probability non-conservation in the creation/annihilation operator representation (the probability is conserved by the sum-over-states, not by individual matrix elements). This is well-understood in the stochastic process literature and should be presented more clearly to avoid the impression that it is a defect.

**Location:** SS7.3; SS8.4 item 4.

### 6.4 Parisi-Wu Stochastic Quantization for Non-Abelian Theories

**Assessment: SIGNIFICANT GAP, CORRECTLY ACKNOWLEDGED**

Based on the web search, the current status is:
- Abelian (U(1)) gauge theories: Rigorous results exist for the Langevin dynamics on 2D torus using discrete regularity structures.
- Non-Abelian: No rigorous results. Recent progress on Yang-Mills-Higgs in 3D using regularity structures establishes local-in-time solutions but not the full stochastic quantization correspondence.

The proposition correctly states this gap (SS7.4 caveat: "Proven rigorously only for Abelian theories; non-Abelian extension is expected but not established"). This is a significant gap in the Z3 -> SU(3) bridge but is honestly acknowledged.

**Issue SP-3 (Moderate): The gap is more serious than the proposition suggests.** The statement "expected but not established" may give the impression that the non-Abelian extension is a technicality. In reality, the non-Abelian stochastic quantization involves the Gribov problem (gauge copies), which is a fundamental obstruction. Recent work (arXiv:2406.15059) specifically addresses this. The proposition should note the Gribov obstruction as a specific challenge.

**Location:** SS7.4.

### 6.5 mu_c Constant Across Program Lengths

**Assessment: PHYSICALLY SENSIBLE AND WELL-EXPLAINED**

The finding that mu_c ~ 0.011 is independent of program length L (violating Eigen scaling mu_c proportional to 1/L) is initially surprising but is well-explained: the replicator core is always ~20 trits regardless of L, and the threshold depends on the VM's computational fidelity, not genome length. Phase 2 SS2.2.2 provides convincing numerical evidence (mu_c x L increases linearly with L, confirming mu_c = const).

This is actually an interesting and novel result that distinguishes the computational self-replication from biological quasispecies.

**No issues identified.**

---

## 7. EXPERIMENTAL BOUNDS

### 7.1 Nucleon Mass

| Quantity | Proposition Value | Experimental Value | Status |
|----------|------------------|-------------------|--------|
| M_skyrmion (classical, f_pi = 88 MeV) | 1180 MeV | N/A (classical) | -- |
| M_nucleon (with quantum corrections) | ~940 MeV | 938.272 MeV (PDG) | CONSISTENT (by construction) |

**Assessment:** The Skyrme model parameters (f_pi, e) are typically FIT to reproduce M_N and M_Delta simultaneously. Using f_pi = 88 MeV (CG value) instead of the ANW fitted value changes the game: the classical mass is ~1180 MeV, and the claim that "~20% quantum corrections" yield 940 MeV needs independent verification. See Issue Q-2.

### 7.2 Deconfinement Temperature

| Quantity | Proposition Value | Experimental/Lattice Value | Status |
|----------|------------------|---------------------------|--------|
| T_c (full QCD crossover) | 155 MeV | 155 +/- 2 +/- 3 MeV | CONSISTENT |
| T_c (pure SU(3) gauge) | Not quoted | ~270 MeV | MISSING (see Issue Q-1) |

### 7.3 Pion Decay Constant

| Quantity | CG Value | PDG Value | Discrepancy | Status |
|----------|----------|-----------|-------------|--------|
| f_pi | 88.0 MeV | 92.2 +/- 0.1 MeV | 4.6% (4.2 MeV) | TENSION |

**Assessment:** The CG framework derives f_pi = sqrt(sigma)/5 = 440/5 = 88.0 MeV (Prop 0.0.17k). The PDG value is 92.2 MeV (charged pion decay constant). The 4.6% discrepancy is noted in the CLAUDE.md instructions ("95.6% of PDG") but is not addressed in Prop 0.0.XXe itself. Since the skyrmion mass depends linearly on f_pi, this 4.6% discrepancy propagates to a 4.6% shift in M_classical. This is within the framework's stated uncertainties but should be mentioned.

---

## 8. ISSUES SUMMARY

### Critical Issues (0)

None. The proposition does not make any claims that are physically wrong.

### Significant Issues (3)

| ID | Description | Location | Recommended Action |
|----|-------------|----------|-------------------|
| Q-1 | Conflation of pure-gauge T_c ~ 270 MeV with full QCD crossover T_pc ~ 155 MeV | SS5.2, Phase 5 SS5.4.2 | Clarify which T_c is being mapped and why |
| SP-1 | 47% discrepancy between PDE rho* (0.810) and discrete soup (~55%) inadequately explained | SS3.4 | Present systematic comparison; discuss implications for coarse-graining validity |
| S-1 | Conflation of pi_3 (3D skyrmions) with pi_2 (2D solitons on dS) in Claim 5 | SS6.1, Claim 5 table | Distinguish solitons ON dS from solitons in emergent 3D space |

### Moderate Issues (4)

| ID | Description | Location | Recommended Action |
|----|-------------|----------|-------------------|
| P-2 | 50% bilayer coupling attributed to Thm 0.2.1 but is actually a modeling parameter | SS1.1, SS3.2 | Mark as assumption, not derived |
| P-3 | "Self-replication IS bootstrap self-consistency" stated more strongly than evidence supports | SS4.5, SS9 | Soften to "structural isomorphism" consistently |
| Q-2 | Quantum corrections to skyrmion mass oversimplified as "~20%" | SS6.3 | Cite specific quantum correction mechanisms |
| SP-3 | Parisi-Wu gap for non-Abelian theories underrepresented; Gribov problem not mentioned | SS7.4 | Add note on Gribov obstruction |
| SP-4 | Z3 symmetry is explicitly broken by VM OPEN instruction (treats trit 0 specially); affects Svetitsky-Yaffe mapping assumption | SS3.1, Phase 2 SS2.1.4 | Note explicit Z3 breaking; discuss whether it is "soft" enough for Svetitsky-Yaffe |

### Minor Issues (3)

| ID | Description | Location | Recommended Action |
|----|-------------|----------|-------------------|
| P-1 | Pre-geometric status of PDE dynamics unclear | SS3.1-3.2 | Clarify that Fisher-KPP operates at computational scaffolding level |
| L-1 | D -> 0 limit not discussed | SS4.4 | Add note that D > 0 is essential for global attractor |
| SP-2 | Non-Hermitian H_DP presented as potentially problematic; actually standard for Doi-Peliti | SS7.3, SS8.4 | Clarify that non-Hermiticity is expected, not pathological |

---

## 9. LIMIT CHECKS (Summary Table)

| Limit | Behavior | Verified | Notes |
|-------|----------|----------|-------|
| mu -> 0 | rho* -> k/(k+gamma) ~ 0.89 | YES | Matches fully-seeded data |
| mu -> mu_c | rho* -> 0 (error catastrophe) | YES | Sharp transition confirmed numerically |
| kappa -> 0 | Layers decouple | YES (implicit) | Should be stated explicitly |
| D -> 0 | Local ODE; no spatial coupling | NOT CHECKED | See L-1 |
| Large N | Discrete -> PDE | PARTIAL | Convergence observed but rate not established |
| R -> infinity (flat limit) | v -> 2*sqrt(D*k) | YES | 51% reduction on compact S^2 explained |
| gamma -> 0 | Standard Fisher-KPP | YES | Reduces to f(rho) = k*rho*(1-rho) - mu*rho |

---

## 10. EXPERIMENTAL TENSIONS

| Observable | CG/Proposition Value | Experimental Value | Tension | Severity |
|------------|---------------------|-------------------|---------|----------|
| f_pi | 88.0 MeV | 92.2 MeV | 4.6% | Low (within framework uncertainties) |
| M_nucleon | ~940 MeV (after corrections) | 938.3 MeV | ~0.2% | None (but correction method uncertain) |
| T_c (QCD) | 155 MeV (quoted) | 155 MeV (crossover) / 270 MeV (pure gauge) | 0% / 74% | Significant (see Q-1) |
| rho* (PDE vs soup) | 0.810 vs ~0.55 | N/A (internal) | 47% | Significant (see SP-1) |
| Front speed | 51% of flat KPP | N/A (internal) | -- | None (explained by geometry) |

---

## 11. FRAMEWORK CONSISTENCY (Cross-References)

| Cross-Reference | Checked | Consistent | Notes |
|-----------------|---------|------------|-------|
| Def 0.1.1 (Stella topology) | YES | YES | Bilayer dS = dT+ disjoint union dT- correctly used |
| Def 0.1.2 (Three color fields) | YES | YES | Z3 phases correctly identified |
| Thm 0.2.1 (Total field superposition) | YES | PARTIAL | Coupling invoked but 50% not derived (P-2) |
| Thm 0.0.3 (Stella uniqueness -> SU(3)) | YES | YES | Used correctly in SS7.5 |
| pi_3(SU(3)) = Z | YES | YES | Standard topology; correctly applied to skyrmions |
| Svetitsky-Yaffe (1982) | YES | YES | Structural mapping correctly stated with caveats |
| Doi-Peliti (1976, 1985) | YES | YES | Verified numerically; non-Hermiticity correctly noted |
| Fisher-KPP (1937) | YES | YES | Standard theory correctly applied |

---

## 12. WHAT THE PROPOSITION DOES WELL

1. **Intellectual honesty.** The Limitations section (SS8) is thorough and correctly separates rigorous results from structural results from conjectures. This is exemplary practice.

2. **Multi-level description.** The three-level operator hierarchy (microscopic/mesoscopic/macroscopic) in SS1.1 is well-conceived and provides a clear framework for understanding what each level captures and what it misses.

3. **Non-equilibrium acknowledgment.** The proposition repeatedly and correctly notes that the soup is non-equilibrium and that the Potts/SU(3) mapping is structural, not quantitative. This is more honest than many theoretical physics papers.

4. **The catalytic/non-catalytic dichotomy.** This is a genuinely insightful way to frame the vacuum vs matter distinction and connects self-replication to the physics of vacuum stability.

5. **Error catastrophe / deconfinement analogy.** The structural mapping is compelling and the numerical evidence (mu_c independent of L) provides an interesting non-trivial prediction.

---

## 13. COMPUTATIONAL VERIFICATION (Scripts Re-Executed)

All verification scripts were independently re-executed as part of this review.

### 13.1 Fisher-KPP PDE Simulation (`rd_on_dS.py`)

**Mutation sweep (Experiment 1):** Re-executed. Results match the proposition's claims exactly:
- rho* at mu=0: 0.891 (matches observed 0.890)
- rho* at mu=0.012: 0.000 (matches observed 0.000)
- Systematic 7-10% underprediction in mid-range confirmed
- The PDE steady state formula rho* = (k_eff - mu_eff)/(k_eff + gamma) is verified to machine precision

**Long-run convergence (3000 epochs):** Independently verified that the bilayer PDE converges to rho* = 0.8097 with 0.00% error. Both T+ and T- layers equilibrate to the same value. The T- lag (seeded only T+) is approximately 300 epochs, consistent with the proposition's claim.

**Observation:** The PDE mathematics is correct. The 47% discrepancy with the discrete soup (0.810 vs ~0.55) is a coarse-graining issue, not a PDE error. The PDE perfectly reproduces its own analytical predictions.

### 13.2 Doi-Peliti Verification (`doi_peliti_verification.py`)

**All 4 tests passed** (L=2 mu=0, L=2 mu=0.01, L=2 mu=0.05, L=4 mu=0):

| Test | Core H*NESS=0 | MC Match | Z3 Symmetry | Hermitian | Ergodic Classes |
|------|---------------|----------|-------------|-----------|-----------------|
| L=2, mu=0 | PASS (||res|| = 0) | PASS | Broken (expected) | No | 44 |
| L=2, mu=0.01 | PASS (||res|| < 1e-15) | PASS | Broken (expected) | No | 1 |
| L=2, mu=0.05 | PASS (||res|| < 1e-16) | PASS | Broken (expected) | No | 1 |
| L=4, mu=0 | PASS (||res|| = 0) | PASS | Broken (expected) | No | 1852 |

**Key findings from re-execution:**
1. The Doi-Peliti theorem H_DP * P* = 0 is verified to machine precision in all cases
2. The Hamiltonian is confirmed NON-Hermitian in all cases (as claimed in SS7.3)
3. Max |Im(lambda)| = 0.587 for L=4 (matches the "~0.59" claim in SS7.3)
4. Z3 dynamical symmetry is explicitly BROKEN (the OPEN instruction treats trit 0 specially)
5. With mutation (mu > 0), the system is fully ergodic (1 ergodic class); without mutation, many absorbing states exist (1821 for L=4)
6. The Z3 symmetry breaking is spontaneous in the NESS, not just dynamical

**Additional observation (Issue SP-4, new):** The Z3 dynamical symmetry breaking deserves more attention in the proposition. The OPEN instruction (trit pair [1,2]) checks whether tape[h0] == 0, which treats trit value 0 as special. This means the Z3 symmetry is explicitly broken at the VM level, not just spontaneously broken by the NESS. The proposition claims Z3 symmetry (SS3.1, Phase 2 SS2.1.4), but the VM dynamics break it. This should be noted as an explicit breaking that may affect the Svetitsky-Yaffe mapping, which assumes the Z3 symmetry is a global symmetry of the dynamics.

However, the NESS with mutation (mu > 0) still shows approximate Z3 structure (the most probable states cluster around specific Z3 sectors), suggesting that the symmetry breaking is "soft" -- the VM treats 0 differently, but the overall dynamics still exhibit Z3-like ordering. This deserves further analysis.

### 13.3 Numerical Observations Bearing on Issue SP-1 (rho* Discrepancy)

Re-running the mutation sweep reveals a pattern: the PDE systematically overpredicts relative to the discrete soup, and the overprediction INCREASES at intermediate mutation rates. This pattern is:

| mu | PDE rho* | Soup rho* | Overprediction |
|----|----------|-----------|----------------|
| 0.000 | 0.891 | 0.890 | +0.1% |
| 0.002 | 0.729 | 0.802 | -9.1% (underpredicts!) |
| 0.004 | 0.567 | 0.644 | -12.0% |
| 0.006 | 0.405 | 0.477 | -15.1% |
| 0.010 | 0.081 | 0.189 | -57.1% |
| 0.012 | 0.000 | 0.000 | 0% |

Wait -- the PDE actually UNDERPREDICTS the soup at intermediate mu. This is the opposite of what one might expect from a mean-field overestimate. The soup maintains higher density than the PDE predicts. This suggests that the soup's quasispecies diversity actually HELPS maintain replicator density (diverse replicators are harder to destroy than a single species), which is not captured by the single-species Fisher-KPP model.

This is actually consistent with the quasispecies explanation invoked in the proposition, but the direction of the discrepancy (PDE too low, not too high) differs from what SS3.4 states ("PDE overpredicts absolute density"). The proposition should correct this characterization.

**Correction to Issue SP-1:** The PDE does NOT overpredict -- it underpredicts the soup density at intermediate mutation rates. The proposition's statement in SS3.4 ("The PDE overpredicts absolute density") appears to be incorrect. The PDE gives rho* = 0.810 at mu = 0.001, while the soup gives ~55%. But the soup data comes from the spontaneous emergence experiments (where replicators nucleate from random soup), not from the mutation sweep data in Phase 2 (where the soup starts fully seeded). The Phase 2 fully-seeded data at mu = 0.001 is not directly comparable because the Phase 2 mutation sweep at mu = 0.001 was not included in the table. The proposition should clarify which experimental condition (spontaneous vs seeded) is being compared.

---

## 14. CONFIDENCE ASSESSMENT

**CONFIDENCE: MEDIUM**

**Justification:**
- The mathematical content (Fisher-KPP theory, fixed-point analysis, stability) is on solid ground: **HIGH confidence**.
- The discrete soup simulations are well-documented and reproducible: **HIGH confidence**.
- The Doi-Peliti correspondence is numerically verified to machine precision (4/4 tests): **HIGH confidence**.
- The structural analogies (error catastrophe <-> deconfinement, catalytic <-> vacuum) are compelling but remain at the level of analogy: **MEDIUM confidence**.
- The Z3 -> SU(3) bridge relies on five independent arguments, none of which is fully constructive: **LOW-MEDIUM confidence**.
- The quantitative QCD predictions (T_c, M_N, f_pi) rely on parameter choices and modeling assumptions that are not derived from first principles: **LOW-MEDIUM confidence**.
- New finding: The Z3 symmetry is explicitly broken by the VM's OPEN instruction, which may affect the Svetitsky-Yaffe mapping: **needs investigation**.

The proposition's greatest strength is its honesty about what is established vs structural vs conjectural. The issues identified above are mostly matters of precision and clarity rather than fundamental errors.

### Updated Issue Count After Computational Verification

| Severity | Count | New from computation |
|----------|-------|---------------------|
| Critical | 0 | 0 |
| Significant | 3 | 0 (SP-1 refined but not resolved) |
| Moderate | 5 | +1 (SP-4: Z3 explicit breaking by VM) |
| Minor | 3 | 0 |

---

## Sources

- [PDG Lattice QCD Review 2024](https://pdg.lbl.gov/2024/reviews/rpp2024-rev-lattice-qcd.pdf)
- [PDG Lattice QCD Review 2025](https://pdg.lbl.gov/2025/reviews/rpp2024-rev-lattice-qcd.pdf)
- [Deconfinement in pure gauge SU(3): ghost propagator (arXiv:2301.01229)](https://arxiv.org/abs/2301.01229)
- [Ghost propagator and deconfinement in SU(3) (arXiv:2307.08662)](https://arxiv.org/abs/2307.08662)
- [Topological data analysis of deconfinement (arXiv:2412.09112)](https://arxiv.org/html/2412.09112)
- [Phase transitions in Potts model on triangular lattice (Springer)](https://link.springer.com/article/10.1134/S1063776112130092)
- [Three-state Potts model on triangular lattice (arXiv:cond-mat/9311055)](https://arxiv.org/abs/cond-mat/9311055)
- [Phase structure lattice QCD and Potts model (arXiv:2601.15720)](https://arxiv.org/html/2601.15720)
- [Svetitsky-Yaffe universality review (arXiv:2407.10678)](https://arxiv.org/html/2407.10678)
- [Lattice QCD Thermodynamics with Physical Quark Masses (arXiv:1502.02296)](https://arxiv.org/abs/1502.02296)
- [QCD crossover at finite chemical potential (arXiv:2002.02821)](https://arxiv.org/abs/2002.02821)
- [QCD phase transition with chiral quarks (arXiv:1402.5175)](https://arxiv.org/abs/1402.5175)
- [Stochastic Quantization of Abelian Gauge Theory (Springer)](https://link.springer.com/article/10.1007/s00220-021-04114-x)
- [Stochastic quantisation of Yang-Mills-Higgs in 3D (Springer)](https://link.springer.com/article/10.1007/s00222-024-01264-2)
- [Gribov Problem and Stochastic Quantization (arXiv:2406.15059)](https://arxiv.org/html/2406.15059)
- [Quantizing Yang-Mills: Parisi-Wu to Global Path Integral (arXiv:hep-th/9912041)](https://arxiv.org/abs/hep-th/9912041)
- [Quantum binding energies in the Skyrme model (arXiv:2307.09272)](https://arxiv.org/html/2307.09272)
- [Nonlinear rigid-body quantization of Skyrmions (arXiv:2311.11667)](https://arxiv.org/html/2311.11667)
- [Smorgasbord of Skyrmions (Springer JHEP)](https://link.springer.com/article/10.1007/JHEP08(2022)117)
