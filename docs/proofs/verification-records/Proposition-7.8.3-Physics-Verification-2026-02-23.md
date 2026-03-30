# Proposition 7.8.3: Bethe-Salpeter Glueball Mass Ratio -- Adversarial Physics Verification

**Date:** 2026-02-23
**Reviewer:** Independent Physics Verification Agent (Claude Opus 4.6)
**Documents Reviewed:**
- Statement: `docs/proofs/Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md`
- Derivation: `docs/proofs/Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Derivation.md`
- Applications: `docs/proofs/Phase7/Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Applications.md`
- Cross-references: Prop 7.8.2, Thm 7.5.2, Thm 7.7.3, Prop 0.0.38

---

## Executive Summary

| Item | Assessment |
|------|-----------|
| **VERIFIED** | **Partial** |
| **PHYSICAL ISSUES** | 5 findings (2 moderate, 3 minor) |
| **MATHEMATICAL CORRECTNESS** | Derivation algebra verified; closed-form formula correct |
| **EXPERIMENTAL TENSIONS** | None significant (0.01 sigma vs lattice) |
| **FRAMEWORK CONSISTENCY** | Consistent with Prop 7.8.2, Thm 7.5.2, Thm 7.7.3 |
| **CONFIDENCE** | **Medium-High** |

The derivation is mathematically correct: the algebra from the spinless Salpeter equation through the AFM and variational optimization to the closed-form R_BS = 3*sqrt(3*(2-3*alpha_s)/2) checks out at every step. The agreement with lattice Monte Carlo (0.01 sigma) is striking but should be understood as partially fortuitous given the ~7% theoretical uncertainty. The main concerns are (1) the self-consistency of the coupling determination, which is not as rigorous as claimed, (2) the treatment of systematic uncertainties in the combination with Prop 7.8.2, and (3) some subtleties around the constituent gluon picture. None of these invalidate the result, but several warrant honest acknowledgment.

---

## 1. PHYSICAL CONSISTENCY

### 1.1 Constituent Gluon Model for 0++ Glueball

**Assessment: ADEQUATE with caveats**

The two-constituent-gluon picture of the 0++ glueball is well-established in the phenomenological literature (Boulanger et al. EPJA 38 (2008) 317; Mathieu et al. PRD 70 (2004) 014017; Hong et al. PLB 775 (2017) 89). The key physical justification is that the 0++ is the lightest glueball and its quantum numbers are naturally explained by two gluons in an s-wave color singlet.

**Caveat:** The notion of a "constituent gluon" is less well-defined than a constituent quark, because gluons carry color charge and self-interact. In a confining theory, there is no clean separation between the binding potential and the constituents. The model should be understood as an effective description at the scale of the glueball, not as a literal statement about the internal structure. The proposition acknowledges this implicitly but could be more explicit.

### 1.2 Spinless Salpeter Equation for Massless Particles

**Assessment: CORRECT**

The Hamiltonian H = 2|p| + V(r) is the standard form of the spinless Salpeter equation for two massless particles in the center-of-mass frame. This is the correct relativistic generalization for spinless bound states when both constituents are massless. The use of |p| (rather than sqrt(p^2 + m^2)) is appropriate for gluons, which have zero mass in perturbation theory.

### 1.3 Cornell Potential for Adjoint Sources

**Assessment: CORRECT**

The Cornell potential V(r) = sigma_adj * r - 3*alpha_s/r combines:
- A linear confining term with Casimir-scaled adjoint string tension
- A one-gluon-exchange Coulomb term with the correct color factor for the singlet channel

The color factor <1|F1.F2|1> = -3 is verified in 5.3-5.4. The minus sign correctly indicates attraction.

**FINDING F-1 (Minor):** The Cornell potential is an approximation. At short distances (r < 0.1 fm), perturbative corrections beyond one-gluon exchange become important. At long distances (r > 1.2 fm), string breaking for adjoint sources sets in (Bali 2000 suggests the adjoint string breaks at r_b ~ 1.25 fm). The glueball wavefunction extends over ~1/beta ~ 0.5/1.98 ~ 0.25 fm (using beta_opt from Eq. 9.5 and sqrt(sigma) = 440 MeV -> a ~ 0.45 fm), so the relevant distances are within the regime where the Cornell potential is valid. The proposition does not explicitly compute the glueball size and confirm it is within the Cornell regime. This should be stated.

### 1.4 alpha_s = 0.38 at the Glueball Scale

**Assessment: PROBLEMATIC (see Finding F-2)**

**FINDING F-2 (Moderate):** The self-consistency argument in 9.6 is weaker than presented. The one-loop running coupling at the two natural scales gives:

- Scale (a): mu = m_G/2 ~ 750 MeV -> alpha_s = 0.47 (from verification script output)
- Scale (b): mu = beta*sqrt(sigma) ~ 871 MeV -> alpha_s = 0.42

Both of these are significantly *above* the adopted value alpha_s = 0.38. The argument in 9.6 that "alpha_s ~ 0.34 (two-loop estimate)" at 871 MeV is stated without computation, and the verification script confirms the one-loop values bracket 0.42-0.47, not 0.34-0.42 as the text implies. The tension with the adopted central value (1.54 sigma per the verification script) is not negligible.

The adopted value alpha_s = 0.38 +/- 0.04 appears to be chosen because it gives R_BS ~ 3.41, matching the lattice value. While the uncertainty range (0.34 to 0.42) does bracket values consistent with the one-loop estimates, and two-loop and scheme corrections do reduce alpha_s, the argument is effectively: "we choose alpha_s such that R_BS matches lattice, and this choice is self-consistent within uncertainties." This is not circular per se (the formula's *structure* is independent of alpha_s), but the claimed "self-consistency" overstates the rigor. The more honest statement is: "the formula R_BS(alpha_s) passes through the lattice value at alpha_s = 0.38, which is within the plausible range for the glueball scale."

### 1.5 Massless Constituent Gluons in a Confining Theory

**Assessment: ADEQUATE**

In the Salpeter equation, "massless" refers to the absence of a bare mass term in the kinetic energy. The gluons acquire a dynamical mass through confinement (the bound state mass is ~1.5 GeV). This is analogous to how massless quarks in the current mass sense acquire constituent masses through QCD dynamics. The model is consistent in that the mass emerges entirely from the potential energy, which is the physical content of "mass from confinement."

---

## 2. LIMITING CASES

| Limit | Value | Physical Interpretation | Assessment |
|-------|-------|------------------------|------------|
| alpha_s -> 0 (pure confinement) | R_BS -> 3*sqrt(3) = 5.196 | Mass entirely from linear potential | REASONABLE: pure linear potential gives larger mass due to stronger confinement |
| alpha_s -> 2/3 (critical coupling) | R_BS -> 0 | Coulomb attraction overwhelms confinement | CORRECT: this is the Coulomb catastrophe for the semirelativistic equation; the model breaks down |
| alpha_s = 0.38 (central) | R_BS = 3.407 | Lattice = 3.405 +/- 0.021 | CONSISTENT (0.01 sigma) |
| sigma -> 0 | R_BS independent of sigma | Ratio property of dimensional analysis | CORRECT: both m_G and sqrt(sigma) scale as sigma^{1/2} |
| N_c dependence | Embedded in color factors (C2(adj)/C2(fund)) | Would change for other gauge groups | CORRECT |

**The pure-confinement limit R_BS -> 5.196 is reasonable.** For comparison, the Airy function solution of the semirelativistic Salpeter equation with a purely linear potential gives the ground state energy E_0 ~ c * (sigma)^{1/2} where c depends on the specific method. The AFM value of 5.196 is an upper bound on the exact result. Literature values for the pure linear semirelativistic problem give values in the range 4.5-5.2, so the AFM overestimates by ~5-10%, consistent with expectations.

**The critical coupling alpha_s = 2/3 is physical.** For the nonrelativistic Coulomb problem with coupling -3*alpha_s/r and kinetic energy p^2/(2*m_eff), bound states exist only if the coupling exceeds a threshold. For the semirelativistic Salpeter equation with |p| kinetic energy, the threshold is known to be at alpha_s = 2/(pi) ~ 0.637 for a pure Coulomb potential with coefficient -3*alpha_s. The value 2/3 ~ 0.667 from the model is close to this, confirming the model captures the correct physics. With the linear term, the system always has bound states, but the formula breaks down as the Coulomb term dominates.

---

## 3. SYMMETRY AND QUANTUM NUMBERS

### 3.1 s-wave Wavefunction and J^PC = 0++

**Assessment: CORRECT**

The exponential wavefunction psi(r) = (beta^3/pi)^{1/2} exp(-beta*r) is spherically symmetric (l = 0), giving J = 0. For two identical bosons (gluons) in an s-wave, the spatial wavefunction is symmetric under particle exchange. The color-singlet state in 8 x 8 -> 1 is symmetric (from the symmetric part of the tensor product). The combined state is therefore:
- J = 0 (s-wave)
- P = +1 (two identical bosons in s-wave: P = (-1)^L = +1)
- C = +1 (gluons are their own antiparticles in pure gauge; two-gluon C = (-1)^{L+S} = +1 for L=0, S=0)

This correctly produces J^PC = 0++.

### 3.2 Color-Singlet Channel

**Assessment: CORRECT**

The decomposition 8 x 8 = 1 + 8_S + 8_A + 10 + 10bar + 27 is the standard SU(3) tensor product decomposition of two adjoint representations. The dimensionalities check out: 8 x 8 = 64 = 1 + 8 + 8 + 10 + 10 + 27. The glueball is correctly identified with the singlet (1) channel, as glueballs are color-neutral bound states.

### 3.3 Color Factor Verification

**Assessment: CORRECT**

The formula <R|F1.F2|R> = (1/2)(C2(R) - C2(R1) - C2(R2)) with C2(1) = 0, C2(8) = 3 gives -3. This is a standard group theory result.

---

## 4. CASIMIR SCALING

### 4.1 Validity of sigma_adj/sigma_fund = 9/4

**Assessment: CORRECT at relevant distances**

Casimir scaling predicts sigma_R/sigma_fund = C2(R)/C2(fund). For the adjoint: 9/4 = 2.250. Bali (2000) finds sigma_8/sigma_3 = 2.26 +/- 0.06 from lattice simulations, consistent to within 0.17 sigma.

### 4.2 String Breaking for Adjoint Sources

**Assessment: ACKNOWLEDGED but could be more explicit**

The adjoint representation has N-ality 0, meaning the asymptotic string tension vanishes. The adjoint string breaks at a distance r_b ~ 1.25-1.55 fm (Bali 2000; G2 gluodynamics studies suggest similar scales). For the glueball, the relevant distance scale is the glueball "radius" ~1/(2*beta_opt):

- beta_opt = 1.981 * sqrt(sigma) ~ 1.981 * 440 MeV = 871 MeV ~ 4.4/fm
- Glueball size ~ 1/(2*beta) ~ 0.23 fm (in natural units: 1/(2*871 MeV) * 197.3 MeV*fm ~ 0.11 fm)

This is well below the string breaking distance, so Casimir scaling is valid in the relevant regime. Prop 7.8.2 Section 9.2 acknowledges this explicitly. The Derivation file (10.3) addresses Casimir corrections quantitatively and finds them negligible (0.2%).

### 4.3 Lattice Evidence

**Assessment: ADEQUATE**

Bali (2000) provides the most comprehensive lattice study of Casimir scaling for SU(3). The adjoint potential is measured at distances up to ~0.8 fm and shows excellent agreement with Casimir scaling. At the glueball scale (~0.1-0.3 fm), the agreement is within statistical errors. The quoted sigma_8/sigma_3 = 2.26 +/- 0.06 is a fair summary.

---

## 5. AUXILIARY FIELD METHOD PHYSICS

### 5.1 AFM Upper Bound

**Assessment: CORRECT**

The AFM identity |p| = min_nu [p^2/(2nu) + nu/2] is exact. Replacing the operator |p| with the optimized quadratic form for a *specific* choice of nu gives an upper bound on the true energy. The variational principle then guarantees E_var >= E_exact. The AFM + variational method therefore produces a rigorous upper bound on the ground state energy.

### 5.2 AFM Accuracy for Cornell Potential

**Assessment: REASONABLE, but ~5% claim needs qualification**

The Derivation 10.2 claims "AFM error for the Cornell potential has been benchmarked against numerical solutions and is typically ~5%." The references cited are [12] (Silvestre-Brac & Semay, JMP 46 (2005)) and [13] (Mathieu et al., PRD 77 (2008)).

**FINDING F-3 (Minor):** The ~5% figure should be more carefully qualified. The Mathieu et al. 2008 paper studies *three-gluon* glueballs, not two-gluon ones. For two-gluon systems, the relevant comparison would be with numerical solutions of the spinless Salpeter equation with Cornell potential, as in Mathieu et al. PRD 70 (2004) 014017. The AFM overestimate depends on the ratio of Coulomb to linear potential strength; for alpha_s = 0.38, the Coulomb term is significant (about 33% of the linear term at the optimal beta). A more careful estimate would be ~5-10% overestimate, which is what the verification script ADV-2 adopts (7%). The proposition's claim of ~5% is optimistic but not unreasonable.

### 5.3 Comparison with Numerical Salpeter Solutions

**Assessment: CONSISTENT with literature**

Constituent gluon models using the semirelativistic Salpeter equation with Cornell potential typically find the 0++ glueball mass in the range 1400-1700 MeV (Mathieu et al. PRD 70 (2004); Boulanger et al. EPJA 38 (2008); Hong et al. PLB 775 (2017)). Using sqrt(sigma) = 440 MeV, R_BS = 3.41 gives m_G = 1500 MeV, squarely within this range.

---

## 6. UNCERTAINTY ASSESSMENT

### 6.1 delta(alpha_s) = 0.04

**FINDING F-4 (Moderate):** The uncertainty delta(alpha_s) = 0.04 is presented as motivated by the "scale ambiguity" between the two scale choices (9.3 and 9.4). However, the verification script reveals:

- Scale (a): alpha_s(750 MeV) = 0.467 (one-loop)
- Scale (b): alpha_s(871 MeV) = 0.416 (one-loop)
- Central of these two: 0.44

The adopted central value (0.38) is 1.5 sigma *below* the one-loop central estimate. The justification is that "two-loop corrections reduce alpha_s by ~10-15%," but this is not computed explicitly. If the true coupling at the relevant scale were 0.42 (as the one-loop scale (b) suggests), then R_BS(0.42) = 3.16, which is 0.24/0.24 ~ 1 sigma below the lattice value -- still consistent, but the "0.01 sigma agreement" would disappear.

The uncertainty 0.04 captures a range [0.34, 0.42] which does bracket reasonable values, but the presentation of the self-consistency as tight is misleading. A more conservative estimate would be alpha_s = 0.40 +/- 0.06, giving R_BS = 3.29 +/- 0.37 (11%), which is still consistent with lattice at ~0.3 sigma but with wider uncertainty.

This does not invalidate the result, but the claimed 7% precision is optimistic. A more honest assessment would be ~10-11%.

### 6.2 Scale Choices

**Assessment: REASONABLE**

The two scale choices (half the glueball mass, and the variational momentum parameter) are standard in bound-state physics. They provide a natural range for the coupling.

### 6.3 Self-Consistency Argument (Section 9.6)

**Assessment: WEAK (see F-2 above)**

The self-consistency argument starts with alpha_s = 0.38, computes beta_opt = 871 MeV, evaluates alpha_s(871 MeV) and claims "Central: alpha_s ~ 0.38 -- self-consistent within the uncertainty." But the one-loop formula gives 0.42 at this scale, not 0.38. The argument relies on unspecified two-loop and scheme corrections to bring this down by ~10%. This is plausible but not demonstrated.

### 6.4 Correlated vs Uncorrelated Uncertainties (Section 10.5)

**Assessment: REASONABLE**

The treatment in 10.5 correctly identifies that the AFM/variational systematics are correlated (they push R upward as an upper bound) while the alpha_s uncertainty is independent. The decision to adopt the alpha_s uncertainty alone as the total is conservative *if* the AFM overestimate is compensated by a lower effective alpha_s. This is logically consistent: if the true mass is lower (exact solution < variational bound), then a higher alpha_s would be needed to match lattice, partially canceling the systematic.

### 6.5 Inverse-Variance Weighted Average

**FINDING F-5 (Minor):** The inverse-variance weighted average of Prop 7.8.2 (3.38 +/- 0.27) and Prop 7.8.3 (3.41 +/- 0.24) assumes independence. The text correctly identifies Casimir scaling as the shared assumption. However, the treatment implicitly assumes the Casimir scaling uncertainty is negligible (which is true at 0.2%), so the combination is valid. The standard formula for weighted average applies when the measurements are uncorrelated. Since the dominant uncertainties (Delta for 7.8.2, alpha_s for 7.8.3) are genuinely independent, the combination is well-motivated. But the shared Casimir scaling means the combined uncertainty cannot go below the Casimir scaling systematic (~0.2%), which is far below the 5.3% claimed, so this is not a practical limitation.

---

## 7. COMPARISON WITH LITERATURE

### 7.1 R_BS = 3.41 vs Other Semirelativistic Models

The proposition's result R_BS = 3.41 +/- 0.24 is consistent with:

| Method | R_cont or m_G | Agreement |
|--------|--------------|-----------|
| Lattice MC (Athenodorou & Teper 2020) | 3.405 +/- 0.021 | 0.01 sigma |
| Constituent gluon (Buisseret+ 2006) | ~3.3 +/- 0.3 | 0.3 sigma |
| AdS/CFT holographic | ~3.6 +/- 0.7 | 0.3 sigma |
| SVZ sum rules (Narison 1998) | ~3.2 +/- 0.5 | 0.4 sigma |

### 7.2 Known Issues with Constituent Gluon Models

Constituent gluon models have known limitations:
1. The gluon self-coupling is not accounted for (only pairwise interactions)
2. Spin-orbit and tensor forces are neglected in the spinless approximation
3. The Coulomb term may need running alpha_s(r) rather than a fixed value
4. String breaking for adjoint sources at large r is not included

These are all subleading effects for the 0++ ground state, where the dominant physics is the confining linear potential. The spinless approximation is exact for the 0++ (no spin-orbit coupling needed). The proposition's treatment is standard for this class of models.

---

## 8. EXPERIMENTAL / LATTICE COMPARISON

### 8.1 Lattice Value Clarification

The prompt raises a concern about R_cont = 3.405 vs the "Morningstar-Peardon value of 1710 MeV." This is clarified in the proposition:

- Morningstar & Peardon (1999) quote m(0++) = 1730 +/- 50 +/- 80 MeV using sqrt(sigma) ~ 440 MeV (their r_0 scale). This gives R ~ 1730/440 ~ 3.93.
- However, the 1999 study used a finite set of lattice spacings and did not perform a full continuum extrapolation.
- Athenodorou & Teper (2020) performed a rigorous continuum extrapolation with 7 different lattice spacings, obtaining R_cont = 3.405 +/- 0.021. This is the modern benchmark.
- The difference arises because the continuum extrapolation removes O(a^2) lattice artifacts, which are significant for glueball masses.

The proposition correctly uses R_cont = 3.405 from Athenodorou & Teper (2020) as the comparison value.

### 8.2 Combined 5.3% Uncertainty

The 5.3% combined uncertainty represents a meaningful improvement over Prop 7.8.2's 8.0% alone. Given the identified concerns about the alpha_s determination (F-2, F-4), the true uncertainty of the Bethe-Salpeter estimate alone may be closer to 10-11%. If this were the case, the combined uncertainty would be closer to 6-7%, still representing an improvement but less dramatic. The 5.3% figure is therefore somewhat optimistic.

---

## 9. FRAMEWORK CONSISTENCY

### 9.1 Casimir Invariants (Prop 0.0.38)

The Casimir values C2(3) = 4/3 and C2(8) = 3 are standard SU(3) results and consistent throughout the framework. Prop 0.0.38 uses these values in the heat kernel coefficients a_R(beta), and the same values appear here. **CONSISTENT.**

### 9.2 One-Loop Beta Function (Thm 7.5.2)

The one-loop coefficient is quoted as b_0 = 11/(16*pi^2) in Thm 7.5.2 and in the symbol table (Section 2). However, the self-consistency calculation (Section 9.2) uses b_0 = 11*N_c/(12*pi) = 2.626.

These are **different conventions**:
- b_0 = 11/(16*pi^2) ~ 0.0697 is the coefficient in the RG equation d(alpha_s)/d(ln mu) = -2*b_0*alpha_s^2
- b_0 = 11*N_c/(12*pi) = 2.626 is the coefficient in alpha_s(mu) = 1/(b_0*ln(mu^2/Lambda^2)) where the equation reads d(alpha_s)/d(ln mu^2) = -b_0*alpha_s^2

Let me verify: if d(alpha_s)/d(ln mu) = -2*b_0*alpha_s^2 with b_0 = 11/(16*pi^2), then d(alpha_s)/d(ln mu^2) = -b_0*alpha_s^2 and the solution is alpha_s = 1/(b_0*ln(mu^2/Lambda^2)) with b_0 = 11/(16*pi^2) ~ 0.0697.

But the derivation Section 9.2 uses alpha_s = 1/(b_0*ln(mu^2/Lambda^2)) with b_0 = 11*3/(12*pi) = 2.626. These cannot both be correct. The standard one-loop formula for N_f = 0 SU(N_c) is:

alpha_s(mu) = 2*pi / (b_0 * ln(mu^2/Lambda^2))

where b_0 = (11/3)*N_c = 11 for SU(3). Then: alpha_s = 2*pi/(11*ln(mu^2/Lambda^2)).

The value in Section 9.2: alpha_s = 1/(2.626*ln(mu^2/Lambda^2)) = 1/((11*3/(12*pi))*ln(...)) = 12*pi/(33*ln(...)) = 2*pi/(5.5*ln(...)). Wait, let me compute more carefully: 11*3/(12*pi) = 33/(12*pi) = 33/37.70 = 0.8754, and 1/0.8754 = 1.142...

Actually, let me check the conventions. The standard form is:

alpha_s(Q) = 4*pi / (beta_0 * ln(Q^2/Lambda^2))

where beta_0 = 11 - (2/3)*n_f = 11 for n_f = 0.

This gives alpha_s(750 MeV) = 4*pi/(11*ln(750^2/220^2)) = 12.566/(11*2.445) = 12.566/26.89 = 0.467.

The verification script computes alpha_s(mu_a) = 0.467, which matches this convention. But the script uses b0 = 11*3/(12*pi) = 0.8754 in the formula alpha_s = 1/(b0*ln(mu^2/Lambda^2)), giving 1/(0.8754*2.445) = 1/2.140 = 0.467. This also checks out. So b0 = 11*N_c/(12*pi) is the coefficient when alpha_s = 1/(b0*ln(mu^2/Lambda^2)), which is equivalent to the standard formula alpha_s = 4*pi/(beta_0*ln(Q^2/Lambda^2)) with beta_0 = 11.

These are just different conventions for writing the same formula. The derivation is internally consistent, and the b_0 = 11/(16*pi^2) in Thm 7.5.2 refers to the beta function in the form beta(g) = -b_0*g^3 - ..., which gives a different numerical value. **CONSISTENT** (different conventions, same physics).

### 9.3 Updated c_FI Propagation to Thm 7.7.3

Thm 7.7.3 currently reports c = 6.78 +/- 0.31 (using R_cont = 3.405 from lattice MC and sqrt(sigma)/Lambda = 1.99 +/- 0.09). The updated framework-internal value c_FI = 6.78 +/- 0.38 from the combined Props 7.8.2 + 7.8.3 is consistent. The central value matches almost exactly (6.78 in both cases), and the framework-internal error (0.38) is larger than the lattice-input error (0.31) as expected. **CONSISTENT.**

---

## 10. DETAILED FINDINGS

### F-1: Glueball Size and Cornell Potential Regime (Minor)

**Location:** Derivation Section 5.3
**Issue:** The proposition uses the Cornell potential without verifying that the glueball's spatial extent falls within the regime where this potential is valid (i.e., below the adjoint string-breaking distance ~1.25 fm).
**Impact:** Low. The glueball size is ~0.1-0.2 fm, well within the Cornell regime. But this should be stated explicitly.
**Recommendation:** Add a sentence in Section 5.3 or 10.3 computing the glueball RMS radius and confirming it is below the string-breaking distance.

### F-2: Self-Consistency of Coupling Determination (Moderate)

**Location:** Derivation Section 9.6
**Issue:** The self-consistency claim is weaker than presented. The one-loop alpha_s at both natural scales (0.42-0.47) exceeds the adopted value (0.38). The argument relies on unspecified two-loop and scheme corrections.
**Impact:** Moderate. The central value alpha_s = 0.38 may be ~1.5 sigma below the self-consistent one-loop estimate. This does not invalidate the formula (which is valid for any alpha_s < 2/3) but it means the "self-consistency" language overstates the rigor.
**Recommendation:** (a) Compute the two-loop running coupling explicitly at the glueball scale and show it gives ~0.38. (b) Or, more honestly, state that alpha_s = 0.38 is chosen as the value at which R_BS matches lattice data, and that this lies within the plausible range bracketed by one-loop estimates at different scales. (c) Expand the uncertainty to alpha_s = 0.40 +/- 0.06 for a more conservative estimate.

### F-3: AFM Accuracy Claim (Minor)

**Location:** Derivation Section 10.2
**Issue:** The ~5% AFM error claim cites references [12, 13] for Cornell potential benchmarks. Reference [13] (Mathieu et al. 2008) studies three-gluon glueballs, not two-gluon systems. A more appropriate benchmark would be Mathieu et al. PRD 70 (2004) for two-gluon systems.
**Impact:** Low. The ~5% figure is plausible but the citation is not perfectly targeted.
**Recommendation:** Cite the two-gluon glueball paper (Mathieu et al. PRD 70 (2004) 014017) rather than the three-gluon paper for the AFM accuracy benchmark.

### F-4: alpha_s Uncertainty May Be Underestimated (Moderate)

**Location:** Derivation Section 10.1
**Issue:** The adopted delta(alpha_s) = 0.04 gives a range [0.34, 0.42]. But the one-loop self-consistent estimate at the glueball scale is 0.42-0.47, suggesting the true central value may be higher (around 0.40-0.42) with the uncertainty extending up to 0.46-0.48. A more conservative delta = 0.06 would better capture the scale uncertainty.
**Impact:** Moderate. If the true uncertainty is 10-11% rather than 7%, the combined uncertainty with Prop 7.8.2 would be 6-7% rather than 5.3%. Still an improvement, but less dramatic.
**Recommendation:** Either compute two-loop alpha_s to justify the tight range, or expand to delta = 0.06 for conservatism.

### F-5: Weighted Average Assumptions (Minor)

**Location:** Applications Section 11.2
**Issue:** The inverse-variance weighted average assumes the two estimates are uncorrelated. They share the Casimir scaling assumption, but the shared systematic is negligible (0.2%). More importantly, both methods fundamentally describe the same physical system and may share some model-dependent assumptions about the glueball being a two-constituent system. The systematic from this shared picture is hard to quantify.
**Impact:** Low. The shared model assumption (two-constituent glueball) is well-supported by lattice data showing the 0++ glueball is dominated by two-gluon operators, so this is unlikely to introduce a significant correlated bias.
**Recommendation:** Add a brief note acknowledging that both methods share the two-constituent glueball picture and that this model assumption is well-supported by lattice operator analysis.

---

## 11. LIMIT CHECKS TABLE

| Limit | Formula Prediction | Physical Expectation | Assessment |
|-------|-------------------|---------------------|------------|
| alpha_s -> 0 | R_BS = 3*sqrt(3) = 5.196 | Pure confinement; large mass | PASS (reasonable; AFM upper bound) |
| alpha_s -> 2/3 | R_BS -> 0 | Coulomb catastrophe | PASS (model breaks down appropriately) |
| alpha_s = 0.38 | R_BS = 3.407 | Lattice: 3.405 +/- 0.021 | PASS (0.01 sigma) |
| sigma -> 0 at fixed alpha_s | R_BS independent of sigma | Dimensional analysis | PASS |
| sigma -> infinity at fixed alpha_s | Same R_BS | Dimensional analysis | PASS |
| Coulomb off (alpha_s = 0) | R_BS = 5.196 | AFM exact for pure linear | PASS |
| Linear off, pure Coulomb | Not well-defined (no confinement) | No bound states in isolation | PASS (formula undefined) |
| N_c -> infinity (adj) | Color factors scale with N_c | Large-N limit well-defined | PASS |

---

## 12. OVERALL ASSESSMENT

### VERIFIED: Partial

The mathematical derivation from Salpeter equation to closed-form R_BS is correct. The algebra, color factors, variational optimization, and AFM application are all verified. The formula R_BS = 3*sqrt(3*(2-3*alpha_s)/2) is a genuine, closed-form, dimensionless prediction that depends on a single phenomenological parameter (alpha_s).

The agreement with lattice Monte Carlo (0.01 sigma) is impressive but should be understood with nuance: the alpha_s value that produces this agreement (0.38) is not determined from first principles with high confidence. The self-consistency argument is suggestive but not rigorous. A more conservative assessment would quote R_BS = 3.4 +/- 0.4 (12%), still fully consistent with lattice.

The combination with Prop 7.8.2 is well-motivated and produces a meaningful uncertainty reduction. The updated c_FI = 6.78 +/- 0.38 is consistent with the lattice-input value.

### PHYSICAL ISSUES

1. **F-1 (Minor):** Glueball size vs Cornell regime not explicitly verified
2. **F-2 (Moderate):** Self-consistency of alpha_s = 0.38 overstated; one-loop gives 0.42-0.47
3. **F-3 (Minor):** AFM ~5% accuracy citation targets three-gluon systems, not two-gluon
4. **F-4 (Moderate):** alpha_s uncertainty 0.04 may be underestimated; 0.06 more conservative
5. **F-5 (Minor):** Weighted average shares two-constituent model assumption (but well-supported)

### EXPERIMENTAL TENSIONS

None significant. R_BS = 3.41 vs lattice 3.405 is 0.01 sigma. The combined result R = 3.40 vs lattice 3.405 is 0.03 sigma.

### FRAMEWORK CONSISTENCY

All cross-references checked:
- Casimir invariants consistent with Prop 0.0.38
- Beta function convention consistent with Thm 7.5.2 (different normalization, same physics)
- Updated c_FI consistent with Thm 7.7.3
- Prop 7.8.2 inputs correctly quoted and combined

### CONFIDENCE: Medium-High

The derivation is correct. The physical model is well-motivated and consistent with the literature. The main weakness is the alpha_s determination, which is more uncertain than presented. The overall conclusion -- that the Bethe-Salpeter approach gives R ~ 3.4, consistent with lattice -- is robust. The precise uncertainty (7% vs 10-12%) depends on how conservatively one treats the coupling.

---

## 13. RECOMMENDATIONS FOR IMPROVEMENT

1. **Compute two-loop alpha_s explicitly** at the glueball scale (871 MeV) to support the adopted value of 0.38. Show the calculation.

2. **Compute the glueball RMS radius** from the optimized wavefunction and verify it is below the adjoint string-breaking distance.

3. **Either expand the uncertainty** to delta(alpha_s) = 0.06 (conservative) or justify the tight range with an explicit two-loop calculation.

4. **Soften the self-consistency language** in Section 9.6. Replace "self-consistent" with "consistent within the scale uncertainty" and acknowledge the one-loop estimates are systematically higher.

5. **Correct the AFM benchmark reference** in Section 10.2 to cite the two-gluon Salpeter paper (Mathieu et al. PRD 70 (2004)) rather than the three-gluon paper (PRD 77 (2008)).

6. **Add a note** in Section 11.2 about the shared two-constituent glueball model assumption.

---

## References Consulted

- Athenodorou, A. & Teper, M. JHEP 11 (2020) 172. [arXiv:2007.06422](https://arxiv.org/abs/2007.06422)
- Bali, G.S. PRD 62 (2000) 114503. [hep-lat/0006022](https://www.researchgate.net/publication/1986441_Casimir_scaling_of_SU3_static_potentials)
- Morningstar, C. & Peardon, M. PRD 60 (1999) 034509. [hep-lat/9901004](https://arxiv.org/abs/hep-lat/9901004)
- Mathieu, V., Semay, C. & Silvestre-Brac, B. PRD 70 (2004) 014017
- Mathieu, V., Semay, C. & Silvestre-Brac, B. PRD 77 (2008) 094009. [arXiv:0803.0815](https://arxiv.org/abs/0803.0815)
- Boulanger, N. et al. EPJA 38 (2008) 317. [arXiv:0806.3875](https://www.researchgate.net/publication/225145181_Constituent_gluon_interpretation_of_glueballs_and_gluelumps)
- Silvestre-Brac, B. & Semay, C. JMP 46 (2005) 032302. [arXiv:1102.1321](https://arxiv.org/abs/1102.1321)
- Hong, D.K. et al. PLB 775 (2017) 89
- Necco, S. & Sommer, R. NPB 622 (2002) 328

---

*Verification completed: 2026-02-23*
*Agent: Claude Opus 4.6 (Independent Physics Verification)*
*Overall: PARTIAL VERIFICATION -- derivation correct, physics sound, uncertainty may be underestimated*
