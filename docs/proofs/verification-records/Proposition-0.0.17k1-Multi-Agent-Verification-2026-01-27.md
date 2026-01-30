# Multi-Agent Verification Report: Proposition 0.0.17k1

## One-Loop Correction to the Pion Decay Constant

**Verification Date:** 2026-01-27
**Document:** `docs/proofs/foundations/Proposition-0.0.17k1-One-Loop-Correction-To-Pion-Decay-Constant.md`
**Status:** **FAILED** — Critical arithmetic error invalidates headline result

---

## Executive Summary

| Agent | Verdict | Confidence |
|-------|---------|------------|
| Mathematical | **FAILED** | High |
| Physics | **FAILED** | Low (due to arithmetic error) |
| Literature | **PARTIAL** | Medium |

**Overall Assessment:** All three independent verification agents identified the same critical arithmetic error in §3.3 Step 4. The product 0.01490 × 8.606 = **0.1282**, not 0.0467 as claimed. The conceptual approach (applying standard ChPT one-loop corrections to a CG-derived tree-level value) is sound, but the numerical execution is incorrect. Additionally, there is a likely double-counting issue with the Gasser-Leutwyler formula: the scale-independent $\bar{\ell}_4$ should not be combined with a separate chiral logarithm.

**Key Finding:** The correct one-loop correction using the standard GL scale-independent formula $\delta = m_\pi^2/(16\pi^2 f^2) \times \bar{\ell}_4$ gives $\delta \approx 6.6\%$, yielding $f_\pi \approx 93.8$ MeV — overshooting PDG by ~1.9%. This is a known feature of one-loop SU(2) ChPT and does not invalidate the framework, but the 0.01σ pull claim is incorrect.

---

## 1. Mathematical Verification Results

### 1.1 Verified Components

| Component | Status | Notes |
|-----------|--------|-------|
| Logarithm (Step 1) | ✅ VERIFIED | ln(135²/1106²) = −4.207, document says −4.206 (rounding OK) |
| Combination (Step 2) | ✅ VERIFIED | 4.206 + 4.4 = 8.606 |
| Prefactor (Step 3) | ✅ VERIFIED | 2 × 135² / (2 × 1106²) = 0.01490 |
| Product (Step 4) | ❌ **WRONG** | 0.01490 × 8.606 = **0.1282**, not 0.0467 |
| Final value (Step 5) | ❌ **WRONG** | Depends on Step 4 |

### 1.2 Critical Errors

**ERROR 1: Arithmetic Error in Step 4 (CRITICAL)**
- **Location:** §3.3, Step 4 (line 119)
- **Problem:** 0.01490 × 8.606 = 0.1282, not 0.0467. Off by factor ~2.75.
- **Impact:** Invalidates the headline result $f_\pi = 92.1$ MeV and the 0.01σ pull claim.
- **Severity:** CRITICAL

**ERROR 2: Factor-of-2 Inconsistency Between §1 and §3.1 (HIGH)**
- **Location:** §1 (line 45) vs §3.1 (line 89)
- **Problem:** §1 has prefactor $N_f/(4\pi)^2 \times m_\pi^2/f^2$, while §3.1 has $N_f m_\pi^2/(2(4\pi f)^2)$. These differ by a factor of 2.
- **Impact:** The two stated formulas are inconsistent with each other.
- **Severity:** HIGH

**ERROR 3: Probable Double-Counting of Chiral Logarithm (HIGH)**
- **Location:** §3.1 and §3.3
- **Problem:** The document adds $-\ln(m_\pi^2/\mu^2) = +4.207$ to $\bar{\ell}_4 = 4.4$, getting 8.606. In the standard GL convention, $\bar{\ell}_4$ is **scale-independent** and already absorbs the logarithmic dependence. It should be used alone: $\delta = m_\pi^2/(16\pi^2 f^2) \times \bar{\ell}_4$. If one separates the log, one must use the **scale-dependent** $\ell_4^r(\mu)$, not $\bar{\ell}_4$.
- **Impact:** The formula structure appears to double-count, inflating the correction.
- **Severity:** HIGH

### 1.3 Correct Standard Result

Using the scale-independent GL formula for SU(2) ChPT:

$$\delta = \frac{m_\pi^2}{16\pi^2 f^2} \bar{\ell}_4 = \frac{135^2}{16\pi^2 \times 88^2} \times 4.4 = 0.01491 \times 4.4 = 0.0656$$

$$f_\pi^{(1\text{-loop})} = 88.0 \times 1.066 = 93.8 \text{ MeV}$$

This overshoots PDG (92.07 MeV) by ~1.9% — a known feature of one-loop SU(2) ChPT.

---

## 2. Physics Verification Results

### 2.1 Verified Components

| Check | Status | Notes |
|-------|--------|-------|
| Sign of correction (+) | ✅ VERIFIED | Positive correction is standard in ChPT |
| Chiral limit (m_π → 0) | ✅ VERIFIED | δ → 0, f_π → f_tree |
| Dimensional consistency | ✅ VERIFIED | All terms dimensionless |
| Scale independence (structure) | ✅ VERIFIED | GL guarantees μ-independence at O(p⁴) |
| Physical value of l̄₄ | ✅ VERIFIED | 4.4 ± 0.2 consistent with FLAG |

### 2.2 Issues Found

**ISSUE 1: Anharmonic Oscillator Analogy (MINOR)**
- §4.1 claims fluctuations "stiffen" the phase lock by analogy with anharmonic oscillators. The sign depends on the anharmonicity sign, which is not established from CG. The positive correction actually comes from l̄₄ > 0, an empirical input.

**ISSUE 2: CG → ChPT Mapping Not Derived (MODERATE)**
- §2.2 asserts (not derives) that CG phase fluctuations are identical to pion degrees of freedom. The three-bullet argument is qualitative. The verification checklist (§7) acknowledges this gap.

**ISSUE 3: CG-Specific O(p⁴) Corrections Not Addressed (MODERATE)**
- If CG has a different UV completion than QCD, the LECs (including l̄₄) could differ. Using the empirical l̄₄ implicitly assumes CG matches QCD at O(p⁴), which is unproven.

**ISSUE 4: Missing Domain-of-Validity Discussion (MINOR)**
- Heavy pion limit and large-N_f behavior not discussed.

### 2.3 Limit Checks

| Limit | Expected | Result | Status |
|-------|----------|--------|--------|
| Chiral (m_π → 0) | δ → 0 | δ ~ m_π² ln(m_π²) → 0 | ✅ PASS |
| Large N_f | δ grows, perturbation breaks | Formula gives linear N_f growth | ⚠️ NOT DISCUSSED |
| Heavy pion (m_π → Λ_χ) | Expansion breaks down | δ ~ O(1) | ⚠️ NOT DISCUSSED |
| N_f = 0 | No pion loops | δ = 0 | ✅ PASS |

### 2.4 Framework Consistency

- Tree-level value from Prop 0.0.17k: Minor inconsistency (88.0 vs 87.7 MeV in 17k)
- Use of empirical l̄₄ is honest (§6 declares it), but limits predictive power
- The proposition is a consistency check, not a first-principles derivation

---

## 3. Literature Verification Results

### 3.1 Citation Accuracy

| Reference | Status | Notes |
|-----------|--------|-------|
| Gasser & Leutwyler (1984) | ✅ VERIFIED | Ann. Phys. 158, 142 (1984) correct |
| Bijnens et al. | ⚠️ YEAR MISMATCH | Text says "(1999)" but refs list 1996/1997 papers |
| Scherer (2003) | ✅ VERIFIED | Adv. Nucl. Phys. 27, 277 (2003) correct |
| PDG 2024 | ✅ VERIFIED | Phys. Rev. D 110, 030001 (2024) correct |
| FLAG 2024 for √σ | ⚠️ IMPRECISE | √σ is a general lattice result, not standard FLAG output |

### 3.2 Experimental Data

| Value | Claimed | Reference Data | Status |
|-------|---------|----------------|--------|
| f_π (PDG) | 92.07 ± 0.57 MeV | 92.1 ± 0.6 MeV (PS convention) | ✅ VERIFIED |
| m_π | 135.0 MeV | 134.977 MeV (π⁰) | ✅ VERIFIED (approx.) |
| l̄₄ | 4.4 ± 0.2 | ~4.4 (FLAG, phenomenology) | ✅ VERIFIED |
| √σ | 440 ± 30 MeV | Standard lattice range | ✅ VERIFIED |

### 3.3 Missing References

1. **Colangelo, Gasser, Leutwyler (2001)**, Nucl. Phys. B 603, 125 — Precision l̄₄ from Roy equations
2. **FLAG reviews** for lattice LEC determinations — More relevant for l̄₄ than for √σ

### 3.4 Convention Check

The proposition uses $f_\pi \approx 92$ MeV (Peskin-Schroeder / physical convention), consistent with project standards (pdg-particle-data.md §3.1). **VERIFIED.**

---

## 4. Recommendations

### 4.1 Required Fixes (Before Re-verification)

1. **Fix the GL formula:** Use either:
   - Scale-independent: $\delta = m_\pi^2/(16\pi^2 f^2) \times \bar{\ell}_4$ (no separate log), OR
   - Scale-dependent: $\delta = m_\pi^2/(16\pi^2 f^2) \times [-\ln(m_\pi^2/\mu^2) + \ell_4^r(\mu) \times 32\pi^2]$ with proper $\ell_4^r$
2. **Fix the arithmetic** and propagate corrected values throughout
3. **Reconcile §1 and §3.1 formulas** (factor-of-2 discrepancy)
4. **Update the headline result:** With the correct standard formula, $f_\pi \approx 93.8$ MeV, overshooting PDG by ~1.9%. This should be discussed honestly.

### 4.2 Suggested Improvements

5. Correct Bijnens et al. year reference (1996/1997, not 1999)
6. Add Colangelo et al. (2001) reference for l̄₄
7. Add domain-of-validity discussion (m_π ≪ 4πf_π)
8. Note that 1-loop overshoot is a known feature of SU(2) ChPT
9. Derive (or outline) the CG → ChPT mapping in a companion document

---

## 5. Verification Metadata

| Field | Value |
|-------|-------|
| Verification method | Multi-agent adversarial review (3 agents) |
| Agents used | Mathematical, Physics, Literature |
| Critical errors found | 3 (arithmetic, formula inconsistency, double-counting) |
| Moderate issues | 3 (CG→ChPT mapping, CG-specific corrections, reference year) |
| Minor issues | 3 (analogy, domain, missing refs) |
| Computational verification | See `verification/verify_prop_0_0_17k1_adversarial.py` |
| Re-verification needed | Yes — after fixing identified errors |
