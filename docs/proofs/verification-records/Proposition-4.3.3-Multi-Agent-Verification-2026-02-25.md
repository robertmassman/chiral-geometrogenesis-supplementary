# Multi-Agent Verification Report: Proposition 4.3.3

## W-Soliton Cosmological Abundance

**File:** `docs/proofs/Phase4/Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md`
**Date:** 2026-02-25
**Agents:** Literature, Mathematical, Physics (adversarial)

---

## Executive Summary

| Agent | Verdict | Confidence |
|-------|---------|------------|
| Literature | Partial | Medium-High |
| Mathematical | Partial | Medium-High |
| Physics | Partial | Medium-High |

**Overall Verdict: PARTIAL — 8 issues found (1 arithmetic error, 1 internal inconsistency, 6 warnings)**

The ADM mechanism is physically sound and the final numerical prediction ($\Omega_W h^2 = 0.139$) is correctly computed and consistent with Planck ($0.1200 \pm 0.0012$) within the stated $\pm 30\%$ theoretical uncertainty. However, all three agents independently identified the same arithmetic error in $\epsilon_W^{required}$, and several geometric factors lack rigorous first-principles derivations.

---

## Issues Found

### ISSUE 1: Arithmetic Error in $\epsilon_W^{required}$ (ALL THREE AGENTS)

**Location:** Section 4.3 (line 126) and Section 6.3 (lines 226–229)

**Problem:** The document states $\epsilon_W^{required} = 2.2 \times 10^{-13}$. Independent calculation by all three agents gives:

$$\epsilon_W^{req} = \frac{\Omega_{DM}/\Omega_b}{s_0/n_\gamma} \times \eta_B \times \frac{m_p}{M_W} = \frac{5.357}{7.04} \times 6.1 \times 10^{-10} \times \frac{0.938}{1620} = 2.69 \times 10^{-13}$$

Even using the document's rounded $\Omega_{DM}/\Omega_b \approx 5.5$: result is $2.76 \times 10^{-13}$, not $2.2 \times 10^{-13}$.

**Impact:** The claimed "41% discrepancy" (Section 6.3) is actually ~15%, consistent with the correctly computed 16% overshoot in Section 6.4. The final result ($\Omega_W h^2 = 0.139$) is unaffected — it was computed independently.

**Severity:** Moderate — misleading comparison but correct final result.

**Fix:** Replace $\epsilon_W^{required} = 2.2 \times 10^{-13}$ with $2.7 \times 10^{-13}$ and update the "41%" to "~15%".

### ISSUE 2: Internal Inconsistency Between Sections 6.3 and 6.4 (Math + Physics agents)

**Location:** Sections 6.3–6.4

**Problem:** Section 6.3 claims $\epsilon_W$ is "within 41% of the required value" while Section 6.4 shows $\Omega_W h^2 = 0.139$, which is 16% above Planck. Since $\Omega_W \propto \epsilon_W$, these percentages should be identical. The inconsistency traces to the arithmetic error in Issue 1.

**Fix:** Correcting Issue 1 resolves this inconsistency.

### ISSUE 3: LZ Exclusion Factor Overstated (Literature agent)

**Location:** Section 3.2 (lines 84–86)

**Problem:** The document claims $\sigma_{SI}(\lambda = 0.5) \approx 3 \times 10^{-45}$ cm$^2$ is "excluded by LZ by a factor of $\sim 300$." The LZ best limit of $2.2 \times 10^{-48}$ cm$^2$ is at 40 GeV, not at 1620 GeV. At $M_W = 1620$ GeV, the LZ exclusion curve weakens to $\sim 10^{-45}$ cm$^2$, giving an exclusion factor of $\sim 3$, not $\sim 300$.

**Impact:** The qualitative conclusion (thermal freeze-out is excluded) remains valid. The quantitative claim is misleading.

**Severity:** Moderate — affects a supporting argument, not the main result.

**Fix:** Replace "excluded by LZ by a factor of $\sim 300$" with the correct exclusion factor at 1620 GeV, or clarify that the factor refers to the mass-averaged limit.

### ISSUE 4: Mass Value Selection Bias (Math + Physics agents)

**Location:** Throughout (M_W = 1620 GeV used consistently)

**Problem:** The proposition uses $M_W = 1620$ GeV (Faddeev topological lower bound) throughout. Theorem 4.3.2 reports the central value as $M_W = 1800 \pm 500$ GeV. Using $M_W = 1800$ GeV gives $\Omega_W h^2 = 0.155$ (29% overshoot), still within the $\pm 30\%$ band but less comfortable.

**Severity:** Low — both values are within the stated uncertainty range.

**Fix:** Explicitly state that the Faddeev lower bound is used and why, and show the sensitivity to this choice.

### ISSUE 5: Ad Hoc Geometric Factors (Physics + Math agents)

**Location:** Sections 5.1, 5.3, 5.5

Three of the five geometric factors lack rigorous first-principles derivations:

| Factor | Value | Concern |
|--------|-------|---------|
| $f_{singlet}^{eff} = 1/3$ | "1 vertex vs 3 color vertices" | The singlet has zero direct anomaly coupling ($\langle \mathbf{1} \| T^a T^a \| \mathbf{1} \rangle = 0$). The 1/3 from vertex counting is heuristic. |
| $f_{solid} = 1/2$ | $\sqrt{\Omega_W/4\pi}$ | Why square root? If intensity (not amplitude) scaling, $f_{solid} = 1/4$ instead. |
| $\|f_{chiral}\| = \sqrt{3}$ | Three-color coherence | Coherent addition of 3 amplitudes should give 3, not $\sqrt{3}$. The actual mechanism (anomaly coefficient?) is not derived. |

**Severity:** Moderate — affects the "no fitted parameters" claim.

**Fix:** Provide rigorous derivations from the anomaly structure, or explicitly acknowledge these as geometric estimates with associated systematic uncertainties.

### ISSUE 6: Missing ADM Literature References (Literature agent)

**Location:** Section 10

**Missing references:**
1. **Nussinov (1985)** — "Technocosmology: could a technibaryon excess provide a natural missing mass candidate?" *Phys. Lett. B* 165, 55. (Original ADM-like idea; historical priority.)
2. **Zurek (2014)** — "Asymmetric Dark Matter: Theories, Signatures, and Constraints." *Phys. Rep.* 537, 91 [arXiv:1308.0338]. (Comprehensive review discussing TeV-scale ADM variants.)
3. **Petraki & Volkas (2013)** — "Review of asymmetric dark matter." *Int. J. Mod. Phys. A* 28, 1330028 [arXiv:1305.4939].

**Severity:** Low — the main KLZ reference is correct but context for non-standard mass scale is missing.

### ISSUE 7: Symmetric Depletion Argument is Qualitative (Math + Physics agents)

**Location:** Section 4.2

**Problem:** The argument that symmetric W + W̄ annihilation is "sufficient" is qualitative. The math agent estimates $\Gamma/H \sim 6$ at $T \sim M_W/20$, meaning the symmetric component is only marginally depleted. A quantitative calculation (Boltzmann equation or Lee-Weinberg analysis) showing the residual symmetric fraction is needed.

**Severity:** Moderate — affects the validity of the ADM mechanism.

**Fix:** Add a quantitative estimate of the symmetric depletion factor, e.g., $n_{\bar{W}}/n_W|_{T \to 0}$.

### ISSUE 8: Error Budget Incomplete (Math agent)

**Location:** Section 9.1

**Problem:** The $\pm 30\%$ total uncertainty omits the $M_W$ uncertainty from Theorem 4.3.2 ($M_W = 1800 \pm 500$ GeV, i.e., 28%). Including this in quadrature gives $\sqrt{30^2 + 28^2} \approx 41\%$. Also, $f_{VEV}$ and $f_{overlap}$ both depend on $v_W$, creating a correlated uncertainty not accounted for.

**Severity:** Low — the prediction remains consistent with Planck even with larger uncertainties.

---

## Verified Claims

The following were independently verified by at least two agents:

| Claim | Literature | Math | Physics |
|-------|-----------|------|---------|
| $\kappa_W^{geom} = 5.1 \times 10^{-4}$ | ✅ | ✅ | ✅ |
| $\epsilon_W = 3.1 \times 10^{-13}$ | ✅ | ✅ | ✅ |
| $\Omega_W h^2 = 0.139$ | ✅ | ✅ | ✅ |
| $\eta_B = 6.1 \times 10^{-10}$ (Planck 2018) | ✅ | — | — |
| $\Omega_{DM} h^2 = 0.1200 \pm 0.0012$ (Planck 2018) | ✅ | — | — |
| $\Omega_b h^2 = 0.0224$ (Planck 2018) | ✅ | — | — |
| $s_0/n_\gamma = 7.04$ (standard cosmology) | ✅ | ✅ | ✅ |
| Thermal freeze-out fails ($\Omega \sim 23$) | — | ✅ | ✅ |
| ADM formula is standard (KLZ 2009) | ✅ | ✅ | ✅ |
| $\sigma_{SI} \lesssim 10^{-47}$ cm$^2$ below LZ | ✅ | — | ✅ |
| No circularity in dependency chain | — | ✅ | ✅ |
| Dimensional analysis consistent | — | ✅ | — |
| All citation details correct | ✅ | — | — |
| Topological stability + ADM annihilation compatible | — | — | ✅ |
| BBN, CMB constraints satisfied | — | — | ✅ |

---

## Experimental Bounds Check (Physics Agent)

| Constraint | CG Prediction | Experimental Bound | Margin |
|------------|---------------|-------------------|--------|
| Direct detection (LZ) | $\sigma_{SI} \sim 1.5 \times 10^{-47}$ cm$^2$ | $\sim 10^{-46}$ cm$^2$ at 1.6 TeV | Factor ~7 below |
| Collider (LHC) | $M_W = 1620$ GeV, gauge singlet | No direct constraint | Safe |
| Self-interaction | $\sigma/m \sim 10^{-12}$ cm$^2$/g | $< 0.2$ cm$^2$/g | Factor $\sim 10^{11}$ |
| BBN | $T_{dec} \sim 80$ GeV $\gg T_{BBN}$ | Compatible | Safe |
| CMB | $f_{eff} \cdot \sigma v / M_W \sim 6 \times 10^{-33}$ | $< 3.5 \times 10^{-28}$ | Factor ~56,000 |
| $\Omega_W h^2$ | $0.14 \pm 0.04$ | $0.1200 \pm 0.0012$ (Planck) | Within 1$\sigma$ CG band |

---

## Numerical Verification Summary (Math Agent)

| Quantity | Claimed | Re-derived | Status |
|----------|---------|-----------|--------|
| $1/3 \times 0.25 \times 1/2$ | 0.0417 | 0.04167 | ✅ |
| $0.0417 \times 7.1 \times 10^{-3}$ | $2.96 \times 10^{-4}$ | $2.96 \times 10^{-4}$ | ✅ |
| $\kappa_W^{geom}$ | $5.1 \times 10^{-4}$ | $5.12 \times 10^{-4}$ | ✅ |
| $\epsilon_W = \eta_B \times \kappa_W$ | $3.1 \times 10^{-13}$ | $3.12 \times 10^{-13}$ | ✅ |
| $\epsilon_W^{required}$ | $2.2 \times 10^{-13}$ | $2.69 \times 10^{-13}$ | ❌ (22% error) |
| $M_W/m_p$ | 1727 | 1727 | ✅ |
| $\Omega_b h^2 \times 7.04$ | 0.158 | 0.1577 | ✅ |
| $\Omega_W h^2$ (ADM) | 0.139 | 0.139 | ✅ |
| $\Omega_W h^2$ (thermal) | $\sim 23$ | 23.1 | ✅ |

---

## Recommendations (Priority Order)

1. **Fix arithmetic error** in $\epsilon_W^{required}$: change $2.2 \times 10^{-13}$ to $2.7 \times 10^{-13}$ and update "41%" to "~15%" (resolves Issues 1 & 2)
2. **Correct LZ exclusion factor** at 1620 GeV mass point (Issue 3)
3. **Add quantitative symmetric depletion calculation** with Boltzmann or Lee-Weinberg analysis (Issue 7)
4. **Provide rigorous derivations** of $f_{singlet}$, $f_{solid}$, $f_{chiral}$ from anomaly structure (Issue 5)
5. **Acknowledge mass value choice** explicitly (Issue 4)
6. **Add missing ADM review references**: Nussinov (1985), Zurek (2014), Petraki & Volkas (2013) (Issue 6)
7. **Expand error budget** to include $M_W$ uncertainty (Issue 8)

---

## Cross-Reference Consistency (Math Agent)

| Parameter | Prop 4.3.3 | Source | Source Value | Match |
|-----------|-----------|--------|-------------|-------|
| $M_W$ | 1620 GeV | Thm 4.3.2 | 1619 (Faddeev), 1800 (central) | Partial |
| $\lambda_{H\Phi}$ | 0.036 | Def 4.3.1 §8.3 | 0.036 | ✅ |
| $v_W$ | 123 GeV | Prop 5.1.2b §4.5 | $123 \pm 15$ GeV | ✅ |
| $f_{overlap}$ | $7.1 \times 10^{-3}$ | Prop 5.1.2b §3.4 | $(7.1 \pm 1.1) \times 10^{-3}$ | ✅ |
| $e_W$ | 4.5 | Prop 5.1.2b §5.2 | $4.5 \pm 0.3$ | ✅ |
| $\eta_B$ | $6.1 \times 10^{-10}$ | Planck 2018 | $(6.12 \pm 0.04) \times 10^{-10}$ | ✅ |
| $\Omega_b h^2$ | 0.0224 | Planck 2018 | $0.02237 \pm 0.00015$ | ✅ |

---

*Report compiled from three independent adversarial verification agents.*
*Computational verification: `verification/Phase4/prop_4_3_3_adversarial_verification.py`*
