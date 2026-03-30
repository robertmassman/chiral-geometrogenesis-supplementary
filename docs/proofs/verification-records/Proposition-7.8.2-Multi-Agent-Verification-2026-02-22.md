# Multi-Agent Verification Report: Proposition 7.8.2
## Framework-Internal Glueball Mass Ratio

**Date:** 2026-02-22
**Target:** Proposition 7.8.2 (3-file structure: Statement, Derivation, Applications)
**Agents:** Literature, Mathematical (adversarial), Physics (adversarial)

---

## Overall Verdict

| Agent | Verified | Confidence | Key Finding |
|-------|----------|------------|-------------|
| Literature | Partial | Medium-High | Citations mostly accurate; minor gaps in references |
| Mathematical | Partial | Medium-High | Core algebra verified; numerical table errors; subtle circularity in Delta |
| Physics | Partial | Medium-High | Physics sound; N-ality interpretation needs correction; error budget may be underestimated |

**Consolidated Status: PARTIAL — sound core result with correctable issues**

The central result $R_\text{cont}^{\text{FI}} = 3.42 \pm 0.22$ is robust and consistent with lattice data at $0.07\sigma$. All three agents agree that the core derivation is correct but flag issues that should be addressed before upgrading the status.

---

## 1. Literature Verification Agent

### 1.1 Citation Accuracy

| Ref | Paper | Claim Verified? | Notes |
|-----|-------|-----------------|-------|
| [1] | Athenodorou & Teper, JHEP 11 (2020) 172 | **Yes** | $R_\text{cont} = 3.405 \pm 0.021$ confirmed; current best value |
| [2] | Necco & Sommer, NPB 622 (2002) | **Partial** | $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994$ is **derived** from $r_0\Lambda = 0.602$, not directly quoted |
| [3] | Morningstar & Peardon, PRD 60 (1999) | **Yes** | Correctly cited as context |
| [4] | Ishikawa et al., JHEP 12 (2017) | **Issue** | Listed but **never used** in the text |
| [5] | Bali, PRD 62 (2000) | **Partial** | $\sigma_8/\sigma_3 = 2.26 \pm 0.06$ is a reasonable interpretation, not a direct quote |
| [6] | Athenodorou & Teper, JHEP 12 (2021) | **Yes** | Missing article number: should be "JHEP 12 (2021) **082**" |
| [7] | Buisseret et al., PLB 873 (2026) | **Yes** | Correctly cited; supports Casimir scaling formula |
| [8] | Hong et al., PLB 775 (2017) 89 | **Yes** | Correctly cited; note they use mass-squared form |

### 1.2 Standard Results Verified

- $C_2(\mathbf{3}) = 4/3$ and $C_2(\mathbf{8}) = 3$: **Correct** (standard SU(3) Lie algebra)
- $\mathbf{8} \otimes \mathbf{8} = \mathbf{1} \oplus \mathbf{8}_S \oplus \mathbf{8}_A \oplus \mathbf{10} \oplus \overline{\mathbf{10}} \oplus \mathbf{27}$: **Correct** (dimensions sum to 64)
- $b_0 = 11/(16\pi^2)$: **Correct** (one-loop SU(3) Yang-Mills)
- Constituent gluon model: **Established** approach in the literature

### 1.3 Missing References

| Reference | Why It Should Be Cited |
|-----------|----------------------|
| Buisseret, Mathieu & Semay, EPJA 27 (2006) 225 | Earliest systematic Casimir scaling for glueballs by [7] authors |
| Boulanger, Buisseret, Mathieu & Semay, EPJA 38 (2008) 317 | Constituent gluon interpretation of glueballs |
| Dalla Brida & Ramos, EPJC 79 (2019) 435 | Modern $\Lambda_{\overline{\text{MS}}}$ determination (gradient flow) |
| Lucini, Teper & Wenger, JHEP 06 (2004) 012 | Earlier SU($N$) glueball spectrum |
| Specific refs for AdS/CFT and SVZ sum rules entries in §11.4 comparison table | Currently uncited |

### 1.4 Suggested Updates

1. Complete [6] citation with article number 082
2. Add footnote that $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994$ is derived from Necco-Sommer $r_0\Lambda$
3. Note explicitly that Hong et al. [8] use mass-squared form of Casimir scaling
4. Either use or remove reference [4] (Ishikawa et al.)
5. Add specific references for AdS/CFT and sum rules entries in §11.4

---

## 2. Mathematical Verification Agent

### 2.1 Re-Derived Equations

| Equation | Claim | Re-derived Value | Status |
|----------|-------|------------------|--------|
| Eq 5.8 | $\sigma_8/\sigma_3 \to 2$ | 2 (from leading-order ratio) | **VERIFIED** |
| Eq 5.11 | $\sigma_8/\sigma_3 \to 9/4$ | $C_2(8)/C_2(3) = 9/4$ | **VERIFIED** |
| Eq 6.8 | $M_0^{\text{SC}} = 2$ | 2 (algebraically exact in model) | **VERIFIED** |
| Eq 6.9 | $R_\text{cont}^{\text{SC}} = 3.0$ | $2 \times 3/2 = 3.0$ | **VERIFIED** |
| Eq 7.2 | $\Delta_1 = 0.126$ | $(1/2)(1/1.994)^2 = 0.1258$ | **VERIFIED** |
| Eq 7.5 | $\Delta_2 = 0.0664$ | $(3/(2\pi))\sqrt{b_0 \cdot I_\text{FCC}} = 0.0662$ | **VERIFIED** |
| Eq 8.2 | $R_\text{cont}^{\text{FI}} = 3.42$ | $2.0 \times 1.14 \times 1.5 = 3.42$ | **VERIFIED** |
| Eq 8.3 | $\delta R = 0.21$ | $2.0 \times 0.07 \times 1.5 = 0.21$ | **VERIFIED** |
| Eq 8.5 | Tension $= 0.068\sigma$ | $0.015/0.22 = 0.0682$ | **VERIFIED** |
| Eq 8.7 | $c_\text{FI} = 6.82$ | $3.42 \times 1.994 = 6.8195$ | **VERIFIED** (should round to 6.82, not 6.81) |
| Eq 8.10 | $\delta c = 0.445$ | $6.82 \times 0.06519 = 0.4446$ | **VERIFIED** |
| Eq 1.12 | $c_\text{lat} = 6.79$ | $3.405 \times 1.994 = 6.7896$ | **VERIFIED** |

### 2.2 Errors Found

| ID | Severity | Description | Location |
|----|----------|-------------|----------|
| E-1 | MINOR | Rounding inconsistency: $3.42 \times 1.994 = 6.8195$ rounds to 6.82, not 6.81 as stated | Eqs (1.11), (8.11) |
| E-2 | MODERATE | Monotonicity of $\sigma_8/\sigma_3$ claimed without proof; numerical table appears non-monotonic | Derivation §5.4 |
| E-3 | MODERATE | Numerical table values at large $\beta$ inconsistent with weak-coupling formula. At $\beta=100$: table gives $\sigma_3 = 0.069$ but weak-coupling predicts $\sigma_3 \approx 0.0067$ | Derivation §5.4 |

### 2.3 Warnings

| ID | Severity | Description | Location |
|----|----------|-------------|----------|
| W-1 | MODERATE | Constituent gluon model assumptions (two-body, unit proportionality, partial cancellation) are model inputs, not derived | §6.2–6.4 |
| W-2 | MODERATE | Monotonicity claim references "convexity of heat kernel" but proof not provided | §5.4 |
| W-3 | **MAJOR** | $\Delta_3 = 0.135$ uses lattice $R_\text{cont}^{\text{lat}} = 3.405$ directly. Central value $\Delta = 0.14$ is calibrated to lattice extraction. Two genuinely independent estimates ($\Delta_1 = 0.126$, $\Delta_2 = 0.066$) have midpoint $\sim 0.096$, which would give $R_\text{cont}^{\text{FI}} \approx 3.29$ | §7.4–7.5, §3.4 |
| W-4 | MINOR | SU($N$) tensions in §11.2 use only lattice error, not framework error in quadrature | §11.2 |
| W-5 | MINOR | "$M_0^{\text{SC}} = 2$ (exact)" could mislead; exact only within model assumptions | §6.3 |

### 2.4 Key Concern: Subtle Circularity in $\Delta$

The circular reasoning avoidance table (§3.4) claims $\Delta$ does not use lattice $R_\text{cont}$. However:

- $\Delta_3 = (M_0^{\text{lat}}(3) - 2)/2 = (3.405/1.5 - 2)/2 = 0.135$ **directly uses** $R_\text{cont}^{\text{lat}}$
- The central value $\Delta = 0.14$ is "chosen to match the SU(3) lattice extraction" (§7.5)
- The two genuinely independent estimates: $\Delta_1 = 0.126$ and $\Delta_2 = 0.066$ (midpoint $\sim 0.096$)
- With $\Delta = 0.096$: $R_\text{cont}^{\text{FI}} = 2.0 \times 1.096 \times 1.5 = 3.288$, still consistent at $0.55\sigma$

**Impact:** The qualitative conclusion ($R_\text{cont}^{\text{FI}}$ consistent with lattice) survives, but the excellent $0.07\sigma$ agreement is partly due to calibration.

---

## 3. Physics Verification Agent

### 3.1 Physical Consistency Checks

| Check | Result |
|-------|--------|
| $R_\text{cont}^{\text{FI}} = 3.42$ in physically reasonable range? | **YES** (lattice: 3.405, other semi-analytic: 3.0–3.6) |
| Constituent gluon model physically motivated? | **YES** (established approach, supported by Buisseret et al.) |
| Glueballs emerge only at $\varepsilon > 0$? | **YES** (correctly argued from block-diagonal transfer matrix) |
| Connected correlator vanishes at $t > 0$ for $\varepsilon = 0$? | **YES** (from global label constraint) |
| Hierarchy $m(0^{++}) > \sqrt{\sigma}$? | **YES** ($R = 3.42 > 1$) |

### 3.2 Limit Checks

| Limit | Expected | Obtained | Status |
|-------|----------|----------|--------|
| $\beta \to 0$ (strong coupling) | $\sigma_8/\sigma_3 \to 2$ | 2 (from character expansion) | **PASS** (math correct, N-ality interpretation wrong) |
| $\beta \to \infty$ (weak coupling) | $\sigma_8/\sigma_3 \to 9/4$ | $9/4 = 2.25$ | **PASS** |
| $\Delta \to 0$ | $R = 3.0$ | $2 \times 1 \times 1.5 = 3.0$ | **PASS** |
| $\Delta \to 0.07$ ($1\sigma$ low) | $R = 3.21$ | $2 \times 1.07 \times 1.5 = 3.21$ | **PASS** |
| $\Delta \to 0.21$ ($1\sigma$ high) | $R = 3.63$ | $2 \times 1.21 \times 1.5 = 3.63$ | **PASS** |
| Large $N$ ($N \to \infty$) | $M_0 = 2$, $\eta \to \sqrt{2}$, $R \to 2\sqrt{2} = 2.83$ | Consistent with lattice trend | **PASS** |

### 3.3 Experimental Tensions

| Quantity | Framework Value | Lattice Value | Tension | Status |
|----------|----------------|---------------|---------|--------|
| $R_\text{cont}$ (SU(3)) | $3.42 \pm 0.22$ | $3.405 \pm 0.021$ | $0.07\sigma$ | **PASS** |
| $c_\text{FI}$ | $6.81 \pm 0.50$ | $6.78 \pm 0.31$ | $0.05\sigma$ | **PASS** |
| $\sigma_8/\sigma_3$ (scaling window) | $9/4 = 2.25$ | $2.26 \pm 0.06$ (Bali) | $0.17\sigma$ | **PASS** |
| $M_0$ | $2.28 \pm 0.14$ | $2.282 \pm 0.013$ (wt. mean) | $0.01\sigma$ | **PASS** |
| $R_\text{cont}$ (SU(4)) | 3.33 | $3.52 \pm 0.11$ | $1.7\sigma$ | **WARNING** |
| $R_\text{cont}$ (SU(5)) | 3.29 | $3.55 \pm 0.14$ | $1.9\sigma$ | **WARNING** |

### 3.4 Physical Issues

| ID | Severity | Description |
|----|----------|-------------|
| P-1 | **MODERATE** | **N-ality interpretation incorrect.** The strong-coupling ratio $\sigma_8/\sigma_3 = 2$ is attributed to "N-ality scaling with $k_8 = 2$" but the adjoint has N-ality **0** for SU(3). The ratio 2 arises from the order of the character expansion ($\beta^2$ vs $\beta^1$), not from N-ality. |
| P-2 | **MODERATE** | **Numerical table does not converge to 9/4.** At $\beta = 500$, ratio is 1.969 instead of approaching 2.25. Either the table uses wrong formulas at large $\beta$, or the approximation switches between regimes. |
| P-3 | **MODERATE** | **Error budget underestimated.** $M_0^{\text{SC}} = 2$ assumed exact; no systematic for constituent gluon proportionality constant. Adding 5% systematic on $M_0^{\text{SC}}$ would increase $\delta R$ from 0.22 to ~0.27. |
| P-4 | LOW | **Partial circularity in $\Delta_3$** (same as math agent W-3). |
| P-5 | MINOR | **Rounding inconsistency** $c_\text{FI} = 6.81$ vs computed 6.82. |

### 3.5 Framework Consistency

| Cross-reference | Status |
|----------------|--------|
| Thm 7.7.3 (Mass Gap Bound) | **CONSISTENT** ($c_\text{FI} = 6.81$ vs $c_\text{lat} = 6.78$) |
| Prop 7.8.1 (Casimir Scaling) | **CONSISTENT** ($M_0 = 2.28$ vs 2.33, $0.34\sigma$) |
| Prop 0.0.38 (FCC Partition Function) | **CONSISTENT** (heat kernel eigenvalues correctly used) |
| Thm 7.5.3 (Crossover Path) | **CONSISTENT** (representation mixing correctly used) |
| Thm 7.6.5 (UV Stability) | **CONSISTENT** ($I_\text{FCC} = 0.276$ correctly referenced) |
| Thm 7.5.2 (Perturbative Universality) | **CONSISTENT** ($b_0 = 11/(16\pi^2)$ correct) |

---

## 4. Consolidated Findings

### 4.1 Issues Requiring Action (by severity)

| Priority | Issue | Agents | Recommended Action |
|----------|-------|--------|-------------------|
| **HIGH** | $\Delta_3$ uses lattice $R_\text{cont}$ — subtle circularity not flagged in §3.4 | Math (W-3), Physics (P-4) | Distinguish "framework-internal" ($\Delta_1$, $\Delta_2$) from "lattice-calibrated" ($\Delta_3$) estimates in §7.5 and §3.4 |
| **MODERATE** | N-ality interpretation wrong in §5.2 | Physics (P-1) | Replace "N-ality scaling with $k_8 = 2$" with correct character expansion explanation |
| **MODERATE** | Numerical table in §5.4 has errors at large $\beta$ | Math (E-2, E-3), Physics (P-2) | Recompute table using exact heat kernel values or correct formula switching |
| **MODERATE** | Monotonicity claimed without proof | Math (E-2, W-2) | Either provide proof or weaken to "numerical evidence suggests" |
| **MODERATE** | Error budget missing $M_0^{\text{SC}}$ systematic | Physics (P-3) | Consider adding 5% systematic on $M_0^{\text{SC}}$ |
| MINOR | Rounding: $c_\text{FI} = 6.81$ vs 6.82 | Math (E-1), Physics (P-5) | Standardize to 6.82 |
| MINOR | [6] missing article number 082 | Literature | Add article number |
| MINOR | [4] Ishikawa et al. unused | Literature | Remove or add context |
| MINOR | Missing prior work citations | Literature | Add Buisseret (2006), Boulanger et al. (2008) |

### 4.2 What the Proposition Gets Right

1. **Core derivation is algebraically correct** — all key equations independently verified
2. **$M_0^{\text{SC}} = 2$ identity is elegant** — group-independent, exact within the model
3. **Framework consistency is excellent** — cross-checks with Thm 7.7.3, Prop 7.8.1 all pass
4. **Honest about limitations** — §9.2 and §11.3 are commendably forthright
5. **Physically sound approach** — constituent gluon model + Casimir scaling is well-established
6. **Goal achieved** — external MC inputs reduced from 2 to 1

### 4.3 Impact on Status

The issues found do **not** invalidate the result. The central value $R_\text{cont}^{\text{FI}} = 3.42 \pm 0.22$ is robust:
- Even using only genuinely independent $\Delta$ estimates ($\Delta \sim 0.096$), the result $R_\text{cont}^{\text{FI}} \approx 3.29 \pm 0.21$ is consistent with lattice at $0.55\sigma$
- The conclusion $c_\text{FI} > 0$ (mass gap) is unaffected
- Framework consistency with all prerequisite theorems holds

**Recommended status after corrections:** 🔶 NOVEL ✅ VERIFIED (pending Lean 4 formalization for full verification)

---

## 5. Verification Scripts

- **Adversarial verification:** `verification/Phase7/verify_prop_7_8_2_adversarial.py`
- **Exact heat kernel table:** `verification/Phase7/compute_exact_heat_kernel_table.py`
- **Plots:** `verification/plots/prop_7_8_2_*.png`

---

## 6. Corrections Applied (2026-02-22)

All 9 consolidated findings from §4.1 have been addressed:

| # | Issue | Resolution | New Value |
|---|-------|------------|-----------|
| 1 | $\Delta_3$ circularity (HIGH) | Restructured §7.5: Tier 1 (FI) vs Tier 2 (lattice-calibrated); recentered $\Delta$ on $\Delta_1$ | $\Delta = 0.126 \pm 0.07$ |
| 2 | N-ality interpretation (MODERATE) | Replaced with character expansion explanation; adjoint N-ality = 0 | §5.2 rewritten |
| 3 | Numerical table errors (MODERATE) | Recomputed with exact SU(3) heat kernel integration | Table now converges to $9/4$ at large $\beta$ |
| 4 | Monotonicity without proof (MODERATE) | Weakened to "monotonic in scaling window; shallow minimum near $\beta \approx 0.5$" | §5.4, §1.1 updated |
| 5 | Missing $M_0^{\text{SC}}$ systematic (MODERATE) | Added 5% systematic on proportionality constant $c$ | $\delta R$: $0.21 \to 0.27$ |
| 6 | Rounding $c_\text{FI}$ (MINOR) | All values recomputed consistently | $c_\text{FI} = 6.74 \pm 0.55$ |
| 7 | [6] article number (MINOR) | Added JHEP 12 (2021) 082 | — |
| 8 | [4] unused (MINOR) | Cited in §7.2 as alternative $\Lambda_{\overline{\text{MS}}}$ determination | — |
| 9 | Missing citations (MINOR) | Added [9] Boulanger et al. (2008), [10] Dalla Brida & Ramos (2019); expanded notes on [2], [5], [7], [8] | — |

**Post-correction key results:**
- $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$ (was $3.42 \pm 0.22$)
- Tension with lattice: $0.09\sigma$ (was $0.07\sigma$)
- $c_\text{FI} = 6.74 \pm 0.55$ (was $6.81 \pm 0.50$)
- Conservative 3σ lower bound: $c_\text{low} = 4.96$ (was $4.75$; improved due to recentering)

The central result is modestly shifted ($-1.2\%$) with a larger error bar ($+23\%$), reflecting more honest treatment of the circularity and systematic uncertainties. The qualitative conclusion ($R_\text{cont}^{\text{FI}}$ consistent with lattice, $c > 0$) is robust.

---

*Report generated by multi-agent adversarial review system, 2026-02-22.*
*Corrections applied 2026-02-22.*
