# Proposition 7.8.2: Framework-Internal Glueball Mass Ratio — Applications

**Parent document:** [Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md)

This file contains the impact assessment, verification checklist, cross-checks, and references for Proposition 7.8.2.

---

## §9. Impact on Mass Gap Proof

### §9.1 Theorem 7.7.3 Upgrade

Theorem 7.7.3 Part (c) gives the quantitative mass gap bound:

$$m_\text{phys} \geq c \cdot \Lambda_{\overline{\text{MS}}} \quad \text{with} \quad c = R_\text{cont} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} \tag{9.1}$$

Previously, both $R_\text{cont}$ and $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ were external lattice MC inputs. With Prop 7.8.2 Part (d), the bound can be restated as:

$$m_\text{phys} \geq c_\text{FI} \cdot \Lambda_{\overline{\text{MS}}} \quad \text{with} \quad c_\text{FI} = R_\text{cont}^{\text{FI}} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} = 6.74 \pm 0.55 \tag{9.2}$$

where $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$ is framework-internal and only $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ remains external.

**Conservative lower bound** (at $3\sigma$ confidence):

$$c_{\text{FI},\text{low}} = (R_\text{cont}^{\text{FI}} - 3\delta R^{\text{FI}}) \times \left(\frac{\sqrt{\sigma}}{\Lambda}\right)_\text{low} = (3.38 - 0.81) \times (1.994 - 0.063) = 2.57 \times 1.931 = 4.96 \tag{9.3}$$

This is weaker than Thm 7.7.3's $c_\text{low} = 5.75$ but still firmly establishes $c > 0$, which is the essential requirement for the mass gap.

### §9.2 Theorem 7.7.5 Strengthening

Theorem 7.7.5 (self-contained mass gap proof) lists external lattice MC inputs as a caveat. Prop 7.8.2 reduces this from "two external MC inputs" to "one external MC input ($\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$)." This strengthens the self-containedness of the proof by eliminating the dependence on the glueball spectrum computation (which requires large-scale Monte Carlo simulations with operator optimization, smearing, and variational analysis).

The remaining input $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ is in principle computable from the two-loop beta function and the non-perturbative strong-coupling partition function, but this computation (Plan §12.2 Item G) is significantly harder and is left for future work.

### §9.3 Strengthening Program Implications

| Item | Before Prop 7.8.2 | After Prop 7.8.2 |
|------|-------------------|-------------------|
| F (Analytic $R_\text{cont}$) | Open | ✅ Partially Resolved |
| G (Explicit $\mu_\text{min}$) | Open | Open (unaffected) |
| External MC inputs to Thm 7.7.3 | 2 | 1 |
| Self-containedness | Relies on glueball MC + scale setting MC | Relies on scale setting MC only |

---

## §10. Verification Status and Test Checklist

### §10.1 Standard Tests (C-1 through C-14)

| ID | Description | Status |
|----|-------------|--------|
| C-1 | Casimir scaling at weak coupling: $\sigma_8/\sigma_3 \to 9/4$ as $\beta \to \infty$ | PASS |
| C-2 | Strong-coupling ratio: $\sigma_8/\sigma_3 \to 2$ as $\beta \to 0$ (character expansion order) | PASS |
| C-3 | Monotonic increase of $\sigma_8/\sigma_3$ in scaling window; shallow minimum near $\beta \approx 0.5$ | PASS |
| C-4 | $M_0^{\text{SC}} = 2$ exact within constituent gluon model | PASS |
| C-5 | $R_\text{cont}^{\text{SC}} = M_0^{\text{SC}} \times \eta(\text{SU}(3)) = 3.0$ | PASS |
| C-6 | $R_\text{cont}^{\text{FI}} = 3.38$ within $1\sigma$ of lattice $3.405$ ($0.09\sigma$) | PASS |
| C-7 | $\Delta = 0.126$ framework-internal; $\Delta_3 = 0.135$ lattice consistency check | PASS |
| C-8 | $c_\text{FI} = 6.74 > 0$ | PASS |
| C-9 | $c_\text{FI}$ consistent with $c_\text{lat} = 6.79$ within $1\sigma$ ($0.08\sigma$) | PASS |
| C-10 | Error propagation for $R_\text{cont}^{\text{FI}}$ | PASS |
| C-11 | Error propagation for $c_\text{FI}$ | PASS |
| C-12 | Dimensional consistency | PASS |
| C-13 | $M_0$ extraction for SU($N$) $N = 2$–$12$ all give $\Delta > 0$ | PASS |
| C-14 | Framework $M_0 \times \eta(N)$ recovers lattice $R_\text{cont}$ for all SU($N$) | PASS |

### §10.2 Adversarial Tests (ADV-1 through ADV-6)

| ID | Description | Status |
|----|-------------|--------|
| ADV-1 | $R_\text{cont}^{\text{FI}}$ sensitivity to $\Delta$ over full uncertainty range | PASS |
| ADV-2 | Casimir scaling validity in scaling window (not just asymptotically) | PASS |
| ADV-3 | No circular reasoning ($R_\text{cont}^{\text{FI}}$ independent of lattice $R_\text{cont}$) | PASS |
| ADV-4 | Sensitivity to $I_\text{FCC}$ value | PASS |
| ADV-5 | Constituent gluon model for non-$0^{++}$ quantum numbers | PASS |
| ADV-6 | Subleading corrections to $M_0^{\text{SC}} = 2$ | PASS |

### §10.3 Verification Scripts

- **Standard + Adversarial:** `verification/Phase7/prop_7_8_2_framework_internal_glueball_ratio.py`
- **Results:** 14/14 standard PASS, 6/6 adversarial PASS
- **Plot:** `verification/plots/prop_7_8_2_casimir_crossover.png` — shows $\sigma_8/\sigma_3$ crossover from 2 to $9/4$

- **Multi-Agent Adversarial Physics:** `verification/Phase7/verify_prop_7_8_2_adversarial.py`
- **Results:** 10/10 adversarial physics tests PASS, 3 findings (2 MODERATE, 1 LOW)
- **Plots:** `verification/plots/prop_7_8_2_adversarial_summary.png`, `prop_7_8_2_monte_carlo_bootstrap.png`, `prop_7_8_2_circularity_test.png`, `prop_7_8_2_SU_N_universality.png`

### §10.4 Multi-Agent Verification Report

- **Report:** [Proposition-7.8.2-Multi-Agent-Verification-2026-02-22.md](../verification-records/Proposition-7.8.2-Multi-Agent-Verification-2026-02-22.md)
- **Agents:** Literature (citation accuracy), Mathematical (algebraic verification), Physics (physical consistency)
- **Original verdict:** PARTIAL — sound core result with correctable issues
- **Key findings addressed (2026-02-22):**
  1. ~~N-ality interpretation in §5.2 needs correction~~ → **FIXED:** Replaced with character expansion explanation
  2. ~~Numerical table in §5.4 has errors at large $\beta$~~ → **FIXED:** Recomputed with exact heat kernel integration
  3. ~~$\Delta_3$ introduces subtle circularity~~ → **FIXED:** Restructured §7.5 into Tier 1 (framework-internal) and Tier 2 (lattice-calibrated); adopted $\Delta = 0.126 \pm 0.07$ centered on $\Delta_1$
  4. ~~Monotonicity claim without proof~~ → **FIXED:** Weakened to "monotonic in scaling window; shallow minimum near $\beta \approx 0.5$"
  5. ~~Error budget missing $M_0^{\text{SC}}$ systematic~~ → **FIXED:** Added 5% systematic, increasing $\delta R$ from 0.21 to 0.27
  6. ~~Rounding $c_\text{FI} = 6.81$ vs 6.82~~ → **FIXED:** All values recomputed consistently with $\Delta = 0.126$
  7. ~~[6] missing article number~~ → **FIXED:** Added JHEP 12 (2021) 082
  8. ~~[4] Ishikawa unused~~ → **FIXED:** Cited in §7.2 as alternative $\Lambda_{\overline{\text{MS}}}$ determination
  9. ~~Missing citations~~ → **FIXED:** Added Boulanger et al. (2008) [9], Dalla Brida & Ramos (2019) [10]; expanded [7] note
- **Post-correction status:** All 9 consolidated findings resolved

---

## §11. Cross-Checks and Limitations

### §11.1 Consistency with Proposition 7.8.1

Prop 7.8.1 extracts $M_0 = 2.33 \pm 0.05$ (bias-corrected) from SU($N$) + Sp($2N$) lattice data. This proposition derives $M_0 = M_0^{\text{SC}} \times (1 + \Delta) = 2.0 \times 1.126 = 2.25 \pm 0.18$. The tension:

$$\frac{|2.25 - 2.33|}{\sqrt{0.18^2 + 0.05^2}} = \frac{0.08}{0.187} = 0.43\sigma \tag{11.1}$$

Fully compatible. The slight deficit ($2.25$ vs $2.33$) is expected because the empirical $M_0$ from Prop 7.8.1 includes the bias correction for the upward trend with $N$, which pushes $M_0$ above the SU(3)-dominated weighted mean of $2.282$.

### §11.2 SU($N$) Universality

The framework predicts $R_\text{cont}(N) = M_0 \times \eta(N)$ for all SU($N$). Using $M_0 = 2.25 \pm 0.18$:

| $N$ | $\eta(N)$ | $R_\text{cont}^{\text{FI}}(N)$ | $\delta R^{\text{FI}}$ | $R_\text{cont}^{\text{lat}}(N)$ | Tension |
|-----|-----------|-------------------------------|----------------------|-------------------------------|---------|
| 2 | 1.633 | 3.68 | $\pm 0.29$ | $3.56 \pm 0.18$ | $0.35\sigma$ |
| 3 | 1.500 | 3.38 | $\pm 0.27$ | $3.405 \pm 0.021$ | $0.09\sigma$ |
| 4 | 1.461 | 3.29 | $\pm 0.26$ | $3.52 \pm 0.11$ | $0.82\sigma$ |
| 5 | 1.443 | 3.25 | $\pm 0.26$ | $3.55 \pm 0.14$ | $1.02\sigma$ |
| 6 | 1.435 | 3.23 | $\pm 0.26$ | $3.53 \pm 0.15$ | $1.00\sigma$ |
| 8 | 1.425 | 3.21 | $\pm 0.26$ | $3.55 \pm 0.22$ | $1.00\sigma$ |
| 12 | 1.418 | 3.19 | $\pm 0.25$ | $3.60 \pm 0.30$ | $1.05\sigma$ |

*Note:* Tensions are computed using combined uncertainties $\sqrt{(\delta R^{\text{FI}})^2 + (\delta R^{\text{lat}})^2}$. The $\delta R^{\text{FI}}$ column includes the framework error (from $M_0$ uncertainty), which was omitted in the earlier version.

The tensions for $N \geq 4$ ($\sim 1\sigma$) reflect the fact that $\Delta(N)$ increases with $N$ (see Derivation §7.4) while the framework uses a fixed $\Delta = 0.126$ calibrated to SU(3). Using the $N$-dependent $\Delta(N)$ from §7.4 would resolve these tensions, but this is not needed for the SU(3) application.

### §11.3 Limitations

1. **Semi-analytic nature:** The RG enhancement $\Delta = 0.126 \pm 0.07$ is estimated, not rigorously derived. This is the dominant source of uncertainty (though the $M_0^{\text{SC}}$ systematic also contributes; see Derivation §8.1).

2. **Constituent gluon model assumptions:** The model assumes two-body threshold ($m_G = 2m_g$) with partial cancellation of binding and kinetic energies. A first-principles derivation would require the Bethe-Salpeter equation.

3. **Casimir scaling regime:** The derivation assumes $\sigma_8/\sigma_3 = C_2(\mathbf{8})/C_2(\mathbf{3})$ holds in the scaling window. Lattice data [5] confirms this to $\sim 5\%$, but exact Casimir scaling is not guaranteed — it is a prediction of the FCC framework at weak coupling.

4. **$N$-dependence:** The framework-internal estimate uses a fixed $\Delta = 0.126$ (from the $\Lambda/\sqrt{\sigma}$ ratio). For other gauge groups, $\Delta(N)$ varies (see Derivation §7.4). A fully group-independent computation of $\Delta$ remains an open problem.

5. **Adjoint string breaking:** The analysis uses the intermediate-distance adjoint string tension, which is parametrically well-defined for glueball physics but not for asymptotic confinement. This is physically correct but requires careful phrasing.

### §11.4 Comparison with Other Approaches

| Approach | $R_\text{cont}$ | Uncertainty | External inputs | Reference |
|----------|-----------------|-------------|-----------------|-----------|
| Lattice MC | $3.405$ | $0.6\%$ | Full MC simulation | [1] |
| Constituent gluon | $\sim 3.3$ | $\sim 10\%$ | Casimir scaling + dimensional analysis | [7, 8, 9] |
| **This work (Prop 7.8.2)** | $3.38$ | $8.0\%$ | FCC partition function + $\Lambda/\sqrt{\sigma}$ scaling | — |
| AdS/CFT holographic | $\sim 3.6$ | $\sim 20\%$ | AdS geometry + string theory | Brower et al., NPB 587 (2000) 249 |
| Sum rules (SVZ) | $\sim 3.0$–$3.5$ | $\sim 15\%$ | OPE condensates | Narison, NPB 509 (1998) 312 |

The framework-internal estimate is competitive with other semi-analytic approaches and superior to holographic estimates in precision.

---

## §12. References

[1] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[2] Necco, S. & Sommer, R. "The N_f = 0 heavy quark potential from short to intermediate distances." Nucl. Phys. B 622 (2002) 328. [arXiv:hep-lat/0108008]

[3] Morningstar, C. & Peardon, M.J. "The glueball spectrum from an anisotropic lattice study." PRD 60 (1999) 034509. [arXiv:hep-lat/9901004]

[4] Ishikawa, K.-I. et al. "$\Lambda_{\overline{\text{MS}}}$ from the nonperturbatively renormalized quark mass." JHEP 12 (2017) 067.

[5] Bali, G.S. "Casimir scaling of SU(3) static potentials." PRD 62 (2000) 114503. [arXiv:hep-lat/0006022]

[6] Athenodorou, A. & Teper, M. "SU($N$) gauge theories in 3+1 dimensions: glueball spectrum, string tensions and topology." JHEP 12 (2021) 082. [arXiv:2106.00364]

[7] Buisseret, F. et al. "Casimir scaling and glueball mass ratios." PLB 873 (2026). [arXiv:2509.09454]

[8] Hong, D.K. et al. "Casimir scaling and glueball mass." PLB 775 (2017) 89. [arXiv:1705.00286]

[9] Boulanger, N., Buisseret, F., Mathieu, V. & Semay, C. "Constituent gluon interpretation of glueballs." EPJA 38 (2008) 317. [arXiv:0806.3875]

[10] Dalla Brida, M. & Ramos, A. "The gradient flow coupling at high perturbative orders from the lattice." EPJC 79 (2019) 435. [arXiv:1905.05147]

---

*End of applications. See the [Statement file](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio.md) for the formal claims and the [Derivation file](./Proposition-7.8.2-Framework-Internal-Glueball-Mass-Ratio-Derivation.md) for the complete mathematical derivation.*
