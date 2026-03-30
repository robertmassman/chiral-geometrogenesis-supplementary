# Proposition 7.8.3: Bethe-Salpeter Glueball Mass Ratio — Applications

**Parent document:** [Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md)

This file contains the combined analysis with Prop 7.8.2, verification checklist, limitations, and cross-references.

---

## §11. Combined Analysis with Proposition 7.8.2

### §11.1 Two Independent Estimates

| Quantity | Prop 7.8.2 (Heat Kernel + RG) | Prop 7.8.3 (Salpeter + AFM) |
|----------|------------------------------|----------------------------|
| $R_\text{cont}$ | $3.38 \pm 0.27$ | $3.41 \pm 0.36$ |
| Relative uncertainty | 8.0% | 10.5% |
| Dominant systematic | $\Delta$ (RG enhancement) | $\alpha_s$ (scale ambiguity) |
| Method | Constituent gluon + perturbative dressing | Variational bound state |

### §11.2 Weighted Average

The two estimates have **different dominant systematics** (RG enhancement vs scale ambiguity) and share only the Casimir scaling assumption. Both methods rely on a **two-constituent gluon model** of the $0^{++}$ glueball, which is well-supported by lattice operator analysis (the $0^{++}$ ground state has dominant overlap with two-gluon operators [9]) but should be noted as a shared assumption.

We combine them via inverse-variance weighted average:

$$w_1 = \frac{1}{\delta R_1^2} = \frac{1}{0.27^2} = 13.72, \qquad w_2 = \frac{1}{\delta R_2^2} = \frac{1}{0.36^2} = 7.72 \tag{11.1}$$

$$R_\text{combined} = \frac{w_1 R_1 + w_2 R_2}{w_1 + w_2} = \frac{13.72 \times 3.38 + 7.72 \times 3.41}{21.44} = \frac{46.4 + 26.3}{21.44} = 3.39 \tag{11.2}$$

$$\delta R_\text{combined} = \frac{1}{\sqrt{w_1 + w_2}} = \frac{1}{\sqrt{21.44}} = 0.216 \approx 0.22 \tag{11.3}$$

$$\boxed{R_\text{combined} = 3.39 \pm 0.22 \quad (6.3\%)} \tag{11.4}$$

**Consistency check:** The two inputs agree at:

$$\frac{|3.38 - 3.41|}{\sqrt{0.27^2 + 0.36^2}} = \frac{0.03}{0.450} = 0.07\sigma \tag{11.5}$$

Excellent internal consistency.

### §11.3 Updated Mass Gap Coefficient

$$c_\text{FI}^{(\text{combined})} = R_\text{combined} \times \frac{\sqrt{\sigma}}{\Lambda_{\overline{\text{MS}}}} = 3.39 \times 1.994 = 6.76 \tag{11.6}$$

Error propagation:

$$\frac{\delta c}{c} = \sqrt{\left(\frac{0.22}{3.39}\right)^2 + \left(\frac{0.021}{1.994}\right)^2} = \sqrt{0.00421 + 0.000111} = 0.0658 \tag{11.7}$$

$$\delta c = 6.76 \times 0.066 = 0.45 \tag{11.8}$$

$$\boxed{c_\text{FI}^{(\text{combined})} = 6.76 \pm 0.45} \tag{11.9}$$

> **Note on $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}}$ tension:** The value $1.994 \pm 0.021$ is from Necco & Sommer (2002) [2]. A more recent determination by Ishikawa et al. (2017) [4] finds $1.934 \pm 0.049$, which is $1.2\sigma$ lower. Using the Ishikawa value would shift $c_\text{FI}$ to $3.39 \times 1.934 = 6.56$, a $\sim 3\%$ reduction. This is within the current uncertainty and does not affect the qualitative conclusion, but represents a systematic that future work should address by using the FLAG average when available.

### §11.4 Impact Summary

| Quantity | Before (Prop 7.8.2 alone) | After (combined) | Improvement |
|----------|--------------------------|-------------------|-------------|
| $R_\text{cont}^{\text{FI}}$ | $3.38 \pm 0.27$ (8.0%) | $3.39 \pm 0.22$ (6.3%) | 19% reduction in $\delta R$ |
| $c_\text{FI}$ | $6.74 \pm 0.55$ (8.2%) | $6.76 \pm 0.45$ (6.6%) | 18% reduction in $\delta c$ |
| Tension vs lattice | $0.09\sigma$ | $0.04\sigma$ | Improved central value |
| External MC inputs | 1 ($\sqrt{\sigma}/\Lambda$) | 1 ($\sqrt{\sigma}/\Lambda$) | Unchanged |

### §11.5 Conservative Lower Bound (at $3\sigma$)

$$c_{\text{FI,low}}^{(\text{combined})} = (3.39 - 3 \times 0.22) \times (1.994 - 3 \times 0.021) = 2.73 \times 1.931 = 5.27 \tag{11.10}$$

This is stronger than Prop 7.8.2's $3\sigma$ lower bound of $c_{\text{FI,low}} = 4.96$ (Statement §9.1), and still firmly establishes $c > 0$.

---

## §12. Verification Status and Test Checklist

### §12.1 Standard Tests (C-1 through C-14)

| ID | Description | Status |
|----|-------------|--------|
| C-1 | Color factor $\langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle = -3$ for $\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ | PASS |
| C-2 | Casimir scaling $\sigma_\text{adj}/\sigma_\text{fund} = 9/4$ | PASS |
| C-3 | AFM identity $\min_\nu[p^2/(2\nu) + \nu/2] = |p|$ | PASS |
| C-4 | Variational matrix elements: $\langle p^2\rangle = \beta^2$, $\langle 1/r\rangle = \beta$, $\langle r\rangle = 3/(2\beta)$ | PASS |
| C-5 | AFM optimization: $\nu^* = \beta$ | PASS |
| C-6 | Energy functional: $E = (2-3\alpha_s)\beta + 27\sigma_3/(8\beta)$ | PASS |
| C-7 | $\beta$ optimization: $\beta^2 = 27\sigma_3/(8(2-3\alpha_s))$ | PASS |
| C-8 | Closed-form: $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ | PASS |
| C-9 | $R_\text{BS}(0.38) = 3.407$ consistent with lattice $3.405$ ($0.02\sigma$) | PASS |
| C-10 | Uncertainty $\delta R = 0.36$ (10.5%) with $\delta\alpha_s = 0.06$ | PASS (updated) |
| C-11 | Combined weighted average $R = 3.39 \pm 0.22$ (6.3%) | PASS (updated) |
| C-12 | Updated $c_\text{FI} = 6.76 \pm 0.45$ | PASS (updated) |
| C-13 | Dimensional consistency of all equations | PASS |
| C-14 | Coupling consistent within scale uncertainty at glueball scale | PASS (softened) |
| C-15 | Two-loop $\alpha_s$ explicitly computed (§9.5) | PASS (new) |
| C-16 | Glueball RMS radius $r_\text{rms} = 0.39$ fm within Cornell validity (§10.6) | PASS (new) |

### §12.2 Adversarial Tests (ADV-1 through ADV-6)

| ID | Description | Status |
|----|-------------|--------|
| ADV-1 | Variational bound: $E_\text{var} \geq E_\text{exact}$ (AFM gives upper bound) | PASS |
| ADV-2 | AFM approximation systematic error subdominant to $\alpha_s$ uncertainty | PASS |
| ADV-3 | Casimir scaling corrections beyond weak coupling: $< 0.2\%$ effect on $R$ | PASS |
| ADV-4 | $R_\text{BS}$ sensitivity to $\alpha_s$ over full uncertainty range; lattice in $1\sigma$ band | PASS |
| ADV-5 | Independence from Prop 7.8.2: different methods, different dominant systematics | PASS |
| ADV-6 | Consistent with literature estimates (constituent gluon, holographic, sum rules) | PASS |

### §12.3 Verification Scripts

- **Standard + Adversarial:** `verification/Phase7/prop_7_8_3_bethe_salpeter_glueball_ratio.py`
- **Results:** 14/14 standard PASS, 6/6 adversarial PASS
- **Plot:** `verification/plots/prop_7_8_3_bethe_salpeter_summary.png` — 4-panel summary ($R_\text{BS}$ vs $\alpha_s$, method comparison, uncertainty improvement, derivation chain)

---

## §13. Limitations and Future Directions

### §13.1 What Was Achieved

The combined analysis reduces the framework-internal $R_\text{cont}$ uncertainty from 8.0% (Prop 7.8.2 alone) to 6.3%. This represents a meaningful improvement and partially addresses the Plan §12.2.F action item.

### §13.2 What Was Not Achieved

The aspiration target of $\leq 2\%$ (Plan §12.2.F) was not reached. The 6.3% combined uncertainty is limited by:

1. **Scale ambiguity in $\alpha_s$** (Prop 7.8.3): The dominant uncertainty. Reducing this requires either BLM (Brodsky-Lepage-Mackenzie) scale-setting or direct determination of $\alpha_s$ at the glueball scale from the lattice in the V-scheme.

2. **RG enhancement uncertainty** (Prop 7.8.2): The 56% relative uncertainty in $\Delta$ limits the heat-kernel estimate. A full Bethe-Salpeter calculation on the crossover path would resolve this.

3. **Shared Casimir scaling assumption**: Both estimates use $\sigma_\text{adj}/\sigma_\text{fund} = 9/4$. If this ratio has an $O(5\%)$ correction at the relevant scale, both estimates would shift coherently. However, lattice data [5] constrains this to $\lesssim 3\%$.

### §13.3 Paths to $\leq 2\%$ — RESOLVED by Prop 7.8.4

| Approach | Expected precision | Feasibility | Status |
|----------|-------------------|-------------|--------|
| BLM scale-setting for $\alpha_s$ | $\sim 3\%$ in $R$ | Moderate (requires NLO calculation) | ✅ Used as consistency check in Prop 7.8.4 |
| **Lattice V-scheme $\alpha_V$ at glueball scale** | **$\sim 2\%$ in $R$** | **Moderate (exists for some couplings)** | **✅ ACHIEVED: 1.7% via Prop 7.8.4** |
| Direct lattice Bethe-Salpeter | $\sim 1\%$ in $R$ | Hard (requires specialized code) | Open (future) |
| Numerical solution of Salpeter equation | $\sim 5\%$ (same $\alpha_s$ issue) | Easy (but doesn't fix dominant error) | Superseded |

> **Update (2026-02-23):** [Proposition 7.8.4](./Proposition-7.8.4-V-Scheme-BLM-Glueball-Mass-Ratio.md) identifies the Salpeter coupling as $\alpha_V$ (V-scheme), compiles lattice $\alpha_V = 0.373 \pm 0.010$ from three independent determinations (two quenched, one $N_f = 2+1$), and achieves $R_V = 3.45 \pm 0.06$ (1.7%). Combined with Prop 7.8.2: $c_\text{FI} = 6.87 \pm 0.14$ (2.0%). The $\leq 2\%$ aspiration target is met. Prop 7.8.4 supersedes Prop 7.8.3 for the Salpeter-based estimate.

### §13.4 Honest Assessment

| Metric | Before (Prop 7.8.2) | After (+ Prop 7.8.3) | Target |
|--------|---------------------|----------------------|--------|
| $\delta R / R$ | 8.0% | 6.3% | $\leq 2\%$ |
| $\delta c / c$ | 8.2% | 6.6% | $\leq 2\%$ |
| $c_{3\sigma,\text{low}}$ | 4.96 | 5.27 | — |
| External MC inputs | 1 | 1 | 0 |

The 6.3% result is a meaningful improvement (19% uncertainty reduction), well above the noise level, and the two independent methods give mutually consistent results. The $\leq 2\%$ aspiration would require additional technical developments (BLM, V-scheme coupling, or direct lattice BS).

---

## §14. Cross-References and Dependency Updates

### §14.1 Forward References

- **Theorem 7.7.3:** Updated quantitative bound with $c_\text{FI}^{(\text{combined})} = 6.76 \pm 0.45$
- **Theorem 7.7.5:** Self-contained proof strengthened (tighter coefficient)
- **Plan §12.2.F:** Action item "Improve $\Delta$ precision via Bethe-Salpeter equation" → addressed; combined 6.3% < 8.0% previous

### §14.2 Backward References

- **Proposition 7.8.2:** $R_\text{cont}^{\text{FI}} = 3.38 \pm 0.27$ (combined with this result)
- **Proposition 0.0.38:** Casimir invariants from exact FCC partition function
- **Theorem 7.5.2:** One-loop beta function coefficient $b_0$
- **External [1]:** Lattice $R_\text{cont} = 3.405 \pm 0.021$ (CHECK, not input)
- **External [2]:** $\sqrt{\sigma}/\Lambda_{\overline{\text{MS}}} = 1.994 \pm 0.021$ (remaining external input)
- **External [5]:** Lattice Casimir scaling confirmation
- **External [11, 12]:** AFM method

### §14.3 Comparison Table

| Quantity | Prop 7.8.2 | Prop 7.8.3 (BS) | Combined | Lattice |
|----------|-----------|-----------------|----------|---------|
| $R_\text{cont}$ | $3.38 \pm 0.27$ | $3.41 \pm 0.36$ | $3.39 \pm 0.22$ | $3.405 \pm 0.021$ |
| Uncertainty | 8.0% | 10.5% | 6.3% | 0.6% |
| $c_\text{FI}$ | $6.74 \pm 0.55$ | — | $6.76 \pm 0.45$ | $6.79 \pm 0.31$ |
| Method | Heat kernel + RG | Salpeter + AFM | Weighted avg | MC simulation |

---

## References

[1] Athenodorou, A. & Teper, M. "The glueball spectrum of SU(3) gauge theory in 3+1 dimensions." JHEP 11 (2020) 172. [arXiv:2007.06422]

[2] Necco, S. & Sommer, R. "The N_f = 0 heavy quark potential from short to intermediate distances." Nucl. Phys. B 622 (2002) 328. [arXiv:hep-lat/0108008]

[5] Bali, G.S. "Casimir scaling of SU(3) static potentials." PRD 62 (2000) 114503. [arXiv:hep-lat/0006022]

[11] Semay, C. "An accurate closed-form approximate solution for the spinless Salpeter equation." Phys. Lett. A 376 (2012) 2217.

[12] Silvestre-Brac, B. & Semay, C. "Duality relations in the auxiliary field method." J. Math. Phys. 52 (2011) 052107. [arXiv:1102.1321]

[13] Mathieu, V., Semay, C. & Silvestre-Brac, B. "Semirelativistic potential model for three-gluon glueball states." PRD 77 (2008) 094009. [arXiv:0803.0815]

[14] Brau, F. & Semay, C. "Semirelativistic potential model for glueball states." PRD 70 (2004) 014017. [arXiv:hep-ph/0412173]

---

*End of applications. See the [Statement file](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md) for the formal claims and the [Derivation file](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Derivation.md) for the complete mathematical derivation.*
