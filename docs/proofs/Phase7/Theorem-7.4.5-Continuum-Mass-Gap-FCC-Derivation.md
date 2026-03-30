# Theorem 7.4.5: Continuum Mass Gap from FCC Scaling — Derivation

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Theorem-7.4.5-Continuum-Mass-Gap-FCC.md) | Theorem statement, motivation, symbol table |
| **Derivation (this file)** | Complete derivation of Parts (a)-(d) |
| [Applications](./Theorem-7.4.5-Continuum-Mass-Gap-FCC-Applications.md) | Verification, numerical checks, physical interpretation |

---

## §5. Derivation of Parts (a)-(b): Physical Mass Gap and Rigorous Bound

### §5.1 Non-Perturbative Lattice Spacing ✅ ESTABLISHED

The lattice spacing is defined non-perturbatively through string tension matching. Since $\sigma_\text{phys} = \sigma_\text{lat}/(2a^2)$ (the factor of 2 arises because $a$ is the nearest-neighbor distance on the FCC/D₄ lattice, and the triangular plaquette geometry differs from the hypercubic square plaquette), we have:

$$a(\beta) = \sqrt{\frac{\sigma_\text{lat}(\beta)}{2\sigma_\text{phys}}}$$

where:
- $\sigma_\text{phys} = (440 \text{ MeV})^2 = (\hbar c/R_\text{stella})^2$ is the physical string tension
- $\sigma_\text{lat}(\beta) = -\ln u_\mathbf{3}(\beta) > 0$ is the dimensionless lattice string tension
- $a$ is the nearest-neighbor distance (Prop 7.4.3, §5.1)

This definition:
1. Is non-perturbative (valid at all couplings)
2. Gives $a > 0$ whenever $\sigma_\text{lat} > 0$ (i.e., $\beta < \beta_c$)
3. **On the FCC lattice**, $a$ does **not** reach zero at $\beta_c$: since $\sigma_\text{lat}(\beta_c) = (3/8)\ln 3 \approx 0.412 > 0$ (the string tension remains finite at the first-order transition), the lattice spacing approaches a finite minimum $a_\text{min} = \sqrt{0.412/(2\sigma_\text{phys})} \approx 0.20$ fm. This contrasts with the hypercubic lattice, where $\sigma_\text{lat} \to 0$ at the second-order transition, giving $a \to 0$ continuously. **The FCC lattice alone does not provide a continuum limit** — this is the core structural limitation addressed in Part (c) via the universality conjecture C3.
4. At weak coupling (before the transition), reduces to the asymptotic scaling formula (Prop 7.4.3) up to lattice artifact corrections

### §5.2 Physical Mass Gap Formula 🔶 NOVEL

**Theorem 5.2.1.** *The physical mass gap at lattice spacing $a(\beta)$ is:*

$$m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)} = \sqrt{3\sigma_\text{phys}} \cdot \frac{\mu(\beta)}{\sqrt{\sigma_\text{lat}(\beta)}}$$

$$= \sqrt{3\sigma_\text{phys}} \cdot R(\beta)$$

*where $R(\beta) = \mu(\beta)/\sqrt{\sigma_\text{lat}(\beta)}$ is the dimensionless ratio from Prop 7.4.4.*

**Proof.** From §5.1, $a(\beta) = \sqrt{\sigma_\text{lat}(\beta)/(2\sigma_\text{phys})}$. Substituting:

$$m_\text{phys} = \frac{\sqrt{3/2}\,\mu}{a} = \sqrt{3/2}\,\mu \cdot \sqrt{\frac{2\sigma_\text{phys}}{\sigma_\text{lat}}} = \sqrt{3\sigma_\text{phys}} \cdot \frac{\mu}{\sqrt{\sigma_\text{lat}}} = \sqrt{3\sigma_\text{phys}} \cdot R(\beta) \quad \square$$

### §5.3 Finite-Lattice-Spacing Positivity ✅ ESTABLISHED

**Theorem 5.3.1 (Pointwise Positivity).** *For any $\beta < \beta_c$:*

$$m_\text{phys}(\beta) = \sqrt{3\sigma_\text{phys}} \cdot R(\beta) > 0$$

**Proof.** We need:
1. $\sigma_\text{phys} > 0$: Given by $\sigma_\text{phys} = (\hbar c/R_\text{stella})^2 > 0$ since $R_\text{stella} > 0$
2. $R(\beta) > 0$: This requires $\mu(\beta) > 0$ (Theorem 7.4.2) and $\sigma_\text{lat}(\beta) > 0$

For $\beta < \beta_c$:
- $\mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta) > 0$ because $u_\mathbf{3}(\beta) < 3^{-3/8}$ (Thm 7.4.2)
- $\sigma_\text{lat}(\beta) = -\ln u_\mathbf{3}(\beta) > 0$ because $u_\mathbf{3}(\beta) < 1$ for all $\beta < \infty$

Therefore $m_\text{phys}(\beta) > 0$. $\square$

**Interpretation:** This theorem says that at any finite lattice spacing (any $\beta < \beta_c$), the SU(3) gauge theory on the FCC lattice has a positive mass gap. The mass gap exists at every scale — the question is whether it survives the continuum limit.

### §5.4 Explicit Mass Gap Values ✅ ESTABLISHED

Using the formula $m_\text{phys} = \sqrt{3\sigma_\text{phys}} \cdot R(\beta)$ with $\sqrt{\sigma_\text{phys}} = 440$ MeV:

| $\beta$ | $\mu$ | $\sigma_\text{lat}$ | $R$ | $m_\text{phys}$ (MeV) |
|---------|-------|---------------------|-----|----------------------|
| 3.0 | 7.91 | 1.40 | 6.69 | 5100 |
| 5.0 | 2.72 | 0.752 | 3.14 | 2390 |
| 7.0 | 1.10 | 0.548 | 1.49 | 1140 |
| 8.0 | 0.68 | 0.494 | 0.97 | 740 |

The mass gap decreases as $\beta$ increases (approaching the continuum), but remains positive.

---

## §6. Derivation of Part (c): Conditional Continuum Mass Gap

### §6.1 The R → 0 Problem and Universality Route 🔮 CONJECTURE

**Exact result (Prop 7.4.4a).** On the FCC lattice:

$$R(\beta) = \frac{\mu(\beta)}{\sqrt{\sigma_\text{lat}(\beta)}} \to 0 \quad \text{as } \beta \to \beta_c^-$$

This is proven exactly: $\mu$ vanishes linearly at $\beta_c$ while $\sigma_\text{lat} \to (3/8)\ln 3 \approx 0.412$ remains finite. The FCC lattice's global label constraint (Migdal-Witten decomposition) freezes out the surface roughening fluctuations that would normally drive $\sigma_\text{lat} \to 0$ at a second-order transition on the hypercubic lattice. Therefore:

$$m_\text{phys}^\text{FCC}(\beta_c) = \sqrt{3\sigma_\text{phys}} \cdot R(\beta_c) = 0$$

**The FCC lattice alone does not yield a positive continuum mass gap.** The exact solvability that enables Part (b) simultaneously prevents the physical continuum limit for Part (c).

### §6.2 Universality-Based Derivation 🔮 CONJECTURE

**Theorem 6.2.1 (Conditional).** *Under Conjectures C1-C3 (reformulated), the continuum mass gap is:*

$$m_\text{phys} = \frac{m_{0^{++}}}{\sqrt{\sigma}}\bigg|_\text{lattice QCD} \times \sqrt{\sigma_\text{CG}} = C_\text{gap} \cdot \Lambda_{\overline{MS}}$$

*where the glueball ratio is imported from standard lattice QCD via universality, and $\sqrt{\sigma_\text{CG}} = \hbar c/R_\text{stella}$.*

**Derivation (conditional on C1-C3):**

**Step 1 (Uses C1 — Continuum existence).** The continuum limit of SU(3) lattice gauge theory exists as a Wightman QFT. This is the core mathematical content of the Millennium Problem.

**Step 2 (Uses C2 — Mass gap).** The continuum SU(3) Yang-Mills theory has mass gap $\Delta > 0$. Combined with C1, this implies the dimensionless ratio $m_{0^{++}}/\sqrt{\sigma}$ is a well-defined positive number in the continuum theory.

**Step 3 (Uses C3 — Universality).** The FCC and hypercubic lattice formulations have the same continuum limit. This is supported by: (i) identical gauge group SU(3); (ii) identical one-loop coefficient $b_0 = 11/(16\pi^2)$ (Prop 7.4.3); (iii) identical two-loop coefficient $b_1$; (iv) standard RG universality arguments. Under C3, the universal glueball ratio from standard lattice QCD transfers to the FCC lattice:

$$\frac{m_{0^{++}}}{\sqrt{\sigma}} = 3.405 \pm 0.021 \qquad \text{(Athenodorou \& Teper 2020)}$$

**Step 4.** The CG framework provides $\sqrt{\sigma} = \hbar c / R_\text{stella} = 440$ MeV (Prop 0.0.17j). Therefore:

$$m_\text{phys} = 3.405 \times 440 \text{ MeV} \approx 1498 \text{ MeV}$$

**Step 5.** Expressing in terms of $\Lambda_{\overline{MS}}$: the pure-gauge ($N_f = 0$) lattice determination gives $\sqrt{\sigma}/\Lambda_{\overline{MS}} = 1.93 \pm 0.04$ (Ishikawa et al. 2017, arXiv:1702.06289, from $\Lambda_{\overline{MS}}/\sqrt{\sigma} = 0.517(10)(^{+8}_{-7})$). Therefore:

$$C_\text{gap} = \frac{m_\text{phys}}{\Lambda_{\overline{MS}}} = \frac{m_{0^{++}}/\sqrt{\sigma}}{\Lambda_{\overline{MS}}/\sqrt{\sigma}} = \frac{3.405}{0.517} \approx 6.6$$

### §6.3 Status of Each Conjecture (Reformulated)

**Conjecture C1 (Continuum existence):** The continuum limit of SU(3) lattice gauge theory defines a well-defined Wightman QFT.

*Status:* 🔮 Open — this is the core of the Clay Millennium Problem. All numerical evidence (lattice Monte Carlo, strong-coupling expansions, functional methods) supports existence. The constructive work of Balaban (1987, 1988) establishes existence in the small-field regime.

**Conjecture C2 (Mass gap):** The continuum SU(3) Yang-Mills theory has mass gap $\Delta > 0$.

*Status:* 🔮 Open — the second part of the Millennium Problem. Numerically established to high precision from lattice QCD ($m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$), but not rigorously proven.

**Conjecture C3 (Universality):** The FCC and hypercubic lattice formulations have the same continuum limit.

*Status:* 🔶 Strong evidence — same gauge group, same perturbative coefficients $b_0, b_1$, standard RG universality arguments. The FCC lattice has $O(a^4)$ improved rotational symmetry (Prop 7.4.3), which strengthens the universality expectation. Rigorous proof would require controlling lattice-specific corrections to all orders.

**Comparison with original formulation:** The original Conjecture C1 stated that $R(\beta) \to R_\infty$ with $R_\infty > 0$. This is falsified by the exact result $R(\beta_c) = 0$ (Prop 7.4.4a). The reformulated conjectures C1-C3 are honest about this limitation and route the continuum mass gap through universality rather than through the FCC $R$ ratio.

---

## §7. Derivation of Part (d): CG Framework Prediction

### §7.1 Mass Gap from $R_\text{stella}$ 🔶 NOVEL

In the CG framework:

$$\sqrt{\sigma_\text{phys}} = \frac{\hbar c}{R_\text{stella}} = \frac{197.327 \text{ MeV}\cdot\text{fm}}{0.44847 \text{ fm}} = 440 \text{ MeV}$$

Using the most recent lattice QCD glueball ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405 \pm 0.021$ (Athenodorou & Teper 2020):

$$m_\text{phys} \approx 3.4 \times 440 \text{ MeV} \approx 1498 \text{ MeV}$$

### §7.2 Comparison with Lattice QCD Data ✅ ESTABLISHED

The lightest glueball mass from lattice QCD (pure SU(3)):

| Study | $r_0 m_{0^{++}}$ | $m_{0^{++}}/\sqrt{\sigma}$ | $m_{0^{++}}$ (MeV) | Scale convention |
|-------|-------------------|------|---------|------|
| Morningstar & Peardon (1999) | 4.21 ± 0.11 ± 0.04 | 3.63 (derived${}^\dagger$) | 1730 ± 50 ± 80 | $r_0^{-1} = 410(20)$ MeV |
| Chen et al. (2006) | 4.16 ± 0.11 | 3.59 (derived${}^\dagger$) | 1710 ± 50 ± 80 | $r_0^{-1} = 410(20)$ MeV |
| Athenodorou & Teper (2020) | 3.95 ± 0.03 | **3.405 ± 0.021** | 1651 ± 22 | $\sqrt{\sigma} = 485(6)$ MeV |

${}^\dagger$ *Derived from $r_0 m_{0^{++}}$ using $r_0\sqrt{\sigma} = 1.160(6)$ (Athenodorou & Teper 2020). Note: Morningstar & Peardon did not directly report $m/\sqrt{\sigma}$; their primary result is $r_0 m_{0^{++}} = 4.21(11)(4)$. The ratio $m/\sqrt{\sigma} \approx 3.74$ quoted in some secondary sources uses an older scale determination.*

**String tension convention note:** The CG framework gives $\sqrt{\sigma} = 440$ MeV (from $R_\text{stella}$, consistent with FLAG 2024 $N_f = 2+1$), while pure-gauge lattice QCD gives $\sqrt{\sigma} = 485 \pm 6$ MeV (Athenodorou & Teper 2020). The dimensionless ratio $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ is scale-independent. Using CG's $\sqrt{\sigma}$: $m \approx 3.4 \times 440 \approx 1498$ MeV. Using pure-gauge $\sqrt{\sigma}$: $m \approx 3.4 \times 485 \approx 1651$ MeV.

### §7.3 The Mass Gap Scale and Provenance 🔶 NOVEL

The Part (d) prediction is a **hybrid result** combining two independent inputs:

| Input | Source | Status |
|-------|--------|--------|
| $\sqrt{\sigma} = \hbar c / R_\text{stella} = 440$ MeV | CG framework (Prop 0.0.17j) | 🔶 NOVEL |
| $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ | Standard lattice QCD (Athenodorou & Teper 2020) | ✅ ESTABLISHED |

**What CG contributes:**
1. **The lattice is derived:** The FCC lattice from Thm 0.0.6 has a characteristic scale $R_\text{stella}$
2. **The string tension is geometric:** $\sigma = (\hbar c/R_\text{stella})^2$ (Prop 0.0.17j)
3. **Universality:** The FCC lattice shares the same continuum limit as standard lattice QCD (C3)

**What CG does NOT independently derive:**
4. **The glueball ratio** $m_{0^{++}}/\sqrt{\sigma} = 3.4$ is imported from standard lattice QCD, not computed from the FCC analysis (which gives $R \to 0$). This ratio requires universality (C3) to transfer from hypercubic to FCC.

This gives the mass gap hierarchy:

$$m_\text{phys} \approx 3.4\sqrt{\sigma} \approx 3.4 \times \frac{\hbar c}{R_\text{stella}} \approx 1.5 \text{ GeV}$$

---

## Appendix A: Relationship Between Parts (b), (c), and the R → 0 Problem

Part (b) says: "At any finite lattice spacing, the mass gap is positive."
Part (c) says: "The mass gap remains positive in the continuum limit."

**On the FCC lattice specifically,** the exact result is:

1. $m_\text{phys}(\beta) > 0$ for all $\beta < \beta_c$ ✅ (Part b — proven)
2. $m_\text{phys}(\beta) \to 0$ as $\beta \to \beta_c^-$ ✅ (Exact — from $R(\beta_c) = 0$, Prop 7.4.4a)

This means the FCC lattice analysis **alone** does not yield a positive continuum mass gap. The mass gap vanishes at the transition because $\mu \to 0$ linearly while $\sigma_\text{lat}$ remains finite (the string tension does not vanish due to the global label constraint freezing out surface roughening).

**On the hypercubic lattice** (standard lattice QCD), the situation is different:
- The deconfinement transition is a crossover or second-order (lattice-dependent), allowing $a \to 0$ continuously
- Numerical evidence overwhelmingly shows $m_{0^{++}}/\sqrt{\sigma} = 3.405(21)$ in the continuum limit
- The mass gap remains positive as $a \to 0$ (numerical evidence, not rigorously proven)

**The gap between Parts (b) and (c) is bridged by universality (C3):** the FCC and hypercubic lattice theories share the same continuum limit. The FCC contribution is the exact mass gap positivity at finite $a$ and the derived lattice geometry; the continuum mass gap value is imported from standard lattice QCD via universality.

## Appendix B: What Would Disprove Part (c)?

Part (c) would be disproved if any of the following were shown:

1. **SU(3) Yang-Mills is conformal:** If the continuum theory had no mass gap ($m_\text{phys} = 0$), Conjecture C2 would fail. All evidence strongly disfavors this.

2. **The continuum limit doesn't exist:** If SU(3) lattice gauge theory did not have a well-defined continuum limit (e.g., the limit is trivial/free), Conjecture C1 would fail. This would be surprising given the overwhelming numerical evidence.

3. **FCC and hypercubic lattices have different continuum limits:** If universality (C3) failed, the FCC mass gap could differ from the standard result. This would require a violation of standard RG universality expectations despite matching perturbative coefficients $b_0, b_1$.

**What does NOT disprove Part (c):**

4. **$R(\beta) \to 0$ on the FCC lattice:** This is already proven (Prop 7.4.4a) and is accounted for in the reformulated conjecture structure. Part (c) routes through universality, not through the FCC $R$ ratio.

None of scenarios 1-3 is considered likely, but they are logically possible — hence the conjectural status of Part (c).

---

*Document created: 2026-02-13*
*Classification: 🔶 NOVEL / 🔮 CONJECTURE*
*Phase: 7 (Renormalization, unitarity, consistency)*
