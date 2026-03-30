# Proposition 7.4.4: Scaling Window Identification on FCC — Applications

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Proposition-7.4.4-Scaling-Window-FCC.md) | Proposition statement, motivation, symbol table |
| [Derivation](./Proposition-7.4.4-Scaling-Window-FCC-Derivation.md) | Complete derivation of Parts (a)-(d) |
| **Applications (this file)** | Verification, numerical checks, physical interpretation |

---

## §8. Applications and Verification

### §8.1 Physical Interpretation

#### §8.1.1 The Scaling Window in Context

The scaling window is the regime where the lattice theory faithfully represents the continuum. On the FCC lattice:

| Regime | $\beta$ range | Physics | Reliability |
|--------|-------------|---------|-------------|
| Deep strong coupling | $0 < \beta < 3$ | Lattice artifacts dominate | Low |
| Strong coupling | $3 < \beta < \beta_\text{sc}$ | Non-perturbative QCD, but lattice effects significant | Medium |
| **Scaling window** | $\beta_\text{sc} < \beta < \beta_c$ | **Continuum physics accessible** | **High** |
| Critical | $\beta = \beta_c$ | Phase transition, $\mu = 0$ | N/A |
| Deconfined | $\beta > \beta_c$ | Unphysical (lattice artifact) | N/A |

#### §8.1.2 Mass Gap Prediction — Current Status

With the non-perturbative lattice spacing, the physical mass gap is:

$$m_\text{phys} = \sqrt{3\sigma_\text{phys}} \cdot R(\beta)$$

where $\sqrt{\sigma_\text{phys}} = 440$ MeV. **However, $R(\beta) \to 0$ as $\beta \to \beta_c^-$**, so the current strong-coupling analysis gives $m_\text{phys} \to 0$ in the continuum limit.

For comparison, standard lattice QCD on hypercubic lattices gives (Morningstar & Peardon 1999):

$$\frac{m_{0^{++}}}{\sqrt{\sigma}} = 3.93 \pm 0.23 \quad (\text{range } 3.5 - 4.0)$$

$$m_{0^{++}} \approx 3.93 \times 440 \text{ MeV} \approx 1730 \text{ MeV} \approx 1.7 \text{ GeV}$$

On the FCC lattice, $R(\beta) \approx 3.7$ occurs at $\beta \approx 5$, which is outside the scaling window near $\beta_c \approx 11.4$. This mismatch is the central open problem (see Statement §9.2). Resolving it likely requires a non-perturbative correction to the string tension identification $\sigma_\text{lat} = -\ln u_\mathbf{3}$ near $\beta_c$.

#### §8.1.3 Two Scales: Planck vs QCD

The CG framework naturally explains the hierarchy between the Planck and QCD scales:

1. **Planck scale:** $a_\text{CG} \sim \ell_P \sim 10^{-35}$ m — the fundamental discretization
2. **QCD scale:** $\Lambda_\text{QCD}^{-1} \sim 10^{-16}$ m — where confinement and mass gap emerge
3. **Ratio:** $\Lambda_\text{QCD}/M_P \sim 10^{-19}$ — explained by the exponential of the asymptotic scaling formula

### §8.2 Numerical Verification: Part (a) — Physical Mass Gap

#### §8.2.1 $m_\text{phys}(\beta)$ Across the Coupling Range

Computing $m_\text{phys} = \sqrt{3/2}\,\mu/a$ with the non-perturbative lattice spacing $a = \sqrt{\sigma_\text{lat}/(2\sigma_\text{phys})}$ ($a$ = nearest-neighbor distance, Prop 7.4.3 §5.1):

| $\beta$ | $u_\mathbf{3}$ | $\mu$ | $\sigma_\text{lat}$ | $R = \mu/\sqrt{\sigma_\text{lat}}$ | $\sqrt{3} \cdot R$ |
|---------|----------------|-------|---------------------|-------------------------------------|---------------------|
| 1.0 | 0.060 | 19.19 | 2.811 | 11.45 | 19.83 |
| 3.0 | 0.203 | 9.46 | 1.594 | 7.49 | 12.97 |
| 5.0 | 0.354 | 5.01 | 1.039 | 4.92 | 8.52 |
| 7.0 | 0.483 | 2.52 | 0.727 | 2.96 | 5.12 |
| 9.0 | 0.580 | 1.06 | 0.544 | 1.43 | 2.48 |
| 10.0 | 0.618 | 0.55 | 0.481 | 0.80 | 1.38 |
| 10.5 | 0.635 | 0.34 | 0.454 | 0.50 | 0.87 |
| 11.0 | 0.650 | 0.15 | 0.430 | 0.22 | 0.39 |
| 11.3 | 0.659 | 0.04 | 0.417 | 0.06 | 0.11 |

*Note: $R$ decreases monotonically from large values at strong coupling to $R = 0$ at $\beta_c \approx 11.4$. The lattice QCD glueball ratio $R \approx 3.93$ (Morningstar & Peardon 1999) occurs around $\beta \approx 5.5$, deep in the strong-coupling regime.*

#### §8.2.2 Interpretation

The ratio $R(\beta)$ is strictly monotonically decreasing from $R \to \infty$ at strong coupling to $R(\beta_c) = 0$. Key observations:

1. **$R \approx 3.93$ at $\beta \approx 5.5$** — this is where the FCC model's mass-gap-to-string-tension ratio matches the lattice QCD glueball value (Morningstar & Peardon 1999), but this is in the strong-coupling regime, not near the continuum limit
2. **$R$ varies by a factor of $\sim 3.4$ across $\beta \in [5, 9]$** — from 4.92 to 1.43, which is not "approximately constant"
3. **$R \to 0$ at $\beta_c \approx 11.4$** — the ratio vanishes because $\mu \to 0$ while $\sigma_\text{lat} \to (3/8)\ln 3 > 0$

This indicates that the strong-coupling string tension $\sigma_\text{lat} = -\ln u_\mathbf{3}$ does not correctly represent the physical string tension near the continuum limit.

### §8.3 Numerical Verification: Part (b) — Dimensionless Ratio Analysis

#### §8.3.1 Analytical Formula

The ratio $R(\beta) = \mu/\sqrt{\sigma_\text{lat}}$ can be written:

$$R = \frac{-3\ln 3 + 8x}{\sqrt{x}} \quad \text{where } x = -\ln u_\mathbf{3}$$

At $\beta_c$: $x = (3/8)\ln 3 \approx 0.412$ and $R = 0$. Note: $\mu$ vanishes at $\beta_c$ but $\sigma_\text{lat} = x$ does **not** — it stays at $(3/8)\ln 3 > 0$.

The derivative:

$$\frac{dR}{dx} = \frac{8x + 3\ln 3}{2x^{3/2}} > 0 \quad \text{for all } x > 0$$

Since $u_\mathbf{3}'(\beta) > 0$ and $x$ is decreasing in $\beta$, we have $dx/d\beta < 0$, so $dR/d\beta < 0$ — $R$ is **strictly monotonically decreasing** in $\beta$.

#### §8.3.2 The Alternative Ratio $\tilde{R}$

The ratio of mass gap to string tension:

$$\tilde{R}(\beta) = \frac{\mu(\beta)}{\sigma_\text{lat}(\beta)} = \frac{-3\ln 3 + 8x}{x} = 8 - \frac{3\ln 3}{x}$$

This ratio also vanishes at $\beta_c$ ($\tilde{R} = 8 - 8 = 0$) and approaches 8 at strong coupling. Both $R$ and $\tilde{R}$ are monotonically decreasing to 0 — no definition of the dimensionless ratio produces a finite non-zero limit at $\beta_c$ with the current strong-coupling string tension.

#### §8.3.3 Comparison with Lattice QCD Target

The lattice QCD glueball ratio $m_{0^{++}}/\sqrt{\sigma} \approx 3.93 \pm 0.23$ (Morningstar & Peardon 1999; range 3.5–4.0) corresponds to $R \approx 3.7$ at $\beta \approx 5$. This is deep in the strong-coupling regime, far from the continuum limit at $\beta_c \approx 11.4$. The FCC model does not reproduce this ratio in the scaling window — this is the central open problem identified in the multi-agent verification.

### §8.4 Numerical Verification: Part (c) — CG Lattice Spacing

#### §8.4.1 Computation

The CG lattice spacing:

$$a_\text{CG} = \sqrt{\frac{8}{\sqrt{3}}\ln(3)} \times \ell_P = \sqrt{5.07} \times 1.616 \times 10^{-35} \text{ m} = 3.64 \times 10^{-35} \text{ m}$$

Corresponding to energy scale:

$$\frac{1}{a_\text{CG}} = \frac{\hbar c}{a_\text{CG}} = \frac{0.197327 \text{ GeV}\cdot\text{fm}}{3.64 \times 10^{-20} \text{ fm}} = 5.42 \times 10^{18} \text{ GeV}$$

This is just below the Planck energy ($M_P = 1.22 \times 10^{19}$ GeV), confirming the CG lattice is at the Planck scale.

#### §8.4.2 $\beta_*$ Value

Using $\Lambda_\text{FCC} \approx 2.6$ MeV (Prop 7.4.3) and $a_\text{CG} = 3.64 \times 10^{-35}$ m:

$$\beta_* = 12 b_0 \ln\frac{1}{a_\text{CG}\Lambda_\text{FCC}} \approx 12 \times 0.06966 \times \ln\frac{1}{4.80 \times 10^{-22}} = 0.836 \times 49.1 \approx 41.0$$

Including the two-loop correction: $\beta_* \approx 41.2$.

This places $\beta_*$ far above $\beta_c \approx 11.4$:

$$\beta_* - \beta_c \approx 41.0 - 11.4 = 29.6$$

The CG lattice spacing is ~30 units of $\beta$ above the phase transition — deeply perturbative.

### §8.5 Numerical Verification: Part (d) — Transition as Artifact

#### §8.5.1 Comparison with Finite-Temperature Transition

The finite-temperature deconfinement transition on cubic SU(3) lattices occurs at:

$$N_\tau \times a \sim 1/T_c \implies \beta_\text{deconf}(N_\tau) \text{ varies with } N_\tau$$

Typical values: $\beta_\text{deconf} \approx 5.7$ for $N_\tau = 4$ (cubic).

The FCC bulk transition at $\beta_c \approx 11.4$ is:
- At zero temperature (not finite temperature)
- Present for all spatial volumes (not a finite-size effect)
- A consequence of the global label constraint (not gauge dynamics)

This confirms the transition is qualitatively different from the physical deconfinement transition.

#### §8.5.2 Universality Test — Status

If the FCC and cubic lattices describe the same continuum theory (SU(3) Yang-Mills), then physical quantities extracted from the continuum limit should agree:

$$\frac{m_{0^{++}}}{\sqrt{\sigma}}\bigg|_\text{FCC} = \frac{m_{0^{++}}}{\sqrt{\sigma}}\bigg|_\text{cubic} = 3.93 \pm 0.23$$

**Current status:** The FCC model with the strong-coupling string tension gives $R(\beta) \to 0$ at $\beta_c$, which does **not** match the cubic lattice value. This does not necessarily invalidate the universality conjecture (C4), because the discrepancy may be due to the strong-coupling string tension identification $\sigma_\text{lat} = -\ln u_\mathbf{3}$ not representing the physical string tension near $\beta_c$. A proper non-perturbative calculation of the Wilson loop area law on the FCC lattice is needed to resolve this test.

### §8.6 Self-Consistency Checks

#### §8.6.1 Dimensional Consistency

| Quantity | Dimensions | Check |
|----------|-----------|-------|
| $m_\text{phys} = \sqrt{3/2}\,\mu/a$ | [Energy] | ✅ ($\mu$ dimensionless, $a$ length) |
| $R = \mu/\sqrt{\sigma_\text{lat}}$ | Dimensionless | ✅ (both dimensionless) |
| $\beta_* = 12b_0\ln(1/a\Lambda)$ | Dimensionless | ✅ ($a\Lambda$ dimensionless) |
| $a_\text{CG}^2 = (8/\sqrt{3})\ln(3)\ell_P^2$ | Length$^2$ | ✅ |

#### §8.6.2 Limiting Cases

1. **$\beta \to 0$:** $u_\mathbf{3} \to 0$, $\mu \to \infty$, $a \to \infty$ — both gap and spacing large ✅
2. **$\beta \to \beta_c^-$:** $\mu \to 0$, $\xi \to \infty$ — continuum limit signals ✅
3. **$\sigma_\text{phys} \to 0$:** $m_\text{phys} \to 0$ (massless gluons, no confinement) ✅
4. **Large $N_c$ (t'Hooft limit):** Confinement persists, mass gap expected to scale as $O(1)$ in $1/N_c$ — not explicitly tested but consistent with framework ⚠️

### §8.7 Summary Table of Results

| Part | Claim | Method | Status |
|------|-------|--------|--------|
| (a) | Physical mass gap formula; finite limit requires non-perturbative corrections | Analytical + numerical | 🔮 CONJECTURE |
| (b) | $R(\beta)$ monotonically decreasing to 0; mismatch with lattice QCD target 3.7 | Analytical proof ($dR/dx > 0$) | 🔮 CONJECTURE |
| (c) | $\beta_* \approx 41$ | Asymptotic scaling + CG lattice spacing | 🔶 NOVEL |
| (d) | Bulk transition is artifact | 4 independent arguments | 🔮 CONJECTURE |

---

*Document created: 2026-02-13*
*Last revised: 2026-02-13 (post-verification: corrected numerical table, β_c ≈ 11.4, Λ_FCC = 2.6 MeV, β_* ≈ 41)*
*Classification: 🔮 CONJECTURE (Parts a-b) / 🔶 NOVEL (Part c) / 🔮 CONJECTURE (Part d)*
*Phase: 7 (Renormalization, unitarity, consistency)*
