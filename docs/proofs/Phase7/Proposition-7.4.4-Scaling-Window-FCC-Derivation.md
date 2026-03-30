# Proposition 7.4.4: Scaling Window Identification on FCC — Derivation

## Navigation

| File | Purpose |
|------|---------|
| [Statement](./Proposition-7.4.4-Scaling-Window-FCC.md) | Proposition statement, motivation, symbol table |
| **Derivation (this file)** | Complete derivation of Parts (a)-(d) |
| [Applications](./Proposition-7.4.4-Scaling-Window-FCC-Applications.md) | Verification, numerical checks, physical interpretation |

---

## §5. Derivation of Parts (a)-(b): Scaling Region and Ratio Stabilization

### §5.1 Physical Mass Gap Formula 🔶 NOVEL

The physical mass gap on the FCC lattice is:

$$m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)}$$

where:
- $\mu(\beta) = -3\ln 3 - 8\ln u_\mathbf{3}(\beta)$ is the intensive lattice mass gap (Thm 7.4.2)
- $a(\beta)$ is the lattice spacing (nearest-neighbor distance) from asymptotic scaling (Prop 7.4.3, §5.1)
- $\sqrt{3/2}$ converts from (111) layer spacing $d_{111} = a\sqrt{2/3}$ to nearest-neighbor units

**The factor $\sqrt{3/2}$:** The mass gap $\mu(\beta)$ measures the decay rate per (111) layer. Each layer has thickness $d_{111} = a\sqrt{2/3}$ where $a$ is the nearest-neighbor distance (Prop 7.4.3, §5.1). Therefore:

$$\text{decay rate per unit length} = \frac{\mu(\beta)}{d_{111}} = \frac{\sqrt{3/2}\,\mu(\beta)}{a}$$

### §5.2 Behavior of $m_\text{phys}(\beta)$ 🔶 NOVEL

**At strong coupling ($\beta \ll \beta_c$):**

$$\mu(\beta) \approx -3\ln 3 - 8\ln u_\mathbf{3}(\beta) \gg 1$$

$$a(\beta) \text{ is not well-described by asymptotic scaling (non-perturbative regime)}$$

The product $m_\text{phys}$ is not reliably computed from the perturbative $a(\beta)$ at strong coupling. However, using the CG lattice spacing $a = R_\text{stella} = 0.44847$ fm (Prop 0.0.17j):

$$m_\text{phys}^{(\text{strong})} \sim \frac{\sqrt{3} \times O(10)}{0.44847 \text{ fm}} \sim O(\text{GeV})$$

**Near $\beta_c$ (scaling window):**

As $\beta \to \beta_c^-$:
- $u_\mathbf{3}(\beta) \to 3^{-3/8}$, so $\mu(\beta) \to 0^+$
- From asymptotic scaling: $a(\beta) \to 0$ exponentially

The key question: does $\mu(\beta)/a(\beta)$ converge?

Near $\beta_c$, we can expand:

$$\mu(\beta) = -8\frac{u_\mathbf{3}'(\beta_c)}{u_\mathbf{3}(\beta_c)}(\beta - \beta_c) + O((\beta - \beta_c)^2)$$

$$= C_\mu (\beta_c - \beta) + O((\beta_c - \beta)^2)$$

where $C_\mu = 8 u_\mathbf{3}'(\beta_c)/u_\mathbf{3}(\beta_c) > 0$ (since $u_\mathbf{3}$ is monotonically increasing).

Meanwhile, $a(\beta)$ varies exponentially:

$$a(\beta) = a(\beta_c) \exp\left(-\frac{\beta - \beta_c}{12b_0}\right) \times \text{power-law corrections}$$

So near $\beta_c$:

$$\frac{\mu(\beta)}{a(\beta)} \approx \frac{C_\mu(\beta_c - \beta)}{a(\beta_c)} \times \exp\left(\frac{\beta_c - \beta}{12b_0}\right)$$

The exponential growth of $1/a$ dominates the linear decay of $\mu$. Therefore:

$$m_\text{phys}(\beta) \to \infty \text{ as } \beta \to \beta_c^-$$

**This means the physical mass gap diverges near $\beta_c$ when using the perturbative scaling formula for $a(\beta)$.** This is expected: the perturbative $a(\beta)$ is not valid near a first-order phase transition. The true lattice spacing near $\beta_c$ is determined non-perturbatively.

### §5.3 Resolution: Non-Perturbative Lattice Spacing 🔶 NOVEL

Near $\beta_c$, the lattice spacing should be defined through a physical observable, not the perturbative formula. The standard approach (Sommer 1994) uses the force between static quarks:

$$r_0^2 F(r_0) = 1.65 \implies a/r_0$$

On the FCC lattice, we can alternatively use the string tension:

$$a(\beta) = \sqrt{\frac{\sigma_\text{lat}(\beta)}{2\sigma_\text{phys}}}$$

where $\sigma_\text{phys} \approx (440 \text{ MeV})^2$ and $\sigma_\text{lat} = -\ln u_\mathbf{3}(\beta)$. The factor of 2 in the denominator arises because $a$ is the nearest-neighbor distance (Prop 7.4.3, §5.1); the string tension relation is $\sigma_\text{phys} = \sigma_\text{lat}/(2a^2)$ (the factor of 2 accounts for the FCC triangular plaquette geometry vs the hypercubic square plaquette).

With this non-perturbative definition:

$$m_\text{phys}(\beta) = \frac{\sqrt{3/2}\,\mu(\beta)}{a(\beta)} = \sqrt{3/2}\,\mu \cdot \sqrt{\frac{2\sigma_\text{phys}}{\sigma_\text{lat}}} = \sqrt{3\sigma_\text{phys}} \cdot \frac{\mu}{\sqrt{\sigma_\text{lat}}}$$

$$= \sqrt{3\sigma_\text{phys}} \cdot R(\beta)$$

where $R(\beta) = \mu(\beta)/\sqrt{\sigma_\text{lat}(\beta)}$ is the dimensionless ratio from Part (b).

**Therefore, $m_\text{phys}$ is determined by the stabilization of $R(\beta)$.**

### §5.4 Dimensionless Ratio $R(\beta)$ 🔮 CONJECTURE

Using the strong-coupling string tension $\sigma_\text{lat} = -\ln u_\mathbf{3}$ (**Assumption A1**, see Statement §3.5):

$$R(\beta) = \frac{\mu(\beta)}{\sqrt{\sigma_\text{lat}(\beta)}} = \frac{-3\ln 3 - 8\ln u_\mathbf{3}}{\sqrt{-\ln u_\mathbf{3}}}$$

Let $x = -\ln u_\mathbf{3}(\beta) > 0$ (positive in the confined phase). Then:

$$R = \frac{-3\ln 3 + 8x}{\sqrt{x}} = 8\sqrt{x} - \frac{3\ln 3}{\sqrt{x}}$$

This function has the following behavior:
- At $\beta_c$: $x_c = (3/8)\ln 3 \approx 0.412$, giving $\mu(\beta_c) = -3\ln 3 + 8x_c = 0$ and $R(\beta_c) = 0$
- At strong coupling ($x \gg 1$): $R \approx 8\sqrt{x} \to \infty$

The derivative:

$$\frac{dR}{dx} = \frac{4}{\sqrt{x}} + \frac{3\ln 3}{2x^{3/2}} = \frac{8x + 3\ln 3}{2x^{3/2}} > 0$$

So $R(x)$ is monotonically increasing in $x$ (equivalently, monotonically decreasing in $\beta$ since $x$ decreases with $\beta$). **The ratio does not plateau — it strictly decreases from $R \to \infty$ at strong coupling to $R = 0$ at $\beta_c$.** In the interval $\beta \in [5, 9]$, $R$ decreases from $\approx 4.9$ to $\approx 1.4$ — a factor of $\sim 3.4$, which is not a plateau.

**The R → 0 problem:** The key observation is that $\sigma_\text{lat}(\beta_c) = (3/8)\ln 3 \approx 0.412 > 0$ while $\mu(\beta_c) = 0$. On standard hypercubic lattices, both quantities vanish together as $a \to 0$, yielding a finite ratio $m_{0^{++}}/\sqrt{\sigma} \approx 3.7$. The discrepancy indicates that $\sigma_\text{lat} = -\ln u_\mathbf{3}$ is a strong-coupling definition that does not correctly represent the physical string tension near $\beta_c$ (see Assumption A1 in Statement §3.5).

**An alternative ratio:** Consider

$$\tilde{R}(\beta) = \frac{\mu(\beta)}{\sigma_\text{lat}(\beta)} = 8 - \frac{3\ln 3}{x}$$

This also vanishes at $\beta_c$ (where $\tilde{R} = 0$) and approaches 8 at strong coupling. Neither $R$ nor $\tilde{R}$ provides a finite non-zero continuum limit with the current strong-coupling string tension definition.

### §5.5 Standard Lattice QCD Comparison ✅ ESTABLISHED

On standard hypercubic SU(3) lattices, the mass-gap-to-string-tension ratio is known from lattice Monte Carlo:

$$\frac{m_{0^{++}}}{\sqrt{\sigma}} \approx 3.5 - 4.0$$

where $m_{0^{++}}$ is the lightest glueball mass (the mass gap of the pure gauge theory). This provides a target value for $R_\infty$ on the FCC lattice.

---

## §6. Derivation of Part (c): CG Lattice Spacing Connection

### §6.1 CG Lattice Spacing 🔶 NOVEL

From Proposition 0.0.17r:

$$a_\text{CG}^2 = \frac{8}{\sqrt{3}}\ln(3)\ell_P^2 \approx 5.07\ell_P^2$$

$$a_\text{CG} = \sqrt{5.07} \times 1.616 \times 10^{-35} \text{ m} = 3.64 \times 10^{-35} \text{ m}$$

This is a **Planck-scale** lattice spacing, much smaller than the QCD scale ($\sim 0.1$ fm $= 10^{-16}$ m). It represents the fundamental discretization scale, not the QCD lattice spacing used in the scaling window.

### §6.2 Mapping to $\beta_*$ 🔶 NOVEL

Using the asymptotic scaling formula from Prop 7.4.3:

$$a(\beta_*) = a_\text{CG}$$

$$\frac{1}{\Lambda_\text{FCC}}\left(\frac{6b_0}{\beta_*}\right)^{-b_1/(2b_0^2)}\exp\left(-\frac{\beta_*}{12b_0}\right) = a_\text{CG}$$

At leading order:

$$\beta_* \approx 12b_0 \ln\frac{1}{a_\text{CG}\Lambda_\text{FCC}}$$

Using $\Lambda_\text{FCC} \approx 0.010 \times \Lambda_{\overline{MS}}$ (Prop 7.4.3, §7.3) with $\Lambda_{\overline{MS}} = 260 \pm 20$ MeV for quenched SU(3) (Sommer 1994):

$$\Lambda_\text{FCC} \approx 0.010 \times 260 \text{ MeV} = 2.6 \text{ MeV}$$

Converting to inverse meters: $\Lambda_\text{FCC} = 2.6 \text{ MeV}/(197.327 \text{ MeV}\cdot\text{fm}) = 1.318 \times 10^{13} \text{ m}^{-1}$

$$a_\text{CG} \times \Lambda_\text{FCC} = 3.64 \times 10^{-35} \times 1.318 \times 10^{13} \approx 4.80 \times 10^{-22}$$

$$\beta_* \approx 12 \times 0.06966 \times \ln(1/4.80 \times 10^{-22}) = 0.836 \times 49.1 \approx 41.0$$

Including the two-loop correction:

$$\beta_* \approx 41.0 + \frac{b_1}{b_0}\ln(41.0) \approx 41.0 + 0.0587 \times 3.71 \approx 41.2$$

### §6.3 Physical Interpretation 🔶 NOVEL

The CG lattice spacing $a_\text{CG}$ corresponds to $\beta_* \approx 41$, which is:

- **Deep in the perturbative regime** ($\beta_* \gg \beta_c \approx 11.4$)
- **Far above the bulk phase transition** ($\beta_* > \beta_c$)
- **In the "deconfined" phase** of the FCC lattice model

This has important implications:

1. The CG lattice spacing is NOT in the scaling window ($\beta_\text{sc} < \beta < \beta_c$)
2. The CG lattice spacing corresponds to the **fundamental** discretization scale (Planck scale)
3. The QCD mass gap lives at much larger scales ($\sim 0.1$ fm), corresponding to $\beta < \beta_c$

**Resolution:** The CG framework has two lattice spacings:
- **Fundamental:** $a_\text{CG} \sim \ell_P$ (Planck scale, from holographic self-consistency)
- **Effective QCD:** $a_\text{eff} \sim 0.1$ fm (QCD scale, in the scaling window)

The fundamental lattice is the microscopic structure; the effective QCD lattice emerges after renormalization group flow from $\beta_*$ down to $\beta_\text{sc}$.

### §6.4 RG Flow and the Bulk Transition 🔮 CONJECTURE

**Open issue:** The RG flow from the Planck scale ($\beta_* \approx 41$) to the QCD scale ($\beta < \beta_c \approx 11.4$) must cross the first-order bulk transition at $\beta_c$. This is a non-trivial requirement:

1. **On hypercubic lattices**, there is no bulk transition — the RG flow proceeds smoothly from UV to IR
2. **On the FCC lattice**, the global label constraint creates a barrier at $\beta_c$

**Possible resolutions:**
- **(i)** If the bulk transition is truly a lattice artifact (Conjecture C2), then the *physical* RG flow ignores it — the continuum theory's RG flow is defined independently of the lattice model's phase structure. The lattice model at $\beta < \beta_c$ and $\beta > \beta_c$ may both describe the same continuum theory, just in different regimes of the lattice approximation.
- **(ii)** The "two lattice spacing" interpretation: the fundamental lattice ($a_\text{CG}$) and effective QCD lattice ($a_\text{eff}$) are not connected by RG flow on the same FCC lattice model. Rather, $a_\text{CG}$ describes the fundamental discretization scale, while the scaling window at $\beta < \beta_c$ independently captures QCD physics.
- **(iii)** Non-perturbative effects may smooth the transition for the physical observables, even though the FCC partition function shows a first-order transition.

**Status:** This issue does not affect the validity of the mass gap formula or the CG lattice spacing computation separately. It affects the *interpretation* of how the Planck-scale lattice connects to QCD-scale physics through RG flow.

---

## §7. Derivation of Part (d): Phase Transition Analysis

### §7.1 Nature of the Bulk Transition 🔮 CONJECTURE

**Conjecture C2 (Bulk Transition is Artifact):** The first-order deconfinement transition at $\beta_c$ on the FCC lattice is a lattice artifact that does not obstruct the continuum limit of SU(3) Yang-Mills theory.

**Evidence for this conjecture:**

### §7.2 Evidence 1: Global Label Constraint 🔶 NOVEL

The exact partition function $Z_\text{FCC} = \sum_R d_R^{3N} a_R^{8N}$ (Prop 2.5.2b) enforces a **global label constraint**: all cells carry the same representation $R$. This constraint is specific to the exact character expansion on the FCC lattice. It arises from:

1. **Face-sharing topology:** Adjacent cells share faces, and character orthogonality forces $R_1 = R_2$
2. **Connected face-sharing graph:** The FCC lattice has a connected face-sharing graph, propagating the constraint globally

At weak coupling ($\beta \gg 1$), individual plaquettes fluctuate freely. The global constraint becomes unphysical — in the continuum, there is no global representation constraint. The transition at $\beta_c$ marks the point where the global constraint breaks down, not a physical phase transition.

**Important clarification (addressing circularity concern):** The mass gap formula $\mu(\beta)$ is *derived* using the global label constraint (via the exact partition function). Part (d) argues that this constraint is a *lattice artifact* that does not obstruct the continuum limit. These are compatible claims: the constraint is a valid feature of the FCC lattice model that yields exact results at finite lattice spacing. The claim is that the *phase transition* caused by the constraint's breakdown at $\beta_c$ is an artifact — not that the constraint itself is invalid. The mass gap $\mu(\beta)$ is well-defined for $\beta < \beta_c$ where the constraint holds. The continuum limit is taken as $\beta \to \beta_c^-$, approaching but not crossing the point where the constraint breaks down.

### §7.3 Evidence 2: Divergent Correlation Length ✅ ESTABLISHED

At $\beta_c$, the correlation length diverges:

$$\xi(\beta) = \frac{1}{\mu(\beta)} \to \infty \quad \text{as } \beta \to \beta_c^-$$

A divergent correlation length is the standard criterion for a **continuum limit**: when $\xi \gg a$, the lattice structure becomes invisible and the long-distance physics is described by a continuum field theory. The first-order transition provides exactly the divergent correlation length needed.

### §7.4 Evidence 3: No Bulk Transition on Hypercubic ✅ ESTABLISHED

Standard SU(3) lattice gauge theory on hypercubic lattices does NOT have a bulk phase transition at zero temperature. The continuum limit is taken by smoothly varying $\beta \to \infty$. The FCC bulk transition is a consequence of the FCC-specific global label constraint, not of SU(3) Yang-Mills physics.

**Comparison:**

| Feature | Hypercubic SU(3) | FCC SU(3) |
|---------|-----------------|-----------|
| Bulk transition | None | First-order at $\beta_c$ |
| Partition function | Not exactly solvable | Exactly solvable |
| Transfer matrix | Dense (numerical) | Diagonal (exact) |
| Global constraint | None | All cells same $R$ |
| Continuum limit | $\beta \to \infty$ (smooth) | $\beta \to \beta_c^-$ (scaling window) |
| Same continuum theory? | Yes | Yes (conjectured) |

### §7.5 Evidence 4: Smooth Ratio Behavior 🔶 NOVEL

If the bulk transition were a physical feature (rather than an artifact), one would expect the dimensionless ratio $R(\beta) = \mu/\sqrt{\sigma_\text{lat}}$ to show anomalous behavior (discontinuity, divergence, or non-monotonicity) near $\beta_c$. Instead, $R(\beta)$ varies smoothly and monotonically through the entire coupling range, with no singular behavior at the transition — consistent with the transition being a lattice artifact rather than a physical singularity.

### §7.6 Summary of Conjectures

| Conjecture | Statement | Evidence Level | Status |
|------------|-----------|---------------|--------|
| **C1** | Continuum mass gap: $m_\text{phys}$ is finite and positive in continuum limit despite $R \to 0$ | Open problem | 🔮 |
| **C2** | Bulk transition is artifact: does not obstruct continuum limit | Strong (3 independent arguments) | 🔮 |
| **C3** | Continuum limit exists: $\lim_{a \to 0} m_\text{phys}$ is finite | Moderate (standard lattice QCD expectation) | 🔮 |
| **C4** | Universality: FCC continuum theory = standard SU(3) YM | Strong (same gauge group, same UV behavior) | 🔮 |

These conjectures are aspects of the Clay Millennium Prize Problem. The CG framework provides structural support but does not resolve them rigorously.

---

## Appendix A: Critical Coupling Computation

The critical coupling $\beta_c$ is determined by $u_\mathbf{3}(\beta_c) = 3^{-3/8}$, where:

$$u_\mathbf{3}(\beta) = \frac{a_\mathbf{3}(\beta)}{a_\mathbf{1}(\beta)}$$

and $a_R(\beta)$ are the SU(3) heat kernel coefficients. The numerical value is $\beta_c \approx 11.4$ (from the verification scripts for Thm 7.4.2).

## Appendix B: Scaling Window Width Estimate

The scaling window is approximately $\beta_c - \delta < \beta < \beta_c$ where $\delta$ is determined by requiring that:

1. Asymptotic scaling is approximately valid: $|a(\beta)/a_\text{pert}(\beta) - 1| < \epsilon$
2. The mass gap is still positive: $\mu(\beta) > 0$
3. The correlation length is large: $\xi > \xi_\text{min}$

For $\epsilon = 0.1$ and $\xi_\text{min} = 5$ lattice spacings, the window width is estimated to be $\delta \sim 1-2$ (from comparison with standard lattice QCD scaling analyses).

---

*Document created: 2026-02-13*
*Last revised: 2026-02-13 (post-verification corrections: Λ_FCC, β_c, β_*, R→0 analysis, σ_lat assumption)*
*Classification: 🔮 CONJECTURE (Parts a-b) / 🔶 NOVEL (Part c) / 🔮 CONJECTURE (Part d)*
*Phase: 7 (Renormalization, unitarity, consistency)*
