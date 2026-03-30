# Theorem 4.3.2: W-Soliton Existence and Properties

## Status: 🔶 NOVEL ✅ VERIFIED — W-SECTOR TOPOLOGICAL SOLITONS

**Role in Framework:** This theorem establishes that the W-sector field theory ([Definition 4.3.1](Definition-4.3.1-W-Sector-Field-Theory.md)) supports topologically stable soliton solutions — the dark matter particles of Chiral Geometrogenesis. The W-soliton is the hidden-sector analog of the visible-sector baryon (Theorems 4.1.1–4.1.3), stabilized by the same topological mechanism ($\pi_3(\text{SU}(2)) = \mathbb{Z}$) but operating in the gauge-singlet W domain.

**Dependencies:**
- ✅ Definition 4.3.1 (W-Sector Field Theory) — W condensate field, VEV, gauge properties
- ✅ Theorem 4.1.1 (Soliton Existence from Field Topology) — Existence proof for visible-sector solitons
- ✅ Theorem 4.1.2 (Topological Charge Quantization / Soliton Mass Spectrum) — Mass formula $M = 6\pi^2 f/e$
- ✅ Theorem 4.1.3 (Fermion Number from Topology) — Topological stability mechanism
- ✅ Theorem 4.1.4 (Dynamic Suspension Equilibrium) — Soliton equilibrium in pressure field

**Content Source:** Extracted from [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) §4.2, §6.2, §17. Sections 7–8 (dynamic suspension, self-interaction) are new derivations extending Theorems 4.1.4 and 4.1.1 to the W-sector.

**Lean 4 Formalization:** [Theorem_4_3_2.lean](../../../lean/ChiralGeometrogenesis/Phase4/Theorem_4_3_2.lean)

**Downstream:** [Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) (relic abundance), [Proposition 4.3.4](Proposition-4.3.4-W-Soliton-Structure-Formation.md) (structure formation)

**Computational Verification:**
- `verification/Phase8/issue_1_skyrme_mass_resolution.py` — Mass formula verification
- `verification/Phase8/w_condensate_quantitative_predictions.py` — Quantitative predictions

---

## 1. Statement

**Theorem.** The W-sector field theory (Definition 4.3.1) admits topologically stable soliton solutions with the following properties:

**(a) Topological classification:** W-solitons carry integer topological charge:
$$Q_W \in \mathbb{Z}, \quad Q_W = \frac{1}{24\pi^2}\int_{D_W} d^3x\, \epsilon^{ijk}\,\text{Tr}\bigl[(U_W^\dagger\partial_i U_W)(U_W^\dagger\partial_j U_W)(U_W^\dagger\partial_k U_W)\bigr]$$

where $U_W: D_W \to \text{SU}(2)$ is the W-sector chiral map.

**(b) Soliton mass:** The lightest W-soliton ($|Q_W| = 1$) has mass:
$$\boxed{M_W \approx 1800 \pm 500 \text{ GeV}}$$

bounded between the Faddeev topological lower bound ($6\pi^2 v_W/e_W \approx 1620$ GeV) and the ANW numerical result ($72.92\,v_W/e_W \approx 1993$ GeV), with $v_W = 123 \pm 15$ GeV and $e_W = 4.5 \pm 0.3$.

**(c) Absolute stability:** The lightest W-soliton is topologically protected against decay:
$$\tau_{W} > 10^{34} \text{ years}$$

**(d) Self-interaction cross-section:**
$$\frac{\sigma_{WW}}{M_W} \approx 1.4 \times 10^{-12} \text{ cm}^2/\text{g} \ll 0.2 \text{ cm}^2/\text{g (JWST 2025 bound)}$$

### Key Results Summary

| Property | Value | Source | Status |
|----------|-------|--------|--------|
| Topological charge | $Q_W \in \mathbb{Z}$ | $\pi_3(\text{SU}(2)) = \mathbb{Z}$ | ✅ Established |
| Mass | $1800 \pm 500$ GeV | Faddeev bound to ANW numerical + parameter uncertainties | ✅ Verified |
| Lifetime | $> 10^{34}$ yr | Exact topological stability (gauge singlet) | ✅ Established |
| Self-interaction | $\sigma/m \approx 1.4 \times 10^{-12}$ cm$^2$/g | Geometric cross-section | ✅ Within bounds |
| Spin | 1/2 (fermionic) | Index theorem (Thm 4.1.3) | ✅ Established |

---

## 2. Physical Motivation

### 2.1 Parallel Construction

The visible-sector solitons (baryons) arise from the topological structure of the RGB chiral field:
- The chiral map $U: \mathbb{R}^3 \to \text{SU}(2)$ defines a mapping classified by $\pi_3(\text{SU}(2)) = \mathbb{Z}$
- The Skyrme term stabilizes these solitons against collapse (Derrick's theorem)
- The resulting particles are identified with baryons (proton, neutron)

The W-sector has an **identical topological structure**. The W condensate $\chi_W$ defines a chiral map $U_W$ with the same homotopy classification. The question is not whether solitons exist — that follows from the topology — but what their **properties** are.

### 2.2 Why W-Solitons Are Dark Matter Candidates

W-solitons inherit all the desirable properties of dark matter candidates:
1. **Massive:** $M_W \approx 1.8$ TeV (non-relativistic at matter-radiation equality)
2. **Stable:** Topological protection gives lifetime $\gg$ age of universe
3. **Dark:** Complete gauge singlet — interacts only through gravity and Higgs portal
4. **Predictive:** Mass, coupling, and cross-sections all determined by geometry

---

## 3. Topological Classification

### 3.1 The W-Sector Chiral Map

The W condensate $\chi_W$ (Definition 4.3.1) can be written in the Skyrme parameterization:

$$U_W(x) = \exp\bigl(i\boldsymbol{\tau} \cdot \hat{n}_W(x)\, F_W(r)\bigr)$$

where $\boldsymbol{\tau}$ are the Pauli matrices, $\hat{n}_W(x) = x/|x|$ is the hedgehog ansatz, and $F_W(r)$ is the radial profile function with boundary conditions:

$$F_W(0) = \pi, \quad F_W(\infty) = 0$$

### 3.2 Homotopy Classification

The chiral map $U_W: \mathbb{R}^3 \cup \{\infty\} \cong S^3 \to \text{SU}(2) \cong S^3$ is classified by:

$$\pi_3(\text{SU}(2)) = \mathbb{Z}$$

This is **identical** to the visible-sector classification (Theorem 4.1.1). The topological charge $Q_W$ is an integer that cannot change under continuous deformations of the field.

### 3.3 Topological Charge Integral

The topological charge is:

$$Q_W = \frac{1}{24\pi^2}\int d^3x\, \epsilon^{ijk}\,\text{Tr}\bigl[(U_W^\dagger\partial_i U_W)(U_W^\dagger\partial_j U_W)(U_W^\dagger\partial_k U_W)\bigr] \in \mathbb{Z}$$

For the hedgehog ansatz, this evaluates to:

$$Q_W = \frac{1}{\pi}\bigl[F_W(0) - F_W(\infty)\bigr] - \frac{1}{\pi}\sin\bigl(2F_W(0)\bigr)/2 = 1$$

The same winding number formula applies as in Theorem 4.1.2.

---

## 4. W-Soliton Mass

### 4.1 Skyrme Lagrangian for W-Sector

The W-sector Skyrme Lagrangian is:

$$\mathcal{L}_W = \frac{v_W^2}{4}\,\text{Tr}(\partial_\mu U_W^\dagger \partial^\mu U_W) + \frac{1}{32 e_W^2}\,\text{Tr}\bigl([U_W^\dagger\partial_\mu U_W, U_W^\dagger\partial_\nu U_W]^2\bigr)$$

### 4.2 Mass Formula

Following the standard Skyrme analysis (identical to Theorem 4.1.2 with substitutions $f_\pi \to v_W$, $e \to e_W$):

$$M_W = \frac{6\pi^2 v_W}{e_W} |Q_W|$$

For the lightest soliton ($|Q_W| = 1$):

$$M_W = \frac{6\pi^2 \times 123 \text{ GeV}}{4.5} = \frac{7286}{4.5} \text{ GeV} \approx 1619 \text{ GeV}$$

### 4.3 Skyrme Parameter $e_W$

The Skyrme parameter $e_W$ is determined from the stella geometry. [Proposition 4.3.5](Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) provides the rigorous first-principles derivation from the pressure-curvature integral over the W domain (upgrading the semi-numerical determination in [Proposition 5.1.2b §5.2](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md)):

$$e_W = 4.5 \pm 0.3$$

This is close to the visible-sector value $e \approx 4.84$ (from Adkins-Nappi-Witten fitting), differing by the singlet-vs-triplet geometric factor.

### 4.4 Mass Uncertainty

The mass formula $M_W = 6\pi^2 v_W/e_W$ uses the Faddeev-Bogomolny topological lower bound as an analytical approximation. The full numerically-optimized Skyrme mass is $M_W^{(ANW)} = 72.92\,v_W/e_W \approx 1993$ GeV (Adkins-Nappi-Witten 1983), which is 23% higher. This systematic shift is the dominant uncertainty.

**Uncertainty budget:**

| Source | Contribution | Effect on $M_W$ |
|--------|-------------|-----------------|
| $v_W$ ($\pm 15$ GeV) | $\pm 12\%$ | $\pm 194$ GeV |
| $e_W$ ($\pm 0.3$) | $\pm 7\%$ | $\pm 108$ GeV |
| Higher-order corrections (6-derivative terms) | $\pm 5\%$ | $\pm 81$ GeV |
| Faddeev bound vs ANW numerical | $+23\%$ (one-sided) | $+374$ GeV |
| **Total range** | — | **1330–2400 GeV** |

The mass is bounded between the Faddeev approximation with minimum parameters and the ANW numerical result with maximum parameters:

$$M_W^{(\min)} = \frac{6\pi^2 (v_W - \delta v_W)}{e_W + \delta e_W} = \frac{6\pi^2 \times 108}{4.8} = 1332 \text{ GeV}$$

$$M_W^{(\max)} = \frac{72.92 (v_W + \delta v_W)}{e_W - \delta e_W} = \frac{72.92 \times 138}{4.2} = 2396 \text{ GeV}$$

The central value using the Faddeev bound is 1620 GeV; using the ANW coefficient it is 1993 GeV. We report the geometric mean as the best estimate:

$$\boxed{M_W \approx 1800 \pm 500 \text{ GeV}}$$

where the $\pm 500$ GeV encompasses both the parameter uncertainties and the Faddeev-to-ANW systematic. This is consistent with the EFT validity constraint $M_W \lesssim \Lambda_W = 4\pi v_W \approx 1546$ GeV only at the lower end of the range, indicating that higher-order corrections (6-derivative terms) are important and the Skyrme model gives an order-of-magnitude mass estimate rather than a precision prediction (see §9.3).

> **Convention note:** The formula $M = 6\pi^2 v_W/e_W$ corresponds to the Faddeev-Bogomolny bound $\tilde{E} \geq 12\pi^2 |B|$ in Skyrme units, converted to physical units. The ANW numerical coefficient $72.92 = 1.232 \times 6\pi^2$ accounts for the fact that the B = 1 hedgehog sits 23.2% above this bound. See `verification/Phase8/issue_1_skyrme_mass_resolution.py`.

---

## 5. Topological Stability

### 5.1 Faddeev-Bogomolny Topological Bound

The W-soliton energy satisfies the Faddeev-Bogomolny topological lower bound (Faddeev 1976):

$$E_W \geq \frac{6\pi^2 v_W}{e_W} |Q_W|$$

where the coefficient $6\pi^2 = 59.22$ in physical units corresponds to $12\pi^2 = 118.44$ in dimensionless Skyrme units. This bound is derived from the Cauchy-Schwarz inequality between the sigma-model and Skyrme energy densities, and is **not saturated** — no BPS solution exists in the standard Skyrme model.

The numerically-optimized B = 1 hedgehog Skyrmion (Adkins-Nappi-Witten 1983) has energy $\tilde{E} = 1.232 \times 12\pi^2 = 145.9$ in Skyrme units, giving a physical mass coefficient of $72.92\,v_W/e_W$ — i.e., 23.2% above the Faddeev bound. The formula $M_W = 6\pi^2 v_W/e_W$ used in §4.2 is therefore the **topological lower bound**, not the full numerical mass. The systematic shift is accounted for in the uncertainty budget (§4.4).

### 5.2 Skyrme Stabilization

The Skyrme term (fourth-order derivative term in $\mathcal{L}_W$) prevents collapse by Derrick's theorem. Under a spatial rescaling $x \to \lambda x$ (with $\lambda > 1$ compressing the configuration), the energy components in $d = 3$ scale as $E_2 \sim \lambda^{-1}$ and $E_4 \sim \lambda^{+1}$. Equivalently, parameterizing by soliton size $R$:
- The sigma-model (kinetic) term has energy $E_2 \propto R$, so it favors **contraction** (smaller $R$ lowers $E_2$)
- The Skyrme (fourth-derivative) term has energy $E_4 \propto 1/R$, so it favors **expansion** (larger $R$ lowers $E_4$)
- The balance at the energy minimum $dE/dR = 0$ gives a stable soliton of finite size, with the virial relation $E_2 = E_4$

### 5.3 Topological Protection

The topological charge $Q_W \in \mathbb{Z}$ is conserved:
- No continuous field evolution can change $Q_W$
- The lightest soliton ($|Q_W| = 1$) cannot decay to $Q_W = 0$ (vacuum)
- This gives **proton-like** stability: $\tau_W > 10^{34}$ years

The decay channels that could violate this are:
1. **Gauge boson emission:** Forbidden — W-soliton is a complete gauge singlet
2. **Gravitational decay:** Suppressed by $(M_W/M_P)^4 \sim 10^{-64}$
3. **Portal-mediated decay:** Forbidden — requires $\Delta Q_W \neq 0$, but the Higgs portal coupling $\lambda_{H\Phi} |\Phi_W|^2 |H|^2$ conserves $Q_W$
4. **Topological unwinding:** In a pure Skyrme model (no gauge fields), the topological charge $Q_W$ is **exactly conserved** — there is no sphaleron or instanton path connecting sectors of different $Q_W$. This is because sphalerons require gauge fields (as in electroweak baryon number violation, where $S_{EW} = 2\pi/\alpha_W \sim 185$), but the W-soliton is a complete gauge singlet with no gauge coupling. The topological protection is therefore exact, not merely exponentially suppressed.

### 5.4 Stability Hierarchy

$$\tau_W \gg \tau_{proton} > 10^{34} \text{ yr} \gg \tau_{universe} \approx 1.4 \times 10^{10} \text{ yr}$$

W-solitons are **absolutely stable** on cosmological timescales.

---

## 6. Soliton Classification and Dark Matter Candidacy

### 6.1 W-Soliton vs Visible-Sector Soliton Comparison

| Property | Visible (Baryon) | W-Soliton | Ratio |
|----------|-----------------|-----------|-------|
| Chiral map | $U: S^3 \to \text{SU}(2)$ | $U_W: S^3 \to \text{SU}(2)$ | Same topology |
| Homotopy | $\pi_3(\text{SU}(2)) = \mathbb{Z}$ | $\pi_3(\text{SU}(2)) = \mathbb{Z}$ | Identical |
| VEV | $f_\pi = 92.1$ MeV | $v_W = 123$ GeV | $v_W/f_\pi \approx 1340$ |
| Skyrme parameter | $e = 4.84$ | $e_W = 4.5$ | $e_W/e \approx 0.93$ |
| Mass | $M_p = 938$ MeV | $M_W \approx 1800$ GeV | $M_W/M_p \approx 1900$ |
| Color charge | Triplet (confined) | **Singlet** | — |
| EW charge | Non-trivial | **Singlet** | — |
| Stability | Topological | Topological | Same mechanism |
| Domain | $D_{RGB}$ | $D_W$ | Geometrically separated |
| Observability | Visible | **Dark** | — |

**Key insight:** The W-soliton is **the same type of topological object** as the proton, just operating at a different energy scale and in the gauge-singlet sector.

### 6.2 Complete Soliton Classification on $\partial\mathcal{S}$

The stella octangula $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ has 8 vertices organized into 4 sectors ([Definition 0.1.1](../Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md) §2.2). Each vertex supports a chiral condensate and, in principle, topological soliton solutions. The complete classification is:

| Sector | Tetrahedron | Vertices | Gauge Charges | Soliton Type |
|--------|-------------|----------|---------------|--------------|
| **Color** | $T_+$ | $v_R, v_G, v_B$ | SU(3)$_c$ triplet, SU(2)$_L$ non-trivial | Visible baryons ($Q > 0$) |
| **Singlet** | $T_+$ / $T_-$ combined | $v_W, v_{\bar{W}}$ | Complete gauge singlet | **W-soliton** ($Q_W > 0$) |
| **Anti-color** | $T_-$ | $v_{\bar{R}}, v_{\bar{G}}, v_{\bar{B}}$ | SU(3)$_c$ anti-triplet, SU(2)$_L$ non-trivial | Antibaryons ($Q < 0$) |
| **Anti-W** | — (see below) | — | Complete gauge singlet | Anti-W-soliton ($Q_W < 0$) |

**Critical structural point:** The W condensate is **not** localized on a single tetrahedron. The $T_+ \leftrightarrow T_-$ exchange symmetry maps $v_W = (1,1,1)/\sqrt{3}$ to $v_{\bar{W}} = (-1,-1,-1)/\sqrt{3}$, and the W condensate is the *symmetric combination* of both vertices ($\chi_W^{T_+} = \chi_W^{T_-}$ up to phase), transforming as the SU(2)$_L$ singlet ([Definition 4.3.1](Definition-4.3.1-W-Sector-Field-Theory.md) §7.2). There is therefore a **single W sector** spanning both tetrahedra, not separate W and $\bar{W}$ sectors. The "anti-W-soliton" is the anti-particle (topological charge $Q_W = -1$) within this single sector, not a soliton at a separate vertex.

We now systematically evaluate each sector's viability as a dark matter candidate.

### 6.3 Anti-Color Soliton Exclusion ($\bar{R}$, $\bar{G}$, $\bar{B}$ Sectors)

The anti-color vertices on $T_-$ support soliton solutions with negative topological charge ($Q < 0$) — these are **antibaryons** (antiprotons, antineutrons). They are excluded as dark matter candidates by three independent arguments:

**(i) Strong interactions.** Anti-color solitons carry SU(3)$_c$ anti-triplet charge. They interact strongly with visible matter via the QCD coupling $\alpha_s \sim 0.3$ at the confinement scale. Any relic population would bind with baryonic matter, forming exotic hadronic states, in gross conflict with observation.

**(ii) Cosmological depletion by baryogenesis.** The chiral bias mechanism ([Theorem 4.2.1](Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md)) preferentially produces positive-charge solitons ($Q > 0$, baryons) over negative-charge solitons ($Q < 0$, antibaryons). After the EWPT, baryon–antibaryon annihilation depletes the symmetric component, leaving only the baryon excess $\eta_B = 6.1 \times 10^{-10}$. The antibaryon relic abundance is negligible.

**(iii) Electroweak charge.** Anti-color solitons are also non-trivial under SU(2)$_L \times$ U(1)$_Y$, giving them electromagnetic and weak interactions. They are not "dark" by any criterion.

**Conclusion:** Anti-color solitons are observable antibaryons, not dark matter. ✗

### 6.4 Anti-W-Soliton ($Q_W < 0$) Analysis

Within the single W sector (§6.2), anti-W-solitons carry topological charge $Q_W = -1$. Their properties are **identical** to W-solitons (same mass $M_W$, same gauge-singlet status, same stability) but with opposite topological charge. The question is whether they constitute a separate dark matter population.

**They do not**, because the ADM mechanism ([Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md)) depletes them:

1. **Production asymmetry.** The chiral phase factor $f_{chiral} = -\sqrt{3}$ (Proposition 4.3.3 §5.5) preferentially produces W-solitons ($Q_W = +1$) over anti-W-solitons ($Q_W = -1$), with asymmetry $\epsilon_W = \kappa_W^{geom} \cdot \eta_B \approx 3.1 \times 10^{-13}$.

2. **Symmetric annihilation.** $W + \bar{W}$ pairs annihilate via SU(2)$_W$ gauge interactions with cross-section $\langle\sigma v\rangle_{total} \approx 10^{-22}$ cm$^3$/s (Proposition 4.3.3 §4.2). The symmetric component is depleted by a factor $\delta_{sym} \approx 1.6 \times 10^{-6} \ll 1$.

3. **Residual abundance.** The surviving anti-W-soliton density is suppressed by $\delta_{sym}$ relative to the W-soliton density:

$$n_{\bar{W}}^{residual} \approx \delta_{sym} \times \epsilon_W \times s \approx 10^{-6} \times n_W$$

This is negligible. The dark matter is composed entirely of W-solitons ($Q_W = +1$).

**Conclusion:** Anti-W-solitons are not a separate DM candidate; they are the depleted anti-particles of the W-soliton. ✗

### 6.5 Uniqueness of W-Soliton as Dark Matter Candidate

**Theorem (Uniqueness).** Among all soliton sectors on $\partial\mathcal{S}$, the W-soliton ($Q_W = +1$) is the **unique** viable dark matter candidate.

*Proof.* By exhaustive classification (§6.2), the stella octangula supports solitons in four sectors. We eliminate each alternative:

| Candidate | Excluded by | Section |
|-----------|------------|---------|
| Anti-color solitons ($\bar{R}, \bar{G}, \bar{B}$) | Strong interactions + baryogenesis depletion | §6.3 |
| Anti-W-solitons ($Q_W = -1$) | ADM symmetric annihilation ($\delta_{sym} \sim 10^{-6}$) | §6.4 |
| Visible baryons ($R, G, B$) | Strongly interacting, electromagnetic — by definition not dark | §6.1 |

The W-soliton ($Q_W = +1$) survives all exclusion criteria:
- **Gauge singlet** → dark by construction (§5.3, [Definition 4.3.1](Definition-4.3.1-W-Sector-Field-Theory.md) §7.3)
- **Topologically stable** → lifetime $> 10^{34}$ yr (§5)
- **Asymmetric production** → survives ADM depletion as the majority species (§6.4)
- **TeV-scale mass** → non-relativistic at matter-radiation equality, CDM-compatible ([Proposition 4.3.4](Proposition-4.3.4-W-Soliton-Structure-Formation.md))

No other topological soliton on $\partial\mathcal{S}$ satisfies all four criteria simultaneously. $\square$

### 6.6 Comparison of All Soliton Sectors

| Property | Baryon (RGB) | W-Soliton ($Q_W\!>\!0$) | Antibaryon ($\bar{R}\bar{G}\bar{B}$) | Anti-W ($Q_W\!<\!0$) |
|----------|:---:|:---:|:---:|:---:|
| Mass scale | $\sim 1$ GeV | $\sim 1.8$ TeV | $\sim 1$ GeV | $\sim 1.8$ TeV |
| Color charge | Triplet | **Singlet** | Anti-triplet | **Singlet** |
| EW charge | Non-trivial | **None** | Non-trivial | **None** |
| Topological stability | $\pi_3 = \mathbb{Z}$ | $\pi_3 = \mathbb{Z}$ | $\pi_3 = \mathbb{Z}$ | $\pi_3 = \mathbb{Z}$ |
| Cosmological survival | ✅ (baryogenesis) | ✅ (ADM majority) | ✗ (annihilated) | ✗ ($\delta_{sym} \sim 10^{-6}$) |
| Interacts with matter? | Strongly | Gravity + portal only | Strongly | Gravity + portal only |
| **DM viable?** | **No** (visible) | **Yes** (unique) | **No** (depleted + visible) | **No** (depleted) |

---

## 7. Dynamic Suspension in W Domain

> **Important distinction:** The dynamic suspension mechanism describes confinement in **field-theory internal space** (the pre-geometric domain structure on $\partial\mathcal{S}$), not localization in physical spacetime. After spacetime emergence (Phase 5), W-solitons are free-streaming massive particles distributed across galactic halos. The domain $D_W$ constrains the soliton's **internal field structure** — analogous to how a proton's quark fields are confined within $\sim 1$ fm while the proton itself moves freely through space.

### 7.1 Extension of Theorem 4.1.4

Theorem 4.1.4 (Dynamic Suspension Equilibrium) establishes that visible-sector solitons exist in a state of dynamic suspension, maintained by the equilibrium of the three color field pressures. The **same mechanism** applies to the W-sector, with $P_W(x)$ replacing the role of $P_{RGB}(x)$.

### 7.2 Equilibrium Condition

The W-soliton sits at the equilibrium point of the W-domain pressure field:

$$\nabla V_{eff}^{(W)}(x_0) = 0$$

where the effective potential is:

$$V_{eff}^{(W)}(x_0) = \lambda_W \int d^3x \, \rho_W^{sol}(x - x_0) \cdot P_W(x) + V_{top}^{(W)}$$

### 7.3 Stability

The W-sector effective potential has a positive-definite Hessian at equilibrium:

$$K_{ij}^{(W)} = \frac{\partial^2 V_{eff}^{(W)}}{\partial x_0^i \partial x_0^j}\bigg|_{x_0 = x_0^{eq}} > 0$$

This follows from the same argument as Theorem 4.1.4 §6.2: the pressure function $P_W(x)$ has a unique maximum within $D_W$, and the soliton-pressure overlap integral is a convex function of position near this maximum.

### 7.4 Confinement

Unlike visible-sector solitons (which are confined by the balance of three color pressures), W-solitons are confined to the W domain by the **single** W pressure function. The confinement is less tight — the restoring force scales as:

$$F_{restore}^{(W)} \sim K_W^{(0)} \delta x$$

with stiffness $K_W^{(0)}$ determined by the curvature of $P_W(x)$ at its maximum. This weaker confinement is consistent with the W-soliton's role as a weakly-interacting particle.

---

## 8. Self-Interaction Cross-Section

### 8.1 Cross-Section Estimates

Two approaches bracket the W-soliton self-interaction:

**Perturbative (lower bound).** Treating W-solitons as point particles interacting via the Higgs portal gives $\sigma \sim \lambda_{H\Phi}^2/(16\pi M_W^2) \sim 10^{-35}$ cm$^2$. This underestimates the soliton-soliton cross-section because it ignores the extended field structure.

**Geometric (primary estimate).** For extended solitons, the dominant contribution comes from the overlap of their chiral field profiles at impact parameters $b \lesssim r_W$. The geometric cross-section is:

$$\sigma_{WW} \approx \pi r_W^2$$

where the soliton radius is:

$$r_W \sim \frac{1}{e_W v_W} = \frac{1}{4.5 \times 123 \text{ GeV}} \approx \frac{1}{554 \text{ GeV}} \approx 3.6 \times 10^{-17} \text{ cm}$$

Therefore:

$$\sigma_{WW} \approx \pi (3.6 \times 10^{-17})^2 \approx 4 \times 10^{-33} \text{ cm}^2$$

### 8.2 Self-Interaction per Unit Mass

$$\frac{\sigma_{WW}}{M_W} = \frac{4 \times 10^{-33} \text{ cm}^2}{1620 \text{ GeV} \times 1.78 \times 10^{-24} \text{ g/GeV}} \approx \frac{4 \times 10^{-33}}{2.9 \times 10^{-21}} \approx 1.4 \times 10^{-12} \text{ cm}^2/\text{g}$$

This geometric estimate is the dominant contribution. In standard Skyrmion-Skyrmion scattering, low-energy resonance enhancements are $\mathcal{O}(10)$ (comparable to $\Delta(1232)$ enhancement in $\pi N$ scattering; see Manton 2025, arXiv:2505.12362), which would give at most $\sigma/m \sim 10^{-11}$ cm$^2$/g — still far below observational bounds.

### 8.3 Observational Compatibility

The observational constraints on dark matter self-interaction from cluster mergers are:

| Source | Bound ($\sigma/m$) | Reference |
|--------|-------------------|-----------|
| Bullet Cluster (offset) | $< 5$ cm$^2$/g | Markevitch et al. (2004) |
| Bullet Cluster (simulations) | $< 1.25$ cm$^2$/g (68% CL) | Randall et al. (2008) |
| 72 cluster ensemble | $< 0.47$ cm$^2$/g (95% CL) | Harvey et al. (2015) |
| JWST Bullet Cluster | $< 0.2$ cm$^2$/g | Cha et al. (2025) |

The W-soliton geometric self-interaction satisfies the tightest current bound by a factor of $\sim 10^{11}$:

$$\boxed{\frac{\sigma_{WW}}{M_W} \approx 1.4 \times 10^{-12} \text{ cm}^2/\text{g} \ll 0.2 \text{ cm}^2/\text{g (JWST 2025)}}$$

W-soliton dark matter is effectively **collisionless** on astrophysical scales.

---

## 9. Consistency Checks

### 9.1 Big Bang Nucleosynthesis (BBN)

As a BBN consistency check, the temperature at which W-solitons decouple from the thermal bath can be estimated from the standard WIMP freeze-out formula:

$$T_{dec} \approx \frac{M_W}{20} \approx 90 \text{ GeV}$$

(using $M_W \approx 1800$ GeV). This estimate applies to thermal freeze-out; in the ADM scenario ([Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md)), the relevant decoupling temperature is set by the $Q_W$-asymmetry transfer mechanism and is similarly $\gg T_{BBN}$. In either case, $T_{dec} \gg T_{BBN} \sim 1$ MeV, so W-solitons have **no impact** on light element abundances. ✅

### 9.2 Cosmic Microwave Background (CMB)

W-solitons are topologically stable and do not annihilate efficiently at late times. The Higgs-portal annihilation cross-section is:

$$\langle\sigma v\rangle \sim \frac{\lambda_{H\Phi}^2}{16\pi M_W^2} \cdot c \approx 1.2 \times 10^{-28} \text{ cm}^3/\text{s}$$

This is a factor $\sim 260$ below the thermal relic value $\langle\sigma v\rangle_{th} \approx 3 \times 10^{-26}$ cm$^3$/s, meaning the portal coupling alone is **insufficient** to annihilate the symmetric component via thermal freeze-out (which would give $\Omega h^2 \sim 30$, over-abundant by $\sim 250\times$). This confirms the necessity of the asymmetric dark matter (ADM) production mechanism ([Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md)), where a primordial $Q_W$ asymmetry (analogous to baryogenesis) sets the relic abundance.

For the CMB constraint specifically: with $\langle\sigma v\rangle \sim 10^{-28}$ cm$^3$/s and $M_W \sim 1.8$ TeV, the effective energy deposition parameter $f_{eff}\langle\sigma v\rangle/M_W \sim 10^{-31}$ cm$^3$/s/GeV is far below the Planck bound of $3.5 \times 10^{-28}$ cm$^3$/s/GeV. There is **no** late-time energy injection that would distort the CMB spectrum, regardless of whether the symmetric component is depleted. ✅

### 9.3 EFT Validity and Unitarity

The portal coupling satisfies perturbative unitarity:

$$\lambda_{H\Phi} = 0.036 \ll \frac{4\pi}{3} \approx 4.2$$

**EFT cutoff.** The Skyrme model is a low-energy effective theory valid below $\Lambda_W = 4\pi v_W \approx 1546$ GeV. The soliton mass $M_W \approx 1800$ GeV exceeds this cutoff ($M_W/\Lambda_W \approx 1.2$), meaning higher-order operators (6-derivative terms and beyond) contribute at the same order as the Skyrme term. For comparison, in the visible sector $M_N/\Lambda_\chi \approx 938/1160 \approx 0.81$ — the nucleon mass is below the chiral EFT cutoff, but only marginally.

This is a well-known limitation of the Skyrme model: the classical soliton mass generically sits near or above the EFT cutoff. The W-soliton mass prediction should therefore be understood as an **order-of-magnitude estimate** ($M_W \sim 1$–$2$ TeV) rather than a precision calculation. The wide uncertainty range ($\pm 500$ GeV) in §4.4 accounts for this.

Crucially, the **topological stability** ($Q_W$ conservation) is exact and does not depend on the EFT validity — it follows from the homotopy classification $\pi_3(\text{SU}(2)) = \mathbb{Z}$, which holds nonperturbatively. ✅

### 9.4 Dimensional Analysis Summary

| Quantity | Expression | Value | Dimensions | Check |
|----------|-----------|-------|------------|-------|
| $M_W$ (Faddeev) | $6\pi^2 v_W/e_W$ | 1620 GeV | [Energy] | ✅ |
| $M_W$ (ANW) | $72.92\,v_W/e_W$ | 1993 GeV | [Energy] | ✅ |
| $M_W$ (central) | — | $1800 \pm 500$ GeV | [Energy] | ✅ |
| $r_W$ | $1/(e_W v_W)$ | 0.00036 fm | [Length] | ✅ |
| $\sigma_{WW}$ | $\pi r_W^2$ | $4 \times 10^{-33}$ cm$^2$ | [Area] | ✅ |
| $\sigma/m$ | $\sigma_{WW}/M_W$ | $1.4 \times 10^{-12}$ cm$^2$/g | — | ✅ |
| $\Lambda_W$ | $4\pi v_W$ | 1546 GeV | [Energy] | ✅ |
| $T_{dec}$ | $\sim M_W/20$ | $\sim 90$ GeV | [Energy] | ✅ |
| $\tau_W$ | $> 10^{34}$ yr | — | [Time] | ✅ |

---

## 10. Summary

**Theorem 4.3.2** establishes that the W-sector supports topologically stable solitons that are:

1. **Classified** by $\pi_3(\text{SU}(2)) = \mathbb{Z}$ — same homotopy as visible baryons
2. **Massive** at $M_W \approx 1800 \pm 500$ GeV — bounded between Faddeev bound ($6\pi^2 v_W/e_W$) and ANW numerical result ($72.92\,v_W/e_W$)
3. **Absolutely stable** with $\tau > 10^{34}$ yr — exact topological protection (gauge singlet, no sphaleron path)
4. **Effectively collisionless** with $\sigma/m \sim 10^{-12}$ cm$^2$/g — satisfies JWST 2025 bound by $\sim 10^{11}$
5. **Dark by construction** — complete gauge singlet
6. **Suspended** in the W domain (field-theory internal space) by pressure equilibrium — extending Theorem 4.1.4
7. **Consistent** with BBN, CMB (including symmetric component analysis), and unitarity bounds; relic abundance requires ADM mechanism

These properties make W-solitons a natural dark matter candidate within Chiral Geometrogenesis. Moreover, the exhaustive classification of all soliton sectors on $\partial\mathcal{S}$ (§6.2–§6.5) establishes that the W-soliton is the **unique** viable dark matter candidate: anti-color solitons are excluded by strong interactions and baryogenesis, and anti-W-solitons are depleted by the ADM mechanism.

The mass prediction is an order-of-magnitude estimate ($M_W \sim 1$–$2$ TeV) due to the soliton mass sitting near the EFT cutoff $\Lambda_W = 4\pi v_W \approx 1.5$ TeV, a well-known limitation of the Skyrme model approach.

---

## 11. References

**CG Framework:**
- [Definition 0.1.1](../Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md) — Stella octangula vertex structure (§6.2)
- [Definition 4.3.1](Definition-4.3.1-W-Sector-Field-Theory.md) — W-sector field theory
- [Theorem 4.1.1](Theorem-4.1.1-Soliton-Existence-From-Field-Topology.md) — Soliton existence from field topology
- [Theorem 4.1.2](Theorem-4.1.2-Topological-Charge-Quantization.md) — Soliton mass spectrum
- [Theorem 4.1.3](Theorem-4.1.3-Baryon-Number-Conservation.md) — Fermion number from topology
- [Theorem 4.1.4](Theorem-4.1.4-Dynamic-Suspension-Equilibrium.md) — Dynamic suspension equilibrium
- [Theorem 4.2.1](Theorem-4.2.1-Chiral-Bias-Soliton-Formation.md) — Chiral bias / baryogenesis (§6.3)
- [Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) — ADM relic abundance / anti-W depletion (§6.4)
- [Proposition 4.3.4](Proposition-4.3.4-W-Soliton-Structure-Formation.md) — Structure formation compatibility (§6.5)
- [Proposition 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) — Self-consistent $v_W$, $e_W$
- [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) — Observational predictions

**External Physics — Skyrme Model:**
- Skyrme, T.H.R. (1962). "A unified field theory of mesons and baryons." *Nucl. Phys.* 31, 556–569.
- Adkins, G.S., Nappi, C.R. & Witten, E. (1983). "Static properties of nucleons in the Skyrme model." *Nucl. Phys. B* 228, 552–566.
- Witten, E. (1983). "Current algebra, baryons, and quark confinement." *Nucl. Phys. B* 223, 433–444.
- Manton, N.S. (2025). "Approach to nuclear cross sections via classical Skyrmion scattering." [arXiv:2505.12362]

**External Physics — Skyrmion Dark Matter (Prior Work):**
- Kitano, R. & Kurachi, M. (2016). "Electroweak-Skyrmion as topological dark matter." *JHEP* 07, 037. [arXiv:1605.07355]
- Gudnason, S.B. & Rishi, M. (2017). "Very heavy dark Skyrmions." *Eur. Phys. J. C* 77, 813. [arXiv:1709.02213]
- Hamada, Y., Kitano, R. & Kurachi, M. (2022). "Electroweak-Skyrmion as asymmetric dark matter." *JHEP* 02, 124. [arXiv:2112.01388]

**External Physics — DM Self-Interaction Constraints:**
- Markevitch, M. et al. (2004). "Direct constraints on the dark matter self-interaction cross-section from the merging galaxy cluster 1E 0657-56." *ApJ* 606, 819. [arXiv:astro-ph/0309303]
- Randall, S.W. et al. (2008). "Constraints on the self-interaction cross section of dark matter from numerical simulations of the merging galaxy cluster 1E 0657-56." *ApJ* 679, 1173. [arXiv:0704.0261]
- Harvey, D. et al. (2015). "The nongravitational interactions of dark matter in colliding galaxy clusters." *Science* 347, 1462. [arXiv:1503.07675]
- Robertson, A., Massey, R. & Eke, V. (2017). "What does the Bullet Cluster tell us about self-interacting dark matter?" *MNRAS* 465, 569. [arXiv:1605.04307]
- Cha, S. et al. (2025). "JWST constraints on dark matter self-interactions from the Bullet Cluster." Accepted to *ApJL*. [arXiv:2601.22245]

**Computational Verification:**
- `verification/Phase8/issue_1_skyrme_mass_resolution.py`
- `verification/Phase8/w_condensate_quantitative_predictions.py`
- `verification/Phase4/theorem_4_3_2_adversarial_verification.py` — Adversarial physics verification (10 tests, 4 plots)

**Verification Records:**
- [Multi-Agent Verification Report (2026-02-25)](../verification-records/Theorem-4.3.2-Multi-Agent-Verification-2026-02-25.md) — Literature, Mathematics, Physics agents
