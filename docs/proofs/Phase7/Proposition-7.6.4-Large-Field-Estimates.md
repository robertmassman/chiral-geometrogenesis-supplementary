# Proposition 7.6.4: Large-Field Estimates on D₄ Lattice

**Status:** 🔶 NOVEL (D₄-specific Peierls estimates) / ✅ ESTABLISHED (Balaban large-field framework)

**Role in framework:** Fourth and final geometric input (G.2d) for the Balaban RG iteration on the FCC/D₄ lattice. Shows that gauge field configurations outside the small-field region are exponentially suppressed.

**Classification:**
- Part (a): ✅ ESTABLISHED (definition) + 🔶 NOVEL (D₄ geometry)
- Part (b): ✅ ESTABLISHED (Wilson action convexity) + 🔶 NOVEL (triangular plaquette estimates)
- Part (c): 🔶 NOVEL (Peierls estimate with D₄ entropy/energy balance)
- Part (d): 🔶 NOVEL (polymer expansion and exponential suppression on D₄)

**Key results:**
- (a) Large-field region Ω_k^ℓ is the complement of Ω_k^s from Prop 7.6.3
- (b) Action penalty: ΔS_p ≥ p₀² g_k^{-2δ}/6 per violated plaquette; ΔS_γ ≥ p₀² g_k^{-2δ} V/(18) for a polymer of V vertices
- (c) Peierls exponent κ_FCC = p₀²g_k^{-2δ}/18 − ln(24) > 0 for g_k² < g_crit² ≈ 3×10⁻⁷
- (d) Exponential suppression: Z_k^ℓ ≤ C · exp(−κ_FCC · V_k / g_k²)

**Dependencies:**
- ✅ Proposition 7.6.3 — Regular configuration space Ω_k^s, regularity constant p₀^{D₄}
- ✅ Proposition 7.6.2 — Propagator bounds, Combes-Thomas estimates
- ✅ Proposition 7.6.1 — Averaging kernel Q_FCC
- ✅ Theorem 7.5.3 — Crossover path, mass gap persistence

**Enables:**
- Theorem 7.6.5 — Small-Field UV Stability on FCC
- Phase G.2 completion (all four geometric inputs established)

## File Structure

| File | Purpose | Sections |
|------|---------|----------|
| **Proposition-7.6.4-Large-Field-Estimates.md** (this file) | Statement & motivation | §1–4, §9–10 |
| [Proposition-7.6.4-Large-Field-Estimates-Derivation.md](./Proposition-7.6.4-Large-Field-Estimates-Derivation.md) | Complete derivation | §5–8, Appendices |
| [Proposition-7.6.4-Large-Field-Estimates-Applications.md](./Proposition-7.6.4-Large-Field-Estimates-Applications.md) | Verification & physics | §9–12 |

---

## §0. Verification Status

**Verification date:** 2026-02-14
**Status:** ✅ VERIFIED — All 12 findings resolved (5 corrections + 7 warnings)

### Verification Checklist

- [x] Standard verification script: `verification/Phase7/prop_7_6_4_large_field_estimates.py` — 13/13 PASS
- [x] Adversarial verification script: `verification/Phase7/prop_7_6_4_adversarial_physics.py` — 12/12 PASS
- [x] Multi-agent verification: [Proposition-7.6.4-Multi-Agent-Verification-2026-02-14.md](../verification-records/Proposition-7.6.4-Multi-Agent-Verification-2026-02-14.md)
- [x] Plots generated:
  - `verification/plots/prop_7_6_4_adversarial_verification.png`
  - `verification/plots/prop_7_6_4_peierls_comparison.png`

### Findings and Resolutions

| ID | Severity | Summary | Resolution |
|----|----------|---------|------------|
| **F1** | Critical | Per-site penalty gap between statement and derivation | ✅ RESOLVED: Conservative vertex-covering bound used throughout; tight bound labeled as conjecture |
| **F2** | Significant | Z⁴ comparison formula inconsistent | ✅ RESOLVED: Both D₄ and Z⁴ use same conservative convention |
| **F3** | Significant | Incorrect inequality direction in KP verification | ✅ RESOLVED: Corrected to $-\ln(1-\varepsilon) \leq 2\varepsilon$ for $\varepsilon \leq 1/2$ |
| **F4** | Significant | Reference 11 wrong authors/title | ✅ RESOLVED: Replaced with Celmaster (1982) |
| **F5** | Moderate | SU(3) volume factor c_vol dropped | ✅ RESOLVED: Normalized Haar measure ($\int dU = 1$) eliminates c_vol |
| **W1–W7** | Low | Various exposition improvements | ✅ RESOLVED |

See [full verification report](../verification-records/Proposition-7.6.4-Multi-Agent-Verification-2026-02-14.md) for complete details.

---

## §1. Formal Statement

### Part (a): Large-Field Region Definition ✅ ESTABLISHED + 🔶 NOVEL

*Let $\Lambda_k = D_4(\eta_k)$ be the $D_4$ lattice at RG scale $k$ with lattice spacing $\eta_k = 2^k a$, and let $\Omega_k^s$ be the small-field (regular) configuration space defined in Prop 7.6.3, Part (a). The **large-field region** is the complement:*

$$\boxed{\Omega_k^\ell := \mathcal{A}_k \setminus \Omega_k^s = \{U \in \mathcal{A}_k : \exists\, p \text{ s.t. } \|U_p - \mathbb{1}\| > p_0\, g_k^{1-\delta}\}}$$

*where $\mathcal{A}_k$ is the full gauge field configuration space on $\Lambda_k$.*

**(a.1) Connected large-field regions.** *A connected large-field region (polymer) $\gamma \subset \Lambda_k$ is a maximal connected subset of vertices $x$ such that at least one plaquette touching $x$ violates the small-field condition. Two vertices are connected if they are nearest neighbors on $D_4$ (distance $\eta_k\sqrt{2}$).*

**(a.2) Coordination number.** *Each vertex of $D_4$ has $z = 24$ nearest neighbors (vs. $z = 8$ on $\mathbb{Z}^4$). This gives a lattice animal entropy bound:*

$$N_{D_4}(V) \leq e \cdot z_{\text{eff}}^V, \qquad z_{\text{eff}} = 24$$

*where $N_{D_4}(V)$ is the number of connected subsets of volume $V$ containing a fixed vertex.*

**(a.3) Large-field link.** *A link $\ell$ is a **large-field link** if any plaquette containing $\ell$ violates the small-field condition. On $D_4$, each link participates in $n_\triangle^\ell = 8$ triangular plaquettes (Prop 7.6.3, Part (a.4)).*

### Part (b): Action Penalty Bound ✅ ESTABLISHED + 🔶 NOVEL

*For any configuration $U \in \Omega_k^\ell$ with $n_p$ violated plaquettes (i.e., plaquettes $p$ satisfying $\|U_p - \mathbb{1}\| > p_0\, g_k^{1-\delta}$), the action penalty relative to the minimum is:*

$$\boxed{\Delta\mathcal{S} := \mathcal{S}_\text{FCC}(U) - \mathcal{S}_\text{FCC}(\mathbb{1}) \geq \frac{p_0^2\, g_k^{2(1-\delta)}}{6g_k^2} \cdot n_p = \frac{p_0^2\, g_k^{-2\delta}}{6} \cdot n_p}$$

*where the factor $1/6 = 1/(2N_c)$ for $SU(3)$ comes from the Wilson action normalization.*

**(b.1) Per-plaquette penalty.** *Each violated triangular plaquette contributes:*

$$\Delta S_p \geq \frac{1}{g_k^2}\left(1 - \frac{1}{3}\operatorname{Re}\operatorname{Tr}\, U_p\right) \geq \frac{p_0^2\, g_k^{2(1-\delta)}}{6g_k^2} = \frac{p_0^2\, g_k^{-2\delta}}{6}$$

**(b.2) Per-vertex violation count.** *Each large-field vertex $x$ touches at least one violated plaquette $p_x$. Since plaquettes on $D_4$ are triangular, each violated plaquette has 3 vertices — all of which are large-field (they touch a violated plaquette) and hence belong to the same polymer (they are mutual nearest neighbors). For a connected polymer of $V$ vertices, the minimum number of distinct violated plaquettes is $\lceil V/3 \rceil$, since each plaquette covers at most 3 vertices.*

**(b.3) Total penalty for a region of volume $V$.** *A connected large-field region of $V$ vertices has at least $\lceil V/3 \rceil$ distinct violated plaquettes, giving:*

$$\Delta S_\gamma \geq \left\lceil \frac{V}{3}\right\rceil \cdot \frac{p_0^2\, g_k^{-2\delta}}{6} \geq \frac{V}{3} \cdot \frac{p_0^2\, g_k^{-2\delta}}{6} = \frac{p_0^2\, g_k^{-2\delta}}{18} \cdot V$$

**(b.4) Conjectured tight bound.** *If each large-field link has ALL $n_\triangle^\ell = 8$ touching plaquettes violated (heuristically expected when $\|U_\ell - \mathbb{1}\|$ is large), the per-site penalty would improve to $(4/3)p_0^2 g_k^{-2\delta}$. This 24× enhancement over the proven bound is not rigorously established because a violated plaquette $U_p = U_{\ell_1}U_{\ell_2}U_{\ell_3}$ far from identity does not imply any individual link $U_{\ell_i}$ is far from identity (non-abelian cancellation). The proven bound (b.3) suffices for the Peierls argument.*

### Part (c): Peierls Estimate on D₄ 🔶 NOVEL

*The Peierls argument balances the action penalty (energy) against the combinatorial entropy of large-field regions:*

$$\boxed{\kappa_\text{FCC} := \frac{p_0^2\, g_k^{-2\delta}}{18} - \ln(24) > 0 \quad \text{for } g_k^2 < g_{\text{crit}}^2}$$

*where $\kappa_\text{FCC}$ is the **Peierls exponent** on $D_4$. The denominator $18 = 6 \times 3$ reflects the per-plaquette penalty factor $1/6$ (from $1/(2N_c)$ with $N_c = 3$) and the vertex-covering factor $1/3$ (each triangular plaquette covers 3 vertices).*

**(c.1) Critical coupling.** *The Peierls exponent vanishes at:*

$$g_{\text{crit}}^2 = \left(\frac{p_0^2}{18\ln 24}\right)^{1/\delta}$$

*For $p_0 = 2/\sqrt{3}$ (exact; $p_0^2 = 4/3$) and $\delta = 1/4$:*

$$g_{\text{crit}}^{-2\delta} = g_{\text{crit}}^{-1/2} = \frac{18 \ln 24}{p_0^2} = \frac{18 \times 3.178}{4/3} = \frac{57.20}{1.333} \approx 42.9$$

$$g_{\text{crit}}^2 \approx 2.95 \times 10^{-7}, \qquad \beta_{\text{crit}} = 6/g_{\text{crit}}^2 \approx 2.0 \times 10^7$$

*This is an extremely weak coupling, deep in the perturbative regime. The large $\beta_{\text{crit}}$ is characteristic of rigorous Peierls bounds in lattice gauge theory (Balaban's Z⁴ analysis has comparable thresholds). For the Balaban RG program, only the existence of a finite $\beta_{\text{crit}}$ matters — the initial lattice spacing is chosen small enough that $g_0^2 < g_{\text{crit}}^2$.*

**(c.1′) Conjectured tight critical coupling.** *If the tight per-site bound (b.4) were proven, the Peierls exponent would become $\kappa_\text{FCC}^{\text{tight}} = (4/3)p_0^2 g_k^{-2\delta} - \ln(24)$, giving $\beta_{\text{crit}}^{\text{tight}} \approx 61$. This 24× improvement in the exponent coefficient shifts $\beta_{\text{crit}}$ by a factor of $24^{1/\delta} = 24^4 \approx 3.3 \times 10^5$.*

**(c.2) Comparison with $\mathbb{Z}^4$.** *On the hypercubic lattice, applying the same conservative analysis (each square plaquette covers 4 vertices):*

$$\kappa_{\mathbb{Z}^4} = \frac{(p_0^{\text{cubic}})^2\, g_k^{-2\delta}}{24} - \ln(8)$$

*where $p_0^{\text{cubic}} = 1$ and the denominator $24 = 6 \times 4$ reflects $1/(2N_c) = 1/6$ and 4 vertices per square plaquette.*

| Factor | $\mathbb{Z}^4$ | $D_4$ | Ratio |
|--------|----------------|-------|-------|
| Per-plaquette energy | $(p_0^{\text{cubic}})^2 g_k^{-2\delta}/6$ | $(p_0^{D_4})^2 g_k^{-2\delta}/6$ | $(p_0^{D_4}/p_0^{\text{cubic}})^2 = 4/3$ |
| Vertices per plaquette | 4 (square) | 3 (triangle) | $3/4$ (D₄ better) |
| Per-site energy (conservative) | $g_k^{-2\delta}/24$ | $(4/3)g_k^{-2\delta}/18 \approx g_k^{-2\delta}/13.5$ | $1.78\times$ (D₄ better) |
| Entropy per site | $\ln(8) \approx 2.08$ | $\ln(24) \approx 3.18$ | $1.53\times$ (D₄ worse) |
| Peierls exponent $\kappa$ | $g_k^{-2\delta}/24 - 2.08$ | $g_k^{-2\delta}/13.5 - 3.18$ | — |

*The D₄ lattice has 1.78× larger per-site energy (from higher $p_0^2$ and fewer vertices per plaquette) which outweighs the 1.53× larger entropy (from $z = 24$ vs. $z = 8$). The D₄ Peierls ratio (energy/entropy per site) is 1.16× the Z⁴ ratio, confirming D₄ is more favorable.*

### Part (d): Exponential Suppression 🔶 NOVEL

*The total contribution of the large-field region to the partition function is exponentially suppressed:*

$$\boxed{Z_k^\ell \leq C \cdot \exp\!\left(-\frac{\kappa_\text{FCC}}{g_k^2} \cdot V_k\right)}$$

*where $V_k = |\Lambda_k|$ is the lattice volume and $C$ is a constant depending only on $D_4$ geometry.*

**(d.1) Polymer expansion.** *The large-field contribution factorizes as a polymer gas:*

$$Z_k^\ell = \sum_{\{\gamma_1, \ldots, \gamma_n\}} \prod_{i=1}^n w(\gamma_i)$$

*where the sum is over compatible collections of connected large-field regions (polymers) $\gamma_i$, and $w(\gamma_i)$ is the polymer activity.*

**(d.2) Activity bound.** *Each polymer $\gamma$ of volume $|\gamma|$ satisfies:*

$$|w(\gamma)| \leq \exp\!\left(-\kappa_\text{FCC} \cdot |\gamma| / g_k^2\right)$$

**(d.3) Kotecky-Preiss convergence.** *The polymer expansion converges when the Kotecky-Preiss criterion is satisfied:*

$$\sum_{\gamma \ni x} |w(\gamma)| \cdot e^{a|\gamma|} \leq a \quad \text{for some } a > 0$$

*This holds for $\kappa_\text{FCC}/g_k^2$ sufficiently large (i.e., $g_k$ sufficiently small).*

**(d.4) RG compatibility.** *The large-field contribution $Z_k^\ell/Z_k$ is exponentially small in $1/g_k^2$ and does not disrupt the effective action structure produced by the small-field analysis (Prop 7.6.3). Specifically:*

$$\left|\ln\frac{Z_k}{Z_k^s} - \ln\frac{Z_k^\ell}{Z_k^s}\right| \leq C' \cdot e^{-\kappa_\text{FCC}/(2g_k^2)}$$

---

## §2. Symbol and Dimension Table

| Symbol | Name | Type | Definition / Value |
|--------|------|------|-------------------|
| $\Lambda_k$ | Lattice at scale $k$ | $D_4(\eta_k)$ | Gauge field lives here |
| $\eta_k$ | Lattice spacing at scale $k$ | Length | $\eta_k = 2^k a$ |
| $g_k$ | Running coupling at scale $k$ | Dimensionless | $g_k^2 \approx g_0^2/(1 - 2b_0 g_0^2 \ln 2^k)$ |
| $\delta$ | Small-field exponent | Dimensionless | $0 < \delta < 1$; typically $\delta = 1/4$ |
| $\Omega_k^s$ | Small-field region | Open subset of $\mathcal{A}_k$ | $\{U : \|U_p - \mathbb{1}\| \leq p_0 g_k^{1-\delta}\}$ (Prop 7.6.3) |
| $\Omega_k^\ell$ | Large-field region | Complement of $\Omega_k^s$ | $\mathcal{A}_k \setminus \Omega_k^s$ |
| $p_0$ | Regularity constant | Dimensionless | $p_0^{D_4} = 2p_0^{\text{cubic}}/\sqrt{3}$ (Prop 7.6.3) |
| $U_p$ | Plaquette variable | $\in SU(3)$ | $U_{\ell_1}U_{\ell_2}U_{\ell_3}$ for triangular $p$ |
| $\mathcal{S}_\text{FCC}$ | FCC Wilson action | Dimensionless | $\frac{1}{g_k^2}\sum_\triangle (1 - \frac{1}{3}\operatorname{Re}\operatorname{Tr} U_\triangle)$ |
| $n_p$ | Number of violated plaquettes | Integer | Plaquettes with $\|U_p - \mathbb{1}\| > p_0 g_k^{1-\delta}$ |
| $n_\triangle^\ell$ | Plaquettes per link | Integer | $8$ on $D_4$ (Prop 7.6.3) |
| $N_\triangle$ | Plaquettes per vertex | Integer | $96$ on $D_4$ |
| $z$ | Coordination number | Integer | $24$ on $D_4$ (vs. $8$ on $\mathbb{Z}^4$) |
| $z_{\text{eff}}$ | Effective entropy per site | Dimensionless | $24$ (lattice animal growth constant) |
| $N_{D_4}(V)$ | Lattice animals of volume $V$ | Integer | $\leq e \cdot 24^V$ |
| $\gamma$ | Polymer (connected large-field region) | Subset of $\Lambda_k$ | Maximal connected component |
| $w(\gamma)$ | Polymer activity | Complex | $\leq e^{-\kappa_\text{FCC}|\gamma|/g_k^2}$ |
| $\kappa_\text{FCC}$ | Peierls exponent | Dimensionless | $p_0^2 g_k^{-2\delta}/18 - \ln(24)$ (proven); $(4p_0^2 g_k^{-2\delta}/3) - \ln(24)$ (conjectured tight) |
| $g_{\text{crit}}^2$ | Critical coupling | Dimensionless | Where $\kappa_\text{FCC} = 0$ |
| $V_k$ | Lattice volume | Integer | $|\Lambda_k|$ |
| $Z_k^s, Z_k^\ell$ | Small/large-field partition fn. | Real | Contributions from $\Omega_k^s$ and $\Omega_k^\ell$ |

---

## §3. Background and Motivation

### §3.1 Balaban's Large-Field Program

In Balaban's renormalization group program for lattice gauge theories, the configuration space at each RG scale is decomposed into:

$$\mathcal{A}_k = \Omega_k^s \cup \Omega_k^\ell \tag{3.1}$$

The small-field region $\Omega_k^s$ (Prop 7.6.3) is where perturbation theory applies — the Wilson action is expanded around the saddle point and the Gaussian integral is controlled by the Hessian. The large-field region $\Omega_k^\ell$ is where the field strength exceeds the perturbative bound $p_0 g_k^{1-\delta}$.

Papers IX–X of Balaban's series (CMP 119, 1988; CMP 122, 1989) establish the **large-field estimates** on the hypercubic lattice:

1. **Action penalty:** Configurations with $n_p$ violated plaquettes have action penalty $\geq c \cdot n_p / g_k^2$ (Paper IX, §3)
2. **Peierls argument:** The entropy of connected large-field regions is bounded by $z^V$ where $z = 8$ is the hypercubic coordination number (Paper X, §2)
3. **Polymer expansion:** The large-field partition function factorizes into a convergent polymer gas (Paper X, §4)
4. **Exponential suppression:** The total large-field contribution is $\leq C \cdot e^{-c/g_k^2}$ per lattice volume (Paper X, Theorem 1)

### §3.2 The Peierls Argument

The Peierls argument is a fundamental tool from statistical mechanics. For a lattice model with:
- **Energy penalty:** Each "defect" of volume $V$ costs energy $E(V) \geq \alpha V$
- **Entropy:** The number of defects of volume $V$ containing a fixed site is $\leq e \cdot z^V$

The total contribution of defects is bounded by:

$$\sum_{V=1}^\infty e \cdot z^V \cdot e^{-\alpha V} = e \sum_{V=1}^\infty e^{(\ln z - \alpha)V} \tag{3.2}$$

This converges when $\alpha > \ln z$ — i.e., when the energy penalty per site exceeds the logarithm of the coordination number. The Peierls exponent is $\kappa = \alpha - \ln z > 0$.

### §3.3 D₄ Geometry: More Energy, More Entropy

The D₄ lattice has two geometric features that affect the Peierls argument:

| Feature | Effect on Peierls | D₄ value | Z⁴ value |
|---------|------------------|----------|----------|
| Coordination number $z$ | ↑ entropy ($\ln z$) | 24 | 8 |
| Plaquettes per link $n_\triangle^\ell$ | ↑ energy penalty | 8 | 6 |
| Plaquettes per vertex $N_\triangle$ | ↑ total action per site | 96 | 24 |
| Plaquette area $A_\triangle$ | Affects regularity constant | $\eta_k^2\sqrt{3}/2$ | $\eta_k^2$ |

**Net effect:** The combination of higher $p_0^{D_4}$ and fewer vertices per plaquette (3 vs. 4) gives D₄ a 1.78× larger per-site energy, which **dominates** the 1.53× increase in entropy ($\ln 24$ vs. $\ln 8$). The Peierls argument on D₄ is therefore **stronger** than on Z⁴ — large-field configurations are more strongly suppressed on the FCC lattice.

### §3.4 Role in Phase G

This proposition provides the fourth and final geometric input for the Balaban RG iteration on FCC:

| Input | Source | Status |
|-------|--------|--------|
| 1. Averaging kernel $Q_\text{FCC}$ | Prop 7.6.1 | ✅ Complete |
| 2. Propagator bounds | Prop 7.6.2 | ✅ Complete |
| 3. Regular configurations + variational problem | Prop 7.6.3 | ✅ Complete |
| **4. Large-field (Peierls) estimates** | **Prop 7.6.4 (this)** | **✅ Complete** |

With all four inputs established, the full Balaban RG step on the FCC lattice is defined: the small-field contribution is computed by saddle-point expansion (Prop 7.6.3), and the large-field contribution is controlled by Peierls estimates (this proposition). The combination yields UV stability (Thm 7.6.5).

---

## §4. Structure of the Derivation

### §4.1 Part (a): Large-Field Region Geometry

**Strategy:** Define $\Omega_k^\ell$ as the complement of $\Omega_k^s$, then analyze the connectivity structure and lattice animal enumeration on D₄.

Key steps:
1. **Definition** — $\Omega_k^\ell = \mathcal{A}_k \setminus \Omega_k^s$ where $\Omega_k^s$ is from Prop 7.6.3
2. **Connected components** — Maximal connected subsets of vertices with violated plaquettes
3. **Lattice animal counting** — Bound $N_{D_4}(V) \leq e \cdot 24^V$ via Klarner-type argument
4. **D₄ vs. Z⁴ entropy** — Compare growth constants (24 vs. 8)

See §5 in the Derivation file.

### §4.2 Part (b): Action Penalty

**Strategy:** Use the Wilson action convexity in the large-field region to bound the action penalty per violated plaquette.

Key steps:
1. **Per-plaquette bound** — $1 - \frac{1}{3}\operatorname{Re}\operatorname{Tr} U_p \geq p_0^2 g_k^{2(1-\delta)}/6$ when $\|U_p - \mathbb{1}\| > p_0 g_k^{1-\delta}$
2. **Vertex-covering argument** — Each large-field vertex touches $\geq 1$ violated plaquette; each triangular plaquette covers 3 vertices
3. **Distinct plaquette count** — $V$ vertices require $\geq \lceil V/3 \rceil$ distinct violated plaquettes
4. **Total penalty for volume $V$** — $\Delta S \geq (p_0^2 g_k^{-2\delta}/18) \cdot V$

See §6 in the Derivation file.

### §4.3 Part (c): Peierls Estimate

**Strategy:** Combine lattice animal entropy with action penalty to establish positive Peierls exponent.

Key steps:
1. **Entropy factor** — $\ln(z_{\text{eff}}) = \ln(24) \approx 3.18$
2. **Energy factor** — $p_0^2 g_k^{-2\delta}/18$ per site (conservative; see Part (b.4) for conjectured tight bound)
3. **Energy-entropy balance** — $\kappa_\text{FCC} = \text{energy} - \text{entropy} > 0$
4. **Critical coupling** — Find $g_{\text{crit}}^2$ where $\kappa_\text{FCC} = 0$
5. **D₄ vs. Z⁴ comparison** — Show D₄ ratio is more favorable

See §7 in the Derivation file.

### §4.4 Part (d): Polymer Expansion

**Strategy:** Organize the large-field contribution as a polymer gas and prove convergence via the Kotecky-Preiss criterion.

Key steps:
1. **Polymer definition** — Maximal connected large-field regions
2. **Activity bound** — $|w(\gamma)| \leq e^{-\kappa_\text{FCC}|\gamma|/g_k^2}$
3. **Kotecky-Preiss criterion** — Adapted to D₄ coordination number
4. **Total suppression** — Sum over all polymers bounded by $e^{-\kappa_\text{FCC} V_k/g_k^2}$
5. **RG compatibility** — Large-field contribution doesn't disrupt effective action

See §8 in the Derivation file.

---

## §9. Summary and Connections

### §9.1 What This Proposition Establishes

1. **Large-field control:** The complement of the small-field region is exponentially suppressed in the partition function, with suppression factor $e^{-\kappa_\text{FCC}/g_k^2}$ per unit volume (for $g_k^2 < g_{\text{crit}}^2$)
2. **D₄ advantage:** The Peierls exponent on D₄ is ~1.16× larger than on Z⁴ (comparing the energy-to-entropy ratio), due to the higher $p_0^{D_4}$ and fewer vertices per triangular plaquette outweighing the higher entropy
3. **Polymer convergence:** The large-field contribution factorizes into a convergent polymer gas, compatible with the Balaban RG framework
4. **Phase G.2 completion:** All four geometric inputs (averaging kernel, propagator bounds, regular configurations, large-field estimates) are now established

### §9.2 Honest Assessment

**What is rigorously established (✅):**
- Definition of large-field region as complement of $\Omega_k^s$ — topological complement
- Per-plaquette action penalty from Wilson action convexity — standard lattice gauge theory (Seiler 1982)
- Lattice animal enumeration upper bound — combinatorial inequality (Klarner-type)
- Kotecky-Preiss convergence criterion — proven for abstract polymer models (Kotecky-Preiss 1986)

**What is novel but well-grounded (🔶):**
- The D₄-specific coordination number $z = 24$ and plaquette counts ($n_\triangle^\ell = 8$, $N_\triangle = 96$)
- The explicit Peierls exponent $\kappa_\text{FCC} = p_0^2 g_k^{-2\delta}/18 - \ln(24)$ (rigorously proven)
- The conjectured tight exponent $\kappa_\text{FCC}^{\text{tight}} = (4p_0^2 g_k^{-2\delta}/3) - \ln(24)$ (heuristic; see (b.4))
- The energy-entropy balance favoring D₄ over Z⁴ (1.78× per-site energy vs. 1.53× entropy, using conservative bounds)
- The explicit critical coupling $g_{\text{crit}}^2$
- The compatibility of the polymer expansion with the D₄ RG iteration

**Limitations:**
- The lattice animal bound $N_{D_4}(V) \leq e \cdot 24^V$ is a crude upper bound; the true growth constant may be smaller
- The per-site penalty uses the conservative vertex-covering bound ($\lceil V/3 \rceil$ plaquettes for $V$ vertices); the true penalty is likely much larger
- The critical coupling $\beta_{\text{crit}} \approx 2 \times 10^7$ is extremely large (very weak coupling), characteristic of rigorous Peierls bounds; only the finiteness of $\beta_{\text{crit}}$ matters for the Balaban program
- The critical coupling $g_{\text{crit}}^2$ depends on $p_0$ and $\delta$, which are fixed but not uniquely determined
- The exponential suppression is in $1/g_k^2$, which grows with RG scale — this is compensated by the running coupling staying bounded in the perturbative regime

### §9.3 What This Enables

- **Thm 7.6.5 (UV stability):** With both small-field (Prop 7.6.3) and large-field (this) contributions controlled, the effective action at scale $k+1$ has the same structure as at scale $k$ — the RG iteration is well-defined
- **Phase G.4 (IR control):** The large-field suppression at each scale contributes a convergent sum to the total effective action error
- **Continuum limit:** The combination of UV stability and IR control (from the exact mass gap) establishes the existence of the continuum limit with mass gap

### §9.4 Key Comparison: D₄ vs. Hypercubic

| Feature | Hypercubic ($\mathbb{Z}^4$) | FCC ($D_4$) | Significance |
|---------|----------------------------|-------------|-------------|
| Coordination number | 8 | 24 | 3× more entropy |
| Plaquettes/vertex | 24 (square) | 96 (triangular) | 4× more action terms |
| Plaquettes/link | 6 | 8 | 1.33× more per link |
| Vertices/plaquette | 4 (square) | 3 (triangle) | D₄ better covering |
| Per-site energy (conservative) | $g_k^{-2\delta}/24$ | $(4/3)g_k^{-2\delta}/18$ | 1.78× larger on D₄ |
| Entropy per site | $\ln 8 \approx 2.08$ | $\ln 24 \approx 3.18$ | 1.53× larger on D₄ |
| Peierls exponent $\kappa$ (conservative) | $g_k^{-2\delta}/24 - 2.08$ | $(4/3)g_k^{-2\delta}/18 - 3.18$ | D₄ favorable |

---

## §10. References

### External References

1. T. Balaban, "Convergent renormalization expansions for lattice gauge theories," *Commun. Math. Phys.* **119** (1988) 243–285. [Paper IX]
2. T. Balaban, "Large field renormalization. I. The basic step of the R operation," *Commun. Math. Phys.* **122** (1989) 175–202. [Paper X]
3. T. Balaban, "Large field renormalization. II. Localization, exponentiation, and bounds for the R operation," *Commun. Math. Phys.* **122** (1989) 355–392. [Paper XI]
4. J. Dimock, "The Renormalization Group According to Balaban. II. Large fields," *J. Math. Phys.* **54** (2013) 092301, arXiv:1212.5562. [Dimock II; treats scalar $\varphi^4$ in $d=3$, not gauge theory — the large-field techniques are analogous]
5. R. Kotecky and D. Preiss, "Cluster expansion for abstract polymer models," *Commun. Math. Phys.* **103** (1986) 491–498.
6. R. Fernandez and A. Procacci, "Cluster expansion for abstract polymer models — new bounds from tree partitions," *Commun. Math. Phys.* **274** (2007) 123–140, arXiv:math-ph/0605041.
7. E. Seiler, *Gauge Theories as a Problem of Constructive QFT and Statistical Mechanics,* Springer LNP 159 (1982), §III.
8. D. Klarner, "Cell growth problems," *Canadian J. Math.* **19** (1967) 851–863.
9. J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, 3rd ed. (Springer, 1999), Ch. 4 — $D_4$ lattice.
10. M. Creutz, *Quarks, Gluons and Lattices* (Cambridge UP, 1983), Ch. 6–7, 9–10.
11. W. Celmaster, "Gauge theories on the body-centered hypercubic lattice," *Phys. Rev. D* **26** (1982) 2955. [Triangular plaquette action on BCC lattice]

### Framework References

12. Proposition 7.6.3 — Regular Configurations and Variational Problem on $D_4$ (small-field region $\Omega_k^s$, regularity constant $p_0^{D_4}$, Hessian bounds)
13. Proposition 7.6.2 — Gauge Field Propagator Bounds on $D_4$ (covariant Laplacian, Combes-Thomas decay)
14. Proposition 7.6.1 — FCC Averaging Kernel on $D_4$ (blocking kernel $Q_\text{FCC}$, gauge covariance)
15. Theorem 7.5.3 — Bulk Transition Termination Under Modified FCC Action (crossover path, mass gap persistence)
16. Proposition 7.4.3 — FCC Lattice Perturbation Theory ($D_4$ Laplacian, fourth-moment isotropy)
17. [Research Note: Balaban RG Adaptation to FCC](../supporting/Research-Note-Balaban-RG-Adaptation-FCC.md) §4.10 — Paper X adaptation

---

*Document created: 2026-02-14*
*Classification: 🔶 NOVEL (D₄-specific Peierls estimates) / ✅ ESTABLISHED (Balaban large-field framework)*
*Phase: 7 (Renormalization, unitarity, consistency)*
*Program: Yang-Mills Mass Gap — Phase G (Constructive Continuum Limit), Step G.2d*
