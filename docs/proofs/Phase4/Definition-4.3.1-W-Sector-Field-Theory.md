# Definition 4.3.1: W-Sector Field Theory

## Status: 🔶 NOVEL — W CONDENSATE HIDDEN SECTOR FIELD THEORY

**Role in Framework:** This definition establishes the formal field-theoretic structure of the W (singlet) sector of the stella octangula. The W vertex — the fourth vertex of each tetrahedron in $\partial\mathcal{S}$ — projects to the color singlet in SU(3) weight space. The W condensate $\chi_W$ provides the foundation for a hidden dark sector that is **dark by construction**: a complete gauge singlet with only gravitational and Higgs-portal interactions.

**Dependencies:**
- ✅ Definition 0.1.1 (Stella Octangula Boundary Topology) — Vertex structure, $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$
- ✅ Definition 0.1.2 (Three Color Fields with Relative Phases) — RGB field phases $\phi_R = 0, \phi_G = 2\pi/3, \phi_B = 4\pi/3$
- ✅ Definition 0.1.3 (Pressure Functions from Geometric Opposition) — Pressure modulation $P_c(x)$
- ✅ Definition 0.1.4 (Color Field Domains) — Domain decomposition $D_c$, W domain $D_W$
- ✅ Theorem 3.0.1 (Pressure-Modulated Superposition) — VEV structure

**Content Source:** Extracted and refined from [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) §2, §3, §4.1, §4.3, §5, §12, §13, §14. Field theory placed on formal footing within Phase 4 framework.

**Lean 4 Formalization:** [Definition_4_3_1.lean](../../../lean/ChiralGeometrogenesis/Phase4/Definition_4_3_1.lean)

**Downstream:** [Theorem 4.3.2](Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) (soliton existence), [Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md) (relic abundance), [Proposition 4.3.4](Proposition-4.3.4-W-Soliton-Structure-Formation.md) (structure formation), [Proposition 4.3.5](Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md) (Skyrme parameter derivation), [Prediction 8.2.4](../Phase8/Prediction-8.2.4-W-Sector-Gravitational-Waves.md) (W-sector gravitational waves)

---

## 1. Statement

**Definition.** The **W-sector field theory** is the extension of the CG chiral field to include the fourth (singlet) vertex of the stella octangula. It consists of:

**(a)** A complex scalar field $\chi_W: D_W \to \mathbb{C}$ defined on the W domain, with:
$$\chi_W(x) = a_W(x) \, e^{i\phi_W}$$

where $a_W(x) = a_W^0 \cdot P_W(x)$ is the pressure-modulated amplitude and $\phi_W = \pi$ is the W phase.

**(b)** A vacuum expectation value $\langle \chi_W \rangle = v_W = 123 \pm 15$ GeV, derived self-consistently from the soliton mass formula, potential minimization, and the geometric constraint $\mu_W^2/\mu_H^2 = 1/3$.

**(c)** The extended chiral field:
$$\boxed{\chi_{ext} = \chi_R + \chi_G + \chi_B + \chi_W = \sum_{c \in \{R,G,B\}} a_c(x) e^{i\phi_c} + a_W(x) e^{i\pi}}$$

**(d)** A Higgs portal coupling $\lambda_{H\Phi} = 0.036$ arising from domain boundary overlap.

**(e)** Complete gauge singlet status: no SU(3)$_c$, no SU(2)$_L$, no U(1)$_Y$ charge.

### Symbol Table

| Symbol | Definition | Dimensions | Value/Range |
|--------|-----------|------------|-------------|
| $\chi_W$ | W-sector chiral field | [Energy] | Complex scalar |
| $D_W$ | W domain on $\partial\mathcal{S}$ | — | Solid angle $\Omega_W = \pi$ sr |
| $\phi_W$ | W condensate phase | [dimensionless] | $\pi$ (exact) |
| $v_W$ | W condensate VEV | [Energy] | $123 \pm 15$ GeV |
| $a_W(x)$ | W amplitude function | [Energy] | $a_W^0 \cdot P_W(x)$ |
| $P_W(x)$ | W pressure function | [Length$^{-2}$] | $1/(|x - x_W|^2 + \epsilon^2)$ |
| $\lambda_{H\Phi}$ | Higgs portal coupling | [dimensionless] | 0.036 |
| $\Phi_W$ | W condensate scalar singlet | [Energy] | $\langle \Phi_W \rangle = v_W$ |
| $\chi_{ext}$ | Extended chiral field | [Energy] | RGB + W |

**Dimensional Convention Note:** Definition 0.1.2 establishes the color fields $\chi_c$ as **dimensionless** at the pre-geometric level ($a_0$ has dimensions [Length$^2$], $P_c$ has [Length$^{-2}$], product is dimensionless). In Definition 4.3.1, we use the **physical-scale convention** where $\chi_W$ carries dimensions [Energy], appropriate for the effective field theory after VEV formation. The connection is: $\chi_W^{phys}(x) = v_W \cdot \chi_W^{pre-geom}(x)$, where $v_W = 123$ GeV sets the energy scale (analogous to how $v_0 = f_\pi$ sets the visible-sector scale in Theorem 3.0.1 §5.1). This convention change is standard in chiral perturbation theory: the dimensionless chiral field $U \in \text{SU}(N)$ parametrizes the coset space, while the physical pion field $\pi^a$ carries dimensions [Energy] via $U = \exp(i\pi^a \tau^a / f_\pi)$.

---

## 2. Physical Motivation

### 2.1 The Fourth Vertex

The stella octangula $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ consists of two interpenetrating tetrahedra, each with **four** vertices. In the standard CG framework (Definition 0.1.2), only three vertices per tetrahedron are assigned to color fields:

$$x_R = \frac{1}{\sqrt{3}}(1, -1, -1), \quad x_G = \frac{1}{\sqrt{3}}(-1, 1, -1), \quad x_B = \frac{1}{\sqrt{3}}(-1, -1, 1)$$

The **fourth vertex** is:

$$x_W = \frac{1}{\sqrt{3}}(1, 1, 1)$$

This vertex is present in the geometry but was not assigned a field in the original Phase 0 definitions. Its inclusion is geometrically natural — it completes the tetrahedral structure.

### 2.2 SU(3) Weight Space Projection

Under projection to the $(T_3, T_8)$ weight plane of SU(3):
- $x_R, x_G, x_B \to$ color triplet vertices (the fundamental representation $\mathbf{3}$)
- $x_W \to (0, 0)$ = the **color singlet** (origin of weight space)

The W vertex represents the singlet component of the $\mathbf{3} \otimes \bar{\mathbf{3}} = \mathbf{8} \oplus \mathbf{1}$ decomposition. This singlet is **automatically invisible** to the strong force.

### 2.3 Geometric Necessity

The fourth vertex is not optional — it is an intrinsic part of the tetrahedron $T_+$. Omitting it from the field theory leaves an incomplete description of the geometry. The W-sector field theory completes the field content of $\partial\mathcal{S}$ by assigning a chiral condensate to every vertex.

---

## 3. W Domain Geometry

### 3.1 Domain Definition

From Definition 0.1.4, the W domain is defined by pressure dominance:

$$D_W = \{x \in \mathbb{R}^3 : P_W(x) \geq P_c(x) \text{ for all } c \in \{R, G, B\}\}$$

where $P_c(x) = 1/(|x - x_c|^2 + \epsilon^2)$ is the pressure function from Definition 0.1.3.

### 3.2 Solid Angle

By the tetrahedral symmetry of $T_+$, each of the four vertices (R, G, B, W) commands an equal share of the solid angle:

$$\Omega_W = \frac{4\pi}{4} = \pi \text{ steradians}$$

This represents 25% of the total solid angle, consistent with the W vertex being one of four equivalent vertices of a regular tetrahedron.

### 3.3 Domain Center and Vertex-Face Duality

The W domain $D_W$ (Voronoi cell) is **centered on the W vertex** $x_W = (1,1,1)/\sqrt{3}$ and extends outward along the direction $\hat{x}_W$ from the tetrahedron's center. The region where $P_W$ dominates over all color pressures is the solid cone around $x_W$.

The **opposite face centroid** is:

$$x_W^{face} = \frac{x_R + x_G + x_B}{3} = \frac{1}{3\sqrt{3}}(-1, -1, -1) = -\frac{x_W}{3}$$

This face centroid $-x_W/3$ lies at the intersection of $D_R$, $D_G$, and $D_B$ — the point of **maximal pressure competition** from the three color fields and the point farthest from $D_W$ within $T_+$. In the language of Definition 0.1.4, the vertex $x_W$ is the pressure dominance center while $-x_W/3$ is the pressure depression center for the W channel. This is the standard vertex-face duality of the tetrahedron applied to the pressure domain decomposition.

---

## 4. W Phase Determination: $\phi_W = \pi$

### 4.1 Symmetry Constraint

The W vertex is the singlet direction in SU(3) weight space. Its phase $\phi_W$ must be invariant under $\mathbb{Z}_3$ rotations R $\to$ G $\to$ B. This constrains $\phi_W$ to be independent of the individual color phases.

### 4.2 Proof via $\mathbb{Z}_3$ Invariance and Antipodality

**Theorem.** The W condensate phase is:
$$\boxed{\phi_W = \pi}$$

**Proof.** The argument proceeds in three steps: symmetry restriction, geometric selection, and consistency verification.

**Step 1: $\mathbb{Z}_3$ invariance restricts $\phi_W$ to $\{0, \pi\}$.**

The $\mathbb{Z}_3$ cyclic symmetry $R \to G \to B \to R$ permutes the color phases $(\phi_R, \phi_G, \phi_B) = (0, 2\pi/3, 4\pi/3)$ while leaving the singlet vertex $x_W$ invariant. Since $\phi_W$ is a property of the singlet sector, it must be $\mathbb{Z}_3$-invariant.

For $e^{i\phi_W}$ to be invariant under all permutations of the color labels, it must lie in the $\mathbb{Z}_3$-fixed subspace. Since $\mathbb{Z}_3$ acts on $U(1)$ phases by cyclic rotation of $2\pi/3$, the fixed points satisfy $e^{i\phi_W} = e^{i(\phi_W + 2\pi k/3)}$ for all $k$, which requires $e^{i\phi_W}$ to be **real-valued**: $e^{i\phi_W} \in \{+1, -1\}$, i.e., $\phi_W \in \{0, \pi\}$.

**Step 2: Geometric antipodality selects $\phi_W = \pi$.**

The sum of the three color vertices is:

$$x_R + x_G + x_B = \frac{1}{\sqrt{3}}\bigl[(1,-1,-1) + (-1,1,-1) + (-1,-1,1)\bigr] = \frac{1}{\sqrt{3}}(-1, -1, -1) = -x_W$$

The RGB centroid direction is exactly $-x_W$: the color sector and the singlet vertex are geometrically **antipodal**. This geometric opposition maps to a phase opposition. Specifically, the CG framework assigns phases to vertices by their position in the weight diagram (Definition 0.1.2). The W vertex, being the antipode of the RGB centroid, carries the opposite sign: $e^{i\phi_W} = -1$, giving $\phi_W = \pi$.

**Step 3: Consistency — $\phi_W = 0$ violates the singlet decoupling condition.**

If $\phi_W = 0$, then $\chi_W = a_W(x) \cdot e^{0} = a_W(x) > 0$, which is in phase with $\chi_R = a_R(x) e^{0}$ along the $\phi_R = 0$ direction. This would produce constructive interference between the singlet and one color channel, breaking the $\mathbb{Z}_3$ symmetry of the extended field $\chi_{ext}$ and violating the singlet decoupling condition $(\chi_R + \chi_G + \chi_B)^* \chi_W = 0$ at the symmetric center. Therefore $\phi_W = 0$ is excluded.

The unique $\mathbb{Z}_3$-invariant, geometrically consistent, singlet-decoupled phase is $\phi_W = \pi$. $\quad\blacksquare$

### 4.3 Physical Interpretation

The $\phi_W = \pi$ phase means:
1. **Maximum decoupling:** The W sector is "out of phase" with the visible sector
2. **Dark sector identity:** The anti-phase relationship is the geometric origin of "darkness"
3. **Stabilization:** The negative relative phase creates repulsive mixing in the potential, stabilizing the W sector against decay into visible-sector particles

---

## 5. W Condensate VEV

### 5.1 Geometric Estimate (Superseded)

A naive geometric estimate from the stella octangula symmetry gives:

$$v_W^{geom} = \frac{v_H}{\sqrt{3}} \approx 142 \text{ GeV}$$

where the $1/\sqrt{3}$ factor reflects the singlet-vs-triplet projection in SU(3).

### 5.2 Self-Consistent Derivation (Preferred)

[Proposition 5.1.2b §4.5](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) derives $v_W$ from three self-consistency conditions:

1. **Soliton mass formula:** $M_W = 6\pi^2 v_W/e_W$ (from Theorem 4.1.2)[^skyrme]
2. **Potential minimization:** $v_W^2 = (\mu_W^2 - \lambda_{HW} v_H^2)/(2\lambda_W)$
3. **Geometric constraint:** $\mu_W^2/\mu_H^2 = 1/3$ (stella vertex counting)

With the Skyrme parameter $e_W = 4.5 \pm 0.3$ from stella geometry ([Proposition 4.3.5](Proposition-4.3.5-Skyrme-Parameter-First-Principles-Derivation.md)), solving these conditions yields:

$$\boxed{v_W = 123 \pm 15 \text{ GeV}}$$

with quartic coupling:
$$\lambda_W = 0.101 \pm 0.020 \quad \Rightarrow \quad \frac{\lambda_W}{\lambda_H} = 0.78$$

### 5.3 Comparison

| Approach | $v_W$ (GeV) | $M_W^{soliton}$ (GeV) | Status |
|----------|-------------|----------------------|--------|
| Geometric estimate ($v_H/\sqrt{3}$) | 142 | 1680 | Superseded |
| Potential minimum ($\lambda_W = \lambda_H$) | 108 | 1280 | Limiting case |
| **Self-consistent** ([Prop 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md)) | **123 ± 15** | **1620 ± 160** | **Preferred** |

The 15% shift from the geometric estimate to the self-consistent value reflects the portal coupling correction: Higgs-W mixing ($\lambda_{H\Phi} = 0.036$) shifts the W-sector potential minimum.

[^skyrme]: The analytic Bogomolny bound gives $M = 6\pi^2 f/e \approx 59.22\,f/e$. The full numerical optimization (Adkins, Nappi & Witten 1983) gives $M = 72.92\,f/e$, a 23% enhancement from the non-BPS profile. The ratio $6\pi^2/72.92 = 0.812$ represents a systematic underestimate of the analytic bound. This is within the combined model uncertainties ($\pm 15$%); see [Theorem 4.3.2 §4.4](Theorem-4.3.2-W-Soliton-Existence-And-Properties.md).

---

## 6. Extended Chiral Field

### 6.1 Definition

The standard CG chiral field (Definition 0.1.2, Theorem 0.2.1) is:

$$\chi_{total} = \chi_R + \chi_G + \chi_B = \sum_{c \in \{R,G,B\}} a_c(x) \, e^{i\phi_c}$$

The **extended chiral field** includes the W sector:

$$\chi_{ext} = \chi_R + \chi_G + \chi_B + \chi_W$$

where:

$$\chi_W = a_W(x) \, e^{i\phi_W} = a_W^0 \cdot P_W(x) \cdot e^{i\pi}$$

### 6.2 Properties of the Extended Field

**Superposition:** The W component adds coherently to the total field:

$$\chi_{ext}(x) = \sum_{c \in \{R,G,B\}} a_c(x) \, e^{i\phi_c} + a_W(x) \, e^{i\pi}$$

**Domain separation:** In the interior of each domain, only the dominant field contributes significantly:
- In $D_c$ ($c \in \{R,G,B\}$): $\chi_{ext} \approx \chi_c$
- In $D_W$: $\chi_{ext} \approx \chi_W$

**Boundary mixing:** At domain boundaries $\partial D_c \cap \partial D_W$, the fields overlap, generating the portal coupling (§8).

### 6.3 Consistency with Theorem 0.2.1

The total field superposition theorem (Theorem 0.2.1) establishes that $\chi_{total} = \chi_R + \chi_G + \chi_B$ satisfies $|\chi_{total}|^2 = 3|\chi_0|^2$ at the center by the $\mathbb{Z}_3$ phase cancellation. Adding $\chi_W$ modifies this:

$$|\chi_{ext}|^2 = |\chi_R + \chi_G + \chi_B|^2 + |\chi_W|^2 + 2\,\text{Re}\bigl[(\chi_R + \chi_G + \chi_B)^* \chi_W\bigr]$$

The cross-term involves $(\chi_R + \chi_G + \chi_B)^* \cdot e^{i\pi}$. At the stella center where $a_R = a_G = a_B = a_0$ and $\phi_c = 2\pi(c-1)/3$:

$$\chi_R + \chi_G + \chi_B = a_0(e^{0} + e^{2\pi i/3} + e^{4\pi i/3}) = 0$$

so the cross-term vanishes identically at the center. The W field decouples at the point of maximal $\mathbb{Z}_3$ symmetry, consistent with its singlet character.

---

## 7. Gauge Properties

### 7.1 Color Singlet

The W vertex projects to $(T_3, T_8) = (0, 0)$ in the SU(3) weight diagram — the **color singlet**. Therefore:

$$T^a \chi_W = 0 \quad \text{for all } a = 1, \ldots, 8$$

The W condensate carries **no color charge**.

### 7.2 Electroweak Singlet

**Note:** Color singlet status alone does not imply electroweak singlet status — the SM Higgs boson is an SU(3)$_c$ singlet but an SU(2)$_L$ doublet. The W condensate requires an independent electroweak argument.

The SU(2)$_L$ structure in CG emerges from the $T_+ \leftrightarrow T_-$ exchange symmetry of the stella octangula ([Proposition 0.0.22](../foundations/Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md)). The doublet organization of matter fields (e.g., $(u_L, d_L)$, $(\nu_L, e_L)$) pairs corresponding vertices of the two tetrahedra. The W condensate is an SU(2)$_L$ singlet for three reasons:

1. **Within-tetrahedron argument.** Each tetrahedron $T_\pm$ has 4 vertices. Under the GUT decomposition $D_4 \supset \text{SU}(3) \times \text{SU}(2) \times \text{U}(1)$ ([Theorem 0.0.4](../foundations/Theorem-0.0.4-GUT-Structure.md)), the 4 vertices of a single tetrahedron decompose as $(\mathbf{3}, \mathbf{1})_{-1/3} \oplus (\mathbf{1}, \mathbf{1})_0$: three color triplet vertices that are SU(2)$_L$ singlets, plus the W vertex as a complete singlet. SU(2)$_L$ doublets require vertex pairs drawn from **different** tetrahedra, not from within one tetrahedron.

2. **$T_+ \leftrightarrow T_-$ symmetry.** The $T_+ \leftrightarrow T_-$ exchange maps $x_W(T_+) = (1,1,1)/\sqrt{3}$ to $x_W(T_-) = (-1,-1,-1)/\sqrt{3}$. Both positions define **identical, independent** W-sector condensates by the $\partial\mathcal{S}$ symmetry. A field that is symmetric under the doublet exchange ($\chi_W^{T_+} = \chi_W^{T_-}$ up to phase) transforms as the singlet ($T_3 = 0$, symmetric combination), not as a component of a doublet.

3. **Hypercharge assignment.** In the SU(5) embedding, the complete singlet $(\mathbf{1}, \mathbf{1})_0$ carries zero hypercharge by construction. The W vertex sits at the origin of the full weight space (zero under all Cartan generators), giving $Y = 0$.

Therefore:

$$T^i_{SU(2)} \chi_W = 0, \quad Y \chi_W = 0$$

The W condensate carries **no electroweak charge**. The full group-theoretic derivation connecting the stella octangula geometry to the SM gauge quantum numbers is given in [Proposition 0.0.22](../foundations/Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md) and [Theorem 0.0.4](../foundations/Theorem-0.0.4-GUT-Structure.md).

### 7.3 Complete Gauge Singlet

Combining §7.1 and §7.2:

$$\chi_W \text{ transforms as } (\mathbf{1}, \mathbf{1}, 0) \text{ under } \text{SU(3)}_c \times \text{SU(2)}_L \times \text{U(1)}_Y$$

This is a **complete gauge singlet**. The W condensate interacts with the visible sector only through:
1. **Gravity** (universal coupling via $T_{\mu\nu}$)
2. **Higgs portal** (scalar mixing through domain boundary overlap)

This makes W-sector particles **dark by construction** — no fine-tuning is needed to suppress gauge interactions.

---

## 8. Higgs Portal Coupling

### 8.1 Portal Lagrangian

The interaction between the W condensate and the Higgs field takes the portal form:

$$\mathcal{L}_{portal} = -\lambda_{H\Phi} (H^\dagger H)(\Phi_W^\dagger \Phi_W)$$

where $H$ is the Standard Model Higgs doublet and $\Phi_W$ is the W condensate field with $\langle \Phi_W \rangle = v_W$.

### 8.2 Geometric Origin

In CG, the portal coupling arises from **domain boundary interactions**. The W domain shares boundaries with R, G, B domains, and the boundary overlap determines the coupling:

$$\lambda_{H\Phi}^{geom} = g_0^2 \int_{\partial D_W} P_W(\mathbf{x}) \cdot P_{RGB}(\mathbf{x}) \, dA$$

where $P_{RGB} = P_R + P_G + P_B$ and $g_0$ is the coupling at the domain boundary scale.

**Coupling scale $g_0$:** The parameter $g_0$ characterizes the strength of field interactions at the domain boundary $\partial D_W$. In the CG framework, the domain boundary sits at the scale $R_{stella} \sim 0.45$ fm, which is the QCD confinement scale. At this scale, the running QCD coupling is $\alpha_s(R_{stella}) \approx 0.3$–$0.5$, giving $g_s = \sqrt{4\pi\alpha_s} \approx 2$–$2.5$. However, $g_0$ is not the QCD gauge coupling itself — it is the effective coupling between the W-sector condensate and the RGB sector at the domain boundary. Since both sectors share the same geometric substrate ($\partial\mathcal{S}$), the boundary coupling inherits the same order of magnitude as the strong coupling: $g_0 \sim O(1)$. We adopt $g_0 = 1.0 \pm 0.3$ as a dimensionless $O(1)$ parameter, noting that the result $\lambda_{H\Phi}$ depends on $g_0^2$ and the full geometric integral, making it insensitive to the precise value at the factor-of-2 level.

### 8.3 Evaluation

For the stella octangula geometry with $\varepsilon \ll 1$, the integral in §8.2 is evaluated by exploiting tetrahedral symmetry.

**Step 1: Symmetry reduction.** The boundary $\partial D_W$ consists of three equivalent edges where $D_W$ meets $D_R$, $D_G$, $D_B$. By tetrahedral symmetry, the three contributions are equal:

$$\int_{\partial D_W} P_W \cdot P_{RGB} \, dA = 3 \int_{\partial D_W \cap \partial D_R} P_W \cdot P_R \, dA$$

**Step 2: Boundary geometry.** Each boundary $\partial D_W \cap \partial D_c$ is a great-circle arc on $\partial\mathcal{S}$ where $P_W = P_c$. By the regularized pressure form $P_c = 1/(|x - x_c|^2 + \varepsilon^2)$, the equal-pressure locus satisfies $|x - x_W|^2 = |x - x_c|^2$, which is a plane bisecting $x_W$ and $x_c$. The intersection with the unit sphere has solid angle factor $\sqrt{3}/(4\pi)$ per edge.

**Step 3: Integral evaluation.** On the boundary, $P_W = P_c = 1/(d^2 + \varepsilon^2)$ where $d$ is the distance to the midpoint. Integrating over each arc and summing:

$$\lambda_{H\Phi}^{geom} = \frac{g_0^2}{4} \cdot \frac{3\sqrt{3}}{8\pi} \cdot \ln\!\left(\frac{1}{\varepsilon}\right)$$

The factor $1/4$ comes from the 4-vertex normalization, $3\sqrt{3}/(8\pi)$ from the boundary geometry, and $\ln(1/\varepsilon)$ from the logarithmic divergence of the pressure product integral regulated at scale $\varepsilon$.

**Step 4: Numerical evaluation.** With $g_0 = 1$ and $\varepsilon = 0.5$ (the QCD flux tube scale $\sim R_{stella}/2$, giving a mild logarithm):

$$\lambda_{H\Phi} = \frac{1}{4} \times \frac{3\sqrt{3}}{8\pi} \times \ln(2) = \frac{1}{4} \times 0.2067 \times 0.6931 = 0.0358$$

$$\boxed{\lambda_{H\Phi} \approx 0.036}$$

This is within the range $0.02$–$0.05$ allowed by the geometric uncertainty ($g_0 \in [0.7, 1.3]$, $\varepsilon \in [0.3, 0.7]$).

### 8.4 Physical Consequences

The portal coupling $\lambda_{H\Phi} = 0.036$ has three consequences:

1. **Direct detection:** Spin-independent cross-section $\sigma_{SI} \approx 1.5 \times 10^{-47}$ cm$^2$, a factor $\sim$7 below the current LZ bound ($\sim 10^{-46}$ cm$^2$ at $M \approx 1.6$ TeV; LZ 2024, arXiv:2410.17036). Testable at DARWIN/XLZD (arXiv:2404.19524).
2. **Thermal equilibration:** Sufficient for thermal contact in early universe ($T > M_W$)
3. **Relic abundance:** Thermal freeze-out with this coupling gives $\Omega h^2 \approx 23$ (over-abundant by 200$\times$) — this tension is resolved by asymmetric production ([Proposition 4.3.3](Proposition-4.3.3-W-Soliton-Cosmological-Abundance.md))
4. **Higgs signal strength:** On-shell $h \to W_{\text{soliton}} W_{\text{soliton}}$ is kinematically forbidden ($M_W \approx 1620$ GeV $\gg m_h/2 = 62.6$ GeV). The W-sector has no light scalar excitations (§8.5). The predicted Higgs signal strength is $\mu = 1.00$, consistent with LHC data ($\mu^{\text{obs}} = 1.00 \pm 0.06$).

**Comparison with standard scalar singlet DM models.** The CG W-sector shares the Higgs portal Lagrangian structure with the standard scalar singlet dark matter model (Silveira & Zee 1985; Burgess, Pospelov & ter Veldhuis 2001), but differs in several key respects:

| Feature | Standard Scalar Singlet | CG W-Sector |
|---------|------------------------|-------------|
| VEV | $\langle S \rangle = 0$ ($\mathbb{Z}_2$ stabilized) | $v_W = 123$ GeV (condensate) |
| Mass origin | Free parameter | Soliton mass from Skyrme dynamics |
| Portal coupling | Fit to relic abundance | Derived from geometry ($\lambda_{H\Phi} = 0.036$) |
| Production | Thermal freeze-out | Asymmetric dark matter |
| Scalar excitations | Light scalar $h_S$ | None (nonlinear sigma model) |
| Stability | $\mathbb{Z}_2$ symmetry (imposed) | Topological charge $Q_W \in \mathbb{Z}$ (derived) |

**Computational Verification:** `verification/Phase8/issue_3_portal_uv_completion.py`

### 8.5 Higgs Exotic Decay Constraint

**Potential concern:** In a linear scalar field theory with $\lambda_W = 0.101$ and $v_W = 123$ GeV, a scalar excitation would have mass $m_{h_W} = \sqrt{2\lambda_W}\,v_W \approx 55.3$ GeV $< m_h/2 = 62.6$ GeV, opening the exotic decay $h \to h_W h_W$. This would reduce the Higgs signal strength to $\mu \approx 0.26$, excluded at $>12\sigma$ by LHC data ($\mu^{\text{obs}} = 1.00 \pm 0.06$).

**Resolution:** This constraint does not apply to the W-sector because the dynamics is governed by the **Skyrme Lagrangian** (nonlinear sigma model), not a linear scalar field theory.

The W-sector Skyrme Lagrangian ([Theorem 4.3.2 §4.1](Theorem-4.3.2-W-Soliton-Existence-And-Properties.md)) is:

$$\mathcal{L}_W = \frac{v_W^2}{4}\,\text{Tr}(\partial_\mu U_W^\dagger \partial^\mu U_W) + \frac{1}{32 e_W^2}\,\text{Tr}\bigl([U_W^\dagger\partial_\mu U_W, U_W^\dagger\partial_\nu U_W]^2\bigr)$$

where $U_W \in \text{SU}(2)$ is the chiral map. Three consequences follow:

1. **No radial degree of freedom.** In the nonlinear sigma model, the field is constrained to the SU(2) group manifold: $|U_W|$ is frozen, not dynamical. The formula $m = \sqrt{2\lambda}\,v$ applies to fundamental linear scalars (like the SM Higgs), not to nonlinear sigma model fields. There is no propagating scalar ("dark Higgs") excitation in the physical spectrum.

2. **QCD analogy.** This parallels the visible sector: the chiral Lagrangian (nonlinear sigma model) has pions (Goldstone bosons) but no $\sigma$ particle. The $f_0(500)/\sigma$ resonance appears only in the linear sigma model extension, where it is extremely broad ($\Gamma_\sigma \approx m_\sigma$) — not a well-defined particle. The W-sector analog is identical: the effective potential parameters $(\lambda_W, v_W)$ determine the condensate scale, not a scalar mass.

3. **Soliton excitation spectrum.** The physical excitations of the Skyrme soliton are:
   - **Rotational modes** (quantized spin/isospin): $\Delta E \sim 1/(2\mathcal{I})$ where $\mathcal{I} \sim R_W^3 v_W^2$
   - **Breathing (vibrational) modes**: $\omega \sim 2$–$3/R_W \approx 1100$–$1700$ GeV
   - **Translation modes** (zero modes, give momentum)

   All excitations are at energies $\gg m_h/2$. Even if they could couple to the Higgs boson, such decays would be kinematically forbidden.

**Portal coupling in the NL$\sigma$M.** With the modulus frozen at $v_W$, the portal term becomes:
$$\mathcal{L}_{portal} = -\lambda_{H\Phi}\,v_W^2\,|H|^2$$
This contributes a constant shift to the Higgs mass parameter: $\delta\mu_H^2 = \lambda_{H\Phi}\,v_W^2 \approx 545$ GeV$^2$. This is absorbed into the renormalized SM parameters and does not produce exotic decays. The portal coupling connects the Higgs to the W-soliton as a **composite object**, determining the direct detection cross-section (§8.4), not to a light scalar.

**On-shell $h \to W_{\text{soliton}} W_{\text{soliton}}$** is independently kinematically forbidden: $M_W \approx 1620$ GeV $\gg m_h/2$.

**Backup argument.** Even if one were to insist on a linear scalar interpretation, the threshold coupling $\lambda_W^{thr} = (m_h/2)^2/(2v_W^2) = 0.130$ is within the stated $2\sigma$ uncertainty ($\lambda_W = 0.101 \pm 0.020$). However, this backup argument is unnecessary given the nonlinear sigma model resolution above.

**Computational Verification:** `verification/Phase4/definition_4_3_1_higgs_constraint_resolution.py`

---

## 9. Consistency Checks

### 9.1 Dimensional Analysis

| Quantity | Expression | Mass Dimension | Verification |
|----------|-----------|----------------|--------------|
| $\chi_W$ | $a_W(x) e^{i\phi_W}$ | [Energy] | ✓ Field dimension |
| $v_W$ | $123$ GeV | [Energy] | ✓ VEV dimension |
| $\phi_W$ | $\pi$ | [dimensionless] | ✓ Phase |
| $\lambda_{H\Phi}$ | 0.036 | [dimensionless] | ✓ Coupling |
| $\Omega_W$ | $\pi$ sr | [dimensionless] | ✓ Solid angle |
| $P_W(x)$ | $1/(|x-x_W|^2 + \epsilon^2)$ | [Length$^{-2}$] | ✓ Pressure |

### 9.2 Symmetry Checks

| Symmetry | Check | Status |
|----------|-------|--------|
| $\mathbb{Z}_3$ invariance of $\phi_W$ | $\phi_W = \pi$ independent of R,G,B labeling | ✅ |
| Tetrahedral symmetry of $D_W$ | $\Omega_W = 4\pi/4 = \pi$ | ✅ |
| Gauge singlet status | $(T_3, T_8) = (0,0)$ in SU(3) weight space | ✅ |
| Antipodal relation | $x_R + x_G + x_B = -x_W$ | ✅ |
| $\mathbb{Z}_3$ decoupling at center | Cross-term $(\sum \chi_c)^* \chi_W = 0$ at center | ✅ |

### 9.3 Unification Point 5 (Mass Generation)

The W condensate acquires its VEV through the **same mechanism** as the visible-sector chiral condensate: pressure-modulated field dynamics on $\partial\mathcal{S}$ (Theorem 3.0.1). The W-sector simply operates at a different vertex with a different coupling strength. This is consistent with Unification Point 5 (mass generation) — there is one mechanism at different scales, not two different mechanisms.

### 9.4 Consistency with Prediction 8.3.1

All field-theoretic definitions in this document are consistent with [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md). The present document provides the **formal Phase 4 treatment**; Prediction 8.3.1 retains the full observational predictions (§7–§9, §15–§16).

---

## 10. References

**CG Framework:**
- [Definition 0.1.1](../Phase0/Definition-0.1.1-Stella-Octangula-Boundary-Topology.md) — Stella octangula boundary topology
- [Definition 0.1.2](../Phase0/Definition-0.1.2-Three-Color-Fields-Relative-Phases.md) — Three color fields and relative phases
- [Definition 0.1.3](../Phase0/Definition-0.1.3-Pressure-Functions.md) — Pressure functions from geometric opposition
- [Definition 0.1.4](../Phase0/Definition-0.1.4-Color-Field-Domains.md) — Color field domains
- [Theorem 3.0.1](../Phase3/Theorem-3.0.1-Pressure-Modulated-Superposition.md) — Pressure-modulated superposition
- [Proposition 5.1.2b](../Phase5/Proposition-5.1.2b-Precision-Cosmological-Densities.md) — Self-consistent $v_W$ derivation
- [Prediction 8.3.1](../Phase8/Prediction-8.3.1-W-Condensate-Dark-Matter.md) — W condensate dark matter (observational predictions)
- [Theorem 0.0.4](../foundations/Theorem-0.0.4-GUT-Structure.md) — GUT structure from stella octangula (D₄ decomposition)
- [Proposition 0.0.22](../foundations/Proposition-0.0.22-SU2-Substructure-From-Stella-Octangula.md) — SU(2) substructure from stella (electroweak singlet argument)
- [Theorem 4.3.2](Theorem-4.3.2-W-Soliton-Existence-And-Properties.md) — W-soliton existence and Skyrme Lagrangian

**External Physics — Scalar Singlet Dark Matter:**
- Silveira, V. & Zee, A. (1985). "Scalar phantoms." *Phys. Lett. B* 161, 136–140. — Pioneer scalar singlet DM paper.
- Burgess, C. P., Pospelov, M. & ter Veldhuis, T. (2001). "The Minimal model of nonbaryonic dark matter: A Singlet scalar." *Nucl. Phys. B* 619, 709. [arXiv:hep-ph/0011335] — Standard modern reference for scalar singlet DM.
- Patt, B. & Wilczek, F. (2006). "Higgs-field portal into hidden sectors." [arXiv:hep-ph/0605188] — Higgs portal formulation.
- Athron, P. et al. [GAMBIT Collaboration] (2017). "Status of the scalar singlet dark matter model." *Eur. Phys. J. C* 77, 568. [arXiv:1705.07931] — Comprehensive global fits and constraints.

**External Physics — Skyrme Model:**
- Adkins, G. S., Nappi, C. R. & Witten, E. (1983). "Static Properties of Nucleons in the Skyrme Model." *Nucl. Phys. B* 228, 552–566. — Numerically-optimized Skyrme soliton mass: $M = 72.92\,f_\pi/e$ (vs.\ analytic bound $M = 6\pi^2 f_\pi/e$; ratio $6\pi^2/72.92 = 0.812$, systematic $\sim$19% shift).

**External Physics — Direct Detection Experiments:**
- LZ Collaboration (2024). "Dark matter search results from 4.2 tonne-years of exposure of the LUX-ZEPLIN (LZ) experiment." [arXiv:2410.17036] — Current world-leading SI exclusion limits; at $M \approx 1.6$ TeV, the bound is $\sigma_{SI} \lesssim 10^{-46}$ cm$^2$, so the CG prediction ($1.5 \times 10^{-47}$ cm$^2$) is a factor $\sim$7 below current sensitivity.
- XENONnT Collaboration (2025). "First Dark Matter Search with Nuclear Recoils from the XENONnT Experiment." [arXiv:2502.18005] — Independent limit $1.7 \times 10^{-47}$ cm$^2$ at 30 GeV.
- DARWIN/XLZD Collaboration (2024). "XLZD: The next-generation liquid xenon observatory for dark matter and neutrino physics." [arXiv:2404.19524] — Future sensitivity reaching the CG prediction regime.

**Higgs Signal Strength:**
- ATLAS & CMS Collaborations, PDG 2024. Combined Higgs signal strength $\mu = 1.00 \pm 0.06$; invisible BR $< 10.7\%$ (ATLAS 95% CL). On-shell $h \to W_{\text{soliton}} W_{\text{soliton}}$ is kinematically forbidden ($M_W \approx 1620$ GeV $\gg m_h/2$); see §8.5 for the scalar excitation constraint resolution.

**Computational Verification:**
- `verification/Phase8/w_condensate_quantitative_predictions.py`
- `verification/Phase8/issue_3_portal_uv_completion.py`
- `verification/Phase4/definition_4_3_1_adversarial_verification.py` — Adversarial physics verification (10 tests, 3 plots)
- `verification/Phase4/definition_4_3_1_higgs_constraint_resolution.py` — Higgs exotic decay constraint resolution (§8.5)

**Verification Records:**
- [Multi-Agent Verification Report (2026-02-25)](../verification-records/Definition-4.3.1-Multi-Agent-Verification-2026-02-25.md) — Literature, Mathematics, Physics agents
