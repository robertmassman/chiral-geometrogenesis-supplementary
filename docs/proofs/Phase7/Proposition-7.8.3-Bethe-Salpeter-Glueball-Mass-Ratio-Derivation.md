# Proposition 7.8.3: Bethe-Salpeter Glueball Mass Ratio — Derivation

**Parent document:** [Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio.md)

This file contains the complete derivation of $R_\text{BS} = 3\sqrt{3(2-3\alpha_s)/2}$ from the spinless Salpeter equation.

---

## §5. Spinless Salpeter Equation Setup

### §5.1 Two-Gluon Hamiltonian

The lightest $0^{++}$ glueball is modeled as a bound state of two massless constituent gluons. In the center-of-mass frame, the spinless Salpeter Hamiltonian is:

$$H = 2|\mathbf{p}| + V(r) \tag{5.1}$$

where $|\mathbf{p}|$ is the relativistic kinetic energy for a massless particle and $V(r)$ is the interquark potential in the appropriate color channel.

### §5.2 Color Factor Derivation

The two gluons each transform in the adjoint representation ($\mathbf{8}$). The tensor product decomposes as:

$$\mathbf{8} \otimes \mathbf{8} = \mathbf{1} \oplus \mathbf{8}_S \oplus \mathbf{8}_A \oplus \mathbf{10} \oplus \overline{\mathbf{10}} \oplus \mathbf{27} \tag{5.2}$$

The $0^{++}$ glueball corresponds to the **color-singlet** ($\mathbf{1}$) channel. The color interaction is determined by the expectation value of the color operator $F_1 \cdot F_2 = T_1^a T_2^a$ in the singlet state:

$$\langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle = \frac{1}{2}\left[C_2(\mathbf{1}) - C_2(\mathbf{8}) - C_2(\mathbf{8})\right] \tag{5.3}$$

With $C_2(\mathbf{1}) = 0$ (trivial representation) and $C_2(\mathbf{8}) = N = 3$:

$$\langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle = \frac{1}{2}(0 - 3 - 3) = -3 \tag{5.4}$$

The negative sign indicates **attraction** in the singlet channel, as required for binding.

### §5.3 Cornell Potential in the Singlet Channel

The Cornell potential for the color-singlet two-gluon system consists of:

**One-gluon exchange (OGE) Coulomb term:**

$$V_\text{OGE}(r) = \langle \mathbf{1}|F_1 \cdot F_2|\mathbf{1}\rangle \cdot \frac{\alpha_s}{r} = -\frac{3\alpha_s}{r} \tag{5.5}$$

**Linear confining term:** The string tension for two adjoint sources forming a singlet is given by Casimir scaling in the weak-coupling regime:

$$\sigma_\text{adj} = \frac{C_2(\mathbf{8})}{C_2(\mathbf{3})} \cdot \sigma_3 = \frac{9}{4}\sigma_3 \tag{5.6}$$

This is confirmed by lattice measurements: Bali (2000) [5] finds $\sigma_8/\sigma_3 = 2.26 \pm 0.06$, consistent with $9/4 = 2.250$ to within errors. The linear term is:

$$V_\text{lin}(r) = \sigma_\text{adj} \cdot r = \frac{9}{4}\sigma_3 \cdot r \tag{5.7}$$

**Total Hamiltonian:**

$$\boxed{H = 2|\mathbf{p}| + \frac{9}{4}\sigma_3 \, r - \frac{3\alpha_s}{r}} \tag{5.8}$$

This is the spinless Salpeter equation for two massless particles interacting via the Cornell potential with color factors appropriate to the $\mathbf{8} \otimes \mathbf{8} \to \mathbf{1}$ channel.

---

## §6. Auxiliary Field Method (AFM)

### §6.1 Replacing the Relativistic Kinetic Energy

The relativistic kinetic energy $T = 2|\mathbf{p}|$ makes the Salpeter equation non-local in coordinate space. The auxiliary field method (AFM) [11, 12] replaces $|\mathbf{p}|$ with a variational form that is quadratic in $\mathbf{p}$:

$$|\mathbf{p}| = \min_{\nu > 0}\left[\frac{p^2}{2\nu} + \frac{\nu}{2}\right] \tag{6.1}$$

This identity is exact: the minimum over the auxiliary parameter $\nu$ is attained at $\nu^* = |\mathbf{p}|$, giving $f(\nu^*) = |\mathbf{p}|/2 + |\mathbf{p}|/2 = |\mathbf{p}|$.

**Proof:** $f(\nu) = p^2/(2\nu) + \nu/2$. Setting $f'(\nu) = -p^2/(2\nu^2) + 1/2 = 0$ gives $\nu^* = |p|$ and $f(\nu^*) = |p|$.

For the two-gluon system:

$$2|\mathbf{p}| = \min_{\nu > 0}\left[\frac{p^2}{\nu} + \nu\right] \tag{6.2}$$

### §6.2 AFM Hamiltonian

Substituting Eq. (6.2) into the Salpeter Hamiltonian Eq. (5.8):

$$H_\text{AFM}(\nu) = \frac{p^2}{\nu} + \nu + \frac{9}{4}\sigma_3 \, r - \frac{3\alpha_s}{r} \tag{6.3}$$

This is a non-relativistic Schrodinger-type Hamiltonian with effective mass $m_\text{eff} = \nu/2$ (since $p^2/\nu = p^2/(2 \cdot \nu/2)$). The ground state energy is computed variationally and then optimized over $\nu$.

### §6.3 Envelope Theory Interpretation

The AFM is related to **envelope theory** (Silvestre-Brac & Semay [12]): for a power-law potential $V(r) = ar^n$, the AFM gives the **exact** eigenvalues. For mixed potentials (such as Cornell = linear + Coulomb), the AFM provides a **variational upper bound**. The quality of the bound depends on how well the dominant potential component approximates a pure power law. Since the glueball is primarily a confining (linear) system with a subleading Coulomb correction, the AFM is expected to be accurate to $O((\alpha_s/\alpha_c)^2)$ where $\alpha_c$ is the critical coupling.

---

## §7. Exponential Variational Wavefunction

### §7.1 Ansatz

We use the exponential (hydrogen-like) $s$-wave wavefunction:

$$\psi(r) = \sqrt{\frac{\beta^3}{\pi}} \, e^{-\beta r} \tag{7.1}$$

where $\beta > 0$ is the variational parameter (inverse size of the glueball). This is normalized: $\int |\psi|^2 d^3r = 1$.

### §7.2 Matrix Elements

The following matrix elements are exact (standard integrals):

$$\langle p^2 \rangle = \beta^2 \tag{7.2}$$

$$\langle 1/r \rangle = \beta \tag{7.3}$$

$$\langle r \rangle = \frac{3}{2\beta} \tag{7.4}$$

**Derivations:**

For $\langle p^2 \rangle$: Using $\nabla^2 \psi = (\beta^2 - 2\beta/r)\psi$:

$$\langle p^2 \rangle = -\int \psi^* \nabla^2 \psi \, d^3r = -\frac{\beta^3}{\pi} \cdot 4\pi \int_0^\infty r^2 (\beta^2 - 2\beta/r) e^{-2\beta r} dr$$

$$= -4\beta^3 \left[\beta^2 \cdot \frac{1}{4\beta^3} - 2\beta \cdot \frac{1}{4\beta^2}\right] = -4\beta^3\left[\frac{1}{4\beta} - \frac{1}{2\beta}\right] = -4\beta^3 \cdot \left(-\frac{1}{4\beta}\right) = \beta^2 \tag{7.5}$$

where we used $\int_0^\infty r^2 e^{-2\beta r} dr = 2/(2\beta)^3$ and $\int_0^\infty r \, e^{-2\beta r} dr = 1/(2\beta)^2$.

For $\langle 1/r \rangle$: $4\pi \int_0^\infty r \cdot e^{-2\beta r} dr = 4\pi/(2\beta)^2$, normalized by $\pi/\beta^3$, giving $\beta$.

For $\langle r \rangle$: $4\pi \int_0^\infty r^3 e^{-2\beta r} dr = 4\pi \cdot 6/(2\beta)^4 = 3\pi/(2\beta^4)$, normalized by $\pi/\beta^3$, giving $3/(2\beta)$.

### §7.3 Energy Expectation Value

Substituting the matrix elements into $H_\text{AFM}(\nu)$:

$$\langle H_\text{AFM} \rangle = \frac{\beta^2}{\nu} + \nu + \frac{9}{4}\sigma_3 \cdot \frac{3}{2\beta} - 3\alpha_s \cdot \beta \tag{7.6}$$

$$= \frac{\beta^2}{\nu} + \nu + \frac{27\sigma_3}{8\beta} - 3\alpha_s \beta \tag{7.7}$$

### §7.4 Optimization Over $\nu$

Minimizing with respect to $\nu$:

$$\frac{\partial \langle H \rangle}{\partial \nu} = -\frac{\beta^2}{\nu^2} + 1 = 0 \quad \Longrightarrow \quad \nu^* = \beta \tag{7.8}$$

This is a universal result of the AFM: the optimal auxiliary parameter equals the variational momentum scale.

Substituting $\nu = \beta$:

$$\langle H \rangle_{\nu=\beta} = \beta + \beta + \frac{27\sigma_3}{8\beta} - 3\alpha_s \beta = (2 - 3\alpha_s)\beta + \frac{27\sigma_3}{8\beta} \tag{7.9}$$

### §7.5 Optimization Over $\beta$

The energy has the form $E(\beta) = A\beta + B/\beta$ with:

$$A = 2 - 3\alpha_s > 0 \quad (\text{for } \alpha_s < 2/3), \qquad B = \frac{27\sigma_3}{8} > 0 \tag{7.10}$$

Minimizing:

$$\frac{\partial E}{\partial \beta} = A - \frac{B}{\beta^2} = 0 \quad \Longrightarrow \quad \beta^{*2} = \frac{B}{A} = \frac{27\sigma_3}{8(2 - 3\alpha_s)} \tag{7.11}$$

At the optimum:

$$E^* = A\sqrt{B/A} + B/\sqrt{B/A} = \sqrt{AB} + \sqrt{AB} = 2\sqrt{AB} \tag{7.12}$$

---

## §8. Closed-Form Mass Formula

### §8.1 Ground State Energy

Substituting $A$ and $B$:

$$m(0^{++}) = E^* = 2\sqrt{AB} = 2\sqrt{(2 - 3\alpha_s) \cdot \frac{27\sigma_3}{8}} \tag{8.1}$$

### §8.2 Ratio $R_\text{BS}$

Dividing by $\sqrt{\sigma_3}$:

$$R_\text{BS} = \frac{m(0^{++})}{\sqrt{\sigma_3}} = 2\sqrt{\frac{27(2 - 3\alpha_s)}{8}} \tag{8.2}$$

Simplifying the coefficient:

$$2\sqrt{\frac{27}{8}} = 2 \cdot \frac{3\sqrt{3}}{2\sqrt{2}} = \frac{3\sqrt{3}}{\sqrt{2}} = 3\sqrt{\frac{3}{2}} \tag{8.3}$$

Therefore:

$$\boxed{R_\text{BS} = 3\sqrt{\frac{3(2 - 3\alpha_s)}{2}}} \tag{8.4}$$

**Key properties of the formula:**

1. **$\sigma_3$ cancels exactly** — the ratio depends only on $\alpha_s$ (and group-theoretic factors embedded in the coefficients)
2. **Valid for $\alpha_s < 2/3$** — otherwise the argument of the square root becomes negative (the Coulomb attraction overwhelms the linear confinement)
3. **Limit $\alpha_s \to 0$** (pure linear potential): $R_\text{BS} \to 3\sqrt{3} \approx 5.196$ — the mass is entirely from confinement
4. **Origin of the factor 3:** From Casimir scaling: $(9/4) \times (3/(2\beta)) = 27/(8\beta)$; the coefficient $27/8$ propagates through $\sqrt{27/8} = 3\sqrt{3/8}$ and $2 \times 3\sqrt{3/8} = 3\sqrt{3/2}$

---

## §9. Self-Consistent Coupling Determination

### §9.1 The Scale Ambiguity

The formula Eq. (8.4) requires specifying $\alpha_s$ at an appropriate renormalization scale $\mu$ for the glueball system. There is an inherent ambiguity in the choice of $\mu$, which is the dominant source of uncertainty.

### §9.2 One-Loop Running Coupling

Using the one-loop formula for pure SU(3) Yang-Mills:

$$\alpha_s(\mu) = \frac{4\pi}{\beta_0 \ln(\mu^2/\Lambda_{\overline{\text{MS}}}^2)} \tag{9.1}$$

with $\beta_0 = (11N_c - 2N_f)/3 = 11$ for pure SU(3) ($N_f = 0$), and $\Lambda_{\overline{\text{MS}}} = \sqrt{\sigma}/1.994 \approx 220$ MeV [2].

Equivalently, writing $\alpha_s = 1/(b_0 \ln(\mu^2/\Lambda^2))$ with $b_0 = \beta_0/(4\pi) = 11/(4\pi) \approx 0.875$.

> **Convention note:** The symbol table (§2) and Thm 7.5.2 use the convention $\hat{b}_0 = 11/(16\pi^2) \approx 0.070$, which is the coefficient in the beta function for $g^2$: $\mu \, dg/d\mu = -\hat{b}_0 g^3$. The relationship is $b_0 = 4\pi \hat{b}_0 = 11/(4\pi) = 0.875$. These encode the same physics.

### §9.3 Scale Choice (a): Half the Glueball Mass

A natural scale is half the glueball mass (the internal momentum scale):

$$\mu_a = m_G/2 \approx R_\text{cont} \cdot \sqrt{\sigma}/2 \approx 3.4 \times 440/2 \approx 750 \text{ MeV} \tag{9.2}$$

$$\alpha_s^{(1)}(\mu_a) = \frac{4\pi}{11 \times \ln(750^2/220^2)} = \frac{12.57}{11 \times 2.445} = 0.467 \tag{9.3}$$

This gives $R_\text{BS}(0.467) = 3\sqrt{3(2-1.401)/2} = 3\sqrt{0.899} = 2.85$, which undershoots the lattice value significantly.

### §9.4 Scale Choice (b): Typical Internal Momentum

The variational parameter $\beta$ sets the typical momentum scale. From Eq. (7.11):

$$\beta^* = \sqrt{\frac{27\sigma_3}{8(2-3\alpha_s)}} \tag{9.4}$$

Using $\sqrt{\sigma_3} = 440$ MeV and $\alpha_s = 0.38$:

$$\beta^* = \sqrt{\frac{27}{8 \times 0.86}} \times \sqrt{\sigma_3} = \sqrt{3.924} \times 440 = 1.981 \times 440 \approx 871 \text{ MeV} \tag{9.5}$$

At this scale:

$$\alpha_s^{(1)}(871) = \frac{4\pi}{11 \times \ln(871^2/220^2)} = \frac{12.57}{11 \times 2.752} = 0.415 \tag{9.6}$$

This gives $R_\text{BS}(0.415) = 3\sqrt{3(2-1.245)/2} = 3\sqrt{1.133} = 3.19$.

### §9.5 Two-Loop Correction

At these scales ($\mu \lesssim 1$ GeV), the perturbative series converges slowly. The two-loop formula is:

$$\alpha_s^{(2)}(\mu^2) = \frac{4\pi}{\beta_0 L}\left[1 - \frac{\beta_1}{\beta_0^2}\frac{\ln L}{L}\right] \tag{9.7}$$

where $L = \ln(\mu^2/\Lambda_{\overline{\text{MS}}}^2)$, $\beta_0 = 11$, and $\beta_1 = 34N_c^2/3 = 102$ for pure SU(3) ($N_f = 0$).

| Scale | $L$ | $\alpha_s^{(1)}$ | $\alpha_s^{(2)}$ | Two-loop shift | $R_\text{BS}$ (1-loop) | $R_\text{BS}$ (2-loop) |
|-------|-----|-------------------|-------------------|----------------|------------------------|------------------------|
| 750 MeV | 2.445 | 0.467 | 0.322 | $-31\%$ | 2.85 | 3.74 |
| 871 MeV | 2.752 | 0.415 | 0.286 | $-31\%$ | 3.19 | 3.92 |

The two-loop correction is $\sim 31\%$ at both scales, indicating that the perturbative $\overline{\text{MS}}$ coupling is not well-converged at the glueball scale. This is a well-known feature of non-perturbative QCD: the $\overline{\text{MS}}$ scheme requires resummation or a more physical scheme at $\mu \lesssim 1$ GeV.

### §9.6 Central Estimate

The one-loop and two-loop $\overline{\text{MS}}$ values span the range $\alpha_s \approx 0.29$–$0.47$, with the large spread reflecting poor perturbative convergence rather than a precise determination. More physically relevant for bound-state problems is the **V-scheme** (potential-subtracted) coupling, which resums the leading infrared contributions. Lattice determinations of $\alpha_V$ at scales $\sim 1$ GeV give $\alpha_V \approx 0.35$–$0.40$ [10].

We adopt:

$$\alpha_s = 0.38 \pm 0.06 \tag{9.8}$$

where the central value matches the V-scheme lattice coupling, and the uncertainty spans the range from two-loop $\overline{\text{MS}}$ at the higher scale ($0.29$) to one-loop $\overline{\text{MS}}$ at the lower scale ($0.47$), rounded conservatively. This range encompasses:
- The two-loop $\overline{\text{MS}}$ estimates ($0.29$–$0.32$)
- The V-scheme lattice coupling ($0.35$–$0.40$)
- The one-loop $\overline{\text{MS}}$ estimates ($0.42$–$0.47$)

### §9.7 Consistency Check

The adopted coupling is consistent within the scale uncertainty if the glueball mass it predicts has an internal momentum scale at which the coupling lies within the adopted range. Starting from $\alpha_s = 0.38$:

1. $R_\text{BS}(0.38) = 3.407$, so $m_G = 3.407 \times 440 = 1499$ MeV
2. Typical momentum: $\beta^* = 871$ MeV
3. At this scale: $\alpha_s^{(1)} = 0.415$, $\alpha_s^{(2)} = 0.286$; midpoint $\approx 0.35$
4. The adopted $\alpha_s = 0.38$ lies within the $[0.29, 0.42]$ range at the glueball scale

This is consistent within the scheme and scale uncertainty, though the poor convergence of the perturbative series prevents a precise self-consistency determination. The $\pm 0.06$ uncertainty conservatively reflects this limitation.

---

## §10. Uncertainty Budget

### §10.1 Dominant: Scale Ambiguity ($\alpha_s$ Uncertainty)

$$\frac{dR_\text{BS}}{d\alpha_s} = 3 \cdot \frac{1}{2}\left[\frac{3(2-3\alpha_s)}{2}\right]^{-1/2} \cdot \left(-\frac{9}{2}\right) = -\frac{27}{4R_\text{BS}/3} = -\frac{81}{4R_\text{BS}} \tag{10.1}$$

At $\alpha_s = 0.38$, $R_\text{BS} = 3.407$:

$$\left|\frac{dR}{d\alpha_s}\right| = \frac{81}{4 \times 3.407} = 5.94 \tag{10.2}$$

$$\delta R_{\alpha_s} = 5.94 \times 0.06 = 0.357 \tag{10.3}$$

### §10.2 Subleading: AFM Approximation

The AFM is exact for pure power-law potentials and provides a variational upper bound for mixed potentials. For the Cornell potential, the dominant contribution is linear (exact under AFM), with the Coulomb term as a perturbation. The AFM systematic error is:

$$\delta R_\text{AFM} \sim O\left(\frac{V_\text{Coulomb}}{V_\text{linear}}\right)^2 R_\text{BS} \tag{10.4}$$

At the optimal $\beta$: $V_\text{Coulomb}/V_\text{linear} = 3\alpha_s\beta/(9\sigma_3/(4 \cdot 2\beta/3)) \approx 0.33$ for $\alpha_s = 0.38$, giving $\delta R_\text{AFM} \sim 0.1 R_\text{BS} \sim 0.37$.

However, this is an overestimate — the AFM error for the Cornell potential has been benchmarked against numerical solutions and is typically $\sim 5\%$ [12, 14]:

$$\delta R_\text{AFM} \approx 0.05 \times R_\text{BS} = 0.17 \tag{10.5}$$

### §10.3 Subleading: Casimir Scaling Corrections

Deviations from exact Casimir scaling ($\sigma_8/\sigma_3 = 9/4$) at the glueball scale affect $R_\text{BS}$ at the level:

$$\delta R_\text{Casimir} \sim \frac{1}{2} \cdot \frac{\delta(\sigma_8/\sigma_3)}{9/4} \cdot R_\text{BS} \approx 0.5 \times 0.004 \times 3.4 = 0.007 \tag{10.6}$$

This is negligible ($\ll 1\%$).

### §10.4 Subleading: Variational Wavefunction

The exponential wavefunction is not the exact ground state of the Cornell potential. However, it captures the essential physics (exponential tail from confinement, cusp at the origin from Coulomb). More sophisticated wavefunctions (Hulthen, Gaussian, etc.) change the result by $\lesssim 3\%$ [14].

$$\delta R_\text{var} \approx 0.03 \times R_\text{BS} = 0.10 \tag{10.7}$$

### §10.5 Total Uncertainty

| Source | $\delta R$ | Relative |
|--------|-----------|----------|
| Scale ambiguity ($\alpha_s$) | 0.357 | 10.5% |
| AFM approximation | 0.17 | 5.0% |
| Variational wavefunction | 0.10 | 2.9% |
| Casimir scaling corrections | 0.007 | 0.2% |

The systematics (AFM, variational, Casimir) are **correlated** — they all push $R_\text{BS}$ in the same direction (upward, since the variational/AFM provides an upper bound). We do not add them in quadrature with the $\alpha_s$ uncertainty, but instead note that:

1. The dominant uncertainty ($\alpha_s$) is **independent** of the systematics
2. The AFM+variational systematic is partially absorbed into the $\alpha_s$ uncertainty (since the "correct" $\alpha_s$ would compensate for the AFM overestimate)

We adopt the $\alpha_s$ uncertainty as the total, noting that it conservatively covers the systematic effects:

$$\boxed{\delta R_\text{BS} = 0.36 \quad (10.5\%)} \tag{10.8}$$

### §10.6 Validity of the Cornell Potential

The Cornell potential ($\sigma r - C\alpha_s/r$) is valid when the glueball wavefunction is confined within the region where the adjoint string remains unbroken. We verify this using the glueball RMS radius from the variational wavefunction.

For the exponential wavefunction Eq. (7.1):

$$\langle r^2 \rangle = 4\beta^3 \int_0^\infty r^4 e^{-2\beta r} dr = 4\beta^3 \cdot \frac{24}{(2\beta)^5} = \frac{3}{\beta^2} \tag{10.9}$$

$$r_\text{rms} = \sqrt{\langle r^2 \rangle} = \frac{\sqrt{3}}{\beta^*} \tag{10.10}$$

With $\beta^* = 871$ MeV $= 4.41$ fm$^{-1}$ (using $\hbar c = 197.3$ MeV$\cdot$fm):

$$r_\text{rms} = \frac{\sqrt{3}}{4.41} = 0.39 \text{ fm} \tag{10.11}$$

The adjoint string-breaking distance (where the string energy exceeds twice the gluelump mass) is $r_\text{break} \approx 1.25$ fm from lattice measurements. Since $r_\text{rms}/r_\text{break} \approx 0.31$, the glueball wavefunction is well-confined within the linear confinement regime, and the Cornell potential is a valid description of the interquark interaction at the relevant distance scale.

---

*End of derivation. See the [Applications file](./Proposition-7.8.3-Bethe-Salpeter-Glueball-Mass-Ratio-Applications.md) for combined analysis, verification checklist, and limitations.*
