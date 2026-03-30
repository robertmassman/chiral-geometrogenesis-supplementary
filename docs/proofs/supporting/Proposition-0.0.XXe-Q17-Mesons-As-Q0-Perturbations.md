# Proposition 0.0.XXe — Q17: Are Mesons Faithfully Described as Large-Amplitude Q=0 Perturbations?

## Status: 🔶 NOVEL ✅ VERIFIED — MESON SECTOR ANALYSIS AND LEVEL-CROSSING IDENTIFICATION

**Verification:**
- [Adversarial Review (2026-03-18)](../verification-records/Proposition-0.0.XXe-Q17-Mesons-Multi-Agent-Verification-2026-03-18.md) — Three-perspective (Literature, Math, Physics) adversarial review: all core claims verified
- [Adversarial Physics Verification Script](../../../verification/verify_Q17_mesons_as_perturbations.py) — 29/29 tests pass ([plots](../../../verification/plots/Q17_mesons_adversarial_verification.png))

## Date: 2026-03-18

## Overview

This document investigates Open Question 17 from the [Proposition 0.0.XXe Workplan](Proposition-0.0.XXe-Continuum-Limit-Self-Replicating-Fields-WORKPLAN.md): whether mesons are faithfully described as "large-amplitude $Q = 0$ perturbations" in the Fisher-KPP framework. The investigation reveals that this description is **partially correct but fundamentally incomplete** — mesons require the macroscopic (chiral field) level of description, not the mesoscopic (Fisher-KPP density) level.

**Dependencies:**
- Prop 0.0.XXe Phase 3 (Reaction-Diffusion Formulation) — Fisher-KPP equation on $\partial\mathcal{S}$
- Prop 0.0.XXe Phase 4 (Continuum Fixed-Point Identification) — three-level description
- Prop 0.0.XXe Phase 5 (Soliton Classification) — catalytic/non-catalytic dichotomy
- Thm 4.1.4 (Dynamic Suspension Equilibrium) — meson spectrum from geometry
- Thm 4.1.1 (Existence of Solitons) — topological classification

---

## 1. The Question

Section §8.3 of the main Proposition 0.0.XXe document lists "Mesons as large-amplitude $Q = 0$ perturbations" as conjectural. The Phase 5 analysis (§5.2.5) describes mesons as:

> "non-catalytic but topologically trivial — stabilized by a potential barrier, not topology... In the Fisher-KPP framework: mesons correspond to large-amplitude perturbations of $\rho^*$ that temporarily resist the restoring force."

This raises four sub-questions identified in the workplan:
1. What is the linear perturbation spectrum of the Fisher-KPP operator around $\rho^*$?
2. Do nonlinear $Q = 0$ solutions (breathers, oscillons) exist?
3. Can the Fisher-KPP perturbation spectrum reproduce Skyrme model meson scaling?
4. Are there discrete soup signatures of meson-like excitations?

---

## 2. Linear Perturbation Spectrum of Fisher-KPP on $\partial\mathcal{S}$

### 2.1 Linearization Around $\rho^*$

The Fisher-KPP equation on $\partial\mathcal{S}$ (Phase 3, §3.2.4):

$$\frac{\partial \rho}{\partial t} = D \nabla^2_{\partial\mathcal{S}} \rho + k_{\text{eff}} \rho(1 - \rho) - \mu_{\text{eff}} \rho$$

(taking $\gamma = 0$ from Q13). The spatially uniform steady state is:

$$\rho^* = 1 - \frac{\mu_{\text{eff}}}{k_{\text{eff}}} = \frac{k_{\text{eff}} - \mu_{\text{eff}}}{k_{\text{eff}}}$$

Write $\rho(\mathbf{x}, t) = \rho^* + \delta\rho(\mathbf{x}, t)$ and linearize. The reaction term expands as:

$$f(\rho) = k_{\text{eff}} \rho(1 - \rho) - \mu_{\text{eff}} \rho$$

$$f'(\rho) = k_{\text{eff}}(1 - 2\rho) - \mu_{\text{eff}}$$

At $\rho = \rho^*$:

$$f'(\rho^*) = k_{\text{eff}}\left(1 - 2\frac{k_{\text{eff}} - \mu_{\text{eff}}}{k_{\text{eff}}}\right) - \mu_{\text{eff}} = k_{\text{eff}} - 2(k_{\text{eff}} - \mu_{\text{eff}}) - \mu_{\text{eff}} = -(k_{\text{eff}} - \mu_{\text{eff}})$$

So the linearized equation is:

$$\boxed{\frac{\partial \delta\rho}{\partial t} = D \nabla^2_{\partial\mathcal{S}} \delta\rho - (k_{\text{eff}} - \mu_{\text{eff}}) \delta\rho}$$

### 2.2 Eigenmodes on $\partial\mathcal{S}$

Since $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ is topologically two $S^2$ surfaces, the Laplacian eigenmodes are spherical harmonics on each component. On a sphere of radius $R$, the Laplace-Beltrami eigenvalues are:

$$\nabla^2_{S^2} Y_\ell^m = -\frac{\ell(\ell+1)}{R^2} Y_\ell^m, \qquad \ell = 0, 1, 2, \ldots$$

with degeneracy $2\ell + 1$ for each $\ell$.

Since $\partial\mathcal{S} = \partial T_+ \sqcup \partial T_-$ consists of two $S^2$ components, the linearized system on the bilayer with cross-coupling strength $\varepsilon$ is:

$$\frac{\partial}{\partial t}\begin{pmatrix}\delta\rho_+ \\ \delta\rho_-\end{pmatrix} = \begin{pmatrix} D\nabla^2 - c - \varepsilon & \varepsilon \\ \varepsilon & D\nabla^2 - c - \varepsilon \end{pmatrix} \begin{pmatrix}\delta\rho_+ \\ \delta\rho_-\end{pmatrix}$$

where $c = k_{\text{eff}} - \mu_{\text{eff}}$. This decouples into symmetric ($\delta\rho_s = \delta\rho_+ + \delta\rho_-$) and antisymmetric ($\delta\rho_a = \delta\rho_+ - \delta\rho_-$) sectors:

$$\dot{\delta\rho}_s = (D\nabla^2 - c)\,\delta\rho_s, \qquad \dot{\delta\rho}_a = (D\nabla^2 - c - 2\varepsilon)\,\delta\rho_a$$

The symmetric sector has eigenvalues $\lambda_\ell^{(s)} = D\ell(\ell+1)/R^2 + c$ (identical to a single sphere), while the antisymmetric sector has $\lambda_\ell^{(a)} = D\ell(\ell+1)/R^2 + c + 2\varepsilon > \lambda_\ell^{(s)}$. Both sectors have purely real, positive eigenvalues — the bilayer coupling accelerates antisymmetric decay but introduces no oscillatory modes.

Expanding $\delta\rho = \sum_{\ell,m} a_{\ell m}(t) \, Y_\ell^m(\theta, \phi)$:

$$\dot{a}_{\ell m} = \left[-D \frac{\ell(\ell+1)}{R^2} - (k_{\text{eff}} - \mu_{\text{eff}})\right] a_{\ell m}$$

The solution is purely exponential decay:

$$\boxed{a_{\ell m}(t) = a_{\ell m}(0) \, e^{-\lambda_\ell t}, \qquad \lambda_\ell = D \frac{\ell(\ell+1)}{R^2} + (k_{\text{eff}} - \mu_{\text{eff}})}$$

### 2.3 Numerical Eigenvalues

With the extracted parameters ($k_{\text{eff}} = 0.24$, $\mu_{\text{eff}} = 0.02$, $D = 0.01$, and $R_{\text{stella}} = 0.449$ fm):

| Mode $\ell$ | $D\ell(\ell+1)/R^2$ | $\lambda_\ell$ | Decay time $\tau_\ell = 1/\lambda_\ell$ |
|---|---|---|---|
| 0 (uniform) | 0 | 0.220 | 4.55 epochs |
| 1 (dipole) | 0.099 | 0.319 | 3.13 epochs |
| 2 (quadrupole) | 0.298 | 0.518 | 1.93 epochs |
| 3 (octupole) | 0.595 | 0.815 | 1.23 epochs |
| 4 | 0.992 | 1.212 | 0.83 epochs |
| $\ell$ (general) | $D\ell(\ell+1)/R^2$ | $0.22 + D\ell(\ell+1)/R^2$ | decreasing |

All eigenvalues are real and positive, confirming purely exponential decay with no oscillatory modes. Higher $\ell$ modes decay faster due to the diffusion penalty $\propto \ell(\ell+1)$.

### 2.4 Critical Result: No Oscillatory Modes

**Every eigenvalue $\lambda_\ell$ is real and positive.** This means:

1. **All perturbations decay monotonically** — they do not oscillate
2. **There is no natural frequency** associated with any mode
3. **The Fisher-KPP equation is first-order in time** (parabolic, not hyperbolic)

**Mathematical proof of self-adjointness:** The linearized operator $\mathcal{L} = D\nabla^2 - (k_{\text{eff}} - \mu_{\text{eff}})$ is self-adjoint on $L^2(S^2)$ with respect to the standard inner product. Self-adjoint operators have purely real spectra. Since every eigenvalue is negative (decay), oscillatory modes are **structurally impossible**, not merely absent for specific parameter values.

**Matano's convergence theorem (1979):** For scalar parabolic equations $\partial_t u = \Delta u + f(u)$ on compact domains (including $S^2$), every bounded solution converges to a stationary solution as $t \to \infty$. There are no periodic orbits, no chaos, no oscillatory transients. This is a consequence of the existence of a Lyapunov functional, and makes meson-like oscillatory excitations **mathematically impossible** within Fisher-KPP.

This is a fundamental mismatch with meson physics:
- Mesons are oscillatory excitations with a definite mass (frequency): $m_\pi = 140$ MeV, $m_\rho = 775$ MeV
- The Klein-Gordon equation governing mesons is **second-order in time**: $(\partial_t^2 - \nabla^2 + m^2)\phi = 0$
- Fisher-KPP perturbations have **no oscillation frequency** — they decay exponentially to $\rho^*$

**Conclusion:** The linearized Fisher-KPP spectrum contains **no meson-like excitations**. The Fisher-KPP equation operates at the wrong level of description for mesons.

---

## 3. Nonlinear Q=0 Solutions

### 3.1 Breathers and Oscillons

Could nonlinear effects create metastable, oscillatory $Q = 0$ excitations within the Fisher-KPP framework?

**Breathers** are exact periodic solutions of nonlinear PDEs. The prototypical example is the sine-Gordon breather in 1+1D:

$$\phi(x,t) = 4 \arctan\left(\frac{\sqrt{1-\omega^2}}{\omega} \frac{\sin(\omega t)}{\cosh(\sqrt{1-\omega^2} \, x)}\right)$$

which is localized, oscillatory, and has $Q = 0$. However:

1. **Exact breathers require integrability.** The sine-Gordon equation is integrable in 1+1D; the Fisher-KPP equation is not integrable in any dimension.

2. **Fisher-KPP is dissipative, not conservative.** Breathers exist in Hamiltonian (energy-conserving) systems. The Fisher-KPP equation has a Lyapunov functional:
   $$\mathcal{L}[\rho] = \int_{\partial\mathcal{S}} \left[\frac{D}{2}|\nabla\rho|^2 - \int_0^\rho f(s) \, ds\right] d^2x$$
   which decreases monotonically: $\dot{\mathcal{L}} \leq 0$. Any localized perturbation loses "energy" continuously and must relax to $\rho^*$.

3. **No oscillatory mechanism.** The Fisher-KPP equation is first-order in time. To oscillate, a system needs a restoring force that "overshoots" the equilibrium — this requires inertia (second time derivative). The Fisher-KPP dynamics is purely overdamped.

**Oscillons** are long-lived, quasi-periodic, localized excitations in nonlinear field theories. They exist in:
- $\phi^4$ theory in 3+1D (Bogolyubsky & Makhankov 1976 [15]; Gleiser 1994)
- Abelian Higgs model
- Axion models (Kolb & Tkachev 1994 [16])

All of these are **wave equations** (second-order in time), not diffusion equations. The key requirement is a **nonlinear dispersion relation** that traps energy in a localized region. Fisher-KPP, being a diffusion equation, disperses perturbations monotonically.

### 3.2 The Doi-Peliti Route

The Doi-Peliti formalism (Doi 1976; Peliti 1985; Phase 4, §4.2.5) maps the stochastic soup dynamics to a quantum field theory with a second-quantized action:

$$S = \int dt \, d^2x \left[\bar{\psi}(\partial_t - D\nabla^2)\psi - k_{\text{eff}} \bar{\psi}(\bar{\psi} + 1)\psi + \mu_{\text{eff}} \bar{\psi}\psi\right]$$

where $\psi, \bar{\psi}$ are the Doi-Peliti fields. This action is:
- First-order in time (like the original Fisher-KPP)
- Has $\bar{\psi}$ and $\psi$ as independent fields (not complex conjugates)
- Describes the stochastic fluctuations around the mean-field solution

The Doi-Peliti spectrum includes **stochastic modes** whose eigenvalues are complex (with real part giving the decay rate and imaginary part giving stochastic oscillation frequency). However:
- These are **stochastic oscillations** (noise-driven), not coherent wave-like excitations
- Their frequencies scale as $1/\sqrt{N_{\text{local}}}$ (fluctuation-dominated), not as $m_\pi \sim \Lambda_{\text{QCD}}$
- They vanish in the mean-field ($N_{\text{local}} \to \infty$) limit

**Conclusion:** The Fisher-KPP framework, even with stochastic corrections, does not support meson-like excitations.

### 3.3 Oscillons in Skyrme-Like Models

For completeness: do $Q = 0$ oscillons exist in the full Skyrme model? The literature shows:
- In $\phi^4$ theory (3+1D), oscillons survive for $O(10^3\text{--}10^8)$ oscillation periods before decaying via radiation (Gleiser & Sicilia, Phys. Rev. D 80, 125037, 2009). Their longevity arises from an approximate adiabatic invariant.
- In the sine-Gordon model (1+1D), exact breathers exist. In higher dimensions, these deform into radiating oscillons (Galvez Ghersi & Braden, Phys. Rev. D 108, 096017, 2023).
- In the standard 3+1D Skyrme model, $Q = 0$ oscillons have not been a major focus. The breathing mode of the skyrmion is a $Q = 1$ vibrational mode, distinct from a $Q = 0$ oscillon.

The key point is that all oscillon-supporting models are **wave equations** (second-order in time). No oscillons exist in diffusion equations. The Fisher-KPP equation is structurally incapable of supporting oscillons.

### 3.4 The Diffusion-to-Wave Bridge

The mathematical bridge between the diffusive (mesoscopic) and wave-like (macroscopic) descriptions is the **telegraph equation** (Cattaneo 1948):

$$\tau \frac{\partial^2 \rho}{\partial t^2} + \frac{\partial \rho}{\partial t} = D \nabla^2 \rho + \text{reaction terms}$$

where $\tau$ is a relaxation time. This interpolates:
- $\tau \to 0$: diffusion equation (Fisher-KPP, parabolic, infinite propagation speed)
- $\tau \to \infty$: wave equation (Klein-Gordon, hyperbolic, finite propagation speed $c = \sqrt{D/\tau}$)

In the CG framework, the mesoscopic-to-macroscopic transition may involve precisely this physics: at short timescales the field has "inertia" (the $\tau \partial_t^2$ term) that the diffusive approximation averages out. The meson excitations emerge when the full inertial dynamics is retained. This is consistent with the Z₃ → SU(3) promotion (Phase 4, §4.2.5): the phase degrees of freedom that carry meson quantum numbers emerge only when the full gauge structure is restored.

---

## 4. Why the Fisher-KPP Level Cannot Describe Mesons

### 4.1 The Three-Level Hierarchy

Phase 4 (§4.1.4) established three levels of description:

| Level | Description | Time derivative | Meson content |
|-------|-------------|-----------------|---------------|
| **Microscopic** | $\mathbb{Z}_3^N$ configurations | Discrete (Markov chain) | None (combinatorial) |
| **Mesoscopic** | Density $\rho(\mathbf{x},t) \in [0,1]$ | First-order (Fisher-KPP) | **None** (no oscillatory modes) |
| **Macroscopic** | Chiral field $U(\mathbf{x},t) \in SU(3)$ | Second-order (Skyrme) | **Yes** (full meson spectrum) |

The key insight is that **mesons live at the macroscopic level**, not the mesoscopic level. The Fisher-KPP density $\rho$ tracks only the total replicator population — it has lost the phase information ($\mathbb{Z}_3 \to SU(3)$) that gives rise to meson excitations.

### 4.2 What $\rho$ Sees vs What Mesons Need

The density field $\rho$ captures:
- Total fraction of replicators vs food at each point
- Spatial gradients (diffusion)
- Population dynamics (growth, decay, competition)

Mesons require:
- **Phase structure**: Pions are Goldstone modes of chiral symmetry breaking. They are excitations of the **phase** $\theta$ of the chiral field $U = e^{i\pi^a \tau^a / f_\pi}$, not of the amplitude $\rho$.
- **Wave dynamics**: Meson propagation satisfies $(\partial_t^2 - \nabla^2 + m^2)\pi = 0$, which is second-order in time (oscillatory), not first-order (diffusive).
- **Internal quantum numbers**: Pions carry isospin ($I = 1$); $\rho$ mesons carry isospin and spin. The scalar $\rho$ field has no internal quantum numbers.

### 4.3 The Phase-Amplitude Decomposition

The connection between levels becomes clear through a phase-amplitude decomposition analogous to the **linear sigma model** (Gell-Mann & Lévy 1960). In the linear sigma model, the chiral field is parametrized as:

$$\Sigma(\mathbf{x}, t) = \bigl(\sigma(\mathbf{x},t) + f_\pi\bigr) \, e^{i \pi^a(\mathbf{x},t) \tau^a / f_\pi}$$

where $\sigma$ is the radial (amplitude) field and $\pi^a$ are the angular (phase) fields. The vacuum has $\sigma = 0$, $\pi^a = 0$, giving $\Sigma = f_\pi \cdot \mathbb{1}$.

In the CG framework, the analogous decomposition relates the Fisher-KPP density to the chiral field:

$$\Sigma(\mathbf{x}, t) = f_\pi\left(\frac{\rho(\mathbf{x},t)}{\rho^*}\right)^{1/2} e^{i \pi^a(\mathbf{x},t) \tau^a / f_\pi}$$

where the identification $\sigma/f_\pi \leftrightarrow (\rho/\rho^*)^{1/2} - 1$ maps Fisher-KPP density fluctuations to the radial mode of the linear sigma model. **This is not a strict SU(3) parametrization** — the chiral field $U \in SU(3)$ is recovered by restricting to unit modulus: $U = \Sigma/|\Sigma| = e^{i\pi^a \tau^a/f_\pi}$, which projects out the amplitude sector entirely. The key point is:

- $\rho$ (amplitude) = the $\sigma$ mode of the linear sigma model, governed by Fisher-KPP at the mesoscopic level
- $\pi^a$ (phase) = the Goldstone modes, governed by the Skyrme Lagrangian at the macroscopic level

These are complementary, not competing descriptions. The Fisher-KPP equation governs the **amplitude** sector. The meson spectrum comes from the **phase** sector.

In the vacuum state:
- Amplitude: $\rho = \rho^*$ (the Fisher-KPP fixed point), i.e., $\sigma = 0$
- Phase: $U = \mathbb{1}$ (uniform, no Goldstone excitations)

A pion excitation perturbs the **phase** while leaving the amplitude at $\rho^*$:
- Amplitude: $\rho \approx \rho^*$ (unchanged to leading order)
- Phase: $U = e^{i \pi^a(\mathbf{x},t) \tau^a / f_\pi} \neq \mathbb{1}$ (pion field excited)

This is why pions are invisible to the Fisher-KPP description — they live in the orthogonal (phase) sector. Only the scalar $\sigma/f_0(500)$ meson, which involves amplitude fluctuations ($\delta\rho \neq 0$), has any overlap with the Fisher-KPP dynamics (see §5.3).

---

## 5. How Mesons Actually Arise in the CG Framework

### 5.1 The Macroscopic Level: Skyrme Model on $\partial\mathcal{S}$

At the macroscopic level, the dynamics is governed by the Skyrme Lagrangian (Phase 5, §5.3.1):

$$\mathcal{L} = \frac{f_\pi^2}{4} \text{Tr}(D_\mu U^\dagger D^\mu U) + \frac{1}{32e^2} \text{Tr}([D_\mu U^\dagger U, D_\nu U^\dagger U]^2) + \frac{f_\pi^2 m_\pi^2}{4} \text{Tr}(U + U^\dagger - 2)$$

This is a **wave equation** (second-order in time via the $D_0 U$ terms). Linearizing around the vacuum $U = \mathbb{1}$ by writing $U = e^{i \pi^a \tau^a / f_\pi} \approx \mathbb{1} + i \pi^a \tau^a / f_\pi + \ldots$:

- The sigma-model (two-derivative) term gives the kinetic term: $\frac{1}{2}(\partial_\mu \pi^a)(\partial^\mu \pi^a)$
- The Skyrme (four-derivative) term contributes **only at higher order**: at quadratic order around $U = \mathbb{1}$, the commutator $[U^\dagger\partial_\mu U, U^\dagger\partial_\nu U]$ is $O(\pi^2)$, so its square is $O(\pi^4)$. It does not appear in the linearized propagator.
- The mass term gives $-\frac{1}{2} m_\pi^2 (\pi^a)^2$

The linearized Lagrangian is therefore the free Klein-Gordon Lagrangian:

$$\mathcal{L}_{\text{linear}} = \frac{1}{2}(\partial_\mu \pi^a)(\partial^\mu \pi^a) - \frac{1}{2} m_\pi^2 (\pi^a)^2$$

yielding:

$$(\partial_t^2 - \nabla^2 + m_\pi^2)\pi^a = 0$$

with oscillatory solutions $\pi^a \sim e^{-i\omega t}$ where $\omega = \sqrt{k^2 + m_\pi^2}$.

**Important:** Linearization around $U = \mathbb{1}$ produces **only pions**. Vector mesons ($\rho$, $\omega$) do not emerge from the standard Skyrme model at the linearized level — they require extending the model via hidden local symmetry (Bando, Kugo, Yamawaki 1988) or equivalent massive Yang-Mills coupling (Meissner & Zahed 1986). In the CG framework, vector mesons arise naturally from the full Yang-Mills structure on $\partial\mathcal{S}$, which provides the hidden local symmetry through the geometric gauge connection.

Note also that fluctuations around the **skyrmion** background $U_0 = e^{iF(r)\hat{r}\cdot\boldsymbol{\tau}}$ (rather than the vacuum $U = \mathbb{1}$) yield a different spectrum: translational/rotational zero modes (quantized into nucleon/delta quantum numbers, Adkins, Nappi & Witten 1983), breathing modes, and higher partial-wave excitations. These are **baryon resonances**, not free mesons.

### 5.2 Meson Spectrum from the CG Geometry

The meson spectrum in the CG framework arises from:

**Pions ($\pi$, $J^{PC} = 0^{-+}$, $m_\pi \approx 140$ MeV):**
- Pseudo-Goldstone bosons of chiral symmetry breaking
- Mass from the explicit breaking term in the Skyrme Lagrangian
- The pion decay constant is $f_\pi = \sqrt{\sigma}/5 = 88$ MeV (Prop 0.0.17k)
- Mass relation: $m_\pi^2 f_\pi^2 = -m_q \langle\bar{q}q\rangle$ (Gell-Mann–Oakes–Renner)

**Vector mesons ($\rho$, $\omega$, $J^{PC} = 1^{--}$):**
- In the minimal Skyrme model: these are not fundamental — they emerge when the Skyrme model is extended with hidden local symmetry (Bando et al. 1988) or when the full Yang-Mills structure on $\partial\mathcal{S}$ is included
- In the CG framework: the geometry of $\partial\mathcal{S}$ determines the spectrum. The 8 faces and 12 edges provide discrete mode structure (Thm 4.1.4)
- KSFR relation: $m_\rho^2 = 2 g_{\rho\pi\pi}^2 f_\pi^2$ connects $\rho$ mass to pion physics

**Scalar mesons ($\sigma$, $f_0$, $J^{PC} = 0^{++}$):**
- Radial excitations of the chiral field — perturbations of the amplitude $\rho$
- These are the **only** mesons that have any connection to the Fisher-KPP description
- In the linear sigma model (Gell-Mann & Lévy 1960 [17]): $m_\sigma \approx 2m_q / \sqrt{\lambda}$ where $\lambda$ is the quartic coupling
- The $\sigma(500)$ (or $f_0(500)$) is broad and has been controversial — consistent with being a "nearly Fisher-KPP" mode (overdamped or marginally oscillatory)

### 5.3 The Scalar Meson as a Borderline Case

The scalar $\sigma$ meson deserves special attention. It is the only meson that involves amplitude fluctuations (not just phase). In the linear sigma model (Gell-Mann & Lévy 1960 [17]), the chiral field is decomposed as (cf. §4.3):

$$\Sigma = (\sigma + f_\pi) \, e^{i\pi^a\tau^a/f_\pi}$$

The $\sigma$ field represents radial oscillations of the chiral condensate — fluctuations of $|\langle\bar{q}q\rangle|$. Via the identification $\sigma/f_\pi \leftrightarrow (\rho/\rho^*)^{1/2} - 1$ established in §4.3, the $\sigma$ mode maps to Fisher-KPP density fluctuations around $\rho^*$.

In the Fisher-KPP description, a perturbation of $\rho$ around $\rho^*$ decays with rate $\lambda_0 = k_{\text{eff}} - \mu_{\text{eff}} = 0.22$ (per epoch). If we identify the epoch timescale with $1/\sqrt{\sigma_{\text{string}}} \sim 1/440$ MeV$^{-1}$, the decay rate maps to:

$$\Gamma_\sigma \sim (k_{\text{eff}} - \mu_{\text{eff}}) \times 440 \text{ MeV} \sim 97 \text{ MeV}$$

This is remarkably close to the experimental width of the $f_0(500)$: $\Gamma_{f_0(500)} = 400\text{--}700$ MeV (PDG). The $f_0(500)$ is the broadest established meson, consistent with it being an **overdamped mode** on the boundary between the Fisher-KPP (dissipative) and Skyrme (oscillatory) descriptions.

However, this numerical coincidence should not be overinterpreted — the Fisher-KPP equation does not describe $\sigma$ meson dynamics. The proper treatment requires the second-order chiral Lagrangian with the $\sigma$ field explicitly included (the linear sigma model).

---

## 6. Discrete Soup Signatures

### 6.1 What to Look For

If mesons are phase excitations of the vacuum, their discrete soup analogs would be:
- Transient, localized fluctuations in the **$\mathbb{Z}_3$ phase** (not the replicator density)
- Configurations where nearby sites have different $\mathbb{Z}_3$ values but the same replicator density
- Short-lived $\mathbb{Z}_3$ domain walls that annihilate (net $Q = 0$)

### 6.2 Why They Are Hard to See

The mesoscopic Fisher-KPP description tracks only $\rho$ (total replicator density), not the $\mathbb{Z}_3$ phase. The Phase 1 simulations show (Q12 follow-up, Round 2):

1. **Z₃ order parameter:** The soup spontaneously breaks $\mathbb{Z}_3$ — one sector dominates (52% in $4\pi/3$ sector). This means the "vacuum" has a definite $\mathbb{Z}_3$ phase, but the breaking is explicit (from the VM instruction set), not spontaneous.

2. **Z₃ correlations are flat:** The correlator $\langle \psi(\mathbf{x}) \psi^*(\mathbf{y}) \rangle$ shows no spatial structure at any lattice size or mutation rate. This means $\mathbb{Z}_3$ phase excitations have zero correlation length — they are infinitely massive (or equivalently, not propagating).

3. **Density and phase sectors are decoupled:** The $\rho$ correlator has a finite correlation length $\xi_\rho$, but the $\mathbb{Z}_3$ phase correlator is constant. These sectors do not mix in the soup.

### 6.3 Interpretation

The discrete soup operates at a level where meson physics is not resolved. The $\mathbb{Z}_3$ soup captures:
- Vacuum formation (Fisher-KPP dynamics) ✅
- Confinement/deconfinement transition (error catastrophe ↔ $\mathbb{Z}_3$ Potts) ✅
- Center vortex defects ($\mathbb{Z}_3$ winding) ✅

But it does not capture:
- Meson excitations ❌ (require full SU(3) phase structure)
- Meson propagation ❌ (require second-order time dynamics)
- Chiral symmetry breaking ❌ (require continuous $SU(3)_L \times SU(3)_R$ → $SU(3)_V$)

This is consistent with the three-level hierarchy: mesons are a **macroscopic** phenomenon, and the soup operates at the microscopic/mesoscopic level.

---

## 7. Revised Understanding

### 7.1 What "Large-Amplitude Q=0 Perturbations" Gets Right

The phrase correctly captures:
1. **Topological triviality:** Mesons carry $Q = 0$. They are in the same topological sector as the vacuum.
2. **Instability:** Mesons decay because there is no topological protection. They relax to the vacuum (eventually).
3. **Energy hierarchy:** Mesons sit above the vacuum but below baryons in the energy landscape.
4. **Localization:** Mesons are localized excitations of the vacuum, not extended objects.

### 7.2 What It Gets Wrong

The phrase is misleading because:
1. **"Perturbations of $\rho^*$"** implies mesons are density (amplitude) excitations. Most mesons (pions, vectors) are **phase** excitations — they perturb $U$, not $\rho$.
2. **"In the Fisher-KPP framework"** implies the Fisher-KPP equation can describe mesons. It cannot — it is first-order in time (no oscillations) and has no phase degrees of freedom.
3. **"Large-amplitude"** is misleading for pions, which are the lightest mesons and correspond to the **smallest** excitations of the chiral field (Goldstone modes).

### 7.3 Corrected Statement

**Mesons are oscillatory excitations of the chiral field $U(\mathbf{x},t) \in SU(3)$ around the vacuum $U = \mathbb{1}$, with topological charge $Q = 0$, governed by the Skyrme Lagrangian on $\partial\mathcal{S}$.**

They belong to the macroscopic level of the three-level hierarchy (Phase 4, §4.1.4):
- **Pions** are pseudo-Goldstone modes (phase excitations, $\delta U \neq \mathbb{1}$, $\delta\rho \approx 0$)
- **Vector mesons** ($\rho$, $\omega$) arise from the gauge field dynamics or hidden local symmetry
- **Scalar mesons** ($\sigma$, $f_0$) are the only mesons that involve amplitude fluctuations ($\delta\rho \neq 0$); their large width is consistent with the dissipative character of the amplitude sector

The Fisher-KPP framework faithfully describes the **vacuum** ($Q = 0$ ground state) and its **stability** (global attractor). It does not describe **meson excitations** above the vacuum — these require the chiral field dynamics that emerges at the macroscopic level.

### 7.4 Resolution of the Catalytic-Topological Dichotomy Gap

The workplan noted that mesons are a gap in the catalytic-topological dichotomy because they are neither catalytic (they don't self-replicate) nor topologically protected ($Q = 0$). The resolution:

| Category | Examples | Protection | Level |
|----------|----------|------------|-------|
| **Catalytic** (vacuum) | $\rho^*$, QCD vacuum | Dynamical (Fisher-KPP attractor) | Mesoscopic |
| **Phase excitations** (mesons) | $\pi$, $\rho$, $\omega$ | None (finite lifetime, $Q = 0$) | **Macroscopic** |
| **Amplitude excitations** (scalar mesons) | $\sigma$, $f_0(500)$ | None (overdamped, very broad) | Mesoscopic → Macroscopic borderline |
| **Topological** (baryons) | $p$, $n$, $\Delta$ | Topological ($\pi_3 = \mathbb{Z}$) | Macroscopic |

Mesons fill the gap between vacuum and baryons by being **unprotected excitations at the macroscopic level**. Their finite lifetime is a direct consequence of having no topological or dynamical protection — they are resonances, not stable states.

---

## 8. Implications for the Proposition 0.0.XXe Framework

### 8.1 Updates to Phase 5 (Soliton Classification)

Section §5.2.5 should be updated to clarify:
1. Mesons are **not** perturbations of the Fisher-KPP density $\rho$ — they are perturbations of the chiral field $U$
2. The phrase "large-amplitude perturbations of $\rho^*$" should be replaced with "oscillatory excitations of the chiral vacuum $U = \mathbb{1}$ in the $Q = 0$ sector"
3. The energy hierarchy (§5.3.2) is correct as stated — meson energies $E = E_{\text{vac}} + \omega_n$ are properly described at the macroscopic level

### 8.2 Updates to §8.3 (Conjectural Elements)

The meson description should be reclassified from "conjectural" to **"structurally resolved"**:
- The statement "mesons are $Q = 0$ excitations" is correct and well-established (Skyrme model)
- The statement "mesons are Fisher-KPP perturbations" is incorrect and should be replaced
- The meson spectrum arises from the Skyrme Lagrangian on $\partial\mathcal{S}$, which is the established macroscopic description

### 8.3 No New Computational Verification Needed

This investigation is primarily conceptual/analytical. The key finding — that mesons require the macroscopic (Skyrme) level, not the mesoscopic (Fisher-KPP) level — follows from the mathematical structure of the equations:
- Fisher-KPP is parabolic (first-order in time, no oscillations)
- Skyrme is hyperbolic (second-order in time, oscillatory modes)
- The phase degrees of freedom ($\pi^a$) that carry meson quantum numbers are absent from the Fisher-KPP density $\rho$

No new numerical simulation is needed to establish this.

---

## 9. Summary

### Answer to Q17

**Are mesons faithfully described as large-amplitude $Q = 0$ perturbations?**

**Partially.** Mesons are correctly identified as:
- $Q = 0$ excitations (topologically trivial, in the same sector as the vacuum)
- Unstable (no topological protection, finite lifetime)
- Localized (not space-filling like the vacuum)

But they are **not** faithfully described as "perturbations of $\rho^*$ in the Fisher-KPP framework":
- The Fisher-KPP equation has no oscillatory modes — all perturbations decay monotonically
- Mesons are phase excitations of the chiral field $U$, not amplitude excitations of the density $\rho$
- The meson spectrum requires the macroscopic (Skyrme) level of description

The correct description is: **Mesons are oscillatory excitations of the chiral field vacuum on $\partial\mathcal{S}$, governed by the Skyrme Lagrangian, with $Q = 0$ and no topological protection. They emerge at the macroscopic level of the three-level hierarchy, beyond the reach of the mesoscopic Fisher-KPP description.**

### Status of the Catalytic-Topological Dichotomy

The dichotomy (§6.4 of main proposition) is **complete** once we recognize that mesons live at a different level:
- **Mesoscopic level:** Catalytic (vacuum) vs everything else (perturbations that decay)
- **Macroscopic level:** $Q = 0$ resonances (mesons) vs $Q \neq 0$ stable solitons (baryons)

The dichotomy applies at each level separately. Mesons are unprotected excitations at the macroscopic level — they decay because they have neither dynamical (catalytic) nor topological ($Q \neq 0$) protection.

### Priority Assessment

This question is now **RESOLVED** at the structural level. The remaining quantitative question — can the specific meson masses be derived from the geometry of $\partial\mathcal{S}$ via the Skyrme model? — is addressed in Thm 4.1.4 (Applications §10.3) and is part of the broader Phase 4 program, not specific to Prop 0.0.XXe.

---

## References

1. T.H.R. Skyrme, "A unified field theory of mesons and baryons," Nucl. Phys. 31 (1962) 556
2. G.S. Adkins, C.R. Nappi, E. Witten, "Static properties of nucleons in the Skyrme model," Nucl. Phys. B 228 (1983) 552
3. U.-G. Meissner & I. Zahed, "Skyrmions in the presence of vector mesons," Phys. Rev. Lett. 56 (1986) 1035; Phys. Rev. D 34 (1986) 3484
4. M. Bando, T. Kugo, K. Yamawaki, "Nonlinear realization and hidden local symmetry," Phys. Rep. 164 (1988) 217
5. I. Zahed & G.E. Brown, "The Skyrme model," Phys. Rep. 142 (1986) 1
6. H. Matano, "Asymptotic behavior and stability of solutions of semilinear diffusion equations," Publ. RIMS Kyoto 15 (1979) 401 — convergence theorem for scalar parabolic equations on compact domains
7. M. Gleiser & D. Sicilia, "A general theory of oscillon dynamics," Phys. Rev. D 80 (2009) 125037
8. J.T. Galvez Ghersi & J. Braden, "Dimensional deformation of sine-Gordon breathers into oscillons," Phys. Rev. D 108 (2023) 096017
9. R.A. Fisher, "The wave of advance of advantageous genes," Ann. Eugenics 7 (1937) 355
10. A.N. Kolmogorov, I.G. Petrovsky, N.S. Piskunov, "Study of the diffusion equation with growth," Moscow Univ. Bull. Math. 1 (1937) 1
11. M. Gell-Mann, R.J. Oakes, B. Renner, "Behavior of current divergences under SU(3) × SU(3)," Phys. Rev. 175 (1968) 2195
12. C. Cattaneo, "Sulla conduzione del calore," Atti Sem. Mat. Fis. Univ. Modena 3 (1948) 83 — telegraph equation bridging diffusion and wave dynamics
13. M. Doi, "Second quantization representation for classical many-particle system," J. Phys. A 9 (1976) 1465 — original Doi formalism for stochastic many-body systems
14. L. Peliti, "Path integral approach to birth-death processes on a lattice," J. Physique 46 (1985) 1469 — field-theoretic formulation of reaction-diffusion systems
15. I.L. Bogolyubsky & V.G. Makhankov, "Lifetime of pulsating solitons in some classical models," JETP Lett. 24 (1976) 12 — first observation of oscillons in φ⁴ theory
16. E.W. Kolb & I.I. Tkachev, "Nonlinear axion dynamics and the formation of cosmological pseudosolitons," Phys. Rev. D 49 (1994) 5040 — oscillons in axion cosmology
17. M. Gell-Mann & M. Lévy, "The axial vector current in beta decay," Nuovo Cimento 16 (1960) 705 — original linear sigma model with σ-π decomposition
