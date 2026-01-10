/-
# Wave Equation and Huygens' Principle

This module provides a mathematical treatment of the wave equation and
Huygens' principle in n spatial dimensions, establishing the connection
between wave propagation and dimensionality.

## Overview

The **wave equation** in n spatial dimensions is:
  ∂²u/∂t² = c² ∇ₙ²u

where ∇ₙ² is the n-dimensional Laplacian and c is the wave speed.

**Huygens' principle** states that wavefronts propagate as sharp signals:
a δ-impulse at t=0 remains a δ-pulse at t>0, with no "afterglow" or tail.

## Key Results (Hadamard's Theorem, CORRECTED)

1. **n = 1 (odd but degenerate)**: Huygens' principle FAILS (no spreading mechanism)
2. **n = 2 (even)**: Signals have tails - afterglow persists after wavefront
3. **n = 3, 5, 7, ... (odd ≥ 3)**: Huygens' principle HOLDS - sharp propagation
4. **n = 4, 6, 8, ... (even)**: Signals have tails - no sharp propagation

**The precise characterization is: HuygensPrinciple n ↔ (Odd n ∧ n ≥ 3)**

## Units Convention

**We use geometric units where c = 1.** This means:
- The light cone is |x| = t (not |x| = ct)
- Time and space have the same dimensional units
- To convert to SI: replace t with ct

## Mathematical Structure

- `GreenFunction n`: Fundamental solution G(x,t) with □G = δ(x)δ(t)
- `OnLightCone n`: Points (x,t) with |x| = t and t > 0
- `HasSharpSupport`: Green's function supported only on light cone
- `HuygensPrinciple n`: n ≥ 3 ∧ Odd n ∧ HasSharpSupport n (GreenFunction n)

## Physical Significance

In 3D (n = 3, which is odd ≥ 3):
- Light signals arrive sharply without afterglow
- Sound waves don't "ring" indefinitely
- Communication is possible without signal smearing

In 2D (if we lived in a 2D world):
- A flash of light would create an expanding ring PLUS dim illumination
  that persists forever inside the ring
- Echoes would never completely fade

In 1D (despite being odd):
- Signals spread to fill the entire region |x| ≤ t, not concentrate on |x| = t
- The spreading is "filling" rather than "focusing" - no wavefront sharpening occurs
- Mathematically: G₁(x,t) = (1/2)θ(t - |x|), a step function not a delta

## References

- Hadamard, J. (1923). "Lectures on Cauchy's Problem"
- Courant, R. & Hilbert, D. (1962). "Methods of Mathematical Physics" Vol. II
- Günther, P. (1988). "Huygens' Principle and Hyperbolic Equations"
- McLenaghan, R.G. (1974). "On the validity of Huygens' principle"
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Topology.Basic

set_option linter.style.docString false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace ChiralGeometrogenesis.PureMath.Analysis

/-! ## Physical Dimension Constraints

**IMPORTANT: The case n = 0 is physically meaningless.**

Throughout this module, we work with spatial dimension n ≥ 1. The case n = 0 corresponds
to a 0-dimensional space (a single point), which has no meaningful wave propagation:

- **EuclideanSpace 0** = Fin 0 → ℝ ≅ Unit (the trivial space)
- **Wave equation in 0D**: ∂²u/∂t² = 0 (no spatial derivatives)
- **Solutions**: u(t) = at + b (linear in time, no propagation)
- **Light cone**: |x|² = t² degenerates since Σᵢ xᵢ² = 0 always
- **Green's function**: Undefined (no spatial delta function source)

**Type-theoretic note:** Lean allows `n = 0` in our definitions, but the resulting
objects are degenerate:
- `OnLightCone 0 (x, t) ↔ t > 0 ∧ 0 = t²` ↔ False (for t > 0)
- `InsideLightCone 0 (x, t) ↔ t > 0 ∧ 0 < t²` ↔ t > 0
- `HuygensPrinciple 0` ↔ False (requires n ≥ 3)

**Axiom constraints:** Most axioms explicitly require n ≥ 1 or n ≥ 2 to exclude
the degenerate case. Where no explicit constraint appears, the axiom applies
vacuously or degenerately to n = 0.

**Physical interpretation:** The analysis of wave propagation and Huygens' principle
is only meaningful for n ≥ 1, and the non-trivial cases start at n ≥ 2.
-/

/-! ## Basic Definitions -/

/-- Euclidean space ℝⁿ -/
abbrev EuclideanSpace (n : ℕ) := Fin n → ℝ

/-- Spacetime point (x, t) with x ∈ ℝⁿ and t ∈ ℝ -/
abbrev SpacetimePoint (n : ℕ) := EuclideanSpace n × ℝ

/-! ## Wave Equation Components

We define the wave equation and its fundamental solution.
Full formalization requires Mathlib's distribution theory and Fourier analysis.
-/

/-- A scalar field on n-dimensional spacetime: u(x, t) -/
def ScalarField (n : ℕ) := SpacetimePoint n → ℝ

/-- The wave operator □ = ∂²/∂t² - ∇² applied to a field.
    Returns true if the field satisfies the homogeneous wave equation □u = 0.

    **Definition (in geometric units c = 1):**
    □u = ∂²u/∂t² - ∑ᵢ ∂²u/∂xᵢ² = 0

    **Note:** Full formalization requires Mathlib's differential operators.
    We axiomatize the predicate and constrain it via specification axioms below.

    **Reference:** Courant-Hilbert Vol. II, Ch. VI
-/
axiom SatisfiesWaveEquation : (n : ℕ) → ScalarField n → Prop

/-- **Specification:** The zero field satisfies the wave equation.
    □0 = 0 trivially. -/
axiom waveEquation_zero : ∀ n : ℕ, SatisfiesWaveEquation n (fun _ => 0)

/-- **Specification:** The wave equation is linear.
    If □u = 0 and □v = 0, then □(αu + βv) = 0 for any constants α, β. -/
axiom waveEquation_linear :
  ∀ (n : ℕ) (u v : ScalarField n) (α β : ℝ),
    SatisfiesWaveEquation n u →
    SatisfiesWaveEquation n v →
    SatisfiesWaveEquation n (fun p => α * u p + β * v p)

/-- The Green's function (fundamental solution) of the wave equation.
    G(x,t) satisfies □G = δ(x)δ(t) in the distributional sense.

    **Definition:** The retarded Green's function is the unique distribution satisfying:
    1. □G = δ(x)δ(t)  (inhomogeneous wave equation with point source)
    2. G(x,t) = 0 for t < 0  (causality/retarded condition)
    3. G(x,t) = 0 for |x| > t  (finite propagation speed, c = 1)

    **Explicit forms (in geometric units c = 1):**
    - n = 1: G(x,t) = (1/2)θ(t - |x|)
    - n = 2: G(x,t) = (1/2π) θ(t - |x|) / √(t² - |x|²)
    - n = 3: G(x,t) = (1/4π) δ(t - |x|) / |x|
    - n = 4: G(x,t) ∝ θ(t - |x|) / (t² - |x|²)^{3/2}

    **Key property:** The form of G determines whether Huygens holds:
    - n odd ≥ 3:  G ∝ δ(t - |x|) / |x|^{(n-2)/2}  (on light cone only)
    - n even:     G ∝ θ(t - |x|) / (t² - |x|²)^{...}  (inside light cone)
    - n = 1:      G ∝ θ(t - |x|)  (degenerate odd case)

    **Reference:** Courant-Hilbert Vol. II, Ch. VI; Jackson Ch. 6
-/
axiom GreenFunction : (n : ℕ) → ScalarField n

/-- **Bundled Green's function data with specifications.**
    This structure packages the Green's function with its core mathematical properties,
    ensuring that any Green's function we work with satisfies the fundamental axioms.

    **Bundled specifications:**
    - `symmetric`: G(-x, t) = G(x, t) — spherical symmetry
    - `retarded`: G(x, t) = 0 for t < 0 — causality

    **Why bundle?** This pattern ensures we never use a Green's function without its
    specifications being available. It makes the axiomatization more robust and
    clarifies which properties are definitional vs derived.
-/
structure GreenFunctionSpec (n : ℕ) where
  /-- The Green's function is symmetric in spatial coordinates. -/
  symmetric : ∀ (x : EuclideanSpace n) (t : ℝ),
    GreenFunction n (x, t) = GreenFunction n (fun i => -x i, t)
  /-- The Green's function vanishes for t < 0 (retarded/causal condition). -/
  retarded : ∀ (x : EuclideanSpace n) (t : ℝ),
    t < 0 → GreenFunction n (x, t) = 0

/-- **Axiom:** The Green's function for each dimension satisfies its specifications.
    This single axiom replaces the separate `greenFunction_symmetric` and
    `greenFunction_retarded` axioms, bundling them together. -/
axiom greenFunctionSpec : ∀ n : ℕ, GreenFunctionSpec n

/-- **Derived:** The Green's function is symmetric in spatial coordinates.
    G(-x, t) = G(x, t) — the response to a point source is spherically symmetric. -/
theorem greenFunction_symmetric (n : ℕ) (x : EuclideanSpace n) (t : ℝ) :
    GreenFunction n (x, t) = GreenFunction n (fun i => -x i, t) :=
  (greenFunctionSpec n).symmetric x t

/-- **Derived:** The Green's function vanishes for t < 0.
    This is the retarded (causal) condition: effects cannot precede causes. -/
theorem greenFunction_retarded (n : ℕ) (x : EuclideanSpace n) (t : ℝ) :
    t < 0 → GreenFunction n (x, t) = 0 :=
  (greenFunctionSpec n).retarded x t

/-! ### Geometric Units Convention (c = 1)

Throughout this module, we work in **geometric units** where the wave speed c = 1.

This means:
- The light cone is defined by |x| = t (not |x| = ct)
- The wave equation is ∂²u/∂t² = ∇²u (not ∂²u/∂t² = c²∇²u)
- Time and space have the same units

**Physical interpretation:**
- In SI units: c ≈ 3×10⁸ m/s (speed of light)
- To convert our results to SI units: replace t with ct and ω with ω/c

**Mathematical convenience:**
This simplification doesn't affect the dimension-dependence results.
The odd/even distinction for Huygens' principle is independent of c.

**Reference:** Misner, Thorne & Wheeler (1973), "Gravitation", Box 1.3
-/

/-- The light cone in spacetime: points (x,t) with |x| = t (t > 0).
    The forward light cone is where signals can propagate.

    **Units:** c = 1 (geometric units). The condition |x|² = t² is equivalent
    to |x|² = c²t² in SI units. -/
def OnLightCone (n : ℕ) (p : SpacetimePoint n) : Prop :=
  let (x, t) : EuclideanSpace n × ℝ := p
  t > 0 ∧ (∑ i : Fin n, (x i)^2) = (t)^2

/-- Inside the light cone: points with |x| < t (t > 0).
    If Huygens fails, the Green's function has support here.

    **Units:** c = 1 (geometric units). The condition |x|² < t² is equivalent
    to |x|² < c²t² in SI units, i.e., the signal has arrived. -/
def InsideLightCone (n : ℕ) (p : SpacetimePoint n) : Prop :=
  let (x, t) : EuclideanSpace n × ℝ := p
  t > 0 ∧ (∑ i : Fin n, (x i)^2) < (t)^2

/-- The support of a spacetime field in the distributional sense.

    **Definition (for smooth functions):** supp(f) = cl{p : f(p) ≠ 0}

    **Definition (for distributions):** The support of a distribution T is the
    complement of the largest open set U where T vanishes, i.e., where
    ⟨T, φ⟩ = 0 for all test functions φ with support in U.

    **Key distinction:**
    - For smooth functions: supp(f) is the topological closure of {p : f(p) ≠ 0}
    - For distributions with singularities (δ, δ'): support includes singular points
    - For the Green's function G with δ(t - |x|): supp(G) = {(x,t) : t ≥ 0, |x| = t}

    **Why distributional support matters:**
    The Green's function in odd dimensions n ≥ 3 involves δ(t - |x|), which is
    zero as a function everywhere except on the light cone, but non-zero as a
    distribution ON the light cone. The distributional support correctly captures
    this: supp(G) = light cone.

    **Key property:** The support characterizes where a field has "influence."
    For the Green's function, supp(G) determines which spacetime points
    receive a signal from the source at the origin.

    **Note:** We axiomatize Support rather than defining it directly because
    proper definition requires Mathlib's distribution theory (not yet available).

    **Reference:** Hörmander, "The Analysis of Linear Partial Differential Operators I"
-/
axiom Support : (n : ℕ) → ScalarField n → Set (SpacetimePoint n)

/-- **Bundled Support specifications.**
    This structure packages the Support axiom with its core mathematical properties,
    ensuring consistency with distributional support theory.

    **Bundled specifications:**
    - `mono`: If |f| ≤ |g| pointwise (for smooth f,g), then supp(f) ⊆ supp(g)
    - `zero`: supp(0) = ∅
    - `nonzero_in_support`: f(p) ≠ 0 → p ∈ supp(f) (non-zero points are in support)
    - `closure_property`: Support equals the closure of the non-zero set

    **Why the asymmetric spec?**
    For distributions, p ∈ supp(f) does NOT imply f(p) ≠ 0 because:
    - δ(x) has support {0}, but δ(0) is undefined as a function value
    - The Green's function G has support on the light cone, but G(p) = 0
      for most points p on the light cone when viewed as a function

    The correct specification is:
    - Forward: f(p) ≠ 0 → p ∈ supp(f)  (always true)
    - Backward: p ∈ supp(f) means "f has influence at p" (distributional sense)

    **Why bundle?** This pattern ensures we never use the Support function without
    its definitional properties being available.
-/
structure SupportSpec (n : ℕ) where
  /-- Support is monotonic under absolute value (for smooth functions). -/
  mono : ∀ (f g : ScalarField n),
    (∀ p, |f p| ≤ |g p|) → Support n f ⊆ Support n g
  /-- The support of zero is empty. -/
  zero : Support n (fun _ => 0) = ∅
  /-- Non-zero points are in the support (forward direction only).
      This is the correct formulation for distributional support. -/
  nonzero_in_support : ∀ (f : ScalarField n) (p : SpacetimePoint n),
    f p ≠ 0 → p ∈ Support n f
  /-- Support contains its limit points (closure property).
      For any sequence of points in supp(f) converging to p, we have p ∈ supp(f).
      This is the topological closure condition without requiring IsClosed typeclass. -/
  closure_property : ∀ (f : ScalarField n) (p : SpacetimePoint n),
    (∀ ε > 0, ∃ q ∈ Support n f, ∀ i : Fin n, |p.1 i - q.1 i| < ε ∧ |p.2 - q.2| < ε) →
    p ∈ Support n f

/-- **Axiom:** The Support function for each dimension satisfies its specifications.
    This single axiom replaces separate axioms, bundling them together. -/
axiom supportSpec : ∀ n : ℕ, SupportSpec n

/-- **Derived:** Support is monotonic under absolute value.
    If |f| ≤ |g| pointwise, then supp(f) ⊆ supp(g). -/
theorem support_mono (n : ℕ) (f g : ScalarField n) :
    (∀ p, |f p| ≤ |g p|) → Support n f ⊆ Support n g :=
  (supportSpec n).mono f g

/-- **Derived:** The support of zero is empty.
    supp(0) = ∅ -/
theorem support_zero (n : ℕ) : Support n (fun _ => 0) = ∅ :=
  (supportSpec n).zero

/-- **Derived:** Non-zero function values imply membership in support.
    f(p) ≠ 0 → p ∈ supp(f)

    **Note:** The converse does NOT hold for distributions! -/
theorem nonzero_in_support (n : ℕ) (f : ScalarField n) (p : SpacetimePoint n) :
    f p ≠ 0 → p ∈ Support n f :=
  (supportSpec n).nonzero_in_support f p

/-- **Derived:** Support contains its limit points (closure property). -/
theorem support_closure_property (n : ℕ) (f : ScalarField n) (p : SpacetimePoint n) :
    (∀ ε > 0, ∃ q ∈ Support n f, ∀ i : Fin n, |p.1 i - q.1 i| < ε ∧ |p.2 - q.2| < ε) →
    p ∈ Support n f :=
  (supportSpec n).closure_property f p

/-! ### Specification Axioms for Green's Function

These axioms constrain the abstract `GreenFunction` and `Support` to have
physically and mathematically meaningful properties. They ensure that our
axiomatization is consistent with the actual theory.
-/

/-- **Specification:** The Green's function satisfies the wave equation.
    This is the defining property: □G = δ(x)δ(t).

    **Reference:** Courant-Hilbert Vol. II, §VI.13 -/
axiom greenFunction_satisfies_wave_equation :
  ∀ n : ℕ, n ≥ 1 → SatisfiesWaveEquation n (GreenFunction n)

/-- **Specification:** The Green's function has support in the forward light cone.
    Causality: G(x,t) = 0 for t ≤ 0 and for |x| > ct (outside light cone).

    This is the retarded (causal) Green's function. The advanced Green's function
    would have support in the backward light cone, but we use retarded for physics.

    **Reference:** Jackson, Classical Electrodynamics Ch. 6 -/
axiom greenFunction_causal_support :
  ∀ n : ℕ, ∀ p : SpacetimePoint n,
    p ∈ Support n (GreenFunction n) →
    (OnLightCone n p ∨ InsideLightCone n p)

/-- **Specification:** The Green's function is non-trivial.
    There exists at least one point in its support (it's not identically zero).

    **Reference:** Courant-Hilbert Vol. II, §VI.13 -/
axiom greenFunction_nontrivial :
  ∀ n : ℕ, n ≥ 1 → (Support n (GreenFunction n)).Nonempty

/-- A field has "sharp support" if its support is exactly on the light cone
    (not inside it). This is the key property for Huygens' principle. -/
def HasSharpSupport (n : ℕ) (G : ScalarField n) : Prop :=
  ∀ p : SpacetimePoint n, p ∈ Support n G → OnLightCone n p

/-! ## Huygens' Principle

Huygens' principle states that wave signals propagate sharply:
initial data at t=0 influences the solution only on the light cone,
not inside it. This means no "afterglow" or reverberations.
-/

/-- **Huygens' Principle for dimension n:**
    The Green's function of the wave equation has support only
    on the light cone, not inside it.

    Physically: A sharp pulse at t=0 creates a sharp expanding spherical
    wavefront. After the wavefront passes, the field returns exactly to zero.

    **Mathematical characterization:**
    HuygensPrinciple n ↔ HasSharpSupport n (GreenFunction n)

    **CRITICAL NOTE on n = 1:**
    The 1D case is special and does NOT satisfy Huygens in the strict sense.
    The 1D Green's function is G(x,t) = (1/2c)θ(ct - |x|), which has support
    for |x| ≤ ct (inside the light cone), not just on it.

    Huygens' principle properly holds only for odd n ≥ 3.

    **Reference:** Hadamard (1923), Courant-Hilbert Vol. II
-/
def HuygensPrinciple (n : ℕ) : Prop :=
  n ≥ 3 ∧ Odd n ∧ HasSharpSupport n (GreenFunction n)

/-! ## Hadamard's Theorem

The central theorem connecting wave propagation to dimensionality.
-/

/-! ### Hadamard's Theorem (1923)

Huygens' principle holds if and only if the spatial dimension is odd AND ≥ 3.

**Precise Statement:**
For the wave equation ∂²u/∂t² = c²∇²u in n spatial dimensions:
- n = 1: Green's function G = (1/2c)θ(ct - |x|) has support |x| ≤ ct → NO Huygens
- n = 2: Green's function has logarithmic tail inside light cone → NO Huygens
- n = 3: Green's function G = δ(ct - |x|)/(4πc|x|) has support |x| = ct → YES Huygens
- n = 4: Green's function has power-law tail inside light cone → NO Huygens
- n = 2k+1 (k ≥ 1): Huygens holds (delta-function support)
- n = 2k: Huygens fails (Heaviside function support)

**Proof via Spherical Means (Outline):**

Define the spherical mean: M(r,t) = (1/|S^{n-1}|) ∮_{|x|=r} u(x,t) dS

If □u = 0, then M satisfies the Euler-Poisson-Darboux equation:
  ∂²M/∂t² = ∂²M/∂r² + ((n-1)/r) ∂M/∂r

**Key transformation (Hadamard's descent):**
For n = 2m+1 (odd, m ≥ 1): Let M̃ = r^m M. Then M̃ satisfies:
  ∂²M̃/∂t² = ∂²M̃/∂r²  (pure 1D wave equation!)
Solution: M̃(r,t) = f(r+ct) + g(r-ct) → delta-function propagation.

For n = 2m (even): The transformation involves integrals, leading to:
  M̃(r,t) = ∫ K(r,t,s) M̃₀(s) ds
The kernel K has support inside the light cone → afterglow.

**Why n = 1 fails despite being odd:**
The formula G ∝ (∂/∂t)^m [δ(ct-r)/r^m] requires m ≥ 1, i.e., n ≥ 3.
For n = 1 (m = 0), there's no derivative to sharpen the support.

**Reference:**
- Hadamard, J. (1923). "Lectures on Cauchy's Problem", Ch. II
- Courant, R. & Hilbert, D. (1962). "Methods of Math Physics" Vol. II, §VI.13
- Günther, P. (1988). "Huygens' Principle and Hyperbolic Equations"
-/

/-- **MASTER AXIOM (Hadamard's Characterization):**
    The Green's function has sharp support if and only if n ≥ 3 AND n is odd.

    This single axiom consolidates the dimension-dependent behavior:
    - n = 1: Odd but < 3, so NO sharp support (degenerate case)
    - n = 2: Even, so NO sharp support (tail inside light cone)
    - n = 3: Odd AND ≥ 3, so YES sharp support (delta on light cone)
    - n = 4: Even, so NO sharp support
    - n = 5, 7, 9, ...: Odd AND ≥ 3, so YES sharp support
    - n = 6, 8, 10, ...: Even, so NO sharp support

    **Mathematical basis:**
    The Green's function in n dimensions has the form:
    - n = 2m+1 (odd, m ≥ 1): G ∝ (∂/∂t)^{m-1} [δ(t-r)/r^{m}] — delta support
    - n = 2m (even): G ∝ θ(t-r) / (t²-r²)^{(n-1)/2} — Heaviside support
    - n = 1 (m=0): G = (1/2)θ(t-|x|) — no sharpening mechanism

    **Reference:**
    - Hadamard, J. (1923). "Lectures on Cauchy's Problem", Ch. II
    - Courant, R. & Hilbert, D. (1962). "Methods of Math Physics" Vol. II, §VI.13

    **Why a single axiom?**
    1. Eliminates redundancy (three axioms → one)
    2. Makes the characterization self-documenting
    3. Both directions are available via the ↔
    4. Prevents potential inconsistency between separate axioms
-/
axiom greenFunction_sharp_support_iff :
  ∀ n : ℕ, HasSharpSupport n (GreenFunction n) ↔ (n ≥ 3 ∧ Odd n)

/-- **Derived (Hadamard forward):** For odd n ≥ 3, the Green's function has sharp support. -/
theorem greenFunction_sharp_support_odd (n : ℕ) (hn3 : n ≥ 3) (hodd : Odd n) :
    HasSharpSupport n (GreenFunction n) :=
  (greenFunction_sharp_support_iff n).mpr ⟨hn3, hodd⟩

/-- **Derived (Hadamard backward for even):** For even n, the Green's function does NOT have sharp support.

    **Note:** The hypothesis `n ≥ 2` is retained for API consistency and documentation
    (even n ≥ 2 are the physically meaningful even dimensions), but is not used in
    the proof since the Even/Odd contradiction is sufficient. The n = 0 case is
    also even and satisfies this theorem. -/
theorem greenFunction_not_sharp_even (n : ℕ) (_hn2 : n ≥ 2) (heven : Even n) :
    ¬HasSharpSupport n (GreenFunction n) := by
  intro hsharp
  have ⟨_, hodd⟩ := (greenFunction_sharp_support_iff n).mp hsharp
  -- Even and Odd are contradictory
  rcases hodd with ⟨k, hk⟩
  rcases heven with ⟨m, hm⟩
  omega

/-- **Derived (1D special case):** The 1D Green's function does NOT have sharp support.
    G₁(x,t) = (1/2)θ(t - |x|) is supported on |x| ≤ t, not just |x| = t. -/
theorem greenFunction_1D_not_sharp : ¬HasSharpSupport 1 (GreenFunction 1) := by
  intro hsharp
  have ⟨hn3, _⟩ := (greenFunction_sharp_support_iff 1).mp hsharp
  omega

/-- **Derived (2D special case):** The 2D Green's function does NOT have sharp support.
    G₂(x,t) = (1/2π) θ(t - |x|) / √(t² - |x|²) is supported on |x| ≤ t. -/
theorem greenFunction_2D_not_sharp : ¬HasSharpSupport 2 (GreenFunction 2) := by
  intro hsharp
  have ⟨_, hodd⟩ := (greenFunction_sharp_support_iff 2).mp hsharp
  rcases hodd with ⟨k, hk⟩
  omega

/-- **Theorem (Hadamard, 1923):**
    Huygens' principle holds if and only if n is odd AND n ≥ 3.
-/
theorem huygens_iff_odd_geq_3 (n : ℕ) (hn : n ≥ 1) :
    HuygensPrinciple n ↔ (Odd n ∧ n ≥ 3) := by
  unfold HuygensPrinciple
  constructor
  · -- Forward: Huygens implies odd and ≥ 3
    intro ⟨hn3, hodd, _⟩
    exact ⟨hodd, hn3⟩
  · -- Backward: odd and ≥ 3 implies Huygens
    intro ⟨hodd, hn3⟩
    exact ⟨hn3, hodd, greenFunction_sharp_support_odd n hn3 hodd⟩

/-! ## Explicit Green's Functions

For reference, we state the explicit forms of Green's functions.
These motivate the odd/even distinction.
-/

/-- **Green's function structure in 1D (n=1, odd but < 3):**

    G(x,t) = (1/2c) θ(ct - |x|)

    **IMPORTANT:** Despite n=1 being odd, Huygens does NOT hold!
    The Heaviside θ function means support is |x| ≤ ct (inside light cone),
    not just |x| = ct (on light cone).

    **Physical interpretation:** In 1D, a pulse at x=0, t=0 creates a
    rectangular wave that fills the region |x| < ct, not a sharp front.

    **Mathematical reason:** The Hadamard descent formula
    G ∝ (∂/∂t)^m [δ(ct-r)/r^m] requires m ≥ 1 (i.e., n ≥ 3).
    For n=1 (m=0), there's no time derivative to sharpen the support.

    **Reference:** Courant-Hilbert Vol. II, §VI.13
-/
theorem green_function_1D_no_huygens : ¬HuygensPrinciple 1 := by
  intro ⟨hn3, _, _⟩
  -- HuygensPrinciple requires n ≥ 3, but n = 1
  omega

/-- **Green's function structure in 3D (n=3, odd ≥ 3):**

    G(x,t) = δ(ct - |x|) / (4πc|x|)

    The delta function ensures support is EXACTLY on |x| = ct.
    This is why we can have sharp sounds and clear images.

    **Derivation via spherical means:**
    For n=3 (m=1), Hadamard's formula gives:
    G(r,t) ∝ (∂/∂t)^1 [δ(ct-r)/r^1] = δ(ct-r)/r + (ct)δ'(ct-r)/r

    After regularization, this gives the retarded Green's function
    with support exactly on the forward light cone |x| = ct, t > 0.

    **Physical consequence:**
    - Light flashes arrive sharply, then darkness returns immediately
    - Sound pulses are crisp without reverberations
    - Communication signals don't smear over time

    **Reference:** Jackson, Classical Electrodynamics Ch. 6
-/
theorem green_function_3D_huygens : HuygensPrinciple 3 := by
  unfold HuygensPrinciple
  refine ⟨by norm_num, ⟨1, rfl⟩, ?_⟩
  exact greenFunction_sharp_support_odd 3 (by norm_num) ⟨1, rfl⟩

/-- **Green's function structure in 5D (n=5, odd ≥ 3):**

    G(x,t) ∝ δ''(t - |x|) / |x|³

    The second derivative of the delta function still has support
    exactly on |x| = t. This is the next odd dimension after 3D.

    **Mathematical structure (Hadamard descent):**
    For n = 5 = 2·2 + 1 (m = 2), the formula is:
    G ∝ (∂/∂t)² [δ(t - r)/r²]

    Each time derivative sharpens the wavefront while adding powers of 1/r.

    **Physical consequence:** If our space were 5D, Huygens would still hold.
    Light signals would arrive sharply without afterglow, though the
    intensity would fall off faster (as 1/r³ instead of 1/r in 3D).

    **Reference:** Courant-Hilbert Vol. II, §VI.13
-/
theorem green_function_5D_huygens : HuygensPrinciple 5 := by
  unfold HuygensPrinciple
  refine ⟨by decide, ⟨2, rfl⟩, ?_⟩
  exact greenFunction_sharp_support_odd 5 (by decide) ⟨2, rfl⟩

/-- **Green's function structure in 2D (n=2, even):**

    G(x,t) = θ(ct - |x|) / (2πc√(c²t² - |x|²))

    The Heaviside θ function means support extends INSIDE the light cone.
    A 2D pulse creates an afterglow that fades as 1/√(t² - |x|²/c²).

    **Mathematical structure:**
    The 2D Green's function can be obtained from the 3D one via
    "method of descent" (integrating over the third coordinate):
    G₂D(x,y,t) = ∫ G₃D(x,y,z,t) dz

    This integration "smears" the delta function into a Heaviside function.

    **Physical consequence:** If we lived in Flatland (2D), after a light
    flashes, we'd see a ring expand AND a dim glow persisting inside it.
    The glow fades as 1/√(t² - r²/c²), never quite reaching zero.

    **Reference:** Morse & Feshbach, Methods of Theoretical Physics Vol. I
-/
theorem green_function_2D_no_huygens : ¬HuygensPrinciple 2 := by
  intro ⟨hn3, hodd, _⟩
  -- HuygensPrinciple requires n ≥ 3, but n = 2
  omega

/-- **Green's function structure in 4D (n=4, even):**

    G(x,t) ∝ θ(ct - |x|) / (c²t² - |x|²)^{3/2}

    Similar to 2D, the Green's function has support inside the light cone.
    The power-law decay (3/2 instead of 1/2) means faster fading but still
    non-zero inside the light cone.

    **Mathematical reason:** For n=4 (even), the descent formula gives:
    G₄D ∝ ∫₁^{ct} G₅D dr = ∫₁^{ct} δ''(ct-r)/r² dr

    The integration converts delta functions to Heaviside functions.

    **Physical consequence:** If our space were 4D, radio signals would
    be followed by fading echoes, making precise communication difficult.
    The tail would decay as 1/(t² - r²/c²)^{3/2}.
-/
theorem green_function_4D_no_huygens : ¬HuygensPrinciple 4 := by
  intro ⟨hn3, hodd, _⟩
  -- HuygensPrinciple requires Odd n, but 4 is even
  rcases hodd with ⟨k, hk⟩
  omega

/-! ## Connection to Physical Axioms

These theorems provide the mathematical foundation for the Huygens-related
axioms in PhysicalAxioms.lean.
-/

/-- **Canonical Hadamard's Theorem Export:**

    HuygensPrinciple n ↔ (Odd n ∧ n ≥ 3)

    This is THE single canonical theorem for Huygens' principle characterization.
    All downstream code should use this theorem directly.

    **Usage patterns:**
    - Forward (extract Odd): `(huygens_iff_odd n hn).mp h` gives `⟨hodd, hge3⟩`
    - Forward (just Odd): Use `hadamard_implies_odd` from PhysicalAxioms.lean
    - Backward: `(huygens_iff_odd n hn).mpr ⟨hodd, hge3⟩`

    **Why no simplified wrapper?**
    A wrapper like `HuygensPrinciple n ↔ Odd n` (with n ≥ 3 precondition) would
    hide the critical n ≥ 3 constraint. Making it explicit in the ↔ statement
    ensures type-safety and self-documentation.
-/
theorem huygens_iff_odd (n : ℕ) (hn : n ≥ 1) :
    HuygensPrinciple n ↔ (Odd n ∧ n ≥ 3) :=
  huygens_iff_odd_geq_3 n hn

/-- Export: 3D satisfies Huygens (key for D=4 spacetime) -/
theorem huygens_in_3D : HuygensPrinciple 3 :=
  green_function_3D_huygens

/-- Export: Even dimensions fail Huygens (need odd AND ≥ 3)

    **Note:** The hypothesis `n ≥ 1` is not used in the proof because the
    Even/Odd contradiction is sufficient. However, we retain it for API
    consistency with other dimension-dependent theorems and to document
    that we're considering physically meaningful dimensions (n ≥ 1).
    The n = 0 case is physically meaningless but also satisfies this
    theorem since 0 is even.
-/
theorem even_fails_huygens (n : ℕ) (_hn : n ≥ 1) (heven : Even n) :
    ¬HuygensPrinciple n := by
  intro ⟨_, hodd, _⟩
  -- Even and Odd are contradictory
  rcases hodd with ⟨k, hk⟩
  rcases heven with ⟨m, hm⟩
  omega

/-- **Physical significance theorem:**

    Among dimensions supporting stable physics (n ∈ {2, 3}),
    only n = 3 allows clean wave propagation without echoes.

    This is one reason why observers can only exist in 3D space.
-/
theorem observer_requires_huygens :
    ∀ n ∈ ({2, 3} : Set ℕ), HuygensPrinciple n ↔ n = 3 := by
  intro n hn
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  constructor
  · intro hhuy
    rcases hn with rfl | rfl
    · -- n = 2: Even, can't satisfy Huygens
      exfalso
      exact green_function_2D_no_huygens hhuy
    · -- n = 3: Already correct
      rfl
  · intro heq
    subst heq
    exact green_function_3D_huygens

/-! ## Mathematical Details: Spherical Means Method

The proof of Hadamard's theorem uses the **method of spherical means**.
This section provides the mathematical infrastructure connecting the
n-dimensional wave equation to dimension-dependent behavior.

### Overview of the Method

1. **Define the spherical mean** M_u(r,t) as the average of u over a sphere of radius r
2. **Derive the EPD equation:** If □u = 0, then M satisfies a 1+1 dimensional PDE
3. **Transform the EPD equation:** The transformation M̃ = r^{(n-1)/2} M yields:
   - For odd n: A pure 1D wave equation (d'Alembert form)
   - For even n: An equation involving integrals (Volterra form)
4. **Conclude:** The d'Alembert solutions have delta-function support (Huygens);
   the Volterra solutions have support inside the light cone (tails).

### References

- Courant, R. & Hilbert, D. (1962). "Methods of Mathematical Physics" Vol. II, §V.3, §VI.13
- John, F. (1955). "Plane Waves and Spherical Means" — Chapter 2
- Hadamard, J. (1923). "Lectures on Cauchy's Problem" — Chapter II
-/

/-- The spherical mean of a scalar field u at radius r and time t.

    **Definition:**
    M_u(r,t) = (1/|S^{n-1}|) ∮_{|x|=r} u(x,t) dS

    where |S^{n-1}| = 2π^{n/2}/Γ(n/2) is the surface area of the unit (n-1)-sphere.

    **Key property:** The spherical mean converts the n-dimensional wave equation
    into a 1+1 dimensional PDE (the Euler-Poisson-Darboux equation).

    **Physical interpretation:** M_u(r,t) represents the average field value
    at distance r from the origin at time t. For a point source at the origin,
    M captures how the wavefront propagates radially.
-/
axiom SphericalMean : (n : ℕ) → ScalarField n → (ℝ → ℝ → ℝ)

/-- **Bundled Spherical Mean specifications.**
    This structure packages the spherical mean with its core mathematical properties.

    **Bundled specifications:**
    - `symmetry`: M_u(r,t) is symmetric in r (even function of r)
    - `linearity`: M_{αu + βv}(r,t) = α M_u(r,t) + β M_v(r,t)
    - `initial_value`: M_u(0,t) = u(0,t) (limit as r → 0)
    - `smoothness`: M_u is smooth in (r,t) for r > 0

    **Why substantive specs?**
    The spherical mean has specific mathematical structure that constrains its
    behavior. These properties are used in deriving the EPD equation and
    proving Huygens' principle.

    **Reference:** John (1955), "Plane Waves and Spherical Means" Ch. 2
-/
structure SphericalMeanSpec (n : ℕ) where
  /-- Spherical mean is symmetric in radius (even function).
      M(-r, t) = M(r, t) for all r, t.
      This follows from the definition as an integral over the sphere |x| = |r|. -/
  symmetry : ∀ (u : ScalarField n) (r t : ℝ),
    SphericalMean n u r t = SphericalMean n u (-r) t
  /-- Spherical mean is linear in the field.
      M_{αu + βv} = α M_u + β M_v.
      This follows from linearity of integration. -/
  linearity : ∀ (u v : ScalarField n) (α β r t : ℝ),
    SphericalMean n (fun p => α * u p + β * v p) r t =
    α * SphericalMean n u r t + β * SphericalMean n v r t
  /-- Spherical mean of constant field equals the constant.
      If u(x,t) = c for all x, then M_u(r,t) = c. -/
  constant_field : ∀ (c r t : ℝ),
    SphericalMean n (fun _ => c) r t = c
  /-- Spherical mean is bounded by the sup norm of the field.
      |M_u(r,t)| ≤ sup_{|x|=r} |u(x,t)|.
      This follows from the mean being an average. -/
  bounded : ∀ (u : ScalarField n) (r t : ℝ) (B : ℝ),
    r > 0 → (∀ x : EuclideanSpace n, (∑ i, (x i)^2) = r^2 → |u (x, t)| ≤ B) →
    |SphericalMean n u r t| ≤ B

/-- **Axiom:** The spherical mean for each dimension satisfies its specifications. -/
axiom sphericalMeanSpec : ∀ n : ℕ, SphericalMeanSpec n

/-- **Derived:** Spherical mean is symmetric in radius. -/
theorem sphericalMean_symmetry (n : ℕ) (u : ScalarField n) (r t : ℝ) :
    SphericalMean n u r t = SphericalMean n u (-r) t :=
  (sphericalMeanSpec n).symmetry u r t

/-- **Derived:** Spherical mean is linear. -/
theorem sphericalMean_linear (n : ℕ) (u v : ScalarField n) (α β r t : ℝ) :
    SphericalMean n (fun p => α * u p + β * v p) r t =
    α * SphericalMean n u r t + β * SphericalMean n v r t :=
  (sphericalMeanSpec n).linearity u v α β r t

/-- **Derived:** Spherical mean of constant is constant. -/
theorem sphericalMean_constant (n : ℕ) (c r t : ℝ) :
    SphericalMean n (fun _ => c) r t = c :=
  (sphericalMeanSpec n).constant_field c r t

/-- **Derived:** Spherical mean of zero is zero. -/
theorem sphericalMean_zero (n : ℕ) (r t : ℝ) :
    SphericalMean n (fun _ => 0) r t = 0 :=
  sphericalMean_constant n 0 r t

/-- **Specification:** The spherical mean of the Green's function inherits
    the support properties from the Green's function.

    **Full characterization (both directions):**
    If G has support only on the light cone (|x| = t), then M_G(r,t) ≠ 0 ↔ r = t.

    **Forward (r = t → nonzero):**
    The wavefront at distance r arrives at time t = r (in units c = 1).
    Since G is non-trivial, the spherical mean captures this arriving wave.

    **Backward (nonzero → r = t):**
    If M_G(r,t) ≠ 0, then there must be support on the sphere |x| = r at time t.
    Since G has support only on |x| = t, we need r = t.

    **Mathematical derivation:**
    For odd n ≥ 3, the Green's function has the form:
      G(x,t) = c_n · δ^{(m-1)}(t - |x|) / |x|^{m}  where n = 2m + 1

    The spherical mean at radius r integrates over |x| = r:
      M_G(r,t) = (1/|S^{n-1}|) ∮_{|x|=r} G(x,t) dS

    Since G involves δ(t - |x|), the integral is non-zero only when r = t.

    **Reference:** John (1955), "Plane Waves and Spherical Means" Ch. 2
-/
axiom sphericalMean_green_support :
  ∀ (n : ℕ),
    n ≥ 3 → Odd n →
    ∀ (r t : ℝ), r > 0 → t > 0 →
      SphericalMean n (GreenFunction n) r t ≠ 0 ↔ r = t

/-! ### The Euler-Poisson-Darboux Equation

The **EPD equation** is a 1+1 dimensional wave equation with a "friction" term:

  ∂²M/∂t² = ∂²M/∂r² + ((n-1)/r) ∂M/∂r

This can be rewritten as:

  ∂²M/∂t² = (1/r^{n-1}) ∂/∂r (r^{n-1} ∂M/∂r)

The coefficient (n-1)/r encodes the geometric spreading in n dimensions.

**Key insight:** The EPD equation can be transformed into simpler forms:
- For odd n = 2m+1: The substitution M̃ = r^m M yields ∂²M̃/∂t² = ∂²M̃/∂r²
- For even n = 2m: The transformation involves integrals (Volterra equation)
-/

/-- The EPD equation relates the spherical mean M to a 1+1 dimensional wave-like PDE.

    **Statement (Courant-Hilbert Vol. II, §V.3):**
    If u : ℝⁿ × ℝ → ℝ satisfies the n-dimensional wave equation □u = 0,
    then its spherical mean M(r,t) = M_u(r,t) satisfies:

      ∂²M/∂t² = ∂²M/∂r² + ((n-1)/r) ∂M/∂r

    **Proof outline:**
    1. Apply the Laplacian in spherical coordinates: ∇²u = ∂²u/∂r² + ((n-1)/r)∂u/∂r + (1/r²)∇²_S u
    2. Average over the sphere; the angular Laplacian ∇²_S u averages to zero
    3. The resulting equation for the average is the EPD equation

    **Key properties encoded:**
    - The EPD is a well-posed initial value problem
    - Domain of dependence: M(r₀,t₀) depends only on M(·, 0) in [max(0, r₀-t₀), r₀+t₀]
    - Finite propagation speed (= 1 in geometric units)

    **IMPORTANT: Domain constraint for spherical means:**
    The spherical mean M(r,t) is only defined for r ≥ 0 (radius is non-negative).
    The domain of dependence [r₀-t₀, r₀+t₀] must be intersected with [0, ∞).
    When r₀ < t₀, the effective domain is [0, r₀+t₀], not [r₀-t₀, r₀+t₀].

    **Reference:** Courant-Hilbert Vol. II, §V.3; John (1955) Ch. 2
-/
axiom EPD_equation :
  ∀ (n : ℕ) (u : ScalarField n),
    n ≥ 1 →
    SatisfiesWaveEquation n u →
    -- The spherical mean M = SphericalMean n u satisfies the EPD equation
    let M := SphericalMean n u
    -- Key property: Finite propagation speed (domain of dependence)
    -- M(r₀,t₀) for t₀ > 0 depends only on M(·, 0) in [max(0, r₀-t₀), r₀+t₀]
    -- CORRECTED: r must be positive (spherical mean is defined for r > 0)
    (∀ r₀ t₀ : ℝ, r₀ > 0 → t₀ > 0 →
      -- If M vanishes on the initial data in the domain of dependence
      -- Note: we require r > 0 since spherical mean is only meaningful for positive radius
      (∀ r, r > 0 → r ≥ max 0 (r₀ - t₀) → r ≤ r₀ + t₀ → M r 0 = 0) →
      -- Then M vanishes at (r₀, t₀)
      M r₀ t₀ = 0)

/-! ### Dimension-Dependent Transformation

The crucial step in Hadamard's proof is transforming the EPD equation.
The transformation depends on whether n is odd or even.

**For odd n = 2m + 1 (m ≥ 1):**
Define M̃(r,t) = r^m · M(r,t). Then M̃ satisfies the pure 1D wave equation:
  ∂²M̃/∂t² = ∂²M̃/∂r²

This has the d'Alembert solution M̃(r,t) = f(r+t) + g(r-t), which gives
delta-function propagation: a δ-source at t=0 produces δ-functions at t>0.

**For even n = 2m:**
The transformation involves integrals (method of descent), leading to a
Volterra integral equation. Solutions have support inside the light cone
(not just on it), creating the "tail" or "afterglow" effect.

**Why n = 1 fails:**
For n = 1 (m = 0), the transformation M̃ = r^0 · M = M is trivial.
The 1D wave equation ∂²u/∂t² = ∂²u/∂x² has fundamental solution
G(x,t) = (1/2)θ(t - |x|), which has support for |x| ≤ t, not just |x| = t.
There's no radial spreading to sharpen the wavefront.
-/

/-- **Transformation for odd dimensions n = 2m + 1 (m ≥ 1):**

    The substitution M̃ = r^m · M transforms the EPD equation into the
    pure 1D wave equation ∂²M̃/∂t² = ∂²M̃/∂r².

    **Mathematical derivation (Courant-Hilbert Vol. II, §VI.13):**

    Starting from: ∂²M/∂t² = ∂²M/∂r² + ((n-1)/r) ∂M/∂r

    With n = 2m + 1 and M̃ = r^m M:

    1. ∂M/∂r = (1/r^m)[∂M̃/∂r - (m/r)M̃]
    2. ∂²M/∂r² = (1/r^m)[∂²M̃/∂r² - (2m/r)∂M̃/∂r + m(m+1)/r² M̃]
    3. Substituting into EPD with (n-1)/r = 2m/r:
       ∂²M̃/∂t² = ∂²M̃/∂r²  (the cross terms cancel!)

    **Consequence:** Solutions are of d'Alembert form f(r±t),
    giving delta-function support on the light cone r = t.

    **Reference:** Courant-Hilbert Vol. II, §VI.13; John (1955) Theorem 2.1
-/
axiom EPD_transformation_odd_dims :
  ∀ (m : ℕ),
    m ≥ 1 →
    let n : ℕ := 2 * m + 1
    -- For odd n ≥ 3, the transformed EPD has d'Alembert form
    -- This means solutions propagate as f(r+t) + g(r-t)
    ∀ (u : ScalarField n),
      SatisfiesWaveEquation n u →
      -- The transformed spherical mean satisfies the 1D wave equation
      -- which has delta-function fundamental solutions
      ∃ (Mtilde : ℝ → ℝ → ℝ),
        -- Mtilde = r^m · SphericalMean n u
        (∀ r t, r > 0 → Mtilde r t = r^m * SphericalMean n u r t) ∧
        -- d'Alembert form: Mtilde(r,t) = f(r+t) + g(r-t) for some functions f, g
        -- This is encoded as: there exist f, g such that Mtilde factors this way
        (∃ (f g : ℝ → ℝ), ∀ r t, r > 0 → Mtilde r t = f (r + t) + g (r - t))

/-- **Transformation for even dimensions n = 2m:**

    The EPD equation cannot be reduced to the 1D wave equation.
    Instead, it transforms into a Volterra integral equation.

    **Mathematical derivation (Method of Descent):**

    For even n = 2m, the solution in n dimensions is obtained by
    integrating the (n+1)-dimensional solution over one variable:

    G_n(x,t) = ∫_{-∞}^{∞} G_{n+1}(x, x_{n+1}, t) dx_{n+1}

    Since n+1 is odd, G_{n+1} has delta-function support on |x| = t.
    But the integral over x_{n+1} "smears" this into support for |x| ≤ t.

    **Explicit form for n = 2:**
    G_2(x,t) = (1/2π) θ(t - |x|) / √(t² - |x|²)

    This has support for |x| ≤ t (inside light cone), not just |x| = t.

    **Volterra integral representation:**
    For even n = 2m, the spherical mean M(r,t) of any solution u satisfies
    a Volterra integral equation of the form:

    M(r,t) = ∫₀ᵗ K(r,t,s) F(r,s) ds + boundary terms

    where K is a kernel involving the initial data. The integral form
    inherently spreads support inside the light cone.

    **Key consequence:** The spherical mean at (r,t) depends on values
    in the entire domain of dependence, not just on the light cone.
    This is encoded by showing that for any solution, M(r,t) can be
    non-zero even when r ≠ t (inside the light cone).

    **Reference:** Courant-Hilbert Vol. II, §VI.13; Hadamard (1923) Ch. II
-/
axiom EPD_transformation_even_dims :
  ∀ (m : ℕ),
    m ≥ 1 →
    let n : ℕ := 2 * m
    -- For even n ≥ 2, the EPD involves integrals (Volterra form)
    ∀ (u : ScalarField n),
      SatisfiesWaveEquation n u →
      let M := SphericalMean n u
      -- The Volterra structure: M depends on initial data via integral kernel
      -- Key property: M(r,t) can be non-zero inside the light cone (r < t)
      -- This is expressed as: there exists a kernel K such that:
      (∃ (K : ℝ → ℝ → ℝ → ℝ),
        -- Property 1: The kernel K(r,t,s) satisfies causality: K = 0 for s > t
        (∀ r t s, s > t → K r t s = 0) ∧
        -- Property 2: The kernel is non-trivial for interior points (r < t)
        -- This is what creates the "tail" effect in even dimensions
        (∀ r t, r > 0 → t > r →
          -- There exists s ∈ (0, t) where K contributes
          ∃ s, 0 < s ∧ s < t ∧ K r t s ≠ 0) ∧
        -- Property 3: The kernel relates to the spherical mean structure
        -- For interior points, M depends on initial data through K
        (∀ r t, r > 0 → t > r → t > 0 →
          -- If initial data vanishes, check if M can still be non-zero
          -- This encodes the Volterra integral structure without explicit ∫
          (M r 0 = 0 → ∃ s, 0 < s ∧ s < t ∧ K r t s * M r s ≠ 0) ∨ M r t = 0))

/-- **The 1D special case (n = 1):**

    Despite n = 1 being odd, Huygens' principle fails because:
    1. The EPD transformation M̃ = r^m M with m = 0 is trivial (M̃ = M)
    2. There's no radial spreading mechanism in 1D
    3. The fundamental solution is G(x,t) = (1/2)θ(t - |x|)

    **Physical interpretation:**
    In 1D, a pulse at x = 0 creates two waves traveling in opposite directions.
    At any later time t, the field is non-zero for |x| ≤ t (the waves have passed).
    There's no "wavefront" in the sense of a localized disturbance.

    **Reference:** Courant-Hilbert Vol. II, §VI.13
-/
theorem EPD_1D_degenerate :
    let n : ℕ := 1
    -- n = 1 = 2*0 + 1 is odd, but m = 0 < 1 means the transformation is trivial
    -- The Green's function has support inside the light cone
    ¬HasSharpSupport n (GreenFunction n) :=
  greenFunction_1D_not_sharp

/-! ## Edge Case: n = 0 (Degenerate Dimension)

The following theorems explicitly document the behavior of our definitions
for the physically meaningless case n = 0.
-/

/-- **n = 0 is trivially excluded from Huygens' principle.**
    HuygensPrinciple requires n ≥ 3, so n = 0 automatically fails. -/
theorem huygens_fails_0D : ¬HuygensPrinciple 0 := by
  intro ⟨hn3, _, _⟩
  omega

/-- **The light cone in 0D is empty for t > 0.**
    OnLightCone 0 (x, t) requires t > 0 and Σᵢ xᵢ² = t².
    But Σᵢ over Fin 0 is 0, so 0 = t² implies t = 0, contradicting t > 0. -/
theorem lightCone_0D_empty : ∀ (p : SpacetimePoint 0), p.2 > 0 → ¬OnLightCone 0 p := by
  intro ⟨x, t⟩ ht hLC
  unfold OnLightCone at hLC
  simp only at hLC
  obtain ⟨_, heq⟩ := hLC
  -- Σ i : Fin 0, (x i)² = 0, but we need this to equal t² with t > 0
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at heq
  -- heq : 0 = t², but t > 0 means t² > 0
  have htsq : t^2 > 0 := sq_pos_of_pos ht
  -- heq says 0 = t^2, so t^2 = 0
  have : t^2 = 0 := heq.symm
  rw [this] at htsq
  exact lt_irrefl 0 htsq

/-- **The interior of the light cone in 0D is all of t > 0.**
    InsideLightCone 0 (x, t) ↔ t > 0 ∧ 0 < t², which simplifies to t > 0. -/
theorem insideLightCone_0D_char (p : SpacetimePoint 0) :
    InsideLightCone 0 p ↔ p.2 > 0 := by
  unfold InsideLightCone
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  constructor
  · intro ⟨ht, _⟩; exact ht
  · intro ht
    constructor
    · exact ht
    · exact sq_pos_of_pos ht

/-- **Summary: n = 0 behavior.**
    This theorem consolidates the 0D edge case documentation:
    - Huygens fails (n < 3)
    - Light cone is empty (no points with |x| = t for t > 0)
    - All positive-time points are "inside" the light cone
-/
theorem dimension_0_degenerate :
    ¬HuygensPrinciple 0 ∧
    (∀ p : SpacetimePoint 0, p.2 > 0 → ¬OnLightCone 0 p) ∧
    (∀ p : SpacetimePoint 0, InsideLightCone 0 p ↔ p.2 > 0) :=
  ⟨huygens_fails_0D, lightCone_0D_empty, insideLightCone_0D_char⟩

end ChiralGeometrogenesis.PureMath.Analysis
