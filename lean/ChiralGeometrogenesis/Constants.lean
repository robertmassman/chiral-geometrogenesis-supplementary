/-
  Constants.lean — Re-export hub

  Imports all sub-modules from Constants/ so existing
  `import ChiralGeometrogenesis.Constants` continues to work.

  The monolithic file has been split into domain-specific sub-files:
  - Core.lean: Fundamental particle physics, QCD beta function, SU(3), mathematical constants
  - Geometry.lean: Stella octangula geometry, FCC honeycomb, Wilson fermion parameters
  - Gravity.lean: Fundamental physical constants (SI), Planck units, gravitational structure
  - QCD.lean: QCD experimental values, derived constants, holographic/lattice, Gasser-Leutwyler
  - Electroweak.lean: Electroweak constants, gauge bosons, LHC, oblique parameters, EM constants
  - Cosmology.lean: Dark matter, cosmological densities, precision predictions, anthropic bounds
  - Neutrino.lean: Neutrino mixing, PMNS parameters, mass squared differences
  - GaugeUnification.lean: Gauge unification, cascade β-functions, heterotic string theory
  - MassGap.lean: QCD Casimir factors, Yang-Mills mass gap, glueball predictions, lattice bounds
  - Specialized.lean: Edge-mode decomposition, W-soliton existence/properties
-/
import ChiralGeometrogenesis.Constants.Core
import ChiralGeometrogenesis.Constants.Geometry
import ChiralGeometrogenesis.Constants.Gravity
import ChiralGeometrogenesis.Constants.QCD
import ChiralGeometrogenesis.Constants.Electroweak
import ChiralGeometrogenesis.Constants.Cosmology
import ChiralGeometrogenesis.Constants.Neutrino
import ChiralGeometrogenesis.Constants.GaugeUnification
import ChiralGeometrogenesis.Constants.MassGap
import ChiralGeometrogenesis.Constants.Specialized
