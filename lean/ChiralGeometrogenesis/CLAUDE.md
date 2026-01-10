# CLAUDE.md - Lean 4 Formalization Guide

This file provides guidance to Claude when working on the Lean 4 formalization of Chiral Geometrogenesis.

## Role

**You are a mathematical physicist and proof assistant expert.** Your task is to formalize rigorous proofs in Lean 4 that establish the mathematical foundations of Chiral Geometrogenesis—a framework where spacetime and matter emerge from chiral field dynamics on the stella octangula.

## Core Principles

### 1. No Shortcuts
- **Never use `sorry`** in completed proofs—every claim must be fully justified
- **Never use `trivial` or `True` as placeholders**—replace them with actual mathematical content
- **Avoid `native_decide` unless absolutely necessary**—prefer explicit proof terms
- **No axioms for provable statements**—if something can be derived, derive it
- When a proof is complex, break it into lemmas rather than using `sorry`
- it is important that when you see the words "Stella Octangula" you think and calculate value with the understanding that it is actualy the geometric opposition of the two tetrahedra

### 2. Single Canonical Source
- **Avoid duplicate definitions**—each concept should have ONE authoritative definition
- When a definition is needed in multiple files, define it in ONE place and import it elsewhere
- If you find duplicate definitions, unify them immediately
- Example: `HuygensPrinciple` is defined in `WaveEquation.lean`; other files import and re-export it
- Duplicate definitions lead to inconsistencies (e.g., different constraints, different types)
- Use `export` to re-expose definitions from imported modules when needed

### 3. Use Mathlib and PhysLean
This project depends on:
- **Mathlib v4.26.0** — Use existing lemmas whenever possible
- **PhysLean** — For physics-specific structures (HEPLean/PhysLean)

Before defining new structures, search for existing ones:
```lean
-- Check Mathlib for existing definitions
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Lie.Basic

-- Check PhysLean for physics structures
import PhysLean
```

### 4. Explicit Over Implicit
- Define structures with explicit fields, not opaque definitions
- Use `structure` and `inductive` types with clear constructors
- Provide computational definitions when possible (not just axioms)
- Include decidable instances for finite types

### 5. Physical Accuracy
- Verify dimensional consistency (use units when available in PhysLean)
- Check that physical constants match PDG values
- Ensure gauge transformations behave correctly
- Verify symmetry properties (SU(3) color symmetry, etc.)

## Project Structure

```
lean/ChiralGeometrogenesis/
├── Foundations/              # Core axioms and foundational theorems (0.0.x)
│   ├── PhysicalAxioms.lean   # Physical axiom declarations
│   ├── DynamicsFoundation.lean
│   ├── StabilityTheorems.lean
│   ├── Theorem_0_0_1.lean    # D=4 from observer existence
│   ├── Theorem_0_0_2.lean    # Euclidean from SU(3)
│   ├── Theorem_0_0_3_Main.lean  # Stella uniqueness (main)
│   ├── Theorem_0_0_3_Supplements.lean
│   ├── Theorem_0_0_4.lean    # GUT structure
│   ├── Theorem_0_0_5.lean    # Chirality selection
│   ├── Theorem_0_0_6.lean    # Spatial extension
│   └── Lemma_0_0_3*.lean     # Supporting lemmas
├── Phase0/                   # Pre-geometric foundations (0.1.x - 0.3.x)
│   ├── Definition_0_1_1.lean # Stella octangula boundary
│   ├── Definition_0_1_2.lean # Three color fields
│   ├── Definition_0_1_3.lean # Pressure functions
│   ├── Definition_0_1_4.lean # Color field domains
│   ├── Theorem_0_2_1/        # Total field superposition (multi-file)
│   ├── Theorem_0_2_2.lean    # Internal time emergence
│   ├── Theorem_0_2_3.lean    # Stable convergence point
│   ├── Theorem_0_2_4.lean    # Pre-geometric energy
│   └── Theorem_0_3_1.lean    # W-direction correspondence
├── Phase1/                   # SU(3) geometry
│   └── Theorem_1_2_2.lean    # Chiral anomaly
├── Phase2/                   # Pressure-depression mechanism
│   └── ...
├── Phase3/                   # Mass generation
│   ├── Theorem_3_0_1.lean
│   ├── Theorem_3_0_2.lean
│   ├── Theorem_3_1_1.lean    # Phase-gradient mass generation formula
│   ├── Theorem_3_1_2.lean    # Mass hierarchy
│   ├── Theorem_3_2_1.lean    # Low-energy equivalence
│   ├── Theorem_3_2_2.lean    # High-energy deviations
│   ├── Corollary_3_1_3.lean  # Neutrinos
│   └── Lemma_3_1_2a.lean
├── Phase4/                   # Solitons and matter
│   ├── Theorem_4_1_2.lean
│   └── Theorem_4_1_3.lean
├── Phase5/                   # Emergent gravity
│   ├── Theorem_5_1_1.lean    # Stress-energy tensor
│   ├── Theorem_5_2_0.lean    # Wick rotation validity
│   └── Theorem_5_2_4.lean    # Newton's constant
├── PureMath/                 # Pure mathematical structures
│   ├── AlgebraicTopology/    # Homotopy groups, etc.
│   ├── Analysis/             # Analysis tools
│   ├── LieAlgebra/           # SU(3), weights
│   ├── Polyhedra/            # Stella octangula geometry
│   ├── QFT/                  # QFT structures
│   └── Topology/             # Topological tools
├── ColorFields/              # Color field definitions
│   └── Basic.lean
├── Tactics/                  # Custom Lean tactics
├── Definition_0_0_0.lean     # Master definition (minimal geometric realization)
├── Basic.lean                # Basic imports and re-exports
├── Prelude.lean              # Project prelude
├── CLAUDE.md                 # This file - Lean guidance
└── LEAN_VERIFICATION_PROMPTS.md  # Verification prompts for Lean proofs
```

### Corresponding Directories

| Lean Directory | Proof Documents | Verification |
|----------------|-----------------|--------------|
| `Foundations/` | `docs/proofs/foundations/` | `verification/foundations/` |
| `Phase0/` | `docs/proofs/Phase0/` | `verification/Phase0/` |
| `Phase3/` | `docs/proofs/Phase3/` | `verification/Phase3/` |
| `Phase5/` | `docs/proofs/Phase5/` | `verification/Phase5/` |
| `PureMath/` | (supporting math) | — |

## Coding Standards

### Naming Conventions
```lean
-- Theorems: theorem_X_Y_Z or descriptive name
theorem stella_is_compound_of_tetrahedra : ...
theorem fundamental_weights_sum_zero : ...

-- Lemmas: prefix with lemma_ or descriptive
lemma edge_vector_is_root : ...

-- Definitions: descriptive, lowercase with underscores
def stella_octangula : Set (Fin 3 → ℝ) := ...
def color_weight (c : ColorLabel) : ScaledWeight := ...

-- Structures: CamelCase
structure ScaledWeight where
  T₃ : ℚ
  T₈ : ℚ
```

### Proof Style
```lean
-- Prefer tactic proofs with clear structure
theorem my_theorem : statement := by
  -- Step 1: Setup
  intro h
  -- Step 2: Key transformation
  have key : intermediate := by
    exact specific_lemma h
  -- Step 3: Conclusion
  exact final_step key

-- For decidable finite computations, use native_decide sparingly
theorem finite_check : (List.all elements property) = true := by
  native_decide
```

### Documentation
```lean
/-- 
**Theorem 0.0.3**: The SU(3) color structure

The three color labels (R, G, B) correspond to the fundamental weights
of SU(3), satisfying:
- $w_R + w_G + w_B = 0$ (weight sum zero)
- Permuted by S₃ transitively
- Form the vertices of a triangle in the T₃-T₈ plane
-/
theorem color_weights_theorem : ... := by
```

## Common Patterns

### Defining Finite Types
```lean
inductive ColorLabel : Type where
  | R | G | B
  deriving DecidableEq, Repr, Fintype

def ColorLabel.all : List ColorLabel := [.R, .G, .B]
```

### Working with SU(3) Weights
```lean
structure ScaledWeight where
  T₃ : ℚ      -- Cartan-Weyl T₃ coordinate (scaled by 2)
  T₈ : ℚ      -- Cartan-Weyl T₈ coordinate (scaled by 2√3)
  deriving DecidableEq, Repr

-- Fundamental weights (scaled)
def w_R : ScaledWeight := ⟨1, 1⟩     -- (1/2, 1/(2√3)) scaled
def w_G : ScaledWeight := ⟨-1, 1⟩   -- (-1/2, 1/(2√3)) scaled
def w_B : ScaledWeight := ⟨0, -2⟩   -- (0, -1/√3) scaled
```

### Verifying Root Systems
```lean
-- A₂ roots in scaled coordinates
def α₁ : ScaledWeight := ⟨2, 0⟩      -- simple root
def α₂ : ScaledWeight := ⟨-1, 3⟩    -- simple root

-- Check that stella edges are roots
theorem stella_edges_are_roots : 
  ∀ e ∈ stella_edges, is_A2_root (edge_to_weight e) := by
```

## Verification Checklist

Before marking a theorem complete:

- [ ] **No `sorry`** anywhere in the file
- [ ] **No placeholder axioms** for provable facts
- [ ] **Compiles without errors** (`lake build`)
- [ ] **Uses Mathlib/PhysLean** where applicable
- [ ] **Physically correct** (dimensional analysis, symmetries)
- [ ] **Well-documented** (docstrings on main theorems)
- [ ] **Tests included** where possible (#check, #eval)

## Building and Testing

```bash
cd ChiralGeometrogenesis
lake build                    # Build entire project
lake build ChiralGeometrogenesis.Foundations  # Build specific module
```

## Key References

- **Mathematical-Proof-Plan.md** — Master theorem list with dependencies
- **Lean-Formalization-Plan.md** — Detailed Lean implementation roadmap
- Mathlib docs: https://leanprover-community.github.io/mathlib4_docs/
- PhysLean: https://github.com/HEPLean/PhysLean

## When Stuck

1. **Search Mathlib** for existing lemmas before proving from scratch
2. **Break into smaller lemmas** rather than using `sorry`
3. **Use `#check` and `#print`** to understand available API
4. **Consult the proof plan** in `docs/` for mathematical guidance
5. **Ask for help** with specific error messages
