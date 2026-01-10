# Chiral Geometrogenesis - Lean 4 Formalization

This project contains formal proofs of the Chiral Geometrogenesis framework using Lean 4 and Mathlib.

## 🎯 Main Result: Theorem 0.0.1 (D = 4 Consistency)

**Statement:** Among all possible spacetime dimensions D ≥ 2, D = 4 is the unique
value where physical constraints for observer existence are mutually consistent.

```lean
theorem D_equals_four_consistency :
    ∀ D : ℕ, D ≥ 2 → (ObserverCompatible D ↔ D = 4)
```

**Status:** ✅ Fully verified from axioms (no `sorry` in main theorem)

### For Peer Reviewers

See the `ChiralGeometrogenesis/Foundations/` directory:

| Document | Purpose |
|----------|---------|
| [PEER_REVIEW.md](ChiralGeometrogenesis/Foundations/PEER_REVIEW.md) | Complete peer review guide |
| [DEPENDENCY_GRAPH.md](ChiralGeometrogenesis/Foundations/DEPENDENCY_GRAPH.md) | Axiom dependency analysis |
| [SORRY_DOCUMENTATION.md](ChiralGeometrogenesis/Foundations/SORRY_DOCUMENTATION.md) | All sorry statements documented |
| [VERIFICATION_CHECKLIST.md](ChiralGeometrogenesis/Foundations/VERIFICATION_CHECKLIST.md) | Step-by-step verification |

### Quick Verification

```bash
# Build and check for errors
cd ChiralGeometrogenesis
lake build 2>&1 | grep -E "error|sorry"

# Expected: Only 'sorry' warnings in PureMath/ modules, no errors
```

---

## Project Structure

```
ChiralGeometrogenesis/
├── ChiralGeometrogenesis.lean    # Main module file
├── ChiralGeometrogenesis/
│   ├── Foundations/              # Core axioms and main theorem
│   │   ├── PhysicalAxioms.lean   # 21 axioms (A:6 + B:4 + C:4 + D:7)
│   │   ├── StabilityTheorems.lean # Stability constraints
│   │   ├── Theorem_0_0_1.lean    # Main D=4 theorem
│   │   └── *.md                  # Peer review documentation
│   ├── PureMath/                 # Mathematical foundations
│   │   ├── Topology/KnotTheory.lean  # Concrete knot theory (4 sorries)
│   │   └── Analysis/WaveEquation.lean
│   ├── Definition_0_0_0.lean     # Minimal Geometric Realization
│   └── Theorem_0_0_2.lean        # Euclidean Metric from SU(3)
├── lakefile.toml                 # Build configuration
└── lean-toolchain                # Lean version (v4.26.0)
```

## Getting Started

### Prerequisites

1. Install `elan` (Lean version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. Source the environment:
   ```bash
   source ~/.elan/env
   ```

### Building

```bash
cd ChiralGeometrogenesis
lake build
```

### Opening in VS Code

1. Open VS Code in this directory
2. The Lean 4 extension will automatically activate
3. Open any `.lean` file to see type checking and proof goals

## Working with Proofs

### Writing New Theorems

1. Create a new file in `ChiralGeometrogenesis/` (e.g., `Theorem_X_Y_Z.lean`)
2. Add imports at the top:
   ```lean
   import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
   ```
3. Add the import to `ChiralGeometrogenesis.lean`
4. Run `lake build` to check

### Key Tactics

- `simp` - Simplification
- `ring` - Algebraic simplification
- `omega` - Linear arithmetic
- `norm_num` - Numeric computation
- `exact` - Provide exact proof term
- `sorry` - Mark as incomplete (TODO)

### Mathlib Documentation

- [Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/)
- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)

## Proof Status

| Module | Status | Description |
|--------|--------|-------------|
| `Foundations/Theorem_0_0_1.lean` | ✅ **Main Theorem** | D = 4 consistency (fully verified) |
| `Foundations/PhysicalAxioms.lean` | ✅ Compiles | 21 axioms with documentation |
| `Foundations/StabilityTheorems.lean` | ✅ Compiles | Stability constraint proofs |
| `PureMath/Topology/KnotTheory.lean` | ⚠️ 4 sorry | Knot theory foundations |
| `PureMath/Analysis/WaveEquation.lean` | ⚠️ 6 sorry | Wave/Huygens foundations |
| `Definition_0_0_0.lean` | ✅ Compiles | Geometric realization definition |
| `Theorem_0_0_2.lean` | ✅ Compiles | Euclidean metric from SU(3) |

### Axiom Summary

| Category | Count | Description |
|----------|-------|-------------|
| A (Predicates) | 6 | Definitional predicates |
| B (Physical Laws) | 4 | Dimension scaling laws |
| C (Empirical Facts) | 4 | Observations about 3D |
| D (Math Theorems) | 7 | Mathematical results |
| **Total** | **21** | All documented in PhysicalAxioms.lean |

**Note:** Knot theory (formerly Category E) is now implemented with concrete
definitions in `KnotTheory.lean`, containing 4 sorries for deep topological facts.

---

## Tips for Verification

1. **Start simple**: Begin with basic numerical facts (`2 * 3 = 6`)
2. **Use `sorry`**: Mark incomplete proofs to continue working
3. **Check incrementally**: Run `lake build` frequently
4. **Use the infoview**: VS Code shows proof goals interactively
5. **Search Mathlib**: Many lemmas already exist - use `#check` and `#print`

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.
