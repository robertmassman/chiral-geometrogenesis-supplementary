# Installation Guide

This guide covers setting up the development environment to build and verify the Chiral Geometrogenesis proofs.

## Prerequisites

- macOS, Linux, or Windows with WSL2
- Git
- Python 3.9+
- ~2GB disk space for Lean dependencies

## Lean 4 Setup

### 1. Install elan (Lean version manager)

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Follow the prompts and restart your terminal, or run:
```bash
source ~/.profile  # or ~/.bashrc, ~/.zshrc
```

### 2. Build the Lean project

```bash
cd lean
lake build
```

The first build will download Mathlib4 and its dependencies (~1.5GB). This may take 15-30 minutes depending on your internet connection and CPU.

### 3. Verify the build

After successful build, you should see no errors. You can verify specific theorems:

```bash
lake env lean ChiralGeometrogenesis/Foundations/Theorem_0_0_1.lean
```

## Python Verification Setup

### 1. Create virtual environment (recommended)

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
```

### 2. Install dependencies

```bash
cd verification
pip install numpy scipy sympy matplotlib pytest
```

Or if a requirements.txt exists:
```bash
pip install -r requirements.txt
```

### 3. Run verification suite

```bash
python -m pytest . -v
```

To run a specific phase:
```bash
python -m pytest Phase3/ -v
```

### 4. Run individual verification scripts

```bash
python Phase3/theorem_3_1_1_mass_hierarchy.py
```

## LaTeX Setup (for paper compilation)

### macOS
```bash
brew install --cask mactex
```

### Ubuntu/Debian
```bash
sudo apt install texlive-full latexmk
```

### Compile the paper
```bash
cd paper
latexmk -pdf main.tex
```

## IDE Setup

### VS Code with Lean 4
1. Install [VS Code](https://code.visualstudio.com/)
2. Install the "lean4" extension from the marketplace
3. Open the `lean/` folder as your workspace

### Emacs with lean4-mode
```elisp
(use-package lean4-mode
  :straight (lean4-mode :type git :host github :repo "leanprover/lean4-mode"))
```

## Troubleshooting

### Lean build fails with memory errors
Increase available memory or add swap space. Mathlib4 compilation is memory-intensive.

### Python import errors
Ensure you're in the correct directory and virtual environment is activated:
```bash
cd verification
source ../venv/bin/activate
python -c "import numpy; print('OK')"
```

### Lake cannot find Mathlib
Delete `.lake` and rebuild:
```bash
cd lean
rm -rf .lake
lake build
```

## Verification Checklist

After installation, verify everything works:

- [ ] `lake build` completes without errors
- [ ] `python -m pytest verification/ -v` passes
- [ ] `latexmk -pdf paper/main.tex` produces main.pdf
