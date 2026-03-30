"""
SU(3) Monte Carlo on FCC / D4 / Z^4 Lattice
==============================================

Independent numerical validation of exact analytical formulas for the
partition function, mass gap, and string tension on the FCC (D3), D4,
and Z^4 (hypercubic) lattices.

Modules:
    su3_ops        - SU(3) matrix operations (Numba-accelerated)
    fcc_lattice    - FCC (D3) lattice geometry builder (3D, 12 NN)
    d4_lattice     - D4 root lattice geometry builder (4D, 24 NN, triangular faces)
    z4_lattice     - Z^4 hypercubic lattice builder (4D, 8 NN, square faces)
    updates        - Metropolis + Cabibbo-Marinari heat bath sweeps
                     (triangular and square plaquette variants)
    observables    - Plaquette, Polyakov loop, correlators
                     (triangular and square plaquette variants)
    exact_formulas - Analytical reference values from character expansion
    run_simulation - Main driver with CLI (--lattice {fcc,d4,z4})
"""
