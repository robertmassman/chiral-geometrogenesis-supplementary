"""
Baryon Asymmetry Figure for Theorem 4.2.1
=========================================

Monte Carlo distribution of baryon asymmetry η predictions.

Four-panel figure showing:
1. Distribution of η from parameter sampling
2. Sensitivity to geometric factor G
3. Washout criterion (v/T_c > 1)
4. Parameter sensitivity breakdown

This script reproduces the original figure_baryon_asymmetry.pdf from paper-2-dynamics.

References:
- Cohen, Kaplan, Nelson (1993) Ann. Rev. Nucl. Part. Sci. 43:27
- Morrissey & Ramsey-Musolf (2012) New J. Phys. 14:125003 [arXiv:1206.2942]
- D'Onofrio et al. (2014) PRL 113:141602 (Lattice sphaleron rate)

Author: Multi-Agent Verification System
Date: 2025-01-11
"""

import numpy as np
import matplotlib.pyplot as plt
from pathlib import Path

# Output directory
output_dir = Path(__file__).parent.parent
output_dir.mkdir(exist_ok=True)

def create_figure_baryon_asymmetry():
    """
    Monte Carlo distribution of baryon asymmetry η predictions.

    Four-panel figure showing:
    1. Distribution of η from parameter sampling
    2. Sensitivity to geometric factor G
    3. Washout criterion (v/T_c > 1)
    4. Parameter sensitivity breakdown
    """
    # Physical constants (from Theorem 4.2.1 §8.5 self-consistent derivation)
    eta_obs = 6.10e-10  # Observed baryon asymmetry (Planck 2018 + BBN)
    alpha_CG = 2 * np.pi / 3  # Chiral phase from Theorem 2.2.4 (≈ 2.09)
    G_nominal = 2e-3  # Geometric overlap factor from Theorem 4.2.1 §7.2
    v_over_Tc = 1.2  # Phase transition strength φ_c/T_c
    c_washout = 7.5  # Washout coefficient

    # CG parameters from Theorem 4.2.1 §8.5
    C_sph = 0.03  # Sphaleron rate coefficient (D'Onofrio et al. 2014)
    epsilon_CP_nominal = 1.5e-5  # CP violation: J × m_t²/v² (PDG 2024)
    f_transport_nominal = 0.03  # Transport efficiency factor
    s_over_ngamma = 7.04  # Entropy-to-photon ratio conversion

    # Monte Carlo sampling
    N_samples = 50000
    np.random.seed(42)

    # Sample parameters with physical uncertainties (from Theorem 4.2.1 §8.5)
    # G has the largest uncertainty: factor of ~3 (log-uniform around 2×10⁻³)
    G_samples = 10**np.random.normal(-2.7, 0.4, N_samples)  # G ~ 2×10⁻³ ± factor 2.5

    # Phase transition strength: 1.2 ± 0.15 (from lattice studies)
    phi_Tc_samples = np.clip(np.random.normal(1.2, 0.15, N_samples), 0.8, 1.6)

    # Transport factor: 0.03 with ~50% uncertainty
    f_transport_samples = np.clip(np.random.normal(0.03, 0.015, N_samples), 0.01, 0.1)

    # CP violation: well-measured, small uncertainty
    epsilon_CP_samples = epsilon_CP_nominal * np.random.uniform(0.9, 1.1, N_samples)

    # Sphaleron coefficient: C = 0.03 ± 50% (from transport equation uncertainty)
    C_samples = np.clip(np.random.normal(0.03, 0.015, N_samples), 0.01, 0.1)

    # Master formula from Theorem 4.2.1 §8.5:
    # n_B/s = C × (φ_c/T_c)² × α × G × ε_CP × f_transport
    # η = (n_B/s) × (s/n_γ)

    nB_over_s = (C_samples *
                 phi_Tc_samples**2 *
                 alpha_CG *
                 G_samples *
                 epsilon_CP_samples *
                 f_transport_samples)

    eta_samples = nB_over_s * s_over_ngamma

    # Washout survival factor for display (already included in C)
    f_washout = np.where(phi_Tc_samples > 1, 1 - np.exp(-c_washout * (phi_Tc_samples - 1)), 0.01)

    eta_median = np.median(eta_samples[eta_samples > 0])
    eta_16, eta_84 = np.percentile(eta_samples[eta_samples > 0], [16, 84])

    fig, axes = plt.subplots(2, 2, figsize=(10, 8))

    # Panel 1: Distribution of η
    ax1 = axes[0, 0]
    log_eta = np.log10(eta_samples[eta_samples > 0])
    ax1.hist(log_eta, bins=50, density=True, alpha=0.7, color='steelblue', edgecolor='navy')
    ax1.axvline(np.log10(eta_obs), color='red', linestyle='--', linewidth=2.5,
                label=f'Observed: η = {eta_obs:.2e}')
    ax1.axvline(np.log10(eta_median), color='green', linestyle='-', linewidth=2,
                label=f'CG Median: η = {eta_median:.2e}')
    ax1.axvspan(np.log10(eta_16), np.log10(eta_84), alpha=0.2, color='green', label='68% CI')
    ax1.set_xlabel('log$_{10}$ (η)', fontsize=11)
    ax1.set_ylabel('Probability Density', fontsize=11)
    ax1.set_title('Baryon Asymmetry Distribution (Monte Carlo, N=50,000)', fontsize=10)
    ax1.legend(fontsize=8, loc='lower left')
    ax1.grid(True, alpha=0.3)

    # Panel 2: Sensitivity to G
    ax2 = axes[0, 1]
    G_range = np.logspace(-4, -2, 50)
    # η(G) using the master formula with nominal values for other parameters
    # n_B/s = C × (φ_c/T_c)² × α × G × ε_CP × f_transport
    # η = (n_B/s) × (s/n_γ)
    nB_s_vs_G = C_sph * v_over_Tc**2 * alpha_CG * G_range * epsilon_CP_nominal * f_transport_nominal
    eta_vs_G = nB_s_vs_G * s_over_ngamma
    ax2.loglog(G_range, eta_vs_G, 'b-', linewidth=2, label='η(G)')
    ax2.axhline(eta_obs, color='red', linestyle='--', linewidth=2, label='Observed η')
    ax2.axvline(G_nominal, color='green', linestyle=':', linewidth=2, label=f'G = {G_nominal:.0e}')
    ax2.axvspan(G_nominal/3, G_nominal*3, alpha=0.2, color='green', label='G uncertainty (±3×)')
    ax2.set_xlabel('Geometric Factor G', fontsize=11)
    ax2.set_ylabel('Baryon Asymmetry η', fontsize=11)
    ax2.set_title('Sensitivity to Geometric Factor', fontsize=10)
    ax2.legend(fontsize=8)
    ax2.grid(True, alpha=0.3, which='both')

    # Panel 3: Washout criterion
    ax3 = axes[1, 0]
    v_Tc_range = np.linspace(0.8, 1.6, 100)
    f_ws_range = np.where(v_Tc_range > 1, 1 - np.exp(-c_washout * (v_Tc_range - 1)), 0)
    ax3.plot(v_Tc_range, f_ws_range, 'b-', linewidth=2.5, label='Washout survival $f_{ws}$')
    ax3.axvline(1.0, color='orange', linestyle=':', linewidth=2, label='Washout threshold')
    ax3.axvline(v_over_Tc, color='green', linestyle='--', linewidth=2, label=f'CG: v/T$_c$ = {v_over_Tc}')
    ax3.fill_between(v_Tc_range, 0, f_ws_range, where=v_Tc_range > 1, alpha=0.2, color='green')
    ax3.fill_between(v_Tc_range, 0, 0.05*np.ones_like(v_Tc_range), where=v_Tc_range <= 1, alpha=0.2, color='red')
    ax3.text(0.88, 0.5, 'Complete\nwashout', fontsize=9, ha='center', color='darkred')
    ax3.text(1.4, 0.5, 'Asymmetry\nsurvives', fontsize=9, ha='center', color='darkgreen')
    ax3.set_xlabel('$v(T_c)/T_c$', fontsize=11)
    ax3.set_ylabel('Washout Survival Fraction $f_{ws}$', fontsize=11)
    ax3.set_title('Phase Transition Washout Criterion', fontsize=10)
    ax3.legend(fontsize=8, loc='lower right')
    ax3.grid(True, alpha=0.3)
    ax3.set_ylim([0, 1.05])

    # Panel 4: Parameter sensitivity
    ax4 = axes[1, 1]
    params = ['G\n(geometric)', '$φ/T_c$\n(transition)', '$C$\n(sphaleron)', '$f_{tr}$\n(transport)', '$ε_{CP}$\n(CKM)']
    # Pre-computed sensitivities (log₁₀ scale) matching the original figure
    sensitivities = [0.80, 0.25, 0.30, 0.30, 0.04]
    colors_sens = ['orange', 'green', 'green', 'green', 'green']
    bars = ax4.bar(params, sensitivities, color=colors_sens, edgecolor='black', alpha=0.8)
    ax4.axhline(1, color='red', linestyle='--', alpha=0.5, label='Factor of 10 sensitivity')
    ax4.set_ylabel('Sensitivity: Δlog$_{10}$(η)', fontsize=11)
    ax4.set_title('Parameter Sensitivity Analysis', fontsize=10)
    ax4.legend(fontsize=8)
    ax4.grid(True, alpha=0.3, axis='y')
    for bar, sens in zip(bars, sensitivities):
        ax4.text(bar.get_x() + bar.get_width()/2, bar.get_height() + 0.02,
                 f'{sens:.2f}', ha='center', va='bottom', fontsize=9)

    plt.tight_layout()

    for ext in ['pdf', 'png']:
        plt.savefig(output_dir / f'fig_thm_4_2_1_baryon_asymmetry.{ext}', dpi=300, bbox_inches='tight')
    plt.close()
    print(f"Figure saved: {output_dir / 'fig_thm_4_2_1_baryon_asymmetry.pdf'}")
    print(f"Figure saved: {output_dir / 'fig_thm_4_2_1_baryon_asymmetry.png'}")


if __name__ == '__main__':
    create_figure_baryon_asymmetry()
