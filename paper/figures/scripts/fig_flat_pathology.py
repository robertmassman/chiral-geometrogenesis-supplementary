"""
Figure: Flat Configuration Pathology (§4.6) - Why Non-Uniform Amplitudes Are Required

This script generates fig_flat_pathology.png for the unified paper.
Demonstrates that uniform amplitudes lead to p=0 at equilibrium (destructive interference),
while non-uniform (stella) amplitudes resolve this pathology.

Source: verification/Phase0/theorem_0_1_0_field_existence.py
"""

import numpy as np
import matplotlib.pyplot as plt
from typing import Callable
import os

# Output directory
FIGURES_DIR = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def probability_distribution(x: np.ndarray, phi: np.ndarray,
                             amplitudes: np.ndarray) -> np.ndarray:
    """
    Calculate p_φ(x) = |Σ_c A_c(x) exp(iφ_c)|²

    Parameters:
    -----------
    x : array of spatial positions (for visualization)
    phi : array of three phases [φ_R, φ_G, φ_B]
    amplitudes : array of three amplitudes [A_R, A_G, A_B] at each x

    Returns:
    --------
    Probability distribution at each x
    """
    # Sum over colors
    total = np.zeros_like(x, dtype=complex)
    for c in range(3):
        total += amplitudes[c] * np.exp(1j * phi[c])

    return np.abs(total)**2


def stella_amplitudes(c: int, x: np.ndarray) -> np.ndarray:
    """
    Stella octangula pressure-like amplitudes.
    Model the three fields as having peaks at different positions.
    A_c(x) ∝ cos²((x - 2πc/3)/2) (normalized)
    """
    peak_pos = 2 * np.pi * c / 3
    amplitude = np.cos((x - peak_pos) / 2)**2
    # Normalize so ∫A_c² dx = 1
    norm = np.sqrt(np.sum(amplitude**2) * (x[1] - x[0]))
    return amplitude / norm


def plot_flat_configuration_pathology():
    """
    Visualize the flat configuration pathology (§4.6):
    - Uniform amplitudes lead to p=0 at equilibrium (destructive interference)
    - Non-uniform (stella) amplitudes resolve this pathology
    """
    fig, axes = plt.subplots(2, 2, figsize=(12, 10))

    x = np.linspace(0, 2*np.pi, 500)
    equilibrium_phases = np.array([0, 2*np.pi/3, 4*np.pi/3])
    colors = ['red', 'green', 'blue']

    # Plot 1: Uniform amplitudes
    ax1 = axes[0, 0]
    A_0 = 1.0 / np.sqrt(3)
    for c in range(3):
        ax1.axhline(y=A_0**2, color=colors[c], linestyle='--', alpha=0.7,
                   label=f'|A_{["R","G","B"][c]}|² = {A_0**2:.3f}')
    ax1.set_xlabel('x')
    ax1.set_ylabel('Amplitude²')
    ax1.set_title('Uniform Amplitudes: A_c(x) = A₀ (PATHOLOGICAL)')
    ax1.legend()
    ax1.set_xlim([0, 2*np.pi])
    ax1.set_ylim([0, 0.5])
    ax1.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
    ax1.set_xticklabels(['0', 'π/2', 'π', '3π/2', '2π'])

    # Plot 2: Resulting probability (uniform case)
    ax2 = axes[0, 1]
    A_uniform = np.array([np.ones_like(x) * A_0 for _ in range(3)])
    p_uniform = probability_distribution(x, equilibrium_phases, A_uniform)
    ax2.plot(x, p_uniform, 'purple', linewidth=2)
    ax2.axhline(y=0, color='red', linestyle='--', alpha=0.5)
    ax2.fill_between(x, 0, p_uniform, alpha=0.3, color='purple')
    ax2.set_xlabel('x')
    ax2.set_ylabel('p(x)')
    ax2.set_title(f'Probability: p = |Σ A₀ e^{{iφ_c}}|² = 0 (PATHOLOGY!)')
    ax2.set_xlim([0, 2*np.pi])
    ax2.set_ylim([-0.01, 0.1])
    ax2.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
    ax2.set_xticklabels(['0', 'π/2', 'π', '3π/2', '2π'])
    ax2.annotate('Complete destructive\ninterference!', xy=(np.pi, 0),
                xytext=(np.pi, 0.05), ha='center',
                arrowprops=dict(arrowstyle='->', color='red'),
                fontsize=10, color='red')

    # Plot 3: Stella (non-uniform) amplitudes
    ax3 = axes[1, 0]
    for c in range(3):
        A = stella_amplitudes(c, x)
        ax3.plot(x, A**2, color=colors[c], linewidth=2,
                label=f'|A_{["R","G","B"][c]}(x)|²')
    ax3.set_xlabel('x')
    ax3.set_ylabel('Amplitude²')
    ax3.set_title('Stella Amplitudes: A_c(x) varies with position (RESOLUTION)')
    ax3.legend()
    ax3.set_xlim([0, 2*np.pi])
    ax3.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
    ax3.set_xticklabels(['0', 'π/2', 'π', '3π/2', '2π'])

    # Plot 4: Resulting probability (stella case)
    ax4 = axes[1, 1]
    A_stella = np.array([stella_amplitudes(c, x) for c in range(3)])
    p_stella = probability_distribution(x, equilibrium_phases, A_stella)
    ax4.plot(x, p_stella, 'purple', linewidth=2)
    ax4.fill_between(x, 0, p_stella, alpha=0.3, color='purple')
    ax4.set_xlabel('x')
    ax4.set_ylabel('p(x)')
    ax4.set_title(f'Probability: p > 0 (avg = {np.mean(p_stella):.4f}) ✓ RESOLVED')
    ax4.set_xlim([0, 2*np.pi])
    ax4.set_xticks([0, np.pi/2, np.pi, 3*np.pi/2, 2*np.pi])
    ax4.set_xticklabels(['0', 'π/2', 'π', '3π/2', '2π'])

    plt.suptitle('Flat Configuration Pathology (§4.6): Why Non-Uniform Amplitudes Are Required',
                fontsize=12, fontweight='bold')
    plt.tight_layout()

    # Save to figures directory
    output_path = os.path.join(FIGURES_DIR, 'fig_flat_pathology.png')
    plt.savefig(output_path, dpi=150)
    plt.savefig(output_path.replace('.png', '.pdf'), dpi=150)
    plt.close()

    print(f"Created: {output_path}")
    print(f"Created: {output_path.replace('.png', '.pdf')}")
    return output_path


if __name__ == "__main__":
    plot_flat_configuration_pathology()
