# CLAUDE.md - Figure Generation Guide

This file provides guidance for creating publication-quality figures for the Chiral Geometrogenesis paper.

## Directory Structure

```
figures/
├── scripts/           # Python scripts that generate figures
│   ├── fig_*.py       # Each script generates one or more figures
│   └── ...
├── fig_*.pdf          # Vector output (primary for LaTeX)
├── fig_*.png          # Raster output (for preview/web)
└── CLAUDE.md          # This file
```

## Script Template

Every figure script should follow this structure:

```python
#!/usr/bin/env python3
"""
Figure: [Title] ([Theorem/Section Reference])

[Brief description of what the figure shows]

Key physics:
- [Bullet point 1]
- [Bullet point 2]

Proof Document: docs/proofs/[path]
Paper Section: Section X.X ([Title])

Output: fig_[name].pdf, fig_[name].png
"""

import numpy as np
import matplotlib.pyplot as plt
import os

# Create output directory (parent figures folder)
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
OUTPUT_DIR = os.path.dirname(SCRIPT_DIR)  # figures/
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Publication style settings
plt.rcParams.update({
    'font.family': 'sans-serif',
    'font.sans-serif': ['DejaVu Sans', 'Arial', 'Helvetica'],
    'font.size': 10,
    'axes.labelsize': 11,
    'axes.titlesize': 12,
    'legend.fontsize': 9,
    'xtick.labelsize': 10,
    'ytick.labelsize': 10,
    'figure.dpi': 150,
    'savefig.dpi': 300,
    'text.usetex': False,
    'mathtext.fontset': 'dejavusans',
})

# ... figure creation code ...

def main():
    # Generate and save figures
    fig = create_figure()
    fig.savefig(os.path.join(OUTPUT_DIR, 'fig_name.png'),
                dpi=300, bbox_inches='tight', facecolor='white')
    fig.savefig(os.path.join(OUTPUT_DIR, 'fig_name.pdf'),
                bbox_inches='tight', facecolor='white')
    plt.close('all')

if __name__ == '__main__':
    main()
```

---

## Lessons Learned

### 1. Label Positioning - Avoid Edge Clipping

**Problem:** Labels placed near the edges of the plot area get clipped in the output.

**Solution:** Position elements with margin from the axis limits.

```python
# BAD - labels at y=1.5 get clipped when ylim is [-2, 2]
ax.text(0, 1.85, r'$g^+$', ...)  # Too close to edge!

# GOOD - keep labels within safe zone (80% of axis range)
ax.text(0, 1.35 + 0.38, r'$g^+$', ...)  # Label at ~1.73, within bounds
```

**Rule of thumb:** Keep text/annotations at least 10% away from axis limits.

### 2. Central Annotations - Use Title/Subtitle Instead

**Problem:** Placing key formulas in the center of a visualization obscures the data.

**Solution:** Move important equations to the title as a subtitle.

```python
# BAD - blocks the visualization
ax.text(0, 0, r'$G\tilde{G} \propto |G^+|^2 - |G^-|^2$',
        bbox=dict(facecolor='white', ...))

# GOOD - clean visualization with formula in subtitle
ax.set_title(r'Helicity Selection: $G\tilde{G}$ Coupling Pattern' + '\n' +
             r'$G\tilde{G} \propto |G^+|^2 - |G^-|^2$',
             fontsize=13, fontweight='bold')
```

### 3. Custom Circular Arrows for Helicity

**Problem:** Matplotlib's `Arc` patch doesn't include arrow heads.

**Solution:** Create a custom function combining Arc + annotate arrow.

```python
def draw_helicity_arrow(ax, cx, cy, radius=0.25, direction='ccw', color='white', lw=2.5):
    """
    Draw a circular arrow indicating helicity (spin rotation).

    Parameters:
    - cx, cy: center position
    - radius: size of the circular arrow
    - direction: 'ccw' for positive helicity, 'cw' for negative
    """
    from matplotlib.patches import Arc

    if direction == 'ccw':
        theta1, theta2 = 45, 315
        arrow_angle = np.radians(315)
    else:
        theta1, theta2 = 315, 45
        arrow_angle = np.radians(45)

    # Draw the arc
    arc = Arc((cx, cy), 2*radius, 2*radius, angle=0,
              theta1=theta1, theta2=theta2, color=color, lw=lw)
    ax.add_patch(arc)

    # Arrow head at end of arc
    head_x = cx + radius * np.cos(arrow_angle)
    head_y = cy + radius * np.sin(arrow_angle)

    if direction == 'ccw':
        dx = -np.sin(arrow_angle) * 0.12
        dy = np.cos(arrow_angle) * 0.12
    else:
        dx = np.sin(arrow_angle) * 0.12
        dy = -np.cos(arrow_angle) * 0.12

    ax.annotate('', xy=(head_x + dx, head_y + dy), xytext=(head_x, head_y),
                arrowprops=dict(arrowstyle='->', color=color, lw=lw,
                              mutation_scale=15))
```

### 4. LaTeX Compatibility in Matplotlib

**Problem:** Some LaTeX commands don't work with matplotlib's mathtext parser.

**Unsupported commands:**
- `\xrightarrow` - use `\to` or `\rightarrow` instead
- `\text{}` - use `\mathrm{}` instead
- `\bm{}` - not available, use manual bold

```python
# BAD - will crash
ax.text(0, 0, r'$A \xrightarrow{\rm CPT} B$')

# GOOD - compatible syntax
ax.text(0, 0, r'$A \to B$')
ax.text(0, 0, r'$A \rightarrow B$')
```

### 5. Colormap Design for Physics

**Principle:** Colormaps should convey physical meaning.

```python
# For intensity/coupling strength (0 to max):
# Dark → Bright progression
colors = ['#0d1b2a', '#1b263b', '#415a77', '#778da9', '#e0e1dd',
          '#ffd700', '#ffb700', '#ff9500', '#ff7300', '#ff5100']
cmap = LinearSegmentedColormap.from_list('intensity', colors)

# For diverging data (negative to positive):
# Use symmetric colormap with neutral center
cmap = plt.cm.RdBu_r  # Red (negative) - White (zero) - Blue (positive)
```

### 6. Figure Sizing Guidelines

| Type | Size (inches) | Use Case |
|------|---------------|----------|
| Single panel | (7, 6) | One main visualization |
| Two panels | (12, 5) | Side-by-side comparison |
| Three panels | (14, 5) | Multiple related plots |
| Four panels (2×2) | (12, 10) | Comprehensive overview |

```python
# Single column (journal): width ≤ 3.5 inches
# Double column (journal): width ≤ 7 inches
# Full page: width ≤ 7 inches, height ≤ 9 inches
```

### 7. Panel Labels

Always add panel labels for multi-panel figures:

```python
# Position in axes coordinates (0,0 = bottom-left, 1,1 = top-right)
ax.text(-0.12, 1.05, '(a)', transform=ax.transAxes,
        fontsize=14, fontweight='bold')
```

### 8. Color Palette for Consistency

Use consistent colors across related figures:

```python
# Standard palette for CG figures
COLOR_POSITIVE = '#FFD700'    # Gold - positive helicity/values
COLOR_NEGATIVE = '#4169E1'    # Royal blue - negative helicity/values
COLOR_CHI = '#9B59B6'         # Purple - χ field
COLOR_GLUON = '#E67E22'       # Orange - gluons
COLOR_QUARK = '#27AE60'       # Green - quarks
COLOR_VERTEX = '#2C3E50'      # Dark - vertices/interactions
COLOR_HIGHLIGHT = '#E74C3C'   # Red - important annotations
```

### 9. Always Test with Image Viewing

**Critical:** Always view the generated PNG to catch issues not visible in code:
- Clipped labels
- Overlapping text
- Color contrast problems
- Missing elements

```python
# After generating, always check:
# 1. Open the PNG file and visually inspect
# 2. Check all labels are fully visible
# 3. Verify colors are distinguishable
# 4. Confirm text is readable at expected display size
```

### 10. Minimalism - Don't Over-Design

**Problem:** Adding too many annotations, boxes, arrows, and formulas clutters the figure and obscures the main message.

**Principle:** Each figure should communicate ONE main idea clearly. Let the visualization do the work.

```python
# BAD - cluttered with redundant information
ax.text(..., r'$\sigma/\sigma_{\rm tot} \sim 10^{-9}$', ...)  # Suppression ratio
ax.text(..., r'$\mathcal{M} = \frac{C_\chi^2...}{...}$', ...)  # Full formula
ax.annotate(..., r'$\propto s^2$', ...)  # Scaling arrow
# Plus a large box, multiple colors, etc.

# GOOD - one clear annotation, let the gradient speak
ax.text(2.75, -2.5, r'$\sigma/\sigma_{\rm tot} \sim 10^{-9}$',
        fontsize=12, ha='center', color='white',
        bbox=dict(boxstyle='round', facecolor='purple', alpha=0.85))
```

**Guidelines:**
- **One annotation per panel** unless absolutely necessary
- **Formulas belong in captions** or the paper text, not on the figure
- **Arrows/lines** only if they show something the data doesn't already show
- **If in doubt, leave it out** - simpler is almost always better

**Ask yourself:** "Does this annotation add information the reader can't already see from the visualization?"

---

## Common Patterns

### Gradient Visualization

```python
def create_gradient_plot(ax, data, extent, cmap, title):
    """Standard gradient/heatmap visualization."""
    im = ax.imshow(data, extent=extent, origin='lower',
                   cmap=cmap, vmin=0, vmax=1)
    ax.set_aspect('equal')
    ax.set_title(title, fontsize=13, fontweight='bold')

    # Add colorbar
    from mpl_toolkits.axes_grid1 import make_axes_locatable
    divider = make_axes_locatable(ax)
    cax = divider.append_axes("right", size="5%", pad=0.1)
    cbar = plt.colorbar(im, cax=cax)
    return im, cbar
```

### Feynman Diagram Elements

```python
# Propagator (dashed for scalar)
ax.plot([x1, x2], [y1, y2], '--', color=COLOR_CHI, lw=3)

# Vertex (filled circle)
from matplotlib.patches import Circle
vertex = Circle((x, y), 0.2, facecolor=COLOR_VERTEX,
                edgecolor='white', linewidth=2, zorder=5)
ax.add_patch(vertex)

# External line with arrow
ax.annotate('', xy=(x2, y2), xytext=(x1, y1),
            arrowprops=dict(arrowstyle='->', color=COLOR_GLUON, lw=2.5))
```

### Formula Boxes

```python
from matplotlib.patches import FancyBboxPatch

# Highlighted formula box
box = FancyBboxPatch((x, y), width, height,
                      boxstyle="round,pad=0.3",
                      facecolor='#F8F9FA', edgecolor='#2C3E50', lw=2)
ax.add_patch(box)
ax.text(x + width/2, y + height/2, r'$\mathcal{M} = ...$',
        ha='center', va='center', fontsize=12)
```

---

## Checklist Before Committing

- [ ] Script runs without errors
- [ ] Both PNG and PDF generated
- [ ] All labels visible (not clipped)
- [ ] Colors are distinguishable
- [ ] Text is readable at expected size
- [ ] Colorbars have labels
- [ ] Panel labels present (if multi-panel)
- [ ] Title accurately describes content
- [ ] Docstring includes theorem/section reference
- [ ] Output files named with `fig_` prefix

---

## References

- **Matplotlib documentation:** https://matplotlib.org/stable/
- **Color palettes:** https://colorbrewer2.org/
- **LaTeX symbols in matplotlib:** https://matplotlib.org/stable/tutorials/text/mathtext.html

---

*Last Updated: 2026-01-31*
*Status: Active Development*
