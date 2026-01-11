// ============================================
// CHIRAL GEOMETROGENESIS VISUALIZATION CLASS
// Visualizes spacetime emergence via SU(3) vacuum condensation
// Based on the Stella Octangula as SU(3) weight diagram representation
// ============================================

class TetrahedronVisualization {
    constructor(canvas, isMirrored = false) {
        this.canvas = canvas;
        this.ctx = canvas.getContext('2d');
        this.isMirrored = isMirrored; // Represents C-Conjugation (Charge Conjugation) symmetry
        this.scale = 200;
        this.centerX = 0;
        this.centerY = 0;
        // Brightness represents matter/antimatter distinction via C-symmetry
        // The Stella Octangula's two interpenetrating tetrahedra represent color/anti-color
        this.brightnessMultiplier = isMirrored ? 0.6 : 1.2;
        
        this.resizeCanvas = this.resizeCanvas.bind(this);
        this.draw = this.draw.bind(this);
        
        this.resizeCanvas();
    }

    resizeCanvas() {
        this.canvas.width = this.canvas.offsetWidth;
        this.canvas.height = this.canvas.offsetHeight;
        this.centerX = this.canvas.width / 2;
        this.centerY = this.canvas.height / 2;
    }

    // Transform from world coordinates to screen coordinates
    // When mirrored, applies 180° rotation representing Charge Conjugation (C-symmetry)
    // This transforms color charges to anti-color charges in the SU(3) weight diagram
    toScreen(x, y) {
        if (this.isMirrored) {
            // C-Conjugation: (x, y) -> (-x, -y) maps quarks to antiquarks
            x = -x;
            y = -y;
        }
        return {
            x: this.centerX + x * this.scale,
            y: this.centerY - y * this.scale
        };
    }

    drawPoint(x, y, radius, color, strokeColor = null, strokeWidth = 0) {
        const screen = this.toScreen(x, y);
        this.ctx.fillStyle = this.adjustColor(color);
        this.ctx.beginPath();
        this.ctx.arc(screen.x, screen.y, radius, 0, Math.PI * 2);
        this.ctx.fill();
        if (strokeColor) {
            this.ctx.strokeStyle = this.adjustColor(strokeColor);
            this.ctx.lineWidth = strokeWidth;
            this.ctx.stroke();
        }
    }

    drawCircle(x, y, radius, color, lineWidth = 2) {
        const screen = this.toScreen(x, y);
        this.ctx.strokeStyle = this.adjustColor(color);
        this.ctx.lineWidth = lineWidth;
        this.ctx.beginPath();
        this.ctx.arc(screen.x, screen.y, radius * this.scale, 0, Math.PI * 2);
        this.ctx.stroke();
    }

    drawGridLines(isVertical, spacing, isDotted = false) {
        this.ctx.strokeStyle = isDotted ? 'rgba(255, 255, 255, 0.15)' : 'rgba(255, 255, 255, 0.1)';
        this.ctx.lineWidth = 1;
        if (isDotted) this.ctx.setLineDash([3, 3]);
        
        for (let i = -10; i <= 10; i += spacing) {
            if (spacing === 0.5 && i === Math.floor(i)) continue;
            
            const p1 = isVertical ? this.toScreen(i, -10) : this.toScreen(-10, i);
            const p2 = isVertical ? this.toScreen(i, 10) : this.toScreen(10, i);
            this.ctx.beginPath();
            this.ctx.moveTo(p1.x, p1.y);
            this.ctx.lineTo(p2.x, p2.y);
            this.ctx.stroke();
        }
        
        if (isDotted) this.ctx.setLineDash([]);
    }

    adjustColor(rgbaString) {
        // Parse rgba string and adjust brightness
        const match = rgbaString.match(/rgba?\((\d+),\s*(\d+),\s*(\d+),?\s*([\d.]+)?\)/);
        if (!match) return rgbaString;
        
        let [, r, g, b, a] = match;
        r = Math.min(255, Math.floor(parseInt(r) * this.brightnessMultiplier));
        g = Math.min(255, Math.floor(parseInt(g) * this.brightnessMultiplier));
        b = Math.min(255, Math.floor(parseInt(b) * this.brightnessMultiplier));
        a = a || '1';
        
        return `rgba(${r}, ${g}, ${b}, ${a})`;
    }

    drawGrid(showGrid) {
        if (!showGrid) return;

        this.drawGridLines(true, 0.5, true);
        this.drawGridLines(false, 0.5, true);
        this.drawGridLines(true, 1);
        this.drawGridLines(false, 1);

        this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 255, 0.3)');
        this.ctx.lineWidth = 2;
        this.ctx.beginPath();
        
        let axis1 = this.toScreen(-10, 0);
        let axis2 = this.toScreen(10, 0);
        this.ctx.moveTo(axis1.x, axis1.y);
        this.ctx.lineTo(axis2.x, axis2.y);
        
        axis1 = this.toScreen(0, -10);
        axis2 = this.toScreen(0, 10);
        this.ctx.moveTo(axis1.x, axis1.y);
        this.ctx.lineTo(axis2.x, axis2.y);
        
        this.ctx.stroke();
    }

    // Draw the fundamental tetrahedron - represents one half of the Stella Octangula
    // In SU(3) terms: the three vertices represent the Color Charge triplet (R, G, B)
    // The opposing tetrahedron (when mirrored) represents the Anti-Color triplet
    // Together they form the complete SU(3) weight diagram (Eightfold Way geometry)
    drawTetrahedron(size, showTetrahedron, showColoredSides, showReferencePoints, showInscribedCircle, colorFieldPositions = null) {
        if (!showTetrahedron) return null;

        // Equilateral triangle geometry - the 2D cross-section of the tetrahedron
        // Height ratio follows from SU(3) weight diagram proportions
        const height = size * Math.sqrt(3) / 2;
        // Vertices positioned at SU(3) weight diagram coordinates
        const vertices = [
            { x: 0, y: height * 2 / 3 },
            { x: -size / 2, y: -height * 1 / 3 },
            { x: size / 2, y: -height * 1 / 3 }
        ];

        if (showColoredSides) {
            // Three colored faces represent the three color charges of QCD
            // Red, Green, Blue - the fundamental representation of SU(3)
            const colors = [
                'rgba(255, 0, 0, 0.2)',
                'rgba(0, 255, 0, 0.2)',
                'rgba(0, 0, 255, 0.2)'
            ];

            for (let i = 0; i < vertices.length; i++) {
                const v1 = vertices[i];
                const v2 = vertices[(i + 1) % vertices.length];
                const center = { x: 0, y: 0 };

                const v1Screen = this.toScreen(v1.x, v1.y);
                const v2Screen = this.toScreen(v2.x, v2.y);
                const centerScreen = this.toScreen(center.x, center.y);

                this.ctx.fillStyle = this.adjustColor(colors[i]);
                this.ctx.beginPath();
                this.ctx.moveTo(centerScreen.x, centerScreen.y);
                this.ctx.lineTo(v1Screen.x, v1Screen.y);
                this.ctx.lineTo(v2Screen.x, v2Screen.y);
                this.ctx.closePath();
                this.ctx.fill();
            }
        }

        this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 255, 0.5)');
        this.ctx.lineWidth = 2;
        this.ctx.beginPath();

        for (let i = 0; i < vertices.length; i++) {
            const v1 = this.toScreen(vertices[i].x, vertices[i].y);
            const v2 = this.toScreen(vertices[(i + 1) % vertices.length].x, vertices[(i + 1) % vertices.length].y);

            if (i === 0) {
                this.ctx.moveTo(v1.x, v1.y);
            }
            this.ctx.lineTo(v2.x, v2.y);
        }

        this.ctx.closePath();
        this.ctx.stroke();

        this.drawPoint(0, 0, 4, 'rgba(255, 255, 255, 0.5)');

        if (showReferencePoints) {
            const refColors = [
                'rgba(255, 255, 255, 1)',
                'rgba(255, 255, 255, 1)',
                'rgba(255, 255, 255, 1)'
            ];

            for (let i = 0; i < vertices.length; i++) {
                const v = vertices[i];
                const midX = (v.x + 0) / 2;
                const midY = (v.y + 0) / 2;
                this.drawPoint(midX, midY, 4, refColors[i], 'rgba(255, 255, 255, 0.8)', 1);
            }
        }

        if (showInscribedCircle) {
            // BAG MODEL BOUNDARY (MIT Bag Model)
            // Represents the QCD vacuum confinement boundary where:
            // E_total = E_kinetic + BV (B = vacuum pressure constant, V = bag volume)
            // Inside: quarks move freely. Outside: vacuum pressure confines them.
            // The boundary is where internal kinetic energy balances external vacuum pressure
            const inscribedRadius = height / 3;
            
            // Calculate chiral convergence for pulsing effect
            // Boundary brightens based on COMBINED convergence of all three color fields
            // The bag boundary emerges from collective SU(3) dynamics
            let chiralConvergence = 0;
            if (colorFieldPositions) {
                const colorFieldCenterPos = 1/3; // Center position in the phase cycle
                // Measure proximity to center (0.333) - peaks when field is AT center
                const getConvergenceToCenter = (pos) => {
                    // Distance from center position (0.333)
                    const distFromCenter = Math.abs(pos - colorFieldCenterPos);
                    // Convert to convergence: 1 at center, 0 at vertices
                    // Use a window of ~0.15 around center for smooth transition
                    const window = 0.15;
                    if (distFromCenter <= window) {
                        return 1 - (distFromCenter / window);
                    }
                    return 0;
                };
                // Max of all three fields - brightness peaks when ANY field reaches center
                // This happens 3 times per cycle (at 0°, 120°, 240°)
                chiralConvergence = Math.max(
                    getConvergenceToCenter(colorFieldPositions.red),
                    getConvergenceToCenter(colorFieldPositions.green),
                    getConvergenceToCenter(colorFieldPositions.blue)
                );
            }
            
            // Boundary pulses as fields approach tipping point (Spontaneous Symmetry Breaking)
            const baseOpacity = 0.3 + chiralConvergence * 0.5;
            const lineWidth = 2 + chiralConvergence * 1.5;
            
            // Use bluish color to match vacuum pressure visualization
            const boundaryColor = `rgba(150, 180, 255, ${baseOpacity})`;
            
            this.ctx.setLineDash([]);
            this.drawCircle(0, 0, inscribedRadius, this.adjustColor(boundaryColor), lineWidth);
        }

        return vertices;
    }

    drawFieldDepression(radius, color, edgeIndex, vertices, depressionDepth, depressionWidthDegrees, edgeCurveAmount, intermediateBlend, intermediateDepth, showControlPoints, showDepressionStates = false, hideNonDeformable = false) {
        // Field Depression: Implements the "Pressure-Depression Mechanism" where opposing field colors
        // create pressure that depresses unlike fields toward the opposing tetrahedral apex
        const v1 = vertices[edgeIndex];
        const v2 = vertices[(edgeIndex + 1) % vertices.length];

        const edgeMidX = (v1.x + v2.x) / 2;
        const edgeMidY = (v1.y + v2.y) / 2;
        const edgeAngle = Math.atan2(edgeMidY, edgeMidX);
        const depressionWidthRad = (depressionWidthDegrees * Math.PI) / 180;
        
        // Draw intermediate depression states (ghost layers showing the field being pushed)
        // Visualizes the "tipping point" transition from virtual to observable state
        if (showDepressionStates && depressionDepth >= 0.35) {
            const depressionStates = [
                { depth: 0.35, opacity: 0.35 },
                { depth: 0.40, opacity: 0.40 },
                { depth: 0.45, opacity: 0.45 }
            ];

            for (const state of depressionStates) {
                // Only draw this state if the current depression is greater than or equal to it
                if (depressionDepth >= state.depth) {
                    this.drawDepressionLayer(
                        radius, color, edgeIndex, vertices, state.depth,
                        depressionWidthDegrees, edgeCurveAmount, intermediateBlend, intermediateDepth,
                        state.opacity, hideNonDeformable
                    );
                }
            }
        }

        const angle1 = edgeAngle - depressionWidthRad / 2;
        const p1x = Math.cos(angle1) * radius;
        const p1y = Math.sin(angle1) * radius;

        const angle2 = edgeAngle;
        const p2x = Math.cos(angle2) * radius;
        const p2y = Math.sin(angle2) * radius;

        // Depression curves toward the opposing tetrahedral apex (geometric opposition)
        const oppositeVertex = vertices[(edgeIndex + 2) % vertices.length];
        const controlDepth = depressionDepth * 2;
        let cp2x, cp2y;

        if (controlDepth <= 1.0) {
            cp2x = p2x * (1 - controlDepth);
            cp2y = p2y * (1 - controlDepth);
        } else {
            const t = controlDepth - 1.0;
            cp2x = oppositeVertex.x * t;
            cp2y = oppositeVertex.y * t;
        }

        const angle3 = edgeAngle + depressionWidthRad / 2;
        const p3x = Math.cos(angle3) * radius;
        const p3y = Math.sin(angle3) * radius;

        this.ctx.strokeStyle = this.adjustColor(color);
        this.ctx.lineWidth = 2;
        this.ctx.beginPath();

        const tangentAngle1 = angle1 + Math.PI / 2;
        const cp1Distance = radius * edgeCurveAmount;
        const cp1x = p1x + Math.cos(tangentAngle1) * cp1Distance;
        const cp1y = p1y + Math.sin(tangentAngle1) * cp1Distance;

        const tangentAngle3 = angle3 - Math.PI / 2;
        const cp3Distance = radius * edgeCurveAmount;
        const cp3x = p3x + Math.cos(tangentAngle3) * cp3Distance;
        const cp3y = p3y + Math.sin(tangentAngle3) * cp3Distance;

        const deformDirX = oppositeVertex.x - p2x;
        const deformDirY = oppositeVertex.y - p2y;
        const deformDirLength = Math.sqrt(deformDirX * deformDirX + deformDirY * deformDirY);

        const perpX = -deformDirY / deformDirLength;
        const perpY = deformDirX / deformDirLength;

        const intermediateDistance = radius * intermediateBlend * 0.5;

        let cp1_intermediateX = cp2x + perpX * intermediateDistance;
        let cp1_intermediateY = cp2y + perpY * intermediateDistance;
        let cp3_intermediateX = cp2x - perpX * intermediateDistance;
        let cp3_intermediateY = cp2y - perpY * intermediateDistance;

        cp1_intermediateX = cp1_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp1_intermediateY = cp1_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;
        cp3_intermediateX = cp3_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp3_intermediateY = cp3_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;

        const p3Screen = this.toScreen(p3x, p3y);
        const p1ScreenForPath = this.toScreen(p1x, p1y);

        // Only draw the non-deformable arc if not hidden
        if (!hideNonDeformable) {
            this.ctx.moveTo(p3Screen.x, p3Screen.y);

            const startAngle = angle3;
            const endAngle = angle1 + Math.PI * 2;
            const numSegments = 30;

            for (let i = 1; i <= numSegments; i++) {
                const t = i / numSegments;
                const angle = startAngle + (endAngle - startAngle) * t;
                const x = Math.cos(angle) * radius;
                const y = Math.sin(angle) * radius;
                const p = this.toScreen(x, y);
                this.ctx.lineTo(p.x, p.y);
            }
        } else {
            // When hiding non-deformable section, start the path at p1 (the start of the deformable section)
            this.ctx.moveTo(p1ScreenForPath.x, p1ScreenForPath.y);
        }

        const cp1Screen = this.toScreen(cp1x, cp1y);
        const cp2Screen = this.toScreen(cp2x, cp2y);
        const cp3Screen = this.toScreen(cp3x, cp3y);
        const cp1_intScreen = this.toScreen(cp1_intermediateX, cp1_intermediateY);
        const cp3_intScreen = this.toScreen(cp3_intermediateX, cp3_intermediateY);
        const p3Screen2 = this.toScreen(p3x, p3y);

        this.ctx.bezierCurveTo(cp1Screen.x, cp1Screen.y, cp1_intScreen.x, cp1_intScreen.y, cp2Screen.x, cp2Screen.y);
        this.ctx.bezierCurveTo(cp3_intScreen.x, cp3_intScreen.y, cp3Screen.x, cp3Screen.y, p3Screen2.x, p3Screen2.y);
        this.ctx.stroke();

        if (showControlPoints) {
            const p1Screen = this.toScreen(p1x, p1y);
            const p2Screen = this.toScreen(p2x, p2y);

            this.drawPoint(cp1_intermediateX, cp1_intermediateY, 4, 'purple');
            this.drawPoint(cp3_intermediateX, cp3_intermediateY, 4, 'purple');
            this.drawPoint(cp1x, cp1y, 5, 'orange');
            this.drawPoint(cp3x, cp3y, 5, 'orange');
            this.drawPoint(cp2x, cp2y, 6, 'yellow');
            this.drawPoint(p1x, p1y, 4, 'cyan');
            this.drawPoint(p3x, p3y, 4, 'cyan');
            this.drawPoint(p2x, p2y, 4, 'rgba(255, 255, 255, 0.5)');

            this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 0, 0.5)');
            this.ctx.lineWidth = 1;
            this.ctx.beginPath();
            this.ctx.moveTo(p1Screen.x, p1Screen.y);
            this.ctx.lineTo(cp1Screen.x, cp1Screen.y);
            this.ctx.lineTo(cp1_intScreen.x, cp1_intScreen.y);
            this.ctx.lineTo(cp2Screen.x, cp2Screen.y);
            this.ctx.lineTo(cp3_intScreen.x, cp3_intScreen.y);
            this.ctx.lineTo(cp3Screen.x, cp3Screen.y);
            this.ctx.lineTo(p3Screen.x, p3Screen.y);
            this.ctx.stroke();

            this.ctx.strokeStyle = this.adjustColor('rgba(255, 0, 255, 0.5)');
            this.ctx.setLineDash([5, 5]);
            this.ctx.beginPath();
            this.ctx.moveTo(p2Screen.x, p2Screen.y);
            this.ctx.lineTo(cp2Screen.x, cp2Screen.y);
            this.ctx.stroke();
            this.ctx.setLineDash([]);
        }

        // Only draw the reference circle if not hiding non-deformable section
        if (!hideNonDeformable) {
            this.drawCircle(0, 0, radius, color.replace('1)', '0.2)'), 1);
        }
    }

    // Helper method to draw a single depression layer at a specific depth with custom opacity
    // Represents intermediate states during the symmetry breaking transition
    drawDepressionLayer(radius, color, edgeIndex, vertices, depressionDepth, depressionWidthDegrees, edgeCurveAmount, intermediateBlend, intermediateDepth, opacity, hideNonDeformable = false) {
        const v1 = vertices[edgeIndex];
        const v2 = vertices[(edgeIndex + 1) % vertices.length];

        const edgeMidX = (v1.x + v2.x) / 2;
        const edgeMidY = (v1.y + v2.y) / 2;
        const edgeAngle = Math.atan2(edgeMidY, edgeMidX);
        const depressionWidthRad = (depressionWidthDegrees * Math.PI) / 180;

        const angle1 = edgeAngle - depressionWidthRad / 2;
        const p1x = Math.cos(angle1) * radius;
        const p1y = Math.sin(angle1) * radius;

        const angle2 = edgeAngle;
        const p2x = Math.cos(angle2) * radius;
        const p2y = Math.sin(angle2) * radius;

        const oppositeVertex = vertices[(edgeIndex + 2) % vertices.length];
        const controlDepth = depressionDepth * 2;
        let cp2x, cp2y;

        if (controlDepth <= 1.0) {
            cp2x = p2x * (1 - controlDepth);
            cp2y = p2y * (1 - controlDepth);
        } else {
            const t = controlDepth - 1.0;
            cp2x = oppositeVertex.x * t;
            cp2y = oppositeVertex.y * t;
        }

        const angle3 = edgeAngle + depressionWidthRad / 2;
        const p3x = Math.cos(angle3) * radius;
        const p3y = Math.sin(angle3) * radius;

        // Apply opacity to the color
        const layerColor = color.replace(/rgba?\((\d+),\s*(\d+),\s*(\d+),?\s*[\d.]*\)?/, `rgba($1, $2, $3, ${opacity})`);

        this.ctx.strokeStyle = this.adjustColor(layerColor);
        this.ctx.lineWidth = 1.5;
        this.ctx.beginPath();

        const tangentAngle1 = angle1 + Math.PI / 2;
        const cp1Distance = radius * edgeCurveAmount;
        const cp1x = p1x + Math.cos(tangentAngle1) * cp1Distance;
        const cp1y = p1y + Math.sin(tangentAngle1) * cp1Distance;

        const tangentAngle3 = angle3 - Math.PI / 2;
        const cp3Distance = radius * edgeCurveAmount;
        const cp3x = p3x + Math.cos(tangentAngle3) * cp3Distance;
        const cp3y = p3y + Math.sin(tangentAngle3) * cp3Distance;

        const deformDirX = oppositeVertex.x - p2x;
        const deformDirY = oppositeVertex.y - p2y;
        const deformDirLength = Math.sqrt(deformDirX * deformDirX + deformDirY * deformDirY);

        const perpX = -deformDirY / deformDirLength;
        const perpY = deformDirX / deformDirLength;

        const intermediateDistance = radius * intermediateBlend * 0.5;

        let cp1_intermediateX = cp2x + perpX * intermediateDistance;
        let cp1_intermediateY = cp2y + perpY * intermediateDistance;
        let cp3_intermediateX = cp2x - perpX * intermediateDistance;
        let cp3_intermediateY = cp2y - perpY * intermediateDistance;

        cp1_intermediateX = cp1_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp1_intermediateY = cp1_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;
        cp3_intermediateX = cp3_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp3_intermediateY = cp3_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;

        const p3Screen = this.toScreen(p3x, p3y);
        const p1ScreenForPath = this.toScreen(p1x, p1y);

        // Only draw the non-deformable arc if not hidden
        if (!hideNonDeformable) {
            this.ctx.moveTo(p3Screen.x, p3Screen.y);

            const startAngle = angle3;
            const endAngle = angle1 + Math.PI * 2;
            const numSegments = 30;

            for (let i = 1; i <= numSegments; i++) {
                const t = i / numSegments;
                const angle = startAngle + (endAngle - startAngle) * t;
                const x = Math.cos(angle) * radius;
                const y = Math.sin(angle) * radius;
                const p = this.toScreen(x, y);
                this.ctx.lineTo(p.x, p.y);
            }
        } else {
            // When hiding non-deformable section, start the path at p1 (the start of the deformable section)
            this.ctx.moveTo(p1ScreenForPath.x, p1ScreenForPath.y);
        }

        const cp1Screen = this.toScreen(cp1x, cp1y);
        const cp2Screen = this.toScreen(cp2x, cp2y);
        const cp3Screen = this.toScreen(cp3x, cp3y);
        const cp1_intScreen = this.toScreen(cp1_intermediateX, cp1_intermediateY);
        const cp3_intScreen = this.toScreen(cp3_intermediateX, cp3_intermediateY);
        const p3Screen2 = this.toScreen(p3x, p3y);

        this.ctx.bezierCurveTo(cp1Screen.x, cp1Screen.y, cp1_intScreen.x, cp1_intScreen.y, cp2Screen.x, cp2Screen.y);
        this.ctx.bezierCurveTo(cp3_intScreen.x, cp3_intScreen.y, cp3Screen.x, cp3Screen.y, p3Screen2.x, p3Screen2.y);
        this.ctx.stroke();
    }

    drawVacuumPressurePoints(vertices, tetSize, redColorFieldPos, greenColorFieldPos, blueColorFieldPos) {
        // VACUUM PRESSURE POINTS (Bag Model): Positioned OPPOSITE to their corresponding color field
        // Represents the QCD vacuum pressure that confines quarks within the "bag"
        // The boundary where internal kinetic energy balances external vacuum pressure (B)
        // E_total = E_kinetic + BV (where B is the vacuum pressure constant)
        
        // Calculate the inscribed circle radius (same as in drawTetrahedron)
        const height = tetSize * Math.sqrt(3) / 2;
        const inscribedRadius = height / 3;
        const center = { x: 0, y: 0 };
        
        // Helper to get field position in world coordinates
        const getColorFieldPosition = (faceIndex, colorFieldPosition) => {
            const v1 = vertices[faceIndex];
            const v2 = vertices[(faceIndex + 1) % vertices.length];
            const t = colorFieldPosition;
            
            let fieldX, fieldY;
            if (t <= 0.333333) {
                const localT = t / 0.333333;
                fieldX = v1.x + (center.x - v1.x) * localT;
                fieldY = v1.y + (center.y - v1.y) * localT;
            } else if (t <= 0.666666) {
                const localT = (t - 0.333333) / 0.333333;
                fieldX = center.x + (v2.x - center.x) * localT;
                fieldY = center.y + (v2.y - center.y) * localT;
            } else {
                const localT = (t - 0.666666) / 0.333333;
                fieldX = v2.x + (v1.x - v2.x) * localT;
                fieldY = v2.y + (v1.y - v2.y) * localT;
            }
            return { x: fieldX, y: fieldY };
        };
        
        // Get each color field's position
        const redField = getColorFieldPosition(0, redColorFieldPos);
        const greenField = getColorFieldPosition(1, greenColorFieldPos);
        const blueField = getColorFieldPosition(2, blueColorFieldPos);
        
        // Calculate photon point position - opposite to color field on the inscribed circle
        const getPhotonPosition = (field) => {
            // Get angle from center to field
            const angleToField = Math.atan2(field.y, field.x);
            // Photon is on the opposite side (+ π)
            const photonAngle = angleToField + Math.PI;
            return {
                x: Math.cos(photonAngle) * inscribedRadius,
                y: Math.sin(photonAngle) * inscribedRadius,
                angle: photonAngle
            };
        };
        
        const redPhoton = getPhotonPosition(redField);
        const greenPhoton = getPhotonPosition(greenField);
        const bluePhoton = getPhotonPosition(blueField);
        
        // Draw the gauge boson interaction points (gluon exchange visualization)
        // In QCD, gluons mediate the color force between quarks
        const drawGaugeBosonPoint = (photon, color) => {
            this.drawPoint(photon.x, photon.y, 6, color.replace('1)', '0.9)'), 'rgba(255, 255, 255, 0.8)', 1.5);
        };
        
        // Draw flux tube (color field line) from center to gauge boson point
        const drawFluxTube = (field, photon, color) => {
            const centerScreen = this.toScreen(0, 0);
            const photonScreen = this.toScreen(photon.x, photon.y);
            
            this.ctx.strokeStyle = this.adjustColor(color.replace('1)', '0.4)'));
            this.ctx.lineWidth = 1;
            this.ctx.setLineDash([3, 3]);
            this.ctx.beginPath();
            this.ctx.moveTo(centerScreen.x, centerScreen.y);
            this.ctx.lineTo(photonScreen.x, photonScreen.y);
            this.ctx.stroke();
            this.ctx.setLineDash([]);
        };
        
        // Draw flux tubes first (behind gauge boson points)
        drawFluxTube(redField, redPhoton, 'rgba(255, 100, 100, 1)');
        drawFluxTube(greenField, greenPhoton, 'rgba(100, 255, 100, 1)');
        drawFluxTube(blueField, bluePhoton, 'rgba(100, 100, 255, 1)');
        
        // Draw all 3 gauge boson interaction points
        drawGaugeBosonPoint(redPhoton, 'rgba(255, 100, 100, 1)');
        drawGaugeBosonPoint(greenPhoton, 'rgba(100, 255, 100, 1)');
        drawGaugeBosonPoint(bluePhoton, 'rgba(100, 100, 255, 1)');
    }

    drawTopologicalSoliton(redColorFieldPos, greenColorFieldPos, blueColorFieldPos) {
        // TOPOLOGICAL SOLITON (Skyrmion): Stable interference node representing baryonic matter
        // In Skyrme Model terms: a stable, knotted configuration of the chiral field
        // ROTATES as the color fields converge - driven by the Right-Handed Chiral Current
        // Represents pressure equilibrium where field depressions create persistent geometric patterns
        // The soliton creates balance between internal kinetic energy and external vacuum pressure
        
        // Color fields are offset by 1/3 phase, so they align at vertices when:
        // Red=0, Green=0.333, Blue=0.666 (all at their starting vertices)
        // This happens at positions 0, 0.333, 0.666 in the cycle
        
        // PHASE STRUCTURE ROTATION (not matter rotation!)
        //
        // IMPORTANT: The soliton CORE is stationary (Theorem 0.2.3: stable fixed point).
        // The center is a global attractor with negative eigenvalues (λ₁ = -3K/8, λ₂ = -9K/8).
        // What rotates is the PHASE STRUCTURE — visualizing which color field is currently
        // converging to center.
        //
        // WHY 3× rotation rate?
        //   - Each color field (R, G, B) reaches center ONCE per cycle
        //   - Three convergence events per R→G→B cycle
        //   - Phase indicator arcs rotate ONCE per convergence event
        //   - Total: 3 rotations per cycle
        //
        // Physical basis: Theorem 2.2.2 establishes the limit cycle where all phases
        // advance uniformly (dφ_c/dt = ω) while maintaining 120° separation.
        // The rotating arcs show this phase evolution, not physical matter rotation.
        //
        // Driven by the Right-Handed Chiral Current (J_5^μ)
        // Negative angle enforces clockwise rotation (right-handed chirality)
        const chiralHelixAngle = -redColorFieldPos * 2 * Math.PI * 3;
        
        // Calculate phase-locked alignment - measures proximity to SU(3) weight diagram vertices
        // Vertex positions for each field: 0, 0.333, 0.666 (corresponding to the Stella Octangula points)
        const getPhaseAlignment = (pos) => {
            // Normalize position to 0-1
            const p = ((pos % 1.0) + 1.0) % 1.0;
            // Distance to nearest vertex (0, 0.333, 0.666) in the SU(3) weight diagram
            const d1 = Math.min(p, 1.0 - p); // distance to 0
            const d2 = Math.abs(p - 0.333333);
            const d3 = Math.abs(p - 0.666666);
            const minDist = Math.min(d1, d2, d3);
            // Convert to alignment: 0 = at vertex, 1 = between vertices
            // Peak width ~0.1 around each vertex
            return Math.max(0, 1.0 - minDist / 0.15);
        };
        
        const redPhaseAlignment = getPhaseAlignment(redColorFieldPos);
        const greenPhaseAlignment = getPhaseAlignment(greenColorFieldPos);
        const bluePhaseAlignment = getPhaseAlignment(blueColorFieldPos);
        
        // Phase-locked alignment - the three-phase symmetry (like a three-phase motor)
        const phaseAlignmentStrength = (redPhaseAlignment + greenPhaseAlignment + bluePhaseAlignment) / 3;
        
        // Chiral convergence: measures proximity to center where spacetime emerges
        // At center (position 0.333), all pressure gradients converge - the "generative vacuum"
        // Each color field reaches center once per cycle, creating 3 convergence events
        const centerPos = 1/3;
        const convergenceWindow = 0.15; // Window around center for smooth transition
        const getChiralConvergence = (pos) => {
            const p = ((pos % 1.0) + 1.0) % 1.0;
            const distFromCenter = Math.abs(p - centerPos);
            // Peak convergence when field is at center (pos = 0.333)
            if (distFromCenter <= convergenceWindow) {
                return 1 - (distFromCenter / convergenceWindow);
            }
            return 0;
        };

        const redConvergence = getChiralConvergence(redColorFieldPos);
        const greenConvergence = getChiralConvergence(greenColorFieldPos);
        const blueConvergence = getChiralConvergence(blueColorFieldPos);
        
        // Vacuum energy density - the non-zero energy of the Right-Handed Boundary Condensate (RBC)
        const vacuumEnergyDensity = (redConvergence + greenConvergence + blueConvergence) / 3;
        
        const centerScreen = this.toScreen(0, 0);
        
        // ========================================
        // VACUUM PRESSURE GRADIENT VISUALIZATION (Bag Model)
        // Shows inward pressure from the QCD vacuum - the "external vacuum pressure (B)"
        // Pressure increases toward center, confining the soliton within the bag
        // Lines are STATIC (don't rotate) - represents the constant, pervasive vacuum condensate
        // ========================================
        
        const pressureOuterRadius = 55 + vacuumEnergyDensity * 10;
        const pressureInnerRadius = 8;
        const numPressureLines = 12;
        
        // Draw converging pressure gradient lines (STATIC - no rotation)
        for (let i = 0; i < numPressureLines; i++) {
            const angle = (i / numPressureLines) * 2 * Math.PI; // No rotation added
            
            // Outer point (where pressure originates)
            const outerX = centerScreen.x + Math.cos(angle) * pressureOuterRadius;
            const outerY = centerScreen.y + Math.sin(angle) * pressureOuterRadius;
            
            // Inner point (converging toward center)
            const innerX = centerScreen.x + Math.cos(angle) * pressureInnerRadius;
            const innerY = centerScreen.y + Math.sin(angle) * pressureInnerRadius;
            
            // Create gradient along each line (fades as it approaches center)
            const lineGradient = this.ctx.createLinearGradient(outerX, outerY, innerX, innerY);
            const baseOpacity = 0.08 + vacuumEnergyDensity * 0.12;
            lineGradient.addColorStop(0, `rgba(100, 150, 255, ${baseOpacity * 0.3})`);
            lineGradient.addColorStop(0.5, `rgba(150, 180, 255, ${baseOpacity * 0.7})`);
            lineGradient.addColorStop(0.85, `rgba(200, 220, 255, ${baseOpacity})`);
            lineGradient.addColorStop(1, `rgba(255, 255, 255, 0)`);
            
            this.ctx.strokeStyle = lineGradient;
            this.ctx.lineWidth = 1 + vacuumEnergyDensity * 0.5;
            this.ctx.beginPath();
            this.ctx.moveTo(outerX, outerY);
            this.ctx.lineTo(innerX, innerY);
            this.ctx.stroke();
        }
        
        // Draw prominent inward-pointing arrows at 0°, 120°, 240° - STATIC
        // These align with the threefold symmetry of the tetrahedron
        const arrowAngles = [Math.PI / 2, 3 * Math.PI / 2, 0.84 * Math.PI, 0.16 * Math.PI, 1.84 * Math.PI, 1.16 * Math.PI,]; // 0°, 120°, 240°
        
        // Calculate chiral convergence during approach to center (tipping point)
        // Color fields travel: vertex (0) → center (0.333) → next vertex (0.666) → back (1.0)
        // Brightness peaks when ANY field is near center (0.333) - the "tipping point"
        const chiralCenterPos = 1/3;
        const chiralWindow = 0.15; // Window around center for smooth transition

        // For each color field, calculate proximity to center
        // This represents the energy concentration at the generative vacuum
        const getChiralCenterProximity = (pos) => {
            const distFromCenter = Math.abs(pos - chiralCenterPos);
            // Peak when field is at center (pos = 0.333)
            if (distFromCenter <= chiralWindow) {
                return 1 - (distFromCenter / chiralWindow);
            }
            return 0;
        };

        const redChiralConvergence = getChiralCenterProximity(redColorFieldPos);
        const greenChiralConvergence = getChiralCenterProximity(greenColorFieldPos);
        const blueChiralConvergence = getChiralCenterProximity(blueColorFieldPos);

        // Max chiral convergence - brightness peaks when ANY field reaches center
        const maxChiralConvergence = Math.max(redChiralConvergence, greenChiralConvergence, blueChiralConvergence);
        
        for (const angle of arrowAngles) {
            const arrowDistance = pressureOuterRadius * 0.55;
            const arrowX = centerScreen.x + Math.cos(angle) * arrowDistance;
            const arrowY = centerScreen.y + Math.sin(angle) * arrowDistance;
            
            // Arrow pointing inward - represents converging pressure gradients
            const arrowSize = 8 + vacuumEnergyDensity * 4;
            const arrowAngle = angle + Math.PI; // Point toward center
            
            // Arrows intensify as color fields approach the tipping point
            const arrowOpacity = 0.2 + maxChiralConvergence * 0.7 + vacuumEnergyDensity * 0.1;
            this.ctx.fillStyle = `rgba(180, 200, 255, ${arrowOpacity})`;
            this.ctx.beginPath();
            this.ctx.moveTo(
                arrowX + Math.cos(arrowAngle) * arrowSize,
                arrowY + Math.sin(arrowAngle) * arrowSize
            );
            this.ctx.lineTo(
                arrowX + Math.cos(arrowAngle + 2.5) * arrowSize * 0.6,
                arrowY + Math.sin(arrowAngle + 2.5) * arrowSize * 0.6
            );
            this.ctx.lineTo(
                arrowX + Math.cos(arrowAngle - 2.5) * arrowSize * 0.6,
                arrowY + Math.sin(arrowAngle - 2.5) * arrowSize * 0.6
            );
            this.ctx.closePath();
            this.ctx.fill();
        }
        
        // ========================================
        // SOLITON CORE VISUALIZATION (Emergent Matter)
        // ========================================
        
        // Draw the continuous background glow - the non-zero Vacuum Energy Density (ρ_vac)
        const baseGlowRadius = 10 + vacuumEnergyDensity * 12;
        const baseGlowOpacity = 0.15 + vacuumEnergyDensity * 0.25;
        
        const baseGradient = this.ctx.createRadialGradient(
            centerScreen.x, centerScreen.y, 0,
            centerScreen.x, centerScreen.y, baseGlowRadius
        );
        baseGradient.addColorStop(0, `rgba(200, 200, 255, ${baseGlowOpacity})`);
        baseGradient.addColorStop(0.6, `rgba(150, 150, 200, ${baseGlowOpacity * 0.4})`);
        baseGradient.addColorStop(1, 'rgba(100, 100, 150, 0)');
        
        this.ctx.fillStyle = baseGradient;
        this.ctx.beginPath();
        this.ctx.arc(centerScreen.x, centerScreen.y, baseGlowRadius, 0, Math.PI * 2);
        this.ctx.fill();
        
        // Draw phase-locked pulse - bright flash at three-phase symmetry points
        // Represents the moment when all chiral currents reach vertex equilibrium
        if (phaseAlignmentStrength > 0.3) {
            const pulseRadius = 6 + phaseAlignmentStrength * 18;
            const pulseOpacity = phaseAlignmentStrength * 0.7;
            
            const pulseGradient = this.ctx.createRadialGradient(
                centerScreen.x, centerScreen.y, 0,
                centerScreen.x, centerScreen.y, pulseRadius
            );
            pulseGradient.addColorStop(0, `rgba(255, 255, 255, ${pulseOpacity})`);
            pulseGradient.addColorStop(0.4, `rgba(255, 240, 200, ${pulseOpacity * 0.6})`);
            pulseGradient.addColorStop(1, 'rgba(255, 200, 100, 0)');
            
            this.ctx.fillStyle = pulseGradient;
            this.ctx.beginPath();
            this.ctx.arc(centerScreen.x, centerScreen.y, pulseRadius, 0, Math.PI * 2);
            this.ctx.fill();
        }
        
        // Draw stable core - the topological soliton (Skyrmion) itself
        // This is the "knot" in spacetime that cannot be untied due to geometric twist
        // The Winding Number (topological charge) determines if it's matter or antimatter
        // Proton stability comes from the conservation of this topological charge
        const coreRadius = 3 + phaseAlignmentStrength * 4;
        const coreOpacity = 0.3 + phaseAlignmentStrength * 0.7;
        
        this.ctx.fillStyle = `rgba(255, 255, 255, ${coreOpacity})`;
        this.ctx.beginPath();
        this.ctx.arc(centerScreen.x, centerScreen.y, coreRadius, 0, Math.PI * 2);
        this.ctx.fill();
        
        // Draw phase indicator arcs - shows the R→G→B right-handed cycle phase
        // The arcs rotate WITH the soliton, driven by the Chiral Helical Current
        // This visualizes the Chiral Lagrangian's phase evolution: ℒ_Chiral
        const arcRadius = 18 + vacuumEnergyDensity * 6;
        const arcWidth = Math.PI * 0.5; // Each arc spans 90 degrees (three-phase symmetry)
        
        // Base angle for arcs - includes chiral helix rotation
        const arcBaseAngle = -Math.PI/2 + Math.PI/3 + chiralHelixAngle;
        
        const drawPhaseArc = (intensity, startAngle, color) => {
            const arcOpacity = 0.2 + intensity * 0.6;
            const arcThickness = 1.5 + intensity * 2.5;
            
            this.ctx.strokeStyle = color.replace('1)', `${arcOpacity})`);
            this.ctx.lineWidth = arcThickness;
            this.ctx.lineCap = 'round';
            this.ctx.beginPath();
            this.ctx.arc(centerScreen.x, centerScreen.y, arcRadius, 
                        startAngle - arcWidth/2, startAngle + arcWidth/2);
            this.ctx.stroke();
        };
        
        // Position arcs at 120° intervals (SU(3) threefold symmetry)
        // B→G→R clockwise sequence - the irreversible right-handed phase cycle
        // Each "tick" of time is one phase rotation through this cycle
        drawPhaseArc(blueConvergence, arcBaseAngle, 'rgba(80, 80, 255, 1)');                    // Blue at base
        drawPhaseArc(greenConvergence, arcBaseAngle + 2*Math.PI/3, 'rgba(80, 255, 80, 1)');   // Green at base+120°
        drawPhaseArc(redConvergence, arcBaseAngle + 4*Math.PI/3, 'rgba(255, 80, 80, 1)');    // Red at base+240°
    }

    // ========================================
    // TORSION FIELD VISUALIZATION (Einstein-Cartan Gravity Extension)
    // Torsion T^λ_μν is proportional to the Right-Handed Chiral Current (J_5^μ)
    // This links matter's spin/chirality to geometric twist of emergent spacetime
    // Visualized as twisting distortion of concentric rings around the soliton
    // ========================================
    drawTorsionField(redColorFieldPos, greenColorFieldPos, blueColorFieldPos, tetSize) {
        const centerScreen = this.toScreen(0, 0);
        
        // Calculate Chiral Current strength (J_5^μ) - proportional to inward field motion
        const chiralCenterPos = 1/3;
        const getChiralCurrentStrength = (pos) => {
            if (pos <= chiralCenterPos) {
                return pos / chiralCenterPos;
            }
            return 0;
        };
        
        const redChiralCurrent = getChiralCurrentStrength(redColorFieldPos);
        const greenChiralCurrent = getChiralCurrentStrength(greenColorFieldPos);
        const blueChiralCurrent = getChiralCurrentStrength(blueColorFieldPos);
        
        // Torsion magnitude - peaks when ANY color field's chiral current is maximal
        const torsionMagnitude = Math.max(redChiralCurrent, greenChiralCurrent, blueChiralCurrent);
        
        // TORSION ROTATION: Geometric twist from the dominant chiral current
        // Normalized to ensure consistent torsion regardless of which color field is active
        // The twist angle represents the geometric distortion of emergent spacetime
        // Torsion(T) ∝ Chiral Current(J_5^μ) - links spin to geometry
        let torsionTwistAngle = 0;
        
        if (torsionMagnitude > 0) {
            // Torsion twist is proportional to the chiral current magnitude
            // Negative angle enforces right-handed chirality of the torsion field
            // One full twist (2π) corresponds to maximum chiral convergence
            torsionTwistAngle = -torsionMagnitude * 2 * Math.PI;
        }
        
        // Calculate inscribed circle radius for boundary
        const height = tetSize * Math.sqrt(3) / 2;
        const inscribedRadius = height / 3;
        const inscribedRadiusScreen = inscribedRadius * this.scale;
        
        // Draw twisted concentric rings showing torsion field structure
        // Inner rings twist more - torsion is strongest near the soliton core
        const numRings = 6;
        const maxRadius = inscribedRadiusScreen * 0.95;
        const minRadius = 15;
        
        for (let ring = 0; ring < numRings; ring++) {
            const ringProgress = ring / (numRings - 1);
            const radius = minRadius + (maxRadius - minRadius) * ringProgress;
            
            // Torsion falloff: stronger near center (the soliton), weaker at boundary
            // This represents the localized nature of spin-gravity coupling
            const torsionFalloff = (1 - ringProgress) * torsionMagnitude;
            const ringTwistAngle = torsionTwistAngle * torsionFalloff * 0.5;
            
            // Draw the twisted ring as a series of segments
            const numSegments = 36;
            const baseOpacity = 0.1 + torsionMagnitude * 0.15;
            const ringOpacity = baseOpacity * (0.3 + 0.7 * ringProgress); // Outer rings more visible
            
            this.ctx.strokeStyle = `rgba(180, 150, 255, ${ringOpacity})`;
            this.ctx.lineWidth = 1 + torsionMagnitude * 0.5;
            this.ctx.beginPath();
            
            for (let seg = 0; seg <= numSegments; seg++) {
                const segAngle = (seg / numSegments) * 2 * Math.PI;
                
                // Apply torsion twist - varies sinusoidally for wavy spacetime distortion
                const localTwist = ringTwistAngle * Math.sin(segAngle * 3 + torsionTwistAngle);
                const finalAngle = segAngle + localTwist;
                
                // Radial distortion from torsion - spacetime is not just twisted but stretched
                const radialDistortion = 1 + 0.03 * torsionMagnitude * Math.sin(segAngle * 3 + torsionTwistAngle * 2);
                const distortedRadius = radius * radialDistortion;
                
                const x = centerScreen.x + Math.cos(finalAngle) * distortedRadius;
                const y = centerScreen.y + Math.sin(finalAngle) * distortedRadius;
                
                if (seg === 0) {
                    this.ctx.moveTo(x, y);
                } else {
                    this.ctx.lineTo(x, y);
                }
            }
            
            this.ctx.stroke();
        }
        
        // Draw radial geodesics showing how torsion curves paths through spacetime
        // These represent the twisted null geodesics in torsioned spacetime
        const numRadialLines = 12;
        for (let i = 0; i < numRadialLines; i++) {
            const baseAngle = (i / numRadialLines) * 2 * Math.PI;
            
            const lineOpacity = 0.08 + torsionMagnitude * 0.12;
            this.ctx.strokeStyle = `rgba(200, 170, 255, ${lineOpacity})`;
            this.ctx.lineWidth = 1;
            this.ctx.beginPath();
            
            // Draw curved geodesic from center outward, twisted by torsion field
            const lineSegments = 20;
            for (let seg = 0; seg <= lineSegments; seg++) {
                const segProgress = seg / lineSegments;
                const segRadius = minRadius + (maxRadius - minRadius) * segProgress;
                
                // Torsion decreases with distance from soliton core
                const geodesicTwist = torsionTwistAngle * (1 - segProgress) * torsionMagnitude * 0.3;
                const angle = baseAngle + geodesicTwist;
                
                const x = centerScreen.x + Math.cos(angle) * segRadius;
                const y = centerScreen.y + Math.sin(angle) * segRadius;
                
                if (seg === 0) {
                    this.ctx.moveTo(x, y);
                } else {
                    this.ctx.lineTo(x, y);
                }
            }
            
            this.ctx.stroke();
        }
    }

    draw(params) {
        this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);

        this.drawGrid(params.showGrid);

        const vertices = this.drawTetrahedron(
            params.tetSize,
            params.showTetrahedron,
            params.showColoredSides,
            params.showReferencePoints,
            params.showInscribedCircle,
            {
                red: params.redColorFieldPosition,
                green: params.greenColorFieldPosition,
                blue: params.blueColorFieldPosition
            }
        );

        // Draw vacuum pressure points on inscribed circle
        if (vertices && params.showVacuumPressurePoints) {
            this.drawVacuumPressurePoints(
                vertices,
                params.tetSize,
                params.redColorFieldPosition,
                params.greenColorFieldPosition,
                params.blueColorFieldPosition
            );
        }

        // Draw torsion field (spacetime twist from chiral current)
        if (params.showTorsionField) {
            this.drawTorsionField(
                params.redColorFieldPosition,
                params.greenColorFieldPosition,
                params.blueColorFieldPosition,
                params.tetSize
            );
        }

        // Draw topological soliton (stable interference node) when fields converge
        if (params.showTopologicalSoliton) {
            this.drawTopologicalSoliton(
                params.redColorFieldPosition,
                params.greenColorFieldPosition,
                params.blueColorFieldPosition
            );
        }

        // Draw face color field points - the three color charges cycling through the geometry
        // Each color field follows a triangular path: vertex → center → next vertex → back
        // This path represents the color field's phase evolution in the R→G→B cycle
        if (vertices) {
            const center = { x: 0, y: 0 }; // The generative vacuum - where spacetime emerges
            
            // Helper function to draw a single color field (quark color charge visualization)
            const drawFaceColorField = (faceIndex, colorFieldPosition, color, showColorField) => {
                if (!showColorField) return;
                
                const v1 = vertices[faceIndex];
                const v2 = vertices[(faceIndex + 1) % vertices.length];
                
                let fieldX, fieldY;
                const t = colorFieldPosition;
                
                // Right-handed helical path around the triangular face perimeter:
                // v1 (t=0) → center (t=0.333, tipping point) → v2 (t=0.666) → v1 (t=1.0)
                // This traces one complete phase cycle of the chiral oscillation
                if (t <= 0.333333) {
                    // First segment: v1 to center
                    const localT = t / 0.333333;
                    fieldX = v1.x + (center.x - v1.x) * localT;
                    fieldY = v1.y + (center.y - v1.y) * localT;
                } else if (t <= 0.666666) {
                    // Second segment: center to v2
                    const localT = (t - 0.333333) / 0.333333;
                    fieldX = center.x + (v2.x - center.x) * localT;
                    fieldY = center.y + (v2.y - center.y) * localT;
                } else {
                    // Third segment: v2 back to v1 (completing the loop)
                    const localT = (t - 0.666666) / 0.333333;
                    fieldX = v2.x + (v1.x - v2.x) * localT;
                    fieldY = v2.y + (v1.y - v2.y) * localT;
                }
                
                // Draw the color field point with glow effect
                this.drawPoint(fieldX, fieldY, 5, color.replace('1)', '0.8)'), color, 2);
                
                // Draw a subtle line from center to color field point
                const centerScreen = this.toScreen(0, 0);
                const fieldScreen = this.toScreen(fieldX, fieldY);
                this.ctx.strokeStyle = this.adjustColor(color.replace('1)', '0.3)'));
                this.ctx.lineWidth = 1;
                this.ctx.setLineDash([3, 3]);
                this.ctx.beginPath();
                this.ctx.moveTo(centerScreen.x, centerScreen.y);
                this.ctx.lineTo(fieldScreen.x, fieldScreen.y);
                this.ctx.stroke();
                this.ctx.setLineDash([]);
                
                // Draw a faint trail showing the triangular path
                this.ctx.strokeStyle = this.adjustColor(color.replace('1)', '0.15)'));
                this.ctx.lineWidth = 1;
                this.ctx.setLineDash([2, 2]);
                this.ctx.beginPath();
                const v1Screen = this.toScreen(v1.x, v1.y);
                const v2Screen = this.toScreen(v2.x, v2.y);
                this.ctx.moveTo(v1Screen.x, v1Screen.y);
                this.ctx.lineTo(centerScreen.x, centerScreen.y);
                this.ctx.lineTo(v2Screen.x, v2Screen.y);
                this.ctx.lineTo(v1Screen.x, v1Screen.y);
                this.ctx.stroke();
                this.ctx.setLineDash([]);
            };
            
            // Draw all three face color fields
            drawFaceColorField(0, params.redColorFieldPosition, 'rgba(255, 0, 0, 1)', params.showRedColorField);
            drawFaceColorField(1, params.greenColorFieldPosition, 'rgba(0, 255, 0, 1)', params.showGreenColorField);
            drawFaceColorField(2, params.blueColorFieldPosition, 'rgba(0, 0, 255, 1)', params.showBlueColorField);
        }

        if (params.showFields && vertices) {
            if (params.circleDebugMode) {
                this.drawCircle(0, 0, params.radius, this.adjustColor('rgba(0, 255, 255, 1)'), 2);
                this.ctx.globalCompositeOperation = 'difference';
            }

            // Color field configurations - each represents one of the three QCD color charges
            // The deformation visualizes the Pressure-Depression Mechanism from field interactions
            const fieldConfigs = [
                { show: params.showRedField, color: 'rgba(255, 0, 0, 1)', index: 0, deformation: params.redDeformation, edgeCurve: params.redEdgeCurve, intermediateBlend: params.redIntermediateBlend, hideNonDeformable: params.hideRedNonDeformable || false },
                { show: params.showGreenField, color: 'rgba(0, 255, 0, 1)', index: 1, deformation: params.greenDeformation, edgeCurve: params.greenEdgeCurve, intermediateBlend: params.greenIntermediateBlend, hideNonDeformable: params.hideGreenNonDeformable || false },
                { show: params.showBlueField, color: 'rgba(0, 0, 255, 1)', index: 2, deformation: params.blueDeformation, edgeCurve: params.blueEdgeCurve, intermediateBlend: params.blueIntermediateBlend, hideNonDeformable: params.hideBlueNonDeformable || false }
            ];

            fieldConfigs.forEach(config => {
                if (config.show) {
                    this.drawFieldDepression(
                        params.radius,
                        config.color,
                        config.index,
                        vertices,
                        config.deformation,
                        params.deformWidth,
                        config.edgeCurve,
                        config.intermediateBlend,
                        params.intermediateDepth,
                        params.showControlPoints,
                        params.showDepressionStates,
                        config.hideNonDeformable
                    );
                }
            });

            if (params.circleDebugMode) {
                this.ctx.globalCompositeOperation = 'source-over';
            }
        }
    }
}

// ============================================
// ROTATED 90-DEGREE VIEW CLASS (Orthogonal SU(3) Cross-Section)
// Shows the Stella Octangula from the side (square cross-section view)
// This reveals the 4-fold symmetry hidden within the 3-fold color symmetry
// Represents an orthogonal slice through the SU(3) weight diagram
// ============================================

class TetrahedronVisualization90Degrees extends TetrahedronVisualization {
    constructor(canvas, isMirrored = false) {
        super(canvas, isMirrored);
    }

    // Override drawTetrahedron to show the 4-triangle cross-section
    // When viewing a stellated octahedron from the side (90° rotation),
    // you see 4 triangular sections forming an X pattern
    drawTetrahedron(size, showTetrahedron, showColoredSides, showReferencePoints, showInscribedCircle, colorFieldPositions = null) {
        if (!showTetrahedron) return null;

        // For a stellated octahedron rotated 90 degrees,
        // we see 4 triangular sections meeting at the center
        // This creates a square outline with diagonal divisions
        
        // Calculate the square size based on the tetrahedron size
        // For a stellated octahedron, the square's diagonal should equal
        // the triangle's edge length (size)
        // If diagonal = size, then side = size / sqrt(2)
        const squareSide = size / Math.sqrt(2);
        const squareHalfSize = squareSide / 2;
        
        // Square vertices - the orthogonal cross-section of the Stella Octangula
        // This view reveals the hidden 4-fold symmetry within the 3-fold color structure
        const vertices = [
            { x: -squareHalfSize, y: squareHalfSize },   // top-left
            { x: squareHalfSize, y: squareHalfSize },    // top-right
            { x: squareHalfSize, y: -squareHalfSize },   // bottom-right
            { x: -squareHalfSize, y: -squareHalfSize }   // bottom-left
        ];

        if (showColoredSides) {
            // Four triangular sections - orthogonal slice through the color field structure
            // Shows how color charges distribute in the perpendicular plane
            const colors = [
                'rgba(0, 255, 0, 0.2)',      // Green quadrant
                'rgba(150, 255, 150, 0.2)',  // Green-shifted (mixed state)
                'rgba(0, 0, 255, 0.2)',      // Blue quadrant
                'rgba(255, 0, 0, 0.2)',      // Red quadrant
            ];

            const center = { x: 0, y: 0 }; // Generative vacuum center

            // Draw 4 triangular sections from center to each corner
            for (let i = 0; i < 4; i++) {
                const v1 = vertices[i];
                const v2 = vertices[(i + 1) % vertices.length];

                const v1Screen = this.toScreen(v1.x, v1.y);
                const v2Screen = this.toScreen(v2.x, v2.y);
                const centerScreen = this.toScreen(center.x, center.y);

                this.ctx.fillStyle = this.adjustColor(colors[i]);
                this.ctx.beginPath();
                this.ctx.moveTo(centerScreen.x, centerScreen.y);
                this.ctx.lineTo(v1Screen.x, v1Screen.y);
                this.ctx.lineTo(v2Screen.x, v2Screen.y);
                this.ctx.closePath();
                this.ctx.fill();
            }
        }

        // Draw the square outline
        this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 255, 0.5)');
        this.ctx.lineWidth = 2;
        this.ctx.beginPath();

        for (let i = 0; i < vertices.length; i++) {
            const v1 = this.toScreen(vertices[i].x, vertices[i].y);
            const v2 = this.toScreen(vertices[(i + 1) % vertices.length].x, vertices[(i + 1) % vertices.length].y);

            if (i === 0) {
                this.ctx.moveTo(v1.x, v1.y);
            }
            this.ctx.lineTo(v2.x, v2.y);
        }

        this.ctx.closePath();
        this.ctx.stroke();

        // Draw the diagonal lines from center to vertices creating the X pattern
        const center = { x: 0, y: 0 };
        const centerScreen = this.toScreen(center.x, center.y);
        
        this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 255, 0.5)');
        this.ctx.lineWidth = 2;
        
        for (let i = 0; i < vertices.length; i++) {
            const vScreen = this.toScreen(vertices[i].x, vertices[i].y);
            this.ctx.beginPath();
            this.ctx.moveTo(centerScreen.x, centerScreen.y);
            this.ctx.lineTo(vScreen.x, vScreen.y);
            this.ctx.stroke();
        }

        // Draw center point
        this.drawPoint(0, 0, 4, 'rgba(255, 255, 255, 0.5)');

        if (showReferencePoints) {
            for (let i = 0; i < vertices.length; i++) {
                const v = vertices[i];
                const midX = (v.x + 0) / 2;
                const midY = (v.y + 0) / 2;
                this.drawPoint(midX, midY, 4, 'rgba(255, 255, 255, 1)', 'rgba(255, 255, 255, 0.8)', 1);
            }
        }

        if (showInscribedCircle) {
            // Bag Model Boundary - represents QCD vacuum confinement
            // For both views, use the same inscribed circle radius
            // This represents the sphere being sliced in both cross-sections
            const triangleHeight = size * Math.sqrt(3) / 2;
            const inscribedRadius = triangleHeight / 3;
            
            // Calculate maximum chiral convergence for boundary pulsing effect
            // Measures how close the three color fields are to simultaneous center arrival
            let maxChiralConvergence = 0;
            if (colorFieldPositions) {
                const colorFieldCenterPos = 1/3;
                const getInwardProximity = (pos) => {
                    if (pos <= colorFieldCenterPos) {
                        return pos / colorFieldCenterPos;
                    }
                    return 0;
                };
                maxChiralConvergence = Math.max(
                    getInwardProximity(colorFieldPositions.red),
                    getInwardProximity(colorFieldPositions.green),
                    getInwardProximity(colorFieldPositions.blue)
                );
            }
            
            // Boundary pulses brighter as color fields approach chiral convergence
            const baseOpacity = 0.3 + maxChiralConvergence * 0.5;
            const lineWidth = 2 + maxChiralConvergence * 1.5;
            
            // Use bluish color to match vacuum pressure visualization
            const boundaryColor = `rgba(150, 180, 255, ${baseOpacity})`;
            
            this.ctx.setLineDash([]);
            this.drawCircle(0, 0, inscribedRadius, this.adjustColor(boundaryColor), lineWidth);
        }

        // Return vertices with 4 points (square) instead of 3 (triangle)
        return vertices;
    }

    // Override drawFieldDepression to rotate the depression by 45 degrees counterclockwise (90° view)
    drawFieldDepression(radius, color, edgeIndex, vertices, depressionDepth, depressionWidthDegrees, edgeCurveAmount, intermediateBlend, intermediateDepth, showControlPoints) {
        // Get the edge vertices for this section
        const v1 = vertices[edgeIndex];
        const v2 = vertices[(edgeIndex + 1) % vertices.length];

        // Calculate edge midpoint (where the depression is centered)
        const edgeMidX = (v1.x + v2.x) / 2;
        const edgeMidY = (v1.y + v2.y) / 2;

        // Find angle to edge midpoint and rotate by 45 degrees counterclockwise
        let edgeAngle = Math.atan2(edgeMidY, edgeMidX);
        edgeAngle += Math.PI / 4; // Rotate 45 degrees counterclockwise

        // Convert depression width from degrees to radians
        const depressionWidthRad = (depressionWidthDegrees * Math.PI) / 180;

        // Calculate the three key points for the depression
        const angle1 = edgeAngle - depressionWidthRad / 2;
        const p1x = Math.cos(angle1) * radius;
        const p1y = Math.sin(angle1) * radius;

        const angle2 = edgeAngle;
        const p2x = Math.cos(angle2) * radius;
        const p2y = Math.sin(angle2) * radius;

        // Depression curves toward the opposing vertex (geometric opposition)
        const oppositeVertex = vertices[(edgeIndex + 2) % vertices.length];
        const controlDepth = depressionDepth * 2;
        let cp2x, cp2y;

        if (controlDepth <= 1.0) {
            cp2x = p2x * (1 - controlDepth);
            cp2y = p2y * (1 - controlDepth);
        } else {
            const t = controlDepth - 1.0;
            cp2x = oppositeVertex.x * t;
            cp2y = oppositeVertex.y * t;
        }

        const angle3 = edgeAngle + depressionWidthRad / 2;
        const p3x = Math.cos(angle3) * radius;
        const p3y = Math.sin(angle3) * radius;

        this.ctx.strokeStyle = this.adjustColor(color);
        this.ctx.lineWidth = 2;
        this.ctx.beginPath();

        const tangentAngle1 = angle1 + Math.PI / 2;
        const cp1Distance = radius * edgeCurveAmount;
        const cp1x = p1x + Math.cos(tangentAngle1) * cp1Distance;
        const cp1y = p1y + Math.sin(tangentAngle1) * cp1Distance;

        const tangentAngle3 = angle3 - Math.PI / 2;
        const cp3Distance = radius * edgeCurveAmount;
        const cp3x = p3x + Math.cos(tangentAngle3) * cp3Distance;
        const cp3y = p3y + Math.sin(tangentAngle3) * cp3Distance;

        const deformDirX = oppositeVertex.x - p2x;
        const deformDirY = oppositeVertex.y - p2y;
        const deformDirLength = Math.sqrt(deformDirX * deformDirX + deformDirY * deformDirY);

        const perpX = -deformDirY / deformDirLength;
        const perpY = deformDirX / deformDirLength;

        const intermediateDistance = radius * intermediateBlend * 0.5;

        let cp1_intermediateX = cp2x + perpX * intermediateDistance;
        let cp1_intermediateY = cp2y + perpY * intermediateDistance;
        let cp3_intermediateX = cp2x - perpX * intermediateDistance;
        let cp3_intermediateY = cp2y - perpY * intermediateDistance;

        cp1_intermediateX = cp1_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp1_intermediateY = cp1_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;
        cp3_intermediateX = cp3_intermediateX * (1 - intermediateDepth) + oppositeVertex.x * intermediateDepth;
        cp3_intermediateY = cp3_intermediateY * (1 - intermediateDepth) + oppositeVertex.y * intermediateDepth;

        const p3Screen = this.toScreen(p3x, p3y);
        this.ctx.moveTo(p3Screen.x, p3Screen.y);

        const startAngle = angle3;
        const endAngle = angle1 + Math.PI * 2;
        const numSegments = 30;

        for (let i = 1; i <= numSegments; i++) {
            const t = i / numSegments;
            const angle = startAngle + (endAngle - startAngle) * t;
            const x = Math.cos(angle) * radius;
            const y = Math.sin(angle) * radius;
            const p = this.toScreen(x, y);
            this.ctx.lineTo(p.x, p.y);
        }

        const cp1Screen = this.toScreen(cp1x, cp1y);
        const cp2Screen = this.toScreen(cp2x, cp2y);
        const cp3Screen = this.toScreen(cp3x, cp3y);
        const cp1_intScreen = this.toScreen(cp1_intermediateX, cp1_intermediateY);
        const cp3_intScreen = this.toScreen(cp3_intermediateX, cp3_intermediateY);
        const p3Screen2 = this.toScreen(p3x, p3y);

        this.ctx.bezierCurveTo(cp1Screen.x, cp1Screen.y, cp1_intScreen.x, cp1_intScreen.y, cp2Screen.x, cp2Screen.y);
        this.ctx.bezierCurveTo(cp3_intScreen.x, cp3_intScreen.y, cp3Screen.x, cp3Screen.y, p3Screen2.x, p3Screen2.y);
        this.ctx.stroke();

        if (showControlPoints) {
            const p1Screen = this.toScreen(p1x, p1y);
            const p2Screen = this.toScreen(p2x, p2y);

            this.drawPoint(cp1_intermediateX, cp1_intermediateY, 4, 'purple');
            this.drawPoint(cp3_intermediateX, cp3_intermediateY, 4, 'purple');
            this.drawPoint(cp1x, cp1y, 5, 'orange');
            this.drawPoint(cp3x, cp3y, 5, 'orange');
            this.drawPoint(cp2x, cp2y, 6, 'yellow');
            this.drawPoint(p1x, p1y, 4, 'cyan');
            this.drawPoint(p3x, p3y, 4, 'cyan');
            this.drawPoint(p2x, p2y, 4, 'rgba(255, 255, 255, 0.5)');

            this.ctx.strokeStyle = this.adjustColor('rgba(255, 255, 0, 0.5)');
            this.ctx.lineWidth = 1;
            this.ctx.beginPath();
            this.ctx.moveTo(p1Screen.x, p1Screen.y);
            this.ctx.lineTo(cp1Screen.x, cp1Screen.y);
            this.ctx.lineTo(cp1_intScreen.x, cp1_intScreen.y);
            this.ctx.lineTo(cp2Screen.x, cp2Screen.y);
            this.ctx.lineTo(cp3_intScreen.x, cp3_intScreen.y);
            this.ctx.lineTo(cp3Screen.x, cp3Screen.y);
            this.ctx.lineTo(p3Screen.x, p3Screen.y);
            this.ctx.stroke();

            this.ctx.strokeStyle = this.adjustColor('rgba(255, 0, 255, 0.5)');
            this.ctx.setLineDash([5, 5]);
            this.ctx.beginPath();
            this.ctx.moveTo(p2Screen.x, p2Screen.y);
            this.ctx.lineTo(cp2Screen.x, cp2Screen.y);
            this.ctx.stroke();
            this.ctx.setLineDash([]);
        }

        this.drawCircle(0, 0, radius, color.replace('1)', '0.2)'), 1);
    }

    // Override draw to handle 4-sided geometry
    draw(params) {
        this.ctx.clearRect(0, 0, this.canvas.width, this.canvas.height);

        this.drawGrid(params.showGrid);

        const vertices = this.drawTetrahedron(
            params.tetSize,
            params.showTetrahedron,
            params.showColoredSides,
            params.showReferencePoints,
            params.showInscribedCircle,
            {
                red: params.redColorFieldPosition,
                green: params.greenColorFieldPosition,
                blue: params.blueColorFieldPosition
            }
        );

        if (params.showFields && vertices) {
            if (params.circleDebugMode) {
                this.drawCircle(0, 0, params.radius, this.adjustColor('rgba(0, 255, 255, 1)'), 2);
                this.ctx.globalCompositeOperation = 'difference';
            }

            // Orthogonal view: 4 edges reveal hidden symmetry within SU(3) structure
            // The 3 color fields map to 3 of the 4 visible edges in this cross-section
            const fieldConfigs = [
                { show: params.showRedField, color: 'rgba(255, 0, 0, 1)', index: 0, deformation: params.redDeformation, edgeCurve: params.redEdgeCurve, intermediateBlend: params.redIntermediateBlend },
                { show: params.showGreenField, color: 'rgba(0, 255, 0, 1)', index: 1, deformation: params.greenDeformation, edgeCurve: params.greenEdgeCurve, intermediateBlend: params.greenIntermediateBlend },
                { show: params.showBlueField, color: 'rgba(0, 0, 255, 1)', index: 2, deformation: params.blueDeformation, edgeCurve: params.blueEdgeCurve, intermediateBlend: params.blueIntermediateBlend }
            ];
            
            fieldConfigs.forEach(config => {
                if (config.show && vertices.length > config.index) {
                    this.drawFieldDepression(
                        params.radius,
                        config.color,
                        config.index,
                        vertices,
                        config.deformation,
                        params.deformWidth,
                        config.edgeCurve,
                        config.intermediateBlend,
                        params.intermediateDepth,
                        params.showControlPoints
                    );
                }
            });

            if (params.circleDebugMode) {
                this.ctx.globalCompositeOperation = 'source-over';
            }
        }
    }
}

