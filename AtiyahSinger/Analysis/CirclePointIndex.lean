/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ComponentAnalyticIndex
public import AtiyahSinger.Topology.CirclePointThom

/-!
# Positive analytic index of the circle point pushforward

Public module ID: M0327.

AR02: the original point embedding, positive exterior Thom convention and
original analytic-index map satisfy `ind(j!1) = 1`. The formula holds for
every circle point, both supplied tangent metrics and every positive smooth
density. The auxiliary Fourier measure and its operator of index -1 enter
only the argument, through the same operator's negative Thom symbol class.

Source: Atiyah--Singer I, section 8, pp.525--526, including equation (8.3)
and Figure 3. The sign computation uses the positive complex coordinate
`x + iξ`, agreeing with SG III.12 and Appendix C.3. The statement is given
for the existing component analytic index, which agrees with the original
preconnected analytic index on Circle. The proof keeps this exact symbol comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped Manifold ContDiff

attribute [local instance] isSmoothPositiveMeasure_fourierCircleMeasure
  t2Space_cotangent locallyCompactSpace_cotangent

/-- ASI section 8: the actual positive point Thom pushforward has analytic index one. -/
theorem analyticIndexOfComponents_circlePointPushforward (a : Circle)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle))
    (μ : Measure Circle) [IsSmoothPositiveMeasure (n := 1) μ] :
    analyticIndexOfComponents μ (circlePointPushforward a g₀ g₁) = 1 := by
  -- Compare the same class with the Fourier symbol before evaluating its index.
  have hindex := analyticIndex_circleFourierSymbolKClass
  rw [circleFourierSymbolKClass_eq_neg_circlePointPushforward a g₀ g₁,
    map_neg] at hindex
  have hpoint : analyticIndex fourierCircleMeasure
      (circlePointPushforward a g₀ g₁) = 1 := by
    omega
  -- Density independence and connectedness identify the supplied component index.
  rw [analyticIndexOfComponents_independent_measure μ fourierCircleMeasure,
    analyticIndexOfComponents_eq_analyticIndex]
  exact hpoint

end AtiyahSinger
