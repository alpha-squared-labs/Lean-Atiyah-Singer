/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IndexProduct
public import AtiyahSinger.Analysis.LinearModelAnalyticIndex

/-!
# The ordinary product index in its native product model

Public module ID: M0650.

The specified Euclidean change of model identifies the native cotangent
product class with the original cotangent external product. This adapter is
shared by the zero-base and zero-sphere branches of the associated product
formula; it changes neither factor class nor the actual cotangent map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable {n m : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N] [IsManifold (𝓡 m) ∞ N]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]
  [T2Space N] [CompactSpace N] [SecondCountableTopology N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]

local notation "En" => EuclideanSpace ℝ (Fin n)
local notation "Em" => EuclideanSpace ℝ (Fin m)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 4000000 in
-- The native and Euclidean product atlases must use the same specified coordinate map.
/-- The original native product class has the product of the two original analytic indices. -/
theorem analyticIndexLinearModel_externalProduct
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := m) ν] :
    letI : ChartedSpace (En × Em) (M × N) := prodChartedSpace En M Em N
    letI : IsManifold 𝓘(ℝ, En × Em) ∞ (M × N) := by
      rw [modelWithCornersSelf_prod]
      exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 m) M N
    let p := cotangentProductModelHomeomorph (n := n) (m := m) M N
    letI := p.symm.t2Space
    letI := p.isOpenEmbedding.locallyCompactSpace
    ∀ (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)))
      (v : CompactSupportKZero (CotangentTotalSpace (n := m) (M := N))),
      analyticIndexLinearModel
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm (M × N)
          (compactSupportKZeroPullback ⟨p, p.continuous⟩ p.isProperMap
            (compactSupportKZeroExternalProduct u v)) =
        analyticIndexOfComponents μ u * analyticIndexOfComponents ν v := by
  classical
  dsimp only
  let : ChartedSpace (En × Em) (M × N) := prodChartedSpace En M Em N
  let : IsManifold 𝓘(ℝ, En × Em) ∞ (M × N) := by
    rw [modelWithCornersSelf_prod]
    exact IsManifold.prod (I := 𝓡 n) (I' := 𝓡 m) M N
  let p := cotangentProductModelHomeomorph (n := n) (m := m) M N
  let := p.symm.t2Space
  let := p.isOpenEmbedding.locallyCompactSpace
  intro u v
  let e := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)).symm
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  obtain ⟨ρ, hρ⟩ := exists_smoothPositiveMeasure (n := n + m) (M := M × N)
  let := hρ
  let b := compactSupportKZeroExternalProduct u v
  let t := compactSupportKZeroPullback ⟨p, p.continuous⟩ p.isProperMap b
  -- The actual inverse linear model followed by the actual native product map is the definition.
  have ht : cotangentKZeroLinearModel e (M × N) t = cotangentKZeroExternalProduct u v := by
    exact (DFunLike.congr_fun (compactSupportKZeroPullback_comp
      ⟨(cotangentLinearModelHomeomorph e (M × N)).symm,
        (cotangentLinearModelHomeomorph e (M × N)).symm.continuous⟩
      ⟨p, p.continuous⟩
      (cotangentLinearModelHomeomorph e (M × N)).symm.isProperMap
      p.isProperMap) b).symm
  rw [analyticIndexLinearModel_eq_comp e (M × N) ρ hρ, AddMonoidHom.comp_apply]
  change analyticIndexOfComponents ρ (cotangentKZeroLinearModel e (M × N) t) = _
  rw [ht]
  exact analyticIndexOfComponents_externalProduct μ ν ρ u v

end AtiyahSinger
