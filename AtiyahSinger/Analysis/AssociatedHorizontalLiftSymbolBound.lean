/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedHorizontalCovectorBound
public import AtiyahSinger.Analysis.FullSymbolMetricFrequencyBound

/-!
# Transverse full-symbol bound for the given associated horizontal lift

Public module ID: M0095.

On a compact window in an original associated product chart, the original
order-one full base symbol evaluated on the specified horizontal lift differs
from its horizontal-axis value by an error controlled by the vertical frequency.
The estimate uses the original source and target Hermitian metrics and frames.
Neither the horizontal lift nor the full symbol is replaced by a principal part.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n a a' : ℕ} {B : Type*} [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ B]
  [T2Space B] [SecondCountableTopology B]
  {E : B → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : B → Type*} [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) F]
  [IsSmoothComplexBundle (n := n) (r := a') F]
  {r : ℕ} {P : Type*} [TopologicalSpace P]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Bound the given horizontal full symbol on the same compact product-chart set.
/-- The given horizontal lift has a metric transverse bound for the original full symbol. -/
theorem exists_associatedSphere_horizontalLift_fullSymbol_metric_bound
    (H : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (p : GlobalSymbolFunction (n := n) E F)
    (hp : IsGlobalSymbol (r := a) (q := a') E F 1 p)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') F)
    (b : B) (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r))
    (e : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (K : Set XY) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b c d).target) :
    let base : Z → B :=
      associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let lift (z : Z) := split.symm.toContinuousLinearMap.comp (H.lift z)
    let CP := associatedSphereProductChart S b c d
    let x (z : XY) := base (CP.symm z)
    (∀ z ∈ K, x z ∈ e.baseSet ∩ f.baseSet) →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K, ∀ (ξ : X) (η : Y),
      let z₀ := CP.symm z
      let Ξ := covectorFromChart CP z₀ (split.symm (ξ, η))
      let Δ := p (x z) (Ξ.comp (lift z₀)) - p (x z) (covectorFromChart c (x z) ξ)
      ∀ u : E (x z), (k.pairing (x z) (Δ u) (Δ u)).re ≤
        M * ‖η‖ ^ 2 * (h.pairing (x z) u u).re := by
  classical
  intro base split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro lift CP x hframe
  -- Project the same compact total-space window into its original base chart and frames.
  have hbaseChart (z : XY) (hz : z ∈ K) : x z ∈ c.source := by
    have hw : CP.symm z ∈ CP.source := CP.map_target (hKChart hz)
    have ht : CP.symm z ∈ (associatedSphereTrivialization S b).source := hw.1.1
    have h : (associatedSphereTrivialization S b (CP.symm z)).1 ∈ c.source := hw.1.2.1
    rw [(associatedSphereTrivialization S b).coe_fst ht] at h
    exact h
  have hbase : Continuous base :=
    (associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle).continuous
  have hxcont : ContinuousOn x K :=
    (hbase.comp_continuousOn CP.continuousOn_symm).mono hKChart
  have hxcompact : IsCompact (x '' K) := hK.image_of_continuousOn hxcont
  have hxe : x '' K ⊆ c.source ∩ e.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).1⟩
  have hxf : x '' K ⊆ c.source ∩ f.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).2⟩
  obtain ⟨C, hC, hfrequency⟩ := hp.exists_compact_metric_frequency_bound
    p g h k c hc e f (x '' K) hxcompact hxe hxf
  obtain ⟨D, hD, hlift⟩ := exists_associatedSphere_horizontalCovector_bound
    S H b c hc d hd K hK hKChart
  refine ⟨C * D ^ 2, mul_nonneg hC (sq_nonneg D), ?_⟩
  intro z hz ξ η z₀ Ξ Δ u
  -- Recover the original lifted covector before applying the full-symbol frequency estimate.
  let ν := Ξ.comp (lift z₀)
  let ζ := covectorInChart c (x z) ν
  have hrecover : covectorFromChart c (x z) ζ = ν :=
    covectorFromChart_covectorInChart c hc (x z) (hbaseChart z hz) ν
  have hnorm : ‖ζ - ξ‖ ≤ D * ‖η‖ := hlift z hz ξ η
  have hb := hfrequency (x z) ⟨z, hz, rfl⟩ ξ ζ u
  rw [hrecover] at hb
  have hu : 0 ≤ (h.pairing (x z) u u).re := (h.toCore (x z)).re_inner_nonneg u
  calc
    (k.pairing (x z) (Δ u) (Δ u)).re
        ≤ C * ‖ζ - ξ‖ ^ 2 * (h.pairing (x z) u u).re := hb
    _ ≤ C * (D * ‖η‖) ^ 2 * (h.pairing (x z) u u).re := by gcongr
    _ = (C * D ^ 2) * ‖η‖ ^ 2 * (h.pairing (x z) u u).re := by ring

end AtiyahSinger
