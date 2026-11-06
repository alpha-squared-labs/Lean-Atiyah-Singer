/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductCotangentBounds
public import AtiyahSinger.Analysis.AssociatedProductCovectorCoordinates
public import AtiyahSinger.Analysis.FullSymbolMetricFrequencyBound

/-!
# Metric transverse variation in the actual associated product coordinates

Public module ID: M0096.

The original native full symbol is evaluated at the horizontal components of
the actual associated product-chart covectors. Its difference from the same
map on the horizontal axis is controlled in the prescribed bundle metrics.
The compact overlap controls the original mixed cotangent block; no product
splitting without this mixed block is substituted.
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
local notation "H" => EuclideanSpace ℝ (Fin (n + r))
local notation "Z" => AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- Retain both original product charts when estimating the transverse full-symbol error.
/-- The actual full horizontal symbol has a metric transverse bound in its product chart. -/
theorem exists_associatedSphereProductChart_horizontal_metric_transverse_bound
    (p : GlobalSymbolFunction (n := n) E F)
    (hp : IsGlobalSymbol (r := a) (q := a') E F 1 p)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') F)
    (b₁ b₂ : B) (c₁ c₂ : OpenPartialHomeomorph B X)
    (hc₁ : c₁ ∈ atlas X B) (hc₂ : c₂ ∈ atlas X B)
    (d₁ d₂ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₁ : d₁ ∈ atlas Y (OrthogonalSphere r))
    (hd₂ : d₂ ∈ atlas Y (OrthogonalSphere r))
    (e₀ : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f₀ : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) F))
    [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
    (K : Set H) (hK : IsCompact K) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace split.symm Z
    let C₁ := associatedSphereProductChart S b₁ c₁ d₁
    let C₂ := associatedSphereProductChart S b₂ c₂ d₂
    let e := C₁.symm.trans C₂
    let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
    let x (z : H) := base (C₂.symm z)
    K ⊆ e.target →
    (∀ z ∈ K, x z ∈ e₀.baseSet ∩ f₀.baseSet) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ K, ∀ (ξ : X) (η : Y),
      let frequency (η : Y) := (split (covectorInChart C₁ (C₂.symm z)
        (covectorFromChart C₂ (C₂.symm z) (split.symm (ξ, η))))).1
      let Δ := p (x z) (covectorFromChart c₁ (x z) (frequency η)) -
        p (x z) (covectorFromChart c₁ (x z) (frequency 0))
      ∀ u : E (x z), (k.pairing (x z) (Δ u) (Δ u)).re ≤
        C * ‖η‖ ^ 2 * (h.pairing (x z) u u).re := by
  classical
  intro split
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace split.symm Z
  intro C₁ C₂ e base x hKe hframe
  let pr : H →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let qr : H →L[ℝ] Y := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
  let inx : X →L[ℝ] H := split.symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ X Y)
  let A (z : H) : X →L[ℝ] X := fderiv ℝ (c₁.symm.trans c₂) (pr (e.symm z))
  let Bmix (z : H) : X →L[ℝ] Y := qr.comp ((fderiv ℝ e (e.symm z)).comp inx)
  -- The original compact target window projects to one compact native base window.
  have hbaseChart (z : H) (hz : z ∈ K) : x z ∈ c₁.source := by
    have hw : C₂.symm z ∈ C₁.source := (hKe hz).2
    let t := associatedSphereTrivialization S b₁
    have ht : C₂.symm z ∈ t.source := hw.1.1
    have h : (t (C₂.symm z)).1 ∈ c₁.source := hw.1.2.1
    rw [t.coe_fst ht] at h
    exact h
  have hxcont : ContinuousOn x K :=
    (base.continuous.comp_continuousOn C₂.continuousOn_symm).mono (fun _ hz ↦ (hKe hz).1)
  have hxcompact : IsCompact (x '' K) := hK.image_of_continuousOn hxcont
  have hxe : x '' K ⊆ c₁.source ∩ e₀.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).1⟩
  have hxf : x '' K ⊆ c₁.source ∩ f₀.baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨hbaseChart z hz, (hframe z hz).2⟩
  obtain ⟨C₀, hC₀, hfrequency⟩ := hp.exists_compact_metric_frequency_bound
    p g h k c₁ hc₁ e₀ f₀ (x '' K) hxcompact hxe hxf
  obtain ⟨D, hD, hblocks⟩ := exists_associatedSphereProductChart_cotangent_block_bounds
    S b₁ b₂ c₁ c₂ hc₁ hc₂ d₁ d₂ hd₁ hd₂ K hK hKe
  have hD₀ : 0 ≤ D := le_trans zero_le_one hD
  refine ⟨C₀ * D ^ 2, mul_nonneg hC₀ (sq_nonneg D), ?_⟩
  intro z hz ξ η frequency Δ u
  -- The literal total covector has horizontal component A*xi+B*eta in this source chart.
  have hcoord (η : Y) : frequency η = (A z).adjoint ξ + (Bmix z).adjoint η := by
    have hc := covectorInChart_associatedSphereProductChart_split
      S b₁ b₂ c₁ c₂ hc₁ hc₂ d₁ d₂ hd₁ hd₂ z (hKe hz) ξ η
    change (split (covectorInChart C₁ (C₂.symm z)
      (covectorFromChart C₂ (C₂.symm z) (split.symm (ξ, η))))).1 = _
    rw [hc, split.apply_symm_apply]
  have hdiff : frequency η - frequency 0 = (Bmix z).adjoint η := by
    rw [hcoord η, hcoord 0, map_zero, add_zero, add_sub_cancel_left]
  have hnorm : ‖(Bmix z).adjoint η‖ ≤ D * ‖η‖ :=
    ((Bmix z).adjoint.le_opNorm η).trans
      (mul_le_mul_of_nonneg_right (hblocks z hz).2.2.1 (norm_nonneg η))
  have hb := hfrequency (x z) ⟨z, hz, rfl⟩ (frequency 0) (frequency η) u
  rw [hdiff] at hb
  have hu : 0 ≤ (h.pairing (x z) u u).re := (h.toCore (x z)).re_inner_nonneg u
  calc
    (k.pairing (x z) (Δ u) (Δ u)).re
        ≤ C₀ * ‖(Bmix z).adjoint η‖ ^ 2 * (h.pairing (x z) u u).re := hb
    _ ≤ C₀ * (D * ‖η‖) ^ 2 * (h.pairing (x z) u u).re := by gcongr
    _ = (C₀ * D ^ 2) * ‖η‖ ^ 2 * (h.pairing (x z) u u).re := by ring

end AtiyahSinger
