/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Native zero-section derivative of a smooth bundle-linear map

Public module ID: M1511.

A smooth linear map between two real vector bundles over the same base has,
at fiber zero, the identity base derivative and its actual fiber map. The
statement uses both original native charts and their exact preferred frames.

The proof restricts the actual coordinate derivative to its horizontal and
vertical axes. The zero section fixes the former; fiber linearity fixes the
latter. No derivative of an independently chosen fiber metric is needed.
This standard vector-bundle calculation is used when comparing the prescribed
tangent-normal splitting with the canonical complex Thom orientation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Topology
open scoped ContDiff

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original native coordinate derivative of a smooth bundle-linear map at zero is
the product of the identity base map and its original fiber coordinate map. -/
theorem hasFDerivAt_bundleMap_zero {B F G M : Type}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace M] [ChartedSpace B M] [IsManifold 𝓘(ℝ, B) ∞ M]
    {E₁ E₂ : M → Type}
    [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)] [∀ x, TopologicalSpace (E₁ x)]
    [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)] [∀ x, TopologicalSpace (E₂ x)]
    [TopologicalSpace (TotalSpace F E₁)] [FiberBundle F E₁] [VectorBundle ℝ F E₁]
    [ContMDiffVectorBundle ∞ F E₁ 𝓘(ℝ, B)]
    [TopologicalSpace (TotalSpace G E₂)] [FiberBundle G E₂] [VectorBundle ℝ G E₂]
    [ContMDiffVectorBundle ∞ G E₂ 𝓘(ℝ, B)]
    (Q : ∀ x, E₁ x →L[ℝ] E₂ x)
    (hQ : ContMDiff (𝓘(ℝ, B).prod 𝓘(ℝ, F)) (𝓘(ℝ, B).prod 𝓘(ℝ, G)) ∞
      (fun z : TotalSpace F E₁ ↦ (⟨z.proj, Q z.proj z.snd⟩ : TotalSpace G E₂)))
    (x : M) :
    letI : ChartedSpace (B × F) (TotalSpace F E₁) :=
      inferInstanceAs (ChartedSpace (ModelProd B F) (TotalSpace F E₁))
    letI : ChartedSpace (B × G) (TotalSpace G E₂) :=
      inferInstanceAs (ChartedSpace (ModelProd B G) (TotalSpace G E₂))
    let e₁ := VectorBundle.continuousLinearEquivAt ℝ F E₁ x
    let e₂ := VectorBundle.continuousLinearEquivAt ℝ G E₂ x
    let c := chartAt (B × F) (⟨x, 0⟩ : TotalSpace F E₁)
    let d := chartAt (B × G) (⟨x, 0⟩ : TotalSpace G E₂)
    HasFDerivAt (fun p ↦ d (⟨(c.symm p).proj,
      Q (c.symm p).proj (c.symm p).snd⟩ : TotalSpace G E₂))
      (ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ B)
        (e₂.toContinuousLinearMap.comp ((Q x).comp e₁.symm.toContinuousLinearMap)))
      (c ⟨x, 0⟩) := by
  let : ChartedSpace (B × F) (TotalSpace F E₁) :=
    inferInstanceAs (ChartedSpace (ModelProd B F) (TotalSpace F E₁))
  let : ChartedSpace (B × G) (TotalSpace G E₂) :=
    inferInstanceAs (ChartedSpace (ModelProd B G) (TotalSpace G E₂))
  let z : TotalSpace F E₁ := ⟨x, 0⟩
  let w : TotalSpace G E₂ := ⟨x, 0⟩
  let t := trivializationAt F E₁ x
  let s := trivializationAt G E₂ x
  have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt F E₁ x
  have hs : x ∈ s.baseSet := mem_baseSet_trivializationAt G E₂ x
  let e₁ := t.continuousLinearEquivAt ℝ x ht
  let e₂ := s.continuousLinearEquivAt ℝ x hs
  let κ := chartAt B x
  let a := κ x
  let φ := extChartAt (𝓘(ℝ, B).prod 𝓘(ℝ, F)) z
  let ψ := extChartAt (𝓘(ℝ, B).prod 𝓘(ℝ, G)) w
  let q : TotalSpace F E₁ → TotalSpace G E₂ := fun z ↦ ⟨z.proj, Q z.proj z.snd⟩
  let C : B × F → B × G := ψ ∘ q ∘ φ.symm
  let L := e₂.toContinuousLinearMap.comp ((Q x).comp e₁.symm.toContinuousLinearMap)
  have hφzero : φ z = (a, 0) := by
    dsimp only [φ]
    rw [FiberBundle.extChartAt]
    change (κ (t ⟨x, 0⟩).1, (t ⟨x, 0⟩).2) = _
    rw [t.apply_eq_prod_continuousLinearEquivAt ℝ x ht, map_zero]
  have hqzero : q z = w := by
    change (⟨x, Q x 0⟩ : TotalSpace G E₂) = ⟨x, 0⟩
    rw [map_zero]
  have hC : ContDiffAt ℝ ∞ C (a, 0) := by
    have h := (contMDiffAt_iff.mp (hQ z)).2
    change ContDiffWithinAt ℝ ∞
      (extChartAt (𝓘(ℝ, B).prod 𝓘(ℝ, G)) (q z) ∘ q ∘ φ.symm)
      (Set.range (𝓘(ℝ, B).prod 𝓘(ℝ, F))) (φ z) at h
    rw [hφzero, hqzero] at h
    simpa only [ModelWithCorners.range_eq_univ, contDiffWithinAt_univ] using! h
  let D := fderiv ℝ C (a, 0)
  have hD : HasFDerivAt C D (a, 0) := (hC.differentiableAt (by simp)).hasFDerivAt
  have hvertical (v : F) : C (a, v) = (a, L v) := by
    have hφ : φ.symm (a, v) = (⟨x, e₁.symm v⟩ : TotalSpace F E₁) := by
      dsimp only [φ]
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm (κ x), v) = _
      rw [κ.left_inv (mem_chart_source B x)]
      exact t.symm_apply_eq_mk_continuousLinearEquivAt_symm x ht v
    change ψ (q (φ.symm (a, v))) = _
    rw [hφ]
    dsimp only [ψ]
    rw [FiberBundle.extChartAt]
    change (κ (s ⟨x, Q x (e₁.symm v)⟩).1, (s ⟨x, Q x (e₁.symm v)⟩).2) = _
    rw [s.apply_eq_prod_continuousLinearEquivAt ℝ x hs]
    rfl
  have hhorizontal : (fun u : B ↦ C (u, 0)) =ᶠ[𝓝 a] (fun u : B ↦ (u, (0 : G))) := by
    have hκ : ContinuousAt κ.symm a := κ.continuousAt_symm
      (κ.map_source (mem_chart_source B x))
    have hκx : κ.symm a = x := κ.left_inv (mem_chart_source B x)
    have hbase : ∀ᶠ u in 𝓝 a, κ.symm u ∈ t.baseSet ∩ s.baseSet :=
      hκ (hκx ▸ (t.open_baseSet.inter s.open_baseSet).mem_nhds ⟨ht, hs⟩)
    filter_upwards [hbase, κ.open_target.mem_nhds (κ.map_source (mem_chart_source B x))]
      with u hu huc
    have hφ : φ.symm (u, 0) = (⟨κ.symm u, 0⟩ : TotalSpace F E₁) := by
      dsimp only [φ]
      rw [FiberBundle.extChartAt]
      change t.toOpenPartialHomeomorph.symm (κ.symm u, 0) = _
      rw [t.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) _ hu.1, map_zero]
    change ψ (q (φ.symm (u, 0))) = _
    rw [hφ]
    dsimp only [q, ψ]
    rw [map_zero, FiberBundle.extChartAt]
    change (κ (s ⟨κ.symm u, 0⟩).1, (s ⟨κ.symm u, 0⟩).2) = _
    rw [s.apply_eq_prod_continuousLinearEquivAt ℝ _ hu.2, map_zero, κ.right_inv huc]
  have hD₁ (v : B) : D (v, 0) = (v, 0) := by
    have h := hD.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a (0 : F))
    have hd : HasFDerivAt (fun u : B ↦ (u, (0 : G)))
        (ContinuousLinearMap.inl ℝ B G) a := hasFDerivAt_prodMk_left a (0 : G)
    have he := (h.congr_of_eventuallyEq hhorizontal.symm).unique hd
    exact congrArg (fun T : B →L[ℝ] B × G ↦ T v) he
  have hD₂ (v : F) : D (0, v) = (0, L v) := by
    have h := hD.comp 0 (hasFDerivAt_prodMk_right a (0 : F))
    have hd : HasFDerivAt (fun v : F ↦ (a, L v))
        ((ContinuousLinearMap.inr ℝ B G).comp L) 0 :=
      (hasFDerivAt_const (𝕜 := ℝ) a (0 : F)).prodMk L.hasFDerivAt
    have he := (h.congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun v ↦ (hvertical v).symm))).unique hd
    exact congrArg (fun T : F →L[ℝ] B × G ↦ T v) he
  have heq : D = ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ B) L := by
    apply ContinuousLinearMap.ext
    rintro ⟨v, u⟩
    calc
      D (v, u) = D ((v, 0) + (0, u)) := by congr 1; simp
      _ = D (v, 0) + D (0, u) := map_add D _ _
      _ = (v, L u) := by rw [hD₁, hD₂]; simp
      _ = _ := rfl
  change HasFDerivAt C (ContinuousLinearMap.prodMap (ContinuousLinearMap.id ℝ B) L) (φ z)
  rw [hφzero, ← heq]
  exact hD

end AtiyahSinger
