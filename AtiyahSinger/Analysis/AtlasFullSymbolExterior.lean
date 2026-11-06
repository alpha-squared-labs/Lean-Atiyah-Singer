/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolEllipticity
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.FiniteCotangentChartExterior

/-!
# Exterior invertibility of the original general atlas full symbol

Public module ID: M2298.

Compact-local quantitative ellipticity and a finite common chart cover give one metric
radius outside which the original fiber map is bijective. The supplied atlas frames
transport coordinate invertibility back to those exact fibers. No norm is selected on
an original fiber and ranks may vary between connected components.

Sources: SG III.4.1, III.4.7 and III.13 (13.1). The finite-atlas transport is an explicit
project supplement to the standard exterior construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- The exact general atlas symbol is bijective outside one positive metric radius. -/
theorem IsEllipticFullAtlasSymbol.exists_metric_radius {m : ℝ}
    {a : AtlasSymbolFunction (n := n) E F} (ha : IsEllipticFullAtlasSymbol A B m a)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x (ξ : CotangentFiber (n := n) x),
      R < g.length x ξ → Function.Bijective (a x ξ) := by
  /- Retain the original compact coordinate windows and their inverse radii.
  Their finite cover gives a single metric exterior. In the detected chart, the
  supplied source and target frames recover bijectivity of the original fiber map. -/
  classical
  obtain ⟨C⟩ := nonempty_atlasQuantizationPresentation A B
  let K (i : Fin C.size) := tsupport (C.patch i).output.cutoff
  have hKU (i : Fin C.size) : K i ⊆ atlasSymbolChartDomain A B (C.patch i).chart
      (C.patch i).input.frameIndex (C.patch i).output.frameIndex := by
    intro z hz
    exact ⟨⟨((C.patch i).output.support_subset hz).1,
      (C.patch i).output_support_in_input_frame hz⟩,
      ((C.patch i).output.support_subset hz).2⟩
  -- Each local inverse estimate concerns these same two original frames.
  have hlocal (i : Fin C.size) : ∃ R : ℝ,
      ∀ z ∈ K i, ∀ η : EuclideanSpace ℝ (Fin n), R ≤ ‖η‖ →
        (atlasGlobalSymbolInChart A B a (C.patch i).chart
          (C.patch i).input.frameIndex (C.patch i).output.frameIndex z η).IsInvertible := by
    obtain ⟨R, _, _, _, hbound⟩ := ha (C.patch i).chart (C.patch i).chart_mem_atlas
      (C.patch i).input.frameIndex (C.patch i).output.frameIndex (K i) (hKU i)
      (C.patch i).output.compact_support
    exact ⟨R, fun z hz η hη ↦ (hbound z hz η hη).1⟩
  choose R hbound using hlocal
  have hcover (x : M) : ∃ i : Fin C.size,
      x ∈ (C.patch i).chart.source ∧ (C.patch i).chart x ∈ K i := by
    have hactive : ∃ i : Fin C.size, (C.patch i).weight x ≠ 0 := by
      by_contra h
      push Not at h
      have hsum := C.sum_weight x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hactive
    have hx : x ∈ (C.patch i).chart.source := by
      by_contra hx
      exact hi (by simp [AtlasQuantizationPatch.weight, hx])
    have hcut : (C.patch i).output.cutoff ((C.patch i).chart x) ≠ 0 := by
      simpa only [AtlasQuantizationPatch.weight, ite_eq_left hx] using hi
    exact ⟨i, hx, subset_tsupport _ hcut⟩
  -- The finite cotangent chart theorem retains the actual inverse chart covectors.
  obtain ⟨L, hL, hlarge⟩ := exists_metric_radius_of_cotangent_chart_cover g
    (fun i : Fin C.size ↦ (C.patch i).chart)
    (fun i ↦ subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (n := ∞) (C.patch i).chart_mem_atlas)
    K (fun i ↦ (C.patch i).output.compact_support)
    (fun i z hz ↦ ((C.patch i).output.support_subset hz).1) hcover R
  refine ⟨L, hL, ?_⟩
  intro x ξ hξ
  obtain ⟨i, hx, hwindow, hfreq⟩ := hlarge x ξ hξ.le
  have he : x ∈ (A.chart (C.patch i).input.frameIndex).baseSet := by
    have h := (C.patch i).output_support_in_input_frame hwindow
    simpa only [Set.mem_preimage, (C.patch i).chart.left_inv hx] using h
  have hf : x ∈ (B.chart (C.patch i).output.frameIndex).baseSet := by
    have h := ((C.patch i).output.support_subset hwindow).2
    simpa only [Set.mem_preimage, (C.patch i).chart.left_inv hx] using h
  let e := (A.frameLinearEquiv (C.patch i).input.frameIndex x he).trans
    (EuclideanSpace.equiv (Fin (A.rank (C.patch i).input.frameIndex)) ℂ).symm.toLinearEquiv
  let f := (B.frameLinearEquiv (C.patch i).output.frameIndex x hf).trans
    (EuclideanSpace.equiv (Fin (B.rank (C.patch i).output.frameIndex)) ℂ).symm.toLinearEquiv
  let η := covectorInChart (C.patch i).chart x ξ
  let b := atlasGlobalSymbolInChart A B a (C.patch i).chart
    (C.patch i).input.frameIndex (C.patch i).output.frameIndex ((C.patch i).chart x) η
  have hinv : b.IsInvertible := hbound i ((C.patch i).chart x) hwindow η hfreq
  have hchartFormula (z : EuclideanSpace ℝ (Fin n)) (y : M)
      (hy : (C.patch i).chart.symm z = y)
      (he : y ∈ (A.chart (C.patch i).input.frameIndex).baseSet)
      (hf : y ∈ (B.chart (C.patch i).output.frameIndex).baseSet)
      (η : EuclideanSpace ℝ (Fin n))
      (v : EuclideanSpace ℂ (Fin (A.rank (C.patch i).input.frameIndex))) :
      atlasGlobalSymbolInChart A B a (C.patch i).chart
          (C.patch i).input.frameIndex (C.patch i).output.frameIndex z η v =
        (EuclideanSpace.equiv (Fin (B.rank (C.patch i).output.frameIndex)) ℂ).symm
          (B.frameLinearEquiv (C.patch i).output.frameIndex y hf
            (a y (covectorFromChart (C.patch i).chart y η)
              ((A.frameLinearEquiv (C.patch i).input.frameIndex y he).symm
                ((EuclideanSpace.equiv (Fin (A.rank (C.patch i).input.frameIndex)) ℂ) v)))) := by
    subst y
    dsimp only [atlasGlobalSymbolInChart]
    rw [dite_eq_left ⟨he, hf⟩]
    rfl
  have hmatrix (v : EuclideanSpace ℂ (Fin (A.rank (C.patch i).input.frameIndex))) :
      b v = f (a x ξ (e.symm v)) := by
    simpa only [b, e, f, η, LinearEquiv.trans_apply, LinearEquiv.symm_trans_apply,
      ContinuousLinearEquiv.toLinearEquiv_symm, LinearEquiv.symm_symm,
      ContinuousLinearEquiv.coe_toLinearEquiv, ContinuousLinearEquiv.coe_symm_toLinearEquiv,
      covectorFromChart_covectorInChart (C.patch i).chart
      (C.patch i).chart_mem_atlas x hx] using
        hchartFormula ((C.patch i).chart x) x ((C.patch i).chart.left_inv hx) he hf η v
  -- The exact original map is recovered, rather than a coordinate replacement.
  have hb := hinv.bijective
  constructor
  · intro u v huv
    apply e.injective
    apply hb.1
    rw [hmatrix (e u), hmatrix (e v), e.symm_apply_apply, e.symm_apply_apply, huv]
  · intro w
    obtain ⟨v, hv⟩ := hb.2 (f w)
    exact ⟨e.symm v, f.injective ((hmatrix v).symm.trans hv)⟩

end AtiyahSinger
