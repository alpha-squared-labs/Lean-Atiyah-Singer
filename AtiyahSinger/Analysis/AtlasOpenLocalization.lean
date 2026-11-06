/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasOpenSymbols
public import AtiyahSinger.Geometry.AtlasChartLocalization
public import AtiyahSinger.Geometry.AtlasClopenSections

/-!
# Extending atlas localization from an open submanifold

Public module ID: M0268.

A cutoff in a restricted chart has support inside the open piece. Its
ambient extension uses the same chart, frame and cutoff. Input localization
agrees with localization after section restriction. If the open piece is
also closed, ambient output extension agrees with its smooth zero extension.
These identities preserve the patches used in finite component quantization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {U : Opens M} {hU : Nonempty U}
  {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}

namespace AtlasChartCutoff

/-- Extend the original cutoff and frame from the restricted chart to its ambient chart. -/
def openExtension (L : AtlasChartCutoff (A.restrictOpen U) (c.subtypeRestr hU)) :
    AtlasChartCutoff A c where
  frameIndex := L.frameIndex
  cutoff := L.cutoff
  smooth_cutoff := L.smooth_cutoff
  compact_support := L.compact_support
  support_subset := by
    intro z hz
    have hL := L.support_subset hz
    have hr := c.subtypeRestr_symm_apply hU hL.1
    have hbase : ((A.restrictOpen U).chart L.frameIndex).baseSet =
        Subtype.val ⁻¹' (A.chart L.frameIndex).baseSet :=
      (A.exists_restrictOpenChart U L.frameIndex).choose_spec.1
    refine ⟨c.subtypeRestr_target_subset hU hL.1, ?_⟩
    change c.symm z ∈ (A.chart L.frameIndex).baseSet
    rw [← hr]
    have hx := hL.2
    change (c.subtypeRestr hU).symm z ∈ ((A.restrictOpen U).chart L.frameIndex).baseSet at hx
    rw [hbase] at hx
    exact hx

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localization by the same ambient cutoff is localization of the original restricted section. -/
theorem localize_openExtension
    (L : AtlasChartCutoff (A.restrictOpen U) (c.subtypeRestr hU))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : c.subtypeRestr hU ∈ atlas (EuclideanSpace ℝ (Fin n)) U)
    (u : A.smoothSections) :
    L.openExtension.localize hc u = L.localize hd (atlasSmoothSectionRestriction A U u) := by
  classical
  apply SchwartzMap.ext
  intro z
  change L.openExtension.localizedFunction u z =
    L.localizedFunction (atlasSmoothSectionRestriction A U u) z
  by_cases hz : z ∈ tsupport L.cutoff
  · have hzU := (L.support_subset hz).1
    have hzM := c.subtypeRestr_target_subset hU hzU
    have hr := c.subtypeRestr_symm_apply hU hzU
    simp only [localizedFunction, openExtension, hzU, hzM, ite_true]
    congr 1
    unfold atlasSectionInChart
    have hcoords := (A.exists_restrictOpenChart U L.frameIndex).choose_spec.2
      ⟨(c.subtypeRestr hU).symm z,
        u.val ((c.subtypeRestr hU).symm z).val⟩
    change (A.restrictOpenChart U L.frameIndex
      ⟨(c.subtypeRestr hU).symm z,
        u.val ((c.subtypeRestr hU).symm z).val⟩).2 =
      (A.chart L.frameIndex
        ⟨((c.subtypeRestr hU).symm z).val,
          u.val ((c.subtypeRestr hU).symm z).val⟩).2 at hcoords
    change (EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ).symm
      ((A.chart L.frameIndex ⟨c.symm z, u.val (c.symm z)⟩).2) =
        (EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ).symm
          ((A.restrictOpenChart U L.frameIndex
            ⟨(c.subtypeRestr hU).symm z, u.val ((c.subtypeRestr hU).symm z).val⟩).2)
    exact (congrArg (fun y : M ↦ (EuclideanSpace.equiv
      (Fin (A.rank L.frameIndex)) ℂ).symm
        (A.chart L.frameIndex ⟨y, u.val y⟩).2) hr.symm).trans
      (congrArg (EuclideanSpace.equiv (Fin (A.rank L.frameIndex)) ℂ).symm hcoords.symm)
  · have hzero := image_eq_zero_of_notMem_tsupport hz
    simp only [localizedFunction, openExtension, hzero, Complex.ofReal_zero, zero_smul, ite_self]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extending through the ambient chart is the actual zero extension from the clopen piece. -/
theorem extend_openExtension
    (L : AtlasChartCutoff (A.restrictOpen U) (c.subtypeRestr hU))
    (hclosed : IsClosed (U : Set M))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : c.subtypeRestr hU ∈ atlas (EuclideanSpace ℝ (Fin n)) U)
    (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank L.frameIndex)))) :
    L.openExtension.extend hc v = atlasSmoothSectionZeroExtension A U hclosed (L.extend hd v) := by
  classical
  apply Subtype.ext
  funext x
  change L.openExtension.extendedFunction v x =
    if hx : x ∈ U then L.extendedFunction v ⟨x, hx⟩ else 0
  have hbase : ((A.restrictOpen U).chart L.frameIndex).baseSet =
      Subtype.val ⁻¹' (A.chart L.frameIndex).baseSet :=
    (A.exists_restrictOpenChart U L.frameIndex).choose_spec.1
  by_cases hxU : x ∈ U
  · rw [dite_eq_left hxU]
    by_cases hx : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet
    · have hx' : (⟨x, hxU⟩ : U) ∈ (c.subtypeRestr hU).source ∩
          ((A.restrictOpen U).chart L.frameIndex).baseSet := by
        rw [OpenPartialHomeomorph.subtypeRestr_source, hbase]
        exact hx
      have hframe : (A.restrictOpen U).frameLinearEquiv L.frameIndex ⟨x, hxU⟩ hx'.2 =
          A.frameLinearEquiv L.frameIndex x hx.2 := by
        apply LinearEquiv.ext
        intro w
        exact (A.exists_restrictOpenChart U L.frameIndex).choose_spec.2 ⟨⟨x, hxU⟩, w⟩
      simp only [extendedFunction, openExtension, dite_eq_left hx, dite_eq_left hx']
      rw [hframe]
      rfl
    · have hx' : (⟨x, hxU⟩ : U) ∉ (c.subtypeRestr hU).source ∩
          ((A.restrictOpen U).chart L.frameIndex).baseSet := by
        rw [OpenPartialHomeomorph.subtypeRestr_source, hbase]
        exact hx
      simp only [extendedFunction, openExtension, dite_eq_right hx, dite_eq_right hx']
  · rw [dite_eq_right hxU]
    by_cases hx : x ∈ c.source ∩ (A.chart L.frameIndex).baseSet
    · have hzero : L.cutoff (c x) = 0 := by
        by_contra hne
        have hz := (L.support_subset (subset_tsupport _ hne)).1
        have hr := c.subtypeRestr_symm_apply hU hz
        have hu : c.symm (c x) ∈ U := hr ▸ ((c.subtypeRestr hU).symm (c x)).property
        exact hxU ((c.left_inv hx.1) ▸ hu)
      simp only [extendedFunction, openExtension, dite_eq_left hx, hzero,
        Complex.ofReal_zero, zero_smul]
    · simp only [extendedFunction, openExtension, dite_eq_right hx]

end AtlasChartCutoff

end AtiyahSinger
