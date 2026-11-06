/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundlePresentation

/-!
# Smooth sections from weighted local frames

Public module ID: M1514.

The columns of an original local frame, multiplied by its subordinate smooth
partition function, extend by zero to global smooth sections. This construction
retains the selected presentation and is used to obtain finite separated
generators of an external tensor bundle. It is an implementation of the usual
partition-of-unity argument, not an additional hypothesis on the bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothBundlePresentation

open Bundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- A frame vector times the original partition weight, extended by zero globally. -/
def weightedFrameSection (A : SmoothBundlePresentation (n := n) (r := r) E)
    (i : Fin A.size) (v : EuclideanSpace ℂ (Fin r)) :
    smoothSections (n := n) (r := r) E := by
  classical
  let e := A.frame i
  let := A.frame_mem_atlas i
  let w (x : M) : ℂ := A.cutoff i x
  have hw : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ w :=
    Complex.ofRealCLM.contMDiff.comp (A.smooth_cutoff i)
  refine ⟨fun x ↦ w x • e.symmL ℂ x v, ?_⟩
  intro f hf x hx
  let := hf
  by_cases hxe : x ∈ e.baseSet
  · -- Inside the supporting frame the formula is a smooth transition column.
    have htransition := IsSmoothComplexBundle.contMDiffOn_coordChange
      (n := n) (E := E) e f
    have hcolumn := ((ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ (Fin r)) v).restrictScalars
      ℝ).contMDiff.comp_contMDiffOn htransition
    have hmul : ContDiff ℝ ∞
        (fun z : ℂ × EuclideanSpace ℂ (Fin r) ↦ z.1 • z.2) := contDiff_smul
    have hlocal := hmul.contMDiff.comp_contMDiffOn (hw.contMDiffOn.prodMk_space hcolumn)
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun y ↦ (f ⟨y, w y • e.symmL ℂ y v⟩).2) (e.baseSet ∩ f.baseSet) := by
      apply hlocal.congr
      intro y hy
      change (f ⟨y, w y • e.symmL ℂ y v⟩).2 = w y • (e.coordChangeL ℂ f y) v
      calc
        _ = w y • (f ⟨y, e.symmL ℂ y v⟩).2 :=
          (f.linearEquivAt ℂ y hy.2).map_smul (w y) _
        _ = _ := by rw [e.symmL_apply hy.1, e.coordChangeL_apply f hy]
    exact (hs.contMDiffAt
      ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hxe, hx⟩)).contMDiffWithinAt
  · -- The closed support avoids the frame boundary, so the extension is locally zero.
    have hxw : x ∉ tsupport (A.cutoff i) := fun h ↦ hxe (A.support_subset i h).2
    apply ContMDiffAt.contMDiffWithinAt
    apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport (A.cutoff i)).isOpen_compl.mem_nhds hxw,
      f.open_baseSet.mem_nhds hx] with y hy hfy
    change (f ⟨y, (A.cutoff i y : ℂ) • e.symmL ℂ y v⟩).2 = 0
    rw [image_eq_zero_of_notMem_tsupport hy, Complex.ofReal_zero, zero_smul]
    exact (f.linearEquivAt ℂ y hfy).map_zero

end AtiyahSinger.SmoothBundlePresentation
