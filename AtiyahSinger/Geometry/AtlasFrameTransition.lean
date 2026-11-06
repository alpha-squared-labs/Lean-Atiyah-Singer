/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrame

/-!
# Actual frame transitions with locally varying rank

Public module ID: M1095.

The transition from an original atlas frame to another is the rectangular matrix
of its original transition columns. It sends old section coordinates to new ones.
Smooth pullback into an overlap is used in symbol transport and local quantization.
The reverse transition is obtained by swapping frames on the same overlap; no global
rank equality, fiber norm, density or Hermitian metric is introduced.

This is the variable-rank counterpart of `FrameTransition`, using the existing
`frameLinearEquiv` rather than replacing the original bundle atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

/-- The actual old-to-new coordinate matrix, retaining both independent atlas ranks. -/
def coordChangeL (e f : A.Index) (x : M) :
    EuclideanSpace ℂ (Fin (A.rank e)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank f)) :=
  ∑ a : Fin (A.rank e),
    ContinuousLinearMap.smulRightL ℂ
      (EuclideanSpace ℂ (Fin (A.rank e))) (EuclideanSpace ℂ (Fin (A.rank f)))
      ((ContinuousLinearMap.proj a).comp
        (EuclideanSpace.equiv (Fin (A.rank e)) ℂ).toContinuousLinearMap)
      ((EuclideanSpace.equiv (Fin (A.rank f)) ℂ).symm
        ((A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2))

/-- Pulling the original forward transition along a smooth map into its overlap is smooth. -/
theorem contDiffOn_coordChangeL_comp (e f : A.Index)
    (U : Set (EuclideanSpace ℝ (Fin n))) (c : EuclideanSpace ℝ (Fin n) → M)
    (hc : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ c U)
    (hcover : Set.MapsTo c U ((A.chart e).baseSet ∩ (A.chart f).baseSet)) :
    ContDiffOn ℝ ∞ (fun z ↦ A.coordChangeL e f (c z)) U := by
  -- Each actual frame-transition column is smooth before assembling the finite matrix.
  apply ContDiffOn.sum
  intro a _
  have hcol := (A.contMDiffOn_coordChange e f a).comp hc hcover
  let ew := EuclideanSpace.equiv (Fin (A.rank f)) ℂ
  have hvec := (ew.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp_contDiffOn
    hcol.contDiffOn
  exact ((ContinuousLinearMap.smulRightL ℂ
    (EuclideanSpace ℂ (Fin (A.rank e))) (EuclideanSpace ℂ (Fin (A.rank f)))
    ((ContinuousLinearMap.proj a).comp
      (EuclideanSpace.equiv (Fin (A.rank e)) ℂ).toContinuousLinearMap)).restrictScalars ℝ).contDiff
      |>.comp_contDiffOn hvec

/-- Section coordinates in the new frame are the forward transition of the original ones. -/
theorem coordChangeL_apply (e f : A.Index) (x : M)
    (hx : x ∈ (A.chart e).baseSet ∩ (A.chart f).baseSet) (v : E x) :
    (EuclideanSpace.equiv (Fin (A.rank f)) ℂ).symm ((A.chart f ⟨x, v⟩).2) =
      A.coordChangeL e f x
        ((EuclideanSpace.equiv (Fin (A.rank e)) ℂ).symm ((A.chart e ⟨x, v⟩).2)) := by
  -- Expand the same original fiber vector in the old basis, then apply the new frame.
  let ev := EuclideanSpace.equiv (Fin (A.rank e)) ℂ
  let ew := EuclideanSpace.equiv (Fin (A.rank f)) ℂ
  let R := (A.frameLinearEquiv f x hx.2).toLinearMap.comp
    (A.frameLinearEquiv e x hx.1).symm.toLinearMap
  have hexpand := congrArg R ((Pi.basisFun ℂ (Fin (A.rank e))).sum_repr
    ((A.frameLinearEquiv e x hx.1) (v)))
  simp [R, map_sum, map_smul] at hexpand
  have hcolumn (a : Fin (A.rank e)) :
      (A.frameLinearEquiv f x hx.2) ((A.frameLinearEquiv e x hx.1).symm (Pi.single a 1)) =
        (A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2 := by
    change (A.chart f ⟨x, cast (congrArg E ((A.chart e).proj_symm_apply' hx.1))
      ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2⟩).2 = _
    have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart e).proj_symm_apply' (x := Pi.single a 1) hx.1)
      ((A.chart e).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2
    exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart f z).2) hpoint
  simp only [hcolumn] at hexpand
  change ew.symm ((A.chart f ⟨x, v⟩).2) =
    A.coordChangeL e f x (ev.symm ((A.chart e ⟨x, v⟩).2))
  have hcoord : A.coordChangeL e f x = ∑ a : Fin (A.rank e),
      ContinuousLinearMap.smulRightL ℂ
        (EuclideanSpace ℂ (Fin (A.rank e))) (EuclideanSpace ℂ (Fin (A.rank f)))
        ((ContinuousLinearMap.proj a).comp ev.toContinuousLinearMap)
        (ew.symm ((A.chart f ((A.chart e).toPartialEquiv.symm (x, Pi.single a 1))).2)) := rfl
  rw [hcoord]
  apply ew.injective
  symm
  simpa [map_sum, map_smul, ContinuousLinearMap.smulRightL_apply_apply,
    frameLinearEquiv] using hexpand

end AtiyahSinger.SmoothComplexBundleAtlas
