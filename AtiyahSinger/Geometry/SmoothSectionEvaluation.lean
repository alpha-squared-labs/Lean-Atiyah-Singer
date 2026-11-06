/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import Mathlib.Geometry.Manifold.BumpFunction

/-!
# Smooth sections with a prescribed fiber value

Public module ID: M1411.

On a Hausdorff smooth manifold, every vector in an original smooth bundle
fiber is attained by a global smooth
section. A local constant-frame section is multiplied by a bump equal to one at
the specified point. This standard bundle-section fact is a project supplement
to SG III.1; it is used to test pointwise symbols in supported index comparisons
and to construct finite coordinates for the original smooth kernel actions.
The result keeps the original bundle and allows a noncompact or empty base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- Every vector in a smooth bundle fiber is the value of an original global smooth section. -/
theorem exists_smoothSection_apply_eq (x : M) (v : E x) :
    ∃ s : smoothSections (n := n) (r := r) E, s.val x = v := by
  classical
  let H := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  -- A bump inside the original frame lets its constant vector extend by zero.
  let e := trivializationAt V E x
  have hxE : x ∈ e.baseSet := mem_baseSet_trivializationAt _ E x
  obtain ⟨χ, _, hχ⟩ := (SmoothBumpFunction.nhds_basis_tsupport
    (I := 𝓘(ℝ, H)) x).mem_iff.mp (e.open_baseSet.mem_nhds hxE)
  let w : V := (e ⟨x, v⟩).2
  let s (y : M) : E y := (χ y : ℂ) • e.symmL ℂ y w
  have hs : IsSmoothSection (n := n) (r := r) E s := by
    intro f hf y hy
    let := hf
    by_cases hye : y ∈ e.baseSet
    · -- In the supporting frame, the transition matrix and cutoff are both smooth.
      have htransition := IsSmoothComplexBundle.contMDiffOn_coordChange
        (n := n) (E := E) e f
      have hcolumn := ((ContinuousLinearMap.apply ℂ V w).restrictScalars
        ℝ).contMDiff.comp_contMDiffOn htransition
      have hscalar : ContMDiff 𝓘(ℝ, H) 𝓘(ℝ, ℂ) ∞ (fun z ↦ (χ z : ℂ)) :=
        Complex.ofRealCLM.contMDiff.comp χ.contMDiff
      have hmul : ContDiff ℝ ∞ (fun t : ℂ × V ↦ t.1 • t.2) := contDiff_smul
      have hlocal := hmul.contMDiff.comp_contMDiffOn
        (hscalar.contMDiffOn.prodMk_space hcolumn)
      have hsmooth : ContMDiffOn 𝓘(ℝ, H) 𝓘(ℝ, V) ∞
          (fun z ↦ (f ⟨z, s z⟩).2) (e.baseSet ∩ f.baseSet) := by
        apply hlocal.congr
        intro z hz
        change (f ⟨z, (χ z : ℂ) • e.symmL ℂ z w⟩).2 =
          (χ z : ℂ) • (e.coordChangeL ℂ f z) w
        calc
          _ = (χ z : ℂ) • (f ⟨z, e.symmL ℂ z w⟩).2 :=
            (f.linearEquivAt ℂ z hz.2).map_smul (χ z : ℂ) _
          _ = _ := by rw [e.symmL_apply hz.1, e.coordChangeL_apply f hz]
      exact (hsmooth.contMDiffAt
        ((e.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hye, hy⟩)).contMDiffWithinAt
    · -- Off the supporting frame, the section is zero on an ambient neighborhood.
      have hyχ : y ∉ tsupport χ := fun h ↦ hye (hχ h)
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : V))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport (χ : M → ℝ)).isOpen_compl.mem_nhds hyχ,
        f.open_baseSet.mem_nhds hy] with z hz hfz
      change (f ⟨z, (χ z : ℂ) • e.symmL ℂ z w⟩).2 = 0
      rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, zero_smul]
      exact (f.linearEquivAt ℂ z hfz).map_zero
  refine ⟨⟨s, hs⟩, ?_⟩
  change (χ x : ℂ) • e.symmL ℂ x w = v
  rw [χ.eq_one, Complex.ofReal_one, one_smul, e.symmL_apply hxE]
  exact e.symm_apply_apply_mk hxE v

end AtiyahSinger
