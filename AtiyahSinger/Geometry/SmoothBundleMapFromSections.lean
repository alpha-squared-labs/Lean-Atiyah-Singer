/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Detecting smooth bundle maps on the original smooth sections

Public module ID: M1375.

On a Hausdorff smooth manifold, a fiberwise linear map between the original
native bundles is smooth if and
only if it sends every original global smooth section to a smooth section.
Smooth bump functions recover each fixed local frame near a point. The
criterion supplies the actual finite-degree projections and inclusions used
when assembling the Hodge operator; no continuity follows from linearity alone.

Source: the local frame characterization of smooth bundle morphisms,
Lawson--Michelsohn, Spin Geometry, III.1, with the usual bump-function extension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter
open scoped Manifold ContDiff Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

/-- The original smooth sections detect smoothness of a fiberwise complex-linear map. -/
theorem isSmoothBundleMap_iff_map_smoothSections (a : ∀ x, E x →ₗ[ℂ] F x) :
    IsSmoothBundleMap (n := n) (r := r) (q := q) a ↔
      ∀ u : smoothSections (n := n) (r := r) E,
        IsSmoothSection (n := n) (r := q) F (fun x ↦ a x (u.val x)) := by
  constructor
  · intro ha u
    exact ha.isSmoothSection a u
  intro h
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  -- Real smooth cutoffs extend each fixed original local frame near the chosen point.
  have hloc (f : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas f]
      (x : M) (hx : x ∈ f.baseSet) (a : EuclideanSpace ℂ (Fin r)) :
      ∃ s : smoothSections (n := n) (r := r) E,
        ∀ᶠ y in 𝓝 x, s.val y = f.symmL ℂ y a := by
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.mp
      (f.open_baseSet.mem_nhds hx)
    let s : ∀ y, E y := fun y ↦ (b y : ℂ) • f.symmL ℂ y a
    have hs : IsSmoothSection (n := n) (r := r) E s := by
      intro q hq y hy
      let := hq
      by_cases hyb : y ∈ tsupport b
      · have hyf : y ∈ f.baseSet := hb hyb
        have ht := (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) f q).contMDiffAt
          ((f.open_baseSet.inter q.open_baseSet).mem_nhds ⟨hyf, hy⟩)
        have ha : ContDiff ℝ ∞
            (fun L : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦ L a) :=
          (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
        have hscalar := Complex.ofRealCLM.contMDiff.comp b.contMDiff
        have hmul : ContDiff ℝ ∞
            (fun z : ℂ × EuclideanSpace ℂ (Fin r) ↦ z.1 • z.2) := contDiff_smul
        have hlocal := hmul.comp_contMDiffAt
          (hscalar.contMDiffAt.prodMk_space (ha.comp_contMDiffAt ht))
        apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [f.open_baseSet.mem_nhds hyf, q.open_baseSet.mem_nhds hy]
          with z hzf hzq
        change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) =
          (b z : ℂ) • f.coordChangeL ℂ q z a
        rw [map_smul, f.coordChangeL_apply q ⟨hzf, hzq⟩, f.symmL_apply hzf]
        rfl
      · apply (contMDiffAt_const (c := (0 : EuclideanSpace ℂ (Fin r)))
          |>.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hyb,
          q.open_baseSet.mem_nhds hy] with z hzb hzq
        change (q.linearEquivAt ℂ z hzq) ((b z : ℂ) • f.symmL ℂ z a) = 0
        rw [image_eq_zero_of_notMem_tsupport hzb, Complex.ofReal_zero, zero_smul, map_zero]
    refine ⟨⟨s, hs⟩, ?_⟩
    filter_upwards [b.eventuallyEq_one] with y hy
    change (b y : ℂ) • f.symmL ℂ y a = f.symmL ℂ y a
    change b y = (1 : ℝ) at hy
    rw [hy, Complex.ofReal_one, one_smul]
  -- Test those extensions in the original target frame and use their local equality.
  intro e he f hf j x hx
  let := he
  let := hf
  obtain ⟨u, hu⟩ := hloc e x hx.1 (EuclideanSpace.single j 1)
  have hs := (h u f hf).contMDiffAt (f.open_baseSet.mem_nhds hx.2)
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [hu] with y hy
  change (f ⟨y, a y (e.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 =
    (f ⟨y, a y (u.val y)⟩).2
  rw [hy]

end AtiyahSinger
