/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.SmoothAtlasTransport

/-!
# Composition and transported frames for smooth bundle maps

Public module ID: M1085.

Smooth maps in specified bundle atlases compose on the original fibers.
An atlas transported through a continuous bundle isomorphism makes that
same isomorphism smooth in both directions. These are the standard local
matrix laws for smooth vector bundles (SG III.1); no arbitrary continuous
isomorphism is declared smooth for two independently prescribed atlases.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F H : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
  [TopologicalSpace (TotalSpace Unit H)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {C : SmoothComplexBundleAtlas (n := n) H}

/-- Smooth original bundle maps compose in the same specified atlases. -/
theorem IsSmoothAtlasBundleMap.comp
    {a : ∀ x, E x →ₗ[ℂ] F x} {b : ∀ x, F x →ₗ[ℂ] H x}
    (hb : IsSmoothAtlasBundleMap B C b) (ha : IsSmoothAtlasBundleMap A B a) :
    IsSmoothAtlasBundleMap A C (fun x ↦ (b x).comp (a x)) := by
  classical
  refine ⟨contMDiff_id, ?_⟩
  intro i k l x hx
  obtain ⟨j, hj⟩ := B.covers x
  let U := ((A.chart i).baseSet ∩ (B.chart j).baseSet) ∩ (C.chart k).baseSet
  let colA (y : M) := if hy : y ∈ (A.chart i).baseSet then
    (B.chart j ⟨y, a y ((A.frameLinearEquiv i y hy).symm (Pi.single l 1))⟩).2 else 0
  let colB (s : Fin (B.rank j)) (y : M) := if hy : y ∈ (B.chart j).baseSet then
    (C.chart k ⟨y, b y ((B.frameLinearEquiv j y hy).symm (Pi.single s 1))⟩).2 else 0
  -- On a middle frame, matrix multiplication is a finite sum of smooth products.
  have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Fin (C.rank k) → ℂ) ∞ (fun y ↦ ∑ s, colA y s • colB s y) U := by
    apply contMDiffOn_finsetSum
    intro s _
    have hc := ((contMDiffOn_pi_space.mp (ha.2 i j l)) s).mono
      (fun _ (hy : _ ∈ U) ↦ hy.1)
    have hd := (hb.2 j k s).mono (fun _ (hy : _ ∈ U) ↦ ⟨hy.1.2, hy.2⟩)
    have hmul : ContDiff ℝ ∞
        (fun p : ℂ × (Fin (C.rank k) → ℂ) ↦ p.1 • p.2) := contDiff_smul
    exact hmul.contMDiff.comp_contMDiffOn (hc.prodMk_space hd)
  have heq : ∀ y ∈ U,
      (if hy : y ∈ (A.chart i).baseSet then
        (C.chart k ⟨y, ((b y).comp (a y))
          ((A.frameLinearEquiv i y hy).symm (Pi.single l 1))⟩).2 else 0) =
        ∑ s, colA y s • colB s y := by
    intro y hy
    let v := a y ((A.frameLinearEquiv i y hy.1.1).symm (Pi.single l 1))
    let w := B.frameLinearEquiv j y hy.1.2 v
    let L := (C.frameLinearEquiv k y hy.2).toLinearMap.comp
      ((b y).comp (B.frameLinearEquiv j y hy.1.2).symm.toLinearMap)
    have hexpand := congrArg L ((Pi.basisFun ℂ (Fin (B.rank j))).sum_repr w)
    have hw : (B.frameLinearEquiv j y hy.1.2).symm w = v :=
      LinearEquiv.symm_apply_apply _ _
    simp only [colA, colB, dite_eq_left hy.1.1, dite_eq_left hy.1.2]
    change (C.frameLinearEquiv k y hy.2) (b y v) = ∑ s, w s • L (Pi.single s 1)
    have hL : L w = (C.frameLinearEquiv k y hy.2) (b y v) := by
      change (C.frameLinearEquiv k y hy.2) (b y
        ((B.frameLinearEquiv j y hy.1.2).symm w)) = _
      rw [hw]
    rw [← hL]
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using hexpand.symm
  -- The chosen middle chart is a neighborhood of the point in the original overlap.
  exact ((hs.congr heq).contMDiffAt
    ((((A.chart i).open_baseSet.inter (B.chart j).open_baseSet).inter
      (C.chart k).open_baseSet).mem_nhds ⟨⟨hx.1, hj⟩, hx.2⟩)).contMDiffWithinAt

/-- A transported atlas makes its defining original isomorphism smooth. -/
theorem ComplexBundle.Iso.isSmoothAtlasBundleMap_smoothAtlas (e : Iso E F)
    (B : SmoothComplexBundleAtlas (n := n) F) :
    IsSmoothAtlasBundleMap (e.smoothAtlas B) B e.toHom.linearMap := by
  classical
  refine ⟨contMDiff_id, ?_⟩
  intro i j k
  apply (B.contMDiffOn_coordChange i j k).congr
  intro x hx
  have hi : x ∈ ((e.smoothAtlas B).chart i).baseSet := hx.1
  rw [dite_eq_left hi]
  have hframe : e.linearEquiv x
      (((e.smoothAtlas B).frameLinearEquiv i x hi).symm (Pi.single k 1)) =
        (B.frameLinearEquiv i x hx.1).symm (Pi.single k 1) := by
    apply (B.frameLinearEquiv i x hx.1).injective
    rw [LinearEquiv.apply_symm_apply]
    change (e.smoothAtlas B).frameLinearEquiv i x hi
      (((e.smoothAtlas B).frameLinearEquiv i x hi).symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  change (B.chart j ⟨x, e.linearEquiv x
    (((e.smoothAtlas B).frameLinearEquiv i x hi).symm (Pi.single k 1))⟩).2 = _
  rw [hframe]
  exact congrArg (fun z : TotalSpace Unit F ↦ (B.chart j z).2)
    (TotalSpace.mk_cast (F := Unit) (E := F)
      ((B.chart i).proj_symm_apply' (x := Pi.single k 1) hx.1) _)

/-- The inverse of the atlas-transport isomorphism is smooth in the same two atlases. -/
theorem ComplexBundle.Iso.isSmoothAtlasBundleMap_symm_smoothAtlas (e : Iso E F)
    (B : SmoothComplexBundleAtlas (n := n) F) :
    IsSmoothAtlasBundleMap B (e.smoothAtlas B) e.symm.toHom.linearMap := by
  classical
  refine ⟨contMDiff_id, ?_⟩
  intro i j k
  apply (B.contMDiffOn_coordChange i j k).congr
  intro x hx
  rw [dite_eq_left hx.1]
  change (B.chart j ⟨x, e.linearEquiv x ((e.linearEquiv x).symm
    ((B.frameLinearEquiv i x hx.1).symm (Pi.single k 1)))⟩).2 = _
  rw [LinearEquiv.apply_symm_apply]
  exact congrArg (fun z : TotalSpace Unit F ↦ (B.chart j z).2)
    (TotalSpace.mk_cast (F := Unit) (E := F)
      ((B.chart i).proj_symm_apply' (x := Pi.single k 1) hx.1) _)

end AtiyahSinger
