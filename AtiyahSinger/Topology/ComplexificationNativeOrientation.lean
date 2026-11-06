/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentHomologicalOrientation
public import AtiyahSinger.Topology.ComplexificationBundle
public import AtiyahSinger.Topology.ComplexificationOrientationSign

/-!
# Interleaved native coordinates on an actual complexification

Public module ID: M1731.

The original real bundle charts, doubled and interleaved, give real native charts
on the original complexification topology. The supplied Hermitian metric keeps its
original fiber norms throughout the construction. The real frame of each chart is
exactly the realification of the complexification of its original real frame.

These interfaces allow the normalized complex Thom orientation to be compared with
smooth real bundle charts even when the supplied Hermitian metric is only continuous.
Changing this chart data leaves the original fibers and topologies unchanged.

Source: the standard orientation of a complexification, with explicit native chart
and tensor-product identifications supplied here for the Thom-integral comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The original real/imaginary coordinates carry the actual complexified frame to the
standard interleaved real frame, including rank zero. -/
theorem complexification_interleaved_basis {r : ℕ} {Q : Type*} [AddCommGroup Q] [Module ℝ Q]
    (A : Q ≃ₗ[ℝ] EuclideanSpace ℝ (Fin r)) :
    let L := (complexificationReIm Q).trans
      ((A.prodCongr A).trans (tangentModelCoordinateEquiv r).toLinearEquiv)
    (EuclideanSpace.basisFun (Fin (2 * r)) ℝ).toBasis.map L.symm =
      complexBasisRealification
        (((EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map A.symm).baseChange ℂ) := by
  let L := (complexificationReIm Q).trans
    ((A.prodCongr A).trans (tangentModelCoordinateEquiv r).toLinearEquiv)
  let b := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map A.symm
  let ρ : Fin r × Fin 2 ≃ Fin (2 * r) :=
    finProdFinEquiv.trans (finCongr (Nat.mul_comm r 2))
  have hb (i : Fin r) (j : Fin 2) :
      complexBasisRealification (b.baseChange ℂ) (ρ (i, j)) =
        Complex.basisOneI j ⊗ₜ[ℝ] b i := by
    rw [complexBasisRealification, Module.Basis.reindex_apply]
    change (Complex.basisOneI.smulTower' (b.baseChange ℂ)) (ρ.symm (ρ (i, j))) = _
    rw [ρ.symm_apply_apply, Module.Basis.smulTower'_apply, Module.Basis.baseChange_apply,
      TensorProduct.smul_tmul']
    simp only [smul_eq_mul, mul_one]
  apply DFunLike.ext
  intro k
  obtain ⟨⟨i, j⟩, rfl⟩ := ρ.surjective k
  apply L.injective
  change L (L.symm ((EuclideanSpace.basisFun (Fin (2 * r)) ℝ).toBasis (ρ (i, j)))) = _
  rw [L.apply_symm_apply, hb]
  change _ = tangentModelCoordinateEquiv r
    ((A.prodCongr A) (complexificationReIm Q (Complex.basisOneI j ⊗ₜ[ℝ] b i)))
  rw [(complexificationReIm_properties Q).1]
  simp only [LinearEquiv.prodCongr_apply, map_smul]
  have hAb : A (b i) = (EuclideanSpace.basisFun (Fin r) ℝ).toBasis i := by
    exact A.apply_symm_apply _
  rw [hAb]
  ext k
  obtain ⟨⟨a, t⟩, rfl⟩ := ρ.surjective k
  fin_cases j <;> fin_cases t <;>
    simp [tangentModelCoordinateEquiv, EuclideanSpace.basisFun_apply, ρ,
      EuclideanSpace.sumEquivProd]


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The doubled original real charts give an interleaved native atlas on the fixed
complexification topology with the supplied Hermitian norms. -/
theorem exists_interleaved_complexificationNativeFiberBundle {r : ℕ} {X : Type} [TopologicalSpace X]
    (E : X → Type) [∀ x, AddCommGroup (E x)] [∀ x, Module ℝ (E x)]
    [∀ x, TopologicalSpace (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
    (h : letI := ComplexBundle.complexificationTopology (EuclideanSpace ℝ (Fin r)) E
      ComplexBundle.ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) :
    let V := EuclideanSpace ℝ (Fin r)
    let C := fun x ↦ ℂ ⊗[ℝ] E x
    letI := ComplexBundle.complexificationTopology V E
    letI : ∀ x, NormedAddCommGroup (C x) := h.fiberNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (C x) := h.fiberInnerProductSpace
    letI : ∀ x, InnerProductSpace ℝ (C x) := h.realFiberInnerProductSpace
    let W := EuclideanSpace ℝ (Fin (2 * r))
    letI := ComplexBundle.nativeModelTopology C W
    let H := (ComplexBundle.nativeModelTotalHomeomorph C W).trans
      (ComplexBundle.complexificationDoubleTotalHomeomorph V E)
    ∃ b : FiberBundle W C,
      (letI := b; VectorBundle ℝ W C) ∧
      ∀ x, b.trivializationAt' x =
        (((trivializationAt V E x).prod (trivializationAt V E x)).transFiberHomeomorph
          (tangentModelCoordinateEquiv r).toHomeomorph).compHomeomorph H := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let C := fun x ↦ ℂ ⊗[ℝ] E x
  let := ComplexBundle.complexificationTopology V E
  let : ∀ x, NormedAddCommGroup (C x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (C x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (C x) := h.realFiberInnerProductSpace
  let W := EuclideanSpace ℝ (Fin (2 * r))
  let := ComplexBundle.nativeModelTopology C W
  let H := (ComplexBundle.nativeModelTotalHomeomorph C W).trans
    (ComplexBundle.complexificationDoubleTotalHomeomorph V E)
  let chart (x : X) : Trivialization W (π W C) :=
    (((trivializationAt V E x).prod (trivializationAt V E x)).transFiberHomeomorph
      (tangentModelCoordinateEquiv r).toHomeomorph).compHomeomorph H
  have hchart (x : X) : x ∈ (chart x).baseSet :=
    ⟨mem_baseSet_trivializationAt V E x, mem_baseSet_trivializationAt V E x⟩
  have hlinear (x : X) : (chart x).IsLinear ℝ := by
    constructor
    intro y hy
    let e := trivializationAt V E x
    change y ∈ (e.prod e).baseSet at hy
    let L := (e.prod e).linearMapAt ℝ y
    have hv (w : C y) : (chart x ⟨y, w⟩).2 =
        tangentModelCoordinateEquiv r (L (complexificationReIm (E y) w)) := by
      change tangentModelCoordinateEquiv r ((e.prod e)
        ⟨y, complexificationReIm (E y) w⟩).2 = _
      change _ = tangentModelCoordinateEquiv r
        ((e.prod e).linearMapAt ℝ y (complexificationReIm (E y) w))
      rw [Trivialization.linearMapAt_apply, ite_eq_left hy]
    constructor
    · intro u v
      rw [hv, hv, hv, map_add, map_add, map_add]
    · intro a v
      rw [hv, hv, map_smul, map_smul, map_smul]
  let := ComplexBundle.isFiniteRank_complexification V E
  have hr (x : X) : Module.finrank ℂ (C x) = r := by
    rw [Module.finrank_baseChange]
    exact ((VectorBundle.continuousLinearEquivAt ℝ V E x).toLinearEquiv.finrank_eq).trans
      (by simp [V])
  let old := h.realNativeFiberBundle r hr
  have hmk (x : X) : Topology.IsInducing (@TotalSpace.mk X W C x) :=
    old.totalSpaceMk_isInducing' x
  let b : FiberBundle W C :=
    { totalSpaceMk_isInducing' := hmk
      trivializationAtlas' := {e | e.IsLinear ℝ}
      trivializationAt' := chart
      mem_baseSet_trivializationAt' := hchart
      trivialization_mem_atlas' := hlinear }
  refine ⟨b, ?_, fun _ ↦ rfl⟩
  let := b
  refine { trivialization_linear' := fun e he ↦ he.out, continuousOn_coordChange' := ?_ }
  intro e e' he he'
  let : e.IsLinear ℝ := he.out
  let : e'.IsLinear ℝ := he'.out
  apply continuousOn_clm_apply.mpr
  intro v
  have hin : ContinuousOn (fun y : X ↦ (y, v)) (e.baseSet ∩ e'.baseSet) :=
    continuousOn_id.prodMk continuousOn_const
  have hback := e.continuousOn_symm.comp hin fun y hy ↦ ⟨hy.1, Set.mem_univ v⟩
  have hout := e'.continuousOn.comp hback fun y hy ↦ e'.mem_source.mpr hy.2
  apply hout.snd.congr
  intro y hy
  exact e.coordChangeL_apply e' hy v


end AtiyahSinger
