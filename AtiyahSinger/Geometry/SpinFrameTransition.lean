/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinConnectionFrames

/-!
# Transition matrices of the original lifted spin frames

Public module ID: M1453.

The actual original principal transition relates the two specified unit-section
frames by its vector representation. The formula retains the original right
action and the fixed interleaved coordinate identification. It also expresses
that representation in the same smooth orthonormal-frame coefficients.

Source: the principal and associated frame transition law, Spin Geometry II.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

set_option maxSynthPendingDepth 50

variable {n m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (2 * m))) E
    𝓘(ℝ, EuclideanSpace ℝ (Fin n))]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
    (EuclideanSpace ℝ (Fin (2 * m))) E]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M} {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The principal transition acts on the same two lifted frames of the metric bundle. -/
theorem frame_principal_transition (S : TopologicalSpinStructure m E o hm hP)
    (a b x : M)
    (ha : x ∈ ((S.smoothPrincipalAtlas I).trivialization a).baseSet)
    (hb : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet) (v : V) :
    let t := (S.smoothPrincipalAtlas I).trivialization
    let pa := (t a).toPartialEquiv.symm (x, 1)
    let pb := (t b).toPartialEquiv.symm (x, 1)
    S.frame pa x ((t a).proj_symm_apply' ha) v =
      S.frame pb x ((t b).proj_symm_apply' hb)
        (euclideanSpinVectorRepresentation (2 * m)
          ((euclideanSpinEvenEquiv m).symm ((t b) pa).2) v) := by
  let A := S.smoothPrincipalAtlas I
  let t := A.trivialization
  let p (c : M) := (t c).toPartialEquiv.symm (x, 1)
  let τ := ((t b) (p a)).2
  have hp (c : M) (hc : x ∈ (t c).baseSet) : projection (p c) = x :=
    (t c).proj_symm_apply' hc
  have haction : MulOpposite.op τ • p b = p a := by
    have hpb : p b ∈ (t b).source := (t b).mem_source.mpr (by rw [hp b hb]; exact hb)
    have hpa : p a ∈ (t b).source := (t b).mem_source.mpr (by rw [hp a ha]; exact hb)
    have hacted : MulOpposite.op τ • p b ∈ (t b).source := by
      apply (t b).mem_source.mpr
      rw [hP.projection_smul, hp b hb]
      exact hb
    apply (t b).toOpenPartialHomeomorph.injOn hacted hpa
    change t b (MulOpposite.op τ • p b) = t b (p a)
    apply Prod.ext
    · rw [(t b).coe_fst hacted, (t b).coe_fst hpa,
        hP.projection_smul, hp b hb, hp a ha]
    · rw [A.equivariant b τ (p b) ((t b).mem_source.mp hpb)]
      have hunit : t b (p b) = (x, 1) := (t b).apply_symm_apply' hb
      rw [hunit, one_mul]
  have hframe (q : P) (y : M) (hq : projection q = y) (w : V) :
      (⟨y, S.frame q y hq w⟩ : TotalSpace V E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 w⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  have hG : (realSpinorCoordinateIsometry m).symm
      (realSpinVectorRepresentation m τ (realSpinorCoordinateIsometry m v)) =
        euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm τ) v := by
    apply (realSpinorCoordinateIsometry m).injective
    rw [LinearIsometryEquiv.apply_symm_apply,
      euclideanSpinEvenEquiv_vectorRepresentation, MulEquiv.apply_symm_apply]
  have h := S.equivariant τ (p b) v
  rw [haction, ← hframe (p a) x (hp a ha), ← hframe (p b) x (hp b hb), hG] at h
  exact TotalSpace.mk_injective x h

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual vector representation of the principal transition is smooth on the overlap. -/
theorem contMDiffOn_principal_vector_transition
    (S : TopologicalSpinStructure m E o hm hP) (a b : M) :
    let t := (S.smoothPrincipalAtlas I).trivialization
    ContMDiffOn I 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun x ↦ (euclideanSpinVectorRepresentation (2 * m)
        ((euclideanSpinEvenEquiv m).symm
          ((t b) ((t a).toPartialEquiv.symm (x, 1))).2)).toLinearMap.toContinuousLinearMap)
      ((t a).baseSet ∩ (t b).baseSet) := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization
  let U := (t a).baseSet ∩ (t b).baseSet
  let e := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let G (x : M) : V →L[ℝ] V :=
    (euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm
      ((t b) ((t a).toPartialEquiv.symm (x, 1))).2)).toLinearMap.toContinuousLinearMap
  let c (i j : Fin (2 * m)) (x : M) : ℝ :=
    inner ℝ (S.liftedFrameField (n := n) b j x) (S.liftedFrameField (n := n) a i x)
  have hcolumn (x : M) (hx : x ∈ U) (i : Fin (2 * m)) :
      G x (e i) = ∑ j : Fin (2 * m), c i j x • e j := by
    have hframe := S.frame_principal_transition (n := n) a b x hx.1 hx.2 (e i)
    let f := S.frame ((t b).toPartialEquiv.symm (x, 1)) x ((t b).proj_symm_apply' hx.2)
    have hc (j : Fin (2 * m)) : c i j x = inner ℝ (e j) (G x (e i)) := by
      dsimp only [c, liftedFrameField]
      rw [dite_eq_left hx.2, dite_eq_left hx.1, hframe]
      exact f.inner_map_map _ _
    simp_rw [hc, ← e.repr_apply_apply]
    exact (e.sum_repr _).symm
  have hcolumnSmooth (i : Fin (2 * m)) :
      ContMDiffOn I 𝓘(ℝ, V) ∞ (fun x ↦ ∑ j : Fin (2 * m), c i j x • e j) U := by
    apply contMDiffOn_finsetSum
    intro j _
    have hb := ((S.isLocalFrameOn_liftedFrameField (n := n) b).contMDiffOn j).mono (t := U)
      Set.inter_subset_right
    have ha := ((S.isLocalFrameOn_liftedFrameField (n := n) a).contMDiffOn i).mono (t := U)
      Set.inter_subset_left
    exact (hb.inner_bundle ha).smul contMDiffOn_const
  have hsmooth : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun x ↦ ∑ i : Fin (2 * m), (EuclideanSpace.proj i : V →L[ℝ] ℝ).smulRight
        (∑ j : Fin (2 * m), c i j x • e j)) U := by
    apply contMDiffOn_finsetSum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ V V
      (EuclideanSpace.proj i : V →L[ℝ] ℝ)).contDiff.contMDiff
        |>.comp_contMDiffOn (hcolumnSmooth i)
  apply hsmooth.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  change G x v = _
  have hv := congrArg (G x) (e.sum_repr v)
  simp only [map_sum, map_smul, hcolumn x hx] at hv
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply]
  change G x v = ∑ i : Fin (2 * m), v i • ∑ j : Fin (2 * m), c i j x • e j
  simpa only [e, EuclideanSpace.basisFun_repr] using hv.symm

end TopologicalSpinStructure

end AtiyahSinger
