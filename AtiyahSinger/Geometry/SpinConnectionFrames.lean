/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinFrame
public import AtiyahSinger.Geometry.SpinSmoothLift
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The original lifted spin frames as native local frames

Public module ID: M1450.

The columns of the specified unit-section spin frames, extended by zero outside
their original principal chart, form a native smooth local frame. Their native
coefficient maps are exactly the original metric pairings. This permits the
native local connection formula to use the same fields as SpinorConnection.

Source: the associated orthonormal frames in Spin Geometry II.1 and II.4.
The principal atlas and frame map are those already selected by SpinSmoothLift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

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

/-- The same lifted orthonormal frame column, with the original zero extension. -/
def liftedFrameField (S : TopologicalSpinStructure m E o hm hP)
    (b : M) (a : Fin (2 * m)) (x : M) : E x := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization b
  exact if hx : x ∈ t.baseSet then
    S.frame (t.toPartialEquiv.symm (x, 1)) x (t.proj_symm_apply' hx)
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a) else 0

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified unit-section spin frame is a native smooth local frame on its original domain. -/
theorem isLocalFrameOn_liftedFrameField (S : TopologicalSpinStructure m E o hm hP) (b : M) :
    IsLocalFrameOn I V ∞ (S.liftedFrameField (n := n) b)
      ((S.smoothPrincipalAtlas I).trivialization b).baseSet := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let b₀ := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  have hframe₀ (q : P) (y : M) (hq : projection q = y) (v : V) :
      (⟨y, S.frame q y hq v⟩ : TotalSpace V E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 v⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  have hb (x : M) (hx : x ∈ t.baseSet) :
      (fun a ↦ S.liftedFrameField (n := n) b a x) =
        b₀.toBasis.map (S.frame (t.toPartialEquiv.symm (x, 1)) x
          (t.proj_symm_apply' hx)).toLinearEquiv := by
    funext a
    dsimp only [t] at hx
    simp only [liftedFrameField, dite_eq_left hx, Module.Basis.map_apply]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [hb x hx]
    exact Module.Basis.linearIndependent _
  · intro x hx
    rw [hb x hx, Module.Basis.span_eq]
  · intro a
    apply (S.smoothPrincipalAtlas_compatible I b a).congr
    intro x hx
    let p := t.toPartialEquiv.symm (x, 1)
    have hp : projection p = x := t.proj_symm_apply' hx
    have hfield : S.liftedFrameField (n := n) b a x = S.frame p x hp (b₀ a) := by
      simp only [liftedFrameField, dite_eq_left hx]
      rfl
    exact (congrArg (fun v : E x ↦ (⟨x, v⟩ : TotalSpace V E)) hfield).trans
      (hframe₀ p x hp (b₀ a))

/-- Native local-frame coefficients are the same metric pairings with the lifted columns. -/
theorem liftedFrameField_coeff (S : TopologicalSpinStructure m E o hm hP) (b : M)
    (x : M) (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (a : Fin (2 * m)) (v : E x) :
    (S.isLocalFrameOn_liftedFrameField (n := n) b).coeff a x v =
      inner ℝ (S.liftedFrameField (n := n) b a x) v := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let f := S.frame (t.toPartialEquiv.symm (x, 1)) x (t.proj_symm_apply' hx)
  let B := (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).map f
  have hB : (S.isLocalFrameOn_liftedFrameField (n := n) b).toBasisAt hx = B.toBasis := by
    apply DFunLike.ext
    intro j
    rw [IsLocalFrameOn.toBasisAt_coe]
    simp only [liftedFrameField, dite_eq_left hx]
    rfl
  simp only [IsLocalFrameOn.coeff, dite_eq_left hx]
  change ((S.isLocalFrameOn_liftedFrameField (n := n) b).toBasisAt hx).repr v a = _
  rw [hB]
  change B.repr v a = _
  rw [B.repr_apply_apply]
  congr 1
  simp only [liftedFrameField, dite_eq_left hx]
  rfl

end TopologicalSpinStructure

end AtiyahSinger
