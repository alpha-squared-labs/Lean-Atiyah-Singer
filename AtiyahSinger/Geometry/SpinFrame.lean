/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinStructure

/-!
# The original spin frame at a specified principal point

Public module ID: M1452.

This is the implementation adapter needed to express Clifford multiplication
in a given geometric fiber. It transports only the base-point equality of
the frame already specified by a topological spin structure. It does not
choose another frame or a local section of the principal bundle.

The real model and its orientation remain the interleaved coordinates fixed
in SpinCoordinates. The underlying spin structure has the same original
continuous metric bundle, principal action and equivariant frame lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

/-- The very frame lifted by `p`, with its target transported to the specified original fiber. -/
def TopologicalSpinStructure.frame (S : TopologicalSpinStructure m E o hm hP)
    (p : P) (b : B) (hp : projection p = b) :
    EuclideanSpace ℝ (Fin (2 * m)) ≃ₗᵢ[ℝ] E b :=
  (S.frameMap_projection p).trans hp ▸ (S.frameMap p).val.2

end AtiyahSinger
