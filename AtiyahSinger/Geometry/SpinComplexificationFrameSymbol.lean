/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinComplexificationFrame
public import AtiyahSinger.Geometry.SpinComplexificationSymbol

/-!
# The actual doubled symbol in a supplied spin frame

Public module ID: M1447.

The canonical real metric is extended before applying exterior naturality.
The same principal point and the same native complexification frame carry
both vectors and spinor tensors; the contraction keeps its Hermitian sign.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped TensorProduct

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

set_option maxHeartbeats 600000 in
-- Compare the two contraction recurrences in the unchanged scalar-extension instances.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The supplied spin frame carries the doubled action to the actual exterior Thom symbol. -/
theorem TopologicalSpinStructure.complexificationFrame_symbol
    (S : TopologicalSpinStructure m E o hm hP)
    (e : ComplexSpinor m ≃ₗ[ℂ] Module.Dual ℂ (ComplexSpinor m))
    (he : ∀ (a : CliffordAlgebra (complexSpinorQuadraticForm m)) (s t : ComplexSpinor m),
      e (complexSpinorRepresentation m a s) t = e s (complexSpinorRepresentation m (star a) t))
    (p : P) (b : B) (hp : projection p = b) (v w : EuclideanSpace ℂ (Fin m))
    (z : ComplexSpinor m ⊗[ℂ] ComplexSpinor m) :
    letI := (complexificationHermitianCore (E b)).toNormedAddCommGroup
    letI := InnerProductSpace.ofCore (complexificationHermitianCore (E b)).toCore
    ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
        (complexSpinorDoublingExteriorEquiv m e
          ((TensorProduct.map (cliffordSymbol v) (LinearMap.id : Module.End ℂ (ComplexSpinor m)) +
            TensorProduct.map (complexSpinorChirality m) (cliffordSymbol w)) z)) =
      cliffordSymbol
        ((1 : ℂ) ⊗ₜ[ℝ] S.frame p b hp ((realSpinorCoordinateIsometry m).symm v) +
          Complex.I ⊗ₜ[ℝ] S.frame p b hp ((realSpinorCoordinateIsometry m).symm w))
        (ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap
          (complexSpinorDoublingExteriorEquiv m e z)) := by
  let V := EuclideanSpace ℂ (Fin m)
  let W := E b
  let l : V ≃ₗᵢ[ℝ] W := (realSpinorCoordinateIsometry m).symm.trans (S.frame p b hp)
  let L := l.toLinearEquiv.baseChange ℝ ℂ
  let := (complexificationHermitianCore V).toNormedAddCommGroup
  let := InnerProductSpace.ofCore (complexificationHermitianCore V).toCore
  let := (complexificationHermitianCore W).toNormedAddCommGroup
  let := InnerProductSpace.ofCore (complexificationHermitianCore W).toCore
  let ξ : ℂ ⊗[ℝ] V := (1 : ℂ) ⊗ₜ[ℝ] v + Complex.I ⊗ₜ[ℝ] w
  have hpair (u t : ℂ ⊗[ℝ] V) : inner ℂ (L u) (L t) = inner ℂ u t :=
    complexificationHermitianCore_baseChange l u t
  -- Exterior contraction transports with the same covector through the actual isometry.
  have hcontract (a : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
      ExteriorAlgebra.map L.toLinearMap (CliffordAlgebra.contractLeft (innerₛₗ ℂ ξ) a) =
        CliffordAlgebra.contractLeft (innerₛₗ ℂ (L ξ))
          (ExteriorAlgebra.map L.toLinearMap a) := by
    induction a using CliffordAlgebra.left_induction with
    | algebraMap a => simp only [AlgHom.commutes, CliffordAlgebra.contractLeft_algebraMap,
        map_zero]
    | add a b ha hb => simp only [map_add, ha, hb]
    | ι_mul a u ha =>
      rw [CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
        ExteriorAlgebra.map_apply_ι, map_mul, ExteriorAlgebra.map_apply_ι,
        CliffordAlgebra.contractLeft_ι_mul, ha]
      change inner ℂ ξ u • _ - _ = inner ℂ (L ξ) (L u) • _ - _
      rw [hpair]
  have hsymbol (a : ExteriorAlgebra ℂ (ℂ ⊗[ℝ] V)) :
      ExteriorAlgebra.map L.toLinearMap (cliffordSymbol ξ a) =
        cliffordSymbol (L ξ) (ExteriorAlgebra.map L.toLinearMap a) := by
    change ExteriorAlgebra.map L.toLinearMap
      (ExteriorAlgebra.ι ℂ ξ * a - CliffordAlgebra.contractLeft (innerₛₗ ℂ ξ) a) = _
    rw [map_sub, map_mul, ExteriorAlgebra.map_apply_ι, hcontract]
    rfl
  have hcomp (a : ExteriorAlgebra ℂ (V × V)) :
      ExteriorAlgebra.map L.toLinearMap
        (ExteriorAlgebra.map (complexSpinorComplexificationEquiv m).symm.toLinearMap a) =
      ExteriorAlgebra.map (S.complexificationFrame p b hp).toLinearMap a := by
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rfl
  have h := congrArg (ExteriorAlgebra.map L.toLinearMap)
    (complexSpinorDoublingExteriorEquiv_complexification_symbol m e he v w z)
  rw [hsymbol, hcomp, hcomp] at h
  simpa only [L, ξ, map_add, LinearEquiv.baseChange_tmul,
    LinearIsometryEquiv.coe_toLinearEquiv, l, LinearIsometryEquiv.trans_apply] using h

end AtiyahSinger
