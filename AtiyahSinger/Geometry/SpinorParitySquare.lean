/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SpinorThomClass

/-!
# The two original parity squares

Public module ID: M1466.

The original even and odd associated bundles retain their native Clifford maps.
Both negative-square identities use the same original frame and length. These
are the two fiber identities needed by the uncut supported product construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  isFiniteRank_restrict t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

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

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))
local notation "SpinPlus" => HalfSpinorBundle m hP (0 : ZMod 2)
local notation "SpinMinus" => HalfSpinorBundle m hP (1 : ZMod 2)
local notation "VectorProjection" => (π RealModel E)
local notation "ZeroSet" => Set.range (zeroSection RealModel E)


set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The two original parity actions compose to negative squared length on this half-spin fiber. -/
theorem TopologicalSpinStructure.cliffordParity_one_zero
    (S : TopologicalSpinStructure m E o hm hP) (b : B) (v : E b) (s : HalfSpinorBundle m hP 0 b) :
    S.cliffordParity b v 1 (S.cliffordParity b v 0 s) = -(‖v‖ ^ 2 : ℂ) • s := by
  classical
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  let f (i : ZMod 2) := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p.val p.property
  -- Both factors use the same chosen frame, so the intervening fiber coordinates cancel.
  change f 0 (cliffordSymbolParity w 1
    ((f 1).symm (f 1 (cliffordSymbolParity w 0 ((f 0).symm s))))) = _
  rw [LinearEquiv.symm_apply_apply]
  have hmodel (t : CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 0) :
      cliffordSymbolParity w 1 (cliffordSymbolParity w 0 t) = -(‖w‖ ^ 2 : ℂ) • t := by
    apply Subtype.ext
    exact LinearMap.congr_fun (cliffordSymbol_sq w) t.val
  rw [hmodel, map_smul, LinearEquiv.apply_symm_apply]
  simp only [w, LinearIsometryEquiv.norm_map]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The two original parity actions compose to negative squared length on this half-spin fiber. -/
theorem TopologicalSpinStructure.cliffordParity_zero_one
    (S : TopologicalSpinStructure m E o hm hP) (b : B) (v : E b) (s : HalfSpinorBundle m hP 1 b) :
    S.cliffordParity b v 0 (S.cliffordParity b v 1 s) = -(‖v‖ ^ 2 : ℂ) • s := by
  classical
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  let f (i : ZMod 2) := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p.val p.property
  -- Both factors use the same chosen frame, so the intervening fiber coordinates cancel.
  change f 1 (cliffordSymbolParity w 0
    ((f 0).symm (f 0 (cliffordSymbolParity w 1 ((f 1).symm s))))) = _
  rw [LinearEquiv.symm_apply_apply]
  have hmodel (t : CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 1) :
      cliffordSymbolParity w 0 (cliffordSymbolParity w 1 t) = -(‖w‖ ^ 2 : ℂ) • t := by
    apply Subtype.ext
    exact LinearMap.congr_fun (cliffordSymbol_sq w) t.val
  rw [hmodel, (f 1).map_smul, LinearEquiv.apply_symm_apply]
  simp only [w, LinearIsometryEquiv.norm_map]

end AtiyahSinger
