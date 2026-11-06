/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasDifferentialIndex
public import AtiyahSinger.Analysis.ZeroDimensionalSectionIndex
public import AtiyahSinger.Analysis.ZeroTwistedSpinSymbolClass
public import AtiyahSinger.Geometry.SpinDiracCharacteristic
public import AtiyahSinger.Geometry.ZeroDimensionalCharacteristicIntegral

/-!
# The actual twisted spin index at the native zero-dimensional endpoint

Public module ID: M1057.

The operator is the original zero contraction on the associated even vacuum
line tensored with W, with original odd zero target. Its index need not be
zero. The base uses the positive point orientation induced by the canonical
empty tangent bases. This is the native rank-zero continuation already used
in S01/S02/S04, not a two-sheeted Spin(0) lift or arbitrary signed point data.

Source: the project rank-zero continuation of SG III.13.10, compatible with
the original degenerate exterior spinor model. The direct finite-dimensional
proof retains the same section operator and normalized fundamental-class integral.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  ComplexBundle.tensorTopology ComplexBundle.isFiniteRank_tensor
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal
  t2Space_cotangent locallyCompactSpace_cotangent

set_option maxSynthPendingDepth 40

variable {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)
  (A : SmoothSpinPrincipalAtlas 0 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) projection)
  {W : M → Type} [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
  [TopologicalSpace (TotalSpace Unit W)]
  (B : SmoothComplexBundleAtlas (n := 0) W)
  (g : SmoothTangentMetric (n := 0) (M := M))

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
local notation "TM" => (TangentSpace I : M → Type _)

set_option maxHeartbeats 800000 in
-- Normalize the original finite discrete section spaces and native zero-spin index.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native zero-dimensional twisted index is the original degree-zero characteristic number. -/
theorem zeroTwistedDiracPlus_index
    (hV : letI := complexificationTopology (EuclideanSpace ℝ (Fin 0)) TM
      ComplexBundle.ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x)) :
    letI := B.isFiniteRank
    (((zeroTwistedDiracPlus hP A B).toLinearMap.index : ℤ) : ℚ) =
      compactManifoldCohomologyIntegral (zeroTangentHomologicalOrientation g)
        (spinDiracCharacteristicClass (m := 0) hV (ComplexBundle.kZeroClass W)) := by
  /- On the finite discrete base, the original atlas section spaces are the
  full products of the original fibers. Rank-nullity computes this same
  operator's index; the positive vacuum has rank one and the odd fiber has
  rank zero. Independently, the original degree-zero characteristic restricts
  to rank(W_x) times the unit at each point. The original integral for the
  canonical positive empty tangent bases sums those exact point values.
  This direct endpoint argument uses no general index theorem. -/
  classical
  let : IsFiniteRank W := B.isFiniteRank
  let : DiscreteTopology M := ChartedSpace.discreteTopology (EuclideanSpace ℝ (Fin 0)) M
  let : Finite M := finite_of_compact_of_discrete
  let : Fintype M := Fintype.ofFinite M
  -- Compute the original section operator using the actual two tensor fiber families.
  have hindex := SmoothComplexBundleAtlas.index_eq_sum_finrank_of_zeroDimensional
      (tensorSmoothAtlas (halfSpinorBundleSmoothAtlas 0 hP A 0) B)
      (tensorSmoothAtlas (halfSpinorBundleSmoothAtlas 0 hP A 1) B)
      (zeroTwistedDiracPlus hP A B).toLinearMap
  change (zeroTwistedDiracPlus hP A B).toLinearMap.index =
    (∑ x : M, (Module.finrank ℂ (HalfSpinorBundle 0 hP 0 x ⊗[ℂ] W x) : ℤ)) -
      ∑ x : M, (Module.finrank ℂ (HalfSpinorBundle 0 hP 1 x ⊗[ℂ] W x) : ℤ) at hindex
  simp only [Module.finrank_tensorProduct, finrank_halfSpinorBundle_zero,
    ite_true, one_ne_zero, ite_false, one_mul, zero_mul, Nat.cast_zero,
    Finset.sum_const_zero, sub_zero] at hindex
  -- The sole convolution term is the original zeroth character, since A-hat_0 is the unit.
  have hcharacter : spinDiracCharacteristicClass (m := 0) hV (ComplexBundle.kZeroClass W) =
      chernCharacterKZeroComponent M 0 (ComplexBundle.kZeroClass W) := by
    let := RealBundle.isFiniteRank_of_vectorBundle (EuclideanSpace ℝ (Fin 0)) TM
    have hhat : RealBundle.aHatEvenComponent (EuclideanSpace ℝ (Fin 0)) TM hV 0 =
        singularCohomologyOne ℚ M := by
      simpa [RealBundle.aHatEvenComponent] using
        (RealBundle.pontryagin_aHat_zero (EuclideanSpace ℝ (Fin 0)) TM hV).2
    unfold spinDiracCharacteristicClass
    rw [Fin.sum_univ_one]
    simp only [Fin.val_zero, Nat.sub_zero, Nat.mul_zero,
      CategoryTheory.eqToIso_refl, CategoryTheory.Iso.refl_hom, ModuleCat.id_apply]
    rw [hhat]
    dsimp only [singularCohomologyEvenCup]
    exact singularCohomologyCup_one ℚ M 0 _
  have hpoint (x : M) : singularCohomologyPullback ℚ (ContinuousMap.const PUnit x) 0
      (chernCharacterKZeroComponent M 0 (ComplexBundle.kZeroClass W)) =
        (Module.finrank ℂ (W x) : ℚ) • singularCohomologyOne ℚ PUnit := by
    let f : C(PUnit, M) := ContinuousMap.const _ x
    let E := (f : PUnit → M) *ᵖ W
    let : IsFiniteRank E := isFiniteRank_pullback f
    let h : ContinuousHermitianMetric E := (nonempty_continuousHermitianMetric E).some
    rw [← chernCharacterKZeroComponent_pullback f (ComplexBundle.kZeroClass W) 0,
      ← kZeroClass_pullback f, chernCharacterKZeroComponent_bundle E h 0]
    exact globalChernCharacterComponent_zero_of_finrank E h (Module.finrank ℂ (W x))
      (fun _ ↦ rfl)
  -- The specified positive point orientation evaluates the same class by its rank values.
  rw [hcharacter, compactManifoldCohomologyIntegral_zeroTangent g _
    (fun x ↦ (Module.finrank ℂ (W x) : ℚ)) hpoint, hindex]
  simp only [Int.cast_sum, Int.cast_natCast]

end AtiyahSinger
