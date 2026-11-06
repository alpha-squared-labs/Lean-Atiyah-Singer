/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterKZero
public import AtiyahSinger.Topology.HalfSpinorCharacterBasic
public import AtiyahSinger.Topology.SpinThomCharacter

/-!
# The Chern character of the actual virtual half-spin bundle

Public module ID: M1877.

SG III.11, Proposition 11.24, p.238. On the original compact Hausdorff
base the character of [S+] - [S-] uses the existing ComplexKZero and its
actual character homomorphism. The two classes are the original associated
quotient bundles from the same principal spin bundle. The Euler class uses
the same specified spin frame lift; the inverse A-hat class uses the actual
complexification of its original real bundle and the original cup product.

The lower-degree formula uses ordinary half-spin vanishing. The shifted formula
uses the original supported Thom character and the proper zero section, followed
by cohomological self-intersection. Only a specified metric on the original
complexification remains, with independence provided by InverseAhat. All degrees
are covered without cancelling the Euler class. This compact-base argument does
not establish the separate ordinary formula over an arbitrary base.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u v

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [CompactSpace B] [T2Space B] [TopologicalSpace P]
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

/-- Below the Euler degree, the character of the original virtual half-spin class vanishes. -/
theorem TopologicalSpinStructure.chernCharacter_halfSpinor_difference_eq_zero_of_lt
    (S : TopologicalSpinStructure m E o hm hP) (k : ℕ) (hk : k < m) :
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
    chernCharacterKZeroComponent B k 
      (ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus) = 0 := by
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  -- Choose metrics on the same actual associated bundles, using the original compact base.
  let hPlus := (nonempty_continuousHermitianMetric SpinPlus).some
  let hMinus := (nonempty_continuousHermitianMetric SpinMinus).some
  rw [map_sub, chernCharacterKZeroComponent_bundle SpinPlus hPlus,
    chernCharacterKZeroComponent_bundle SpinMinus hMinus]
  -- The ordinary vanishing is for this exact spin structure and the same two parity bundles.
  exact S.halfSpinorCharacterComponent_eq_zero_of_lt hPlus hMinus k hk

set_option maxHeartbeats 500000 in
-- Retain the original support transports before including the final equality in the even ring.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Proposition 11.24 on the original K class, with the fixed geometric Euler and sign. -/
theorem TopologicalSpinStructure.chernCharacter_halfSpinor_difference_add
    (S : TopologicalSpinStructure m E o hm hP)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (j : ℕ) :
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
    letI := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    chernCharacterKZeroComponent B (m + j) 
      (ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus) =
      (-1 : ℚ) ^ m • singularCohomologyEvenCup ℚ B m j S.rationalEulerClass
        (RealBundle.inverseAHatEvenComponent RealModel E hV j) := by
  classical
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let Y := TotalSpace RealModel E
  let i := bundleZeroSection (2 * m) E
  let f : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let τ := S.spinorThomClass
  let O := S.integralCohomologyOrientation.rationalization
  let χ := bundleCompactSupportChernCharacterComponent (2 * m) E (m + j) τ
  let δ := compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
    ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ Y (2 * (m + j)) ≅
      compactSupportCohomology ℚ Y (2 * j + 2 * m)).hom χ)
  -- The proper zero section retains the original source-minus-target K class.
  have hK : complexKZeroPullback (f.comp i) τ.val =
      ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus := by
    have hz := S.zeroSectionPullback_spinorThomClass
    change complexKZeroPullback
      ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap i i.continuous.isProperMap) τ.val) = _ at hz
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp] at hz
    exact hz
  have hchar : singularCohomologyPullback ℚ i (2 * (m + j))
      (compactSupportCohomologyToOrdinary ℚ Y (2 * (m + j)) χ) =
        chernCharacterKZeroComponent B (m + j)
          (ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus) := by
    dsimp only [χ]
    rw [bundleCompactSupportChernCharacterComponent_toOrdinary]
    change singularCohomologyPullback ℚ i (2 * (m + j))
      (singularCohomologyPullback ℚ f (2 * (m + j))
        (chernCharacterKZeroComponent (OnePoint Y) (m + j) τ.val)) = _
    have hcomp (a : singularCohomology ℚ (OnePoint Y) (2 * (m + j))) :
        singularCohomologyPullback ℚ i (2 * (m + j))
          (singularCohomologyPullback ℚ f (2 * (m + j)) a) =
            singularCohomologyPullback ℚ (f.comp i) (2 * (m + j)) a := by
      change (((singularCohomologyFunctor ℚ (2 * (m + j))).map _ ≫
        (singularCohomologyFunctor ℚ (2 * (m + j))).map _) a) = _
      rw [← Functor.map_comp]
      rfl
    rw [hcomp, ← chernCharacterKZeroComponent_pullback, hK]
  -- The original Thom inverse reconstructs this exact supported character.
  let cT {p q : ℕ} (hpq : p = q) : compactSupportCohomology ℚ Y p →ₗ[ℚ]
      compactSupportCohomology ℚ Y q :=
    (eqToIso (congrArg (compactSupportCohomology ℚ Y) hpq)).hom.hom
  let cH {p q : ℕ} (hpq : p = q) : singularCohomology ℚ B p →ₗ[ℚ]
      singularCohomology ℚ B q :=
    (eqToIso (congrArg (singularCohomology ℚ B) hpq)).hom.hom
  have hthom : cohomologyZeroSectionPushforward ℚ (2 * m) E O (2 * j) δ =
      cT (by omega) χ :=
    (compactBaseCohomologyThomEquiv ℚ (2 * m) E O (2 * j)).apply_symm_apply _
  have hself := zeroSectionPullback_cohomologyZeroSectionPushforward ℚ (2 * m) E O
    (2 * j) δ
  rw [hthom] at hself
  have htransport {p q : ℕ} (hpq : p = q) (a : compactSupportCohomology ℚ Y p) :
      singularCohomologyPullback ℚ i q (compactSupportCohomologyToOrdinary ℚ Y q
        (cT hpq a)) = cH hpq (singularCohomologyPullback ℚ i p
          (compactSupportCohomologyToOrdinary ℚ Y p a)) := by
    subst q
    rfl
  rw [htransport (show 2 * (m + j) = 2 * j + 2 * m by omega), hchar] at hself
  have hδ : δ = (-1 : ℚ) ^ m • RealBundle.inverseAHatEvenComponent RealModel E hV j :=
    S.fiberIntegral_chernCharacter_spinorThom hV j
  rw [hδ, map_smul] at hself
  -- Even cup commutativity places the fixed Euler class first, without cancellation.
  apply singularEvenCohomologyOf_injective ℚ B (m + j)
  have h := congrArg (fun a : singularCohomology ℚ B (2 * j + 2 * m) ↦
    singularEvenCohomologyOf ℚ B (j + m) (cH (by omega) a)) hself
  have hcast {p q n : ℕ} (hpq : p = q) (hqn : q = n)
      (a : singularCohomology ℚ B p) : cH hqn (cH hpq a) = cH (hpq.trans hqn) a := by
    subst q
    subst n
    rfl
  rw [hcast (show 2 * (m + j) = 2 * j + 2 * m by omega)
    (show 2 * j + 2 * m = 2 * (j + m) by omega)] at h
  rw [singularEvenCohomologyOf_eqToIso ℚ B (Nat.add_comm m j)] at h
  simp only [LinearMap.smul_apply] at h
  rw [map_smul, map_smul] at h
  change singularEvenCohomologyOf ℚ B (m + j)
    (chernCharacterKZeroComponent B (m + j)
      (ComplexBundle.kZeroClass SpinPlus - ComplexBundle.kZeroClass SpinMinus)) =
      (-1 : ℚ) ^ m • singularEvenCohomologyOf ℚ B (j + m)
        (singularCohomologyEvenCup ℚ B j m
          (RealBundle.inverseAHatEvenComponent RealModel E hV j)
          (cohomologyEulerClass ℚ (2 * m) E O)) at h
  rw [singularEvenCohomologyOf_cup, ← cohomologyEulerClass_rationalization] at h
  rw [map_smul, singularEvenCohomologyOf_cup]
  exact h.trans (congrArg ((-1 : ℚ) ^ m • ·) (mul_comm _ _))

end AtiyahSinger
