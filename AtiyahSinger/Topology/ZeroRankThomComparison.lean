/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.CompactSupportCohomologyThom
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.ZeroHalfSpinorCharacter
public import AtiyahSinger.Topology.ZeroRankEuler
public import AtiyahSinger.Topology.ZeroSpinThom

/-!
# Original Thom maps at the native rank-zero endpoint

Public module ID: M2276.

The compact-support cohomological inverse with the canonical empty-basis
orientation is restriction along the actual zero section after forgetting
support. The original spin graph action restricts to its input K class.
These comparisons retain the actual maps and the positive vacuum normalization;
they are used by both supported rank-zero spin character formulas.

Sources: the rank-zero continuation of Milnor--Stasheff, section 9, and
Lawson--Michelsohn, III.12, Proposition 12.5. The cohomological calculation
uses self-intersection and the already normalized Euler unit. The K calculation
uses the original graph external product and the actual associated-bundle
trivializations. Neither requires a general tensor Chern-character formula.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u v

variable {B : Type u} [TopologicalSpace B] [CompactSpace B] [T2Space B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0)) E]

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonically normalized rank-zero Thom inverse is ordinary zero-section restriction. -/
theorem compactSupportCohomologyFiberIntegral_rank_zero (p : ℕ)
    (a : compactSupportCohomology ℚ (TotalSpace RealModel E) (p + 0)) :
    compactSupportCohomologyFiberIntegral ℚ 0 E
        (zeroRankIntegralCohomologyOrientation E).rationalization p a =
      singularCohomologyPullback ℚ (bundleZeroSection 0 E) p
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) p a) := by
  let o := (zeroRankIntegralCohomologyOrientation E).rationalization
  -- Use surjectivity of the specified forward map, retaining its exact inverse.
  obtain ⟨b, rfl⟩ := (cohomologyZeroSectionPushforward_bijective ℚ 0 E o p).surjective a
  have hinverse : compactSupportCohomologyFiberIntegral ℚ 0 E o p
      (cohomologyZeroSectionPushforward ℚ 0 E o p b) = b :=
    (compactBaseCohomologyThomEquiv ℚ 0 E o p).symm_apply_apply b
  rw [hinverse]
  -- Forgetting the same support cocone gives the relative Thom self-intersection formula.
  have hforget (c : relativeSingularCohomology ℚ (bundleNonzero 0 E) p) :
      compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) p
        (compactSupportCohomologyClass ℚ (TotalSpace RealModel E)
          (cohomologyZeroSectionSupport 0 E) p c) =
        relativeSingularCohomologyToOrdinary ℚ (bundleNonzero 0 E) p c := by
    have hleg : compactSupportCohomologyClass ℚ (TotalSpace RealModel E)
        (cohomologyZeroSectionSupport 0 E) p ≫
        compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) p =
        relativeSingularCohomologyToOrdinary ℚ (bundleNonzero 0 E) p :=
      CategoryTheory.Limits.colimit.ι_desc _ _
    exact congrArg (fun f ↦ f c) hleg
  change b = singularCohomologyPullback ℚ (bundleZeroSection 0 E) p
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) p
      (compactSupportCohomologyClass ℚ (TotalSpace RealModel E)
        (cohomologyZeroSectionSupport 0 E) p (cohomologyThomMap ℚ 0 E o p b)))
  rw [hforget]
  have hself := zeroSectionPullback_cohomologyThomMap ℚ 0 E o p b
  -- The chosen empty basis has sign +1, and the actual coefficient map preserves it.
  have heuler : cohomologyEulerClass ℚ 0 E o = singularCohomologyOne ℚ B := by
    rw [← cohomologyEulerClass_rationalization]
    exact zeroRankRationalEulerClass_eq_one E
  rw [heuler, singularCohomologyCup_one] at hself
  exact hself.symm

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

variable {P : Type v} [TopologicalSpace P]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
omit [IsContinuousRiemannianBundle RealModel E] in
/-- The original rank-zero spin graph action restricts along the same zero section to its input. -/
theorem zeroSectionPullback_zeroSpinThomHom (a : ComplexKZero B) :
    compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback (bundleZeroSection 0 E)
        (bundleZeroSection 0 E).continuous.isProperMap (zeroSpinThomHom E hP a)) = a := by
  classical
  let p := bundleProjection 0 E
  let i := bundleZeroSection 0 E
  have hi : IsProperMap i := i.continuous.isProperMap
  -- First compare the actual compact graph product with the ordinary tensor product.
  have haction (w : ComplexKZero B) (c : CompactSupportKZero B) :
      compactSupportKZeroToAbsolute
        (complexKZeroCompactSupportAction (ContinuousMap.id B) w c) =
        kZeroMul C(B, ℂ) w (compactSupportKZeroToAbsolute c) := by
    let u := (compactSupportKZeroCompactEquiv B).symm w
    let d : C(B, B × B) := (ContinuousMap.id B).prodMk (ContinuousMap.id B)
    have hd : IsProperMap d := d.continuous.isProperMap
    have hfinite (q : CompactSupportKZero (B × B)) :
        compactSupportKZeroToAbsolute (compactSupportKZeroPullback d hd q) =
          complexKZeroPullback d (compactSupportKZeroToAbsolute q) := by
      change complexKZeroPullback
          ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
          (complexKZeroPullback (properOnePointMap d hd) q.val) =
        complexKZeroPullback d (complexKZeroPullback
          ⟨((↑) : B × B → OnePoint (B × B)), OnePoint.continuous_coe⟩ q.val)
      simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      rfl
    change compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback d hd (compactSupportKZeroExternalProduct u c)) = _
    rw [hfinite, compactSupportKZeroToAbsolute_externalProduct]
    rw [show compactSupportKZeroToAbsolute u = w from
      (compactSupportKZeroCompactEquiv B).apply_symm_apply w]
    change kZeroMap _ (kZeroMul _ _ _) = _
    rw [kZeroMap_mul]
    have hcomp (f : C(B × B, B)) (hf : f.comp d = ContinuousMap.id B) (x : ComplexKZero B) :
        complexKZeroPullback d (complexKZeroPullback f x) = x := by
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hf]
      exact DFunLike.congr_fun (kZeroMap_id (R := C(B, ℂ))) x
    change kZeroMul C(B, ℂ)
      (complexKZeroPullback d (complexKZeroPullback ContinuousMap.fst w))
      (complexKZeroPullback d (complexKZeroPullback ContinuousMap.snd
        (compactSupportKZeroToAbsolute c))) = _
    rw [hcomp _ rfl, hcomp _ rfl]
  -- The positive associated line is trivialized by its vacuum; the odd bundle is actually zero.
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
    (continuous_complexSpinParityRepresentation 0 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
    (continuous_complexSpinParityRepresentation 0 1)
  let := ComplexBundle.trivialTopology (X := B) 1
  let := ComplexBundle.trivialTopology (X := B) 0
  let := ComplexBundle.isFiniteRank_trivial (X := B) 1
  let := ComplexBundle.isFiniteRank_trivial (X := B) 0
  obtain ⟨ePlus, _, _⟩ := existsUnique_halfSpinorBundle_zero_positive_trivial_iso hP
  obtain ⟨eMinus⟩ := exists_halfSpinorBundle_zero_negative_trivial_iso hP
  have hunit : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i hi (zeroSpinorThomClass E hP)) =
        kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1) := by
    have hclass := zeroSectionPullback_zeroSpinorThomClass E hP
    rw [ComplexBundle.kZeroClass_eq_of_iso ePlus, ComplexBundle.kZeroClass_eq_of_iso eMinus,
      ComplexBundle.kZeroClass_trivial, ComplexBundle.kZeroClass_trivial_zero, sub_zero] at hclass
    exact hclass
  -- Proper naturality transports the same graph along the zero section, whose base map is identity.
  change compactSupportKZeroToAbsolute (compactSupportKZeroPullback i hi
    (compactSupportKZeroAction p ((compactSupportKZeroCompactEquiv B).symm a)
      (zeroSpinorThomClass E hP))) = a
  rw [compactSupportKZeroPullback_action]
  change compactSupportKZeroToAbsolute
    (complexKZeroCompactSupportAction (ContinuousMap.id B) a
      (compactSupportKZeroPullback i hi (zeroSpinorThomClass E hP))) = a
  rw [haction, hunit, kZeroMul_comm, kZeroMul_one_left]

end AtiyahSinger
