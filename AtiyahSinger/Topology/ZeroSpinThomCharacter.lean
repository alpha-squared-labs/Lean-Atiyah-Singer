/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.ZeroHalfSpinorFormula
public import AtiyahSinger.Topology.ZeroRankThomComparison
public import AtiyahSinger.Topology.ZeroSpinThom

/-!
# The supported spin Thom character at the native rank-zero endpoint

Public module ID: M2278.

S04. The original zeroSpinorThomClass and the original graph-action map
zeroSpinThomHom have the same fiber-integral character formulas as the
positive even-rank spin branch. The integral is the inverse of the original
compact-base Thom multiplication, with the canonical empty-basis integral
orientation rationalized by the existing coefficient map. The character is
the same supported character on the unchanged native real total space.

Sources: Lawson--Michelsohn, Spin Geometry, III.12, Proposition 12.5 and
equation (12.15), pp.242--243, with the native rank-zero extension of I.2
and the exterior vacuum convention of I.5. The existing positive vacuum
trivialization and negative zero-bundle comparison supply the endpoint;
fiber dimensions alone would not identify the positive K class with one.
This is the degenerate extension, not an additional numbered source theorem.

The base is compact Hausdorff, as for the existing positive-rank character
formula. The given fiber inner products, continuous Riemannian bundle,
principal certificate, parity quotients and tensor complexification remain
fixed. A negative rank-zero orientation or a different stable two-sheeted
Spin(0) convention is not identified with this canonical empty orientation.
No positive-rank TopologicalSpinStructure is assumed at rank zero.

Together with SpinThomCharacter, these two formulas cover every even rank
in the selected compact-base model. The lower-degree condition k < 0 has
no instances. The two formulas below use the exact original Thom inverse and support graph.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

universe u v

variable {B : Type u} {P : Type v} [TopologicalSpace B]
  [CompactSpace B] [T2Space B] [TopologicalSpace P]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 0)) E]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original native rank-zero spin symbol satisfies the normalized Thom character formula. -/
theorem fiberIntegral_chernCharacter_zeroSpinorThom
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    compactSupportCohomologyFiberIntegral ℚ 0 E
        (zeroRankIntegralCohomologyOrientation E).rationalization (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (0 + j)) ≅
              compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * j + 0)).hom
          (bundleCompactSupportChernCharacterComponent 0 E (0 + j)
            (zeroSpinorThomClass E hP))) =
      (-1 : ℚ) ^ 0 • RealBundle.inverseAHatEvenComponent RealModel E hV j := by
  classical
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let : CompactSpace (TotalSpace RealModel E) :=
    (zeroRankBundleProjectionHomeomorph E).symm.compactSpace
  let i := bundleZeroSection 0 E
  -- Naturality compares the original supported character with restriction of the same K class.
  have hchar (c : CompactSupportKZero (TotalSpace RealModel E)) :
      singularCohomologyPullback ℚ i (2 * j)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) (2 * j)
          (bundleCompactSupportChernCharacterComponent 0 E j c)) =
        chernCharacterKZeroComponent B j (compactSupportKZeroToAbsolute
          (compactSupportKZeroPullback i i.continuous.isProperMap c)) := by
    rw [bundleCompactSupportChernCharacterComponent_toOrdinary,
      ← chernCharacterKZeroComponent_pullback, ← chernCharacterKZeroComponent_pullback]
    congr 1
    change complexKZeroPullback i (complexKZeroPullback
        ⟨((↑) : TotalSpace RealModel E → OnePoint (TotalSpace RealModel E)),
          OnePoint.continuous_coe⟩ c.val) =
      complexKZeroPullback ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap i i.continuous.isProperMap) c.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  -- The actual graph unit law identifies the same untwisted class with coefficient one.
  have hunit : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i i.continuous.isProperMap (zeroSpinorThomClass E hP)) =
      (1 : ComplexKZero B) := by
    have h := zeroSectionPullback_zeroSpinThomHom E hP (1 : ComplexKZero B)
    have hone : zeroSpinThomHom E hP (1 : ComplexKZero B) = zeroSpinorThomClass E hP :=
      complexKZeroCompactSupportAction_one (bundleProjection 0 E) (zeroSpinorThomClass E hP)
    rw [hone] at h
    exact h
  -- Canonical empty-basis normalization makes fiber integration ordinary zero-section restriction.
  have hcast (k l : ℕ) (hkl : k = l)
      (c : CompactSupportKZero (TotalSpace RealModel E)) :
      (eqToIso (congrArg (fun n ↦ compactSupportCohomology ℚ
        (TotalSpace RealModel E) (2 * n)) hkl)).hom
        (bundleCompactSupportChernCharacterComponent 0 E k c) =
          bundleCompactSupportChernCharacterComponent 0 E l c := by
    subst l
    rfl
  erw [hcast (0 + j) j (Nat.zero_add j)]
  simp only [pow_zero, one_smul]
  rw [compactSupportCohomologyFiberIntegral_rank_zero]
  change singularCohomologyPullback ℚ i (2 * j)
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) (2 * j)
      (bundleCompactSupportChernCharacterComponent 0 E j (zeroSpinorThomClass E hP))) = _
  rw [hchar, hunit, chernCharacterKZeroComponent_one,
    RealBundle.inverseAHatEvenComponent_rank_zero]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same native rank-zero character formula with an arbitrary original virtual coefficient. -/
theorem fiberIntegral_chernCharacter_zeroSpinThom
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (u : ComplexKZero B) (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    compactSupportCohomologyFiberIntegral ℚ 0 E
        (zeroRankIntegralCohomologyOrientation E).rationalization (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (0 + j)) ≅
              compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * j + 0)).hom
          (bundleCompactSupportChernCharacterComponent 0 E (0 + j)
            (zeroSpinThomHom E hP u))) =
      (-1 : ℚ) ^ 0 • ∑ i : Fin (j + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ B (2 * (i.val + (j - i.val))) ≅
              singularCohomology ℚ B (2 * j)).hom
          (singularCohomologyEvenCup ℚ B i.val (j - i.val)
            (chernCharacterKZeroComponent B i.val u)
            (RealBundle.inverseAHatEvenComponent RealModel E hV (j - i.val))) := by
  classical
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let : CompactSpace (TotalSpace RealModel E) :=
    (zeroRankBundleProjectionHomeomorph E).symm.compactSpace
  let i := bundleZeroSection 0 E
  -- Naturality compares the original supported character with restriction of the same K class.
  have hchar (c : CompactSupportKZero (TotalSpace RealModel E)) :
      singularCohomologyPullback ℚ i (2 * j)
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) (2 * j)
          (bundleCompactSupportChernCharacterComponent 0 E j c)) =
        chernCharacterKZeroComponent B j (compactSupportKZeroToAbsolute
          (compactSupportKZeroPullback i i.continuous.isProperMap c)) := by
    rw [bundleCompactSupportChernCharacterComponent_toOrdinary,
      ← chernCharacterKZeroComponent_pullback, ← chernCharacterKZeroComponent_pullback]
    congr 1
    change complexKZeroPullback i (complexKZeroPullback
        ⟨((↑) : TotalSpace RealModel E → OnePoint (TotalSpace RealModel E)),
          OnePoint.continuous_coe⟩ c.val) =
      complexKZeroPullback ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap i i.continuous.isProperMap) c.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  -- The exact original graph action restricts to u, before applying any character formula.
  have hclass := zeroSectionPullback_zeroSpinThomHom E hP u
  have hcast (k l : ℕ) (hkl : k = l)
      (c : CompactSupportKZero (TotalSpace RealModel E)) :
      (eqToIso (congrArg (fun n ↦ compactSupportCohomology ℚ
        (TotalSpace RealModel E) (2 * n)) hkl)).hom
        (bundleCompactSupportChernCharacterComponent 0 E k c) =
          bundleCompactSupportChernCharacterComponent 0 E l c := by
    subst l
    rfl
  erw [hcast (0 + j) j (Nat.zero_add j)]
  simp only [pow_zero, one_smul]
  rw [compactSupportCohomologyFiberIntegral_rank_zero]
  change singularCohomologyPullback ℚ i (2 * j)
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace RealModel E) (2 * j)
      (bundleCompactSupportChernCharacterComponent 0 E j (zeroSpinThomHom E hP u))) = _
  rw [hchar, hclass]
  -- The rank-zero inverse A-hat family is the unit: only the terminal convolution summand survives.
  simp_rw [RealBundle.inverseAHatEvenComponent_rank_zero]
  symm
  rw [Finset.sum_eq_single (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))]
  · apply singularEvenCohomologyOf_injective ℚ B j
    erw [singularEvenCohomologyOf_eqToIso ℚ B (by omega : j + (j - j) = j)]
    rw [singularEvenCohomologyOf_cup, singularEvenCohomologyOf_degreeTwoPow,
      map_zero, Nat.sub_self, pow_zero, mul_one]
  · intro k _ hkj
    have hk : k.val < j := by
      have hle := Nat.le_of_lt_succ k.isLt
      have hne : k.val ≠ j := fun h ↦ hkj (Fin.ext h)
      omega
    obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j - k.val ≠ 0)
    have hz : singularCohomologyDegreeTwoPow ℚ B (0 : singularCohomology ℚ B 2)
        (j - k.val) = 0 := by
      rw [hl]
      simp only [singularCohomologyDegreeTwoPow, singularCohomologyEvenCup,
        map_zero, LinearMap.zero_apply]
    rw [hz, map_zero, map_zero]
  · exact fun h ↦ (h (Finset.mem_univ _)).elim

end AtiyahSinger
