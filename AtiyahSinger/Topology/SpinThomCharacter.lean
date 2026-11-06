/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactBaseCohomologyThom
public import AtiyahSinger.Topology.ComplexificationInverseTodd
public import AtiyahSinger.Topology.ComplexThomCharacter
public import AtiyahSinger.Topology.InverseAhat
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.RealBundleChernAction
public import AtiyahSinger.Topology.RealCohomologyProjectionFormula
public import AtiyahSinger.Topology.SpinCohomologyOrientation
public import AtiyahSinger.Topology.SpinThom
public import AtiyahSinger.Topology.SpinThomCharacterDegreeZero
public import AtiyahSinger.Topology.SpinThomDefectSquare
public import AtiyahSinger.Topology.SupportedCohomologyThomVanishing

/-!
# The supported Chern character of the original spin Thom class

Public module ID: M2170.

S04, SG III.12, Proposition 12.5, pp.242--243. The input is the original
compact-support spinor symbol, with even spinors as source and odd spinors
as target, and Clifford boundary c(v). Its supported character is constructed
from the original reduced K class, point-relative cohomology and the actual
compact-support comparison for this bundle total space. Fiber integration
is the inverse of the original normalized cup-product Thom map.

All degrees of the positive even-rank spin branch are addressed: lower
components vanish, and the shifted component integrates to (-1)^m times
the actual inverse A-hat component. Coefficients use the original graph-action
spinThomHom and an arbitrary virtual K class, giving a finite cup convolution.
No compactness of the total space or properness of its projection is assumed.

The supported self-tensor argument compares the real/imaginary product
with the complex Thom symbol. Its parity sign cancels the fixed orientation
sign. The degree-zero fiber normalization determines the resulting square
root in the completed even cohomology ring; no Euler class is cancelled.
The rank-zero spin branch is handled separately.

SG defines integration independently by Poincare duality. For oriented
manifold bases, the comparison with the ordered Thom map, including its
degree-dependent sign, is given in ThomGysinComparison; top-degree integral
normalization is proved in ThomIntegralNormalization.
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

/-- Below the Thom degree the original spin symbol, with any K coefficient, has zero character. -/
theorem TopologicalSpinStructure.compactSupportChernCharacter_spinThom_eq_zero_of_lt
    (S : TopologicalSpinStructure m E o hm hP) (u : ComplexKZero B)
    (k : ℕ) (hk : k < m) :
    bundleCompactSupportChernCharacterComponent (2 * m) E k (S.spinThomHom u) = 0 := by
  /- Stage 1: compact disk supports identify the existing Hc model with the
  original Thom pair. The relative Thom theorem, including its vanishing below
  the real rank, gives Hc^(2*k)(E;Q)=0 when 2*k < 2*m. This is a statement about
  the actual support colimit, not the ordinary character after forgetting support.
  Stage 2: apply this vanishing to the specified character of the original graph
  action on u. The relative character retains the original trivialization at
  infinity; no injectivity of forgetting support or zero-section pullback is used.
  In particular u=1 gives the below-degree assertion for spinorThomClass. -/
  have hdegree : 2 * k < 2 * m := by omega
  exact (compactSupportCohomology_subsingleton_below_rank_of_orientation ℚ (2 * m) E
    S.integralCohomologyOrientation.rationalization (2 * k) hdegree).elim _ _

set_option maxHeartbeats 800000 in
-- Normalize the original spin frame and the same scalar-extension Thom character.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Proposition 12.5 for the actual spin symbol and the normalized inverse Thom map. -/
theorem TopologicalSpinStructure.fiberIntegral_chernCharacter_spinorThom
    (S : TopologicalSpinStructure m E o hm hP)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x)) (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    compactSupportCohomologyFiberIntegral ℚ (2 * m) E
        S.integralCohomologyOrientation.rationalization (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (m + j)) ≅
              compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * j + 2 * m)).hom
          (bundleCompactSupportChernCharacterComponent (2 * m) E (m + j)
            S.spinorThomClass)) =
      (-1 : ℚ) ^ m • RealBundle.inverseAHatEvenComponent RealModel E hV j := by
  classical
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let := complexificationTopology RealModel E
  let := isFiniteRank_complexification RealModel E
  -- The original spin frame supplies a basis of this very scalar extension.
  have hr (b : B) : Module.finrank ℂ (ℂ ⊗[ℝ] E b) = 2 * m := by
    obtain ⟨p, hp⟩ := hP.projection_properties.2.2 b
    let β := (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.map
      (S.frame p b hp).toLinearEquiv
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis (β.baseChange ℂ)
  let δ (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) E
    S.integralCohomologyOrientation.rationalization (2 * n)
    ((eqToIso (by congr 1; omega) :
      compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (m + n)) ≅
        compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * n + 2 * m)).hom
      (bundleCompactSupportChernCharacterComponent (2 * m) E (m + n) S.spinorThomClass))
  -- The actual fiber symbol fixes the sign, while the supported self-product fixes the square.
  have hzero : δ 0 = (-1 : ℚ) ^ m • singularCohomologyOne ℚ B := by
    simpa only [δ, Nat.mul_zero, Nat.add_zero] using
      S.fiberIntegral_chernCharacter_spinorThom_zero
  have hsquare (n : ℕ) := S.fiberIntegral_chernCharacter_spinorThom_square hV hr n
  change δ j = (-1 : ℚ) ^ m • RealBundle.inverseAHatEvenComponent RealModel E hV j
  let inv := RealBundle.inverseAHatEvenComponent RealModel E hV
  let conv (a b : ∀ n, singularCohomology ℚ B (2 * n)) (n : ℕ) :=
    ∑ i : Fin (n + 1),
      (eqToIso (by congr 1; omega) :
        singularCohomology ℚ B (2 * (i.val + (n - i.val))) ≅
          singularCohomology ℚ B (2 * n)).hom
        (singularCohomologyEvenCup ℚ B i.val (n - i.val) (a i.val) (b (n - i.val)))
  have hodd (n : ℕ) (hn : ¬ Even n) : inv n = 0 := by
    dsimp only [inv, RealBundle.inverseAHatEvenComponent]
    exact dite_eq_right hn
  -- The actual inverse A-hat has only fourfold cohomological degrees.
  have hparity (n : ℕ) : (-1 : ℚ) ^ n • conv inv inv n = conv inv inv n := by
    by_cases hn : Even n
    · rw [hn.neg_one_pow, one_smul]
    · have hvan : conv inv inv n = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        by_cases hi : Even i.val
        · have hni : ¬ Even (n - i.val) := by
            intro hni
            apply hn
            simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)] using hi.add hni
          simp only [hodd _ hni, map_zero]
        · simp only [hodd _ hi, map_zero, LinearMap.zero_apply]
      rw [hvan, smul_zero]
  have hdsquare (n : ℕ) : conv δ δ n = conv inv inv n := by
    refine (hsquare n).trans ?_
    rw [hV.complexThomDefectComponent_eq_inverseTodd,
      RealBundle.inverseTodd_complexification_eq_inverseAHat_sq RealModel E hV]
    change (-1 : ℚ) ^ (2 * m + n) • conv inv inv n = conv inv inv n
    rw [pow_add, Even.neg_one_pow (even_two_mul m), one_mul]
    exact hparity n
  -- Homogeneous inclusion translates the finite cup convolutions into actual Cauchy products.
  let R := SingularEvenCohomology ℚ B
  let series (a : ∀ n, singularCohomology ℚ B (2 * n)) : PowerSeries R :=
    PowerSeries.mk (fun n ↦ singularEvenCohomologyOf ℚ B n (a n))
  have hcoeff (a b : PowerSeries R) (n : ℕ) :
      PowerSeries.coeff n (a * b) =
        ∑ i : Fin (n + 1), PowerSeries.coeff i.val a * PowerSeries.coeff (n - i.val) b := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i a * PowerSeries.coeff j b) n,
      Fin.sum_univ_eq_sum_range
        (fun i ↦ PowerSeries.coeff i a * PowerSeries.coeff (n - i) b) (n + 1)]
  have hconv (a b : ∀ n, singularCohomology ℚ B (2 * n)) (n : ℕ) :
      singularEvenCohomologyOf ℚ B n (conv a b n) =
        PowerSeries.coeff n (series a * series b) := by
    dsimp only [conv]
    rw [map_sum, hcoeff]
    apply Finset.sum_congr rfl
    intro i _
    rw [singularEvenCohomologyOf_eqToIso ℚ B (by omega), singularEvenCohomologyOf_cup]
    simp only [series, PowerSeries.coeff_mk]
  let D := series δ
  let I := series inv
  have hDI : D * D = I * I := by
    apply PowerSeries.ext
    intro n
    change PowerSeries.coeff n (series δ * series δ) =
      PowerSeries.coeff n (series inv * series inv)
    rw [← hconv δ δ n, ← hconv inv inv n, hdsquare n]
  have hDzero : D.constantCoeff = (-1 : ℚ) ^ m • (1 : R) := by
    simp only [D, series, PowerSeries.constantCoeff_mk, hzero, map_smul,
      singularEvenCohomologyOf_one]
  have hIzero : I.constantCoeff = 1 := by
    simp only [I, series, PowerSeries.constantCoeff_mk, inv,
      RealBundle.inverseAHatEvenComponent_zero, singularEvenCohomologyOf_one]
  -- The sum has unit constant coefficient, so its factor can be cancelled in any rational ring.
  let s : ℚ := (-1 : ℚ) ^ m
  have hs : s * s = 1 := by
    dsimp only [s]
    rw [← mul_pow]
    norm_num
  let J := s • I
  have hJ : J * J = I * I := by
    dsimp only [J]
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hs, one_smul]
  have hunit : IsUnit (D + J) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    change IsUnit (PowerSeries.constantCoeff (D + s • I))
    rw [map_add, PowerSeries.constantCoeff_smul, hDzero, hIzero, ← add_smul]
    have hsne : s + s ≠ 0 := by
      rw [← two_mul]
      exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
    simpa only [Algebra.algebraMap_eq_smul_one, s] using
      (isUnit_iff_ne_zero.mpr hsne).map (algebraMap ℚ R)
  have hfactorZero : (D - J) * (D + J) = 0 := by
    calc
      (D - J) * (D + J) = D * D - J * J := by ring
      _ = 0 := by rw [hDI, hJ, sub_self]
  have hseries : D = J := sub_eq_zero.mp (hunit.mul_left_eq_zero.mp hfactorZero)
  apply singularEvenCohomologyOf_injective ℚ B j
  have hc := congrArg (PowerSeries.coeff j) hseries
  simpa only [D, I, J, series, PowerSeries.coeff_smul, PowerSeries.coeff_mk,
    map_smul, inv, s] using hc

set_option maxHeartbeats 600000 in
-- Normalize the original virtual coefficient and the same normalized Thom inverse.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The same fiber-integral formula with any original virtual bundle coefficient. -/
theorem TopologicalSpinStructure.fiberIntegral_chernCharacter_spinThom
    (S : TopologicalSpinStructure m E o hm hP)
    (hV : letI := complexificationTopology RealModel E
      ContinuousHermitianMetric (fun x ↦ ℂ ⊗[ℝ] E x))
    (u : ComplexKZero B) (j : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle RealModel E
    compactSupportCohomologyFiberIntegral ℚ (2 * m) E
        S.integralCohomologyOrientation.rationalization (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * (m + j)) ≅
              compactSupportCohomology ℚ (TotalSpace RealModel E) (2 * j + 2 * m)).hom
          (bundleCompactSupportChernCharacterComponent (2 * m) E (m + j)
            (S.spinThomHom u))) =
      (-1 : ℚ) ^ m • ∑ i : Fin (j + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ B (2 * (i.val + (j - i.val))) ≅
              singularCohomology ℚ B (2 * j)).hom
          (singularCohomologyEvenCup ℚ B i.val (j - i.val)
            (chernCharacterKZeroComponent B i.val u)
            (RealBundle.inverseAHatEvenComponent RealModel E hV (j - i.val))) := by
  let := RealBundle.isFiniteRank_of_vectorBundle RealModel E
  let Y := TotalSpace RealModel E
  let πE := bundleProjection (2 * m) E
  let O := S.integralCohomologyOrientation.rationalization
  let oneK := AtiyahSinger.kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1)
  let τ := S.spinorThomClass
  let d (n : ℕ) := bundleCompactSupportChernCharacterComponent (2 * m) E n τ
  let δ (n : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * n)
    ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ Y (2 * (m + n)) ≅
      compactSupportCohomology ℚ Y (2 * n + 2 * m)).hom (d (m + n)))
  have haction : S.spinThomHom u = complexKZeroCompactSupportAction πE u τ := rfl
  have hunit : S.spinThomHom oneK = τ := complexKZeroCompactSupportAction_one πE τ
  -- First retain the untwisted coefficient as the inverse of the same normalized Thom map.
  have hconv : compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
      ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ Y (2 * (m + j)) ≅
        compactSupportCohomology ℚ Y (2 * j + 2 * m)).hom
        (bundleCompactSupportChernCharacterComponent (2 * m) E (m + j) (S.spinThomHom u))) =
      ∑ i : Fin (j + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ B (2 * (i.val + (j - i.val))) ≅
              singularCohomology ℚ B (2 * j)).hom
          (singularCohomologyEvenCup ℚ B i.val (j - i.val)
            (chernCharacterKZeroComponent B i.val u) (δ (j - i.val))) := by
    -- Keep all canonical degree changes local; they carry no mathematical choices.
    let cT {m n : ℕ} (hmn : m = n) : compactSupportCohomology ℚ Y m →ₗ[ℚ]
        compactSupportCohomology ℚ Y n :=
      (eqToIso (congrArg (compactSupportCohomology ℚ Y) hmn)).hom.hom
    let cH {m n : ℕ} (hmn : m = n) : singularCohomology ℚ B m →ₗ[ℚ]
        singularCohomology ℚ B n :=
      (eqToIso (congrArg (singularCohomology ℚ B) hmn)).hom.hom
    have cT_trans {m n l : ℕ} (hmn : m = n) (hnl : n = l)
        (b : compactSupportCohomology ℚ Y m) :
        cT hnl (cT hmn b) = cT (hmn.trans hnl) b := by
      subst n
      subst l
      rfl
    have cH_trans {m n l : ℕ} (hmn : m = n) (hnl : n = l)
        (b : singularCohomology ℚ B m) : cH hnl (cH hmn b) = cH (hmn.trans hnl) b := by
      subst n
      subst l
      rfl
    have cT_action (p : ℕ) {q q' : ℕ} (hqq : q = q')
        (a : singularCohomology ℚ Y p) (b : compactSupportCohomology ℚ Y q) :
        cT (congrArg (p + ·) hqq) (compactSupportCohomologyAction ℚ Y p q a b) =
          compactSupportCohomologyAction ℚ Y p q' a (cT hqq b) := by
      subst q'
      rfl
    have cT_integral {p q : ℕ} (hpq : p = q)
        (b : compactSupportCohomology ℚ Y (p + 2 * m)) :
        compactSupportCohomologyFiberIntegral ℚ (2 * m) E O q (cT (congrArg (· + 2 * m) hpq) b) =
          cH hpq (compactSupportCohomologyFiberIntegral ℚ (2 * m) E O p b) := by
      subst q
      rfl
    have cT_d {m n : ℕ} (hmn : m = n) : cT (congrArg (2 * ·) hmn) (d m) = d n := by
      subst n
      rfl
    let F (i : Fin (m + j + 1)) : singularCohomology ℚ B (2 * j) :=
      compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
        (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val)
          (2 * (m + j - i.val))
          (singularCohomologyPullback ℚ πE (2 * i.val) (chernCharacterKZeroComponent B i.val u))
          (d (m + j - i.val))))
    -- Apply the supported action before distributing this same integral over the finite sum.
    have hsum : compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
        ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ Y (2 * (m + j)) ≅
          compactSupportCohomology ℚ Y (2 * j + 2 * m)).hom
          (bundleCompactSupportChernCharacterComponent (2 * m) E (m + j)
            (S.spinThomHom u))) =
        ∑ i : Fin (m + j + 1), F i := by
      rw [haction, bundleCompactSupportChernCharacterComponent_action]
      simp only [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      change compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
        (cT (by omega) (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val)
          (2 * (m + j - i.val)) _ (d (m + j - i.val))))) = F i
      rw [cT_trans (show 2 * i.val + 2 * (m + j - i.val) = 2 * (m + j) by omega)
        (show 2 * (m + j) = 2 * j + 2 * m by omega)]
    -- Each retained term uses the projection formula and exactly the original unit-symbol defect.
    have hterm (i : Fin (m + j + 1)) (hi : i.val ≤ j) : F i =
        (eqToIso (by congr 1; omega) : singularCohomology ℚ B (2 * (i.val + (j - i.val))) ≅
          singularCohomology ℚ B (2 * j)).hom
          (singularCohomologyEvenCup ℚ B i.val (j - i.val)
            (chernCharacterKZeroComponent B i.val u)
            (δ (j - i.val))) := by
      let a := chernCharacterKZeroComponent B i.val u
      let b := d (m + j - i.val)
      have hindex : m + j - i.val = m + (j - i.val) := by omega
      have hdegree : 2 * i.val + 2 * (j - i.val) = 2 * j := by omega
      have hbdegree : 2 * (m + j - i.val) = 2 * (j - i.val) + 2 * m := by omega
      change compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * j)
        (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (m + j - i.val))
          (singularCohomologyPullback ℚ πE (2 * i.val) a) (d (m + j - i.val)))) = _
      have hnormalize : cT (by omega)
          (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (m + j - i.val))
            (singularCohomologyPullback ℚ πE (2 * i.val) a) b) =
        cT (congrArg (· + 2 * m) hdegree)
          (cT (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * m)).symm
            (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (j - i.val) + 2 * m)
              (singularCohomologyPullback ℚ πE (2 * i.val) a) (cT hbdegree b))) := by
        rw [← cT_action (2 * i.val) hbdegree,
          cT_trans (congrArg (2 * i.val + ·) hbdegree)
            (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * m)).symm,
          cT_trans ((congrArg (2 * i.val + ·) hbdegree).trans
            (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * m)).symm)
            (congrArg (· + 2 * m) hdegree)]
      rw [hnormalize, cT_integral hdegree]
      change cH hdegree
        (compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * i.val + 2 * (j - i.val))
          ((eqToIso (by rw [Nat.add_assoc]) :
              compactSupportCohomology ℚ Y ((2 * i.val + 2 * (j - i.val)) + 2 * m) ≅
                compactSupportCohomology ℚ Y (2 * i.val + (2 * (j - i.val) + 2 * m))).inv
            (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (j - i.val) + 2 * m)
              (singularCohomologyPullback ℚ πE (2 * i.val) a) (cT hbdegree b)))) = _
      rw [compactSupportCohomologyFiberIntegral_action]
      have hdefect : compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * (j - i.val))
          (cT hbdegree b) = δ (j - i.val) := by
        change compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * (j - i.val))
          (cT hbdegree b) =
          compactSupportCohomologyFiberIntegral ℚ (2 * m) E O (2 * (j - i.val))
            (cT (show 2 * (m + (j - i.val)) = 2 * (j - i.val) + 2 * m by omega)
              (d (m + (j - i.val))))
        rw [← cT_d hindex, cT_trans (congrArg (2 * ·) hindex)
          (show 2 * (m + (j - i.val)) = 2 * (j - i.val) + 2 * m by omega)]
      rw [hdefect]
      change cH hdegree (singularCohomologyCup ℚ B (2 * i.val) (2 * (j - i.val)) a
        (δ (j - i.val))) =
        cH (by omega) (cH (by omega) (singularCohomologyCup ℚ B (2 * i.val) (2 * (j - i.val)) a
          (δ (j - i.val))))
      rw [cH_trans (show 2 * i.val + 2 * (j - i.val) = 2 * (i.val + (j - i.val)) by omega)
        (show 2 * (i.val + (j - i.val)) = 2 * j by omega)]
    -- Terms beyond j vanish in the original support group before integration.
    have hzero (i : Fin (m + j + 1)) (hi : j < i.val) : F i = 0 := by
      have hd : d (m + j - i.val) = 0 :=
        by
          have hz := S.compactSupportChernCharacter_spinThom_eq_zero_of_lt oneK
            (m + j - i.val) (by omega)
          simpa only [hunit] using hz
      dsimp only [F]
      rw [hd]
      simp only [map_zero]
    rw [hsum]
    have hsize : (j + 1) + m = m + j + 1 := by omega
    rw [← Fin.sum_congr' F hsize]
    have htail (i : Fin m) : F ((Fin.natAdd (j + 1) i).cast hsize) = 0 :=
      hzero _ (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)
    rw [Fin.sum_trunc (fun i : Fin ((j + 1) + m) ↦ F (i.cast hsize)) htail]
    apply Finset.sum_congr rfl
    intro i _
    exact hterm _ (by simpa only [Fin.val_cast, Fin.val_castAdd] using Nat.le_of_lt_succ i.isLt)
  -- The untwisted Spin formula supplies precisely those coefficients, with one fixed sign.
  rw [hconv, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hδ : δ (j - i.val) =
      (-1 : ℚ) ^ m • RealBundle.inverseAHatEvenComponent RealModel E hV (j - i.val) :=
    S.fiberIntegral_chernCharacter_spinorThom hV (j - i.val)
  rw [hδ, map_smul, map_smul]

end AtiyahSinger
