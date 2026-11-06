/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.LowDimensionalRepresentationRing
public import AtiyahSinger.Analysis.EquivariantAnalyticIndexRestriction
public import AtiyahSinger.Analysis.OrthogonalCirclePointIndex
public import AtiyahSinger.Geometry.SpecialOrthogonalGroupManifold

/-!
# Low-dimensional equivariant point normalization

Public module ID: M0796.

AL03: ASI I Lemma (4.7), pp.507--508. The first two theorems retain the source's
generality for arbitrary additive index maps. They assume precisely the finite
instances of the source axioms used here: naturality under the actual pole-swapping
reflection, the original de Rham values, and, for O(1), representation linearity
and restriction to the ordinary circle index. Full excision implies this
diffeomorphism naturality.

The subsequent theorems instantiate the argument for the original analytic
index. The SO(2) value is restriction of the original O(2) index of the same
class. Its domain is still the O(2) K group: the explicit factorization theorem
is essential before using equality in the SO(2) K group. There is no inverse
of K restriction, no surjectivity assumption, and no cancellation in R(O(2)).

The O(1) argument retains the ordinary dimension-one condition. Multiplication
by 1 minus the determinant class alone cannot determine a representation.
The analytic restriction factorization below ensures the normalization argument
uses the same restricted classes and the same original analytic index.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent continuousSMul_orthogonalSphereCotangent
  t2Space_cotangent locallyCompactSpace_cotangent

local notation "O1" => Matrix.orthogonalGroup (Fin 1) ℝ
local notation "O2" => Matrix.orthogonalGroup (Fin 2) ℝ
local notation "SO2" => Matrix.specialOrthogonalGroup (Fin 2) ℝ
local notation "K1" => EquivariantSupportTripleKZero O1
  (TangentBundle (𝓡 1) (OrthogonalSphere 1))
local notation "K2" => EquivariantSupportTripleKZero O2
  (TangentBundle (𝓡 2) (OrthogonalSphere 2))
local notation "KS2" => EquivariantSupportTripleKZero SO2
  (TangentBundle (𝓡 2) (OrthogonalSphere 2))
local notation "ξ" => finiteRepresentationClass (orthogonalDeterminantRepresentation 1)

/-- The O(1) part of ASI Lemma (4.7), for any index satisfying the needed source axioms. -/
theorem orthogonalCircle_point_index_eq_one_of_axioms
    (J : K1 →+ RepresentationGrothendieckGroup O1)
    (I₀ : CompactSupportKZero (CotangentTotalSpace (n := 1) (M := Circle)) →+ ℤ)
    (g₀ : SmoothTangentMetric (n := 0) (M := EuclideanSpace ℝ (Fin 0)))
    (g₁ : SmoothTangentMetric (n := 1) (M := Circle))
    (hModule : ∀ (a : RepresentationGrothendieckGroup O1) (u : K1),
      J (a • u) = a • J u)
    (hReflection : ∀ u : K1, J (orthogonalSphereReflectionPullback 1 u) = J u)
    (hDeRham : J (orthogonalSphereDeRhamClass 1) = 1 - ξ)
    (hRestriction : ∀ u : K1,
      representationDimension O1 (J u) = I₀ (orthogonalCircleKZeroForget u))
    (hPoint : ∀ a : Circle, I₀ (circlePointPushforward a g₀ g₁) = 1)
    (atInfinity : Bool) :
    J (orthogonalSpherePolePushforward 1 atInfinity 1) = 1 := by
  let P (b : Bool) := orthogonalSpherePolePushforward 1 b 1
  -- Reflection exchanges the actual poles and therefore their values under this same J.
  have hpoles (b : Bool) : J (P (!b)) = J (P b) := by
    have h := hReflection (P b)
    simpa only [P, orthogonalSphereReflectionPullback_pole] using h
  have hsplit := congrArg J (orthogonalSphereDeRhamClass_eq_pole_sum 1)
  rw [orthogonalCircleTangentNegation_pole, map_add, map_neg, hModule,
    hDeRham] at hsplit
  have hdet : (1 - ξ) * J (P false) = 1 - ξ := by
    have hp : J (P true) = J (P false) := hpoles false
    change 1 - ξ = J (P false) + -(ξ * J (P true)) at hsplit
    rw [hp] at hsplit
    calc
      _ = J (P false) + -(ξ * J (P false)) := by ring
      _ = 1 - ξ := hsplit.symm
  -- Retain the augmentation condition: multiplication by 1 - det is not injective.
  have hdim : representationDimension O1 (J (P false)) = 1 := by
    rw [hRestriction]
    change I₀ (orthogonalCircleKZeroForget (orthogonalSpherePolePushforward 1 false 1)) = 1
    rw [orthogonalCircleKZeroForget_polePushforward false g₀ g₁]
    exact hPoint _
  have hone := orthogonalLine_eq_one_of_one_sub_det_mul_eq_of_dimension
    (J (P false)) hdet hdim
  cases atInfinity
  · exact hone
  · exact (hpoles false).trans hone

/-- The SO(2) part of ASI Lemma (4.7), on the actual restricted tangent support group. -/
theorem specialOrthogonalPlane_point_index_eq_one_of_axioms
    (J : KS2 →+ RepresentationGrothendieckGroup SO2)
    (hReflection : ∀ u : KS2,
      J (specialOrthogonalSphereReflectionPullback 2 u) = J u)
    (hDeRham : J (orthogonalSphereTangentRestrict 2
      (orthogonalSphereDeRhamClass 2)) = 2)
    (atInfinity : Bool) :
    J (orthogonalSphereTangentRestrict 2
      (orthogonalSpherePolePushforward 2 atInfinity 1)) = 1 := by
  /- Stage 1: restrict the original de Rham decomposition using the
  actual support restriction homomorphism. The restricted theta-pole
  identity removes theta on this class in K_SO(2), where it is valid.
  Stage 2: the reflection restriction square and original pole comparison,
  followed by hReflection, identify the two actual pole values under J.
  Additivity and hDeRham give 2*a=2 for their common SO(2) representation.
  Stage 3: specialOrthogonalPlane_eq_one_of_two_mul_eq_two gives a=1.
  This only cancels the integer two in the actual torsion-free additive
  representation group. No R-linearity beyond additivity is needed in
  this case, so every source R(SO(2))-linear index is covered as well. -/
  let P (b : Bool) := orthogonalSphereTangentRestrict 2
    (orthogonalSpherePolePushforward 2 b 1)
  have hpoles (b : Bool) : J (P (!b)) = J (P b) := by
    have hsquare := DFunLike.congr_fun
      (orthogonalSphereTangentRestrict_reflectionPullback 2)
      (orthogonalSpherePolePushforward 2 b 1)
    simp only [AddMonoidHom.comp_apply, orthogonalSphereReflectionPullback_pole] at hsquare
    exact (congrArg J hsquare).trans (hReflection (P b))
  have hsplit := congrArg (fun u : K2 ↦ J (orthogonalSphereTangentRestrict 2 u))
    (orthogonalSphereDeRhamClass_eq_pole_sum 2)
  simp only [map_add, specialOrthogonalPlaneTangentNegation_pole] at hsplit
  have htwo : 2 * J (P false) = 2 := by
    have hp : J (P true) = J (P false) := hpoles false
    rw [hDeRham] at hsplit
    change 2 = J (P false) + J (P true) at hsplit
    rw [hp] at hsplit
    exact (two_mul _).trans hsplit.symm
  have hone := specialOrthogonalPlane_eq_one_of_two_mul_eq_two (J (P false)) htwo
  cases atInfinity
  · exact hone
  · exact (hpoles false).trans hone

open scoped Matrix.Norms.L2Operator in
/-- Equality after actual SO(2) K restriction gives equality of the restricted analytic indices. -/
theorem representationRestriction_orthogonalSphereTangentIndex_eq
    (u v : K2) (h : orthogonalSphereTangentRestrict 2 u =
      orthogonalSphereTangentRestrict 2 v) :
    representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
        (orthogonalSphereTangentAnalyticIndex 2 u) =
      representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
        (orthogonalSphereTangentAnalyticIndex 2 v) := by
  -- Equip the native groups and sphere with the original compact Lie and Borel structures.
  let := lieGroup_orthogonalGroup 2
  let := lieGroup_specialOrthogonalGroup 2
  let := compactSpace_orthogonalGroup 2
  let := compactSpace_specialOrthogonalGroup 2
  let : MeasurableSpace (Matrix.orthogonalGroup (Fin 2) ℝ) :=
    borel (Matrix.orthogonalGroup (Fin 2) ℝ)
  let : BorelSpace (Matrix.orthogonalGroup (Fin 2) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (Matrix.specialOrthogonalGroup (Fin 2) ℝ) :=
    borel (Matrix.specialOrthogonalGroup (Fin 2) ℝ)
  let : BorelSpace (Matrix.specialOrthogonalGroup (Fin 2) ℝ) := ⟨rfl⟩
  let : MeasurableSpace (OrthogonalSphere 2) := borel (OrthogonalSphere 2)
  let : BorelSpace (OrthogonalSphere 2) := ⟨rfl⟩
  let φ := specialOrthogonalGroupInclusion 2
  have hφ := contMDiff_specialOrthogonalGroupInclusion 2
  let : MulAction (Matrix.specialOrthogonalGroup (Fin 2) ℝ) (OrthogonalSphere 2) :=
    MulAction.compHom _ φ.toMonoidHom
  let : ContinuousSMul (Matrix.specialOrthogonalGroup (Fin 2) ℝ) (OrthogonalSphere 2) :=
    MulAction.continuousSMul_compHom φ.continuous
  let : ContMDiffSMul 𝓘(ℝ, OrthogonalGroupModel 2) (𝓡 2) ∞
      (Matrix.specialOrthogonalGroup (Fin 2) ℝ) (OrthogonalSphere 2) :=
    MulAction.contMDiffSMul_compHom hφ
  -- Restriction commutes with the same inverse round-musical pullback.
  -- Thus the given tangent-class equality yields equality of restricted cotangent classes.
  have hmusical : equivariantCotangentKZeroRestrict
      (VG := OrthogonalGroupModel 2) (VH := OrthogonalGroupModel 2) φ hφ
      (orthogonalSphereMusicalKMap 2 u) =
    equivariantCotangentKZeroRestrict
      (VG := OrthogonalGroupModel 2) (VH := OrthogonalGroupModel 2) φ hφ
      (orthogonalSphereMusicalKMap 2 v) := by
    change equivariantSupportTripleKZeroRestrict φ (orthogonalSphereMusicalKMap 2 u) =
      equivariantSupportTripleKZeroRestrict φ (orthogonalSphereMusicalKMap 2 v)
    have hs := equivariantSupportTripleKZeroRestrict_pullback φ
      ⟨(orthogonalSphereRoundMetric 2).flatHomeomorph.symm,
        (orthogonalSphereRoundMetric 2).flatHomeomorph.symm.continuous⟩
      (orthogonalSphereRoundMetric_flat_symm_equivariant 2)
      (orthogonalSphereRoundMetric 2).flatHomeomorph.symm.isProperMap
    have hu := DFunLike.congr_fun hs u
    have hv := DFunLike.congr_fun hs v
    change equivariantSupportTripleKZeroRestrict φ (orthogonalSphereMusicalKMap 2 u) = _ at hu
    change equivariantSupportTripleKZeroRestrict φ (orthogonalSphereMusicalKMap 2 v) = _ at hv
    rw [hu, hv]
    simp only [AddMonoidHom.comp_apply]
    exact congrArg _ h
  -- The full representation-valued restriction theorem evaluates those same classes.
  -- No lift of an arbitrary SO(2) class or cancellation of K restriction is needed.
  have hiu := DFunLike.congr_fun
    (representationRestriction_equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel 2) (VH := OrthogonalGroupModel 2) φ hφ)
    (orthogonalSphereMusicalKMap 2 u)
  have hiv := DFunLike.congr_fun
    (representationRestriction_equivariantAnalyticIndexMap
      (VG := OrthogonalGroupModel 2) (VH := OrthogonalGroupModel 2) φ hφ)
    (orthogonalSphereMusicalKMap 2 v)
  exact hiu.trans ((congrArg
    (equivariantAnalyticIndexMap (n := 2) (M := OrthogonalSphere 2)
      (VG := OrthogonalGroupModel 2) (G := Matrix.specialOrthogonalGroup (Fin 2) ℝ))
    hmusical).trans hiv.symm)

/-- The original O(1)-equivariant analytic index of either actual pole pushforward is one. -/
theorem orthogonalCirclePoleIndex_eq_one (atInfinity : Bool) :
    orthogonalSphereTangentAnalyticIndex 1
      (orthogonalSpherePolePushforward 1 atInfinity 1) = 1 := by
  -- Use the original index and the same positive density in every finite axiom.
  let g₀ := (SmoothTangentMetric.nonempty
    (n := 0) (M := EuclideanSpace ℝ (Fin 0))).some
  let g₁ := (SmoothTangentMetric.nonempty (n := 1) (M := Circle)).some
  let := isSmoothPositiveMeasure_fourierCircleMeasure
  apply orthogonalCircle_point_index_eq_one_of_axioms
    (orthogonalSphereTangentAnalyticIndex 1)
    (analyticIndexOfComponents fourierCircleMeasure) g₀ g₁
  · exact orthogonalSphereTangentAnalyticIndex_smul 1
  · exact orthogonalSphereTangentAnalyticIndex_reflectionPullback 1
  · exact (orthogonalSphereTangentAnalyticIndex_deRhamClass 1).trans
      orthogonalCircleDeRhamIndex_eq_one_sub_det
  · exact representationDimension_orthogonalCircleTangentIndex fourierCircleMeasure
  · intro a
    exact analyticIndexOfComponents_circlePointPushforward a g₀ g₁ fourierCircleMeasure

/-- Restricting the actual O(2) pole index to SO(2) gives the trivial representation. -/
theorem specialOrthogonalPlanePoleIndex_eq_one (atInfinity : Bool) :
    representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
      (orthogonalSphereTangentAnalyticIndex 2
        (orthogonalSpherePolePushforward 2 atInfinity 1)) = 1 := by
  let R := representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
  let J := orthogonalSphereTangentAnalyticIndex 2
  let P (b : Bool) := orthogonalSpherePolePushforward 2 b 1
  -- Reflection already identifies the indices before representation restriction.
  have hpoles (b : Bool) : R (J (P (!b))) = R (J (P b)) := by
    have h := orthogonalSphereTangentAnalyticIndex_reflectionPullback 2 (P b)
    rw [orthogonalSphereReflectionPullback_pole] at h
    exact congrArg R h
  -- Theta disappears only after the actual SO(2) K restriction; use its factorization.
  have htheta : R (J (orthogonalSphereTangentNegationPullback 2 (P true))) =
      R (J (P true)) :=
    representationRestriction_orthogonalSphereTangentIndex_eq _ _
      (specialOrthogonalPlaneTangentNegation_pole true)
  have hsplit := congrArg (fun u : K2 ↦ R (J u))
    (orthogonalSphereDeRhamClass_eq_pole_sum 2)
  have hdeRham : R (J (orthogonalSphereDeRhamClass 2)) = 2 := by
    change representationRestrictionRingHom (specialOrthogonalGroupInclusion 2)
      (orthogonalSphereTangentAnalyticIndex 2 (orthogonalSphereDeRhamClass 2)) = 2
    rw [orthogonalSphereTangentAnalyticIndex_deRhamClass,
      ← restrictedOrthogonalSphereDeRhamIndex_eq_restriction]
    exact specialOrthogonalTwoSphereDeRhamIndex_eq_two
  simp only [map_add] at hsplit
  change R (J (orthogonalSphereDeRhamClass 2)) =
    R (J (P false)) + R (J (orthogonalSphereTangentNegationPullback 2 (P true))) at hsplit
  have hp : R (J (P true)) = R (J (P false)) := hpoles false
  rw [hdeRham, htheta, hp] at hsplit
  have htwo : 2 * R (J (P false)) = 2 := (two_mul _).trans hsplit.symm
  have hone := specialOrthogonalPlane_eq_one_of_two_mul_eq_two (R (J (P false))) htwo
  cases atInfinity
  · exact hone
  · exact (hpoles false).trans hone

end AtiyahSinger
