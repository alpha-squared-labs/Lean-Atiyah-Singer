/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GlobalChernLocalComparison
public import AtiyahSinger.Topology.InverseTodd

/-!
# Characteristic components of the original complex line

Public module ID: M1931.

The original cohomology model transports the given line to its native rank-one
presentation. Its single actual flag root computes the global Chern character
and inverse Todd components as powers of the same original first Chern class.
The formulas retain arbitrary original fiber universes and the supplied metric.

Source: SG III.11, the Chern-character and multiplicative-sequence root formulas;
SG III.12, the line factor in the Thom-character comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (hline : ∀ x, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hline in
/-- The original line Chern character is the degreewise exponential of its first Chern class. -/
theorem globalChernCharacterComponent_eq_pow_of_finrank_eq_one (k : ℕ) :
    globalChernCharacterComponent E h k = (Nat.factorial k : ℚ)⁻¹ •
      singularCohomologyDegreeTwoPow ℚ X
        (singularCohomologyRationalization X 2 (globalChernClass E h 1)) k := by
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  let hM := cohomologyModelMetric E h
  have hMrank (x : X) : Module.finrank ℂ (M x) = 1 :=
    (cohomologyModelLinearEquiv E x).finrank_eq.trans (hline x)
  let e : Iso M (((ContinuousMap.id X : C(X, X)) : X → X) *ᵖ E) :=
    (cohomologyModelIso E).trans (pullbackIdIso (E := E)).symm
  have hchar := globalChernCharacterComponent_pullback_eq_chernCharacterComponent
    E h (ContinuousMap.id X) M hM 1 hMrank e k
  have hchern := globalChernClass_pullback_eq_chernClass
    E h (ContinuousMap.id X) M hM 1 hMrank e 1
  have hid (R : Type) [CommRing R] (j : ℕ) :
      singularCohomologyPullback R (ContinuousMap.id X) j =
        𝟙 (singularCohomology R X j) := (singularCohomologyFunctor R j).map_id _
  rw [hid, ModuleCat.id_apply] at hchar hchern
  let : ∀ x, NormedAddCommGroup (M x) := hM.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (M x) := hM.fiberInnerProductSpace
  let := nativeModelTopology M (EuclideanSpace ℂ (Fin 1))
  let := hM.nativeFiberBundle 1 hMrank
  let := hM.nativeVectorBundle 1 hMrank
  let hN := hM.nativeModelMetric 1
  let := hermitianFlagTopology 1 M hN
  let Q := HermitianFlagBundle 1 M hN
  let p := hermitianFlagProjection 1 M hN
  -- The only actual flag root is exactly the pullback of the original global first class.
  have hroot : singularCohomologyPullback ℤ p 2 (globalChernClass E h 1) =
      flagChernRoot 1 M hN 0 := by
    rw [hchern, chernClass_flag_pullback 1 M hN 1]
    apply singularEvenCohomologyOf_injective ℤ Q 1
    rw [singularEvenCohomologyOf_elementarySymmetric]
    simp [List.ofFn_succ, Multiset.esymm, Multiset.powersetCard_one]
  have hpow (a : singularCohomology ℚ X 2) (j : ℕ) :
      singularCohomologyPullback ℚ p (2 * j) (singularCohomologyDegreeTwoPow ℚ X a j) =
        singularCohomologyDegreeTwoPow ℚ Q (singularCohomologyPullback ℚ p 2 a) j := by
    apply singularEvenCohomologyOf_injective ℚ Q j
    rw [← singularEvenCohomologyPullback_of, singularEvenCohomologyOf_degreeTwoPow,
      map_pow, singularEvenCohomologyPullback_of, singularEvenCohomologyOf_degreeTwoPow]
  -- The one-root normalized power sum gives the claimed original degree-k component.
  apply hermitianFlagProjection_cohomology_injective ℚ 1 M hN (2 * k)
  rw [hchar, chernCharacterComponent_flag_pullback, map_smul, hpow,
    ← singularCohomologyRationalization_naturality, hroot]
  simp only [Fin.sum_univ_one]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include hline in
/-- The original inverse Todd component of a line is its normalized factorial root coefficient. -/
theorem inverseToddClassComponent_eq_pow_of_finrank_eq_one (k : ℕ) :
    inverseToddClassComponent E h k = ((-1 : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ)) •
      singularCohomologyDegreeTwoPow ℚ X
        (singularCohomologyRationalization X 2 (globalChernClass E h 1)) k := by
  classical
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  let hM := cohomologyModelMetric E h
  have hMrank (x : X) : Module.finrank ℂ (M x) = 1 :=
    (cohomologyModelLinearEquiv E x).finrank_eq.trans (hline x)
  let e : Iso M (((ContinuousMap.id X : C(X, X)) : X → X) *ᵖ E) :=
    (cohomologyModelIso E).trans (pullbackIdIso (E := E)).symm
  have hchern (j : ℕ) := globalChernClass_pullback_eq_chernClass
    E h (ContinuousMap.id X) M hM 1 hMrank e j
  have hid (j : ℕ) : singularCohomologyPullback ℤ (ContinuousMap.id X) j =
      𝟙 (singularCohomology ℤ X j) := (singularCohomologyFunctor ℤ j).map_id _
  simp only [hid, ModuleCat.id_apply] at hchern
  let : ∀ x, NormedAddCommGroup (M x) := hM.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (M x) := hM.fiberInnerProductSpace
  let := nativeModelTopology M (EuclideanSpace ℂ (Fin 1))
  let := hM.nativeFiberBundle 1 hMrank
  let := hM.nativeVectorBundle 1 hMrank
  let hN := hM.nativeModelMetric 1
  let := hermitianFlagTopology 1 M hN
  let Q := HermitianFlagBundle 1 M hN
  let p := hermitianFlagProjection 1 M hN
  let roots : Fin 1 → singularCohomology ℚ Q 2 := fun i ↦
    singularCohomologyRationalization Q 2 (flagChernRoot 1 M hN i)
  -- Every original global Chern input becomes the same one-root elementary coefficient.
  have hck (j : ℕ) : singularCohomologyPullback ℚ p (2 * j)
      (singularCohomologyRationalization X (2 * j) (globalChernClass E h j)) =
        singularCohomologyElementarySymmetric ℚ Q (List.ofFn roots) j := by
    rw [← singularCohomologyRationalization_naturality, hchern j,
      chernClass_flag_pullback 1 M hN j, singularCohomologyRationalization_elementarySymmetric]
    simp only [List.map_ofFn]
    rfl
  have hroot : singularCohomologyPullback ℚ p 2
      (singularCohomologyRationalization X 2 (globalChernClass E h 1)) = roots 0 := by
    rw [hck 1]
    apply singularEvenCohomologyOf_injective ℚ Q 1
    rw [singularEvenCohomologyOf_elementarySymmetric]
    simp [List.ofFn_succ, Multiset.esymm, Multiset.powersetCard_one]
  -- Invert the normalized unit series; this is not division by a cohomology class.
  let q : PowerSeries ℚ := toddCharacteristicSeries⁻¹
  have hq : q.constantCoeff = 1 := by
    simp [q, characteristicSeries_normalization.1]
  have hqk : PowerSeries.coeff k q = (-1 : ℚ) ^ k / (Nat.factorial (k + 1) : ℚ) := by
    have hs : q = PowerSeries.mk (fun j : ℕ ↦
        (-1 : ℚ) ^ j / (Nat.factorial (j + 1) : ℚ)) := by
      apply (PowerSeries.inv_eq_iff_mul_eq_one (by
        rw [characteristicSeries_normalization.1]
        exact one_ne_zero)).mpr
      exact PowerSeries.mul_inv_cancel _ (by simp)
    rw [hs, PowerSeries.coeff_mk]
  apply hermitianFlagProjection_cohomology_injective ℚ 1 M hN (2 * k)
  unfold inverseToddClassComponent
  rw [singularCohomologyWeightedPolynomial_pullback]
  change singularCohomologyWeightedPolynomial Q (fun i : Fin k ↦ i.val + 1)
    (fun i ↦ singularCohomologyPullback ℚ p (2 * (i.val + 1))
      (singularCohomologyRationalization X (2 * (i.val + 1))
        (globalChernClass E h (i.val + 1)))) (MultiplicativeSequence.polynomial q k) k = _
  simp_rw [hck]
  apply singularEvenCohomologyOf_injective ℚ Q k
  rw [singularEvenCohomologyOf_weightedPolynomial Q _ _ _ k
    (MultiplicativeSequence.polynomial_isWeightedHomogeneous q k)]
  rw [map_smul, map_smul, ← singularEvenCohomologyPullback_of,
    singularEvenCohomologyOf_degreeTwoPow, map_pow,
    singularEvenCohomologyPullback_of, hroot]
  let y : Fin 1 → SingularEvenCohomology ℚ Q :=
    fun i ↦ singularEvenCohomologyOf ℚ Q 1 (roots i)
  have heval (i : Fin k) : singularEvenCohomologyOf ℚ Q (i.val + 1)
      (singularCohomologyElementarySymmetric ℚ Q (List.ofFn roots) (i.val + 1)) =
        MvPolynomial.aeval y (MvPolynomial.esymm (Fin 1) ℚ (i.val + 1)) := by
    rw [singularEvenCohomologyOf_elementarySymmetric,
      MvPolynomial.aeval_esymm_eq_multiset_esymm, ← Fin.univ_val_map, Multiset.map_map]
    rfl
  -- The stable polynomial identity evaluates to one factor on this actual single root.
  calc
    _ = MvPolynomial.aeval
        (fun i : Fin k ↦ MvPolynomial.aeval y (MvPolynomial.esymm (Fin 1) ℚ (i.val + 1)))
        (MultiplicativeSequence.polynomial q k) := by
      apply congrArg (fun a : Fin k → SingularEvenCohomology ℚ Q ↦
        MvPolynomial.aeval a (MultiplicativeSequence.polynomial q k))
      funext i
      exact heval i
    _ = MvPolynomial.aeval y
        (MvPolynomial.aeval (fun i : Fin k ↦ MvPolynomial.esymm (Fin 1) ℚ (i.val + 1))
          (MultiplicativeSequence.polynomial q k)) :=
      (MvPolynomial.comp_aeval_apply
        (fun i : Fin k ↦ MvPolynomial.esymm (Fin 1) ℚ (i.val + 1))
        (MvPolynomial.aeval y) _).symm
    _ = MvPolynomial.aeval y (PowerSeries.coeff k (MultiplicativeSequence.rootProduct q 1)) :=
      congrArg (MvPolynomial.aeval y) (MultiplicativeSequence.polynomial_esymm q hq 1 k)
    _ = _ := by
      simp only [MultiplicativeSequence.rootProduct, Fin.prod_univ_one, PowerSeries.coeff_mk,
        map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X, hqk, Algebra.smul_def]
      rfl

end AtiyahSinger.ComplexBundle
