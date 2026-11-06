/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernClass
public import AtiyahSinger.Topology.CohomologyRationalizationPolynomials
public import AtiyahSinger.Topology.EvenCohomologyNewton
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# The degreewise rational Chern character of the original complex bundle

Public module ID: M1605.

C02: SG III.11, (11.22)--(11.23), Proposition 11.16 and Corollary 11.17.
The k-th component is the unique class whose original flag pullback is the
sum of k-th powers of the normalized rational Chern roots divided by k!.
Existence follows from the integral Chern classes and Newton identities;
flag injectivity is used for uniqueness, never as an existence argument.

Components are kept separately, so no finite-dimensional-base assumption or
unsupported infinite sum in a direct-sum cohomology ring occurs. This module
does not descend to the complex K group, introduce compact supports,
or construct Todd, Pontryagin or A-hat classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianFlagTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized power-sum class of the actual line roots descends uniquely to the base. -/
theorem existsUnique_chernCharacterComponent (k : ℕ) :
    ∃! c : singularCohomology ℚ X (2 * k),
      singularCohomologyPullback ℚ (hermitianFlagProjection r E h) (2 * k) c =
        (Nat.factorial k : ℚ)⁻¹ •
          ∑ i : Fin r, singularCohomologyDegreeTwoPow ℚ (HermitianFlagBundle r E h)
            (singularCohomologyRationalization (HermitianFlagBundle r E h) 2
              (flagChernRoot r E h i)) k := by
  -- Construct the degreewise Newton class on the base before using flag injectivity.
  let c : singularCohomology ℚ X (2 * k) := (Nat.factorial k : ℚ)⁻¹ •
    singularCohomologyNewtonPowerSum ℚ X r
      (fun j ↦ singularCohomologyRationalization X (2 * j) (chernClass r E h j)) k
  have hc : singularCohomologyPullback ℚ (hermitianFlagProjection r E h) (2 * k) c =
      (Nat.factorial k : ℚ)⁻¹ •
        ∑ i : Fin r, singularCohomologyDegreeTwoPow ℚ (HermitianFlagBundle r E h)
          (singularCohomologyRationalization (HermitianFlagBundle r E h) 2
            (flagChernRoot r E h i)) k := by
    -- The same rationalized roots give every coefficient of the pulled-back polynomial.
    dsimp only [c]
    rw [map_smul, singularCohomologyNewtonPowerSum_pullback]
    simp_rw [← singularCohomologyRationalization_naturality, chernClass_flag_pullback,
      singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
    rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
    rfl
  refine ⟨c, hc, ?_⟩
  intro y hy
  exact hermitianFlagProjection_cohomology_injective ℚ r E h (2 * k) (hy.trans hc.symm)

/-- The degree-2k component of the actual rational Chern character. -/
def chernCharacterComponent (k : ℕ) : singularCohomology ℚ X (2 * k) :=
  (existsUnique_chernCharacterComponent r E h k).exists.choose

/-- The chosen character component has exactly the normalized original Chern-root formula. -/
theorem chernCharacterComponent_flag_pullback (k : ℕ) :
    singularCohomologyPullback ℚ (hermitianFlagProjection r E h) (2 * k)
        (chernCharacterComponent r E h k) =
      (Nat.factorial k : ℚ)⁻¹ •
        ∑ i : Fin r, singularCohomologyDegreeTwoPow ℚ (HermitianFlagBundle r E h)
          (singularCohomologyRationalization (HermitianFlagBundle r E h) 2
            (flagChernRoot r E h i)) k := by
  exact (existsUnique_chernCharacterComponent r E h k).exists.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degreewise Chern character is the normalized Newton polynomial in the Chern classes. -/
theorem chernCharacterComponent_eq_newton (k : ℕ) :
    chernCharacterComponent r E h k = (Nat.factorial k : ℚ)⁻¹ •
      singularCohomologyNewtonPowerSum ℚ X r
        (fun j ↦ singularCohomologyRationalization X (2 * j) (chernClass r E h j)) k := by
  -- Identify the explicitly constructed base class by the original unique root formula.
  apply hermitianFlagProjection_cohomology_injective ℚ r E h (2 * k)
  rw [chernCharacterComponent_flag_pullback, map_smul,
    singularCohomologyNewtonPowerSum_pullback]
  simp_rw [← singularCohomologyRationalization_naturality, chernClass_flag_pullback,
    singularCohomologyRationalization_elementarySymmetric, List.map_ofFn]
  rw [singularCohomologyNewtonPowerSum_elementarySymmetric]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-zero Chern character is the constant complex rank times the original unit. -/
theorem chernCharacterComponent_zero :
    chernCharacterComponent r E h 0 = (r : ℚ) • singularCohomologyOne ℚ X := by
  -- The empty power is the unit; the same finite root family has exactly r elements.
  apply hermitianFlagProjection_cohomology_injective ℚ r E h 0
  rw [chernCharacterComponent_flag_pullback r E h 0, map_smul, singularCohomologyPullback_one]
  simp [singularCohomologyDegreeTwoPow, Nat.cast_smul_eq_nsmul]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The degree-two component is the rationalization of the integral first Chern class. -/
theorem chernCharacterComponent_one :
    chernCharacterComponent r E h 1 =
      singularCohomologyRationalization X 2 (chernClass r E h 1) := by
  -- Compare in the original flag space, then use its faithful homogeneous ring inclusion.
  apply hermitianFlagProjection_cohomology_injective ℚ r E h 2
  rw [chernCharacterComponent_flag_pullback r E h 1, ← singularCohomologyRationalization_naturality,
    chernClass_flag_pullback r E h 1,
    singularCohomologyRationalization_elementarySymmetric
      (HermitianFlagBundle r E h) (List.ofFn (flagChernRoot r E h)) 1]
  simp only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul]
  apply singularEvenCohomologyOf_injective ℚ (HermitianFlagBundle r E h) 1
  rw [map_sum, singularEvenCohomologyOf_elementarySymmetric]
  simp_rw [singularEvenCohomologyOf_degreeTwoPow, pow_one]
  rw [List.map_ofFn, ← Fin.univ_val_map, Multiset.map_map]
  simp [Multiset.esymm, Multiset.powersetCard_one, Function.comp_def, List.sum_ofFn]

/-- The actual Chern character does not depend on the auxiliary continuous Hermitian metric. -/
theorem chernCharacterComponent_metric_independent
    (h' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ContinuousHermitianMetric E) (k : ℕ) :
    chernCharacterComponent r E h k = chernCharacterComponent r E h' k := by
  -- Both formulas use the metric-independent classes on the original base.
  rw [chernCharacterComponent_eq_newton, chernCharacterComponent_eq_newton]
  simp_rw [chernClass_metric_independent r E h h']

end AtiyahSinger.ComplexBundle
