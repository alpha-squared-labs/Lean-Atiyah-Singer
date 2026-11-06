/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CoefficientChangeIdentity
public import AtiyahSinger.Topology.HermitianProjectiveCohomology
public import AtiyahSinger.Topology.HermitianProjectiveLerayHirsch
public import AtiyahSinger.Topology.LerayHirschPullbackInjectivity
public import AtiyahSinger.Topology.SingularCohomologyPowerComparison

/-!
# Cohomology of the original Hermitian projective bundle

Public module ID: M1891.

The actual projective-product calculation and the original orthonormal charts
give the projective bundle theorem over an arbitrary topological base. The
specified tautological Chern powers form the cohomology basis. Their degree-zero
unit makes the projection pullback injective when the original rank is positive.
The rank-zero power comparison is retained, with an empty basis family and empty total space.

The integral specialization uses the same normalized integral class, since
the original integer coefficient-change map is the identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory HomologicalComplex
open HermitianProjectiveSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original tautological powers give the actual Leray--Hirsch isomorphism in every degree. -/
theorem homologyMap_hermitianProjectiveLerayHirsch_bijective
    (c : ∀ i : ULift.{u} (Fin r),
      singularCocycles R (HermitianProjectiveBundle r E h) (2 * i.down.val))
    (hc : ∀ i : ULift.{u} (Fin r), singularCocycleClass R (HermitianProjectiveBundle r E h)
        (2 * i.down.val) (c i) =
      singularCohomologyDegreeTwoPow R (HermitianProjectiveBundle r E h)
        (singularCohomologyChangeCoefficients R (HermitianProjectiveBundle r E h) 2
          (hermitianProjectiveChernRoot r E h)) i.down.val) (n : ℕ) :
    Function.Bijective (homologyMap
      (singularCohomologyLerayHirschMap R (hermitianProjectiveProjection r E h)
        (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val) c) n) := by
  apply homologyMap_hermitianProjectiveLerayHirsch_bijective_of_model R r E h _ c hc n
  dsimp only
  intro Z tZ c₀ hc₀ k
  -- The lifted Euclidean model has its original norm and exactly the original complex rank.
  let W := ULift.{u} (EuclideanSpace ℂ (Fin r))
  have hdim : Module.finrank ℂ W = r := by
    simp [W, finrank_ulift]
  exact homologyMap_hermitianProjectiveProdLerayHirsch_bijective R Z W r hdim c₀ hc₀ k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In each supported even degree the actual power comparison is bijective. -/
theorem hermitianProjectivePowerCombination_bijective (n : ℕ)
    (hn : ∀ i : Fin r, i.val ≤ n) :
    Function.Bijective (singularCohomologyPowerCombination R
      (hermitianProjectiveProjection r E h)
      (singularCohomologyChangeCoefficients R (HermitianProjectiveBundle r E h) 2
        (hermitianProjectiveChernRoot r E h)) r n hn) := by
  classical
  let Q := HermitianProjectiveBundle r E h
  let t : singularCohomology R Q 2 :=
    singularCohomologyChangeCoefficients R Q 2 (hermitianProjectiveChernRoot r E h)
  -- Choose cocycles representing these same prescribed powers, then use the actual comparison.
  have hrep (k : ℕ) (a : singularCohomology R Q k) :
      ∃ c : singularCocycles R Q k, singularCocycleClass R Q k c = a := by
    let C := singularCochains R Q
    obtain ⟨c, hc⟩ := (C.sc k).moduleCatToCycles.range.mkQ_surjective
      ((C.sc k).moduleCatHomologyIso.hom a)
    refine ⟨c, ?_⟩
    change (C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ c) = a
    rw [hc, Iso.hom_inv_id_apply]
  choose c hc using fun i : ULift.{u} (Fin r) ↦
    hrep (2 * i.down.val) (singularCohomologyDegreeTwoPow R Q t i.down.val)
  exact singularCohomologyPowerCombination_bijective_of_lerayHirsch R
    (hermitianProjectiveProjection r E h) t r n hn c hc
    (homologyMap_hermitianProjectiveLerayHirsch_bijective R r E h c hc (2 * n))

/-- The integral projective basis uses the original normalized integral tautological root. -/
theorem hermitianProjectivePowerCombination_int_bijective (n : ℕ)
    (hn : ∀ i : Fin r, i.val ≤ n) :
    Function.Bijective (singularCohomologyPowerCombination ℤ
      (hermitianProjectiveProjection r E h) (hermitianProjectiveChernRoot r E h) r n hn) := by
  have hb := hermitianProjectivePowerCombination_bijective ℤ r E h n hn
  rw [singularCohomologyChangeCoefficients_int_self] at hb
  exact hb

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A positive-rank original projective projection is injective on cohomology in every degree. -/
theorem hermitianProjectiveProjection_cohomology_injective (hr : 0 < r) (n : ℕ) :
    Function.Injective (singularCohomologyPullback R (hermitianProjectiveProjection r E h) n) := by
  classical
  let Q := HermitianProjectiveBundle r E h
  let t : singularCohomology R Q 2 :=
    singularCohomologyChangeCoefficients R Q 2 (hermitianProjectiveChernRoot r E h)
  have hrep (k : ℕ) (a : singularCohomology R Q k) :
      ∃ c : singularCocycles R Q k, singularCocycleClass R Q k c = a := by
    let C := singularCochains R Q
    obtain ⟨c, hc⟩ := (C.sc k).moduleCatToCycles.range.mkQ_surjective
      ((C.sc k).moduleCatHomologyIso.hom a)
    refine ⟨c, ?_⟩
    change (C.sc k).moduleCatHomologyIso.inv ((C.sc k).moduleCatToCycles.range.mkQ c) = a
    rw [hc, Iso.hom_inv_id_apply]
  choose c hc using fun i : ULift.{u} (Fin r) ↦
    hrep (2 * i.down.val) (singularCohomologyDegreeTwoPow R Q t i.down.val)
  -- Positive rank supplies the actual zero index, whose prescribed power is exactly one.
  let i₀ : ULift.{u} (Fin r) := ⟨⟨0, hr⟩⟩
  have hunit : singularCocycleClass R Q 0 (c i₀) = singularCohomologyOne R Q := hc i₀
  exact singularCohomologyPullback_injective_of_lerayHirsch R
    (hermitianProjectiveProjection r E h) (fun i : ULift.{u} (Fin r) ↦ 2 * i.down.val)
    c i₀ rfl hunit n
    (homologyMap_hermitianProjectiveLerayHirsch_bijective R r E h c hc n).injective

end AtiyahSinger.ComplexBundle
