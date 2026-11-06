/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineChern
public import AtiyahSinger.Topology.EvenCohomologyPolynomials
public import AtiyahSinger.Topology.HermitianProjectiveBundleCohomology
public import AtiyahSinger.Topology.ProjectiveFlagChern
public import AtiyahSinger.Topology.SplittingPrinciple

/-!
# Integral Chern classes of the original finite-rank complex bundle

Public module ID: M1609.

C02. Each root is the normalized first Chern class of the actual tautological
line in the original Hermitian full flag bundle. The elementary symmetric
classes descend uniquely through the original projection. Existence uses the
actual projective power basis and split relation; injectivity alone proves
only uniqueness.

Sources: Milnor--Stasheff Section 14 and Hatcher, Vector Bundles and K-Theory,
Theorem 3.2 and Proposition 3.3. The chosen continuous Hermitian metric constructs
the flag presentation and is not characteristic-class data. Independence from
that metric is stated explicitly. All classes live in the original integral
singular cohomology; no replacement cohomology theory or free Chern map is input.

This is the continuous fixed-rank presentation. The model is the original
rank-r Euclidean fiber model, including rank zero. Arbitrary topological bases
are allowed once the original bundle and a continuous metric are given.
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

attribute [local instance] hermitianFlagTopology hermitianFlagLineTopology
  hermitianProjectiveTopology

/-- An actual Chern root is the normalized first Chern class of a tautological flag line. -/
def flagChernRoot (i : Fin r) :
    singularCohomology ℤ (HermitianFlagBundle r E h) 2 :=
  letI := isFiniteRank_hermitianFlagLine r E h i
  firstChernClass (HermitianFlagLine r E h i) (fun p ↦ p.2.property.2.1 i)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The elementary symmetric classes of the actual flag lines descend uniquely to the base. -/
theorem existsUnique_chernClass (k : ℕ) :
    ∃! c : singularCohomology ℤ X (2 * k),
      singularCohomologyPullback ℤ (hermitianFlagProjection r E h) (2 * k) c =
        singularCohomologyElementarySymmetric ℤ (HermitianFlagBundle r E h)
          (List.ofFn (flagChernRoot r E h)) k := by
  let Q := HermitianFlagBundle r E h
  let f := hermitianFlagProjection r E h
  let F := (f : Q → X) *ᵖ E
  let hnorm : ∀ x, NormedAddCommGroup (E x) := inferInstance
  let hspace : ∀ x, NormedSpace ℂ (E x) := inferInstance
  let : ∀ p, NormedAddCommGroup (F p) := fun p ↦ hnorm (f p)
  let : ∀ p, NormedSpace ℂ (F p) := fun p ↦ hspace (f p)
  let : FiberBundle (EuclideanSpace ℂ (Fin r)) F :=
    FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  let : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F :=
    VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  -- The actual projective basis defines normalized coefficients on the original base.
  have hb := hermitianProjectivePowerCombination_int_bijective r E h r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hb' := hermitianProjectivePowerCombination_int_bijective r F
    (hermitianProjectivePullbackMetric r E h f) r (fun i ↦ Nat.le_of_lt i.isLt)
  let c := projectiveChernCoefficient (hermitianProjectiveProjection r E h) r
    (hermitianProjectiveChernRoot r E h) hb k
  -- The same actual flag coordinates give the split relation for precisely these coefficients.
  have hc := hermitianProjectiveChernCoefficient_flag_pullback_of_iso r E h E h
    (by let := modelTopology (EuclideanSpace ℂ (Fin r)) E; exact Iso.refl E) hb hb' k
  refine ⟨c, hc, ?_⟩
  intro a ha
  exact hermitianFlagProjection_cohomology_injective ℤ r E h (2 * k) (ha.trans hc.symm)

/-- The integral Chern class determined by the actual normalized roots and original projection. -/
def chernClass (k : ℕ) : singularCohomology ℤ X (2 * k) :=
  (existsUnique_chernClass r E h k).exists.choose

/-- The original flag pullback of a Chern class is the specified elementary symmetric class. -/
theorem chernClass_flag_pullback (k : ℕ) :
    singularCohomologyPullback ℤ (hermitianFlagProjection r E h) (2 * k)
        (chernClass r E h k) =
      singularCohomologyElementarySymmetric ℤ (HermitianFlagBundle r E h)
        (List.ofFn (flagChernRoot r E h)) k := by
  -- The choice specification retains the same flag, metric, normalized roots and projection.
  exact (existsUnique_chernClass r E h k).exists.choose_spec

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original Chern class is the normalized coefficient of its actual projective relation. -/
theorem chernClass_eq_projectiveChernCoefficient
    (hb : Function.Bijective
      (singularCohomologyPowerCombination ℤ (hermitianProjectiveProjection r E h)
        (hermitianProjectiveChernRoot r E h) r r (fun i ↦ Nat.le_of_lt i.isLt))) (k : ℕ) :
    chernClass r E h k = projectiveChernCoefficient (hermitianProjectiveProjection r E h) r
      (hermitianProjectiveChernRoot r E h) hb k := by
  let Q := HermitianFlagBundle r E h
  let f := hermitianFlagProjection r E h
  let F := (f : Q → X) *ᵖ E
  let hnorm : ∀ x, NormedAddCommGroup (E x) := inferInstance
  let hspace : ∀ x, NormedSpace ℂ (E x) := inferInstance
  let : ∀ p, NormedAddCommGroup (F p) := fun p ↦ hnorm (f p)
  let : ∀ p, NormedSpace ℂ (F p) := fun p ↦ hspace (f p)
  let : FiberBundle (EuclideanSpace ℂ (Fin r)) F :=
    FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  let : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F :=
    VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  have hb' := hermitianProjectivePowerCombination_int_bijective r F
    (hermitianProjectivePullbackMetric r E h f) r (fun i ↦ Nat.le_of_lt i.isLt)
  -- Uniqueness on the same original flag identifies the chosen class with this coefficient.
  apply hermitianFlagProjection_cohomology_injective ℤ r E h (2 * k)
  rw [chernClass_flag_pullback]
  exact (hermitianProjectiveChernCoefficient_flag_pullback_of_iso r E h E h
    (by let := modelTopology (EuclideanSpace ℂ (Fin r)) E; exact Iso.refl E) hb hb' k).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The integral classes are independent of the auxiliary continuous Hermitian metric. -/
theorem chernClass_metric_independent
    (h' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ContinuousHermitianMetric E) (k : ℕ) :
    chernClass r E h k = chernClass r E h' k := by
  let Q := HermitianFlagBundle r E h'
  let f := hermitianFlagProjection r E h'
  let F := (f : Q → X) *ᵖ E
  let hnorm : ∀ x, NormedAddCommGroup (E x) := inferInstance
  let hspace : ∀ x, NormedSpace ℂ (E x) := inferInstance
  let : ∀ p, NormedAddCommGroup (F p) := fun p ↦ hnorm (f p)
  let : ∀ p, NormedSpace ℂ (F p) := fun p ↦ hspace (f p)
  let : FiberBundle (EuclideanSpace ℂ (Fin r)) F :=
    FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  let : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) F :=
    VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f
  have hb := hermitianProjectivePowerCombination_int_bijective r E h r
    (fun i ↦ Nat.le_of_lt i.isLt)
  have hb' := hermitianProjectivePowerCombination_int_bijective r F
    (hermitianProjectivePullbackMetric r E h f) r (fun i ↦ Nat.le_of_lt i.isLt)
  let c := projectiveChernCoefficient (hermitianProjectiveProjection r E h) r
    (hermitianProjectiveChernRoot r E h) hb k
  -- The first construction is the coefficient of the actual projective relation.
  have hc : chernClass r E h k = c := chernClass_eq_projectiveChernCoefficient r E h hb k
  -- Compare on one fixed second flag; identity transports its same coordinates without
  -- requiring their orthogonality for the first metric.
  have hflag := hermitianProjectiveChernCoefficient_flag_pullback_of_iso r E h E h'
    (by let := modelTopology (EuclideanSpace ℂ (Fin r)) E; exact Iso.refl E) hb hb' k
  apply hc.trans
  apply (existsUnique_chernClass r E h' k).unique
  · exact hflag
  · exact chernClass_flag_pullback r E h' k

/-- The degree-zero Chern class is the original unit. -/
theorem chernClass_zero : chernClass r E h 0 = singularCohomologyOne ℤ X := by
  apply hermitianFlagProjection_cohomology_injective ℤ r E h 0
  rw [chernClass_flag_pullback r E h 0, singularCohomologyPullback_one]
  cases List.ofFn (flagChernRoot r E h) <;> rfl

/-- Chern classes vanish above the complex rank, including the zero-rank bundle. -/
theorem chernClass_eq_zero_of_rank_lt (k : ℕ) (hk : r < k) :
    chernClass r E h k = 0 := by
  apply hermitianFlagProjection_cohomology_injective ℤ r E h (2 * k)
  rw [chernClass_flag_pullback, map_zero]
  -- The original list has exactly r actual roots, so its k-th symmetric class vanishes.
  apply singularEvenCohomologyOf_injective ℤ (HermitianFlagBundle r E h) k
  rw [map_zero, singularEvenCohomologyOf_elementarySymmetric]
  exact Multiset.esymm_of_card_lt (by simpa using hk)

end AtiyahSinger.ComplexBundle
