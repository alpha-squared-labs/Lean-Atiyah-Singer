/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ChernCharacterOperations
public import AtiyahSinger.Topology.VariableRankChern

/-!
# Global characteristic classes on a fixed-rank pullback model

Public module ID: M1867.

The globally assembled characteristic classes pull back to the existing fixed-rank
classes whenever an actual constant-rank bundle models the pullback. The map factors
through the corresponding actual rank stratum of the specified cohomology model.
The comparison retains the original pullback topology and independently supplied
Hermitian metrics. Empty bases and rank zero require no separate rank inference.

This is the local comparison used for varying-rank naturality and common rank
refinements. It uses only fixed-rank naturality, not the global operation formulas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory

universe u v

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hE : ContinuousHermitianMetric E)
  {Y : Type u} [TopologicalSpace Y] (f : C(Y, X))
  (V : Y → Type u) [∀ y, AddCommGroup (V y)] [∀ y, Module ℂ (V y)]
  [TopologicalSpace (TotalSpace Unit V)] [IsFiniteRank V]
  (hV : ContinuousHermitianMetric V) (r : ℕ)
  (hVrank : ∀ y, Module.finrank ℂ (V y) = r)
  (e : Iso V ((f : Y → X) *ᵖ E))

include e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The global integral class restricts to the original fixed-rank class on any pullback model. -/
theorem globalChernClass_pullback_eq_chernClass (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k) (globalChernClass E hE k) =
      (letI : ∀ y, NormedAddCommGroup (V y) := hV.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (V y) := hV.fiberInnerProductSpace
       letI := nativeModelTopology V (EuclideanSpace ℂ (Fin r))
       letI := hV.nativeFiberBundle r hVrank
       letI := hV.nativeVectorBundle r hVrank
       chernClass r V (hV.nativeModelMetric r) k) := by
  -- The actual fiber isomorphism factors f through one rank locus of the specified model.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  have hr (y : Y) : Module.finrank ℂ (M (f y)) = r :=
    (cohomologyModelLinearEquiv E (f y)).finrank_eq.trans
      ((e.linearEquiv y).finrank_eq.symm.trans (hVrank y))
  let S := rankStratum M r
  let g : C(Y, S) := ⟨fun y ↦ ⟨f y, hr y⟩, f.continuous.subtype_mk _⟩
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let hA := rankHermitianMetric M (cohomologyModelMetric E hE) r
  have eM : Iso V ((f : Y → X) *ᵖ M) :=
    e.trans ((cohomologyModelIso E).symm.pullback f)
  have eA : Iso ((g : Y → S) *ᵖ A) V :=
    (pullbackCompIso (E := M) i g).trans eM.symm
  -- Retype the same two original total spaces for the fixed-rank naturality theorem.
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let : ∀ y, NormedAddCommGroup (V y) := hV.fiberNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (V y) := hV.fiberInnerProductSpace
  let := nativeModelTopology A (EuclideanSpace ℂ (Fin r))
  let := nativeModelTopology V (EuclideanSpace ℂ (Fin r))
  let := hA.nativeFiberBundle r (fun x ↦ x.property)
  let := hA.nativeVectorBundle r (fun x ↦ x.property)
  let := hV.nativeFiberBundle r hVrank
  let := hV.nativeVectorBundle r hVrank
  have eA' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) A
      letI := modelTopology (EuclideanSpace ℂ (Fin r)) V
      Iso ((g : Y → S) *ᵖ A) V := by
    rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology]
    exact eA
  have hspec := (existsUnique_globalChernClass E hE k).exists.choose_spec r
  change singularCohomologyPullback ℤ i (2 * k) (globalChernClass E hE k) =
    chernClass r A (hA.nativeModelMetric r) k at hspec
  -- Assembly on the rank stratum followed by fixed-rank naturality gives the comparison.
  calc
    singularCohomologyPullback ℤ f (2 * k) (globalChernClass E hE k) =
        singularCohomologyPullback ℤ g (2 * k)
          (singularCohomologyPullback ℤ i (2 * k) (globalChernClass E hE k)) := by
      change (singularCohomologyFunctor ℤ (2 * k)).map
        ((TopCat.ofHom i).op ≫ (TopCat.ofHom g).op) _ = _
      rw [Functor.map_comp]
      rfl
    _ = singularCohomologyPullback ℤ g (2 * k)
        (chernClass r A (hA.nativeModelMetric r) k) := congrArg _ hspec
    _ = chernClass r V (hV.nativeModelMetric r) k :=
      chernClass_pullback_eq_of_iso r A (hA.nativeModelMetric r) g V
        (hV.nativeModelMetric r) eA' k

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The global rational component restricts to the fixed-rank component on a pullback model. -/
theorem globalChernCharacterComponent_pullback_eq_chernCharacterComponent (k : ℕ) :
    singularCohomologyPullback ℚ f (2 * k) (globalChernCharacterComponent E hE k) =
      (letI : ∀ y, NormedAddCommGroup (V y) := hV.fiberNormedAddCommGroup
       letI : ∀ y, InnerProductSpace ℂ (V y) := hV.fiberInnerProductSpace
       letI := nativeModelTopology V (EuclideanSpace ℂ (Fin r))
       letI := hV.nativeFiberBundle r hVrank
       letI := hV.nativeVectorBundle r hVrank
       chernCharacterComponent r V (hV.nativeModelMetric r) k) := by
  -- The actual fiber isomorphism factors f through one rank locus of the specified model.
  let M := CohomologyModel E
  let := cohomologyModelTopology E
  let := isFiniteRank_cohomologyModel E
  have hr (y : Y) : Module.finrank ℂ (M (f y)) = r :=
    (cohomologyModelLinearEquiv E (f y)).finrank_eq.trans
      ((e.linearEquiv y).finrank_eq.symm.trans (hVrank y))
  let S := rankStratum M r
  let g : C(Y, S) := ⟨fun y ↦ ⟨f y, hr y⟩, f.continuous.subtype_mk _⟩
  let i : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let A := Restrict M S
  let := isFiniteRank_restrict (E := M) (S : Set X)
  let hA := rankHermitianMetric M (cohomologyModelMetric E hE) r
  have eM : Iso V ((f : Y → X) *ᵖ M) :=
    e.trans ((cohomologyModelIso E).symm.pullback f)
  have eA : Iso ((g : Y → S) *ᵖ A) V :=
    (pullbackCompIso (E := M) i g).trans eM.symm
  -- Retype the same two original total spaces for the fixed-rank naturality theorem.
  let : ∀ x, NormedAddCommGroup (A x) := hA.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (A x) := hA.fiberInnerProductSpace
  let : ∀ y, NormedAddCommGroup (V y) := hV.fiberNormedAddCommGroup
  let : ∀ y, InnerProductSpace ℂ (V y) := hV.fiberInnerProductSpace
  let := nativeModelTopology A (EuclideanSpace ℂ (Fin r))
  let := nativeModelTopology V (EuclideanSpace ℂ (Fin r))
  let := hA.nativeFiberBundle r (fun x ↦ x.property)
  let := hA.nativeVectorBundle r (fun x ↦ x.property)
  let := hV.nativeFiberBundle r hVrank
  let := hV.nativeVectorBundle r hVrank
  have eA' : letI := modelTopology (EuclideanSpace ℂ (Fin r)) A
      letI := modelTopology (EuclideanSpace ℂ (Fin r)) V
      Iso V ((g : Y → S) *ᵖ A) := by
    rw [ContinuousHermitianMetric.modelTopology_nativeModelTopology,
      ContinuousHermitianMetric.modelTopology_nativeModelTopology]
    exact eA.symm
  have hspec := (existsUnique_globalChernCharacterComponent E hE k).exists.choose_spec r
  change singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent E hE k) =
    chernCharacterComponent r A (hA.nativeModelMetric r) k at hspec
  -- Assembly on the rank stratum followed by fixed-rank naturality gives the comparison.
  calc
    singularCohomologyPullback ℚ f (2 * k) (globalChernCharacterComponent E hE k) =
        singularCohomologyPullback ℚ g (2 * k)
          (singularCohomologyPullback ℚ i (2 * k) (globalChernCharacterComponent E hE k)) := by
      change (singularCohomologyFunctor ℚ (2 * k)).map
        ((TopCat.ofHom i).op ≫ (TopCat.ofHom g).op) _ = _
      rw [Functor.map_comp]
      rfl
    _ = singularCohomologyPullback ℚ g (2 * k)
        (chernCharacterComponent r A (hA.nativeModelMetric r) k) := congrArg _ hspec
    _ = chernCharacterComponent r V (hV.nativeModelMetric r) k :=
      (chernCharacterComponent_pullback r A (hA.nativeModelMetric r) g r V
        (hV.nativeModelMetric r) eA' k).symm

end AtiyahSinger.ComplexBundle
