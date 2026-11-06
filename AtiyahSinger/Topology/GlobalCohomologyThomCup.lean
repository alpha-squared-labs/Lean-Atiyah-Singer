/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyThom

/-!
# The complete right-cup cochain comparison for a Thom generator

Public module ID: M1868.

Right cup with an actual global relative cocycle whose fiber restrictions are
generators is a quasi-isomorphism from the ordinary cochains extended by the
bundle rank. Local trivializations and the original small-cochain descent
also give vanishing below the rank, so the full target and its incoming
boundaries are retained.

Source: the relative Leray--Hirsch and Thom arguments in Hatcher, Algebraic
Topology, Corollary 4D.9. This formulation keeps the specified global cocycle
and works for arbitrary commutative coefficients and arbitrary base spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits HomologicalComplex

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified fiberwise Thom cocycle makes the full original right-cup map a quasi-isomorphism. -/
theorem relativeSingularCochainCupMap_bijective_of_bundle_generator
    (c : relativeSingularCocycles R (bundleNonzero r E) r)
    (hgen : ∀ x : X, Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
        (A := {v : E x | v ≠ 0}) (B := bundleNonzero r E) (fun _ hv ↦ hv) r
        (relativeSingularCocycleClass R (bundleNonzero r E) r c)))
    (n : ℕ) : Function.Bijective
      (homologyMap (relativeSingularCochainCupMap R (bundleNonzero r E) r c) n) := by
  classical
  let V (x : X) := (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).baseSet
  let U (x : X) := (bundleProjection r E) ⁻¹' V x
  let S (m : ℕ) (a : Fin (m + 1) → X) : Set X := {x | ∀ i, x ∈ V (a i)}
  let A := bundleNonzero r E
  let t := relativeSingularCocycleClass R A r c
  have hOpen (x : X) : IsOpen (U x) :=
    (trivializationAt (EuclideanSpace ℝ (Fin r)) E x).open_baseSet.preimage
      (bundleProjection r E).continuous
  have hCover : ⋃ x, U x = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    exact Set.mem_iUnion.mpr ⟨z.proj,
      FiberBundle.mem_baseSet_trivializationAt' (F := EuclideanSpace ℝ (Fin r)) z.proj⟩
  -- Each tuple has a first chart, so its intersection lies in that chart.
  have hvan (m : ℕ) (a : Fin (m + 1) → X) (q : ℕ) (hq : q < r) :
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U a → _) ⁻¹' A) q) := by
    change Subsingleton (relativeSingularCohomology R (bundleNonzeroOver r E (S m a)) q)
    exact subsingleton_relativeSingularCohomology_bundleTotalOver_below_rank R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S m a) (fun _ hy ↦ hy 0) q hq
  have hlocal (m : ℕ) (a : Fin (m + 1) → X) (q : ℕ) :
      Function.Bijective (fun z : singularCohomology R (singularCechIntersection U a) q ↦
        relativeSingularCohomologyAction R
          ((Subtype.val : singularCechIntersection U a → _) ⁻¹' A) q r z
          (relativeSingularCohomologyPullback R
            (ContinuousMap.subtypeVal (singularCechIntersection U a))
            (fun _ hx ↦ hx) r t)) := by
    let inc : C(BundleTotalOver r E (S m a), TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    change Function.Bijective (fun z : singularCohomology R (BundleTotalOver r E (S m a)) q ↦
      relativeSingularCohomologyAction R (bundleNonzeroOver r E (S m a)) q r z
        (relativeSingularCohomologyPullback R inc
          (A := bundleNonzeroOver r E (S m a)) (B := A) (fun _ hv ↦ hv) r t))
    apply relativeSingularCohomologyAction_bundleTotalOver_bijective R r E
      (trivializationAt (EuclideanSpace ℝ (Fin r)) E (a 0))
      (S m a) (fun _ hy ↦ hy 0)
    intro x hx
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact hgen x
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  by_cases hn : r ≤ n
  · -- At or above the rank, descent identifies the actual cohomological right-cup formula.
    obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    have hcup := relativeSingularCohomologyAction_bijective_of_openCover R
      U A hOpen hCover r c hvan hlocal p
    let J := (singularCochains R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)).extendHomologyIso
      e (j := p) rfl
    apply (Function.Bijective.of_comp_iff _ (ConcreteCategory.bijective_of_isIso J.inv)).mp
    have hformula : homologyMap (relativeSingularCochainCupMap R A r c) (p + r) ∘ J.inv =
        (fun a ↦ relativeSingularCohomologyAction R A p r a t) :=
      funext fun a ↦ homologyMap_relativeSingularCochainCupMap R A r c p a
    rw [hformula]
    exact hcup
  · -- Below the rank, unique Cech gluing and local vanishing make the full target zero.
    have hnr : n < r := Nat.lt_of_not_ge hn
    let F (a : Fin 1 → X) := relativeSingularCochains R
      ((Subtype.val : singularCechIntersection U a → _) ⁻¹' A)
    have (a : Fin 1 → X) : Subsingleton ((F a).homology n) := hvan 0 a n hnr
    have hlocalZero : Subsingleton ((singularCechCochains R U A 1).homology n) :=
      (bijective_homologyMap_cochainFamilyProductProjection R F n).injective.subsingleton
    obtain ⟨z, _hz, huniq⟩ := existsUnique_relativeSingularCohomology_of_cech R U A hOpen hCover n
      (fun m a q hq ↦ hvan (m + 1) a q (hq.trans hnr)) 0 (map_zero _)
    have htarget : Subsingleton (relativeSingularCohomology R A n) :=
      ⟨fun a b ↦ (huniq a (hlocalZero.elim _ _)).trans (huniq b (hlocalZero.elim _ _)).symm⟩
    have hsource : Subsingleton
        (((singularCochains R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)).extend e).homology n) := by
      apply ModuleCat.isZero_iff_subsingleton.mp
      apply (exactAt_iff_isZero_homology _ _).mp
      exact extend_exactAt _ e n (by
        intro p hp
        change p + r = n at hp
        omega)
    exact ⟨fun _ _ _ ↦ hsource.elim _ _, fun a ↦ ⟨0, htarget.elim _ a⟩⟩

end AtiyahSinger
