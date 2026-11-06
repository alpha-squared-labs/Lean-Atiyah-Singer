/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyComparison

/-!
# Forgetting the relative compactification condition

Public module ID: M1692.

The original relative compactification comparison and open extension give the
same ordinary class. Consequently extension intertwines multiplication by an
actual ambient ordinary class with the original supported action on its
restriction. No injectivity of either forgetful map is claimed here.

Source: naturality of singular cohomology of pairs, relative cup and excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  (f : C(X, Y)) (hf : IsOpenEmbedding f)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original relative compactification lift and open extension have the same ordinary image. -/
theorem compactSupportCohomologyToCompactification_toOrdinary (n : ℕ)
    (a : compactSupportCohomology R X n) :
    relativeSingularCohomologyToOrdinary R ((Set.range f)ᶜ) n
        (compactSupportCohomologyToCompactification R f hf n a) =
      compactSupportCohomologyToOrdinary R Y n
        (compactSupportCohomologyOpenExtension R f hf n a) := by
  obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  let L := openEmbeddingCompactImage f K
  let A : Set Y := (Set.range f)ᶜ
  let B : Set Y := (L : Set Y)ᶜ
  have hAB : A ⊆ B := by
    rintro y hy ⟨x, _, rfl⟩
    exact hy ⟨x, rfl⟩
  let P := openEmbeddingCohomologySupportPullback R f hf K n
  let : IsIso P := isIso_openEmbeddingCohomologySupportPullback R f hf K n
  let β := (asIso P).inv α
  have hforget : compactSupportCohomologyToOrdinary R Y n
      (compactSupportCohomologyClass R Y L n β) =
      relativeSingularCohomologyToOrdinary R B n β := by
    have h : compactSupportCohomologyClass R Y L n ≫
        compactSupportCohomologyToOrdinary R Y n =
      relativeSingularCohomologyToOrdinary R B n := colimit.ι_desc _ L
    exact congrArg (fun t ↦ t β) h
  have hid : singularCohomologyPullback R (ContinuousMap.id Y) n = 𝟙 _ := by
    change (singularCohomologyFunctor R n).map (𝟙 _) = _
    exact CategoryTheory.Functor.map_id _ _
  have hsquare := relativeSingularCohomologyPullback_toOrdinary R (ContinuousMap.id Y)
    (show Set.MapsTo (ContinuousMap.id Y) A B from fun _ hz ↦ hAB hz) n
  rw [hid, Category.comp_id] at hsquare
  -- Restricting the relative condition to the boundary preserves the same underlying class.
  rw [compactSupportCohomologyToCompactification_representative,
    compactSupportCohomologyOpenExtension_representative]
  change relativeSingularCohomologyToOrdinary R A n
    (relativeSingularCohomologyRestriction R A B hAB n β) =
      compactSupportCohomologyToOrdinary R Y n (compactSupportCohomologyClass R Y L n β)
  rw [hforget]
  exact congrArg (fun t ↦ t β) hsquare

/-- Open extension respects the action of any class that extends to the actual ambient space. -/
theorem compactSupportCohomologyOpenExtension_toOrdinary_action (p q : ℕ)
    (a : singularCohomology R Y p) (b : compactSupportCohomology R X q) :
    compactSupportCohomologyToOrdinary R Y (p + q)
        (compactSupportCohomologyOpenExtension R f hf (p + q)
          (compactSupportCohomologyAction R X p q
            (singularCohomologyPullback R f p a) b)) =
      singularCohomologyCup R Y p q a
        (compactSupportCohomologyToOrdinary R Y q
          (compactSupportCohomologyOpenExtension R f hf q b)) := by
  -- Compare in the relative compactification first, then forget that same condition.
  rw [← compactSupportCohomologyToCompactification_toOrdinary,
    compactSupportCohomologyToCompactification_action,
    relativeSingularCohomologyToOrdinary_action,
    compactSupportCohomologyToCompactification_toOrdinary]

end AtiyahSinger
