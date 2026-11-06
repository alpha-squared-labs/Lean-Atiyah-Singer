/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback

/-!
# Functoriality of proper compact-support cohomology pullback

Public module ID: M1664.

The actual pullbacks on support representatives reverse composition and preserve
identity maps. These equalities are used when transporting Thom classes through
the native total-space homeomorphisms and in the support-character action square.

Source: functoriality of singular cohomology of pairs and its compact-support colimit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Opposite

universe u

variable (R : Type) [CommRing R] {X Y Z : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Proper pullback reverses the composition of the actual continuous maps. -/
theorem compactSupportCohomologyProperPullback_comp (f : C(X, Y)) (g : C(Y, Z))
    (hf : IsProperMap f) (hg : IsProperMap g) (n : ℕ)
    (a : compactSupportCohomology R Z n) :
    compactSupportCohomologyProperPullback R (g.comp f) (hg.comp hf) n a =
      compactSupportCohomologyProperPullback R f hf n
        (compactSupportCohomologyProperPullback R g hg n a) := by
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R Z n a
  -- Both constructions use the literal iterated inverse image of the same support K.
  rw [compactSupportCohomologyProperPullback_representative,
    compactSupportCohomologyProperPullback_representative,
    compactSupportCohomologyProperPullback_representative]
  have hsquare := relativeSingularCohomologyPullback_comp R f g
    (show Set.MapsTo f
      (properCompactPreimage f hf (properCompactPreimage g hg K) : Set X)ᶜ
      (properCompactPreimage g hg K : Set Y)ᶜ from fun _ hx ↦ hx)
    (show Set.MapsTo g (properCompactPreimage g hg K : Set Y)ᶜ (K : Set Z)ᶜ
      from fun _ hx ↦ hx) n
  exact congrArg (fun z ↦ compactSupportCohomologyClass R X
    (properCompactPreimage (g.comp f) (hg.comp hf) K) n z)
      (congrArg (fun t ↦ t b) hsquare)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pullback along the actual identity fixes every compact-support cohomology class. -/
theorem compactSupportCohomologyProperPullback_id (n : ℕ)
    (a : compactSupportCohomology R X n) :
    compactSupportCohomologyProperPullback R (ContinuousMap.id X) isProperMap_id n a = a := by
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R X n a
  rw [compactSupportCohomologyProperPullback_representative]
  -- The identity pair map induces the identity on the original relative chain quotient.
  have hchains : relativeSingularChainsMap R (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) (K : Set X)ᶜ (K : Set X)ᶜ from
        fun _ hx ↦ hx) = 𝟙 _ := by
    apply (cancel_epi (relativeSingularChainsProjection R (K : Set X)ᶜ)).mp
    simp [relativeSingularChainsMap, relativeSingularChainsProjection, cokernel.map]
  have hpull : relativeSingularCohomologyPullback R (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) (K : Set X)ᶜ (K : Set X)ᶜ from
        fun _ hx ↦ hx) n = 𝟙 _ := by
    let H := singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
    change H.map (relativeSingularChainsMap R (ContinuousMap.id X) _).op = 𝟙 _
    rw [hchains, op_id, H.map_id]
  exact congrArg (fun z ↦ compactSupportCohomologyClass R X K n z)
    (congrArg (fun t ↦ t b) hpull)

/-- Proper pullback along a homeomorphism is the existing literal homeomorphism pullback. -/
theorem compactSupportCohomologyProperPullback_homeomorph (e : X ≃ₜ Y) (n : ℕ)
    (a : compactSupportCohomology R Y n) :
    compactSupportCohomologyProperPullback R (⟨e, e.continuous⟩ : C(X, Y))
        e.isProperMap n a = compactSupportCohomologyHomeomorphPullback R e n a := by
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R Y n a
  rw [compactSupportCohomologyProperPullback_representative,
    compactSupportCohomologyHomeomorphPullback_representative]
  -- Only the proof of compactness differs; the support and the pair map are identical.
  rfl

end AtiyahSinger
