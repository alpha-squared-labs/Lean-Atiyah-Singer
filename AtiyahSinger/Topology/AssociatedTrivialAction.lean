/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The original associated quotient for a trivial fiber action

Public module ID: M1554.

When the supplied action fixes every fiber point, the actual associated
quotient is homeomorphic to the product of the original base and fiber.
The map sends the original class of a pair to its base and unchanged fiber
coordinate. Principal transitivity proves injectivity, and openness of the
original projection proves continuity of the inverse.

No global section, trivialization of the principal bundle, separation, or
nonemptiness assumption is needed. This applies in particular to the two
fixed points of the zero-dimensional orthogonal sphere.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set

variable {G P F B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P]
  [TopologicalSpace F] [MulAction G F]
  [TopologicalSpace B] {projection : P → B}

/-- Trivial fiber action gives the product homeomorphism on the original associated quotient. -/
theorem exists_associatedBundle_homeomorph_of_trivial_action
    (hP : IsPrincipalBundle G projection) (hact : ∀ (g : G) (y : F), g • y = y) :
    ∃ e : AssociatedBundle G P F ≃ₜ B × F,
      ∀ (p : P) (y : F), e (associatedBundleMk G P F p y) = (projection p, y) := by
  let f : C(AssociatedBundle G P F, B × F) := {
    toFun := Quotient.lift (fun z : P × F ↦ (projection z.1, z.2)) (by
      rintro x y ⟨g, rfl⟩
      simp only [hP.projection_smul, hact])
    continuous_toFun := continuous_quot_lift _
      (((hP.projection_properties).1.comp continuous_fst).prodMk continuous_snd) }
  have hmk (p : P) (y : F) : f (associatedBundleMk G P F p y) = (projection p, y) := rfl
  -- Principal transitivity identifies exactly the pairs with the same displayed coordinates.
  have hinj : Function.Injective f := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h x =>
      induction w using Quotient.inductionOn with
      | h y =>
        change (projection x.1, x.2) = (projection y.1, y.2) at h
        obtain ⟨g, hg, _⟩ := hP.existsUnique_smul x.1 y.1 (congrArg Prod.fst h)
        apply Quotient.sound
        refine ⟨g, ?_⟩
        exact Prod.ext hg.symm ((congrArg Prod.snd h).symm.trans (hact g⁻¹ x.2).symm)
  have hsurj : Function.Surjective f := by
    rintro ⟨b, y⟩
    obtain ⟨p, hp⟩ := hP.projection_properties.2.2 b
    exact ⟨associatedBundleMk G P F p y, by rw [hmk, hp]⟩
  -- The same projection is open, so the induced continuous bijection is open as well.
  let q : P × F → AssociatedBundle G P F := Quotient.mk (associatedBundleSetoid G P F)
  have hopen : IsOpenMap f := by
    intro U hU
    have heq : f '' U = (fun z : P × F ↦ (projection z.1, z.2)) '' (q ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := Quotient.exists_rep z
        exact ⟨p, hz, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨q p, hp, rfl⟩
    rw [heq]
    exact (hP.projection_properties.2.1.prodMap (Homeomorph.refl F).isOpenMap) _
      (hU.preimage continuous_quotient_mk')
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    f.continuous hopen, hmk⟩

end AtiyahSinger
