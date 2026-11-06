/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundle
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Product coordinates from a principal gauge

Public module ID: M1536.

A continuous right-equivariant principal coordinate identifies the original
associated quotient with the product. The fiber coordinate is transformed by
that same gauge. Over a discrete base the principal charts supply such a global gauge.
The supplied gauge acts on the fiber and need not trivialize its group action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G P B Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace P] [TopologicalSpace B] [MulAction Gᵐᵒᵖ P]
  [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]

/-- An actual principal gauge gives the product map on every original associated representative. -/
theorem exists_associatedBundle_productHomeomorph_of_gauge
    (hP : IsPrincipalBundle G projection) (θ : C(P, G))
    (hθ : ∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g) :
    ∃ e : AssociatedBundle G P Y ≃ₜ B × Y,
      ∀ (p : P) (y : Y), e (associatedBundleMk G P Y p y) = (projection p, θ p • y) := by
  let f : C(AssociatedBundle G P Y, B × Y) := {
    toFun := Quotient.lift (fun z : P × Y ↦ (projection z.1, θ z.1 • z.2)) (by
      rintro x y ⟨g, rfl⟩
      simp only [hP.projection_smul, hθ, mul_smul, smul_inv_smul])
    continuous_toFun := continuous_quot_lift _
      ((hP.projection_properties.1.comp continuous_fst).prodMk
        ((θ.continuous.comp continuous_fst).smul continuous_snd)) }
  have hmk (p : P) (y : Y) : f (associatedBundleMk G P Y p y) =
      (projection p, θ p • y) := rfl
  -- Principal transitivity identifies the unique simultaneous change of both coordinates.
  have hinj : Function.Injective f := by
    intro z w h
    induction z using Quotient.inductionOn with
    | h x =>
      induction w using Quotient.inductionOn with
      | h y =>
        change (projection x.1, θ x.1 • x.2) = (projection y.1, θ y.1 • y.2) at h
        obtain ⟨g, hg, _⟩ := hP.existsUnique_smul x.1 y.1 (congrArg Prod.fst h)
        have hcoord : θ x.1 • x.2 = θ x.1 • (g • y.2) := by
          simpa only [← hg, hθ, mul_smul] using congrArg Prod.snd h
        have hxy : x.2 = g • y.2 := by
          simpa only [inv_smul_smul] using congrArg (fun v : Y ↦ (θ x.1)⁻¹ • v) hcoord
        apply Quotient.sound
        refine ⟨g, Prod.ext hg.symm ?_⟩
        rw [hxy, inv_smul_smul]
  have hsurj : Function.Surjective f := by
    rintro ⟨b, y⟩
    obtain ⟨p, hp⟩ := hP.projection_properties.2.2 b
    refine ⟨associatedBundleMk G P Y p ((θ p)⁻¹ • y), ?_⟩
    rw [hmk, hp, smul_inv_smul]
  -- The gauge shear is a genuine homeomorphism before the original open projection is taken.
  let shear : P × Y ≃ₜ P × Y := {
    toFun := fun z ↦ (z.1, θ z.1 • z.2)
    invFun := fun z ↦ (z.1, (θ z.1)⁻¹ • z.2)
    left_inv := fun z ↦ by simp only [inv_smul_smul]
    right_inv := fun z ↦ by simp only [smul_inv_smul]
    continuous_toFun := continuous_fst.prodMk ((θ.continuous.comp continuous_fst).smul
      continuous_snd)
    continuous_invFun := continuous_fst.prodMk ((θ.continuous.comp continuous_fst).inv.smul
      continuous_snd) }
  let q : P × Y → AssociatedBundle G P Y := Quotient.mk (associatedBundleSetoid G P Y)
  have hcomp : IsOpenMap (fun z : P × Y ↦ f (q z)) :=
    (hP.projection_properties.2.1.prodMap (Homeomorph.refl Y).isOpenMap).comp shear.isOpenMap
  have hopen : IsOpenMap f := by
    intro U hU
    have himage : f '' U = (fun z : P × Y ↦ f (q z)) '' (q ⁻¹' U) := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := Quotient.exists_rep z
        exact ⟨p, hz, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨q p, hp, rfl⟩
    rw [himage]
    exact hcomp _ (hU.preimage continuous_quotient_mk')
  exact ⟨(Equiv.ofBijective f ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen
    f.continuous hopen, hmk⟩

end AtiyahSinger
