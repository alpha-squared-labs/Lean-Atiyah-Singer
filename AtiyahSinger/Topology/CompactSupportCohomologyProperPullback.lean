/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyAction
public import AtiyahSinger.Topology.CompactSupportKZero
public import AtiyahSinger.Topology.OnePointCohomology

/-!
# Proper pullback of compactly supported singular cohomology

Public module ID: M1665.

Pull back each original relative representative to the inverse image of its
compact support and descend through the same support colimit. This actual map
commutes with ordinary cohomology action and the original one-point comparison.
Properness is required for compact inverse images; no pullback along an arbitrary
bundle projection is asserted. No one-point comparison is assumed invertible.

Source: Hatcher, section 3.3, the compact-support colimit and relative naturality.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits TopologicalSpace OnePoint

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) (hf : IsProperMap f)

/-- Properness equips the literal inverse image of a compact support with its certificate. -/
@[reducible]
def properCompactPreimage (K : Compacts Y) : Compacts X where
  carrier := f ⁻¹' (K : Set Y)
  isCompact' := hf.isCompact_preimage K.isCompact

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Proper pullback on the original compact-support cohomology colimit. -/
def compactSupportCohomologyProperPullback (n : ℕ) :
    compactSupportCohomology R Y n ⟶ compactSupportCohomology R X n :=
  colimit.desc (compactSupportCohomologyFunctor R Y n)
    { pt := compactSupportCohomology R X n
      ι :=
        { app := fun K ↦ relativeSingularCohomologyPullback R f
            (show Set.MapsTo f ((properCompactPreimage f hf K : Set X)ᶜ)
              ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n ≫
              compactSupportCohomologyClass R X (properCompactPreimage f hf K) n
          naturality := by
            intro K L a
            let h : K ≤ L := leOfHom a
            let h' : properCompactPreimage f hf K ≤ properCompactPreimage f hf L :=
              fun _ hx ↦ h hx
            -- The same relative maps commute before passing to the compact-support colimit.
            have hsquare := relativeSingularCohomologyPullback_restriction R f
              (Set.compl_subset_compl.mpr h') (Set.compl_subset_compl.mpr h)
              (show Set.MapsTo f ((properCompactPreimage f hf L : Set X)ᶜ)
                ((L : Set Y)ᶜ) from fun _ hx ↦ hx)
              (show Set.MapsTo f ((properCompactPreimage f hf K : Set X)ᶜ)
                ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n
            simp only [Functor.const_obj_map]
            rw [← Category.assoc]
            change (_ ≫ relativeSingularCohomologyPullback R f _ n) ≫ _ = _
            erw [hsquare, Category.assoc]
            change _ ≫ ((compactSupportCohomologyFunctor R X n).map (homOfLE h') ≫
              colimit.ι (compactSupportCohomologyFunctor R X n) _) = _
            rw [colimit.w]
            exact (Category.comp_id _).symm } }

/-- Proper pullback keeps the specified relative representative on its literal inverse support. -/
theorem compactSupportCohomologyProperPullback_representative
    (K : Compacts Y) (n : ℕ) (a : relativeSingularCohomology R ((K : Set Y)ᶜ) n) :
    compactSupportCohomologyProperPullback R f hf n
        (compactSupportCohomologyClass R Y K n a) =
      compactSupportCohomologyClass R X (properCompactPreimage f hf K) n
        (relativeSingularCohomologyPullback R f
          (show Set.MapsTo f ((properCompactPreimage f hf K : Set X)ᶜ)
            ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n a) := by
  -- Evaluate the defining cocone at this original representative.
  have h : compactSupportCohomologyClass R Y K n ≫
      compactSupportCohomologyProperPullback R f hf n =
      relativeSingularCohomologyPullback R f
        (show Set.MapsTo f ((properCompactPreimage f hf K : Set X)ᶜ)
          ((K : Set Y)ᶜ) from fun _ hx ↦ hx) n ≫
        compactSupportCohomologyClass R X (properCompactPreimage f hf K) n :=
    colimit.ι_desc _ K
  exact congrArg (fun g ↦ g a) h

/-- Proper pullback preserves the ordinary-first action on the same compact supports. -/
theorem compactSupportCohomologyProperPullback_action (p q : ℕ)
    (a : singularCohomology R Y p) (b : compactSupportCohomology R Y q) :
    compactSupportCohomologyProperPullback R f hf (p + q)
        (compactSupportCohomologyAction R Y p q a b) =
      compactSupportCohomologyAction R X p q (singularCohomologyPullback R f p a)
        (compactSupportCohomologyProperPullback R f hf q b) := by
  -- Relative product naturality uses exactly the same preimage support as proper pullback.
  obtain ⟨K, c, rfl⟩ := compactSupportCohomology_exists_representative R Y q b
  rw [compactSupportCohomologyAction_representative,
    compactSupportCohomologyProperPullback_representative,
    compactSupportCohomologyProperPullback_representative,
    relativeSingularCohomologyPullback_action, compactSupportCohomologyAction_representative]

/-- The original one-point comparison commutes with the same extended proper map. -/
theorem compactSupportCohomologyProperPullback_toOnePoint
    [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]
    (n : ℕ) (a : compactSupportCohomology R Y n) :
    compactSupportCohomologyToOnePoint R X n
        (compactSupportCohomologyProperPullback R f hf n a) =
      relativeSingularCohomologyPullback R (properOnePointMap f hf)
        (show Set.MapsTo (properOnePointMap f hf) ({∞} : Set (OnePoint X))
          ({∞} : Set (OnePoint Y)) from fun x hx ↦ by
            have hx' : x = ∞ := hx
            subst x
            rfl) n
        (compactSupportCohomologyToOnePoint R Y n a) := by
  /- Stage 1: represent a on a compact K. The original finite-point
  inclusions commute with f and its actual OnePoint.map extension.
  Naturality of relative pullback gives the square for the two excision maps.
  Stage 2: invert these specified excision maps, then restrict both pairs
  to their original singleton infinity. This is the claimed equality on
  the representative; the colimit representative property finishes.
  No injectivity or surjectivity of the one-point comparison is assumed. -/
  obtain ⟨K, b, rfl⟩ := compactSupportCohomology_exists_representative R Y n a
  let L := properCompactPreimage f hf K
  let fX : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let fY : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let e₀ : C(X, Y) := f
  let e₁ : C(OnePoint X, OnePoint Y) := (properOnePointMap f hf)
  let AX : Set (OnePoint X) := (fX '' (L : Set X))ᶜ
  let AY : Set (OnePoint Y) := (fY '' (K : Set Y))ᶜ
  let hp : Set.MapsTo e₀ ((L : Set X)ᶜ) ((K : Set Y)ᶜ) := fun _ h ↦ h
  have hq : Set.MapsTo e₁ AX AY := by
    intro z hz
    induction z using OnePoint.rec with
    | infty => exact OnePoint.infty_notMem_image_coe
    | coe x =>
      rintro ⟨y, hy, heq⟩
      have hxy : y = f x := OnePoint.coe_injective heq
      apply hz
      exact ⟨x, show f x ∈ (K : Set Y) from hxy ▸ hy, rfl⟩
  have hInfinity : Set.MapsTo e₁ ({∞} : Set (OnePoint X)) ({∞} : Set (OnePoint Y)) := by
    rintro z rfl
    rfl
  have hAX : ({∞} : Set (OnePoint X)) ⊆ AX := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  have hAY : ({∞} : Set (OnePoint Y)) ⊆ AY := by
    rintro z rfl
    exact OnePoint.infty_notMem_image_coe
  let p := relativeSingularCohomologyPullback R e₀ hp n
  let q := relativeSingularCohomologyPullback R e₁ hq n
  let qInfinity := relativeSingularCohomologyPullback R e₁ hInfinity n
  let pX := onePointCohomologySupportPullback R X L n
  let pY := onePointCohomologySupportPullback R Y K n
  let rX := relativeSingularCohomologyRestriction R {∞} AX hAX n
  let rY := relativeSingularCohomologyRestriction R {∞} AY hAY n
  have hX : IsIso pX := isIso_onePointCohomologySupportPullback R X L n
  have hY : IsIso pY := isIso_onePointCohomologySupportPullback R Y K n
  -- Finite-point inclusions commute with the same extended proper map before inversion.
  have hsquare : pY ≫ p = q ≫ pX := by
    dsimp only [pY, pX, onePointCohomologySupportPullback, p, q]
    erw [← relativeSingularCohomologyPullback_comp,
      ← relativeSingularCohomologyPullback_comp]
    rfl
  have hinfinity : rY ≫ qInfinity = q ≫ rX :=
    relativeSingularCohomologyPullback_restriction R e₁ hAX hAY hInfinity hq n
  have hmap : p ≫ onePointCohomologySupportMap R X L n =
      onePointCohomologySupportMap R Y K n ≫ qInfinity := by
    change p ≫ ((asIso pX).inv ≫ rX) = ((asIso pY).inv ≫ rY) ≫ qInfinity
    apply (cancel_epi pY).mp
    erw [← Category.assoc pY p, hsquare, Category.assoc q pX,
      (asIso pX).hom_inv_id_assoc, Category.assoc (asIso pY).inv,
      (asIso pY).hom_inv_id_assoc]
    exact hinfinity.symm
  -- Evaluate that square on the original support representative in the colimit.
  rw [compactSupportCohomologyProperPullback_representative]
  simp only [compactSupportCohomologyToOnePoint_representative]
  exact congrArg (fun t ↦ t b) hmap


end AtiyahSinger
