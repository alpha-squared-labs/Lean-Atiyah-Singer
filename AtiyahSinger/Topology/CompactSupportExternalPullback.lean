/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyProperPullback
public import AtiyahSinger.Topology.CompactSupportExternalRepresentative

/-!
# Proper pullback of a supported external representative

Public module ID: M1672.

The two factors are pulled back only as relative pairs along the actual
components of a specified proper map. Their common supported product is
then placed on the given compact inverse image. Properness is used for
this full map, never for its individual projections.

Source: relative cup naturality and the compact-support cohomology colimit.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace

universe u

set_option maxHeartbeats 600000 in
-- The three pair maps retain the same compact inverse-image equality.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A proper map pulls the external representative back to its specified compact inverse support. -/
theorem compactSupportCohomologyProperPullback_externalRepresentative
    (R : Type) [CommRing R] {X Y Z : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X] [T2Space Y]
    (f : C(Z, X × Y)) (hf : IsProperMap f) (K : Compacts X) (L : Compacts Y)
    (W : Compacts Z) (hW : (W : Set Z) = f ⁻¹' ((K : Set X) ×ˢ (L : Set Y)))
    (p q : ℕ) (a : relativeSingularCohomology R (K : Set X)ᶜ p)
    (b : relativeSingularCohomology R (L : Set Y)ᶜ q) :
    let q₁ := (ContinuousMap.fst : C(X × Y, X)).comp f
    let q₂ := (ContinuousMap.snd : C(X × Y, Y)).comp f
    let A : Set Z := q₁ ⁻¹' (K : Set X)ᶜ
    let B : Set Z := q₂ ⁻¹' (L : Set Y)ᶜ
    compactSupportCohomologyProperPullback R f hf (p + q)
      (compactSupportCohomologyExternalRepresentative R K L p q a b) =
    compactSupportCohomologyClass R Z W (p + q)
      (relativeSingularCohomologyPullback R (ContinuousMap.id Z)
        (A := (W : Set Z)ᶜ) (B := A ∪ B)
        (fun z hz ↦ by
          rw [hW] at hz
          exact not_and_or.mp hz) (p + q)
        (relativeSingularCohomologyUnionCup R A B
          (K.isCompact.isClosed.isOpen_compl.preimage q₁.continuous)
          (L.isCompact.isClosed.isOpen_compl.preimage q₂.continuous) p q
          (relativeSingularCohomologyPullback R q₁ (A := A) (B := (K : Set X)ᶜ)
            (fun _ hz ↦ hz) p a)
          (relativeSingularCohomologyPullback R q₂ (A := B) (B := (L : Set Y)ᶜ)
            (fun _ hz ↦ hz) q b))) := by
  have hW' : W = properCompactPreimage f hf (K ×ˢ L) := Compacts.ext hW
  subst W
  dsimp only
  let q₁ := (ContinuousMap.fst : C(X × Y, X)).comp f
  let q₂ := (ContinuousMap.snd : C(X × Y, Y)).comp f
  let A : Set Z := q₁ ⁻¹' (K : Set X)ᶜ
  let B : Set Z := q₂ ⁻¹' (L : Set Y)ᶜ
  let C : Set (X × Y) := Prod.fst ⁻¹' (K : Set X)ᶜ
  let D : Set (X × Y) := Prod.snd ⁻¹' (L : Set Y)ᶜ
  let hA : IsOpen A := K.isCompact.isClosed.isOpen_compl.preimage q₁.continuous
  let hB : IsOpen B := L.isCompact.isClosed.isOpen_compl.preimage q₂.continuous
  let hC : IsOpen C := K.isCompact.isClosed.isOpen_compl.preimage continuous_fst
  let hD : IsOpen D := L.isCompact.isClosed.isOpen_compl.preimage continuous_snd
  let α := relativeSingularCohomologyPullback R (ContinuousMap.fst : C(X × Y, X))
    (A := C) (B := (K : Set X)ᶜ) (fun _ hz ↦ hz) p a
  let β := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
    (A := D) (B := (L : Set Y)ᶜ) (fun _ hz ↦ hz) q b
  have hAC : Set.MapsTo f A C := fun _ hz ↦ hz
  have hBD : Set.MapsTo f B D := fun _ hz ↦ hz
  have hcomp {Z₁ Z₂ Z₃ : Type u} [TopologicalSpace Z₁] [TopologicalSpace Z₂]
      [TopologicalSpace Z₃] (f₀ : C(Z₁, Z₂)) (g₀ : C(Z₂, Z₃))
      {U₁ : Set Z₁} {U₂ : Set Z₂} {U₃ : Set Z₃}
      (hf₀ : Set.MapsTo f₀ U₁ U₂) (hg₀ : Set.MapsTo g₀ U₂ U₃) (k : ℕ)
      (z : relativeSingularCohomology R U₃ k) :
      relativeSingularCohomologyPullback R f₀ hf₀ k
        (relativeSingularCohomologyPullback R g₀ hg₀ k z) =
      relativeSingularCohomologyPullback R (g₀.comp f₀) (hg₀.comp hf₀) k z :=
    (congrArg (fun t ↦ t z) (relativeSingularCohomologyPullback_comp R f₀ g₀ hf₀ hg₀ k)).symm
  -- First identify the two factor pullbacks as the genuine components of f.
  have hα := hcomp f (ContinuousMap.fst : C(X × Y, X)) hAC
    (show Set.MapsTo ContinuousMap.fst C (K : Set X)ᶜ from fun _ hz ↦ hz) p a
  have hβ := hcomp f (ContinuousMap.snd : C(X × Y, Y)) hBD
    (show Set.MapsTo ContinuousMap.snd D (L : Set Y)ᶜ from fun _ hz ↦ hz) q b
  have hnat := relativeSingularCohomologyPullback_unionCup R f hA hB hC hD hAC hBD p q α β
  have hnat' := hnat.trans (congrArg₂
    (fun x y ↦ relativeSingularCohomologyUnionCup R A B hA hB p q x y) hα hβ)
  let V := properCompactPreimage f hf (K ×ˢ L)
  have hV : Set.MapsTo (ContinuousMap.id Z) (V : Set Z)ᶜ (A ∪ B) :=
    fun _ hz ↦ not_and_or.mp hz
  have hprod : Set.MapsTo (ContinuousMap.id (X × Y))
      (K ×ˢ L : Set (X × Y))ᶜ (C ∪ D) := fun _ hz ↦ not_and_or.mp hz
  have h₁ := hcomp f (ContinuousMap.id (X × Y))
    (show Set.MapsTo f (V : Set Z)ᶜ (K ×ˢ L : Set (X × Y))ᶜ from fun _ hz ↦ hz)
    hprod (p + q) (relativeSingularCohomologyUnionCup R C D hC hD p q α β)
  have h₂ := hcomp (ContinuousMap.id Z) f hV
    (show Set.MapsTo f (A ∪ B) (C ∪ D) from
      fun _ hz ↦ hz.elim (fun h ↦ Or.inl (hAC h)) (fun h ↦ Or.inr (hBD h)))
    (p + q) (relativeSingularCohomologyUnionCup R C D hC hD p q α β)
  -- The proper-pullback colimit leg uses this literal compact preimage, before any degree cast.
  unfold compactSupportCohomologyExternalRepresentative
  rw [compactSupportCohomologyProperPullback_representative]
  apply congrArg (compactSupportCohomologyClass R Z V (p + q))
  exact h₁.trans (h₂.symm.trans (congrArg
    (relativeSingularCohomologyPullback R (ContinuousMap.id Z) hV (p + q)) hnat'))

end AtiyahSinger
