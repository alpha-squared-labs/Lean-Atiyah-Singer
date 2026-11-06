/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyOnePoint
public import AtiyahSinger.Topology.CompactSupportExternalRepresentative
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality

/-!
# Chern convolution for two supported representatives

Public module ID: M1653.

The finite convolution uses actual relative representatives on two fixed
compact supports and their product support. The original one-point product
collapse compares its ordinary image with the absolute Chern character.
A specified injectivity certificate then recovers the original point-relative
identity. That certificate is an explicit hypothesis here; applications must
supply the geometry which proves it for their actual spaces.

Source: multiplicativity and naturality of the Chern character, SG III.11.
The comparison between the original supported models is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory OnePoint TopologicalSpace Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]

set_option maxHeartbeats 600000 in
-- Keep the original point-relative and compact-support degree transports explicit.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Supported external Chern convolution, detected through the original product collapse. -/
theorem compactSupportChernCharacter_externalRepresentative
    (a : CompactSupportKZero X) (b : CompactSupportKZero Y)
    (K : Compacts X) (L : Compacts Y)
    (α : ∀ k, relativeSingularCohomology ℚ (K : Set X)ᶜ (2 * k))
    (β : ∀ k, relativeSingularCohomology ℚ (L : Set Y)ᶜ (2 * k))
    (hα : ∀ k, compactSupportCohomologyToOnePoint ℚ X (2 * k)
      (compactSupportCohomologyClass ℚ X K (2 * k) (α k)) =
        reducedChernCharacterComponent (∞ : OnePoint X) k a)
    (hβ : ∀ k, compactSupportCohomologyToOnePoint ℚ Y (2 * k)
      (compactSupportCohomologyClass ℚ Y L (2 * k) (β k)) =
        reducedChernCharacterComponent (∞ : OnePoint Y) k b)
    (k : ℕ)
    (hdetect : Function.Injective (fun z : relativeSingularCohomology ℚ
      ({∞} : Set (OnePoint (X × Y))) (2 * k) ↦
      singularCohomologyPullback ℚ onePointProductCollapseMap (2 * k)
        (relativeSingularCohomologyToOrdinary ℚ {∞} (2 * k) z))) :
    compactSupportCohomologyToOnePoint ℚ (X × Y) (2 * k)
      (∑ i : Fin (k + 1),
        (eqToIso (by congr 1; omega) :
          compactSupportCohomology ℚ (X × Y) (2 * i.val + 2 * (k - i.val)) ≅
            compactSupportCohomology ℚ (X × Y) (2 * k)).hom
          (compactSupportCohomologyExternalRepresentative ℚ K L
            (2 * i.val) (2 * (k - i.val)) (α i.val) (β (k - i.val)))) =
      reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k
        (compactSupportKZeroExternalProduct a b) := by
  let Z := OnePoint X × OnePoint Y
  let iX : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let iY : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let j : C(X × Y, Z) := iX.prodMap iY
  let hj : IsOpenEmbedding j := OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
  let Q : C(Z, OnePoint (X × Y)) := onePointProductCollapseMap
  let D (n : ℕ) := relativeSingularCohomologyToOrdinary ℚ
    ({∞} : Set (OnePoint (X × Y))) n ≫ singularCohomologyPullback ℚ Q n
  have hcollapse (n : ℕ) (c : compactSupportCohomology ℚ (X × Y) n) :
      D n (compactSupportCohomologyToOnePoint ℚ (X × Y) n c) =
      compactSupportCohomologyToOrdinary ℚ Z n
        (compactSupportCohomologyOpenExtension ℚ j hj n c) := by
    apply compactSupportCohomologyOpenExtension_toOrdinary_onePoint ℚ j hj Q
    · intro x
      rfl
    · rintro ⟨x, y⟩ h
      cases x using OnePoint.rec with
      | infty => rfl
      | coe x =>
        cases y using OnePoint.rec with
        | infty => rfl
        | coe y => exact False.elim (h ⟨(x, y), rfl⟩)
  have hpoint {V : Type u} [TopologicalSpace V] [LocallyCompactSpace V] [T2Space V]
      (n : ℕ) (c : compactSupportCohomology ℚ V n) :
      relativeSingularCohomologyToOrdinary ℚ ({∞} : Set (OnePoint V)) n
        (compactSupportCohomologyToOnePoint ℚ V n c) =
      compactSupportCohomologyToOrdinary ℚ (OnePoint V) n
        (compactSupportCohomologyOpenExtension ℚ
          ⟨((↑) : V → OnePoint V), OnePoint.continuous_coe⟩
          OnePoint.isOpenEmbedding_coe n c) := by
    have h := compactSupportCohomologyOpenExtension_toOrdinary_onePoint ℚ
      ⟨((↑) : V → OnePoint V), OnePoint.continuous_coe⟩ OnePoint.isOpenEmbedding_coe
      (ContinuousMap.id (OnePoint V)) (fun _ ↦ rfl) (fun z hz ↦ by
        cases z using OnePoint.rec with
        | infty => rfl
        | coe v => exact False.elim (hz ⟨v, rfl⟩)) n c
    have hid : singularCohomologyPullback ℚ (ContinuousMap.id (OnePoint V)) n = 𝟙 _ := by
      exact CategoryTheory.Functor.map_id _ _
    rw [hid] at h
    exact h
  have hcast {p q : ℕ} (hpq : p = q) (c : compactSupportCohomology ℚ (X × Y) p) :
      D q (compactSupportCohomologyToOnePoint ℚ (X × Y) q
        ((eqToIso (congrArg (compactSupportCohomology ℚ (X × Y)) hpq)).hom c)) =
      (eqToIso (congrArg (singularCohomology ℚ Z) hpq)).hom
        (D p (compactSupportCohomologyToOnePoint ℚ (X × Y) p c)) := by
    subst q
    rfl
  -- Absolute Chern multiplication uses precisely the original K external product identity.
  have hright : D (2 * k)
      (reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k
        (compactSupportKZeroExternalProduct a b)) =
      chernCharacterKZeroComponent Z k
        (complexKZeroPullback ContinuousMap.fst a.val *
          complexKZeroPullback ContinuousMap.snd b.val) := by
    change singularCohomologyPullback ℚ Q (2 * k)
      (relativeSingularCohomologyToOrdinary ℚ {∞} (2 * k) _) = _
    rw [reducedChernCharacterComponent_toOrdinary,
      ← chernCharacterKZeroComponent_pullback, compactSupportKZeroExternalProduct_pullback]
    rfl
  apply hdetect
  change D (2 * k) (compactSupportCohomologyToOnePoint ℚ (X × Y) (2 * k) _) =
    D (2 * k) (reducedChernCharacterComponent (∞ : OnePoint (X × Y)) k _)
  rw [hright, chernCharacterKZeroComponent_mul]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hcast (by omega), hcollapse,
    compactSupportCohomologyExternalRepresentative_openExtension_toOrdinary ℚ
      iX OnePoint.isOpenEmbedding_coe iY OnePoint.isOpenEmbedding_coe,
    ← hpoint, ← hpoint, hα, hβ, reducedChernCharacterComponent_toOrdinary,
    reducedChernCharacterComponent_toOrdinary,
    chernCharacterKZeroComponent_pullback, chernCharacterKZeroComponent_pullback]
  -- The convolution and ordinary even-cup formulas only differ by degree reassociation.
  let c := singularCohomologyCup ℚ Z (2 * i.val) (2 * (k - i.val))
    (singularCohomologyPullback ℚ ContinuousMap.fst (2 * i.val)
      (chernCharacterKZeroComponent (OnePoint X) i.val a.val))
    (singularCohomologyPullback ℚ ContinuousMap.snd (2 * (k - i.val))
      (chernCharacterKZeroComponent (OnePoint Y) (k - i.val) b.val))
  change (eqToHom (by congr 1; omega) :
    singularCohomology ℚ Z (2 * i.val + 2 * (k - i.val)) ⟶
      singularCohomology ℚ Z (2 * k)) c =
    (eqToHom (by congr 1; omega) : singularCohomology ℚ Z (2 * (i.val + (k - i.val))) ⟶
      singularCohomology ℚ Z (2 * k))
      ((eqToHom (by congr 1; omega) : singularCohomology ℚ Z (2 * i.val + 2 * (k - i.val)) ⟶
        singularCohomology ℚ Z (2 * (i.val + (k - i.val)))) c)
  rw [← ModuleCat.comp_apply, eqToHom_trans]

end AtiyahSinger
