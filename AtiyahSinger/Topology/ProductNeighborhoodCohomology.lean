/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyComparison
public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Ordinary detection for two contractible open cylinders

Public module ID: M2003.

The two relative long exact sequences split on cohomology by the coordinate
projections and contraction of the actual neighborhoods. The small-chain
comparison then embeds the original union-relative cohomology in ordinary
cohomology. This applies to the complement of a compact rectangle in the
product of two one-point compactifications, even when both factors are noncompact.

Source: the relative long exact sequence and singular excision (Hatcher,
Algebraic Topology, Sections 2.1 and 3.1). No quotient/cofibration comparison
or simplexwise detection assumption is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite
open scoped unitInterval

universe u

variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem mono_homologyMap_of_epi_restriction
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ)) (hS : S.ShortExact)
    (h : ∀ k, Epi (homologyMap S.g k)) (n : ℕ) : Mono (homologyMap S.f n) := by
  cases n with
  | zero =>
    have := hS.mono_f
    apply mono_homologyMap_of_mono_of_not_rel
    simp
  | succ n =>
    have := h n
    have hδ : hS.δ n (n + 1) rfl = 0 := by
      apply (cancel_epi (homologyMap S.g n)).mp
      exact (hS.comp_δ n (n + 1) rfl).trans (comp_zero).symm
    exact (hS.homology_exact₁ n (n + 1) rfl).mono_g hδ

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

private theorem isIso_leftCylinderSection (U : Set X) [ContractibleSpace U] (a : U)
    (n : ℕ) :
    IsIso (singularCohomologyPullback R
      (⟨fun y ↦ ⟨(a.val, y), a.property⟩,
        (continuous_const.prodMk continuous_id).subtype_mk _⟩ :
          C(Y, ↥(Prod.fst ⁻¹' U : Set (X × Y)))) n) := by
  let Z := ↥(Prod.fst ⁻¹' U : Set (X × Y))
  let j : C(Y, Z) := ⟨fun y ↦ ⟨(a.val, y), a.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩
  let r : C(Z, Y) := ⟨fun z ↦ z.val.2, continuous_snd.comp continuous_subtype_val⟩
  let first : C(Z, U) := ⟨fun z ↦ ⟨z.val.1, z.property⟩,
    (continuous_fst.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨p, ⟨H₀⟩⟩ := id_nullhomotopic U
  let H : (ContinuousMap.id U).Homotopy (ContinuousMap.const U a) :=
    H₀.trans (H₀.symm.compContinuousMap (ContinuousMap.const U a))
  apply isIso_singularCohomologyPullback_of_homotopyInverse R j r
  · exact ContinuousMap.Homotopic.refl _
  · refine ⟨{
      toFun := fun z ↦ ⟨((H.symm (z.1, first z.2)).val, (r z.2)), (H.symm _).property⟩
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }⟩
    · exact ((continuous_subtype_val.comp (H.symm.continuous.comp
        (continuous_fst.prodMk (first.continuous.comp continuous_snd)))).prodMk
          (r.continuous.comp continuous_snd)).subtype_mk _
    · intro z
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val (H.symm.map_zero_left (first z))) rfl
    · intro z
      apply Subtype.ext
      exact Prod.ext (congrArg Subtype.val (H.symm.map_one_left (first z))) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem isIso_leftCylinderRelativeSection
    (U : Set X) [ContractibleSpace U] (a : U) (V : Set Y) (n : ℕ) :
    let B : Set (X × Y) := Prod.fst ⁻¹' U
    let A : Set (X × Y) := Prod.snd ⁻¹' V
    IsIso (relativeSingularCohomologyPullback R
      (⟨fun y ↦ ⟨(a.val, y), a.property⟩,
        (continuous_const.prodMk continuous_id).subtype_mk _⟩ : C(Y, B))
      (A := V) (B := (Subtype.val : B → X × Y) ⁻¹' A) (fun _ hy ↦ hy) n) := by
  let B : Set (X × Y) := Prod.fst ⁻¹' U
  let A : Set (X × Y) := Prod.snd ⁻¹' V
  let C : Set B := (Subtype.val : B → X × Y) ⁻¹' A
  let j : C(Y, B) := ⟨fun y ↦ ⟨(a.val, y), a.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩
  apply isIso_relativeSingularCohomologyPullback_of_absolute R j
  · exact fun k ↦ isIso_leftCylinderSection R U a k
  · intro k
    let jV : C(V, C) := ⟨fun y ↦ ⟨⟨(a.val, y.val), a.property⟩, y.property⟩,
      ((continuous_const.prodMk continuous_subtype_val).subtype_mk _).subtype_mk _⟩
    let r : C(C, V) := ⟨fun z ↦ ⟨z.val.val.2, z.property⟩,
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
    let first : C(C, U) := ⟨fun z ↦ ⟨z.val.val.1, z.val.property⟩,
      (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _⟩
    obtain ⟨p, ⟨H₀⟩⟩ := id_nullhomotopic U
    let H : (ContinuousMap.id U).Homotopy (ContinuousMap.const U a) :=
      H₀.trans (H₀.symm.compContinuousMap (ContinuousMap.const U a))
    apply isIso_singularCohomologyPullback_of_homotopyInverse R jV r
    · exact ContinuousMap.Homotopic.refl _
    · refine ⟨{
        toFun := fun z ↦
          ⟨⟨((H.symm (z.1, first z.2)).val, (r z.2).val), (H.symm _).property⟩,
            (r z.2).property⟩
        continuous_toFun := ?_
        map_zero_left := ?_
        map_one_left := ?_ }⟩
      · apply Continuous.subtype_mk
        exact ((continuous_subtype_val.comp (H.symm.continuous.comp
          (continuous_fst.prodMk (first.continuous.comp continuous_snd)))).prodMk
            (continuous_subtype_val.comp (r.continuous.comp continuous_snd))).subtype_mk _
      · intro z
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (congrArg Subtype.val (H.symm.map_zero_left (first z))) rfl
      · intro z
        apply Subtype.ext
        apply Subtype.ext
        exact Prod.ext (congrArg Subtype.val (H.symm.map_one_left (first z))) rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem epi_relativeCylinderRestriction
    (U : Set X) [ContractibleSpace U] (V : Set Y) (n : ℕ) :
    let B : Set (X × Y) := Prod.fst ⁻¹' U
    let A : Set (X × Y) := Prod.snd ⁻¹' V
    Epi (relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (A := (Subtype.val : B → X × Y) ⁻¹' A) (B := A) (fun _ hx ↦ hx) n) := by
  let B : Set (X × Y) := Prod.fst ⁻¹' U
  let A : Set (X × Y) := Prod.snd ⁻¹' V
  let a : U := Classical.choice inferInstance
  let j : C(Y, B) := ⟨fun y ↦ ⟨(a.val, y), a.property⟩,
    (continuous_const.prodMk continuous_id).subtype_mk _⟩
  let pull := relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
    (A := (Subtype.val : B → X × Y) ⁻¹' A) (B := A) (fun _ hx ↦ hx) n
  let J := relativeSingularCohomologyPullback R j
    (A := V) (B := (Subtype.val : B → X × Y) ⁻¹' A) (fun _ hy ↦ hy) n
  let P := relativeSingularCohomologyPullback R (ContinuousMap.snd : C(X × Y, Y))
    (A := A) (B := V) (fun _ hx ↦ hx) n
  let : IsIso J := isIso_leftCylinderRelativeSection R U a V n
  have hfac : P ≫ pull ≫ J = 𝟙 _ := by
    dsimp only [P, pull, J]
    rw [← relativeSingularCohomologyPullback_comp,
      ← relativeSingularCohomologyPullback_comp]
    change (relativeSingularCohomologyFunctor R Y n).map (𝟙 (op V)) = _
    exact CategoryTheory.Functor.map_id _ _
  have hPI : P ≫ pull = inv J := by
    apply (cancel_mono J).mp
    rw [Category.assoc, hfac, IsIso.inv_hom_id]
  have : Epi (P ≫ pull) := hPI ▸ inferInstance
  exact epi_of_epi P pull

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem epi_rightCylinderRestriction
    (V : Set Y) [ContractibleSpace V] (n : ℕ) :
    Epi (singularCohomologyPullback R
      (ContinuousMap.subtypeVal (Prod.snd ⁻¹' V : Set (X × Y))) n) := by
  let A : Set (X × Y) := Prod.snd ⁻¹' V
  let b : V := Classical.choice inferInstance
  let i := ContinuousMap.subtypeVal A
  let r : C(X × Y, A) := ⟨fun z ↦ ⟨(z.1, b.val), b.property⟩,
    (continuous_fst.prodMk continuous_const).subtype_mk _⟩
  let second : C(A, V) := ⟨fun z ↦ ⟨z.val.2, z.property⟩,
    (continuous_snd.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨p, ⟨H₀⟩⟩ := id_nullhomotopic V
  let H : (ContinuousMap.id V).Homotopy (ContinuousMap.const V b) :=
    H₀.trans (H₀.symm.compContinuousMap (ContinuousMap.const V b))
  have H' : (r.comp i).Homotopy (ContinuousMap.id A) :=
    { toFun := fun z ↦ ⟨(z.2.val.1, (H.symm (z.1, second z.2)).val), (H.symm _).property⟩
      continuous_toFun :=
        ((continuous_fst.comp (continuous_subtype_val.comp continuous_snd)).prodMk
          (continuous_subtype_val.comp (H.symm.continuous.comp
            (continuous_fst.prodMk (second.continuous.comp continuous_snd))))).subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        exact Prod.ext rfl (congrArg Subtype.val (H.symm.map_zero_left (second z)))
      map_one_left := by
        intro z
        apply Subtype.ext
        exact Prod.ext rfl (congrArg Subtype.val (H.symm.map_one_left (second z))) }
  have hfac : singularCohomologyPullback R r n ≫
      singularCohomologyPullback R i n = 𝟙 _ := by
    let F := singularCohomologyFunctor R n
    change F.map (TopCat.ofHom r).op ≫ F.map (TopCat.ofHom i).op = _
    rw [← F.map_comp, ← op_comp]
    change singularCohomologyPullback R (r.comp i) n = _
    rw [singularCohomologyPullback_homotopic R H']
    exact F.map_id _
  exact epi_of_epi_fac hfac

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Two actual contractible open cylinders have injective union-relative forgetful map. -/
theorem relativeSingularCohomologyToOrdinary_openCylinders_injective
    (U : Set X) (V : Set Y) [ContractibleSpace U] [ContractibleSpace V]
    (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    Function.Injective (relativeSingularCohomologyToOrdinary R
      ((Prod.fst ⁻¹' U) ∪ (Prod.snd ⁻¹' V) : Set (X × Y)) n) := by
  let A : Set (X × Y) := Prod.snd ⁻¹' V
  let B : Set (X × Y) := Prod.fst ⁻¹' U
  let S := singularSubspaceCochainsSequence R A
  let T := relativeUnionSingularCochainSequence R A B
  let D := singularCochainDualFunctor R
  let J := D.map (relativeUnionSingularChainsProjection R B A).op
  -- Each restriction in the two original exact sequences is surjective on cohomology.
  have hS (k : ℕ) : Epi (homologyMap S.g k) :=
    epi_rightCylinderRestriction R V k
  have hT (k : ℕ) : Epi (homologyMap T.g k) :=
    epi_relativeCylinderRestriction R U V k
  have hmonoS : Mono (homologyMap S.f n) :=
    mono_homologyMap_of_epi_restriction R S (shortExact_singularSubspaceCochains R A) hS n
  have hmonoT : Mono (homologyMap T.f n) :=
    mono_homologyMap_of_epi_restriction R T
      (shortExact_relativeUnionSingularCochainSequence R A B) hT n
  -- Their composite is the original joint-relative projection after dualization.
  have hfactor : T.f ≫ S.f = J := by
    change D.map (relativeUnionSingularChainSequence R A B).g.op ≫
      D.map (relativeSingularChainsProjection R A).op = J
    rw [← D.map_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    dsimp [relativeUnionSingularChainSequence, relativeSingularChainsProjection]
    exact cokernel.π_desc _ _ _
  have hmonoJ : Mono (homologyMap J n) := by
    rw [← hfactor, homologyMap_comp]
    infer_instance
  -- Only the specified open-union small-chain comparison is inverted here.
  let C := relativeUnionCohomologyComparison R B A n
  have hC : IsIso C := (ConcreteCategory.isIso_iff_bijective C).mpr
    (relativeUnionCohomologyComparison_bijective R B A
      (hU.preimage continuous_fst) (hV.preimage continuous_snd) n)
  have hfinal : C ≫ homologyMap J n = relativeSingularCohomologyToOrdinary R (B ∪ A) n := by
    let F := D ⋙ homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n
    change F.map (relativeUnionSingularChainsToRelative R B A).op ≫
      F.map (relativeUnionSingularChainsProjection R B A).op =
        F.map (relativeSingularChainsProjection R (B ∪ A)).op
    rw [← F.map_comp, ← op_comp]
    congr 1
    apply congrArg Quiver.Hom.op
    exact cokernel.π_desc _ _ _
  have : Mono (relativeSingularCohomologyToOrdinary R (B ∪ A) n) :=
    hfinal ▸ inferInstance
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

end AtiyahSinger
