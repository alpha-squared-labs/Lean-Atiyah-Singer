/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactificationCohomologyOnePoint
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.ProductNeighborhoodCohomology

/-!
# Detection through the actual product compactification collapse

Public module ID: M2002.

Cofinal contractible infinity neighborhoods in both factors provide compact
rectangles on which the original excision extension is detected by ordinary
cohomology of the product compactification. The comparison with the specified
one-point collapse then detects every point-relative class represented by a
compact support. Both factors may be noncompact.

Source: singular excision, the original support colimit, and the two open-cylinder
relative exact sequences. The compact-support comparison hypothesis is explicit;
no general singular quotient comparison is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits OnePoint TopologicalSpace Topology

universe u

variable (R : Type) [CommRing R] {X Y : Type u}
  [TopologicalSpace X] [TopologicalSpace Y]
  [LocallyCompactSpace X] [LocallyCompactSpace Y] [T2Space X] [T2Space Y]

set_option maxHeartbeats 800000 in
-- Keep the original support-colimit maps and both compact-image excision inverses visible.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original product collapse detects point-relative classes represented by compact supports. -/
theorem singularCohomologyPullback_onePointProductCollapse_injective
    (hX : ∀ K : Compacts X, ∃ L : Compacts X, K ≤ L ∧
      ContractibleSpace ((((↑) : X → OnePoint X) '' (L : Set X))ᶜ : Set (OnePoint X)))
    (hY : ∀ K : Compacts Y, ∃ L : Compacts Y, K ≤ L ∧
      ContractibleSpace ((((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ : Set (OnePoint Y)))
    (n : ℕ)
    (hpoint : Function.Surjective (compactSupportCohomologyToOnePoint R (X × Y) n)) :
    Function.Injective (fun a : relativeSingularCohomology R
      ({∞} : Set (OnePoint (X × Y))) n ↦
        singularCohomologyPullback R onePointProductCollapseMap n
          (relativeSingularCohomologyToOrdinary R {∞} n a)) := by
  classical
  let Z := OnePoint X × OnePoint Y
  let f : C(X, OnePoint X) := ⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩
  let g : C(Y, OnePoint Y) := ⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩
  let j : C(X × Y, Z) := f.prodMap g
  let hj : IsOpenEmbedding j :=
    OnePoint.isOpenEmbedding_coe.prodMap OnePoint.isOpenEmbedding_coe
  let F := compactSupportCohomologyOpenExtension R j hj n ≫
    compactSupportCohomologyToOrdinary R Z n
  -- Enlarge the original support to one rectangle with contractible complement in each factor.
  have hzero (a : compactSupportCohomology R (X × Y) n) (ha : F a = 0) : a = 0 := by
    obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative R (X × Y) n a
    obtain ⟨L₁, hL₁, hcontract₁⟩ := hX (K.map Prod.fst continuous_fst)
    obtain ⟨L₂, hL₂, hcontract₂⟩ := hY (K.map Prod.snd continuous_snd)
    let M : Compacts (X × Y) := L₁ ×ˢ L₂
    have hKM : K ≤ M := by
      intro z hz
      exact ⟨hL₁ ⟨z, hz, rfl⟩, hL₂ ⟨z, hz, rfl⟩⟩
    let β := (compactSupportCohomologyFunctor R (X × Y) n).map (homOfLE hKM) α
    have hrepr : compactSupportCohomologyClass R (X × Y) M n β =
        compactSupportCohomologyClass R (X × Y) K n α :=
      congrArg (fun t ↦ t α) (colimit.w (compactSupportCohomologyFunctor R (X × Y) n)
        (homOfLE hKM))
    let U : Set (OnePoint X) := (((↑) : X → OnePoint X) '' (L₁ : Set X))ᶜ
    let V : Set (OnePoint Y) := (((↑) : Y → OnePoint Y) '' (L₂ : Set Y))ᶜ
    let : ContractibleSpace U := hcontract₁
    let : ContractibleSpace V := hcontract₂
    have hU : IsOpen U := (L₁.isCompact.image OnePoint.continuous_coe).isClosed.isOpen_compl
    have hV : IsOpen V := (L₂.isCompact.image OnePoint.continuous_coe).isClosed.isOpen_compl
    let M' := openEmbeddingCompactImage j M
    have hcomplement : (M' : Set Z)ᶜ = (Prod.fst ⁻¹' U) ∪ (Prod.snd ⁻¹' V) := by
      ext z
      constructor
      · intro hz
        change z.1 ∉ ((↑) : X → OnePoint X) '' (L₁ : Set X) ∨
          z.2 ∉ ((↑) : Y → OnePoint Y) '' (L₂ : Set Y)
        by_contra h
        obtain ⟨⟨x, hx, heqx⟩, ⟨y, hy, heqy⟩⟩ :=
          not_or.mp h |>.imp not_not.mp not_not.mp
        exact hz ⟨(x, y), ⟨hx, hy⟩, Prod.ext heqx heqy⟩
      · rintro (hz | hz) ⟨z', hz', heq⟩
        · exact hz ⟨z'.1, hz'.1, congrArg Prod.fst heq⟩
        · exact hz ⟨z'.2, hz'.2, congrArg Prod.snd heq⟩
    have hdetect : Function.Injective (relativeSingularCohomologyToOrdinary R
        ((M' : Set Z)ᶜ) n) := by
      rw [hcomplement]
      exact relativeSingularCohomologyToOrdinary_openCylinders_injective R U V hU hV n
    let P := openEmbeddingCohomologySupportPullback R j hj M n
    let : IsIso P := isIso_openEmbeddingCohomologySupportPullback R j hj M n
    let γ := (asIso P).inv β
    have hγ : relativeSingularCohomologyToOrdinary R (M' : Set Z)ᶜ n γ = 0 := by
      have hF : F (compactSupportCohomologyClass R (X × Y) M n β) = 0 :=
        (congrArg F hrepr).trans ha
      change compactSupportCohomologyToOrdinary R Z n
        (compactSupportCohomologyOpenExtension R j hj n
          (compactSupportCohomologyClass R (X × Y) M n β)) = 0 at hF
      rw [compactSupportCohomologyOpenExtension_representative] at hF
      have hleg : compactSupportCohomologyClass R Z M' n ≫
          compactSupportCohomologyToOrdinary R Z n =
          relativeSingularCohomologyToOrdinary R (M' : Set Z)ᶜ n := colimit.ι_desc _ M'
      exact (congrArg (fun t ↦ t γ) hleg).symm.trans hF
    have hγzero : γ = 0 := hdetect (hγ.trans (map_zero _).symm)
    have hβzero : β = 0 := by
      have hcancel : P γ = β := (asIso P).inv_hom_id_apply β
      exact hcancel.symm.trans ((congrArg P hγzero).trans (map_zero _))
    rw [← hrepr, hβzero, map_zero]
  have hF : Function.Injective F := by
    intro a b hab
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, hab, sub_self]
  -- The actual collapse and open extension compare the same supported representative.
  let q : C(Z, OnePoint (X × Y)) := onePointProductCollapseMap
  have hfinite (z : X × Y) : q (j z) = (z : OnePoint (X × Y)) := rfl
  have hinfty (z : Z) (hz : z ∉ Set.range j) : q z = ∞ := by
    rcases z with ⟨x, y⟩
    cases x using OnePoint.rec <;> cases y using OnePoint.rec
    · rfl
    · rfl
    · rfl
    · exact False.elim (hz ⟨(_, _), rfl⟩)
  intro a b hab
  obtain ⟨α, rfl⟩ := hpoint a
  obtain ⟨β, rfl⟩ := hpoint b
  have hcompare (c : compactSupportCohomology R (X × Y) n) :
      singularCohomologyPullback R q n
        (relativeSingularCohomologyToOrdinary R {∞} n
          (compactSupportCohomologyToOnePoint R (X × Y) n c)) = F c :=
    compactSupportCohomologyOpenExtension_toOrdinary_onePoint R j hj q hfinite hinfty n c
  have hαβ : α = β := hF ((hcompare α).symm.trans (hab.trans (hcompare β)))
  exact congrArg (compactSupportCohomologyToOnePoint R (X × Y) n) hαβ

end AtiyahSinger
