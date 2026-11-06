/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.OnePointCohomology
public import AtiyahSinger.Topology.OpenEmbeddingKZero
public import AtiyahSinger.Topology.ReducedChernCharacterNaturality

/-!
# Chern character and the original open extension

Public module ID: M1654.

The excision definition of cohomological open extension agrees with pullback
along the actual one-point collapse used by K-theoretic open pushforward.
The comparison is checked on each original compact support, retaining both
excision inverses and restriction to infinity. It needs no injectivity after
forgetting support and does not require an open embedding to be proper.

Source: SG III.12, compact-support functoriality of the Chern character;
Hatcher, Algebraic Topology, Section 3.3, extension by zero and excision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Topology TopologicalSpace OnePoint

universe u

variable {X Y : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Open extension preserves a supported lift of the original reduced Chern character. -/
theorem compactSupportChernCharacter_openPushforward
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (k : ℕ)
    (u : CompactSupportKZero X) (a : compactSupportCohomology ℚ X (2 * k))
    (ha : compactSupportCohomologyToOnePoint ℚ X (2 * k) a =
      reducedChernCharacterComponent (∞ : OnePoint X) k u) :
    compactSupportCohomologyToOnePoint ℚ Y (2 * k)
        (compactSupportCohomologyOpenExtension ℚ f hf (2 * k) a) =
      reducedChernCharacterComponent (∞ : OnePoint Y) k
        (compactSupportKZeroOpenPushforward f hf u) := by
  let := hf.isOpen_range.locallyCompactSpace
  let e := hf.isEmbedding.toHomeomorph
  let c : C(OnePoint Y, OnePoint X) :=
    (properOnePointMap ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap).comp
      ⟨onePointCollapse (Set.range f), continuous_onePointCollapse _ hf.isOpen_range⟩
  have hinfty : c ∞ = ∞ := rfl
  have hfinite (x : X) : c (f x : OnePoint Y) = (x : OnePoint X) := by
    change OnePoint.map e.symm (onePointCollapse (Set.range f) (f x)) = _
    rw [onePointCollapse_coe_of_mem (Set.range f) (f x) ⟨x, rfl⟩, OnePoint.map_some]
    exact congrArg OnePoint.some (hf.isEmbedding.toHomeomorph_symm_apply x)
  have houtside (y : Y) (hy : y ∉ Set.range f) : c (y : OnePoint Y) = ∞ := by
    change OnePoint.map e.symm (onePointCollapse (Set.range f) y) = _
    rw [onePointCollapse_coe_of_notMem (Set.range f) y hy, OnePoint.map_infty]
  let hpoint : Set.MapsTo c ({∞} : Set (OnePoint Y)) ({∞} : Set (OnePoint X)) :=
    fun _ hz ↦ hz ▸ hinfty
  -- The collapse square is compared before either relative class is restricted to infinity.
  have hcoh (n : ℕ) (b : compactSupportCohomology ℚ X n) :
      compactSupportCohomologyToOnePoint ℚ Y n
        (compactSupportCohomologyOpenExtension ℚ f hf n b) =
      relativeSingularCohomologyPullback ℚ c hpoint n
        (compactSupportCohomologyToOnePoint ℚ X n b) := by
    obtain ⟨K, α, rfl⟩ := compactSupportCohomology_exists_representative ℚ X n b
    let L := openEmbeddingCompactImage f K
    let AX : Set (OnePoint X) := (((↑) : X → OnePoint X) '' (K : Set X))ᶜ
    let AY : Set (OnePoint Y) := (((↑) : Y → OnePoint Y) '' (L : Set Y))ᶜ
    have hAX : ({∞} : Set (OnePoint X)) ⊆ AX := by
      rintro z rfl
      exact OnePoint.infty_notMem_image_coe
    have hAY : ({∞} : Set (OnePoint Y)) ⊆ AY := by
      rintro z rfl
      exact OnePoint.infty_notMem_image_coe
    have hc : Set.MapsTo c AY AX := by
      intro z hz himage
      obtain ⟨x, hx, hcx⟩ := himage
      cases z using OnePoint.rec with
      | infty => exact OnePoint.coe_ne_infty x (hcx.trans hinfty)
      | coe y =>
        by_cases hy : y ∈ Set.range f
        · obtain ⟨w, rfl⟩ := hy
          have hxw : x = w := OnePoint.coe_injective (hcx.trans (hfinite w))
          subst w
          exact hz ⟨f x, ⟨x, hx, rfl⟩, rfl⟩
        · exact OnePoint.coe_ne_infty x (hcx.trans (houtside y hy))
    let pF := openEmbeddingCohomologySupportPullback ℚ f hf K n
    let pX := onePointCohomologySupportPullback ℚ X K n
    let pY := onePointCohomologySupportPullback ℚ Y L n
    let q := relativeSingularCohomologyPullback ℚ c hc n
    let rX := relativeSingularCohomologyRestriction ℚ {∞} AX hAX n
    let rY := relativeSingularCohomologyRestriction ℚ {∞} AY hAY n
    let : IsIso pF := isIso_openEmbeddingCohomologySupportPullback ℚ f hf K n
    let : IsIso pX := isIso_onePointCohomologySupportPullback ℚ X K n
    let : IsIso pY := isIso_onePointCohomologySupportPullback ℚ Y L n
    have hsquare : q ≫ pY ≫ pF = pX := by
      dsimp only [q, pY, pF, pX, onePointCohomologySupportPullback,
        openEmbeddingCohomologySupportPullback]
      rw [← relativeSingularCohomologyPullback_comp,
        ← relativeSingularCohomologyPullback_comp]
      have hmaps : c.comp
          ((⟨((↑) : Y → OnePoint Y), OnePoint.continuous_coe⟩ : C(Y, OnePoint Y)).comp f) =
          (⟨((↑) : X → OnePoint X), OnePoint.continuous_coe⟩ : C(X, OnePoint X)) := by
        ext x
        exact hfinite x
      simp only [hmaps]
    have hα : q ((asIso pX).inv α) = (asIso pY).inv ((asIso pF).inv α) := by
      apply (ConcreteCategory.isIso_iff_bijective pY).mp inferInstance |>.injective
      apply (ConcreteCategory.isIso_iff_bijective pF).mp inferInstance |>.injective
      have hh := congrArg (fun g ↦ g ((asIso pX).inv α)) hsquare
      change pF (pY (q ((asIso pX).inv α))) = pX ((asIso pX).inv α) at hh
      have hX : pX ((asIso pX).inv α) = α := (asIso pX).inv_hom_id_apply α
      have hY : pY ((asIso pY).inv ((asIso pF).inv α)) = (asIso pF).inv α :=
        (asIso pY).inv_hom_id_apply ((asIso pF).inv α)
      have hF : pF ((asIso pF).inv α) = α := (asIso pF).inv_hom_id_apply α
      rw [hX] at hh
      rw [hY, hF]
      exact hh
    have hrestriction : rX ≫ relativeSingularCohomologyPullback ℚ c hpoint n = q ≫ rY :=
      relativeSingularCohomologyPullback_restriction ℚ c hAY hAX hpoint hc n
    rw [compactSupportCohomologyOpenExtension_representative]
    change compactSupportCohomologyToOnePoint ℚ Y n
      (compactSupportCohomologyClass ℚ Y L n ((asIso pF).inv α)) = _
    rw [compactSupportCohomologyToOnePoint_representative,
      compactSupportCohomologyToOnePoint_representative]
    change rY ((asIso pY).inv ((asIso pF).inv α)) =
      relativeSingularCohomologyPullback ℚ c hpoint n (rX ((asIso pX).inv α))
    rw [← hα]
    exact (congrArg (fun g ↦ g ((asIso pX).inv α)) hrestriction).symm
  rw [hcoh, ha, reducedChernCharacterComponent_pullback (∞ : OnePoint Y)
    (∞ : OnePoint X) c hinfty u k]
  congr 1
  apply Subtype.ext
  change complexKZeroPullback c u.val = _
  dsimp only [c]
  rw [complexKZeroPullback_comp]
  rfl

/-- On a compact target, the same open extension has the original absolute Chern character. -/
theorem compactSupportChernCharacter_openPushforward_toOrdinary [CompactSpace Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (k : ℕ)
    (u : CompactSupportKZero X) (a : compactSupportCohomology ℚ X (2 * k))
    (ha : compactSupportCohomologyToOnePoint ℚ X (2 * k) a =
      reducedChernCharacterComponent (∞ : OnePoint X) k u) :
    compactSupportCohomologyToOrdinary ℚ Y (2 * k)
        (compactSupportCohomologyOpenExtension ℚ f hf (2 * k) a) =
      chernCharacterKZeroComponent Y k ((compactSupportKZeroCompactEquiv Y)
        (compactSupportKZeroOpenPushforward f hf u)) := by
  -- Finite-point restriction is exactly the original compact-base K equivalence.
  rw [← compactSupportCohomologyToOnePoint_toOrdinary,
    compactSupportChernCharacter_openPushforward f hf k u a ha,
    reducedChernCharacterComponent_toOrdinary, ← chernCharacterKZeroComponent_pullback]
  rfl

end AtiyahSinger
