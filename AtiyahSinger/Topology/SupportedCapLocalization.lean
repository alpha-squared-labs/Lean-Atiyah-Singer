/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCapNaturality
public import AtiyahSinger.Topology.RelativeSingularExcision
public import AtiyahSinger.Topology.RelativeSingularOpenExcision
public import AtiyahSinger.Topology.SimplexLocalHomology

/-!
# Localization of the original supported cap product

Public module ID: M2203.

A cochain vanishing on `A` caps chains small for `{U, A}` to chains on `U`.
The localized operation is the unique lift through the original injective
subspace-chain inclusion. This keeps the front/back cap formula and is the
chain-level localization needed for its Mayer–Vietoris connecting identity.

Source: Hatcher, Algebraic Topology, section 3.3, the local cap argument.
The dimension-three implementation in PoincareLib's IntegralLocalizedCap
was consulted as a method reference; the construction here uses this project's
original complexes, arbitrary coefficients, and all nonnegative degrees.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency false in
/-- Refining a cover decreases the range of its actual small-chain inclusion. -/
theorem range_smallSingularChainsInclusion_le_of_refinement
    (𝒰 𝒱 : Set (Set X)) (href : ∀ U ∈ 𝒰, ∃ V ∈ 𝒱, U ⊆ V) (n : ℕ) :
    ((smallSingularChainsInclusion R 𝒰).f n).hom.range ≤
      ((smallSingularChainsInclusion R 𝒱).f n).hom.range := by
  have hle : smallSingularSet 𝒰 ≤ smallSingularSet 𝒱 := by
    intro k σ hσ
    obtain ⟨U, hU, hs⟩ := hσ
    obtain ⟨V, hV, hUV⟩ := href U hU
    exact ⟨V, hV, hs.trans hUV⟩
  let F := SSet.chainComplexMap (SSet.Subcomplex.homOfLE hle) (singularCoefficient R)
  have hF : F ≫ smallSingularChainsInclusion R 𝒱 = smallSingularChainsInclusion R 𝒰 := by
    exact (((SSet.chainComplexFunctor (ModuleCat.{u} R)).obj (singularCoefficient R)).map_comp
      (SSet.Subcomplex.homOfLE hle) (smallSingularSet 𝒱).ι).symm
  rintro c ⟨b, rfl⟩
  exact ⟨F.f n b, congrArg (fun f ↦ f.f n b) hF⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Smallness for an open region and the vanishing region localizes the actual cap chain.
Neither openness nor a cocycle assumption is needed for this chain-level statement. -/
theorem singularCochainCap_mem_subspace_of_small (U A : Set X) (p q : ℕ)
    (c : (singularChains R X).X (p + q))
    (hc : c ∈ ((smallSingularChainsInclusion R {U, A}).f (p + q)).hom.range)
    (φ : (relativeSingularCochains R A).X p) :
    singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val c ∈
      ((singularSubspaceChains R U).f q).hom.range := by
  -- A small chain is the actual sum of one U-chain and one A-chain.
  rw [range_smallSingularChainsInclusion_pair] at hc
  obtain ⟨b, rfl⟩ := hc
  let u := (biprod.fst : singularChains R U ⊞ singularChains R A ⟶ _).f (p + q) b
  let a := (biprod.snd : singularChains R U ⊞ singularChains R A ⟶ _).f (p + q) b
  have hsum := congrArg (fun f ↦ f.f (p + q) b)
    (biprod.desc_eq (f := singularSubspaceChains R U) (g := singularSubspaceChains R A))
  change (biprod.desc (singularSubspaceChains R U) (singularSubspaceChains R A)).f
    (p + q) b = (singularSubspaceChains R U).f (p + q) u +
      (singularSubspaceChains R A).f (p + q) a at hsum
  rw [hsum, map_add]
  -- The relative cochain kills the A-part before taking any homology quotient.
  have hzero := congrArg (fun f ↦ f a)
    (singularCochainCap_comp_subspace_eq_zero R A p q φ)
  change singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val
    ((singularSubspaceChains R A).f (p + q) a) = 0 at hzero
  rw [hzero, add_zero]
  -- Ordinary cap naturality supplies a lift of the remaining part on the same subspace.
  let i : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  refine ⟨singularCochainCap R U p q
    (((singularCochainsFunctor R).map (TopCat.ofHom i).op).f p
      (relativeSingularCochainEquiv R A p φ).val) u, ?_⟩
  exact singularCochainCap_naturality R i p q _ u

/-- The supported cap chain as an actual chain on the specified localization region. -/
def singularLocalizedCap (U A : Set X) (p q : ℕ)
    (c : (singularChains R X).X (p + q))
    (hc : c ∈ ((smallSingularChainsInclusion R {U, A}).f (p + q)).hom.range) :
    (relativeSingularCochains R A).X p →ₗ[R] (singularChains R U).X q := by
  let i := (singularSubspaceChains R U).f q
  let : IsSplitMono i := isSplitMono_singularChainsMap_of_injective R
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) Subtype.val_injective q
  let e := LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp inferInstance)
  let cap : (relativeSingularCochains R A).X p →ₗ[R] (singularChains R X).X q :=
    ((LinearMap.applyₗ c).comp (singularCochainCap R X p q)).comp
      ((Submodule.subtype _).comp (relativeSingularCochainEquiv R A p).toLinearMap)
  exact e.symm.toLinearMap.comp (cap.codRestrict i.hom.range
    (singularCochainCap_mem_subspace_of_small R U A p q c hc))

/-- Inclusion of the localized cap recovers the original ambient cap chain. -/
theorem singularSubspaceChains_singularLocalizedCap (U A : Set X) (p q : ℕ)
    (c : (singularChains R X).X (p + q))
    (hc : c ∈ ((smallSingularChainsInclusion R {U, A}).f (p + q)).hom.range)
    (φ : (relativeSingularCochains R A).X p) :
    (singularSubspaceChains R U).f q (singularLocalizedCap R U A p q c hc φ) =
      singularCochainCap R X p q (relativeSingularCochainEquiv R A p φ).val c := by
  let i := (singularSubspaceChains R U).f q
  let : IsSplitMono i := isSplitMono_singularChainsMap_of_injective R
    (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) Subtype.val_injective q
  let e := LinearEquiv.ofInjective i.hom ((ModuleCat.mono_iff_injective i).mp inferInstance)
  exact congrArg Subtype.val (e.apply_symm_apply
    ⟨_, singularCochainCap_mem_subspace_of_small R U A p q c hc φ⟩)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Naturality already holds for the original relative cap chains, before taking homology. -/
theorem relativeSingularCochainCap_naturality
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y)) {A : Set X} {B : Set Y}
    (hf : Set.MapsTo f A B) (p q : ℕ) (φ : (relativeSingularCochains R B).X p)
    (c : (relativeSingularChains R A).X (p + q)) :
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f q
        (relativeSingularCochainCap R A p q
          (((singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op).f p φ) c) =
      relativeSingularCochainCap R B p q φ
        ((relativeSingularChainsMap R f hf).f (p + q) c) := by
  let F := relativeSingularChainsMap R f hf
  let O := (singularChainsFunctor R).map (TopCat.ofHom f)
  let G := (singularCochainDualFunctor R).map F.op
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let P := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  have hchain : relativeSingularChainsProjection R A ≫ F =
      O ≫ relativeSingularChainsProjection R B := by
    simp [F, O, relativeSingularChainsProjection, relativeSingularChainsMap]
  have hdual : G ≫ JA = JB ≫ P := by
    change (singularCochainDualFunctor R).map F.op ≫
      (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op =
        (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op ≫
          (singularCochainDualFunctor R).map O.op
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp, hchain]
  -- Surjectivity of the original chain projection reduces the descent to cap naturality.
  obtain ⟨v, rfl⟩ := (ModuleCat.epi_iff_surjective
    ((relativeSingularChainsProjection R A).f (p + q))).mp inferInstance c
  have hchainval := congrArg (fun h ↦ h.f (p + q) v) hchain
  change F.f (p + q) ((relativeSingularChainsProjection R A).f (p + q) v) =
    (relativeSingularChainsProjection R B).f (p + q) (O.f (p + q) v) at hchainval
  change O.f q (relativeSingularCochainCap R A p q (G.f p φ) _) =
    relativeSingularCochainCap R B p q φ (F.f (p + q) _)
  rw [hchainval, relativeSingularCochainCap_projection, relativeSingularCochainCap_projection]
  have hdualval := congrArg (fun h ↦ h.f p φ) hdual
  change (relativeSingularCochainEquiv R A p (G.f p φ)).val =
    P.f p (relativeSingularCochainEquiv R B p φ).val at hdualval
  rw [hdualval]
  exact singularCochainCap_naturality R f p q _ v

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A localized cap represents the relative cap with the uniquely specified excision lift.
This identifies its class inside the open subspace, where ambient homology need not inject. -/
theorem exists_singularLocalizedCap_cycleClass
    (U A : Set X) (hU : IsOpen U) (hA : IsOpen A) (hcover : Aᶜ ⊆ U) (p q : ℕ)
    (c : (singularChains R X).X (p + q))
    (hc : c ∈ ((smallSingularChainsInclusion R {U, A}).f (p + q)).hom.range)
    (z : relativeSingularCycles R A (p + q))
    (hz : z.val = (relativeSingularChainsProjection R A).f (p + q) c)
    (φ : relativeSingularCocycles R A p)
    (w : relativeSingularHomology R ((Subtype.val : U → X) ⁻¹' A) (p + q))
    (hw : relativeSingularHomologyMap R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
        (A := (Subtype.val : U → X) ⁻¹' A) (B := A) (fun _ hx ↦ hx) (p + q) w =
      relativeSingularCycleClass R A (p + q) z) :
    ∃ b : singularCycles R U q,
      b.val = singularLocalizedCap R U A p q c hc φ.val ∧
      singularCycleClass R U q b = relativeSingularCapProduct R
        ((Subtype.val : U → X) ⁻¹' A) p q
        (relativeSingularCohomologyPullback R
          (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)) (fun _ hx ↦ hx) p
          (relativeSingularCocycleClass R A p φ)) w := by
  let i : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let B := i ⁻¹' A
  let F := relativeSingularChainsMap R i (A := B) (B := A) (fun _ hx ↦ hx)
  let G := (singularCochainDualFunctor R).map F.op
  let O := singularSubspaceChains R U
  let CU := relativeSingularChains R B
  let CX := relativeSingularChains R A
  let πU := relativeSingularChainsProjection R B
  let πX := relativeSingularChainsProjection R A
  have hF (k : ℕ) : Function.Injective (F.f k) := by
    let : IsSplitMono (F.f k) := isSplitMono_relativeSingularChainsMap_preimage R i
      Subtype.val_injective A k
    exact (ModuleCat.mono_iff_injective _).mp inferInstance
  -- Separate the small chain into its U-part and the part killed in the pair (X,A).
  obtain ⟨t, ht⟩ := (show c ∈
      ((biprod.desc (singularSubspaceChains R U) (singularSubspaceChains R A)).f
        (p + q)).hom.range by rwa [← range_smallSingularChainsInclusion_pair])
  let cu := (biprod.fst : singularChains R U ⊞ singularChains R A ⟶ _).f (p + q) t
  let ca := (biprod.snd : singularChains R U ⊞ singularChains R A ⟶ _).f (p + q) t
  have hsum : O.f (p + q) cu + (singularSubspaceChains R A).f (p + q) ca = c :=
    (congrArg (fun f ↦ f.f (p + q) t)
      (biprod.desc_eq (f := singularSubspaceChains R U)
        (g := singularSubspaceChains R A))).symm.trans ht
  have hchain : πU ≫ F = O ≫ πX := by
    simp [πU, F, O, πX, relativeSingularChainsMap, singularSubspaceChains, i]
  have hzU : F.f (p + q) (πU.f (p + q) cu) = z.val := by
    have h := congrArg (fun f ↦ f.f (p + q) cu) hchain
    change F.f (p + q) (πU.f (p + q) cu) = πX.f (p + q) (O.f (p + q) cu) at h
    rw [h, hz, ← hsum, map_add]
    have hkill := congrArg (fun f ↦ f.f (p + q) ca)
      (cokernel.condition (singularSubspaceChains R A))
    change πX.f (p + q) ((singularSubspaceChains R A).f (p + q) ca) = 0 at hkill
    rw [hkill, add_zero]
  let zu : relativeSingularCycles R B (p + q) := ⟨πU.f (p + q) cu, by
    change CU.dFrom (p + q) _ = 0
    have hinj : Function.Injective (F.next (p + q)) := hF _
    apply hinj
    have h := congrArg (fun f ↦ f (πU.f (p + q) cu)) (F.comm_from (p + q))
    change CX.dFrom (p + q) (F.f (p + q) (πU.f (p + q) cu)) =
      F.next (p + q) (CU.dFrom (p + q) (πU.f (p + q) cu)) at h
    have hzclosed : CX.dFrom (p + q) z.val = 0 := z.property
    rw [← h, hzU, hzclosed, map_zero]⟩
  let φU : relativeSingularCocycles R B p := ⟨G.f p φ.val, by
    change (relativeSingularCochains R B).dFrom p (G.f p φ.val) = 0
    have h := congrArg (fun f ↦ f φ.val) (G.comm_from p)
    change (relativeSingularCochains R B).dFrom p (G.f p φ.val) =
      G.next p ((relativeSingularCochains R A).dFrom p φ.val) at h
    have hφclosed : (relativeSingularCochains R A).dFrom p φ.val = 0 := φ.property
    rw [h, hφclosed, map_zero]⟩
  -- Excision identifies the constructed relative class with the specified local lift w.
  have hrep : homologyMap F (p + q) (relativeSingularCycleClass R B (p + q) zu) =
      relativeSingularCycleClass R A (p + q) z :=
    homologyMap_cycleClass R _ _ F (p + q) zu z hzU
  have hFIso : IsIso (homologyMap F (p + q)) := by
    have hrange : Aᶜ ⊆ Set.range i := fun x hx ↦ ⟨⟨x, hcover hx⟩, rfl⟩
    have hexc {B' : Set U} {A' : Set X}
        (hB' : B' = (i ⁻¹' Aᶜ)ᶜ) (hA' : A' = Aᶜᶜ) (hf : Set.MapsTo i B' A') :
        HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
          (relativeSingularChainsMap R i hf) := by
      subst B' A'
      exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R i
        hU.isOpenEmbedding_subtypeVal Aᶜ hA.isClosed_compl hrange
    have hF' : HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R)
        (ComplexShape.down ℕ) F :=
      hexc (B' := B) (A' := A) (by ext x; simp [B]) (compl_compl A).symm
        (fun _ hx ↦ hx)
    obtain ⟨e, he⟩ := hF'
    rw [← he]
    exact (e.toHomologyIso (p + q)).isIso_hom
  have hwU : relativeSingularCycleClass R B (p + q) zu = w :=
    ((ConcreteCategory.isIso_iff_bijective _).mp hFIso).1 (hrep.trans hw.symm)
  have hφ : relativeSingularCohomologyPullback R i (A := B) (B := A)
      (fun _ hx ↦ hx) p (relativeSingularCocycleClass R A p φ) =
        relativeSingularCocycleClass R B p φU :=
    homologyMap_cycleClass R _ _ G p φ φU rfl
  let b := relativeSingularCycleCap R B p q φU zu
  refine ⟨b, ?_, ?_⟩
  · -- Compare inside the injective subspace chain map, before passing to absolute homology.
    let : IsSplitMono (O.f q) := isSplitMono_singularChainsMap_of_injective R i
      Subtype.val_injective q
    apply (ModuleCat.mono_iff_injective (O.f q)).mp inferInstance
    change O.f q (relativeSingularCochainCap R B p q (G.f p φ.val) zu.val) = _
    have hn := relativeSingularCochainCap_naturality R i (A := B) (B := A)
      (fun _ hx ↦ hx) p q φ.val zu.val
    change O.f q (relativeSingularCochainCap R B p q (G.f p φ.val) zu.val) =
      relativeSingularCochainCap R A p q φ.val (F.f (p + q) (πU.f (p + q) cu)) at hn
    rw [hzU, hz] at hn
    rw [relativeSingularCochainCap_projection R A p q φ.val c] at hn
    exact hn.trans (singularSubspaceChains_singularLocalizedCap R U A p q c hc φ.val).symm
  · rw [← relativeSingularCapProduct_cycleClass, hwU, ← hφ]
    rfl

end AtiyahSinger
