/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportOpenExtension
public import AtiyahSinger.Topology.LocalHomologyChart
public import AtiyahSinger.Topology.SingularHomologyEvaluationNaturality

/-!
# Local cohomology and evaluation in the original charts

Public module ID: M1934.

Open embeddings induce the original excision isomorphisms in local cohomology.
Chart transport uses those maps and their actual inverses. Kronecker evaluation
is preserved when the integral local homology class is transported by the
existing chart equivalence and then rationalized.

Source: excision and the natural Kronecker pairing, Hatcher, Algebraic Topology,
Sections 2.1 and 3.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Topology

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original pullback of punctured pairs along an open embedding is excision. -/
def localCohomologyOpenEmbeddingIso (R : Type) [CommRing R] [T2Space Y]
    (f : C(X, Y)) (hf : IsOpenEmbedding f) (x : X) (k : ℕ) :
    relativeSingularCohomology R ({f x}ᶜ : Set Y) k ≅
      relativeSingularCohomology R ({x}ᶜ : Set X) k := by
  let P := relativeSingularCohomologyPullback R f
    (A := ({x}ᶜ : Set X)) (B := ({f x}ᶜ : Set Y))
    (fun _ hy h ↦ hy (hf.injective h)) k
  have hpre : ({x}ᶜ : Set X) = (f ⁻¹' ({f x} : Set Y))ᶜ := by
    ext y
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_preimage, hf.injective.eq_iff]
  have hexc {A : Set X} (hA : A = (f ⁻¹' ({f x} : Set Y))ᶜ)
      (h : Set.MapsTo f A ({f x}ᶜ : Set Y)) :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} R) (ComplexShape.down ℕ)
        (relativeSingularChainsMap R f h) := by
    subst A
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding R f hf
      {f x} isClosed_singleton (Set.singleton_subset_iff.mpr ⟨x, rfl⟩)
  have : IsIso P := isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences
    R _ (hexc hpre _) k
  exact asIso P

/-- Transport local cohomology through the same source, chart, and target as local homology. -/
def localCohomologyChartIso (R : Type) [CommRing R] [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (k : ℕ) :
    relativeSingularCohomology R ({x}ᶜ : Set X) k ≅
      relativeSingularCohomology R ({e x}ᶜ : Set Y) k :=
  (localCohomologyOpenEmbeddingIso R (ContinuousMap.subtypeVal e.source)
    e.open_source.isOpenEmbedding_subtypeVal ⟨x, hx⟩ k) ≪≫
    (localCohomologyOpenEmbeddingIso R
      ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
      e.toHomeomorphSourceTarget.isOpenEmbedding ⟨x, hx⟩ k).symm ≪≫
    (localCohomologyOpenEmbeddingIso R (ContinuousMap.subtypeVal e.target)
      e.open_target.isOpenEmbedding_subtypeVal
      (e.toHomeomorphSourceTarget ⟨x, hx⟩) k).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Local chart transport commutes with pullback along a map into its original source. -/
theorem localCohomologyChartIso_naturality (R : Type) [CommRing R]
    [T2Space X] [T2Space Y] {Z : Type u} [TopologicalSpace Z]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source)
    (p : C(Z, X)) (hp : ∀ z, p z ∈ e.source)
    {A : Set Z} (hA : Set.MapsTo p A ({x}ᶜ : Set X)) (k : ℕ) :
    (localCohomologyChartIso R e x hx k).hom ≫
      relativeSingularCohomologyPullback R
        (⟨fun z ↦ e (p z), e.continuousOn.comp_continuous p.continuous hp⟩ : C(Z, Y))
        (A := A) (B := ({e x}ᶜ : Set Y))
        (fun z hz heq ↦ hA hz (e.injOn (hp z) hx heq)) k =
      relativeSingularCohomologyPullback R p hA k := by
  let xs : e.source := ⟨x, hx⟩
  let yt : e.target := e.toHomeomorphSourceTarget xs
  let pS : C(Z, e.source) := ⟨fun z ↦ ⟨p z, hp z⟩, p.continuous.subtype_mk _⟩
  let i := ContinuousMap.subtypeVal e.source
  let j := ContinuousMap.subtypeVal e.target
  let f : C(e.source, e.target) :=
    ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
  let I := localCohomologyOpenEmbeddingIso R i
    e.open_source.isOpenEmbedding_subtypeVal xs k
  let F := localCohomologyOpenEmbeddingIso R f
    e.toHomeomorphSourceTarget.isOpenEmbedding xs k
  let J := localCohomologyOpenEmbeddingIso R j
    e.open_target.isOpenEmbedding_subtypeVal yt k
  let P := relativeSingularCohomologyPullback R pS
    (A := A) (B := ({xs}ᶜ : Set e.source))
    (fun _ hz heq ↦ hA hz (congrArg Subtype.val heq)) k
  have hsource : relativeSingularCohomologyPullback R p hA k = I.hom ≫ P := by
    change _ = relativeSingularCohomologyPullback R i _ k ≫
      relativeSingularCohomologyPullback R pS _ k
    rw [← relativeSingularCohomologyPullback_comp]
    rfl
  have htarget : relativeSingularCohomologyPullback R
      (⟨fun z ↦ e (p z), e.continuousOn.comp_continuous p.continuous hp⟩ : C(Z, Y))
      (A := A) (B := ({e x}ᶜ : Set Y))
      (fun z hz heq ↦ hA hz (e.injOn (hp z) hx heq)) k = J.hom ≫ F.hom ≫ P := by
    change _ = relativeSingularCohomologyPullback R j _ k ≫
      relativeSingularCohomologyPullback R f _ k ≫
      relativeSingularCohomologyPullback R pS _ k
    rw [← relativeSingularCohomologyPullback_comp,
      ← relativeSingularCohomologyPullback_comp]
    rfl
  -- Cancel precisely the two excision inverses used by this chart transport.
  rw [hsource, htarget]
  change (I.hom ≫ F.inv ≫ J.inv) ≫ (J.hom ≫ F.hom ≫ P) = I.hom ≫ P
  simp only [Category.assoc, J.inv_hom_id_assoc, F.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Evaluation remains natural when the same integral homology input is rationalized. -/
theorem singularCochainHomologyEvaluation_rationalization_natural
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : Set.MapsTo f A B) (k : ℕ)
    (a : relativeSingularCohomology ℚ B k) (z : relativeSingularHomology ℤ A k) :
    singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ B) k a
        (relativeSingularHomologyRationalization B k
          (relativeSingularHomologyMap ℤ f hf k z)) =
      singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ A) k
        (relativeSingularCohomologyPullback ℚ f hf k a)
        (relativeSingularHomologyRationalization A k z) := by
  -- Coefficient change commutes with this exact map of pairs.
  rw [relativeSingularHomologyRationalization_naturality f hf k z]
  -- The dual of the same chain map is exactly the given cohomology pullback.
  exact singularCochainHomologyEvaluation_naturality ℚ _ _
    (relativeSingularChainsMap ℚ f hf) k a
    (relativeSingularHomologyRationalization A k z)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original local chart transports rational evaluation without changing its normalization. -/
theorem localCohomologyChartIso_evaluation [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (k : ℕ)
    (a : relativeSingularCohomology ℚ ({x}ᶜ : Set X) k)
    (z : relativeSingularHomology ℤ ({x}ᶜ : Set X) k) :
    singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({e x}ᶜ : Set Y)) k
        ((localCohomologyChartIso ℚ e x hx k).hom a)
        (relativeSingularHomologyRationalization ({e x}ᶜ : Set Y) k
          (localHomologyChartEquiv e x hx k z)) =
      singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({x}ᶜ : Set X)) k a
        (relativeSingularHomologyRationalization ({x}ᶜ : Set X) k z) := by
  let xs : e.source := ⟨x, hx⟩
  let yt : e.target := e.toHomeomorphSourceTarget xs
  let i := ContinuousMap.subtypeVal e.source
  let j := ContinuousMap.subtypeVal e.target
  let f : C(e.source, e.target) :=
    ⟨e.toHomeomorphSourceTarget, e.toHomeomorphSourceTarget.continuous⟩
  let I := localCohomologyOpenEmbeddingIso ℚ i
    e.open_source.isOpenEmbedding_subtypeVal xs k
  let F := localCohomologyOpenEmbeddingIso ℚ f
    e.toHomeomorphSourceTarget.isOpenEmbedding xs k
  let J := localCohomologyOpenEmbeddingIso ℚ j
    e.open_target.isOpenEmbedding_subtypeVal yt k
  let zs := (localHomologyOpenInclusionEquiv e.source e.open_source xs k).symm z
  let zt := localHomologyHomeomorphEquiv e.toHomeomorphSourceTarget xs k zs
  -- Move across target inclusion, then across the same chart homeomorphism.
  change singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({e x}ᶜ : Set Y)) k
    (J.inv (F.inv (I.hom a)))
    (relativeSingularHomologyRationalization ({e x}ᶜ : Set Y) k
      (relativeSingularHomologyMap ℤ j
        (A := ({yt}ᶜ : Set e.target)) (B := ({e x}ᶜ : Set Y))
        (fun _ hy h ↦ hy (Subtype.ext h)) k zt)) = _
  rw [singularCochainHomologyEvaluation_rationalization_natural]
  change singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({yt}ᶜ : Set e.target))
    k (J.hom (J.inv (F.inv (I.hom a))))
    (relativeSingularHomologyRationalization ({yt}ᶜ : Set e.target) k zt) = _
  rw [Iso.inv_hom_id_apply]
  change singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({yt}ᶜ : Set e.target))
    k (F.inv (I.hom a))
    (relativeSingularHomologyRationalization ({yt}ᶜ : Set e.target) k
      (relativeSingularHomologyMap ℤ f
        (A := ({xs}ᶜ : Set e.source)) (B := ({yt}ᶜ : Set e.target))
        (fun _ hy h ↦ hy (e.toHomeomorphSourceTarget.injective h)) k zs)) = _
  rw [singularCochainHomologyEvaluation_rationalization_natural]
  change singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({xs}ᶜ : Set e.source))
    k (F.hom (F.inv (I.hom a)))
    (relativeSingularHomologyRationalization ({xs}ᶜ : Set e.source) k zs) = _
  rw [Iso.inv_hom_id_apply]
  -- Finally the original source excision map cancels its own inverse on z.
  have h := singularCochainHomologyEvaluation_rationalization_natural i
    (A := ({xs}ᶜ : Set e.source)) (B := ({x}ᶜ : Set X))
    (fun _ hy h ↦ hy (Subtype.ext h)) k a zs
  change singularCochainHomologyEvaluation ℚ (relativeSingularChains ℚ ({x}ᶜ : Set X)) k a
    (relativeSingularHomologyRationalization ({x}ᶜ : Set X) k
      (localHomologyOpenInclusionEquiv e.source e.open_source xs k zs)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end AtiyahSinger
