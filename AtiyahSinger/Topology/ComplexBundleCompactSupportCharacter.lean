/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.CompactSupportCohomologyHomeomorph
public import AtiyahSinger.Topology.ComplexBundleRealOrientation
public import AtiyahSinger.Topology.FiniteBundleTopology

/-!
# Compact-support Chern character on the original complex bundle total space

Public module ID: M1696.

C04. The original Unit-model total space, its existing Kc class and its
existing compact-support cohomology are retained. The canonical native real
model is homeomorphic to this total space by the identity on base points and
vectors. With the same supplied Hermitian metric it is a continuous real
Riemannian bundle of rank twice the specified complex rank. The actual
one-point comparison is therefore bijective by the real bundle theorem.

This is transfer of that precise comparison through the original homeomorphism,
not selection of an unrelated cohomology equivalence or a replacement K class.
The inverse comparison applied to the original reduced Chern character gives
the supported character. Compact base, constant finite complex rank and the
specified metric are explicit; rank zero and the empty base are included.
No compactness of the total space or properness of its projection is assumed.

Sources: the compact disk and relative-cohomology construction recorded in
BundleCompactSupportCharacter, Hatcher sections 2.1 and 3.3, and SG III.12.
The compatibility of these original singular models is a project supplement,
not an imported Cech-to-singular comparison. The one-point comparison and the
character's defining comparison and forget-support identities are proved.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle CategoryTheory OnePoint

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

namespace ContinuousHermitianMetric

variable (h : ContinuousHermitianMetric E)

include h in
/-- The same one-point comparison is bijective on the original complex bundle total space. -/
theorem compactSupportCohomologyToOnePoint_bijective
    (R : Type) [CommRing R] (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (n : ℕ) :
    Function.Bijective (compactSupportCohomologyToOnePoint R (TotalSpace Unit E) n) := by
  -- Use the real part of precisely the supplied Hermitian metric and its native atlas.
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let F := EuclideanSpace ℝ (Fin (2 * r))
  let := nativeModelTopology E F
  let := h.realNativeFiberBundle r hr
  let := h.realNativeVectorBundle r hr
  let := h.realNativeRiemannianBundle r hr
  let V := TotalSpace F E
  let Y := TotalSpace Unit E
  let e : V ≃ₜ Y := nativeModelTotalHomeomorph E F
  let : T2Space V := t2Space_fiberBundleTotal F E
  let : LocallyCompactSpace V := locallyCompactSpace_fiberBundleTotal F E
  have hnative := compactSupportCohomologyToOnePoint_bundle_bijective R (2 * r) E n
  let p := compactSupportCohomologyHomeomorphPullback R e n
  have hp : Function.Bijective p := compactSupportCohomologyHomeomorphPullback_bijective R e n
  -- The extended homeomorphism is an isomorphism on both members of the singleton pair.
  let eInf := e.onePointCongr
  let f : C(OnePoint V, OnePoint Y) := ⟨eInf, eInf.continuous⟩
  have hf : Set.MapsTo f ({∞} : Set (OnePoint V)) ({∞} : Set (OnePoint Y)) := by
    rintro z rfl
    rfl
  let es : ({∞} : Set (OnePoint V)) ≃ₜ ({∞} : Set (OnePoint Y)) :=
    eInf.subtype (fun z ↦ by
      change z = ∞ ↔ eInf z = ∞
      constructor
      · rintro rfl
        rfl
      · intro hz
        exact eInf.injective (hz.trans (show eInf ∞ = ∞ from rfl).symm))
  have : IsIso (TopCat.ofHom f) := by
    change IsIso (TopCat.isoOfHomeo
      (X := TopCat.of (OnePoint V)) (Y := TopCat.of (OnePoint Y)) eInf).hom
    infer_instance
  have : IsIso (TopCat.ofHom (⟨es, es.continuous⟩ : C(_, _))) := by
    change IsIso (TopCat.isoOfHomeo
      (X := TopCat.of ({∞} : Set (OnePoint V)))
      (Y := TopCat.of ({∞} : Set (OnePoint Y))) es).hom
    infer_instance
  have : IsIso (relativeSingularChainsMap R f hf) := by
    change IsIso (Limits.cokernel.map _ _
      ((singularChainsFunctor R).map (TopCat.ofHom (⟨es, es.continuous⟩ : C(_, _))))
      ((singularChainsFunctor R).map (TopCat.ofHom f)) (by
        simp only [singularSubspaceChains, ← CategoryTheory.Functor.map_comp]
        rfl))
    infer_instance
  let q := relativeSingularCohomologyPullback R f hf n
  have : IsIso q := by
    change IsIso ((singularCochainDualFunctor R ⋙
      HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map
        (relativeSingularChainsMap R f hf).op)
    infer_instance
  have hq : Function.Bijective q := (ConcreteCategory.isIso_iff_bijective q).mp inferInstance
  have hsquare (a : compactSupportCohomology R Y n) :
      compactSupportCohomologyToOnePoint R V n (p a) =
        q (compactSupportCohomologyToOnePoint R Y n a) :=
    compactSupportCohomologyHomeomorphPullback_toOnePoint R e n a
  -- Transport bijectivity through this actual comparison square.
  constructor
  · intro a b hab
    apply hp.injective
    apply hnative.injective
    exact (hsquare a).trans ((congrArg q hab).trans (hsquare b).symm)
  · intro b
    obtain ⟨x, hx⟩ := hnative.surjective (q b)
    obtain ⟨a, ha⟩ := hp.surjective x
    refine ⟨a, hq.injective ?_⟩
    exact (hsquare a).symm.trans ((congrArg _ ha).trans hx)


/-- The one-point equivalence whose forward map is the original Unit-total colimit comparison. -/
def compactSupportCohomologyOnePointEquiv
    (R : Type) [CommRing R] (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (n : ℕ) :
    compactSupportCohomology R (TotalSpace Unit E) n ≃ₗ[R]
      relativeSingularCohomology R ({∞} : Set (OnePoint (TotalSpace Unit E))) n :=
  LinearEquiv.ofBijective
    (compactSupportCohomologyToOnePoint R (TotalSpace Unit E) n).hom
    (h.compactSupportCohomologyToOnePoint_bijective R r hr n)

/-- The supported character of the original reduced K class on the original complex total space. -/
def compactSupportChernCharacterComponent
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (k : ℕ) :
    CompactSupportKZero (TotalSpace Unit E) →+
      compactSupportCohomology ℚ (TotalSpace Unit E) (2 * k) :=
  (h.compactSupportCohomologyOnePointEquiv ℚ r hr (2 * k)).symm.toAddMonoidHom.comp
    (reducedChernCharacterComponent (∞ : OnePoint (TotalSpace Unit E)) k)

/-- The original comparison sends this supported character to the same point-relative character. -/
theorem compactSupportChernCharacterComponent_toOnePoint
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (k : ℕ)
    (a : CompactSupportKZero (TotalSpace Unit E)) :
    compactSupportCohomologyToOnePoint ℚ (TotalSpace Unit E) (2 * k)
        (h.compactSupportChernCharacterComponent r hr k a) =
      reducedChernCharacterComponent (∞ : OnePoint (TotalSpace Unit E)) k a := by
  /- The defining character applies the inverse of this exact comparison
  to the original reduced character. Applying its forward map cancels
  the inverse by apply_symm_apply. The reduced class, singleton infinity,
  original total topology and degree are the same on both sides. -/
  exact (h.compactSupportCohomologyOnePointEquiv ℚ r hr (2 * k)).apply_symm_apply
    (reducedChernCharacterComponent (∞ : OnePoint (TotalSpace Unit E)) k a)

/-- Forgetting support recovers the ordinary restriction of the same absolute character. -/
theorem compactSupportChernCharacterComponent_toOrdinary
    (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r) (k : ℕ)
    (a : CompactSupportKZero (TotalSpace Unit E)) :
    compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * k)
        (h.compactSupportChernCharacterComponent r hr k a) =
      singularCohomologyPullback ℚ
        ⟨((↑) : TotalSpace Unit E → OnePoint (TotalSpace Unit E)), OnePoint.continuous_coe⟩
        (2 * k) (chernCharacterKZeroComponent (OnePoint (TotalSpace Unit E)) k a.val) := by
  /- First apply compactSupportCohomologyToOnePoint_toOrdinary to this
  actual supported class. The preceding comparison identifies its image
  with the original reduced character of a. Then the original
  reducedChernCharacterComponent_toOrdinary theorem identifies its
  point-relative-to-ordinary image with the same absolute character.
  Pullback uses the actual inclusion of the original Unit-model total
  space into its own one-point compactification throughout. -/
  rw [← compactSupportCohomologyToOnePoint_toOrdinary ℚ (TotalSpace Unit E) (2 * k),
    h.compactSupportChernCharacterComponent_toOnePoint,
    reducedChernCharacterComponent_toOrdinary]

end ContinuousHermitianMetric

end AtiyahSinger.ComplexBundle
