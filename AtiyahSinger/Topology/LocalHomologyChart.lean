/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeSingularOpenExcision
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# Local homology transported through the original chart maps

Public module ID: M1938.

The map from an open neighborhood into its ambient space induces an
isomorphism on local relative singular homology. Its inverse is the inverse
of that actual inclusion map, certified by excision. A partial homeomorphism
then transports local homology by the source inclusion inverse, the original
source-to-target homeomorphism, and the target inclusion, in that order.
No unspecified local homology isomorphism or generator is supplied as data.

The positive Euclidean local class is the translation of the existing
realOrientationCycle of the standard ordered basis. In dimension zero this
is the positive point class. These constructions fix the sign needed when
an atlas is used to specify a homological orientation.

Sources: Hatcher, Algebraic Topology, section 2.1 (excision) and section 3.3
(local orientations). The explicit relative maps and translated affine
simplex normalization are project implementations of those constructions.
The original homology map API uses one common universe for source and target;
the chart comparison below preserves that scope.
Both comparison maps are certified below and define the chart equivalence
with these prescribed forward maps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

set_option linter.unusedVariables false in
/-- The original homeomorphism of punctured pairs induces an isomorphism on local homology. -/
theorem relativeSingularHomologyMap_homeomorph_bijective
    (e : X ≃ₜ Y) (x : X) (k : ℕ) :
    Function.Bijective (relativeSingularHomologyMap ℤ
      (⟨e, e.continuous⟩ : C(X, Y))
      (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set Y))
      (fun y hy h ↦ hy (e.injective h)) k) := by
  /- Stage 1: the given homeomorphism sends exactly x to e x, so its forward
  and inverse maps restrict to the original punctured subspaces. Apply the
  original relative singular-chain functor to these two maps of pairs.
  Stage 2: their composites are the identity pair maps. Functoriality on
  homology therefore makes the two induced maps mutual inverses. This uses
  the actual specified maps, without a choice of generators or rescaling. -/
  let es : ↥({x}ᶜ : Set X) ≃ₜ ↥({e x}ᶜ : Set Y) :=
    e.subtype (fun _y ↦ by simp only [Set.mem_compl_iff, Set.mem_singleton_iff, e.injective.eq_iff])
  -- The original map is an isomorphism both on the ambient spaces and punctured subspaces.
  have : CategoryTheory.IsIso (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y))) := by
    change CategoryTheory.IsIso (TopCat.isoOfHomeo (X := TopCat.of X) (Y := TopCat.of Y) e).hom
    infer_instance
  have : CategoryTheory.IsIso (TopCat.ofHom (⟨es, es.continuous⟩ :
      C(↥({x}ᶜ : Set X), ↥({e x}ᶜ : Set Y)))) := by
    change CategoryTheory.IsIso (TopCat.isoOfHomeo
      (X := TopCat.of ↥({x}ᶜ : Set X)) (Y := TopCat.of ↥({e x}ᶜ : Set Y)) es).hom
    infer_instance
  have : CategoryTheory.IsIso ((singularChainsFunctor ℤ).map
      (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) := inferInstance
  have : CategoryTheory.IsIso ((singularChainsFunctor ℤ).map (TopCat.ofHom
      (⟨es, es.continuous⟩ : C(↥({x}ᶜ : Set X), ↥({e x}ᶜ : Set Y))))) := inferInstance
  -- Cokernel functoriality preserves this specified square of isomorphisms.
  have : CategoryTheory.IsIso (relativeSingularChainsMap ℤ
      (⟨e, e.continuous⟩ : C(X, Y))
      (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set Y))
      (fun y hy h ↦ hy (e.injective h))) := by
    change CategoryTheory.IsIso (CategoryTheory.Limits.cokernel.map _ _
      ((singularChainsFunctor ℤ).map (TopCat.ofHom (⟨es, es.continuous⟩ :
        C(↥({x}ᶜ : Set X), ↥({e x}ᶜ : Set Y)))))
      ((singularChainsFunctor ℤ).map (TopCat.ofHom (⟨e, e.continuous⟩ : C(X, Y)))) (by
        simp only [singularSubspaceChains, ← CategoryTheory.Functor.map_comp]
        rfl))
    infer_instance
  -- Homology preserves the same chain isomorphism, in every degree including zero.
  have : CategoryTheory.IsIso (relativeSingularHomologyMap ℤ
      (⟨e, e.continuous⟩ : C(X, Y))
      (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set Y))
      (fun y hy h ↦ hy (e.injective h)) k) := by
    change CategoryTheory.IsIso
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) k).map
        (relativeSingularChainsMap ℤ (⟨e, e.continuous⟩ : C(X, Y))
          (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set Y))
          (fun y hy h ↦ hy (e.injective h))))
    infer_instance
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The local homology equivalence whose forward map is the original map of punctured pairs. -/
def localHomologyHomeomorphEquiv (e : X ≃ₜ Y) (x : X) (k : ℕ) :
    relativeSingularHomology ℤ ({x}ᶜ : Set X) k ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({e x}ᶜ : Set Y) k :=
  LinearEquiv.ofBijective
    (relativeSingularHomologyMap ℤ (⟨e, e.continuous⟩ : C(X, Y))
      (A := ({x}ᶜ : Set X)) (B := ({e x}ᶜ : Set Y))
      (fun _y hy h ↦ hy (e.injective h)) k).hom
    (relativeSingularHomologyMap_homeomorph_bijective e x k)

set_option linter.unusedVariables false in
/-- Excision makes the original open-neighborhood inclusion bijective on local homology. -/
theorem relativeSingularHomologyMap_openInclusion_bijective [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) (k : ℕ) :
    Function.Bijective (relativeSingularHomologyMap ℤ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
      (A := ({x}ᶜ : Set U)) (B := ({x.val}ᶜ : Set X))
      (fun y hy h ↦ hy (Subtype.ext h)) k) := by
  /- Stage 1: the closure of X \ U is X \ U, since U is open. It lies
  in the open punctured space X \ {x}, because x belongs to U and the
  singleton is closed in the Hausdorff ambient space. These are the actual
  hypotheses of singular excision for the pair (X,X \ {x}).
  Stage 2: excising X \ U leaves precisely (U,U \ {x}). The excision map
  is induced by the displayed subtype inclusion on the original chain
  quotients, hence gives exactly this homology map. The result includes
  degree zero and does not require connectedness or compactness of U. -/
  let f : C(U, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : Topology.IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal
  have hRange : ({x.val} : Set X) ⊆ Set.range f := by
    rintro _ rfl
    exact ⟨x, rfl⟩
  have hPre : f ⁻¹' ({x.val} : Set X) = ({x} : Set U) := by
    ext y
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  have hexc {A : Set U} (hA : A = (f ⁻¹' ({x.val} : Set X))ᶜ)
      (h : Set.MapsTo f A ({x.val}ᶜ : Set X)) :
      HomologicalComplex.homotopyEquivalences (ModuleCat.{u} ℤ) (ComplexShape.down ℕ)
        (relativeSingularChainsMap ℤ f h) := by
    subst A
    exact homotopyEquivalences_relativeSingularChainsMap_openEmbedding ℤ f hf
      {x.val} isClosed_singleton hRange
  obtain ⟨e, he⟩ := hexc (congrArg Set.compl hPre.symm)
    (fun y (hy : y ∈ ({x}ᶜ : Set U)) h ↦ hy (Subtype.ext h))
  have : CategoryTheory.IsIso (relativeSingularHomologyMap ℤ f
      (A := ({x}ᶜ : Set U)) (B := ({x.val}ᶜ : Set X))
      (fun _y hy h ↦ hy (Subtype.ext h)) k) := by
    change CategoryTheory.IsIso (HomologicalComplex.homologyMap _ k)
    erw [← he]
    change CategoryTheory.IsIso (e.toHomologyIso k).hom
    infer_instance
  exact (CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp inferInstance

/-- The inverse of this equivalence is the specified open-inclusion excision inverse. -/
def localHomologyOpenInclusionEquiv [T2Space X]
    (U : Set X) (hU : IsOpen U) (x : U) (k : ℕ) :
    relativeSingularHomology ℤ ({x}ᶜ : Set U) k ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({x.val}ᶜ : Set X) k :=
  LinearEquiv.ofBijective
    (relativeSingularHomologyMap ℤ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X))
      (A := ({x}ᶜ : Set U)) (B := ({x.val}ᶜ : Set X))
      (fun _y hy h ↦ hy (Subtype.ext h)) k).hom
    (relativeSingularHomologyMap_openInclusion_bijective U hU x k)

/-- Local chart transport through the actual source inclusion, chart, and target inclusion. -/
def localHomologyChartEquiv [T2Space X] [T2Space Y]
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source) (k : ℕ) :
    relativeSingularHomology ℤ ({x}ᶜ : Set X) k ≃ₗ[ℤ]
      relativeSingularHomology ℤ ({e x}ᶜ : Set Y) k :=
  ((localHomologyOpenInclusionEquiv e.source e.open_source ⟨x, hx⟩ k).symm.trans
    (localHomologyHomeomorphEquiv e.toHomeomorphSourceTarget ⟨x, hx⟩ k)).trans
      (localHomologyOpenInclusionEquiv e.target e.open_target
        (e.toHomeomorphSourceTarget ⟨x, hx⟩) k)

/-- The positive local Euclidean class is the translated standard affine-simplex class. -/
def euclideanLocalOrientationCycle (r : ℕ) (a : EuclideanSpace ℝ (Fin r)) :
    relativeSingularHomology ℤ ({a}ᶜ : Set (EuclideanSpace ℝ (Fin r))) r :=
  relativeSingularHomologyMap ℤ
    (⟨fun v ↦ a + v, continuous_const.add continuous_id⟩ :
      C(EuclideanSpace ℝ (Fin r), EuclideanSpace ℝ (Fin r)))
    (A := (Set.ofPred (fun v : EuclideanSpace ℝ (Fin r) ↦ v ≠ 0)))
    (B := ({a}ᶜ : Set (EuclideanSpace ℝ (Fin r))))
    (fun _v hv h ↦ hv (add_left_cancel (h.trans (add_zero a).symm))) r
    (realOrientationCycle (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.orientation)

end AtiyahSinger
