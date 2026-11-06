/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GlobalCohomologyThomCup
public import AtiyahSinger.Topology.RelativeCohomologySequence

/-!
# Detecting low-degree base classes on the punctured bundle

Public module ID: M1571.

For an oriented real bundle of rank r, projection from its nonzero vectors
detects base cohomology below degree r. The original complete Thom cochain
comparison makes relative cohomology vanish in those degrees. Exactness of
the actual relative cochain sequence then gives injective restriction, and
the original zero section gives a left inverse to projection pullback.

This is the low-degree part of the Thom--Gysin argument in Milnor--Stasheff,
section 9, and Hatcher, Corollary 4D.9. The coefficient ring and base space
are arbitrary. The result is used to detect the original half-spin character
difference from its actual Clifford isomorphism off the zero section.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Projection from the original nonzero bundle detects cohomology below the oriented fiber rank. -/
theorem singularCohomologyPullback_nonzeroBundle_injective
    (o : CohomologyOrientation R r E) (k : ℕ) (hk : k < r) :
    Function.Injective (singularCohomologyPullback R
      ((bundleProjection r E).comp (ContinuousMap.subtypeVal (bundleNonzero r E))) k) := by
  let T := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let A := bundleNonzero r E
  let t := cohomologyThomClass R r E o
  -- A cocycle of the same normalized Thom class supplies the complete shifted comparison.
  obtain ⟨c, hc⟩ := (relativeSingularCoboundaries R A r).mkQ_surjective
    (((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom t)
  have hct : relativeSingularCocycleClass R A r c = t := by
    change ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.inv
      ((relativeSingularCoboundaries R A r).mkQ c) = t
    rw [hc]
    exact Iso.hom_inv_id_apply _ t
  have hgen (x : X) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
        (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r
        (relativeSingularCocycleClass R A r c)) := by
    have ht : relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
        (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r t = o.fiberClass x :=
      (existsUnique_cohomologyThomClass R r E o).exists.choose_spec x
    rw [hct, ht]
    exact o.is_generator x
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  let : Subsingleton (((singularCochains R T).extend e).homology k) := by
    apply ModuleCat.isZero_iff_subsingleton.mp
    apply (exactAt_iff_isZero_homology _ _).mp
    exact extend_exactAt _ e k (by
      intro p hp
      change p + r = k at hp
      omega)
  have hrel : Subsingleton (relativeSingularCohomology R A k) := by
    have hbij := relativeSingularCochainCupMap_bijective_of_bundle_generator R r E c hgen k
    exact hbij.surjective.subsingleton
  -- Exactness of the original relative sequence turns this vanishing into injective restriction.
  let S := singularSubspaceCochainsSequence R A
  let : Subsingleton (S.X₁.homology k) := hrel
  have hf : homologyMap S.f k = 0 := by
    apply ModuleCat.hom_ext
    ext a
    rw [Subsingleton.elim a 0, map_zero]
    rfl
  have hg : Mono (homologyMap S.g k) :=
    ((shortExact_singularSubspaceCochains R A).homology_exact₂ k).mono_g hf
  have hrestriction : Function.Injective
      (singularCohomologyPullback R (ContinuousMap.subtypeVal A) k) :=
    (ModuleCat.mono_iff_injective (homologyMap S.g k)).mp hg
  -- Projection has its actual zero section as a left inverse on cohomology.
  intro a b hab
  have hcomp : singularCohomologyPullback R
      ((bundleProjection r E).comp (ContinuousMap.subtypeVal A)) k =
      singularCohomologyPullback R (bundleProjection r E) k ≫
        singularCohomologyPullback R (ContinuousMap.subtypeVal A) k :=
    (singularCohomologyFunctor R k).map_comp
      (TopCat.ofHom (bundleProjection r E)).op (TopCat.ofHom (ContinuousMap.subtypeVal A)).op
  rw [hcomp] at hab
  have hp := hrestriction hab
  have hz := congrArg (singularCohomologyPullback R (bundleZeroSection r E) k) hp
  have hid : singularCohomologyPullback R (bundleProjection r E) k ≫
      singularCohomologyPullback R (bundleZeroSection r E) k = 𝟙 _ := by
    let F := singularCohomologyFunctor R k
    change F.map (TopCat.ofHom (bundleProjection r E)).op ≫
      F.map (TopCat.ofHom (bundleZeroSection r E)).op = _
    rw [← F.map_comp, ← op_comp]
    exact F.map_id _
  change (singularCohomologyPullback R (bundleProjection r E) k ≫
    singularCohomologyPullback R (bundleZeroSection r E) k) a =
    (singularCohomologyPullback R (bundleProjection r E) k ≫
      singularCohomologyPullback R (bundleZeroSection r E) k) b at hz
  rw [hid] at hz
  exact hz

end AtiyahSinger
