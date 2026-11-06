/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTrivial

/-!
# Assembly of the topological Serre-Swan correspondence

Public module ID: M2117.

D07/K01/KB01. On compact Hausdorff bases, full faithfulness is assembled for
actual continuous bundle maps and section-module maps. Choices are made from
separately stated existence theorems and retain their evaluation characterizations.
This is the morphism/object correspondence, not a new categorical equivalence definition.
Sources: KA I.6 and Wikipedia Serre-Swan, Topology (fixed snapshot).
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

attribute [local instance] sectionModule

variable [IsFiniteRank E] [IsFiniteRank F] [hC : CompactSpace X] [hT : T2Space X]

include hC hT

/-- Serre-Swan fullness with an actual continuous bundle map. -/
theorem existsUnique_hom_of_sectionMap
    (a : continuousSections E →ₗ[C(X, ℂ)] continuousSections F) :
    ∃! f : Hom E F, f.sectionMap = a := by
  /- Use the existing unique family of continuous linear fiber maps inducing a.
  Bundle that family with its total continuity certificate. Section extensionality
  identifies the induced module map with a; faithfulness proves uniqueness. -/
  -- Bundle the continuous fiber maps furnished by the original fullness theorem.
  obtain ⟨τ, hτ, _⟩ := existsUnique_bundleMap_of_sectionMap E F a
  let f : Hom E F := ⟨τ, hτ.1⟩
  have hf : f.sectionMap = a := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    funext x
    exact hτ.2 s x
  refine ⟨f, hf, ?_⟩
  -- Faithfulness compares the prescribed section actions, not unrelated choices.
  intro g hg
  exact Hom.sectionMap_injective (hg.trans hf.symm)

/-- The bundle map determined by the given section-module map. -/
def homOfSectionMap (a : continuousSections E →ₗ[C(X, ℂ)] continuousSections F) : Hom E F :=
  (existsUnique_hom_of_sectionMap a).exists.choose

/-- The recovered bundle map induces the specified section map. -/
theorem homOfSectionMap_sectionMap
    (a : continuousSections E →ₗ[C(X, ℂ)] continuousSections F) :
    (homOfSectionMap a).sectionMap = a := by
  /- Take the existence part of the uniqueness theorem used in homOfSectionMap.
  Its defining predicate is precisely equality with the given section-module map. -/
  exact (existsUnique_hom_of_sectionMap a).exists.choose_spec

/-- Recovery of a bundle map from its action on sections. -/
theorem homOfSectionMap_eq (f : Hom E F) : homOfSectionMap f.sectionMap = f := by
  /- The recovered map and f induce the same section map by the defining property
  of the construction. Apply faithfulness of the section functor on a compact Hausdorff base. -/
  exact Hom.sectionMap_injective (homOfSectionMap_sectionMap f.sectionMap)

/-- Recovery acts on fiber values exactly as the given module map. -/
theorem homOfSectionMap_apply
    (a : continuousSections E →ₗ[C(X, ℂ)] continuousSections F)
    (s : continuousSections E) (x : X) :
    (homOfSectionMap a).linearMap x (s.val x) = (a s).val x := by
  /- Evaluate the equality of induced section maps on s and then at x. The section
  map evaluation formula gives the desired identity on values in the original fibers. -/
  exact congrArg (fun b : continuousSections E →ₗ[C(X, ℂ)] continuousSections F ↦
    (b s).val x) (homOfSectionMap_sectionMap a)

/-- The section functor is bijective on these actual morphism sets. -/
theorem sectionMap_bijective :
    Function.Bijective (fun f : Hom E F ↦ f.sectionMap) := by
  /- Injectivity is the faithfulness theorem. For a prescribed module map, the
  recovered bundle map supplies a preimage by its section-map characterization. -/
  refine ⟨Hom.sectionMap_injective, ?_⟩
  intro a
  exact ⟨homOfSectionMap a, homOfSectionMap_sectionMap a⟩

/-- The full-faithfulness equivalence with forward map given by taking sections. -/
def sectionMapEquiv : Hom E F ≃ (continuousSections E →ₗ[C(X, ℂ)] continuousSections F) :=
  Equiv.ofBijective (fun f ↦ f.sectionMap) sectionMap_bijective

/-- An isomorphism of section modules lifts to a specified bundle isomorphism. -/
theorem exists_iso_of_sectionEquiv
    (a : continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F) :
    ∃ e : Iso E F, e.toHom.sectionMap = a.toLinearMap := by
  /- Recover continuous bundle maps from a and its inverse. Their composites
  induce identity section maps, hence are identity bundle maps by faithfulness.
  These actual inverse maps give a fiber equivalence with both directions continuous. -/
  -- Recover both directions using the same prescribed module equivalence.
  let f : Hom E F := homOfSectionMap a.toLinearMap
  let g : Hom F E := homOfSectionMap a.symm.toLinearMap
  have hgf : g.comp f = Hom.id E := by
    apply Hom.sectionMap_injective
    change (g.comp f).sectionMap = (Hom.id E).sectionMap
    rw [Hom.sectionMap_comp, Hom.sectionMap_id]
    change (homOfSectionMap a.symm.toLinearMap).sectionMap.comp
      (homOfSectionMap a.toLinearMap).sectionMap = LinearMap.id
    rw [homOfSectionMap_sectionMap, homOfSectionMap_sectionMap]
    exact a.symm_comp
  have hfg : f.comp g = Hom.id F := by
    apply Hom.sectionMap_injective
    change (f.comp g).sectionMap = (Hom.id F).sectionMap
    rw [Hom.sectionMap_comp, Hom.sectionMap_id]
    change (homOfSectionMap a.toLinearMap).sectionMap.comp
      (homOfSectionMap a.symm.toLinearMap).sectionMap = LinearMap.id
    rw [homOfSectionMap_sectionMap, homOfSectionMap_sectionMap]
    exact a.comp_symm
  -- The two actual continuous maps supply the fiber equivalence and its inverse.
  let e : Iso E F :=
    { linearEquiv := fun x ↦
        { toLinearMap := f.linearMap x
          invFun := g.linearMap x
          left_inv := fun v ↦ congrArg (fun b : Hom E E ↦ b.linearMap x v) hgf
          right_inv := fun v ↦ congrArg (fun b : Hom F F ↦ b.linearMap x v) hfg }
      continuous_total := f.continuous_total
      continuous_symm := g.continuous_total }
  exact ⟨e, homOfSectionMap_sectionMap a.toLinearMap⟩

/-- The bundle isomorphism realizing the prescribed section-module equivalence. -/
def isoOfSectionEquiv
    (a : continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F) : Iso E F :=
  (exists_iso_of_sectionEquiv a).choose

/-- The recovered bundle isomorphism induces the chosen module equivalence. -/
theorem isoOfSectionEquiv_sectionMap
    (a : continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F) :
    (isoOfSectionEquiv a).toHom.sectionMap = a.toLinearMap := by
  /- This is the predicate in the existence theorem from which the isomorphism
  was chosen. It fixes the forward map and prevents substitution of an unrelated isomorphism. -/
  exact (exists_iso_of_sectionEquiv a).choose_spec

/-- The recovered isomorphism respects evaluation on the actual fibers. -/
theorem isoOfSectionEquiv_apply
    (a : continuousSections E ≃ₗ[C(X, ℂ)] continuousSections F)
    (s : continuousSections E) (x : X) :
    (isoOfSectionEquiv a).linearEquiv x (s.val x) = (a s).val x := by
  /- Evaluate the characterized equality of section maps at s and x. Both the
  section functor and the underlying forward map of a linear equivalence preserve these values. -/
  exact congrArg (fun b : continuousSections E →ₗ[C(X, ℂ)] continuousSections F ↦
    (b s).val x) (isoOfSectionEquiv_sectionMap a)

end AtiyahSinger.ComplexBundle

namespace AtiyahSinger.IdempotentMatrix

open Bundle

variable {X : Type*} [TopologicalSpace X] (p : IdempotentMatrix C(X, ℂ))

attribute [local instance] fiberTotalSpaceTopology isFiniteRank_fiber
attribute [local instance] ComplexBundle.sectionModule

/-- An image-module/section equivalence supplied by the separately proved image theorem. -/
def imageSectionEquiv :
    p.image ≃ₗ[C(X, ℂ)] ComplexBundle.continuousSections (fun x ↦ p.fiber x) :=
  Classical.choice p.nonempty_image_equiv_continuousSections

end AtiyahSinger.IdempotentMatrix

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [hE : IsFiniteRank E] [hC : CompactSpace X] [hT : T2Space X]

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
attribute [local instance] IdempotentMatrix.isFiniteRank_fiber sectionModule

include hE hC hT

/-- Every finite-rank bundle on a compact Hausdorff base has an actual image presentation. -/
theorem exists_idempotent_presentation :
    ∃ p : IdempotentMatrix C(X, ℂ), Nonempty (Iso E (fun x ↦ p.fiber x)) := by
  /- The section module is finite projective, hence the image of a finite idempotent.
  Identify that image with the sections of its image bundle. The resulting section
  equivalence lifts through full faithfulness to an actual bundle isomorphism. -/
  -- Keep one algebraic presentation through the image-bundle and section identifications.
  let := finite_continuousSections E
  let := projective_continuousSections E
  obtain ⟨p, ⟨e⟩⟩ := exists_idempotentMatrix_of_finite_projective C(X, ℂ)
    (continuousSections E)
  obtain ⟨f, _⟩ := exists_iso_of_sectionEquiv (e.symm.trans p.imageSectionEquiv)
  exact ⟨p, ⟨f⟩⟩

/-- A finite idempotent presenting the given geometric bundle. -/
def idempotentPresentation : IdempotentMatrix C(X, ℂ) :=
  (exists_idempotent_presentation (E := E)).choose

/-- An actual isomorphism from the geometric bundle to its chosen image presentation. -/
def presentationIso : Iso E (fun x ↦ (idempotentPresentation (E := E)).fiber x) :=
  Classical.choice (exists_idempotent_presentation (E := E)).choose_spec

/-- An actual bundle isomorphism identifies the associated section modules. -/
theorem presentation_sections :
    Nonempty (continuousSections E ≃ₗ[C(X, ℂ)]
      (idempotentPresentation (E := E)).image) := by
  /- Apply the section equivalence of presentationIso and then the inverse of the
  chosen image-module/section equivalence. This uses the same idempotent on both sides,
  not another independently chosen presentation of the section module. -/
  exact ⟨(presentationIso (E := E)).sectionLinearEquiv.trans
    (idempotentPresentation (E := E)).imageSectionEquiv.symm⟩

end AtiyahSinger.ComplexBundle
