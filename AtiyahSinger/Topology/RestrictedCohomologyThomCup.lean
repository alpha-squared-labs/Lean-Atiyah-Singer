/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GlobalCohomologyThomCup
public import AtiyahSinger.Topology.SimplexLocalHomology
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# The complete Thom cup comparison on a restricted total space

Public module ID: M2103.

The original total space over any subset is canonically homeomorphic to the
native pullback bundle. This identification preserves its fibers and its
specified relative cocycle. Right-cup naturality transports the full cochain
quasi-isomorphism, including every degree below the bundle rank.

Source: naturality of relative cup and the pullback-bundle Thom theorem,
Hatcher, Algebraic Topology, Sections 3.2 and 4.D.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits HomologicalComplex Opposite

universe u

variable (R : Type) [CommRing R]

private def restrictedThomMapCocycle {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (c : (C.sc n).moduleCatLeftHomologyData.K) :
    (D.sc n).moduleCatLeftHomologyData.K :=
  ⟨F.f n c.val, by
    change D.dFrom n (F.f n c.val) = 0
    have h := congrArg (fun f ↦ f c.val) (F.comm_from n)
    change D.dFrom n (F.f n c.val) = F.next n (C.dFrom n c.val) at h
    have hc : C.dFrom n c.val = 0 := c.property
    rw [h, hc, map_zero]⟩

variable {X : Type u} [TopologicalSpace X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem restrictedThomCup_natural {Y : Type u} [TopologicalSpace Y]
    (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : Set.MapsTo f A B)
    (r : ℕ) (c : relativeSingularCocycles R B r) :
    extendMap ((singularCochainsFunctor R).map (TopCat.ofHom f).op)
        (ComplexShape.embeddingUp'Add (1 : ℕ) r) ≫
      relativeSingularCochainCupMap R A r
        (restrictedThomMapCocycle R ((singularCochainDualFunctor R).map
          (relativeSingularChainsMap R f hf).op) r c) =
      relativeSingularCochainCupMap R B r c ≫
        (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op := by
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : r ≤ n
  · obtain ⟨p, rfl⟩ : ∃ p, n = p + r := ⟨n - r, (Nat.sub_add_cancel hn).symm⟩
    simp only [HomologicalComplex.comp_f, relativeSingularCochainCupMap_f]
    rw [extendMap_f _ e (i := p) (i' := p + r) rfl]
    change (((singularCochains R Y).extendXIso e (i := p) rfl).hom ≫
      ((singularCochainsFunctor R).map (TopCat.ofHom f).op).f p ≫
      ((singularCochains R X).extendXIso e (i := p) rfl).inv) ≫
        ((singularCochains R X).extendXIso e (i := p) rfl).hom ≫ _ = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    ext a
    exact (relativeSingularCochainAction_natural R f A B hf p r
      (((singularCochains R Y).extendXIso e (i := p) rfl).hom a) c.val).symm
  · have hz := (singularCochains R Y).isZero_extend_X e n (by
      intro p hp
      change p + r = n at hp
      omega)
    exact hz.eq_of_src _ _

variable (r : ℕ) (E : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A fiberwise generator on any restricted total space gives the full actual cup comparison. -/
theorem relativeSingularCochainCupMap_bijective_of_bundleTotalOver_generator
    (S : Set X) (c : relativeSingularCocycles R (bundleNonzeroOver r E S) r)
    (hgen : ∀ (x : X) (hx : x ∈ S), Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E S x hx)
        (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E S) (fun _ hv ↦ hv) r
        (relativeSingularCocycleClass R (bundleNonzeroOver r E S) r c)))
    (n : ℕ) : Function.Bijective
      (homologyMap (relativeSingularCochainCupMap R (bundleNonzeroOver r E S) r c) n) := by
  let F := EuclideanSpace ℝ (Fin r)
  let j := ContinuousMap.subtypeVal S
  let E' := (j : S → X) *ᵖ E
  let : ∀ x : S, NormedAddCommGroup (E' x) :=
    fun x ↦ (inferInstance : NormedAddCommGroup (E x.val))
  let : ∀ x : S, NormedSpace ℝ (E' x) :=
    fun x ↦ (inferInstance : NormedSpace ℝ (E x.val))
  let : FiberBundle F E' := FiberBundle.pullback (F := F) (E := E) j
  let : VectorBundle ℝ F E' := VectorBundle.pullback (𝕜 := ℝ) (F := F) (E := E) j
  let Y := TotalSpace F E'
  let V := BundleTotalOver r E S
  let A := bundleNonzero r E'
  let B := bundleNonzeroOver r E S
  -- The native pullback topology gives the evident inverse maps over the same base points.
  let f : C(Y, V) :=
    ⟨fun y ↦ ⟨⟨y.proj.val, y.snd⟩, y.proj.property⟩,
      (Pullback.continuous_lift F E j).subtype_mk _⟩
  let g : C(V, Y) :=
    ⟨fun y ↦ ⟨⟨y.val.proj, y.property⟩, y.val.snd⟩, by
      rw [(inducing_pullbackTotalSpaceEmbedding F E (j : S → X)).continuous_iff]
      exact (((bundleProjection r E).continuous.comp continuous_subtype_val).subtype_mk _)
        |>.prodMk continuous_subtype_val⟩
  have hgf : g.comp f = ContinuousMap.id Y := by
    apply ContinuousMap.ext
    rintro ⟨⟨x, hx⟩, v⟩
    rfl
  have hfg : f.comp g = ContinuousMap.id V := by
    apply ContinuousMap.ext
    rintro ⟨⟨x, v⟩, hx⟩
    rfl
  have hf : Set.MapsTo f A B := fun _ hv ↦ hv
  have hg : Set.MapsTo g B A := fun _ hv ↦ hv
  let P := (singularCochainDualFunctor R).map (relativeSingularChainsMap R f hf).op
  let c' : relativeSingularCocycles R A r := restrictedThomMapCocycle R P r c
  have hgen' (x : S) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusion r E' x)
        (A := {v : E' x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r
        (relativeSingularCocycleClass R A r c')) := by
    have hclass := homologyMap_cycleClass R _ _ P r c
      (restrictedThomMapCocycle R P r c) rfl
    change relativeSingularCohomologyPullback R f hf r
      (relativeSingularCocycleClass R B r c) = relativeSingularCocycleClass R A r c' at hclass
    rw [← hclass]
    simp only [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    exact hgen x.val x.property
  have hglobal := relativeSingularCochainCupMap_bijective_of_bundle_generator R r E' c' hgen' n
  let eTop : TopCat.of Y ≅ TopCat.of V :=
    { hom := TopCat.ofHom f
      inv := TopCat.ofHom g
      hom_inv_id := congrArg TopCat.ofHom hgf
      inv_hom_id := congrArg TopCat.ofHom hfg }
  let Q := (singularCochainsFunctor R).map (TopCat.ofHom f).op
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  have hfTop : IsIso (TopCat.ofHom f) :=
    ⟨TopCat.ofHom g, eTop.hom_inv_id, eTop.inv_hom_id⟩
  have hQ : IsIso Q := by
    dsimp only [Q]
    infer_instance
  have hQe : IsIso (extendMap Q e) := by
    change IsIso ((e.extendFunctor (ModuleCat.{u} R)).map Q)
    infer_instance
  have hP : IsIso (homologyMap P n) :=
    isIso_relativeSingularCohomologyPullback_of_inverse R f g hf hg hgf hfg n
  have hPb := ConcreteCategory.bijective_of_isIso (homologyMap P n)
  have hsquare := restrictedThomCup_natural R f A B hf r c
  have hcomp : Function.Bijective
      ((homologyMap P n) ∘ homologyMap (relativeSingularCochainCupMap R B r c) n) := by
    change Function.Bijective
      (homologyMap (relativeSingularCochainCupMap R B r c) n ≫ homologyMap P n)
    rw [← homologyMap_comp, ← hsquare, homologyMap_comp]
    exact hglobal.comp (ConcreteCategory.bijective_of_isIso (homologyMap (extendMap Q e) n))
  -- Cancel the genuine pullback isomorphism in the natural square, retaining the original cup map.
  exact ⟨fun x y h ↦ hcomp.injective (congrArg (homologyMap P n) h), fun y ↦ by
    obtain ⟨x, hx⟩ := hcomp.surjective (homologyMap P n y)
    exact ⟨x, hPb.injective hx⟩⟩

end AtiyahSinger
