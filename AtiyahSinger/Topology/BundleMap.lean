/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SerreSwan
public import Mathlib.Topology.UrysohnsLemma
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Continuous fiberwise linear bundle maps

Public module ID: M1589.

D07/K01. The maps preserve the base and use the actual total-space topology.
Finite local rank is needed for section modules, not for composition of maps.
Sources: the bundle morphisms in SG I.9 and topological Serre-Swan (KA I.6).
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

variable {X : Type*} [TopologicalSpace X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : X → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {G : X → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
  [TopologicalSpace (TotalSpace Unit G)]

/-- A continuous complex-linear bundle map over the identity of the base. -/
structure Hom (E F : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)] where
  /-- The complex-linear map on each actual fiber. -/
  linearMap : ∀ x, E x →ₗ[ℂ] F x
  /-- Continuity on total spaces; pointwise fiber continuity alone is insufficient. -/
  continuous_total : Continuous (fun z : TotalSpace Unit E ↦
    (⟨z.proj, linearMap z.proj z.snd⟩ : TotalSpace Unit F))

/-- The actual map on total spaces. -/
def Hom.totalMap (f : Hom E F) : TotalSpace Unit E → TotalSpace Unit F :=
  fun z ↦ ⟨z.proj, f.linearMap z.proj z.snd⟩


set_option linter.unusedSectionVars false in
/-- Bundle maps are determined by their fiber maps. -/
@[ext]
theorem Hom.ext (f g : Hom E F)
    (h : ∀ x, f.linearMap x = g.linearMap x) : f = g := by
  /- Apply function extensionality to the families of linear maps. The remaining
  continuity fields are proofs of propositions, hence agree by proof irrelevance. -/
  cases f
  cases g
  congr
  exact funext h

/-- The identity continuous bundle map. -/
def Hom.id (E : X → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] : Hom E E where
  linearMap _ := LinearMap.id
  continuous_total := continuous_id

/-- Composition uses ordinary composition on every fiber and on total spaces. -/
def Hom.comp (g : Hom F G) (f : Hom E F) : Hom E G where
  linearMap x := (g.linearMap x).comp (f.linearMap x)
  continuous_total := g.continuous_total.comp f.continuous_total

set_option linter.unusedSectionVars false in
/-- Composition evaluated on a fiber vector. -/
theorem Hom.comp_apply (g : Hom F G) (f : Hom E F) (x : X) (v : E x) :
    (g.comp f).linearMap x v = g.linearMap x (f.linearMap x v) := by
  /- Unfold composition of bundle maps and of linear maps. The source and target
  base points are both x, so the displayed application has no transport choices. -/
  rfl

set_option linter.unusedSectionVars false in
/-- Identity maps induce identity fiber functions. -/
theorem Hom.id_apply (x : X) (v : E x) : (Hom.id E).linearMap x v = v := by
  /- Unfold the identity bundle map. Its fiber map is the standard identity linear
  map, whose application to v returns the same vector in the same fiber. -/
  rfl

/-- Continuity of the base projection follows from local triviality. -/
theorem continuous_proj [IsFiniteRank E] : Continuous (π Unit E) := by
  /- In a local trivialization the bundle projection is the first product projection.
  The chart sources form an open cover of the total space; continuity is local on this cover. -/
  apply continuous_iff_continuousAt.mpr
  intro z
  obtain ⟨r, e, hz, _⟩ := IsFiniteRank.exists_linear_trivialization (E := E) z.proj
  exact e.continuousAt_proj (e.mem_source.mpr hz)

/-- Each fiber has finite algebraic dimension, without a chosen fiber topology. -/
theorem finite_fiber [IsFiniteRank E] (x : X) : Module.Finite ℂ (E x) := by
  /- Choose a finite-dimensional local trivialization at x. Its linear chart map
  injects the actual fiber into Fin r → ℂ. Transfer finite generation through
  that injection with Module.Finite.of_injective. -/
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  let f : E x →ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun v ↦ (e ⟨x, v⟩).2
      map_add' := (hlinear x hx).map_add
      map_smul' := (hlinear x hx).map_smul }
  -- The actual fiber embeds linearly into the chart's finite coordinate space.
  apply Module.Finite.of_injective f
  intro u v huv
  apply TotalSpace.mk_injective x
  apply e.injOn (e.mem_source.mpr hx) (e.mem_source.mpr hx)
  apply Prod.ext
  · exact (e.proj_toFun ⟨x, u⟩ (e.mem_source.mpr hx)).trans
      (e.proj_toFun ⟨x, v⟩ (e.mem_source.mpr hx)).symm
  · exact huv

attribute [local instance] sectionModule

variable [IsFiniteRank E] [IsFiniteRank F] [IsFiniteRank G]

set_option linter.unusedSectionVars false in
/-- Applying a continuous bundle map to a continuous section preserves continuity. -/
theorem Hom.continuous_section (f : Hom E F) (s : continuousSections E) :
    Continuous (fun x ↦ (⟨x, f.linearMap x (s.val x)⟩ : TotalSpace Unit F)) := by
  /- Compose the total-space map of f with the continuous total-space section s.
  Since f preserves the base, the composite is precisely the displayed section. -/
  exact f.continuous_total.comp s.property

/-- The covariant map of C(X,ℂ)-modules induced on actual continuous sections. -/
def Hom.sectionMap (f : Hom E F) : continuousSections E →ₗ[C(X, ℂ)] continuousSections F where
  toFun s := ⟨fun x ↦ f.linearMap x (s.val x), f.continuous_section s⟩
  map_add' s t := by
    apply Subtype.ext
    funext x
    exact (f.linearMap x).map_add _ _
  map_smul' c s := by
    apply Subtype.ext
    funext x
    exact (f.linearMap x).map_smul (c x) _

/-- The section functor acts by the original fiber map. -/
theorem Hom.sectionMap_apply (f : Hom E F) (s : continuousSections E) (x : X) :
    (f.sectionMap s).val x = f.linearMap x (s.val x) := by
  /- The section map was defined by pointwise application of the fiber map.
  Forget its continuity certificate and evaluate the underlying dependent function at x. -/
  rfl

/-- The section functor preserves identity maps. -/
theorem Hom.sectionMap_id : (Hom.id E).sectionMap = LinearMap.id := by
  /- Apply linear-map extensionality to a section. Both resulting section values
  are definitionally equal, since the fiber map is the identity. -/
  apply LinearMap.ext
  intro s
  rfl

/-- The section functor preserves composition in its actual order. -/
theorem Hom.sectionMap_comp (g : Hom F G) (f : Hom E F) :
    (g.comp f).sectionMap = g.sectionMap.comp f.sectionMap := by
  /- Apply linear-map extensionality to a section. Both sides apply f and then g
  on each fiber, so the resulting section values are definitionally equal. -/
  apply LinearMap.ext
  intro s
  rfl

/-- On compact Hausdorff bases, every fiber vector is the value of a global section. -/
theorem exists_section_value [CompactSpace X] [T2Space X] (x : X) (v : E x) :
    ∃ s : continuousSections E, s.val x = v := by
  /- Choose a local frame around x and a continuous cutoff supported inside its base
  neighborhood and equal to one at x. Multiply the constant coordinate vector by
  that cutoff and extend by zero. Compact Hausdorff normality supplies the cutoff. -/
  classical
  obtain ⟨r, e, hx, hlinear⟩ := IsFiniteRank.exists_linear_trivialization (E := E) x
  obtain ⟨c, hc, _, hsupport, _⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen isCompact_singleton
      e.open_baseSet (Set.singleton_subset_iff.mpr hx)
  -- Retain the inverse of this same chart, with its necessary fiber transport.
  let eLin (y : X) (hy : y ∈ e.baseSet) : E y ≃ₗ[ℂ] (Fin r → ℂ) :=
    { toFun := fun u ↦ (e ⟨y, u⟩).2
      invFun := fun w ↦ cast (congrArg E (e.proj_symm_apply' hy))
        (e.toOpenPartialHomeomorph.symm (y, w)).2
      left_inv := by
        intro u
        rw [cast_eq_iff_heq]
        exact congr_arg_heq (fun z : TotalSpace Unit E ↦ z.2)
          (e.symm_apply_mk_proj (x := ⟨y, u⟩) (e.mem_source.mpr hy))
      right_inv := by
        intro w
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          (e.proj_symm_apply' (x := w) hy) (e.toOpenPartialHomeomorph.symm (y, w)).2
        exact (congrArg (fun z : TotalSpace Unit E ↦ (e z).2) hpoint).trans
          (congrArg Prod.snd (e.apply_symm_apply' hy))
      map_add' := (hlinear y hy).map_add
      map_smul' := (hlinear y hy).map_smul }
  let s : ∀ y, E y := fun y ↦
    if hy : y ∈ e.baseSet then (eLin y hy).symm ((c y : ℂ) • (eLin x hx v)) else 0
  have hs : Continuous (fun y ↦ (⟨y, s y⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    by_cases hy : y ∈ e.baseSet
    · -- Inside the chart, its coordinates are the continuous scalar cutoff times one vector.
      apply e.continuousAt_of_comp_left
        (f := fun z ↦ (⟨z, s z⟩ : TotalSpace Unit E)) continuousAt_id hy
      have hcoords : ContinuousAt (fun z ↦ (c z : ℂ) • (eLin x hx v)) y :=
        (Complex.continuous_ofReal.comp c.continuous).continuousAt.smul continuousAt_const
      apply (continuousAt_id.prodMk hcoords).congr_of_eventuallyEq
      filter_upwards [e.open_baseSet.mem_nhds hy] with z hz
      refine Prod.ext (e.proj_toFun ⟨z, s z⟩ (e.mem_source.mpr hz)) ?_
      change eLin z hz (s z) = _
      simp only [s, dite_eq_left hz, LinearEquiv.apply_symm_apply]
    · -- Outside the chart, closed support containment supplies a whole zero neighborhood.
      have hyc : y ∉ tsupport c := fun h ↦ hy (hsupport h)
      apply (continuous_zero_section E).continuousAt.congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport c).isOpen_compl.mem_nhds hyc] with z hz
      have hcz : c z = 0 := image_eq_zero_of_notMem_tsupport hz
      change (⟨z, s z⟩ : TotalSpace Unit E) = ⟨z, 0⟩
      congr 1
      simp only [s, hcz, Complex.ofReal_zero, zero_smul, map_zero, dite_eq_ite, ite_self]
  refine ⟨⟨s, hs⟩, ?_⟩
  have hcx : c x = 1 := hc (Set.mem_singleton x)
  change s x = v
  simp only [s, dite_eq_left hx, hcx, Complex.ofReal_one, one_smul,
    LinearEquiv.symm_apply_apply]

/-- On compact Hausdorff bases, the actual section functor is faithful. -/
theorem Hom.sectionMap_injective [CompactSpace X] [T2Space X] :
    Function.Injective (fun f : Hom E F ↦ f.sectionMap) := by
  /- Given equality of section maps, realize an arbitrary fiber vector by a global
  section and evaluate that equality at the chosen point. Thus all fiber maps agree;
  extensionality gives equality of the bundle maps. -/
  intro f g h
  apply Hom.ext
  intro x
  apply LinearMap.ext
  intro v
  obtain ⟨s, hs⟩ := exists_section_value (E := E) x v
  have hvalue := congrArg (fun Φ ↦ ((Φ : continuousSections E →ₗ[C(X, ℂ)]
    continuousSections F) s).val x) h
  change f.linearMap x (s.val x) = g.linearMap x (s.val x) at hvalue
  simpa only [hs] using hvalue

end AtiyahSinger.ComplexBundle
