/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.LocalCohomologyThom
public import AtiyahSinger.Topology.TrivialCohomologyThomCup

/-!
# The actual cup map on a trivialized bundle restriction

Public module ID: M1937.

A specified linear trivialization transports the given fiberwise generator to
the Euclidean product pair. Its actual pullback preserves the original ordered
cup product. The product projection is a homotopy equivalence, so the same cup
map is bijective on ordinary cohomology of the original restricted total space.

No openness, connectedness, compactness, or nonemptiness of the chosen subset is
required. The fiber inclusions and the chosen class are the original ones.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory HomologicalComplex Limits
open scoped unitInterval

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  (e : Trivialization (EuclideanSpace ℝ (Fin r)) (π (EuclideanSpace ℝ (Fin r)) E))
  [he : e.IsLinear ℝ] (V : Set X) (hV : V ⊆ e.baseSet)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include e hV he in
/-- Right cup with the given fiberwise generator is bijective on the original
restricted total space. -/
theorem relativeSingularCohomologyAction_bundleTotalOver_bijective
    (U : relativeSingularCohomology R (bundleNonzeroOver r E V) r)
    (hU : ∀ (x : X) (hx : x ∈ V), Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E V x hx)
        (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E V) (fun _ hv ↦ hv) r U))
    (p : ℕ) : Function.Bijective (fun a : singularCohomology R (BundleTotalOver r E V) p ↦
      relativeSingularCohomologyAction R (bundleNonzeroOver r E V) p r a U) := by
  let F := EuclideanSpace ℝ (Fin r)
  let Q : Set (V × F) := {z | z.2 ≠ 0}
  let H := e.preimageHomeomorph hV
  let f : C(BundleTotalOver r E V, V × F) := ⟨H, H.continuous⟩
  let g : C(V × F, BundleTotalOver r E V) := ⟨H.symm, H.symm.continuous⟩
  have hf : Set.MapsTo f (bundleNonzeroOver r E V) Q := by
    intro z hz
    let L := e.continuousLinearEquivAt ℝ z.val.proj (hV z.property)
    change L z.val.snd ≠ 0
    exact L.map_ne_zero_iff.mpr hz
  let iso (k : ℕ) := bundleTrivializationCohomologyIso R r E e V hV k
  have hiso (k : ℕ) : (iso k).hom = relativeSingularCohomologyPullback R f hf k := rfl
  let c := (iso r).inv U
  have hc : (iso r).hom c = U := Iso.inv_hom_id_apply _ _
  -- The specified native fiber and the model fiber are related by the same chart equivalence.
  have hpoint (x : V) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R
        ((ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id F))
        (A := {z | z.2 ≠ 0}) (B := Q) (fun _ hz ↦ hz) r c) := by
    let L := e.continuousLinearEquivAt ℝ x.val (hV x.property)
    let j := bundleFiberInclusionOver r E V x.val x.property
    let k : C(PUnit.{u + 1} × F, E x.val) :=
      ⟨fun z ↦ L.symm z.2, L.symm.continuous.comp continuous_snd⟩
    let l : C(E x.val, PUnit.{u + 1} × F) :=
      ⟨fun v ↦ (PUnit.unit, L v), continuous_const.prodMk L.continuous⟩
    have hk : Set.MapsTo k {z | z.2 ≠ 0} {v | v ≠ 0} :=
      fun _ hz ↦ L.symm.map_ne_zero_iff.mpr hz
    have hl : Set.MapsTo l {v | v ≠ 0} {z | z.2 ≠ 0} :=
      fun _ hz ↦ L.map_ne_zero_iff.mpr hz
    have hlk : l.comp k = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      exact Prod.ext (Subsingleton.elim _ _) (L.apply_symm_apply z.2)
    have hkl : k.comp l = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro v
      exact L.symm_apply_apply v
    let pk := relativeSingularCohomologyPullback R k hk r
    have : IsIso pk :=
      isIso_relativeSingularCohomologyPullback_of_inverse R k l hk hl hlk hkl r
    have hj : Set.MapsTo j {v | v ≠ 0} (bundleNonzeroOver r E V) := fun _ hz ↦ hz
    let t := (ContinuousMap.const PUnit.{u + 1} x).prodMap (ContinuousMap.id F)
    have ht : f.comp (j.comp k) = t := by
      apply ContinuousMap.ext
      intro z
      change H ⟨⟨x.val, L.symm z.2⟩, x.property⟩ = (x, z.2)
      apply Prod.ext
      · rw [e.preimageHomeomorph_apply hV]
      · exact L.apply_symm_apply z.2
    have hsquare : (iso r).hom ≫ relativeSingularCohomologyPullback R j hj r ≫ pk =
        relativeSingularCohomologyPullback R t
          (A := {z | z.2 ≠ 0}) (B := Q) (fun _ hz ↦ hz) r := by
      rw [hiso]
      dsimp only [pk]
      rw [← relativeSingularCohomologyPullback_comp, ← relativeSingularCohomologyPullback_comp]
      congr 1
    have hvalue := congrArg (fun a ↦ a c) hsquare
    change pk (relativeSingularCohomologyPullback R j hj r ((iso r).hom c)) =
      relativeSingularCohomologyPullback R t
        (A := {z | z.2 ≠ 0}) (B := Q) (fun _ hz ↦ hz) r c at hvalue
    rw [hc] at hvalue
    have hgen := (ConcreteCategory.bijective_of_isIso pk).comp (hU x.val x.property)
    have hformula (a : R) : pk (a • relativeSingularCohomologyPullback R j hj r U) =
        a • relativeSingularCohomologyPullback R t
          (A := {z | z.2 ≠ 0}) (B := Q) (fun _ hz ↦ hz) r c := by
      rw [map_smul, hvalue]
    exact (congrArg (fun f ↦ Function.Bijective f) (funext hformula)).mp hgen
  -- The zero section is a homotopy inverse to the projection, by fiberwise scaling.
  let π₀ : C(V × F, V) := ⟨Prod.fst, continuous_fst⟩
  let s : C(V, V × F) := ⟨fun x ↦ (x, 0), by fun_prop⟩
  have hsπ : (s.comp π₀).Homotopic (ContinuousMap.id (V × F)) := by
    refine ⟨{ toFun z := (z.2.1, (z.1 : ℝ) • z.2.2)
              continuous_toFun := by fun_prop
              map_zero_left := ?_
              map_one_left := ?_ }⟩
    · intro z
      simp [s, π₀]
    · intro z
      simp
  have hπs : (π₀.comp s).Homotopic (ContinuousMap.id V) := by
    have h : π₀.comp s = ContinuousMap.id V := rfl
    rw [h]
  have hπ : IsIso (singularCohomologyPullback R π₀ p) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R π₀ s hsπ hπs p
  let cupProd : singularCohomology R (V × F) p → relativeSingularCohomology R Q (p + r) :=
    fun a ↦ relativeSingularCohomologyAction R Q p r a c
  have hbase := relativeSingularCohomologyAction_prod_euclidean_bijective R V r c hpoint p
  have hprod : Function.Bijective cupProd :=
    (Function.Bijective.of_comp_iff cupProd
      (ConcreteCategory.isIso_iff_bijective _ |>.mp hπ)).mp hbase
  -- The native comparison is the same homeomorphism in ordinary and relative cohomology.
  have hgf : (g.comp f).Homotopic (ContinuousMap.id (BundleTotalOver r E V)) := by
    have h : g.comp f = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      exact H.symm_apply_apply z
    rw [h]
  have hfg : (f.comp g).Homotopic (ContinuousMap.id (V × F)) := by
    have h : f.comp g = ContinuousMap.id _ := by
      apply ContinuousMap.ext
      intro z
      exact H.apply_symm_apply z
    rw [h]
  have hordinary : IsIso (singularCohomologyPullback R f p) :=
    isIso_singularCohomologyPullback_of_homotopyInverse R f g hgf hfg p
  let cupNative : singularCohomology R (BundleTotalOver r E V) p →
      relativeSingularCohomology R (bundleNonzeroOver r E V) (p + r) :=
    fun a ↦ relativeSingularCohomologyAction R (bundleNonzeroOver r E V) p r a U
  have hformula (a : singularCohomology R (V × F) p) :
      (iso (p + r)).hom (cupProd a) = cupNative (singularCohomologyPullback R f p a) := by
    have h := relativeSingularCohomologyPullback_action R f hf p r a c
    rw [← hiso (p + r), ← hiso r, hc] at h
    exact h
  have hcomp : Function.Bijective (cupNative ∘ singularCohomologyPullback R f p) :=
    (congrArg (fun f ↦ Function.Bijective f) (funext hformula)).mp
      ((ConcreteCategory.bijective_of_isIso (iso (p + r)).hom).comp hprod)
  exact (Function.Bijective.of_comp_iff cupNative
    (ConcreteCategory.isIso_iff_bijective _ |>.mp hordinary)).mp hcomp

end AtiyahSinger
