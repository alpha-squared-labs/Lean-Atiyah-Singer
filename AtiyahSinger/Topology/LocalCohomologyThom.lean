/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CohomologyOrientation
public import AtiyahSinger.Topology.TrivialCohomologyThom

/-!
# Local cohomology of the original vector bundle pair

Public module ID: M1936.

A specified linear trivialization identifies the actual total space over any
subset of its base set with the product pair. The original cohomology pullbacks
then transfer the product calculation: lower degrees vanish, and top-degree
classes are determined by their restrictions to the original fibers.
The subset need not be connected, open, compact, or nonempty.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

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
/-- The cohomology comparison induced by the specified original bundle trivialization. -/
def bundleTrivializationCohomologyIso (k : ℕ) :
    relativeSingularCohomology R {z : V × EuclideanSpace ℝ (Fin r) | z.2 ≠ 0} k ≅
      relativeSingularCohomology R (bundleNonzeroOver r E V) k := by
  let H := e.preimageHomeomorph hV
  let f : C(BundleTotalOver r E V, V × EuclideanSpace ℝ (Fin r)) := ⟨H, H.continuous⟩
  let g : C(V × EuclideanSpace ℝ (Fin r), BundleTotalOver r E V) :=
    ⟨H.symm, H.symm.continuous⟩
  have hnonzero (z : BundleTotalOver r E V) : (H z).2 ≠ 0 ↔ z.val.snd ≠ 0 := by
    let L := e.continuousLinearEquivAt ℝ z.val.proj (hV z.property)
    change L z.val.snd ≠ 0 ↔ z.val.snd ≠ 0
    exact L.map_ne_zero_iff
  have hf : Set.MapsTo f (bundleNonzeroOver r E V) {z | z.2 ≠ 0} :=
    fun z hz ↦ (hnonzero z).mpr hz
  have hg : Set.MapsTo g {z | z.2 ≠ 0} (bundleNonzeroOver r E V) := by
    intro z hz
    apply (hnonzero (H.symm z)).mp
    rw [H.apply_symm_apply]
    exact hz
  have hgf : g.comp f = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact H.symm_apply_apply z
  have hfg : f.comp g = ContinuousMap.id _ := by
    apply ContinuousMap.ext
    intro z
    exact H.apply_symm_apply z
  have : IsIso (relativeSingularCohomologyPullback R f hf k) :=
    isIso_relativeSingularCohomologyPullback_of_inverse R f g hf hg hgf hfg k
  exact asIso (relativeSingularCohomologyPullback R f hf k)

include e hV he in
/-- Below the bundle rank, the relative cohomology of a trivialized restriction vanishes. -/
theorem subsingleton_relativeSingularCohomology_bundleTotalOver_below_rank
    (k : ℕ) (hk : k < r) :
    Subsingleton (relativeSingularCohomology R (bundleNonzeroOver r E V) k) := by
  have := subsingleton_relativeSingularCohomology_prod_euclidean_below_dim R V r k hk
  exact (ConcreteCategory.bijective_of_isIso
    (bundleTrivializationCohomologyIso R r E e V hV k).hom).surjective.subsingleton

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include e hV he in
/-- In a trivialized restriction, top-degree relative classes are determined by their
restrictions to the original fibers, with no connectedness assumption on the base. -/
theorem relativeSingularCohomology_bundleTotalOver_ext
    (a b : relativeSingularCohomology R (bundleNonzeroOver r E V) r)
    (h : ∀ (x : X) (hx : x ∈ V),
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E V x hx)
          (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E V)
          (fun _ hv ↦ hv) r a =
        relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E V x hx)
          (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E V)
          (fun _ hv ↦ hv) r b) : a = b := by
  let H := e.preimageHomeomorph hV
  let f : C(BundleTotalOver r E V, V × EuclideanSpace ℝ (Fin r)) := ⟨H, H.continuous⟩
  have hf : Set.MapsTo f (bundleNonzeroOver r E V) {z | z.2 ≠ 0} := by
    intro z hz
    let L := e.continuousLinearEquivAt ℝ z.val.proj (hV z.property)
    change L z.val.snd ≠ 0
    exact L.map_ne_zero_iff.mpr hz
  let I := bundleTrivializationCohomologyIso R r E e V hV r
  have hI : I.hom = relativeSingularCohomologyPullback R f hf r := rfl
  apply (ConcreteCategory.bijective_of_isIso I.inv).injective
  apply relativeSingularCohomology_prod_euclidean_ext R V r
  intro x
  -- Compare the original fiber map with the point-times-fiber map in the same chart.
  let L := e.continuousLinearEquivAt ℝ x.val (hV x.property)
  let j := bundleFiberInclusionOver r E V x.val x.property
  let k : C(PUnit.{u + 1} × EuclideanSpace ℝ (Fin r), E x.val) :=
    ⟨fun z ↦ L.symm z.2, L.symm.continuous.comp continuous_snd⟩
  let t := (ContinuousMap.const PUnit.{u + 1} x).prodMap
    (ContinuousMap.id (EuclideanSpace ℝ (Fin r)))
  have hk : Set.MapsTo k {z | z.2 ≠ 0} {v | v ≠ 0} :=
    fun _ hz ↦ L.symm.map_ne_zero_iff.mpr hz
  have hj : Set.MapsTo j {v | v ≠ 0} (bundleNonzeroOver r E V) := fun _ hz ↦ hz
  have ht : f.comp (j.comp k) = t := by
    apply ContinuousMap.ext
    intro z
    change H ⟨⟨x.val, L.symm z.2⟩, x.property⟩ = (x, z.2)
    apply Prod.ext
    · rw [e.preimageHomeomorph_apply hV]
    · change L (L.symm z.2) = z.2
      exact L.apply_symm_apply z.2
  have hsquare : I.hom ≫ relativeSingularCohomologyPullback R j hj r ≫
      relativeSingularCohomologyPullback R k hk r =
        relativeSingularCohomologyPullback R t
          (A := {z | z.2 ≠ 0}) (B := {z | z.2 ≠ 0}) (fun _ hz ↦ hz) r := by
    rw [hI, ← relativeSingularCohomologyPullback_comp,
      ← relativeSingularCohomologyPullback_comp]
    congr 1
  have ha := congrArg (fun g ↦ g (I.inv a)) hsquare
  have hb := congrArg (fun g ↦ g (I.inv b)) hsquare
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply] at ha hb
  exact ha.symm.trans ((congrArg (relativeSingularCohomologyPullback R k hk r)
    (h x.val x.property)).trans hb)

end AtiyahSinger
