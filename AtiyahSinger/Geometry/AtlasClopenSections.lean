/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothAtlasRestriction
public import AtiyahSinger.Geometry.SmoothAtlasSections

/-!
# Actual atlas sections on finite clopen decompositions

Public module ID: M1089.

Restriction keeps every original fiber vector and chart coordinate. On a closed
open piece, the inverse operation extends that vector by zero. A finite
pairwise disjoint clopen cover identifies the original section space with the
product of the
restricted section spaces. These are the actual maps needed for the finite
component index calculation; no fixed global bundle rank is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := n) E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restrict the original atlas section by evaluating the same vector on the open piece. -/
def atlasSmoothSectionRestriction (U : Opens M) :
    A.smoothSections →ₗ[ℂ] (A.restrictOpen U).smoothSections where
  toFun s := ⟨fun x ↦ s.val x.val, by
    intro i
    have hbase : (A.restrictOpenChart U i).baseSet =
        Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
    have hcoords := (A.exists_restrictOpenChart U i).choose_spec.2
    change ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
      (fun x : U ↦ (A.restrictOpenChart U i ⟨x, s.val x.val⟩).2)
      (A.restrictOpenChart U i).baseSet
    rw [hbase]
    apply ((s.property i).comp (contMDiff_subtype_val (U := U)).contMDiffOn
      (fun _ hx ↦ hx)).congr
    intro x _
    exact hcoords ⟨x, s.val x.val⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

open scoped Classical in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extend a section from a clopen piece by its original vectors and zero elsewhere. -/
def atlasSmoothSectionZeroExtension (U : Opens M) (hU : IsClosed (U : Set M)) :
    (A.restrictOpen U).smoothSections →ₗ[ℂ] A.smoothSections where
  toFun s := ⟨fun x ↦ if hx : x ∈ U then s.val ⟨x, hx⟩ else 0, by
    intro i x hx
    by_cases hxU : x ∈ U
    · -- Inside the piece use its inherited chart, with exactly the original coordinates.
      apply ContMDiffAt.contMDiffWithinAt
      rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hxU⟩)]
      have hbase : (A.restrictOpenChart U i).baseSet =
          Subtype.val ⁻¹' (A.chart i).baseSet := (A.exists_restrictOpenChart U i).choose_spec.1
      have hs := (s.property i).contMDiffAt
        ((A.restrictOpenChart U i).open_baseSet.mem_nhds
          (show (⟨x, hxU⟩ : U) ∈ (A.restrictOpenChart U i).baseSet by
            rw [hbase]
            exact hx))
      apply hs.congr_of_eventuallyEq
      filter_upwards [] with y
      erw [dite_eq_left y.property]
      exact ((A.exists_restrictOpenChart U i).choose_spec.2 ⟨y, s.val y⟩).symm
    · -- Closedness makes the displayed extension identically zero near any exterior point.
      apply ContMDiffAt.contMDiffWithinAt
      apply (contMDiffAt_const (c := (0 : Fin (A.rank i) → ℂ))).congr_of_eventuallyEq
      filter_upwards [hU.isOpen_compl.mem_nhds hxU,
        (A.chart i).open_baseSet.mem_nhds hx] with y hy hiy
      erw [dite_eq_right hy]
      exact (A.linear i y hiy).map_zero⟩
  map_add' s t := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U <;> simp [hx]
  map_smul' z s := by
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ U <;> simp [hx]

open scoped Classical in
/-- Restrictions and zero extensions identify sections over a finite disjoint clopen cover. -/
theorem exists_atlasSmoothSectionClopenEquiv {ι : Type*} [Fintype ι]
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ) :
    ∃ e : A.smoothSections ≃ₗ[ℂ] ∀ i, (A.restrictOpen (U i)).smoothSections,
      (∀ u i x, (e u i).val x = u.val x.val) ∧
      (∀ v x, (e.symm v).val x =
        ∑ i, if hx : x ∈ U i then (v i).val ⟨x, hx⟩ else 0) := by
  classical
  let V (i : ι) := (A.restrictOpen (U i)).smoothSections
  let Z (i : ι) := atlasSmoothSectionZeroExtension A (U i) (hclosed i)
  have hZ (i : ι) (v : V i) (x : M) :
      (Z i v).val x = if hx : x ∈ U i then v.val ⟨x, hx⟩ else 0 := rfl
  let R : A.smoothSections →ₗ[ℂ] ∀ i, V i :=
    LinearMap.pi (fun i ↦ atlasSmoothSectionRestriction A (U i))
  have hR (u : A.smoothSections) (i : ι) (x : U i) :
      (R u i).val x = u.val x.val := rfl
  -- Disjointness makes restriction of the finite sum select the prescribed component.
  have hright (v : ∀ i, V i) : R (∑ i, Z i (v i)) = v := by
    funext i
    apply Subtype.ext
    funext x
    rw [hR]
    simp only [Submodule.coe_sum, Finset.sum_apply, hZ]
    rw [Finset.sum_eq_single i]
    · exact dite_eq_left x.property
    · intro j _ hji
      apply dite_eq_right
      intro hj
      exact Set.disjoint_left.mp (hdisjoint hji) hj x.property
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  -- The cover gives the unique surviving term at each original point, including empty pieces.
  have hleft (u : A.smoothSections) : (∑ i, Z i (R u i)) = u := by
    apply Subtype.ext
    funext x
    have hx : x ∈ ⋃ i, (U i : Set M) := hcover.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    simp only [Submodule.coe_sum, Finset.sum_apply, hZ]
    rw [Finset.sum_eq_single i]
    · erw [dite_eq_left hi]
      rfl
    · intro j _ hji
      apply dite_eq_right
      intro hj
      exact Set.disjoint_left.mp (hdisjoint hji) hj hi
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  let e : A.smoothSections ≃ₗ[ℂ] ∀ i, V i := {
    R with
    invFun := fun v ↦ ∑ i, Z i (v i)
    left_inv := hleft
    right_inv := hright }
  refine ⟨e, hR, ?_⟩
  intro v x
  change (∑ i, Z i (v i)).val x = _
  simp only [Submodule.coe_sum, Finset.sum_apply, hZ]

end AtiyahSinger
