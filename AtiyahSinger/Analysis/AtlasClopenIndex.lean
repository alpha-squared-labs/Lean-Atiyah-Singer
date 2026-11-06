/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IndexFiniteSum
public import AtiyahSinger.Analysis.IndexIntertwining
public import AtiyahSinger.Geometry.AtlasClopenSections

/-!
# Index of finite atlas block sums

Public module ID: M0233.

Restriction and zero extension identify the section spaces with their finite
clopen products. For block operators with finite-dimensional kernels and
cokernels, the diagonal block sum has the sum of the block indices.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The index of the actual zero-extended diagonal block sum is the sum of the given indices. -/
theorem index_atlasClopenBlockSum {ι : Type*} [Fintype ι]
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ)
    (P : ∀ i, (A.restrictOpen (U i)).smoothSections →ₗ[ℂ]
      (B.restrictOpen (U i)).smoothSections)
    [∀ i, FiniteDimensional ℂ (P i).ker]
    [∀ i, FiniteDimensional ℂ ((B.restrictOpen (U i)).smoothSections ⧸ (P i).range)] :
    (∑ i, (atlasSmoothSectionZeroExtension B (U i) (hclosed i)).comp
      ((P i).comp (atlasSmoothSectionRestriction A (U i)))).index = ∑ i, (P i).index := by
  classical
  obtain ⟨e, he, _⟩ := exists_atlasSmoothSectionClopenEquiv A U hclosed hdisjoint hcover
  obtain ⟨f, hf, _⟩ := exists_atlasSmoothSectionClopenEquiv B U hclosed hdisjoint hcover
  let T := ∑ i, (atlasSmoothSectionZeroExtension B (U i) (hclosed i)).comp
    ((P i).comp (atlasSmoothSectionRestriction A (U i)))
  have hinter (u : A.smoothSections) : (LinearMap.piMap P) (e u) = f (T u) := by
    funext i
    apply Subtype.ext
    funext x
    rw [hf]
    change ((P i) (e u i)).val x = (T u).val x.val
    have hrestrict : e u i = atlasSmoothSectionRestriction A (U i) u := by
      apply Subtype.ext
      funext y
      exact he u i y
    rw [hrestrict]
    change _ = ((∑ j, (atlasSmoothSectionZeroExtension B (U j) (hclosed j)).comp
      ((P j).comp (atlasSmoothSectionRestriction A (U j)))) u).val x.val
    simp only [LinearMap.sum_apply, LinearMap.comp_apply, Submodule.coe_sum, Finset.sum_apply]
    rw [Finset.sum_eq_single i]
    · change ((P i) (atlasSmoothSectionRestriction A (U i) u)).val x =
        if hx : x.val ∈ U i then
        ((P i) (atlasSmoothSectionRestriction A (U i) u)).val ⟨x.val, hx⟩ else 0
      rw [dite_eq_left x.property]
    · intro j _ hji
      change (if hx : x.val ∈ U j then _ else 0) = 0
      apply dite_eq_right
      intro hxj
      exact Set.disjoint_left.mp (hdisjoint hji) hxj x.property
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  exact (index_eq_of_linearEquiv T (LinearMap.piMap P) e f hinter).trans (index_piMap P)

end AtiyahSinger
