/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenSections

/-!
# Smooth sections on a finite clopen decomposition

Public module ID: M1126.

The actual restrictions of one smooth section identify its section space with
the product of the native pullback section spaces. The inverse is the finite
sum of the actual zero extensions. These are the section maps needed for the
clopen block comparison of analytic indices; no operator or index law is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

open scoped Classical in
/-- Restriction and zero extension identify sections over a finite disjoint clopen cover. -/
theorem exists_smoothSectionClopenEquiv {ι : Type*} [Fintype ι]
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ) :
    ∃ e : smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        ∀ i, smoothSections (n := n) (r := r) (M := U i)
          ((ContinuousMap.subtypeVal (U i : Set M) : U i → M) *ᵖ E),
      (∀ u i x, (e u i).val x = u.val x.val) ∧
      (∀ v x, (e.symm v).val x =
        ∑ i, if hx : x ∈ U i then (v i).val ⟨x, hx⟩ else 0) := by
  classical
  -- Closedness permits the genuine zero extension of every section on each piece.
  let V (i : ι) := smoothSections (n := n) (r := r) (M := U i)
    ((ContinuousMap.subtypeVal (U i : Set M) : U i → M) *ᵖ E)
  let Z (i : ι) (v : V i) : smoothSections (n := n) (r := r) E :=
    smoothSectionZeroExtension E (U i) (U i : Set M) (hclosed i) (Set.Subset.refl _)
      ⟨v, fun x hx ↦ False.elim (hx x.property)⟩
  have hZ (i : ι) (v : V i) (x : M) :
      (Z i v).val x = if hx : x ∈ U i then v.val ⟨x, hx⟩ else 0 := rfl
  let R : smoothSections (n := n) (r := r) E →ₗ[ℂ] (∀ i, V i) :=
    LinearMap.pi (fun i ↦ smoothSectionRestriction E (U i))
  have hR (u : smoothSections (n := n) (r := r) E) (i : ι) (x : U i) :
      (R u i).val x = u.val x.val := rfl
  -- Disjointness makes restriction of this finite sum select precisely its own term.
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
  -- The cover supplies the unique nonzero term at each original base point.
  have hleft (u : smoothSections (n := n) (r := r) E) :
      (∑ i, Z i (R u i)) = u := by
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
  let e : smoothSections (n := n) (r := r) E ≃ₗ[ℂ] (∀ i, V i) :=
    { R with
      invFun := fun v ↦ ∑ i, Z i (v i)
      left_inv := hleft
      right_inv := hright }
  refine ⟨e, hR, ?_⟩
  intro v x
  change (∑ i, Z i (v i)).val x = _
  simp only [Submodule.coe_sum, Finset.sum_apply, hZ]

end AtiyahSinger
