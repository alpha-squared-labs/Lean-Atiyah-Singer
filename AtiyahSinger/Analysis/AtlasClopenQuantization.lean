/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasOpenQuantization

/-!
# One global quantization from the specified component quantizations

Public module ID: M0234.

The finite disjoint cover permits the exact patches of each component to be
assembled into an ambient presentation. Its partition and its actual section
action are the sums of the original zero-extended component data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

/-- Finite component presentations combine with exactly their original section actions. -/
theorem exists_atlasClopenQuantization {ι : Type*} [Fintype ι]
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ)
    (R : ∀ i, AtlasQuantizationPresentation (A.restrictOpen (U i)) (B.restrictOpen (U i))) :
    ∃ C : AtlasQuantizationPresentation A B,
      ∀ (m : ℝ) (p : atlasGlobalSymbolSpace A B m),
        C.toLinearMap p = ∑ i,
          (atlasSmoothSectionZeroExtension B (U i) (hclosed i)).comp
            (((R i).toLinearMap
              ⟨fun x ξ ↦ p.val x.val ξ, p.property.restrictOpen A B (U i)⟩).comp
                (atlasSmoothSectionRestriction A (U i))) := by
  classical
  choose S hweight hmap using fun i j ↦
    ((R i).patch j).exists_openExtension (U i) (hclosed i)
  let e := (Fintype.equivFin (Σ i, Fin (R i).size)).symm
  let patch (k : Fin (Fintype.card (Σ i, Fin (R i).size))) := S (e k).1 (e k).2
  -- Each point belongs to exactly one piece, so the original component partition remains one.
  have hpartition (x : M) : ∑ k, (patch k).weight x = 1 := by
    change (∑ k, (S (e k).1 (e k).2).weight x) = 1
    rw [e.sum_comp (fun ij ↦ (S ij.1 ij.2).weight x), Fintype.sum_sigma]
    have hx : x ∈ ⋃ i, (U i : Set M) := hcover.symm ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    rw [Finset.sum_eq_single i]
    · calc
        (∑ j, (S i j).weight x) = ∑ j, ((R i).patch j).weight ⟨x, hi⟩ :=
          Finset.sum_congr rfl (fun j _ ↦ (hweight i j x).trans (dite_eq_left hi))
        _ = 1 := (R i).sum_weight ⟨x, hi⟩
    · intro j _ hji
      have hj : x ∉ U j := fun hxj ↦ Set.disjoint_left.mp (hdisjoint hji) hxj hi
      simp only [hweight, dite_eq_right hj, Finset.sum_const_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ i))
  let C : AtlasQuantizationPresentation A B := ⟨_, patch, hpartition⟩
  refine ⟨C, ?_⟩
  intro m p
  -- Reindex the same local Fourier pieces and group each component's exact finite sum.
  change (∑ k, ((S (e k).1 (e k).2).toPiece p).toLinearMap) = _
  rw [e.sum_comp (fun ij ↦ ((S ij.1 ij.2).toPiece p).toLinearMap), Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [hmap]
  apply LinearMap.ext
  intro u
  simp only [LinearMap.sum_apply, LinearMap.comp_apply,
    AtlasQuantizationPresentation.toLinearMap, map_sum]

end AtiyahSinger
