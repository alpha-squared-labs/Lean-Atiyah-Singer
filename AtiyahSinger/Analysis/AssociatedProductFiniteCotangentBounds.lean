/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductCotangentBounds

/-!
# Uniform bounds for a finite family of actual active product charts

Public module ID: M0105.

The original compact supports of the active pieces intersect a specified
compact target-chart window in compact subsets of the actual overlaps.
The horizontal and vertical cotangent blocks have common upper and inverse
bounds; the mixed block has a common upper bound.
No common chart domain for inactive pieces is required, and
the finite family may be empty.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {ι P B : Type*} [Finite ι] [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 30 in
/-- One bound controls the actual cotangent blocks wherever each original piece is active. -/
theorem exists_associatedSphereProductChart_finite_cotangent_block_bounds
    (b : ι → B) (c : ι → OpenPartialHomeomorph B X)
    (hc : ∀ i, c i ∈ atlas X B)
    (d : ι → OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : ∀ i, d i ∈ atlas Y (OrthogonalSphere r))
    (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (hc₀ : c₀ ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (s : ι → Set Z) (hs : ∀ i, IsCompact (s i))
    (hsChart : ∀ i, s i ⊆ (associatedSphereProductChart S (b i) (c i) (d i)).source)
    (K : Set H) (hK : IsCompact K)
    (hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let CP := associatedSphereProductChart S b₀ c₀ d₀
    let e := fun i ↦ (associatedSphereProductChart S (b i) (c i) (d i)).symm.trans CP
    let pr := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
    let qr := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
    let inx := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X Y)
    let iny := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ X Y)
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i z, z ∈ K → CP.symm z ∈ s i →
      let A := fderiv ℝ ((c i).symm.trans c₀) (pr ((e i).symm z))
      let B := qr.comp ((fderiv ℝ (e i) ((e i).symm z)).comp inx)
      let V := qr.comp ((fderiv ℝ (e i) ((e i).symm z)).comp iny)
      ‖A.adjoint‖ ≤ D ∧ (∀ ξ, ‖ξ‖ ≤ D * ‖A.adjoint ξ‖) ∧
        ‖B.adjoint‖ ≤ D ∧ ‖V.adjoint‖ ≤ D ∧ ∀ η, ‖η‖ ≤ D * ‖V.adjoint η‖ := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  intro split CP e pr qr inx iny
  let k := CP.symm '' K
  have hk : IsCompact k := hK.image_of_continuousOn (CP.continuousOn_symm.mono hKChart)
  have hkChart : k ⊆ CP.source := by
    rintro z ⟨x, hx, rfl⟩
    exact CP.map_target (hKChart hx)
  let window (i : ι) := CP '' (s i ∩ k)
  have hwindow (i : ι) : IsCompact (window i) :=
    ((hs i).inter hk).image_of_continuousOn
      (CP.continuousOn.mono (inter_subset_right.trans hkChart))
  have hwindowChart (i : ι) : window i ⊆ (e i).target := by
    rintro z ⟨x, hx, rfl⟩
    have hx₀ := hkChart hx.2
    refine ⟨CP.map_source hx₀, ?_⟩
    change CP.symm (CP x) ∈ (associatedSphereProductChart S (b i) (c i) (d i)).source
    rw [CP.left_inv hx₀]
    exact hsChart i hx.1
  -- Each compact window uses the actual transition of that piece into the specified target.
  have hlocal (i : ι) := exists_associatedSphereProductChart_cotangent_block_bounds
    S (b i) b₀ (c i) c₀ (hc i) hc₀ (d i) d₀ (hd i) hd₀
      (window i) (hwindow i) (hwindowChart i)
  choose D hD hbound using hlocal
  let C := 1 + ∑ i, D i
  have hDnonneg (i : ι) : 0 ≤ D i := zero_le_one.trans (hD i)
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ ↦ hDnonneg i))
  have hDC (i : ι) : D i ≤ C := by
    have hsum : D i ≤ ∑ j, D j :=
      Finset.single_le_sum (fun j _ ↦ hDnonneg j) (Finset.mem_univ i)
    exact hsum.trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro i z hz hzs
  have hzw : z ∈ window i :=
    ⟨CP.symm z, ⟨hzs, ⟨z, hz, rfl⟩⟩, CP.right_inv (hKChart hz)⟩
  obtain ⟨hA, hAi, hB, hV, hVi⟩ := hbound i z hzw
  refine ⟨hA.trans (hDC i), ?_, hB.trans (hDC i), hV.trans (hDC i), ?_⟩
  · intro ξ
    exact (hAi ξ).trans (mul_le_mul_of_nonneg_right (hDC i) (norm_nonneg _))
  · intro η
    exact (hVi η).trans (mul_le_mul_of_nonneg_right (hDC i) (norm_nonneg _))

end AtiyahSinger
