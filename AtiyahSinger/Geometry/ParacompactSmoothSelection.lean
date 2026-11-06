/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Structures
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth convex selection over a paracompact manifold

Public module ID: M1338.

Locally admissible constant values in convex sets admit a smooth global
selection on a Hausdorff paracompact finite-dimensional real manifold.
A locally finite refinement and compact smooth bump supports supply positive
weights without a countability or compactness assumption on the base.

This is the usual partition-of-unity argument. In tubular constructions the
convex sets are intervals of positive radii whose fiber disks lie in a specified
open neighborhood; the theorem does not require those radii to have a uniform
positive lower bound.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Function Topology
open scoped ContDiff Manifold

variable {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B] [T2Space B] [ParacompactSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Locally admissible constants in convex sets admit a smooth paracompact selection. -/
theorem exists_contMDiffMap_mem_convex_of_paracompact (t : B → Set F)
    (ht : ∀ x, Convex ℝ (t x))
    (hlocal : ∀ x : B, ∃ c : F, ∀ᶠ y in 𝓝 x, c ∈ t y) :
    ∃ g : ContMDiffMap 𝓘(ℝ, EB) 𝓘(ℝ, F) B F ∞, ∀ x, g x ∈ t x := by
  classical
  choose c hc using hlocal
  have hW (x : B) : ∃ W : Set B, IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W, c x ∈ t y := by
    obtain ⟨W, hW, hWo, hxW⟩ := mem_nhds_iff.mp (hc x)
    exact ⟨W, hWo, hxW, hW⟩
  choose W hWo hWx hWc using hW
  have hweights : ∃ φ : B → B → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ (φ i)) ∧
      (∀ i x, 0 ≤ φ i x) ∧ (∀ x, ∃ i, 0 < φ i x) ∧
      LocallyFinite (fun i ↦ tsupport (φ i)) ∧
      ∀ i, tsupport (φ i) ⊆ W i := by
    -- Start with compact smooth-bump supports inside the admissibility neighborhoods.
    have hb (x : B) : ∃ b : SmoothBumpFunction 𝓘(ℝ, EB) x,
        tsupport b ⊆ W x :=
      (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, EB)) x).mem_iff.mp
        ((hWo x).mem_nhds (hWx x)) |>.imp
          (fun b hb ↦ hb.2)
    choose b hb using hb
    obtain ⟨U, hUo, hUc, hUf, hUb⟩ := precise_refinement
      (fun x ↦ support (b x)) (fun x ↦ (b x).isOpen_support)
      (iUnion_eq_univ_iff.mpr fun x ↦ ⟨x, (b x).c_mem_support⟩)
    -- A continuous bump cover supplies compact closed pieces covering the whole base.
    obtain ⟨ρ, hρ⟩ := BumpCovering.exists_isSubordinate_of_locallyFinite
      isClosed_univ U hUo hUf hUc.ge
    let K (i : B) : Set B := {x | ρ i x = 1}
    have hKclosed (i : B) : IsClosed (K i) := isClosed_eq (ρ i).continuous continuous_const
    have hKU (i : B) : K i ⊆ U i := by
      intro x hx
      apply hρ i
      apply subset_closure
      change ρ i x ≠ 0
      change ρ i x = 1 at hx
      simp [hx]
    have hKc : (univ : Set B) ⊆ ⋃ i, K i := by
      intro x hx
      exact mem_iUnion.mpr ⟨ρ.ind x hx, (ρ.eventuallyEq_one x hx).eq_of_nhds⟩
    have hKcompact (i : B) : IsCompact (K i) :=
      (b i).hasCompactSupport.of_isClosed_subset (hKclosed i)
        ((hKU i).trans ((hUb i).trans subset_closure))
    -- Smooth finitely many small bumps on each compact piece; their supports stay in U i.
    have hφ (i : B) : ∃ φ : B → ℝ,
        ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, ℝ) ∞ φ ∧ (∀ x, 0 ≤ φ x) ∧
        (∀ x ∈ K i, 0 < φ x) ∧ tsupport φ ⊆ U i := by
      have hb' (x : K i) : ∃ b' : SmoothBumpFunction 𝓘(ℝ, EB) (x : B),
          tsupport b' ⊆ U i :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, EB)) (x : B)).mem_iff.mp
          ((hUo i).mem_nhds (hKU i x.property)) |>.imp (fun b' hb' ↦ hb'.2)
      choose c hc using hb'
      obtain ⟨t, ht⟩ := (hKcompact i).elim_finite_subcover
        (fun x : K i ↦ support (c x)) (fun x ↦ (c x).isOpen_support)
        (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, (c ⟨x, hx⟩).c_mem_support⟩)
      refine ⟨fun x ↦ ∑ y ∈ t, c y x, ?_, ?_, ?_, ?_⟩
      · exact contMDiff_finsetSum fun y hy ↦ (c y).contMDiff
      · intro x
        exact Finset.sum_nonneg fun y hy ↦ (c y).nonneg
      · intro x hx
        obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hx)
        exact Finset.sum_pos' (fun z hz ↦ (c z).nonneg)
          ⟨y, hy, lt_of_le_of_ne (c y).nonneg (Ne.symm hxy)⟩
      · apply subset_trans (b := ⋃ y ∈ t, tsupport (c y))
        · apply closure_minimal
          · intro x hx
            by_contra hn
            apply hx
            apply Finset.sum_eq_zero
            intro y hy
            apply image_eq_zero_of_notMem_tsupport
            exact fun hxy ↦ hn (mem_iUnion₂.mpr ⟨y, hy, hxy⟩)
          · exact isClosed_biUnion_finset fun y hy ↦ isClosed_closure
        · exact iUnion₂_subset fun y hy ↦ hc y
    choose φ hφsmooth hφnonneg hφpos hφsupport using hφ
    refine ⟨φ, hφsmooth, hφnonneg, ?_, hUf.subset hφsupport, ?_⟩
    · intro x
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hKc (mem_univ x))
      exact ⟨i, hφpos i x hi⟩
    · intro i
      exact (hφsupport i).trans ((hUb i).trans (subset_closure.trans (hb i)))
  obtain ⟨φ, hφsmooth, hφnonneg, hφpos, hφfinite, hφsupport⟩ := hweights
  let S (x : B) : ℝ := ∑ᶠ i, φ i x
  have hS : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ) ∞ S :=
    contMDiff_finsum hφsmooth (hφfinite.subset (fun _ ↦ subset_closure))
  have hSpos (x : B) : 0 < S x := by
    obtain ⟨i, hi⟩ := hφpos x
    exact finsum_pos (fun j ↦ hφnonneg j x) ⟨i, hi⟩
      ((hφfinite.point_finite x).subset (fun j hj ↦ subset_closure hj))
  let w (i x : B) : ℝ := φ i x * (S x)⁻¹
  have hw (i : B) : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ) ∞ (w i) :=
    (hφsmooth i).mul (hS.inv₀ (fun x ↦ (hSpos x).ne'))
  have hsum (x : B) : ∑ᶠ i, w i x = 1 := by
    dsimp [w]
    rw [← finsum_mul]
    exact mul_inv_cancel₀ (hSpos x).ne'
  have hwfinite : LocallyFinite (fun i ↦ support (w i)) :=
    hφfinite.subset (fun i x hx ↦ subset_closure (left_ne_zero_of_mul hx))
  -- The normalized finite convex combination is admissible at every point.
  let g (x : B) : F := ∑ᶠ i, w i x • c i
  have hg : ContMDiff 𝓘(ℝ, EB) 𝓘(ℝ, F) ∞ g :=
    contMDiff_finsum (fun i ↦ (hw i).smul contMDiff_const)
      (hwfinite.subset (fun i x hx ↦ left_ne_zero_of_smul hx))
  refine ⟨⟨g, hg⟩, fun x ↦ ?_⟩
  apply (ht x).finsum_mem
    (fun i ↦ mul_nonneg (hφnonneg i x) (inv_nonneg.mpr (hSpos x).le)) (hsum x)
  intro i hi
  exact hWc i x (hφsupport i (subset_closure (left_ne_zero_of_mul hi)))

end AtiyahSinger
