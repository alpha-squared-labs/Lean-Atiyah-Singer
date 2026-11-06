/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockKernel
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closing the simultaneous graphs of a graded matrix

Public module ID: M0687.

The original two joint graphs retain each input and both operator images.
When their cross pairings agree, the signed graded graph map is bounded below
on the product of their closures. Its closed image is exactly the closure
of the original graded graph image. This argument applies to associated
bundle operators without identifying the section space with a global tensor
product. Functionality of the joint graphs and geometric Sobolev estimates
are separate prerequisites for the resulting operator-domain identification.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {E₀ E₁ F₀ F₁ : Type*}
  [NormedAddCommGroup E₀] [NormedSpace ℂ E₀] [CompleteSpace E₀]
  [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
  [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]

/-- Energy makes the image of the two joint graph closures equal the graded graph closure. -/
theorem map_jointGraphClosure_of_inner_eq
    (J₀ : Submodule ℂ (E₀ × F₀ × F₁))
    (J₁ : Submodule ℂ (E₁ × F₀ × F₁))
    (f : ((E₀ × F₀ × F₁) × (E₁ × F₀ × F₁)) →L[ℂ]
      (WithLp 2 (E₀ × E₁) × WithLp 2 (F₀ × F₁)))
    (hf : ∀ x y, f (x, y) =
      (WithLp.toLp 2 (x.1, y.1), WithLp.toLp 2 (x.2.1 - y.2.1, x.2.2 + y.2.2)))
    (hcross : ∀ x ∈ J₀, ∀ y ∈ J₁, inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2) :
    (J₀.topologicalClosure.prod J₁.topologicalClosure).map f.toLinearMap =
      ((J₀.prod J₁).map f.toLinearMap).topologicalClosure := by
  let C := J₀.topologicalClosure.prod J₁.topologicalClosure
  let R := (J₀.prod J₁).map f.toLinearMap
  have hC : IsClosed (C : Set ((E₀ × F₀ × F₁) × (E₁ × F₀ × F₁))) :=
    J₀.isClosed_topologicalClosure.prod J₁.isClosed_topologicalClosure
  let : CompleteSpace C := hC.completeSpace_coe
  -- Pass both pairings to the joint closures, retaining all four image coordinates.
  have hcrossClosure (x : E₀ × F₀ × F₁) (hx : x ∈ J₀.topologicalClosure)
      (y : E₁ × F₀ × F₁) (hy : y ∈ J₁.topologicalClosure) :
      inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2 := by
    have hyclosed : IsClosed {y : E₁ × F₀ × F₁ |
        inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    apply hyclosed.closure_subset_iff.mpr ?_ hy
    intro y hy
    have hxclosed : IsClosed {x : E₀ × F₀ × F₁ |
        inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    exact hxclosed.closure_subset_iff.mpr (fun x hx ↦ hcross x hx y hy) hx
  let F := f.comp C.subtypeL
  -- The exact ℓ²-sum norm controls each image; the input coordinates are also retained.
  have hbound (z : C) : ‖z‖ ≤ ‖F z‖ := by
    have hout : ‖(f z.val).2‖ ^ 2 =
        ‖z.val.1.2.1‖ ^ 2 + ‖z.val.1.2.2‖ ^ 2 +
          ‖z.val.2.2.1‖ ^ 2 + ‖z.val.2.2.2‖ ^ 2 := by
      rw [hf, WithLp.prod_norm_sq_eq_of_L2]
      change ‖z.val.1.2.1 - z.val.2.2.1‖ ^ 2 +
        ‖z.val.1.2.2 + z.val.2.2.2‖ ^ 2 = _
      rw [norm_sub_sq (𝕜 := ℂ), norm_add_sq (𝕜 := ℂ),
        hcrossClosure _ z.property.1 _ z.property.2]
      ring
    have ha : ‖z.val.1.2.1‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.2‖, sq_nonneg ‖z.val.2.2.1‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hb : ‖z.val.1.2.2‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.2.2.1‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hc : ‖z.val.2.2.1‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.1.2.2‖,
        sq_nonneg ‖z.val.2.2.2‖, norm_nonneg (f z.val).2]
    have hd : ‖z.val.2.2.2‖ ≤ ‖(f z.val).2‖ := by
      nlinarith [sq_nonneg ‖z.val.1.2.1‖, sq_nonneg ‖z.val.1.2.2‖,
        sq_nonneg ‖z.val.2.2.1‖, norm_nonneg (f z.val).2]
    have hx₀ : ‖z.val.1.1‖ ≤ ‖(f z.val).1‖ := by
      rw [hf]
      exact WithLp.norm_fst_le E₀ (WithLp.toLp 2 (z.val.1.1, z.val.2.1))
    have hx₁ : ‖z.val.2.1‖ ≤ ‖(f z.val).1‖ := by
      rw [hf]
      exact WithLp.norm_snd_le E₀ (WithLp.toLp 2 (z.val.1.1, z.val.2.1))
    change max (max ‖z.val.1.1‖ (max ‖z.val.1.2.1‖ ‖z.val.1.2.2‖))
        (max ‖z.val.2.1‖ (max ‖z.val.2.2.1‖ ‖z.val.2.2.2‖)) ≤
      max ‖(f z.val).1‖ ‖(f z.val).2‖
    exact max_le
      (max_le (hx₀.trans (le_max_left _ _))
        (max_le (ha.trans (le_max_right _ _)) (hb.trans (le_max_right _ _))))
      (max_le (hx₁.trans (le_max_left _ _))
        (max_le (hc.trans (le_max_right _ _)) (hd.trans (le_max_right _ _))))
  have hclosedRange : IsClosed (F.range : Set
      (WithLp 2 (E₀ × E₁) × WithLp 2 (F₀ × F₁))) := by
    have hanti : AntilipschitzWith 1 F := F.antilipschitz_of_bound (fun z ↦ by
      simpa only [NNReal.coe_one, one_mul] using hbound z)
    exact hanti.isClosed_range F.uniformContinuous
  have hRange : F.range = C.map f.toLinearMap := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- The closed image contains the original graph and therefore its entire closure.
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxc : IsClosed {x : E₀ × F₀ × F₁ | f (x, y) ∈ R.topologicalClosure} :=
      R.isClosed_topologicalClosure.preimage (by fun_prop)
    apply hxc.closure_subset_iff.mpr ?_ hx
    intro x hx
    have hyc : IsClosed {y : E₁ × F₀ × F₁ | f (x, y) ∈ R.topologicalClosure} :=
      R.isClosed_topologicalClosure.preimage (by fun_prop)
    apply hyc.closure_subset_iff.mpr ?_ hy
    intro y hy
    exact R.le_topologicalClosure ⟨(x, y), ⟨hx, hy⟩, rfl⟩
  · apply R.topologicalClosure_minimal _ (hRange ▸ hclosedRange)
    apply Submodule.map_mono
    intro z hz
    exact ⟨J₀.le_topologicalClosure hz.1, J₁.le_topologicalClosure hz.2⟩

end AtiyahSinger
