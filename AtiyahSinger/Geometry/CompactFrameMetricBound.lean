/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasTensorMetricComparison

/-!
# Uniform operator comparison in the original compact frame window

Public module ID: M1130.

Smooth Hermitian forms are uniformly equivalent to coordinate squared norms
on a specified compact chart/frame overlap. Consequently every coordinate
operator bound gives a uniform bound for the same conjugated map in those
metrics. In particular one may insert the actual coordinate inverse and its
frequency-dependent bound. The constant depends only on the original metrics,
frames and compact window; no regular variation of native fiber norms or
orthonormality of the original frames is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- A uniform coordinate bound controls the same operator in the specified Hermitian metrics. -/
theorem SmoothComplexBundleAtlas.exists_compact_frame_metric_bound
    (A : SmoothComplexBundleAtlas (n := n) E) (B : SmoothComplexBundleAtlas (n := n) F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (hE : ComplexBundle.ContinuousHermitianMetric E)
    (hF : ComplexBundle.ContinuousHermitianMetric F)
    (hhE : A.IsSmoothHermitianMetric hE) (hhF : B.IsSmoothHermitianMetric hF)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index)
    (K : Set M) (hK : IsCompact K)
    (hKA : K ⊆ c.source ∩ (A.chart i).baseSet)
    (hKB : K ⊆ c.source ∩ (B.chart j).baseSet) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : M) (hx : x ∈ K),
      let e := (A.frameLinearEquiv i x (hKA hx).2).trans
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
      let f := (B.frameLinearEquiv j x (hKB hx).2).trans
        (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.toLinearEquiv
      ∀ (L : EuclideanSpace ℂ (Fin (B.rank j)) →L[ℂ]
          EuclideanSpace ℂ (Fin (A.rank i))) (m : ℝ), 0 ≤ m → ‖L‖ ≤ m →
        ∀ v : F x,
          ((hE.toCore x).inner (e.symm (L (f v))) (e.symm (L (f v)))).re ≤
            C * m ^ 2 * ((hF.toCore x).inner v v).re := by
  classical
  -- Order zero of the original array comparison contains exactly one empty index and no cotensors.
  obtain ⟨aE, bE, haE, hbE, hEb⟩ :=
    A.exists_covariant_array_norm_sq_bounds g hE hhE c hc i 0 K hK hKA
  obtain ⟨aF, bF, haF, hbF, hFb⟩ :=
    B.exists_covariant_array_norm_sq_bounds g hF hhF c hc j 0 K hK hKB
  refine ⟨bE / aF, div_pos hbE haF, ?_⟩
  intro x hx e f L m hm hLm v
  have hEcoord (z : EuclideanSpace ℂ (Fin (A.rank i))) :
      ((hE.toCore x).inner (e.symm z) (e.symm z)).re ≤ bE * ‖z‖ ^ 2 := by
    simpa [e] using (hEb x hx (fun _ ↦ z)).2
  have hFcoord : aF * ‖f v‖ ^ 2 ≤ ((hF.toCore x).inner v v).re := by
    have h := (hFb x hx (fun _ ↦ f v)).1
    have hf : (B.frameLinearEquiv j x (hKB hx).2).symm
        ((EuclideanSpace.equiv (Fin (B.rank j)) ℂ) (f v)) = v :=
      f.symm_apply_apply v
    simpa only [Finset.univ_unique, Finset.sum_singleton, Fin.prod_univ_zero,
      one_mul, hf] using h
  -- Combine the coordinate operator estimate with the input metric's uniform lower bound.
  have hnorm : ‖L (f v)‖ ≤ m * ‖f v‖ :=
    (L.le_opNorm (f v)).trans (mul_le_mul_of_nonneg_right hLm (norm_nonneg _))
  have hsq : ‖L (f v)‖ ^ 2 ≤ m ^ 2 * ‖f v‖ ^ 2 := by
    calc
      ‖L (f v)‖ ^ 2 ≤ (m * ‖f v‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = m ^ 2 * ‖f v‖ ^ 2 := mul_pow _ _ _
  calc
    ((hE.toCore x).inner (e.symm (L (f v))) (e.symm (L (f v)))).re
        ≤ bE * ‖L (f v)‖ ^ 2 := hEcoord _
    _ ≤ bE * (m ^ 2 * ‖f v‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hbE.le
    _ = (bE / aF * m ^ 2) * (aF * ‖f v‖ ^ 2) := by
      field_simp
    _ ≤ (bE / aF * m ^ 2) * ((hF.toCore x).inner v v).re :=
      mul_le_mul_of_nonneg_left hFcoord (mul_nonneg (div_nonneg hbE.le haF.le) (sq_nonneg m))

end AtiyahSinger
