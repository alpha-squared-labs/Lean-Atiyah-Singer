/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothHermitianFrames

/-!
# Orthonormalizing the original smooth atlas coordinates

Public module ID: M1363.

The original Hermitian metric pulls back through each supplied atlas frame to
a positive form on its fixed coordinate space. Smooth Gram--Schmidt gives a
smooth invertible change of those same coordinates to an orthonormal frame.
Only the frame domain is involved; no smooth extension across its boundary
and no change of bundle topology is asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

set_option backward.isDefEq.respectTransparency.types false in
/-- A smooth change of the original coordinates orthonormalizes the specified metric. -/
theorem exists_orthonormalFrameCoordinates (A : SmoothComplexBundleAtlas (n := n) E)
    (h : ComplexBundle.ContinuousHermitianMetric E) (hh : A.IsSmoothHermitianMetric h)
    (i : A.Index) :
    ∃ e : M → EuclideanSpace ℂ (Fin (A.rank i)) ≃L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank i)),
      (∀ x (hx : x ∈ (A.chart i).baseSet) u v,
        (h.toCore x).inner ((A.frameLinearEquiv i x hx).symm (e x u))
          ((A.frameLinearEquiv i x hx).symm (e x v)) = inner ℂ u v) ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
          EuclideanSpace ℂ (Fin (A.rank i))) ∞
        (fun x ↦ (e x).toContinuousLinearMap) (A.chart i).baseSet ∧
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
          EuclideanSpace ℂ (Fin (A.rank i))) ∞
        (fun x ↦ (e x).symm.toContinuousLinearMap) (A.chart i).baseSet := by
  classical
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let b : OrthonormalBasis (Fin (A.rank i)) ℂ V :=
    EuclideanSpace.basisFun (Fin (A.rank i)) ℂ
  let L (x : M) (hx : x ∈ (A.chart i).baseSet) : V ≃ₗ[ℂ] E x :=
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (A.rank i) ↦ ℂ)).toLinearEquiv.trans
      (A.frameLinearEquiv i x hx).symm
  have hb (k : Fin (A.rank i)) :
      (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin (A.rank i) ↦ ℂ)).toLinearEquiv (b k) =
        Pi.single k 1 := by
    change (EuclideanSpace.basisFun (Fin (A.rank i)) ℂ k).ofLp = _
    rw [EuclideanSpace.basisFun_apply]
    rfl
  -- Pull back the actual positive form without installing any replacement fiber norm.
  let H₀ (x : M) (hx : x ∈ (A.chart i).baseSet) : InnerProductSpace.Core ℂ V :=
    { inner := fun u v ↦ (h.toCore x).inner (L x hx u) (L x hx v)
      conj_inner_symm := fun u v ↦ (h.toCore x).conj_inner_symm _ _
      re_inner_nonneg := fun u ↦ (h.toCore x).re_inner_nonneg _
      add_left := by
        intro u v w
        rw [map_add]
        exact (h.toCore x).add_left _ _ _
      smul_left := by
        intro u v z
        rw [map_smul]
        exact (h.toCore x).smul_left _ _ _
      definite := by
        intro u hu
        apply (L x hx).injective
        rw [map_zero]
        exact (h.toCore x).definite _ hu }
  let H (x : M) : InnerProductSpace.Core ℂ V :=
    if hx : x ∈ (A.chart i).baseSet then H₀ x hx else InnerProductSpace.toCore
  -- Its Gram entries are exactly those of the original atlas metric certificate.
  have hH (a c : Fin (A.rank i)) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ (H x).inner (b a) (b c)) (A.chart i).baseSet := by
    apply (hh i a c).congr
    intro x hx
    have hHx : H x = H₀ x hx := dite_eq_left hx
    rw [hHx]
    change (h.toCore x).inner (L x hx (b a)) (L x hx (b c)) = _
    simp only [dite_eq_left hx]
    simp only [L, LinearEquiv.trans_apply]
    rw [hb a, hb c]
    rfl
  obtain ⟨e, he, heSmooth, heInv⟩ := exists_smoothHermitianFrames b.toBasis H
    (A.chart i).baseSet hH
  -- Reconstruct each operator from its smooth columns in this fixed finite basis.
  have hoperator (T : M → V →L[ℂ] V)
      (hT : ∀ k : Fin (A.rank i), ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, V) ∞ (fun x ↦ T x (b k)) (A.chart i).baseSet) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
        T (A.chart i).baseSet := by
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
        (fun x ↦ ∑ k : Fin (A.rank i),
          ContinuousLinearMap.smulRightL ℂ V V (b.toBasis.coord k).toContinuousLinearMap
            (T x (b k))) (A.chart i).baseSet := by
      apply contMDiffOn_finsetSum
      intro k _
      have hc := ((ContinuousLinearMap.smulRightL ℂ V V
        (b.toBasis.coord k).toContinuousLinearMap).restrictScalars ℝ).contDiff (n := ∞)
      exact hc.contMDiff.comp_contMDiffOn (hT k)
    apply hs.congr
    intro x _
    apply ContinuousLinearMap.ext
    intro v
    rw [sum_apply]
    change T x v = ∑ k : Fin (A.rank i), b.repr v k • T x (b k)
    simpa only [map_sum, map_smul] using (congrArg (T x) (b.sum_repr v)).symm
  refine ⟨fun x ↦ (e x).toContinuousLinearEquiv, ?_,
    hoperator _ heSmooth, hoperator _ heInv⟩
  intro x hx u v
  have hs := he x u v
  have hHx : H x = H₀ x hx := dite_eq_left hx
  rw [hHx] at hs
  exact hs

end AtiyahSinger.SmoothComplexBundleAtlas
