/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SmoothProjectionApproximation
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# One smoothing approximation for an operator and its actual adjoint

Public module ID: M0846.

A finite smooth input projection is chosen for two compact maps at once:
the original input inclusion and the actual L2 adjoint after the output
inclusion. Composing the given operator with this same projection has a
smooth finite-rank kernel. It approximates both the operator and its literal
adjoint on their respective original order-one domains.

This strengthens the one-sided smooth-core approximation needed for the
associated vertical residual. No fiberwise smoothing remainder is asserted
to be a PDO on the whole associated space.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
-- Retain the same completion isometry and finite smooth basis through both norm comparisons.
/-- One actual smooth kernel approximates the given map and its literal adjoint on H1. -/
theorem exists_paired_smoothing_approximation_of_smooth_core
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (D : Submodule ℂ (h.SmoothL2Section μ))
    (hD : DenseRange (fun u : D ↦ h.smoothToL2 μ u.val))
    (T : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ)
    (hT : ∀ u : D, ∃ v : smoothSections (n := n) (r := q) F,
      T (h.smoothToL2 μ u.val) = k.smoothToL2 μ v) (ε : ℝ) (hε : 0 < ε) :
    let I := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
      (A.sobolevInclusion 1 0 (by norm_num))
    let J := (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
      (B.sobolevInclusion 1 0 (by norm_num))
    ∃ L : smoothSections (n := n) (r := r) E →ₗ[ℂ] smoothSections (n := n) (r := q) F,
      IsSmoothingOperator μ L ∧
        ∃ R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ,
          (∀ u, R (h.smoothToL2 μ u) = k.smoothToL2 μ (L u)) ∧
          ‖T.comp I - R.comp I‖ < ε ∧
          ‖T.adjoint.comp J - R.adjoint.comp J‖ < ε := by
  classical
  intro I J
  let X := A.SobolevSpace 1
  let Y := B.SobolevSpace 1
  let j : D →ₗᵢ[ℂ] h.L2SectionSpace μ :=
    UniformSpace.Completion.toComplₗᵢ.comp D.subtypeₗᵢ
  have hI : IsCompactOperator I :=
    (A.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap
  have hJ : IsCompactOperator J :=
    (B.isCompactOperator_sobolevInclusion 1 0 (by norm_num)).clm_comp
      (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap
  let U : X × Y →L[ℂ] h.L2SectionSpace μ :=
    I.comp (ContinuousLinearMap.fst ℂ X Y) +
      (T.adjoint.comp J).comp (ContinuousLinearMap.snd ℂ X Y)
  have hU : IsCompactOperator U :=
    (hI.comp_clm (ContinuousLinearMap.fst ℂ X Y)).add
      ((hJ.clm_comp T.adjoint).comp_clm (ContinuousLinearMap.snd ℂ X Y))
  have hdenom : 0 < ‖T‖ + 1 := by positivity
  -- One projection controls both compact images in the same original input L2 space.
  obtain ⟨s, hs⟩ := exists_finite_projection_approximation j hD U hU
    (ε / (‖T‖ + 1)) (div_pos hε hdenom)
  let W := Submodule.span ℂ (s : Set D)
  let V := W.map j.toLinearMap
  let b := stdOrthonormalBasis ℂ W
  have hleft : ‖I - V.starProjection.comp I‖ < ε / (‖T‖ + 1) := by
    have heq : I - V.starProjection.comp I =
        (U - V.starProjection.comp U).comp (ContinuousLinearMap.inl ℂ X Y) := by
      ext u
      change I u - V.starProjection (I u) =
        I u + T.adjoint (J 0) - V.starProjection (I u + T.adjoint (J 0))
      simp only [map_zero, add_zero]
    rw [heq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_inl_le_one ℂ X Y))).trans_lt hs
  have hright : ‖T.adjoint.comp J - V.starProjection.comp (T.adjoint.comp J)‖ <
      ε / (‖T‖ + 1) := by
    have heq : T.adjoint.comp J - V.starProjection.comp (T.adjoint.comp J) =
        (U - V.starProjection.comp U).comp (ContinuousLinearMap.inr ℂ X Y) := by
      ext u
      change T.adjoint (J u) - V.starProjection (T.adjoint (J u)) =
        I 0 + T.adjoint (J u) - V.starProjection (I 0 + T.adjoint (J u))
      simp only [map_zero, zero_add]
    rw [heq]
    exact ((ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _)
        (ContinuousLinearMap.norm_inr_le_one ℂ X Y))).trans_lt hs
  let v (i : Fin (Module.finrank ℂ W)) : h.SmoothL2Section μ := (b i).val.val
  choose w hw using fun i : Fin (Module.finrank ℂ W) ↦ hT (b i).val
  let L : smoothSections (n := n) (r := r) E →ₗ[ℂ]
      smoothSections (n := n) (r := q) F :=
    ∑ i, (innerSL ℂ (v i)).toLinearMap.smulRight (w i)
  let R : h.L2SectionSpace μ →L[ℂ] k.L2SectionSpace μ :=
    ∑ i, (innerSL ℂ (h.smoothToL2 μ (v i))).smulRight (k.smoothToL2 μ (w i))
  -- The original finite smooth vectors give an actual kernel at every Sobolev order.
  have hL : IsSmoothingOperator μ L := by
    apply (isSmoothingOperator_iff_sobolevExtensions μ L A B).mpr
    intro a c
    let f (i : Fin (Module.finrank ℂ W)) : StrongDual ℂ (A.SobolevSpace a) :=
      h.sobolevDuality A μ a (A.smoothToSobolev (-a) (v i))
    refine ⟨∑ i, (f i).smulRight (B.smoothToSobolev c (w i)), ?_⟩
    intro u
    simp only [L, sum_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul,
      ContinuousLinearMap.smulRight_apply]
    apply Finset.sum_congr rfl
    intro i _
    change h.sobolevPairing A μ a (A.smoothToSobolev (-a) (v i))
      (A.smoothToSobolev a u) • B.smoothToSobolev c (w i) = _
    rw [h.sobolevPairing_smooth]
    rfl
  have hR (u : smoothSections (n := n) (r := r) E) :
      R (h.smoothToL2 μ u) = k.smoothToL2 μ (L u) := by
    simp only [R, L, sum_apply, LinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
      LinearMap.smulRight_apply, map_sum, map_smul, innerSL_apply_apply,
      h.inner_smoothToL2]
    rfl
  have hRV : R = T.comp V.starProjection := by
    apply DFunLike.ext'
    apply hD.equalizer R.continuous (T.comp V.starProjection).continuous
    funext u
    change R (j u) = T (V.starProjection (j u))
    rw [← j.map_starProjection W u, b.starProjection_eq_sum_rankOne]
    simp only [sum_apply, InnerProductSpace.rankOne_apply, map_sum, map_smul]
    change (∑ i, (innerSL ℂ (h.smoothToL2 μ (v i))).smulRight
      (k.smoothToL2 μ (w i))) (j u) = _
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    apply Finset.sum_congr rfl
    intro i _
    have hi : h.smoothToL2 μ (v i) = j (b i).val := rfl
    rw [hi, j.inner_map_map]
    change _ = inner ℂ (b i).val u • T (h.smoothToL2 μ (b i).val.val)
    rw [hw i]
  refine ⟨L, hL, R, hR, ?_, ?_⟩
  · -- The forward error is T after the small inclusion error for this same projection.
    rw [hRV, ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_sub]
    calc
      _ ≤ ‖T‖ * ‖I - V.starProjection.comp I‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (‖T‖ + 1) * ‖I - V.starProjection.comp I‖ := by gcongr; linarith
      _ < (‖T‖ + 1) * (ε / (‖T‖ + 1)) := mul_lt_mul_of_pos_left hleft hdenom
      _ = ε := mul_div_cancel₀ ε hdenom.ne'
  · -- The literal adjoint has the same projection on the left, controlling the second image.
    rw [hRV, ContinuousLinearMap.adjoint_comp,
      show V.starProjection.adjoint = V.starProjection from isSelfAdjoint_starProjection V,
      ContinuousLinearMap.comp_assoc]
    exact hright.trans_le (div_le_self hε.le (by linarith [norm_nonneg T]))

end AtiyahSinger

