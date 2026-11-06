/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.GradedBundleOperator
public import AtiyahSinger.Analysis.GradedHodgeFiniteAssembly
public import AtiyahSinger.Analysis.SmoothSectionBundleSum
public import AtiyahSinger.Analysis.SobolevBundleSum

/-!
# An elliptic graded operator controls its first column

Public module ID: M0707.

A supplied elliptic native operator K acts on the first summand as the
column (U,V). Its H¹ estimate on the specified smooth sum Φ(u,0),
transported through the same Sobolev sum equivalences, bounds the H¹ norm
of u by its H⁰ norm and the H⁰ norms of Uu and Vu. This gives a reverse
joint estimate for the original component presentations.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : Fin 2 → SmoothFiniteComplexBundle (n := n) M)

set_option maxHeartbeats 2000000 in
-- The extended limit accommodates the original graded elliptic column and its geometric H1
-- estimate.
/-- The first column of the given elliptic graded operator has the original H1 estimate. -/
theorem graded_left_column_elliptic_bound
    (e : ∀ x, ((A 0).Fiber x × (A 1).Fiber x) ≃ₗ[ℂ] E.Fiber x)
    (f : ∀ x, ((B 0).Fiber x × (B 1).Fiber x) ≃ₗ[ℂ] F.Fiber x)
    (he₀ : IsSmoothBundleMap (n := n) (r := (A 0).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (he₁ : IsSmoothBundleMap (n := n) (r := (A 1).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (hf₀ : IsSmoothBundleMap (n := n) (r := (B 0).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    (hf₁ : IsSmoothBundleMap (n := n) (r := (B 1).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    (U : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber μ 1)
    (V : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber μ 1)
    (W : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 0).rank)
      (A 1).Fiber (B 0).Fiber μ 1)
    (Z : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 1).rank)
      (A 1).Fiber (B 1).Fiber μ 1)
    (D : (i : Fin 2) → SmoothBundlePresentation (n := n) (r := (A i).rank) (A i).Fiber)
    (H : (j : Fin 2) → SmoothBundlePresentation (n := n) (r := (B j).rank) (B j).Fiber)
    (S : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
    (T : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber)
    (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 1) (hKell : K.IsElliptic) :
    let Φ := smoothSectionSumEquiv e he₀ he₁
    let Ψ := smoothSectionSumEquiv f hf₀ hf₁
    (∀ u v, K.toLinearMap (Φ (u, v)) =
      Ψ (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v)) →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber,
        ‖(D 0).smoothToSobolev 1 u‖ ≤ C *
          (‖(D 0).smoothToSobolev 0 u‖ + ‖(H 0).smoothToSobolev 0 (U.toLinearMap u)‖ +
            ‖(H 1).smoothToSobolev 0 (V.toLinearMap u)‖) := by
  classical
  intro Φ Ψ hK
  -- The same smooth sum determines all three completion identifications.
  obtain ⟨I₁, hI₁'⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ)
    e he₀ he₁ (D 0) (D 1) S 1
  obtain ⟨I₀, hI₀'⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ)
    e he₀ he₁ (D 0) (D 1) S 0
  obtain ⟨O₀, hO₀'⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ)
    f hf₀ hf₁ (H 0) (H 1) T 0
  have hI₁ (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      I₁ (S.smoothToSobolev 1 (Φ (u, v))) =
        ((D 0).smoothToSobolev 1 u, (D 1).smoothToSobolev 1 v) := by
    have h := hI₁' (Φ (u, v))
    change I₁ (S.smoothToSobolev 1 (Φ (u, v))) =
      ((D 0).smoothToSobolev 1 ((Φ.symm (Φ (u, v))).1),
        (D 1).smoothToSobolev 1 ((Φ.symm (Φ (u, v))).2)) at h
    simpa only [Φ.symm_apply_apply] using h
  have hI₀ (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      I₀ (S.smoothToSobolev 0 (Φ (u, v))) =
        ((D 0).smoothToSobolev 0 u, (D 1).smoothToSobolev 0 v) := by
    have h := hI₀' (Φ (u, v))
    change I₀ (S.smoothToSobolev 0 (Φ (u, v))) =
      ((D 0).smoothToSobolev 0 ((Φ.symm (Φ (u, v))).1),
        (D 1).smoothToSobolev 0 ((Φ.symm (Φ (u, v))).2)) at h
    simpa only [Φ.symm_apply_apply] using h
  have hO₀ (u : smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber)
      (v : smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) :
      O₀ (T.smoothToSobolev 0 (Ψ (u, v))) =
        ((H 0).smoothToSobolev 0 u, (H 1).smoothToSobolev 0 v) := by
    have h := hO₀' (Ψ (u, v))
    change O₀ (T.smoothToSobolev 0 (Ψ (u, v))) =
      ((H 0).smoothToSobolev 0 ((Ψ.symm (Ψ (u, v))).1),
        (H 1).smoothToSobolev 0 ((Ψ.symm (Ψ (u, v))).2)) at h
    simpa only [Ψ.symm_apply_apply] using h
  -- Apply the full-symbol elliptic estimate to this actual K at orders one and zero.
  obtain ⟨c, hc, hestimate⟩ := K.exists_estimate_of_isElliptic S T hKell 1 0 (by norm_num)
  let a : ℝ := ‖I₁.toContinuousLinearMap‖
  let b : ℝ := ‖O₀.symm.toContinuousLinearMap‖
  let d : ℝ := ‖I₀.symm.toContinuousLinearMap‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  refine ⟨a * c * (b + d), mul_nonneg (mul_nonneg ha hc) (add_nonneg hb hd), ?_⟩
  intro u
  have hleft : ‖(D 0).smoothToSobolev 1 u‖ ≤ a * ‖S.smoothToSobolev 1 (Φ (u, 0))‖ := by
    have h := I₁.toContinuousLinearMap.le_opNorm (S.smoothToSobolev 1 (Φ (u, 0)))
    simpa only [ContinuousLinearEquiv.coe_coe, hI₁, map_zero, Prod.norm_mk,
      norm_zero, max_eq_left (norm_nonneg _)] using h
  have hzero : ‖S.smoothToSobolev 0 (Φ (u, 0))‖ ≤ d * ‖(D 0).smoothToSobolev 0 u‖ := by
    have h := I₀.symm.toContinuousLinearMap.le_opNorm (I₀ (S.smoothToSobolev 0 (Φ (u, 0))))
    change ‖I₀.symm (I₀ (S.smoothToSobolev 0 (Φ (u, 0))))‖ ≤
      d * ‖I₀ (S.smoothToSobolev 0 (Φ (u, 0)))‖ at h
    rw [I₀.symm_apply_apply] at h
    simpa only [hI₀, map_zero,
      Prod.norm_mk, norm_zero, max_eq_left (norm_nonneg _)] using h
  have houtput : ‖T.smoothToSobolev 0 (K.toLinearMap (Φ (u, 0)))‖ ≤
      b * (‖(H 0).smoothToSobolev 0 (U.toLinearMap u)‖ +
        ‖(H 1).smoothToSobolev 0 (V.toLinearMap u)‖) := by
    have h := O₀.symm.toContinuousLinearMap.le_opNorm
      (O₀ (T.smoothToSobolev 0 (K.toLinearMap (Φ (u, 0)))))
    change ‖O₀.symm (O₀ (T.smoothToSobolev 0 (K.toLinearMap (Φ (u, 0)))))‖ ≤
      b * ‖O₀ (T.smoothToSobolev 0 (K.toLinearMap (Φ (u, 0))))‖ at h
    rw [O₀.symm_apply_apply] at h
    have hvalue : K.toLinearMap (Φ (u, 0)) = Ψ (U.toLinearMap u, V.toLinearMap u) := by
      simpa only [map_zero, sub_zero, add_zero] using hK u 0
    rw [hvalue] at h ⊢
    simp only [hO₀, Prod.norm_mk] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)) hb)
  have hkernel := hestimate (S.smoothToSobolev 1 (Φ (u, 0)))
  have hell : ‖S.smoothToSobolev 1 (Φ (u, 0))‖ ≤
      c * (‖T.smoothToSobolev 0 (K.toLinearMap (Φ (u, 0)))‖ +
        ‖S.smoothToSobolev 0 (Φ (u, 0))‖) := by
    norm_num only [PseudodifferentialOperator.sobolevExtension_smoothToSobolev,
      SmoothBundlePresentation.sobolevInclusion_smoothToSobolev] at hkernel
    rw [show (1 : ℝ) - 1 = 0 by ring] at hkernel
    exact hkernel
  have hbound := hleft.trans (mul_le_mul_of_nonneg_left
    (hell.trans (mul_le_mul_of_nonneg_left (add_le_add houtput hzero) hc)) ha)
  -- Only nonnegative scalar bookkeeping remains after the full operator identity.
  have hscalar (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      a * (c * (b * (y + z) + d * x)) ≤ (a * c * (b + d)) * (x + y + z) := by
    have h₀ : b * (y + z) + d * x ≤ (b + d) * (x + y + z) := by
      nlinarith [mul_nonneg hb hx, mul_nonneg hd hy, mul_nonneg hd hz]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₀ hc) ha).trans_eq
      (by ring)
  exact hbound.trans (hscalar _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _))

end AtiyahSinger
