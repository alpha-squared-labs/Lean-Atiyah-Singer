/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedTensorGlobalSymbol

/-!
# The formal adjoint of a graded bundle operator

Public module ID: M0708.

For the specified native graded operator and orthogonal sum metrics, the
four corner adjunction identities determine its formal-adjoint matrix.
The reverse matrix has the upper-right block added and the lower-left
block negated. Its smooth action is identified with the formal adjoint
of the same supplied operator K.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

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

set_option maxHeartbeats 1600000 in
-- Normalize the literal graded matrix adjoint in the original orthogonal sum coordinates.
/-- The reverse smooth matrix is the literal formal adjoint of the same native graded PDO. -/
theorem graded_metricFormalAdjoint_call
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
    (hA : ∀ i, SmoothHermitianMetric (n := n) (r := (A i).rank) (A i).Fiber)
    (hB : ∀ i, SmoothHermitianMetric (n := n) (r := (B i).rank) (B i).Fiber)
    {m : ℝ}
    (U₀ : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber μ m)
    (V₀ : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber μ m)
    (U₁ : PseudodifferentialOperator (n := n) (r := (B 1).rank) (q := (A 1).rank)
      (B 1).Fiber (A 1).Fiber μ m)
    (V₁ : PseudodifferentialOperator (n := n) (r := (B 0).rank) (q := (A 1).rank)
      (B 0).Fiber (A 1).Fiber μ m)
    (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ m)
    (hK : ∀ u v, K.toLinearMap (smoothSectionSumEquiv e he₀ he₁ (u, v)) =
      smoothSectionSumEquiv f hf₀ hf₁
        (U₀.toLinearMap u - (V₁.metricFormalAdjoint (hB 0) (hA 1)).toLinearMap v,
          V₀.toLinearMap u + (U₁.metricFormalAdjoint (hB 1) (hA 1)).toLinearMap v))
    (hE : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
    (hF : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (hEpair : ∀ x u v, hE.pairing x (e x u) (e x v) =
      (hA 0).pairing x u.1 v.1 + (hA 1).pairing x u.2 v.2)
    (hFpair : ∀ x u v, hF.pairing x (f x u) (f x v) =
      (hB 0).pairing x u.1 v.1 + (hB 1).pairing x u.2 v.2) :
    ∀ u v, (K.metricFormalAdjoint hE hF).toLinearMap
      (smoothSectionSumEquiv f hf₀ hf₁ (u, v)) =
        smoothSectionSumEquiv e he₀ he₁
          ((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap u +
            (V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap v,
            -V₁.toLinearMap u + U₁.toLinearMap v) := by
  classical
  let Φ := smoothSectionSumEquiv e he₀ he₁
  let Ψ := smoothSectionSumEquiv f hf₀ hf₁
  let rev := Φ.toLinearMap.comp
    ((((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap.coprod
      (V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap).prod
        ((-V₁.toLinearMap).coprod U₁.toLinearMap)).comp Ψ.symm.toLinearMap)
  have hrevApply
      (x : smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber)
      (y : smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) :
      rev (Ψ (x, y)) = Φ
        ((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap x +
          (V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap y,
          -V₁.toLinearMap x + U₁.toLinearMap y) := by
    simp only [rev, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply,
      LinearMap.neg_apply]
  -- Integrate the two literal orthogonal pairings on the same smooth sum coordinates.
  have hΦ (u v : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber ×
      smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      hE.sectionPairing μ (Φ u) (Φ v) =
        (hA 0).sectionPairing μ u.1 v.1 + (hA 1).sectionPairing μ u.2 v.2 := by
    unfold SmoothHermitianMetric.sectionPairing
    rw [← integral_add ((hA 0).integrable_pairing μ u.1 v.1)
      ((hA 1).integrable_pairing μ u.2 v.2)]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [Φ, Ψ]
    rw [smoothSectionSumEquiv_apply, smoothSectionSumEquiv_apply]
    exact hEpair x (u.1.val x, u.2.val x) (v.1.val x, v.2.val x)
  have hΨ (u v : smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber ×
      smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) :
      hF.sectionPairing μ (Ψ u) (Ψ v) =
        (hB 0).sectionPairing μ u.1 v.1 + (hB 1).sectionPairing μ u.2 v.2 := by
    unfold SmoothHermitianMetric.sectionPairing
    rw [← integral_add ((hB 0).integrable_pairing μ u.1 v.1)
      ((hB 1).integrable_pairing μ u.2 v.2)]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [Φ, Ψ]
    rw [smoothSectionSumEquiv_apply, smoothSectionSumEquiv_apply]
    exact hFpair x (u.1.val x, u.2.val x) (v.1.val x, v.2.val x)
  -- The four original corner identities give the reverse matrix, including its minus sign.
  have hrev : IsMetricFormalAdjoint hE hF μ K.toLinearMap rev := by
    intro w t
    obtain ⟨⟨u, v⟩, rfl⟩ := Φ.surjective w
    obtain ⟨⟨x, y⟩, rfl⟩ := Ψ.surjective t
    rw [hK, hΨ]
    rw [hrevApply]
    rw [hΦ]
    let cA₀ := (hA 0).smoothL2SectionCore μ
    let cA₁ := (hA 1).smoothL2SectionCore μ
    let cB₀ := (hB 0).smoothL2SectionCore μ
    let cB₁ := (hB 1).smoothL2SectionCore μ
    change cB₀.inner
        (U₀.toLinearMap u - (V₁.metricFormalAdjoint (hB 0) (hA 1)).toLinearMap v) x +
      cB₁.inner
        (V₀.toLinearMap u + (U₁.metricFormalAdjoint (hB 1) (hA 1)).toLinearMap v) y =
      cA₀.inner u ((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap x +
        (V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap y) +
      cA₁.inner v (-V₁.toLinearMap x + U₁.toLinearMap y)
    rw [InnerProductSpace.Core.inner_sub_left, InnerProductSpace.Core.inner_add_left,
      InnerProductSpace.Core.inner_add_right, InnerProductSpace.Core.inner_add_right,
      InnerProductSpace.Core.inner_neg_right]
    change ((hB 0).sectionPairing μ (U₀.toLinearMap u) x -
        (hB 0).sectionPairing μ
          ((V₁.metricFormalAdjoint (hB 0) (hA 1)).toLinearMap v) x) +
      ((hB 1).sectionPairing μ (V₀.toLinearMap u) y +
        (hB 1).sectionPairing μ
          ((U₁.metricFormalAdjoint (hB 1) (hA 1)).toLinearMap v) y) = _
    rw [U₀.isMetricFormalAdjoint_metricFormalAdjoint (hA 0) (hB 0),
      V₀.isMetricFormalAdjoint_metricFormalAdjoint (hA 0) (hB 1),
      (V₁.isMetricFormalAdjoint_metricFormalAdjoint (hB 0) (hA 1)).symm,
      (U₁.isMetricFormalAdjoint_metricFormalAdjoint (hB 1) (hA 1)).symm]
    change
      ((hA 0).sectionPairing μ u
          ((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap x) -
        (hA 1).sectionPairing μ v (V₁.toLinearMap x)) +
      ((hA 0).sectionPairing μ u
          ((V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap y) +
        (hA 1).sectionPairing μ v (U₁.toLinearMap y)) =
      ((hA 0).sectionPairing μ u
          ((U₀.metricFormalAdjoint (hA 0) (hB 0)).toLinearMap x) +
        (hA 0).sectionPairing μ u
          ((V₀.metricFormalAdjoint (hA 0) (hB 1)).toLinearMap y)) +
      (-(hA 1).sectionPairing μ v (V₁.toLinearMap x) +
        (hA 1).sectionPairing μ v (U₁.toLinearMap y))
    ring
  have heq := (K.isMetricFormalAdjoint_metricFormalAdjoint hE hF).unique hrev
  intro u v
  rw [heq]
  exact hrevApply u v

end AtiyahSinger
