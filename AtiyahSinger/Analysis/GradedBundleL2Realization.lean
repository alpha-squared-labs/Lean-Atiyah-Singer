/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# The native graded operator in fixed integral output coordinates

Public module ID: M0693.

The same four smooth operator blocks determine the whole bounded Sobolev-to-L2
matrix in any specified sum coordinates with the original smooth formulas.
In particular, these coordinate equivalences can be fixed before a cutoff
parameter is chosen; no new coordinate or norm choice is made for each PDO.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : Fin 2 → SmoothFiniteComplexBundle (n := n) M)

set_option maxHeartbeats 1000000 in
-- Normalize the four original Sobolev blocks and their common dense smooth image.
/-- The same graded smooth matrix has its literal L2 matrix in the specified fixed coordinates. -/
theorem gradedBundleL2Realization_eq
    {m : ℝ}
    (U : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber μ m)
    (V : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber μ m)
    (W : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 0).rank)
      (A 1).Fiber (B 0).Fiber μ m)
    (Z : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 1).rank)
      (A 1).Fiber (B 1).Fiber μ m)
    (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ m)
    (Φ : (smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber ×
        smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) ≃ₗ[ℂ]
      smoothSections (n := n) (r := E.rank) E.Fiber)
    (Ψ : (smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber ×
        smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) ≃ₗ[ℂ]
      smoothSections (n := n) (r := F.rank) F.Fiber)
    (hK : ∀ u v, K.toLinearMap (Φ (u, v)) =
      Ψ (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v))
    (D : (i : Fin 2) → SmoothBundlePresentation (n := n) (r := (A i).rank) (A i).Fiber)
    (H : (j : Fin 2) → SmoothBundlePresentation (n := n) (r := (B j).rank) (B j).Fiber)
    (S : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
    (T : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber)
    (k₀ : SmoothHermitianMetric (n := n) (r := (B 0).rank) (B 0).Fiber)
    (k₁ : SmoothHermitianMetric (n := n) (r := (B 1).rank) (B 1).Fiber)
    (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
    (s : ℝ) (hs : 0 ≤ s - m)
    (I : S.SobolevSpace s ≃L[ℂ] WithLp 2 ((D 0).SobolevSpace s × (D 1).SobolevSpace s))
    (O : k.L2SectionSpace μ ≃L[ℂ] WithLp 2 (k₀.L2SectionSpace μ × k₁.L2SectionSpace μ))
    (hI : ∀ u v, I (S.smoothToSobolev s (Φ (u, v))) =
      WithLp.toLp 2 ((D 0).smoothToSobolev s u, (D 1).smoothToSobolev s v))
    (hO : ∀ u v, O (k.smoothToL2 μ (Ψ (u, v))) =
      WithLp.toLp 2 (k₀.smoothToL2 μ u, k₁.smoothToL2 μ v)) :
    O.toContinuousLinearMap.comp ((k.sobolevZeroEquivL2 (μ := μ) T).toContinuousLinearMap.comp
      (K.sobolevRealization S T s 0 hs)) =
      (gradedBlockOperator
        ((k₀.sobolevZeroEquivL2 (μ := μ) (H 0)).toContinuousLinearMap.comp
          (U.sobolevRealization (D 0) (H 0) s 0 hs))
        ((k₁.sobolevZeroEquivL2 (μ := μ) (H 1)).toContinuousLinearMap.comp
          (V.sobolevRealization (D 0) (H 1) s 0 hs))
        ((k₀.sobolevZeroEquivL2 (μ := μ) (H 0)).toContinuousLinearMap.comp
          (W.sobolevRealization (D 1) (H 0) s 0 hs))
        ((k₁.sobolevZeroEquivL2 (μ := μ) (H 1)).toContinuousLinearMap.comp
          (Z.sobolevRealization (D 1) (H 1) s 0 hs))).comp I.toContinuousLinearMap := by
  -- Compare values on the same dense native smooth image in the chosen Sobolev domain.
  apply DFunLike.coe_injective
  apply (S.denseRange_smoothToSobolev s).equalizer
    (O.toContinuousLinearMap.comp
      ((k.sobolevZeroEquivL2 (μ := μ) T).toContinuousLinearMap.comp
        (K.sobolevRealization S T s 0 hs))).continuous
    (((gradedBlockOperator _ _ _ _).comp I.toContinuousLinearMap).continuous)
  funext u
  obtain ⟨⟨u, v⟩, rfl⟩ := Φ.surjective u
  change O (k.sobolevZeroEquivL2 T
    (K.sobolevRealization S T s 0 hs (S.smoothToSobolev s (Φ (u, v))))) = _
  rw [K.sobolevRealization_smoothToSobolev, k.sobolevZeroEquivL2_smooth, hK, hO]
  change _ = gradedBlockOperator _ _ _ _ (I (S.smoothToSobolev s (Φ (u, v))))
  rw [hI]
  apply WithLp.ofLp_injective
  change (k₀.smoothToL2 μ (U.toLinearMap u - W.toLinearMap v),
      k₁.smoothToL2 μ (V.toLinearMap u + Z.toLinearMap v)) =
    (k₀.sobolevZeroEquivL2 (H 0)
        (U.sobolevRealization (D 0) (H 0) s 0 hs ((D 0).smoothToSobolev s u)) +
      -(k₀.sobolevZeroEquivL2 (H 0)
        (W.sobolevRealization (D 1) (H 0) s 0 hs ((D 1).smoothToSobolev s v))),
      k₁.sobolevZeroEquivL2 (H 1)
        (V.sobolevRealization (D 0) (H 1) s 0 hs ((D 0).smoothToSobolev s u)) +
      k₁.sobolevZeroEquivL2 (H 1)
        (Z.sobolevRealization (D 1) (H 1) s 0 hs ((D 1).smoothToSobolev s v)))
  -- The upper-right minus sign is the original signed graded block, before and after completion.
  simp only [PseudodifferentialOperator.sobolevRealization_smoothToSobolev,
    SmoothHermitianMetric.sobolevZeroEquivL2_smooth, map_add, map_neg, sub_eq_add_neg]

end AtiyahSinger
