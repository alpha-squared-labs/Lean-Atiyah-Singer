/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LowConeVerticalEstimate
public import AtiyahSinger.Analysis.RightProductCutoffRealization

import all AtiyahSinger.Analysis.ProductSymbolCutoff

/-!
# The actual right product cutoff is bounded by vertical energy

Public module ID: M0932.

At one fixed positive parameter, the original right-factor regularization has
all spatial jets bounded by the original right-frequency weight. Its scalar
frequency profile is bounded by one and contributes no spatial derivative.
The existing spatial quantization theorem therefore bounds its actual output
by the original L² norm and vertical first derivatives, with no joint H1
error absorption.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff SchwartzMap

variable {n m r s t : ℕ}

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in
-- Keep the full spatial Leibniz estimates and exact original tensor permutations explicit.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified right product cutoff has a bound in the original vertical graph norm. -/
theorem exists_rightProductCutoff_vertical_estimate
    (α : SymbolFunction m (s * r) (t * r)) (hα : IsSymbol univ 1 α)
    (hαK : HasCompactSupport α)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * s))))
        (v : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin (r * t)))),
        (∀ x, v x = quantize (rightProductCutoffSymbol α χ ε) u x) →
        ‖v.toLp 2‖ ^ 2 ≤ C * (‖u.toLp 2‖ ^ 2 +
          ∑ j : Fin m,
            ‖(LineDeriv.lineDerivOp (EuclideanSpace.single (Fin.natAdd n j) (1 : ℝ))
              u).toLp 2‖ ^ 2) := by
  classical
  generalize ha₀ : rightProductCutoffSymbol α χ ε = a₀
  let X := EuclideanSpace ℝ (Fin (n + m))
  let X₁ := EuclideanSpace ℝ (Fin n)
  let X₂ := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℂ (Fin (r * s)) →L[ℂ] EuclideanSpace ℂ (Fin (r * t))
  let split : X ≃L[ℝ] X₁ × X₂ := EuclideanSpace.finAddEquivProd
  let p₁ : X →L[ℝ] X₁ := (ContinuousLinearMap.fst ℝ X₁ X₂).comp split.toContinuousLinearMap
  let p₂ : X →L[ℝ] X₂ := (ContinuousLinearMap.snd ℝ X₁ X₂).comp split.toContinuousLinearMap
  let ei := (tensorCoordinateSwap r s).toContinuousLinearEquiv.toContinuousLinearMap
  let eo := (tensorCoordinateSwap r t).symm.toContinuousLinearEquiv.toContinuousLinearMap
  let Φ : (EuclideanSpace ℂ (Fin (s * r)) →L[ℂ]
      EuclideanSpace ℂ (Fin (t * r))) →L[ℂ] V :=
    LinearMap.toContinuousLinearMap {
      toFun b := eo.comp (b.comp ei)
      map_add' b c := by ext v; simp
      map_smul' z b := by ext v; simp }
  let β : SymbolFunction m (r * s) (r * t) := fun y η ↦ Φ (α y η)
  have hβ : IsSymbol univ 1 β :=
    isSymbol_continuousLinearMap 1 α hα (Φ.restrictScalars ℝ)
  have hβc : ContDiff ℝ ∞ (Function.uncurry β) := by
    simpa only [univ_prod_univ, contDiffOn_univ] using hβ.1
  have hβs (η : X₂) : ContDiff ℝ ∞ (fun y ↦ β y η) :=
    hβc.comp (contDiff_id.prodMk contDiff_const)
  let K : Set X := split.symm '' (tsupport χ ×ˢ tsupport α)
  have hK : IsCompact K := (hχK.prod hαK).image split.symm.continuous
  have hyK (x : X) (hx : x ∈ K) : p₂ x ∈ tsupport α := by
    obtain ⟨z, hz, rfl⟩ := hx
    change (split (split.symm z)).2 ∈ tsupport α
    simpa only [split.apply_symm_apply] using hz.2
  have hswap (x : X) :
      (EuclideanSpace.finAddEquivProd (n := m) (m := n)) (productCoordinateSwap n m x) =
        ((split x).2, (split x).1) := by
    have h := congrArg (EuclideanSpace.finAddEquivProd (n := m) (m := n))
      (productCoordinateSwap_apply n m (split x).1 (split x).2)
    rw [ContinuousLinearEquiv.apply_symm_apply] at h
    change (EuclideanSpace.finAddEquivProd (n := m) (m := n))
      (productCoordinateSwap n m (split.symm (split x))) =
        ((split x).2, (split x).1) at h
    rw [split.symm_apply_apply] at h
    exact h
  let f : X → ℝ := fun ξ ↦ productFrequencyCutoff ε ‖p₂ ξ‖ ‖p₁ ξ‖
  have hf (ξ : X) : 0 ≤ f ξ ∧ f ξ ≤ 1 := by
    have h := productCutoffError_scalar_bound ε ‖p₂ ξ‖ ‖p₁ ξ‖
      (norm_nonneg _) (norm_nonneg _)
    dsimp only [f]
    constructor <;> linarith [h.1, h.2.1]
  let c : X → ℂ := fun x ↦ (χ (p₁ x) : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp (hχ.comp p₁.contDiff)
  have hbase (ξ : X) : ContDiff ℝ ∞ (fun x ↦ c x • β (p₂ x) (p₂ ξ)) :=
    hc.smul ((hβs (p₂ ξ)).comp p₂.contDiff)
  -- Both original tensor permutations and the original frequency cutoff stay in this equality.
  have hformula (x ξ : X) : a₀ x ξ =
      (f ξ : ℂ) • (c x • β (p₂ x) (p₂ ξ)) := by
    rw [← ha₀]
    simp only [rightProductCutoffSymbol, isometricSymbolTransport, productCutoffSymbol,
      liftedProductSymbol, hswap]
    change eo.comp ((((f ξ : ℂ) • ((χ (p₁ x) : ℂ) • α (p₂ x) (p₂ ξ)))).comp ei) = _
    simp only [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rfl
  have hsupport (x : X) (hx : x ∉ K) (ξ : X) :
      a₀ x ξ = 0 := by
    rw [hformula]
    by_cases h₁ : p₁ x ∈ tsupport χ
    · have h₂ : p₂ x ∉ tsupport α := by
        intro h₂
        exact hx ⟨split x, ⟨h₁, h₂⟩, split.symm_apply_apply x⟩
      have hz : α (p₂ x) = 0 := image_eq_zero_of_notMem_tsupport h₂
      simp only [β, hz, Pi.zero_apply, map_zero, smul_zero]
    · simp only [c, image_eq_zero_of_notMem_tsupport h₁, Complex.ofReal_zero, zero_smul,
        smul_zero]
  have hder (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ a₀ y ξ) x‖ ≤
        C * (1 + ‖(EuclideanSpace.finAddEquivProd (n := n) (m := m) ξ).2‖) := by
    -- Every original right-symbol spatial derivative has the same vertical frequency weight.
    have hader (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ x, x ∈ K →
        ‖iteratedFDeriv ℝ j (fun y ↦ β (p₂ y) (p₂ ξ)) x‖ ≤ A * (1 + ‖p₂ ξ‖) := by
      obtain ⟨A, hA, hAb⟩ := hβ.2 (tsupport α) (subset_univ _) hαK j 0
      refine ⟨A * ‖p₂‖ ^ j, by positivity, ?_⟩
      intro ξ x hx
      have hd : ‖iteratedFDeriv ℝ j (fun y ↦ β y (p₂ ξ)) (p₂ x)‖ ≤
          A * (1 + ‖p₂ ξ‖) := by
        have hz : (fun y ↦ iteratedFDeriv ℝ 0 (β y) (p₂ ξ)) =
            (continuousMultilinearCurryFin0 ℝ X₂ V).symm ∘ (fun y ↦ β y (p₂ ξ)) := by
          funext y
          exact congrFun iteratedFDeriv_zero_eq_comp _
        simpa only [symbolDerivative, hz, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
          Nat.cast_zero, sub_zero, Real.rpow_one] using hAb _ (hyK x hx) (p₂ ξ)
      rw [show (fun y ↦ β (p₂ y) (p₂ ξ)) = (fun y ↦ β y (p₂ ξ)) ∘ p₂ from rfl,
        p₂.iteratedFDeriv_comp_right (hβs _) x (by simp)]
      calc
        _ ≤ ‖iteratedFDeriv ℝ j (fun y ↦ β y (p₂ ξ)) (p₂ x)‖ * ‖p₂‖ ^ j := by
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (iteratedFDeriv ℝ j (fun y ↦ β y (p₂ ξ)) (p₂ x)).norm_compContinuousLinearMap_le
              (fun _ ↦ p₂)
        _ ≤ (A * (1 + ‖p₂ ξ‖)) * ‖p₂‖ ^ j := by gcongr
        _ = _ := by ring
    have hcder (j : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K,
        ‖iteratedFDeriv ℝ j c x‖ ≤ B := by
      obtain ⟨B, hB⟩ := (hK.image (hc.continuous_iteratedFDeriv (by simp)).norm).bddAbove
      exact ⟨max B 0, le_max_right _ _, fun x hx ↦
        (hB ⟨x, hx, rfl⟩).trans (le_max_left _ _)⟩
    choose A hA hAb using hader
    choose B hB hBb using hcder
    let C : ℝ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * B j * A (i - j)
    have hC : 0 ≤ C := Finset.sum_nonneg (fun j _ ↦
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB j)) (hA (i - j)))
    refine ⟨C, hC, ?_⟩
    intro ξ x hx
    have hbd : ‖iteratedFDeriv ℝ i (fun y ↦ c y • β (p₂ y) (p₂ ξ)) x‖ ≤
        C * (1 + ‖p₂ ξ‖) := by
      have hle := norm_iteratedFDeriv_smul_le hc ((hβs (p₂ ξ)).comp p₂.contDiff) x
        (n := i) (by simp)
      apply hle.trans
      simp only [C, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hBj := hB j
      calc
        _ ≤ (i.choose j : ℝ) * B j * (A (i - j) * (1 + ‖p₂ ξ‖)) := by
          gcongr
          · exact hBb j x hx
          · exact hAb (i - j) ξ x hx
        _ = _ := by ring
    simp_rw [hformula]
    rw [iteratedFDeriv_const_smul_apply' ((hbase ξ).contDiffAt.of_le (by simp)),
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf ξ).1]
    exact (mul_le_mul_of_nonneg_left hbd (hf ξ).1).trans
      ((mul_le_mul_of_nonneg_right (hf ξ).2 (mul_nonneg hC (by positivity))).trans_eq
        (one_mul _))
  have hfull : ContDiff ℝ ∞ (Function.uncurry a₀) := by
    rw [← ha₀]
    simpa only [univ_prod_univ, contDiffOn_univ] using
      (isSymbol_rightProductCutoffSymbol α hα χ hχ ε hε).1
  have hmeas : StronglyMeasurable (Function.uncurry a₀) :=
    hfull.continuous.stronglyMeasurable
  have hsmooth (ξ : X) : ContDiff ℝ ∞ (fun x ↦ a₀ x ξ) :=
    hfull.comp (contDiff_id.prodMk contDiff_const)
  exact exists_quantize_vertical_estimate_of_spatial_bounds
    (n := n) (m := m) (r := r * s) (q := r * t)
    a₀ hmeas hsmooth K hK hsupport hder

end AtiyahSinger
