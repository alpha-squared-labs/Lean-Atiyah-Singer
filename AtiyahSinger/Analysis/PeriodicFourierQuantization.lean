/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.PeriodicFourierAction

/-!
# The exact periodic projection in Euclidean line coordinates

Public module ID: M0854.

The scalar period-one Fourier action is transported through the canonical
orthonormal coordinates of the real and complex lines. The SG frequency
rescaling is explicit, so the resulting action has the original normalization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap Topology

set_option maxHeartbeats 800000 in

/-- Exact local Fourier series of the matrix quantization, in the original line coordinates. -/
theorem quantize_periodicProjectionMatrixSymbol (ψ φ : 𝓢(ℝ, ℂ))
    (u : 𝓢(EuclideanSpace ℝ (Fin 1), EuclideanSpace ℂ (Fin 1)))
    (x : EuclideanSpace ℝ (Fin 1)) :
    let l := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    let e := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm
    let v := SchwartzMap.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l.symm.toContinuousLinearEquiv u)
    e (quantize (periodicProjectionMatrixSymbol ψ φ) u x) =
      ψ (l x) * ∑' n : ℕ, (Real.fourierChar (l x * (n : ℝ)) : ℂ) *
        (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ v)) (n : ℝ) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  dsimp only
  let l : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let e : EuclideanSpace ℂ (Fin 1) ≃ₗᵢ[ℂ] ℂ :=
    (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm
  let v : 𝓢(ℝ, ℂ) :=
    SchwartzMap.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l.symm.toContinuousLinearEquiv u)
  change e (quantize (periodicProjectionMatrixSymbol ψ φ) u x) =
    ψ (l x) * ∑' n : ℕ, (Real.fourierChar (l x * (n : ℝ)) : ℂ) *
      (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ v)) (n : ℝ)
  -- Both orthonormal coordinate changes preserve the precise Fourier transform.
  have hv (t : ℝ) : v t = e (u (l.symm t)) := rfl
  have heint {D : Type} [MeasureSpace D]
      (f : D → EuclideanSpace ℂ (Fin 1)) :
      e (∫ t, f t) = ∫ t, e (f t) :=
    (e.toLinearIsometry.integral_comp_comm f).symm
  have hFourier (η : ℝ) : (𝓕 v) η = e ((𝓕 u) (l.symm η)) := by
    rw [SchwartzMap.fourier_coe]
    calc
      _ = e (𝓕 ((u : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℂ (Fin 1)) ∘
          l.symm) η) := by
        rw [Real.fourier_eq, Real.fourier_eq, heint]
        apply integral_congr_ae
        filter_upwards with t
        simp only [hv, Function.comp_apply, Circle.smul_def, map_smul, smul_eq_mul]
      _ = _ := by rw [Real.fourier_comp_linearIsometry, SchwartzMap.fourier_coe]
  -- Rescale SG frequency and then apply the measure-preserving real coordinate.
  rw [quantize_rescaled, heint,
    ← l.symm.measurePreserving.integral_comp l.symm.toHomeomorph.measurableEmbedding]
  rw [← periodicProjectionSymbol_integral ψ φ v (l x)]
  apply integral_congr_ae
  filter_upwards with η
  have hscale : l ((2 * Real.pi) • l.symm η) / (2 * Real.pi) = η := by
    rw [map_smul, l.apply_symm_apply, smul_eq_mul]
    exact mul_div_cancel_left₀ η (by positivity)
  have hinner : inner ℝ x (l.symm η) = l x * η := by
    rw [← l.inner_map_map, l.apply_symm_apply]
    change η * l x = l x * η
    exact mul_comm _ _
  have hphase : Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x (l.symm η) : ℂ)) =
      (Real.fourierChar (l x * η) : ℂ) := by
    rw [Real.fourierChar_apply, hinner]
    congr 1
    push_cast
    ring
  simp only [periodicProjectionMatrixSymbol, smul_apply,
    ContinuousLinearMap.id_apply]
  rw [hscale, hphase, map_smul, map_smul, ← hFourier]
  simp only [smul_eq_mul, mul_assoc]
  rfl

/-- Compact output cutoff support gives compact spatial support of the whole matrix symbol. -/
theorem hasCompactSupport_periodicProjectionMatrixSymbol (ψ φ : 𝓢(ℝ, ℂ))
    (hψ : HasCompactSupport (ψ : ℝ → ℂ)) :
    HasCompactSupport (periodicProjectionMatrixSymbol ψ φ) := by
  let l : EuclideanSpace ℝ (Fin 1) ≃ₗᵢ[ℝ] ℝ :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  have hK : IsCompact (l ⁻¹' tsupport ψ) := by
    convert hψ.image l.symm.continuous using 1
    ext x
    constructor
    · intro hx
      exact ⟨l x, hx, l.symm_apply_apply x⟩
    · rintro ⟨t, ht, rfl⟩
      simpa only [Set.mem_preimage, l.apply_symm_apply] using ht
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ ((isClosed_tsupport ψ).preimage l.continuous)
  intro x hx
  by_contra h
  have hz : ψ (l x) = 0 := image_eq_zero_of_notMem_tsupport h
  apply hx
  funext ξ
  have hz' : ψ ((OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm x) = 0 := hz
  simp only [periodicProjectionMatrixSymbol, periodicProjectionSymbol, hz',
    zero_mul, tsum_zero, zero_smul, Pi.zero_apply]

/-- The actual periodic quantization has both output support and annihilation of disjoint inputs. -/
theorem hasOperatorSupport_periodicProjectionQuantization (ψ φ : 𝓢(ℝ, ℂ))
    (P : 𝓢(EuclideanSpace ℝ (Fin 1), EuclideanSpace ℂ (Fin 1)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin 1), EuclideanSpace ℂ (Fin 1)))
    (hP : ∀ u x, P u x = quantize (periodicProjectionMatrixSymbol ψ φ) u x) :
    let l := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
    HasOperatorSupport (l ⁻¹' (tsupport ψ ∪ tsupport φ)) P := by
  classical
  let X := EuclideanSpace ℝ (Fin 1)
  let Y := EuclideanSpace ℂ (Fin 1)
  let l : X ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let e : Y ≃ₗᵢ[ℂ] ℂ := (OrthonormalBasis.singleton (Fin 1) ℂ).repr.symm
  let K := l ⁻¹' (tsupport ψ ∪ tsupport φ)
  let v (u : 𝓢(X, Y)) : 𝓢(ℝ, ℂ) :=
    SchwartzMap.postcompCLM e.toContinuousLinearEquiv.toContinuousLinearMap
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l.symm.toContinuousLinearEquiv u)
  have hv (u : 𝓢(X, Y)) (t : ℝ) : v u t = e (u (l.symm t)) := rfl
  have hact (u : 𝓢(X, Y)) (x : X) : e (P u x) =
      ψ (l x) * ∑' n : ℕ, (Real.fourierChar (l x * (n : ℝ)) : ℂ) *
        (𝓕 (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ (v u))) (n : ℝ) := by
    rw [hP]
    exact quantize_periodicProjectionMatrixSymbol ψ φ u x
  change HasOperatorSupport K P
  constructor
  · -- The exact action is zero away from the original output cutoff.
    intro u
    apply closure_minimal ?_
      (((isClosed_tsupport ψ).union (isClosed_tsupport φ)).preimage l.continuous)
    intro x hx
    by_contra hxK
    have hψx : ψ (l x) = 0 := image_eq_zero_of_notMem_tsupport
      (fun h ↦ hxK (Or.inl h))
    apply hx
    apply e.injective
    rw [map_zero, hact, hψx, zero_mul]
  · -- Disjoint input support makes the same localized scalar input identically zero.
    intro u hu
    have hproduct : SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) φ (v u) = 0 := by
      apply SchwartzMap.ext
      intro t
      change φ t * v u t = 0
      by_cases hφt : φ t = 0
      · rw [hφt, zero_mul]
      · have htK : l.symm t ∈ K := by
          change l (l.symm t) ∈ tsupport ψ ∪ tsupport φ
          rw [l.apply_symm_apply]
          exact Or.inr (subset_tsupport φ hφt)
        have ht : l.symm t ∉ tsupport u := fun h ↦ Set.disjoint_left.mp hu h htK
        rw [hv, image_eq_zero_of_notMem_tsupport ht, map_zero, mul_zero]
    apply SchwartzMap.ext
    intro x
    change P u x = 0
    apply e.injective
    rw [map_zero, hact, hproduct]
    simp

end AtiyahSinger
