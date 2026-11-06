/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ProductSchwartzCutoffRealization
public import AtiyahSinger.Analysis.SchwartzTensorDensity

/-!
# The full Schwartz action of a factorwise lifted symbol

Public module ID: M0881.

The original product Fourier integral equals the original first-factor
quantization of the exact Schwartz slice. Both sides are continuous linear
functionals on the full Schwartz space. The established separated formula
and full Schwartz tensor density therefore identify them on arbitrary data.
This supplies the Fourier comparison for compact associated-bundle coordinates.

Source: Fourier factorization and inversion in the original SG normalization.
No joint symbol estimate is asserted for the unregularized lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 1000000 in
-- Keep the fixed product coordinate equivalence in both the Fourier and slice maps.
set_option backward.isDefEq.respectTransparency false in
/-- The lifted Fourier integral acts on every Schwartz function by its exact factor slice. -/
theorem quantize_liftedProductSymbol_eq_slice
    {n m r q : ℕ} (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ)
    (w : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)))
    (y : EuclideanSpace ℝ (Fin m))
    (f : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hf : ∀ t, f t = w (EuclideanSpace.finAddEquivProd.symm (t, y)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (liftedProductSymbol a χ) w (EuclideanSpace.finAddEquivProd.symm (x, y)) =
      (χ y : ℂ) • quantize a f x := by
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let U := EuclideanSpace ℂ (Fin r)
  let V := EuclideanSpace ℂ (Fin q)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let z := e.symm (x, y)
  -- At the fixed spatial point the lifted frequency multiplier has temperate growth.
  have hfrequency (t : X) : (a t).HasTemperateGrowth := by
    refine ⟨?_, ?_⟩
    · have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
      exact hs.comp (contDiff_const.prodMk contDiff_id)
    · intro j
      obtain ⟨C, hC, hbound⟩ := ha.2 {t} (Set.subset_univ _) isCompact_singleton 0 j
      refine ⟨⌈(1 : ℝ) - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
      have h := hbound t (Set.mem_singleton t) ξ
      simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hC
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
  let p : Z →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp e.toContinuousLinearMap
  have hb : (liftedProductSymbol a χ z).HasTemperateGrowth := by
    change (fun ξ ↦ (χ (e z).2 : ℂ) • a (e z).1 (p ξ)).HasTemperateGrowth
    exact (Function.HasTemperateGrowth.const (χ (e z).2 : ℂ)).smul
      ((hfrequency (e z).1).comp p.hasTemperateGrowth)
  have hphase : (fun ξ : Z ↦
      Complex.exp (Complex.I * (inner ℝ z ξ : ℂ))).HasTemperateGrowth := by
    simpa [Function.comp_def, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ z).hasTemperateGrowth
  have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  let d : Z ≃L[ℝ] Z :=
    (LinearEquiv.smulOfNeZero ℝ Z ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
  let F := (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d).comp
    (FourierTransform.fourierCLM ℂ (SchwartzMap Z U))
  let A := SchwartzMap.bilinLeftCLM
    (ContinuousLinearMap.id ℂ (U →L[ℂ] V)).flip (hphase.smul hb)
  let Q : 𝓢(Z, U) →L[ℂ] V :=
    ((2 * Real.pi) ^ (n + m))⁻¹ • (SchwartzMap.integralCLM ℂ volume).comp (A.comp F)
  have hQ (u : 𝓢(Z, U)) : Q u = quantize (liftedProductSymbol a χ) u z := by
    rfl
  -- The affine slice is proper and temperate, hence continuous in the full Schwartz topology.
  have hg : (fun t : X ↦ (t, y)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inl ℝ X Y).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const ((0 : X), y)) using 1
    funext t
    simp
  let S₀ : 𝓢(X × Y, U) →L[ℂ] 𝓢(X, U) :=
    SchwartzMap.compCLM ℂ hg ⟨1, 1, fun t ↦ by
      simpa only [one_mul, pow_one] using
        (norm_fst_le (t, y)).trans (le_add_of_nonneg_left zero_le_one)⟩
  let S := S₀.comp (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
  have hS (u : 𝓢(Z, U)) (t : X) : S u t = u (e.symm (t, y)) := rfl
  let R : 𝓢(Z, U) →L[ℂ] V := (χ y : ℂ) •
    (((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X V)).comp
        ((quantizeSchwartz 1 a ha haK).comp S))
  have hR (u : 𝓢(Z, U)) : R u = (χ y : ℂ) • quantize a (S u) x := by
    exact congrArg ((χ y : ℂ) • ·) (quantizeSchwartz_apply 1 a ha haK (S u) x)
  -- The known separated formula identifies the two actual continuous functionals.
  have hseparated (u : 𝓢(X, U)) (v : 𝓢(Y, ℂ)) (t : 𝓢(Z, U))
      (ht : ∀ s t', t (e.symm (s, t')) = v t' • u s) : Q t = R t := by
    have hSt : S t = v y • u := by
      apply SchwartzMap.ext
      intro s
      exact (hS t s).trans (ht s y)
    rw [hQ, hR]
    rw [quantize_liftedProductSymbol a χ u v t ht x y]
    rw [hSt, ← quantizeSchwartz_apply 1 a ha haK (v y • u) x, map_smul]
    simp only [smul_apply, smul_smul, quantizeSchwartz_apply]
    rfl
  let lift (v : U) : 𝓢(Z, ℂ) →L[ℂ] 𝓢(Z, U) :=
    SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v)
  have hscalar (v : U) (t : 𝓢(Z, ℂ)) : Q (lift v t) = R (lift v t) := by
    apply (dense_span_schwartz_products n m).induction
      (P := fun t : 𝓢(Z, ℂ) ↦ Q (lift v t) = R (lift v t))
      (fun t ht ↦ ?_) (isClosed_eq (Q.comp (lift v)).continuous
        (R.comp (lift v)).continuous) t
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨u, u', hprod⟩ := ht
      let u₀ := SchwartzMap.postcompCLM ((ContinuousLinearMap.id ℂ ℂ).smulRight v) u
      apply hseparated u₀ u' (lift v t)
      intro s s'
      change t (e.symm (s, s')) • v = u' s' • (u s • v)
      rw [hprod, e.apply_symm_apply, smul_smul, mul_comm]
    | zero => simp only [map_zero]
    | add t t' ht ht' htt htt' => simp only [map_add, htt, htt']
    | smul c t ht htt => simp only [map_smul, htt]
  -- Resolve the original finite coefficient fiber without changing its coordinates.
  let f₀ (j : Fin r) := SchwartzMap.postcompCLM (EuclideanSpace.proj (𝕜 := ℂ) j) w
  have hsum : w = ∑ j : Fin r, lift (EuclideanSpace.single j 1) (f₀ j) := by
    apply SchwartzMap.ext
    intro s
    simp only [sum_apply]
    change w s = ∑ j : Fin r, f₀ j s • EuclideanSpace.single j 1
    symm
    have hproj (j : Fin r) (v : U) : (EuclideanSpace.proj (𝕜 := ℂ) j) v = v j := rfl
    simpa only [f₀, SchwartzMap.postcompCLM_apply, hproj,
      OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.coe_toBasis,
      EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.sum_repr (w s)
  have heq : Q w = R w := by
    rw [hsum, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ hscalar _ _)
  have hSf : S w = f := by
    apply SchwartzMap.ext
    intro t
    exact (hS w t).trans (hf t).symm
  simpa only [hQ, hR, hSf] using heq

end AtiyahSinger
