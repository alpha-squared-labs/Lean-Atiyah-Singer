/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.ProductFourierFactorization

/-!
# Actual operators for the product-frequency cutoff

Public module ID: M0877.

The positive-parameter cutoff is quantized on the original Schwartz space.
Its difference from the unregularized factorwise lift is the same Fourier
integral used to define the existing bounded error operator. This comparison
retains the frequency normalization and is needed before assembling the local
operator-norm estimates on a finite bundle atlas.

Source: the frequency regularization in SG III.13.5, p.250. The lifted symbol
has temperate frequency growth but need not satisfy joint symbol estimates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n m r q : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin m)
local notation "Z" => EuclideanSpace ℝ (Fin (n + m))
local notation "U" => EuclideanSpace ℂ (Fin r)
local notation "V" => EuclideanSpace ℂ (Fin q)

/-- The same compact product control supports every parameter of the cutoff symbol. -/
theorem hasCompactSupport_productCutoffSymbol (a : SymbolFunction n r q)
    (ha : HasCompactSupport a) (χ : Y → ℝ) (hχ : HasCompactSupport χ) (ε : ℝ) :
    HasCompactSupport (productCutoffSymbol a χ ε) := by
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let K := e.symm '' (tsupport a ×ˢ tsupport χ)
  have hK : IsCompact K := (ha.prod hχ).image e.symm.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal ?_ hK.isClosed
  intro x hx
  have hleft : (e x).1 ∈ tsupport a := by
    by_contra h
    apply hx
    have hz := image_eq_zero_of_notMem_tsupport h
    funext ξ
    simp only [productCutoffSymbol, liftedProductSymbol]
    change _ • ((χ (e x).2 : ℂ) • a (e x).1 (e ξ).1) = 0
    rw [hz]
    simp
  have hright : (e x).2 ∈ tsupport χ := by
    by_contra h
    apply hx
    have hz := image_eq_zero_of_notMem_tsupport h
    funext ξ
    simp only [productCutoffSymbol, liftedProductSymbol]
    change _ • ((χ (e x).2 : ℂ) • a (e x).1 (e ξ).1) = 0
    rw [hz]
    simp
  exact ⟨e x, ⟨hleft, hright⟩, e.symm_apply_apply x⟩

/-- The cutoff error integral is exactly the difference of the original two quantizations. -/
theorem quantize_productCutoffErrorSymbol (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (χ : Y → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (ε : ℝ) (hε : 0 < ε) (u : 𝓢(Z, U)) (x : Z) :
    quantize (productCutoffErrorSymbol a χ ε) u x =
      quantize (liftedProductSymbol a χ) u x -
        quantize (productCutoffSymbol a χ ε) u x := by
  -- Each fixed spatial slice has temperate frequency growth. The lift only needs
  -- that weaker property; no false joint-symbol estimate is imposed on it.
  have hfrequency {d : ℕ} (b : SymbolFunction d r q) (hb : IsSymbol Set.univ 1 b)
      (y : EuclideanSpace ℝ (Fin d)) : (b y).HasTemperateGrowth := by
    refine ⟨?_, ?_⟩
    · have hs : ContDiff ℝ ∞ (Function.uncurry b) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
      exact hs.comp (contDiff_const.prodMk contDiff_id)
    · intro j
      obtain ⟨C, hC, hbound⟩ := hb.2 {y} (Set.subset_univ _) isCompact_singleton 0 j
      refine ⟨⌈(1 : ℝ) - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
      have h := hbound y (Set.mem_singleton y) ξ
      simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
      apply h.trans
      apply mul_le_mul_of_nonneg_left _ hC
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let p : Z →L[ℝ] X := (ContinuousLinearMap.fst ℝ X Y).comp e.toContinuousLinearMap
  have hlift : (liftedProductSymbol a χ x).HasTemperateGrowth := by
    change (fun ξ ↦ (χ (e x).2 : ℂ) • a (e x).1 (p ξ)).HasTemperateGrowth
    exact (Function.HasTemperateGrowth.const (χ (e x).2 : ℂ)).smul
      ((hfrequency a ha (e x).1).comp p.hasTemperateGrowth)
  have hcut : (productCutoffSymbol a χ ε x).HasTemperateGrowth :=
    hfrequency _ (isSymbol_productCutoffSymbol a ha χ hχ ε hε) x
  -- Temperate multiplication of a Schwartz Fourier transform is integrable.
  have hInt (b : Z → U →L[ℂ] V) (hb : b.HasTemperateGrowth) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        b ξ (fourierSG u ξ)) := by
    have hphase : (fun ξ : Z ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let d : Z ≃L[ℝ] Z :=
      (LinearEquiv.smulOfNeZero ℝ Z ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (𝓕 u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (U →L[ℂ] V)).flip (hphase.smul hb) w).integrable
  simp only [quantize, productCutoffErrorSymbol, Pi.sub_apply, sub_apply, smul_sub]
  rw [integral_sub (hInt _ hlift) (hInt _ hcut), smul_sub]

/-- Positive cutoffs have a unique realization on the original first Bessel coordinates. -/
theorem existsUnique_productCutoffSobolevOperator (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : Y → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃! T : Lp U 2 (volume : Measure Z) →L[ℂ] Lp V 2 (volume : Measure Z),
      ∀ (u : 𝓢(Z, U)) (φ : 𝓢(Z, ℂ)),
        besselRealization (n + m) q 0 (T (schwartzSobolevCoordinate 1 u)) φ =
          ∫ x, φ x • quantize (productCutoffSymbol a χ ε) u x := by
  have hsym := isSymbol_productCutoffSymbol a ha χ hχ ε hε
  have hK := hasCompactSupport_productCutoffSymbol a haK χ hχK ε
  -- Apply the existing compact-symbol realization to this very cutoff symbol.
  obtain ⟨T, hT⟩ := exists_quantize_sobolev_extension 1 1 _ hsym _ hK
    (fun x hx ξ ↦ congrFun (image_eq_zero_of_notMem_tsupport hx) ξ)
  have hT' : ∀ (u : 𝓢(Z, U)) (φ : 𝓢(Z, ℂ)),
      besselRealization (n + m) q 0 (T (schwartzSobolevCoordinate 1 u)) φ =
        ∫ x, φ x • quantize (productCutoffSymbol a χ ε) u x := by
    simpa only [sub_self] using hT
  refine ⟨T, hT', ?_⟩
  intro S hS
  -- Distributional equality determines the Bessel value, and the same Schwartz
  -- coordinates are dense in the entire original Hilbert domain.
  have heq (u : 𝓢(Z, U)) : S (schwartzSobolevCoordinate 1 u) =
      T (schwartzSobolevCoordinate 1 u) := by
    apply besselRealization_injective (n + m) q 0
    ext1 φ
    rw [hS u φ, hT' u φ]
  exact DFunLike.ext' ((denseRange_schwartzSobolevCoordinate (n + m) r 1).equalizer
    S.continuous T.continuous (funext heq))

/-- The actual positive-parameter cutoff acting from the first to the zeroth Bessel space. -/
def productCutoffSobolevOperator (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : Y → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (ε : ℝ) (hε : 0 < ε) :
    Lp U 2 (volume : Measure Z) →L[ℂ] Lp V 2 (volume : Measure Z) :=
  Classical.choose (existsUnique_productCutoffSobolevOperator a ha haK χ hχ hχK ε hε).exists

/-- On Schwartz inputs the bounded cutoff realization has its specified original Fourier action. -/
theorem productCutoffSobolevOperator_apply (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : Y → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχK : HasCompactSupport χ)
    (ε : ℝ) (hε : 0 < ε) (u : 𝓢(Z, U)) (v : 𝓢(Z, V))
    (hv : ∀ x, quantize (productCutoffSymbol a χ ε) u x = v x) :
    productCutoffSobolevOperator a ha haK χ hχ hχK ε hε
      (schwartzSobolevCoordinate 1 u) = schwartzSobolevCoordinate 0 v := by
  have h := Classical.choose_spec
    (existsUnique_productCutoffSobolevOperator a ha haK χ hχ hχK ε hε).exists
  apply besselRealization_injective (n + m) q 0
  ext1 φ
  rw [besselRealization_schwartzSobolevCoordinate]
  change _ = ∫ x, φ x • v x
  rw [show besselRealization (n + m) q 0
      (productCutoffSobolevOperator a ha haK χ hχ hχK ε hε
        (schwartzSobolevCoordinate 1 u)) φ =
        ∫ x, φ x • quantize (productCutoffSymbol a χ ε) u x from h u φ]
  simp_rw [hv]

end AtiyahSinger
