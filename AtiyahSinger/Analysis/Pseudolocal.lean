/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DistributionRegularity
public import AtiyahSinger.Analysis.TwoSidedCutoff

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Sobolev quantization and the pseudolocal property

Public module ID: M0903.

D05/A02: SG III.3.2 and 3.9, pp.177-178 and 182-183. The previously specified
bounded extension is made unique and named in its actual Bessel coordinates.
The result acts on H^s distributions for every real s. No extension to all of
S' or to arbitrary distributions on an open set is silently assumed.

For nested cutoffs, χ P (1-ρ) has a smoothing symbol. Its input factor 1-ρ is not
compactly supported. We use the complete expansion of χ P ρ to compare its symbol
with χp; we do not apply the compact-amplitude theorem to χ(x)(1-ρ(y))p(x,ξ).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- Schwartz functions are dense in the actual Bessel coordinates of every real H^s. -/
theorem denseRange_schwartzSobolevCoordinate (n r : ℕ) (s : ℝ) :
    DenseRange (schwartzSobolevCoordinate (n := n) (r := r) s) := by
  /- Schwartz functions embed densely in L². The positive Bessel multiplier J^s
  is an automorphism of Schwartz space, with inverse J^(-s); both symbols and
  all their derivatives have polynomial growth. Thus the range of J^s followed
  by the L² embedding is exactly the dense image of Schwartz functions in L². -/
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let w (t : ℝ) : X → ℝ := fun ξ ↦ (1 + ‖ξ‖ ^ 2) ^ (t / 2)
  have hw (t : ℝ) : (w t).HasTemperateGrowth := by
    dsimp [w]
    fun_prop
  -- Opposite Bessel weights cancel before applying the Schwartz multiplier.
  have hweights : w s * w (-s) = fun _ ↦ (1 : ℝ) := by
    funext ξ
    change (1 + ‖ξ‖ ^ 2) ^ (s / 2) * (1 + ‖ξ‖ ^ 2) ^ (-s / 2) = 1
    rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring]
    exact Real.rpow_zero _
  have hinverse (u : 𝓢(X, V)) :
      SchwartzMap.fourierMultiplierCLM V (w s)
        (SchwartzMap.fourierMultiplierCLM V (w (-s)) u) = u := by
    rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply (hw s) (hw (-s)),
      hweights, SchwartzMap.fourierMultiplierCLM_const]
    simp
  -- Every Schwartz L² value has an actual J^(-s) Schwartz preimage.
  have hdense : DenseRange (SchwartzMap.toLpCLM ℝ V 2 (volume : Measure X)) :=
    SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top
  refine Dense.mono ?_ hdense
  rintro _ ⟨u, rfl⟩
  refine ⟨SchwartzMap.fourierMultiplierCLM V (w (-s)) u, ?_⟩
  change (SchwartzMap.fourierMultiplierCLM V (w s)
    (SchwartzMap.fourierMultiplierCLM V (w (-s)) u)).toLp 2 = u.toLp 2
  rw [hinverse]

/-- SG 3.2: the bounded Sobolev extension with the stated test identity is unique. -/
theorem existsUnique_quantizeSobolev (m s : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) :
    ∃! P : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ),
          besselRealization n q (s - m) (P (schwartzSobolevCoordinate s u)) φ =
            ∫ x, φ x • quantize p u x := by
  /- Use the existing extension theorem with the compact set tsupport p.
  Two extensions agree as distributions on each Schwartz input, by their test
  identities. Injectivity of the target Bessel realization makes their coordinate
  values equal. Density of Schwartz coordinates and continuity give equality
  on the whole L² coordinate space. This is uniqueness of the specified operator. -/
  obtain ⟨P, hP⟩ := exists_quantize_sobolev_extension m s p hp (tsupport p) hc
    (fun x hx ξ ↦ congrFun (image_eq_zero_of_notMem_tsupport hx) ξ)
  refine ⟨P, hP, ?_⟩
  intro Q hQ
  have htest (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
      Q (schwartzSobolevCoordinate s u) = P (schwartzSobolevCoordinate s u) := by
    apply besselRealization_injective n q (s - m)
    ext1 φ
    rw [hQ u φ, hP u φ]
  have heq := (denseRange_schwartzSobolevCoordinate n r s).equalizer
    Q.continuous P.continuous (funext htest)
  exact DFunLike.ext' heq

/-- The unique H^s → H^(s-m) quantization, written in the fixed L² Bessel coordinates. -/
def quantizeSobolev (m s : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) :
    Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (existsUnique_quantizeSobolev m s p hp hc).exists.choose

/-- The named Sobolev map retains the exact quantization identity on Schwartz functions. -/
theorem besselRealization_quantizeSobolev (m s : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    besselRealization n q (s - m)
      (quantizeSobolev m s p hp hc (schwartzSobolevCoordinate s u)) φ =
        ∫ x, φ x • quantize p u x := by
  /- Apply the specification of the chosen unique extension. The right side
  is the original Fourier quantization paired bilinearly with φ. In particular,
  the coordinate map is not an arbitrary bounded map between copies of L². -/
  exact (existsUnique_quantizeSobolev m s p hp hc).exists.choose_spec u φ

/-- Different Sobolev coordinates and allowed symbol orders give the same output distribution. -/
theorem quantizeSobolev_compatible (m l s t : ℝ) (p : SymbolFunction n r q)
    (hm : IsSymbol Set.univ m p) (hl : IsSymbol Set.univ l p) (hc : HasCompactSupport p)
    (f g : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hfg : besselRealization n r s f = besselRealization n r t g) :
    besselRealization n q (s - m) (quantizeSobolev m s p hm hc f) =
      besselRealization n q (t - l) (quantizeSobolev l t p hl hc g) := by
  /- Regard the common distribution as an element of H^(max s t), using whichever
  of f,g has that order. Approximate there by Schwartz functions. The natural
  Sobolev inclusions give convergence in both input norms. On each approximant
  the two output distributions are exactly the same quantization. Continuity
  of both extensions and both Bessel realizations gives equality in S'. Thus
  neither the input order nor a larger allowed symbol order changes the action. -/
  have ordered (m l s t : ℝ) (hm : IsSymbol Set.univ m p)
      (hl : IsSymbol Set.univ l p) (hst : t ≤ s)
      (f g : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (hfg : besselRealization n r s f = besselRealization n r t g) :
      besselRealization n q (s - m) (quantizeSobolev m s p hm hc f) =
        besselRealization n q (t - l) (quantizeSobolev l t p hl hc g) := by
    obtain ⟨J, _, hJ⟩ := exists_sobolev_inclusion n r s t hst
    have hJschwartz (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
        J (schwartzSobolevCoordinate s u) = schwartzSobolevCoordinate t u := by
      apply besselRealization_injective n r t
      rw [hJ, besselRealization_schwartzSobolevCoordinate,
        besselRealization_schwartzSobolevCoordinate]
    -- Both continuous maps agree on the same dense strong Sobolev coordinates.
    have htest (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
        besselRealization n q (s - m)
            (quantizeSobolev m s p hm hc (schwartzSobolevCoordinate s u)) =
          besselRealization n q (t - l)
            (quantizeSobolev l t p hl hc (J (schwartzSobolevCoordinate s u))) := by
      rw [hJschwartz]
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_quantizeSobolev]
    have heq := (denseRange_schwartzSobolevCoordinate n r s).equalizer
      ((besselRealization n q (s - m)).continuous.comp
        (quantizeSobolev m s p hm hc).continuous)
      ((besselRealization n q (t - l)).continuous.comp
        ((quantizeSobolev l t p hl hc).continuous.comp J.continuous)) (funext htest)
    have hJfg : J f = g := besselRealization_injective n r t ((hJ f).trans hfg)
    simpa only [Function.comp_apply, hJfg] using congrFun heq f
  rcases le_total t s with hst | hts
  · exact ordered m l s t hm hl hst f g hfg
  · exact (ordered l m t s hl hm hts g f hfg.symm).symm

set_option maxSynthPendingDepth 20 in
set_option maxHeartbeats 4000000 in
-- The proof combines the derivative tower, polynomial estimates and Schwartz continuity.
/-- Compact spatial support gives uniform finite Schwartz seminorm bounds for quantization.
This is the standard continuity estimate behind SG III.3.2, stated on the original
Schwartz spaces with the project's SG Fourier normalization. -/
theorem quantize_schwartz_seminorm_bounds
    (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) :
    (∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      ContDiff ℝ ∞ (quantize p u)) ∧
      ∀ k i : ℕ, ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
          (x : EuclideanSpace ℝ (Fin n)),
          ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (quantize p u) x‖ ≤
            C * s.sup (schwartzSeminormFamily ℂ _ _) u := by
  /- First bound every spatial derivative of the phase times the original symbol,
  uniformly in x. Integrable polynomial Fourier bounds justify the entire Taylor
  tower under the frequency integral. The compact output support then controls
  each spatial weight; continuity of weighted Fourier L1 maps supplies finitely
  many seminorms of the original Schwartz input. -/
  -- Polynomial frequency bounds for the phase and the spatially compact symbol.
  have phase_bounds {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (k : ℕ) :
      ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ i
          (fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) x‖ ≤ C * (1 + ‖ξ‖) ^ d := by
    let V := EuclideanSpace ℝ (Fin n)
    obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
    obtain ⟨d, C, hC, hder⟩ := Complex.hasTemperateGrowth_exp_mul_I.norm_iteratedFDeriv_le_uniform k
    refine ⟨d + k, C * (1 + max R 0) ^ d, by positivity, ?_⟩
    intro i hi x hx ξ
    let L : V →L[ℝ] ℝ := innerSL ℝ ξ
    let e : ℝ → ℂ := fun t ↦ Complex.exp (t * Complex.I)
    have he : ContDiff ℝ ∞ e := Complex.hasTemperateGrowth_exp_mul_I.1
    have hfun : (fun x : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))) = e ∘ L := by
      funext x
      simp [e, L, real_inner_comm, mul_comm]
    rw [hfun, L.iteratedFDeriv_comp_right he x (by simp)]
    have hbase : 1 + ‖L x‖ ≤ (1 + max R 0) * (1 + ‖ξ‖) := by
      have hnorm : ‖L x‖ ≤ ‖ξ‖ * max R 0 :=
        (norm_inner_le_norm ξ x).trans (mul_le_mul_of_nonneg_left
          ((hR x hx).trans (le_max_left _ _)) (norm_nonneg _))
      nlinarith [norm_nonneg ξ, le_max_right R 0]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i e (L x)‖ * ‖L‖ ^ i := by
        simpa using ContinuousMultilinearMap.norm_compContinuousLinearMap_le
          (iteratedFDeriv ℝ i e (L x)) (fun _ ↦ L)
      _ ≤ (C * (1 + ‖L x‖) ^ d) * ‖L‖ ^ i := by
        gcongr
        exact hder i hi (L x)
      _ ≤ (C * ((1 + max R 0) * (1 + ‖ξ‖)) ^ d) * (1 + ‖ξ‖) ^ k := by
        gcongr
        calc
          ‖L‖ ^ i = ‖ξ‖ ^ i := by rw [innerSL_apply_norm]
          _ ≤ (1 + ‖ξ‖) ^ i := by gcongr; linarith [norm_nonneg ξ]
          _ ≤ (1 + ‖ξ‖) ^ k := pow_le_pow_right₀ (by linarith [norm_nonneg ξ]) hi
      _ = _ := by rw [mul_pow, pow_add]; ring
  have symbol_bounds {n r q : ℕ} (m : ℝ) (p : SymbolFunction n r q)
      (hp : IsSymbol Set.univ m p) (K : Set (EuclideanSpace ℝ (Fin n)))
      (hK : IsCompact K) (k : ℕ) :
      ∃ (C : ℝ), 0 ≤ C ∧ ∀ i ≤ k, ∀ x ∈ K, ∀ ξ,
        ‖iteratedFDeriv ℝ i (fun x ↦ p x ξ) x‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    choose C hC hbound using fun i ↦ hp.2 K (Set.subset_univ _) hK i 0
    refine ⟨∑ j ∈ Finset.range (k + 1), C j, Finset.sum_nonneg (fun j _ ↦ hC j), ?_⟩
    intro i hi x hx ξ
    have hb := hbound i x hx ξ
    have hzero : (fun y ↦ iteratedFDeriv ℝ 0 (p y) ξ) =
        (continuousMultilinearCurryFin0 ℝ V H).symm ∘ (fun y ↦ p y ξ) := by
      funext y
      exact congrFun (iteratedFDeriv_zero_eq_comp) ξ
    simp only [symbolDerivative, hzero, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
      Nat.cast_zero, sub_zero] at hb
    calc
      _ ≤ C i * (1 + ‖ξ‖) ^ m := hb
      _ ≤ (∑ j ∈ Finset.range (k + 1), C j) * (1 + ‖ξ‖) ^ (⌈m⌉₊ : ℝ) := by
        apply mul_le_mul
        · exact Finset.single_le_sum (fun j _ ↦ hC j) (Finset.mem_range.mpr (by omega))
        · exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil m)
        · positivity
        · exact Finset.sum_nonneg (fun j _ ↦ hC j)
      _ = _ := by rw [Real.rpow_natCast]
  have kernel_bounds {n r q : ℕ} (m : ℝ) (p : SymbolFunction n r q)
      (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p) (k : ℕ) :
      ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ x ξ : EuclideanSpace ℝ (Fin n),
        ‖iteratedFDeriv ℝ k
          (fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ) x‖ ≤
            C * (1 + ‖ξ‖) ^ d := by
    let V := EuclideanSpace ℝ (Fin n)
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    obtain ⟨d, A, hA, hphase⟩ := phase_bounds (tsupport p) hc k
    obtain ⟨B, hB, hpbound⟩ := symbol_bounds m p hp (tsupport p) hc k
    refine ⟨d + ⌈m⌉₊, (2 : ℝ) ^ k * A * B, by positivity, ?_⟩
    intro x ξ
    let e : V → ℂ := fun x ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))
    have he : ContDiff ℝ ∞ e := by
      simpa [e, Function.comp_def, real_inner_comm, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.1.comp (innerSL ℝ ξ).contDiff
    have hps : ContDiff ℝ ∞ (Function.uncurry p) := by
      simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
    have hpx : ContDiff ℝ ∞ (fun x ↦ p x ξ) :=
      hps.comp (contDiff_id.prodMk contDiff_const)
    by_cases hx : x ∈ tsupport p
    · calc
        _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            ‖iteratedFDeriv ℝ i e x‖ * ‖iteratedFDeriv ℝ (k - i) (fun x ↦ p x ξ) x‖ :=
          norm_iteratedFDeriv_smul_le he hpx x (by simp)
        _ ≤ ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
            (A * (1 + ‖ξ‖) ^ d) * (B * (1 + ‖ξ‖) ^ ⌈m⌉₊) := by
          apply Finset.sum_le_sum
          intro i hi
          gcongr
          · exact hphase i (by simpa using hi) x hx ξ
          · exact hpbound (k - i) (Nat.sub_le _ _) x hx ξ
        _ = (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ)) *
            (A * B * (1 + ‖ξ‖) ^ (d + ⌈m⌉₊)) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          rw [pow_add]
          ring
        _ = _ := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
          ring
    · have hsupp : tsupport (fun y : V ↦ e y • p y ξ) ⊆ tsupport p := by
        apply closure_mono
        intro y hy
        contrapose! hy
        simp only [Function.mem_support, ne_eq, not_not] at hy ⊢
        simp [hy]
      have hzero : iteratedFDeriv ℝ k (fun y : V ↦ e y • p y ξ) x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hx
          (hsupp (tsupport_iteratedFDeriv_subset k h)))
      rw [hzero, norm_zero]
      positivity
  -- Uniform integrability makes every differentiated integral an actual derivative.
  have integrate {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) → W)
      (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (hbound : ∀ k : ℕ, ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        Integrable b ∧ ∀ x ξ, ‖iteratedFDeriv ℝ k (fun x ↦ f x ξ) x‖ ≤ b ξ) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f x ξ) ∧
        ∀ k x, iteratedFDeriv ℝ k (fun x ↦ ∫ ξ, f x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ k (fun x ↦ f x ξ) x := by
    let V := EuclideanSpace ℝ (Fin n)
    have parametric {X Y Z : Type}
        [NormedAddCommGroup X] [NormedSpace ℝ X]
        [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (g : X → Y → Z) (hg : ContDiff ℝ ∞ (Function.uncurry g)) (k : ℕ) :
        ContDiff ℝ ∞ (fun z : X × Y ↦ iteratedFDeriv ℝ k (g z.1) z.2) := by
      induction k with
      | zero =>
        exact hg.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ Y Z).symm : _ →L[ℝ] Y [×0]→L[ℝ] Z)
      | succ k ih =>
        have h : ContDiff ℝ ∞
            (Function.uncurry (fun z : X × Y ↦ fun η : Y ↦ iteratedFDeriv ℝ k (g z.1) η)) :=
          ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
        have hd : ContDiff ℝ ∞
            (fun z : X × Y ↦ fderiv ℝ (iteratedFDeriv ℝ k (g z.1)) z.2) :=
          h.fderiv contDiff_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ Y) Z).symm :
            _ →L[ℝ] Y [×(k + 1)]→L[ℝ] Z)
    let D (k : ℕ) (x ξ : V) := iteratedFDeriv ℝ k (fun x ↦ f x ξ) x
    have hs (k : ℕ) : ContDiff ℝ ∞ (Function.uncurry (D k)) := by
      exact (parametric (fun ξ x ↦ f x ξ)
        (hf.comp (contDiff_snd.prodMk contDiff_fst)) k).comp
          (contDiff_snd.prodMk contDiff_fst)
    have hi (k : ℕ) (x : V) : Integrable (D k x) := by
      obtain ⟨b, hb, hbk⟩ := hbound k
      exact hb.mono' ((hs k).continuous.comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable
          (Filter.Eventually.of_forall (hbk x))
    have hd (k : ℕ) (x : V) :
        HasFDerivAt (fun x ↦ ∫ ξ, D k x ξ)
          ((∫ ξ, D (k + 1) x ξ).curryLeft) x := by
      obtain ⟨b, hb, hbk⟩ := hbound (k + 1)
      let L := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ V) W
      have heq (z ξ : V) : fderiv ℝ (fun z ↦ D k z ξ) z = L (D (k + 1) z ξ) := by
        dsimp only [D]
        rw [iteratedFDeriv_succ_eq_comp_left]
        exact (L.apply_symm_apply _).symm
      have hdiff (ξ z : V) : HasFDerivAt (fun z ↦ D k z ξ) (L (D (k + 1) z ξ)) z := by
        rw [← heq]
        exact (((hs k).comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp) z).hasFDerivAt
      have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F := D k) (F' := fun z ξ ↦ L (D (k + 1) z ξ)) (s := Set.univ)
        (bound := b) (x₀ := x) (by simp)
        (Filter.Eventually.of_forall (fun z ↦ (hi k z).1)) (hi k x)
        ((L.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp (hi (k + 1) x)).1)
        (Filter.Eventually.of_forall (fun ξ z _ ↦ by simpa using hbk z ξ))
        hb (Filter.Eventually.of_forall (fun ξ z _ ↦ hdiff ξ z))
      have hL : (∫ ξ, L (D (k + 1) x ξ)) = L (∫ ξ, D (k + 1) x ξ) :=
        L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi (k + 1) x)
      rw [hL] at h
      exact h
    have hTaylor : HasFTaylorSeriesUpTo (∞ : ℕ∞ω) (fun x ↦ ∫ ξ, f x ξ)
        (fun x k ↦ ∫ ξ, D k x ξ) := by
      constructor
      · intro x
        let L := continuousMultilinearCurryFin0 ℝ V W
        calc
          _ = ∫ ξ, L (D 0 x ξ) :=
            (L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm (hi 0 x)).symm
          _ = _ := by
            apply integral_congr_ae
            filter_upwards with ξ
            simp [D, L]
      · intro k _ x
        exact hd k x
      · intro k _
        exact (show Differentiable ℝ (fun x ↦ ∫ ξ, D k x ξ) from
          fun x ↦ (hd k x).differentiableAt).continuous
    exact ⟨hTaylor.contDiff, fun k x ↦ (hTaylor.eq_iteratedFDeriv (by simp) x).symm⟩
  -- Weighted Fourier L1 norms are continuous seminorms of the original input.
  have weighted {n r : ℕ} (d : ℕ) :
      ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
          Integrable (fun ξ ↦ (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) ∧
            (∫ ξ, (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) ≤
              C * s.sup (schwartzSeminormFamily ℂ _ _) u := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let FT : 𝓢(V, E) →L[ℂ] 𝓢(V, E) :=
      (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e).comp (FourierTransform.fourierCLM ℂ _)
    have hFT (u : 𝓢(V, E)) (ξ : V) : FT u ξ = fourierSG u ξ := rfl
    let w : V → ℂ := fun ξ ↦ ((1 + ‖ξ‖ ^ 2) ^ d : ℝ)
    have hw : w.HasTemperateGrowth := by dsimp [w]; fun_prop
    let T : 𝓢(V, E) →L[ℂ] Lp E 1 (volume : Measure V) :=
      (SchwartzMap.toLpCLM ℂ E 1 volume).comp ((SchwartzMap.smulLeftCLM E w).comp FT)
    let q : Seminorm ℂ 𝓢(V, E) := (normSeminorm ℂ _).comp T.toLinearMap
    have hq : Continuous q := T.continuous.norm
    obtain ⟨s, C, _, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ V E) q hq
    have hweight (ξ : V) : (1 + ‖ξ‖) ^ d ≤ (2 : ℝ) ^ d * ‖w ξ‖ := by
      have hbase : 1 + ‖ξ‖ ≤ 2 * (1 + ‖ξ‖ ^ 2) := by nlinarith [sq_nonneg (‖ξ‖ - 1)]
      have hwNorm : ‖w ξ‖ = (1 + ‖ξ‖ ^ 2) ^ d := by
        change ‖(((1 + ‖ξ‖ ^ 2) ^ d : ℝ) : ℂ)‖ = _
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      rw [hwNorm, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hbase d
    refine ⟨s, (2 : ℝ) ^ d * C, by positivity, ?_⟩
    intro u
    let v : 𝓢(V, E) := SchwartzMap.smulLeftCLM E w (FT u)
    have hv (ξ : V) : ‖v ξ‖ = ‖w ξ‖ * ‖fourierSG u ξ‖ := by
      rw [show v ξ = w ξ • FT u ξ from SchwartzMap.smulLeftCLM_apply_apply hw _ _,
        norm_smul, hFT]
    have hb (ξ : V) : (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖ ≤ (2 : ℝ) ^ d * ‖v ξ‖ := by
      rw [hv]
      nlinarith [mul_le_mul_of_nonneg_right (hweight ξ) (norm_nonneg (fourierSG u ξ))]
    have hi : Integrable (fun ξ : V ↦ (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) := by
      apply (v.integrable.norm.const_mul ((2 : ℝ) ^ d)).mono'
        (((continuous_const.add continuous_norm).pow d).mul
          ((FT u).continuous.norm)).aestronglyMeasurable
      filter_upwards with ξ
      change ‖(1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖‖ ≤ _
      rw [Real.norm_of_nonneg (by positivity)]
      exact hb ξ
    refine ⟨hi, ?_⟩
    calc
      _ ≤ ∫ ξ, (2 : ℝ) ^ d * ‖v ξ‖ :=
        integral_mono hi (v.integrable.norm.const_mul _) hb
      _ = (2 : ℝ) ^ d * ‖T u‖ := by
        rw [integral_const_mul]
        congr 1
        exact (SchwartzMap.norm_toLp_one).symm
      _ ≤ (2 : ℝ) ^ d * ((C : ℝ) * s.sup (schwartzSeminormFamily ℂ V E) u) := by
        apply mul_le_mul_of_nonneg_left (hC u) (by positivity)
      _ = _ := by ring
  let V := EuclideanSpace ℝ (Fin n)
  let E := EuclideanSpace ℂ (Fin r)
  let F := EuclideanSpace ℂ (Fin q)
  let H := E →L[ℂ] F
  let a (x ξ : V) : H := Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) • p x ξ
  let f (u : 𝓢(V, E)) (x ξ : V) : F := a x ξ (fourierSG u ξ)
  have hpSmooth : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  have hphaseSmooth : ContDiff ℝ ∞
      (fun z : V × V ↦ Complex.exp (Complex.I * (inner ℝ z.1 z.2 : ℂ))) := by
    simpa [Function.comp_def, mul_comm] using
      Complex.hasTemperateGrowth_exp_mul_I.1.comp (contDiff_inner (𝕜 := ℝ))
  have haSmooth : ContDiff ℝ ∞ (Function.uncurry a) := hphaseSmooth.smul hpSmooth
  have hFourier (u : 𝓢(V, E)) : ContDiff ℝ ∞ (fourierSG u) := by
    exact ((FourierTransform.fourier u).smooth ⊤).comp
      ((2 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ V).contDiff
  have hfSmooth (u : 𝓢(V, E)) : ContDiff ℝ ∞ (Function.uncurry (f u)) := by
    change ContDiff ℝ ∞ (fun z : V × V ↦ a z.1 z.2 (fourierSG u z.2))
    exact ((ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ).contDiff.comp haSmooth).clm_apply
      ((hFourier u).comp contDiff_snd)
  have hkernel (i : ℕ) : ∃ (d : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (u : 𝓢(V, E)) (x ξ : V),
        ‖iteratedFDeriv ℝ i (fun x ↦ f u x ξ) x‖ ≤
          C * ((1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) := by
    obtain ⟨d, C, hC, hb⟩ := kernel_bounds m p hp hc i
    refine ⟨d, C, hC, ?_⟩
    intro u x ξ
    let L : H →L[ℝ] F :=
      (ContinuousLinearMap.apply ℂ F (fourierSG u ξ)).restrictScalars ℝ
    have hL : ‖L‖ ≤ ‖fourierSG u ξ‖ := by
      apply L.opNorm_le_bound (norm_nonneg _)
      intro A
      change ‖A (fourierSG u ξ)‖ ≤ ‖fourierSG u ξ‖ * ‖A‖
      simpa only [mul_comm] using A.le_opNorm (fourierSG u ξ)
    calc
      _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ i (fun x ↦ a x ξ) x‖ :=
        L.norm_iteratedFDeriv_comp_left
          ((haSmooth.comp (contDiff_id.prodMk contDiff_const)).contDiffAt) (by simp)
      _ ≤ ‖fourierSG u ξ‖ * (C * (1 + ‖ξ‖) ^ d) :=
        mul_le_mul hL (hb x ξ) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hIntegral (u : 𝓢(V, E)) :
      ContDiff ℝ ∞ (fun x ↦ ∫ ξ, f u x ξ) ∧
        ∀ i x, iteratedFDeriv ℝ i (fun x ↦ ∫ ξ, f u x ξ) x =
          ∫ ξ, iteratedFDeriv ℝ i (fun x ↦ f u x ξ) x := by
    apply integrate (f u) (hfSmooth u)
    intro i
    obtain ⟨d, C, _, hb⟩ := hkernel i
    obtain ⟨_, _, _, hw⟩ := weighted (n := n) (r := r) d
    exact ⟨fun ξ ↦ C * ((1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖),
      ((hw u).1).const_mul C, hb u⟩
  have hsmooth (u : 𝓢(V, E)) : ContDiff ℝ ∞ (quantize p u) :=
    (hIntegral u).1.const_smul (((2 * Real.pi) ^ n)⁻¹)
  refine ⟨hsmooth, ?_⟩
  intro k i
  obtain ⟨d, C, hC, hb⟩ := hkernel i
  obtain ⟨s, D, hD, hw⟩ := weighted (n := n) (r := r) d
  obtain ⟨R, hR⟩ := hc.isBounded.exists_norm_le
  let c : ℝ := ((2 * Real.pi) ^ n)⁻¹
  refine ⟨s, (max R 0) ^ k * ‖c‖ * C * D, by positivity, ?_⟩
  intro u x
  by_cases hx : x ∈ tsupport p
  · have hder : iteratedFDeriv ℝ i (quantize p u) x =
        c • (∫ ξ, iteratedFDeriv ℝ i (fun x ↦ f u x ξ) x) := by
      change iteratedFDeriv ℝ i (fun x ↦ c • ∫ ξ, f u x ξ) x = _
      rw [iteratedFDeriv_const_smul_apply' ((hIntegral u).1.contDiffAt.of_le (by simp)),
        (hIntegral u).2 i x]
    have hi : ‖∫ ξ, iteratedFDeriv ℝ i (fun x ↦ f u x ξ) x‖ ≤
        C * D * s.sup (schwartzSeminormFamily ℂ V E) u := by
      calc
        _ ≤ ∫ ξ, C * ((1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) :=
          norm_integral_le_of_norm_le ((hw u).1.const_mul C)
            (Filter.Eventually.of_forall (hb u x))
        _ = C * (∫ ξ, (1 + ‖ξ‖) ^ d * ‖fourierSG u ξ‖) := integral_const_mul _ _
        _ ≤ C * (D * s.sup (schwartzSeminormFamily ℂ V E) u) :=
          mul_le_mul_of_nonneg_left (hw u).2 hC
        _ = _ := by ring
    rw [hder, norm_smul]
    calc
      _ ≤ (max R 0) ^ k * (‖c‖ * (C * D * s.sup
          (schwartzSeminormFamily ℂ V E) u)) := by
        gcongr
        exact (hR x hx).trans (le_max_left _ _)
      _ = _ := by ring
  · have hsupp : tsupport (quantize p u) ⊆ tsupport p := by
      apply closure_mono
      intro y hy
      contrapose! hy
      simp only [Function.mem_support, ne_eq, not_not] at hy ⊢
      simp [quantize, hy]
    have hz : iteratedFDeriv ℝ i (quantize p u) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx
        (hsupp (tsupport_iteratedFDeriv_subset i h)))
    rw [hz, norm_zero, mul_zero]
    positivity

/-- A spatially compact symbol sends each Schwartz function to an actual Schwartz function. -/
theorem exists_schwartz_quantize (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    ∃ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
      ∀ x, v x = quantize p u x := by
  /- Differentiate the Fourier integral in x. Each derivative has polynomial
  frequency growth, absorbed by rapid decay of the Fourier transform of u.
  On compact x sets this gives domination for derivatives of every order. The
  output vanishes off tsupport p, so it is smooth and compactly supported and
  hence Schwartz. Local spatial symbol estimates suffice because that support is compact. -/
  obtain ⟨hsmooth, hbound⟩ := quantize_schwartz_seminorm_bounds m p hp hc
  -- The same smooth Fourier integral has every defining Schwartz decay bound.
  refine ⟨{ toFun := quantize p u, smooth' := hsmooth u, decay' := ?_ }, fun _ ↦ rfl⟩
  intro k i
  obtain ⟨s, C, _, h⟩ := hbound k i
  exact ⟨C * s.sup (schwartzSeminormFamily ℂ _ _) u, h u⟩

set_option maxHeartbeats 1000000 in

open FourierTransform in
/-- Multiplication by a compact smooth cutoff has a unique bounded map in H^s coordinates. -/
theorem existsUnique_sobolevCutoffCLM (s : ℝ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    ∃! T : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ f, besselRealization n r s (T f) =
        TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun x ↦ (χ x : ℂ)) (besselRealization n r s f) := by
  /- Fourier multiplication becomes convolution. A polynomial Bessel-weight ratio
  and rapid decay of the fixed cutoff give an integrable convolution majorant.
  The L² estimate then extends the same multiplier from dense Schwartz coordinates;
  continuity of the original distribution maps retains the exact action on H^s. -/
  -- Weighted Cauchy–Schwarz on the product measure supplies the needed L¹–L² estimate.
  have young {n r : ℕ} (A : EuclideanSpace ℝ (Fin n) → ℝ)
    (hAc : Continuous A) (hAi : Integrable A) (hA : ∀ x, 0 ≤ A x)
    (hAe : ∀ x, A (-x) = A x)
    (g h : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (hb : ∀ x, ‖h x‖ ≤ ∫ y, A (x - y) * ‖g y‖) :
    ‖h.toLp 2‖ ≤ (∫ x, A x) * ‖g.toLp 2‖ := by
    let V := EuclideanSpace ℝ (Fin n)
    let ν : Measure (V × V) := volume.prod volume
    have hi (f : 𝓢(V, EuclideanSpace ℂ (Fin r))) : Integrable (fun x ↦ ‖f x‖ ^ 2) :=
      (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp (f.memLp 2 volume)
    have hn (f : 𝓢(V, EuclideanSpace ℂ (Fin r))) :
        ‖f.toLp 2‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
      rw [SchwartzMap.norm_toLp' (by norm_num : (2 : ENNReal) ≠ 0)
        (by norm_num : (2 : ENNReal) ≠ ⊤)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat]
      rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
      exact Real.sq_sqrt (integral_nonneg (fun _ ↦ sq_nonneg _))
    have hGi : Integrable (fun z : V × V ↦ A (z.1 - z.2) * ‖g z.2‖ ^ 2) ν := by
      have hi := (hi g).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hAi
      simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hi
    have hFi : Integrable (fun z : V × V ↦ A (z.1 - z.2) * ‖h z.1‖ ^ 2) ν := by
      have hi := (hi h).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hAi
      have he (x y : V) : A (y - x) = A (x - y) := by rw [← neg_sub x y, hAe]
      have hs := hi.swap
      change Integrable (fun z : V × V ↦ ‖h z.1‖ ^ 2 * A (z.2 - z.1)) ν at hs
      simpa only [he, mul_comm] using hs
    let F : V × V → ℝ := fun z ↦ Real.sqrt (A (z.1 - z.2)) * ‖h z.1‖
    let G : V × V → ℝ := fun z ↦ Real.sqrt (A (z.1 - z.2)) * ‖g z.2‖
    have hFs (z : V × V) : F z ^ 2 = A (z.1 - z.2) * ‖h z.1‖ ^ 2 := by
      dsimp [F]
      rw [mul_pow, Real.sq_sqrt (hA _)]
    have hGs (z : V × V) : G z ^ 2 = A (z.1 - z.2) * ‖g z.2‖ ^ 2 := by
      dsimp [G]
      rw [mul_pow, Real.sq_sqrt (hA _)]
    have hFc : Continuous F := (hAc.comp (continuous_fst.sub continuous_snd)).sqrt.mul
      (h.continuous.comp continuous_fst).norm
    have hGc : Continuous G := (hAc.comp (continuous_fst.sub continuous_snd)).sqrt.mul
      (g.continuous.comp continuous_snd).norm
    have hFL : MemLp F 2 ν := (memLp_two_iff_integrable_sq hFc.aestronglyMeasurable).mpr
      (by simpa only [hFs] using hFi)
    have hGL : MemLp G 2 ν := (memLp_two_iff_integrable_sq hGc.aestronglyMeasurable).mpr
      (by simpa only [hGs] using hGi)
    have hFG (z : V × V) : F z * G z = A (z.1 - z.2) * ‖h z.1‖ * ‖g z.2‖ := by
      dsimp [F, G]
      calc
        _ = Real.sqrt (A (z.1 - z.2)) ^ 2 * ‖h z.1‖ * ‖g z.2‖ := by ring
        _ = _ := by rw [Real.sq_sqrt (hA _)]
    have hmul : Integrable (fun z : V × V ↦ A (z.1 - z.2) * ‖h z.1‖ * ‖g z.2‖) ν := by
      convert! memLp_one_iff_integrable.mp (hFL.mul hGL : MemLp (F * G) 1 ν) using 1
      funext z
      exact (hFG z).symm
    have hFint : (∫ z, F z ^ 2 ∂ν) = (∫ x, A x) * ‖h.toLp 2‖ ^ 2 := by
      simp_rw [hFs]
      rw [integral_prod _ hFi]
      simp_rw [integral_mul_const, integral_sub_left_eq_self]
      rw [integral_const_mul, hn]
    have hGint : (∫ z, G z ^ 2 ∂ν) = (∫ x, A x) * ‖g.toLp 2‖ ^ 2 := by
      simp_rw [hGs]
      rw [integral_prod_symm _ hGi]
      simp_rw [integral_mul_const, integral_sub_right_eq_self]
      rw [integral_const_mul, hn]
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (f := F) (g := G)
      Real.HolderConjugate.two_two
      (ae_of_all ν (fun z ↦ mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
      (ae_of_all ν (fun z ↦ mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)))
      (by simpa using hFL) (by simpa using hGL)
    have hCS' : (∫ z, A (z.1 - z.2) * ‖h z.1‖ * ‖g z.2‖ ∂ν) ≤
        (∫ x, A x) * ‖h.toLp 2‖ * ‖g.toLp 2‖ := by
      have hnA : 0 ≤ ∫ x, A x := integral_nonneg hA
      calc
        _ ≤ Real.sqrt ((∫ x, A x) * ‖h.toLp 2‖ ^ 2) *
            Real.sqrt ((∫ x, A x) * ‖g.toLp 2‖ ^ 2) := by
          simpa only [Real.rpow_two, hFint, hGint, hFG, ← Real.sqrt_eq_rpow] using hCS
        _ = Real.sqrt (∫ x, A x) ^ 2 * ‖h.toLp 2‖ * ‖g.toLp 2‖ := by
          rw [Real.sqrt_mul hnA, Real.sqrt_mul hnA, Real.sqrt_sq (norm_nonneg _),
            Real.sqrt_sq (norm_nonneg _)]
          ring
        _ = _ := by rw [Real.sq_sqrt hnA]
    have hmain : ‖h.toLp 2‖ ^ 2 ≤
        ∫ z, A (z.1 - z.2) * ‖h z.1‖ * ‖g z.2‖ ∂ν := by
      rw [hn, integral_prod _ hmul]
      apply integral_mono (hi h) hmul.integral_prod_left
      intro x
      calc
        ‖h x‖ ^ 2 ≤ ‖h x‖ * (∫ y, A (x - y) * ‖g y‖) := by
          nlinarith [hb x, norm_nonneg (h x)]
        _ = ∫ y, A (x - y) * ‖h x‖ * ‖g y‖ := by
          rw [← integral_const_mul]
          congr 1
          funext y
          ring
    by_cases hz : ‖h.toLp 2‖ = 0
    · rw [hz]
      exact mul_nonneg (integral_nonneg hA) (norm_nonneg _)
    · have hp : 0 < ‖h.toLp 2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith [hmain.trans hCS']
  -- Positive and negative Bessel orders both have polynomially controlled weight ratios.
  have moderate {n : ℕ} (s : ℝ) :
    ∃ (k : ℕ) (C : ℝ), 0 < C ∧ ∀ x y : EuclideanSpace ℝ (Fin n),
      (1 + ‖x‖ ^ 2) ^ (s / 2) ≤
        C * (1 + ‖x - y‖) ^ k * (1 + ‖y‖ ^ 2) ^ (s / 2) := by
    let V := EuclideanSpace ℝ (Fin n)
    let w (t : ℝ) (x : V) := (1 + ‖x‖ ^ 2) ^ (t / 2)
    have hbase (x y : V) : 1 + ‖x‖ ^ 2 ≤ 2 * (1 + ‖x - y‖) ^ 2 * (1 + ‖y‖ ^ 2) := by
      have ht : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        simpa only [sub_add_cancel] using norm_add_le (x - y) y
      have hp : ‖x‖ ^ 2 ≤ (‖x - y‖ + ‖y‖) ^ 2 := by gcongr
      nlinarith [norm_nonneg (x - y), norm_nonneg y,
        sq_nonneg (‖x - y‖ - ‖y‖), sq_nonneg (‖x - y‖ * ‖y‖)]
    obtain ⟨k, hk⟩ := exists_nat_ge |s|
    let C : ℝ := 2 ^ (|s| / 2)
    have hC : 0 < C := by positivity
    have hpos (t : ℝ) (ht : 0 ≤ t) (htk : t ≤ k) (x y : V) :
        w t x ≤ 2 ^ (t / 2) * (1 + ‖x - y‖) ^ k * w t y := by
      calc
        _ ≤ (2 * (1 + ‖x - y‖) ^ 2 * (1 + ‖y‖ ^ 2)) ^ (t / 2) := by
          dsimp [w]
          exact Real.rpow_le_rpow (by positivity) (hbase x y) (by positivity)
        _ = 2 ^ (t / 2) * (1 + ‖x - y‖) ^ t * w t y := by
          rw [Real.mul_rpow (by positivity) (by positivity),
            Real.mul_rpow (by positivity) (by positivity)]
          dsimp [w]
          rw [← Real.rpow_natCast_mul (by positivity)]
          norm_num only [Nat.cast_ofNat]
          rw [show (2 : ℝ) * (t / 2) = t by ring]
        _ ≤ 2 ^ (t / 2) * (1 + ‖x - y‖) ^ k * w t y := by
          gcongr
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (x - y)]) htk
    refine ⟨k, C, hC, ?_⟩
    intro x y
    by_cases hs : 0 ≤ s
    · simpa only [C, abs_of_nonneg hs] using hpos s hs (by simpa [abs_of_nonneg hs] using hk) x y
    · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
      have hw (x : V) : w s x * w (-s) x = 1 := by
        dsimp [w]
        rw [← Real.rpow_add (by positivity), show s / 2 + -s / 2 = 0 by ring,
          Real.rpow_zero]
      have hxy : w (-s) y ≤ C * (1 + ‖x - y‖) ^ k * w (-s) x := by
        simpa only [C, abs_of_neg (lt_of_not_ge hs), norm_sub_rev] using
          hpos (-s) hs' (by simpa [abs_of_neg (lt_of_not_ge hs)] using hk) y x
      change w s x ≤ C * (1 + ‖x - y‖) ^ k * w s y
      calc
        _ = (w s x * w s y) * w (-s) y := by rw [mul_assoc, hw, mul_one]
        _ ≤ (w s x * w s y) * (C * (1 + ‖x - y‖) ^ k * w (-s) x) := by
          exact mul_le_mul_of_nonneg_left hxy (by dsimp [w]; positivity)
        _ = (w s x * w (-s) x) * (C * (1 + ‖x - y‖) ^ k * w s y) := by ring
        _ = _ := by rw [hw, one_mul]
  -- The Fourier normalization is exactly mathlib’s normalization in these Bessel coordinates.
  have product_fourier {n r : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ))
    (g : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) :
    𝓕 (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f g) =
      SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 f) (𝓕 g) := by
    apply (fourierEquiv ℂ 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))).symm.injective
    rw [fourierEquiv_symm_apply, fourierEquiv_symm_apply, fourierInv_fourier_eq]
    apply SchwartzMap.ext
    intro x
    change f x • g x =
      (𝓕 (SchwartzMap.convolution (ContinuousLinearMap.lsmul ℂ ℂ) (𝓕 f) (𝓕 g))) (-x)
    rw [SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply]
    have hf := congrArg (fun u : 𝓢(EuclideanSpace ℝ (Fin n), ℂ) ↦ u x)
      (fourierInv_fourier_eq (F := 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) f)
    have hg := congrArg (fun u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) ↦ u x)
      (fourierInv_fourier_eq (F := 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) g)
    change (𝓕 (𝓕 f)) (-x) = f x at hf
    change (𝓕 (𝓕 g)) (-x) = g x at hg
    rw [hf, hg]
    rfl
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r)
  let w (t : ℝ) (ξ : V) := (1 + ‖ξ‖ ^ 2) ^ (t / 2)
  have hw (t : ℝ) : (w t).HasTemperateGrowth := by dsimp [w]; fun_prop
  let f : 𝓢(V, ℂ) := (hcχ.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hχ)
  let M : 𝓢(V, H) →L[ℂ] 𝓢(V, H) := SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f
  let J (t : ℝ) : 𝓢(V, H) →L[ℂ] 𝓢(V, H) :=
    SchwartzMap.fourierMultiplierCLM H (fun ξ ↦ (w t ξ : ℂ))
  let B : 𝓢(V, H) →ₗ[ℂ] Lp H 2 (volume : Measure V) :=
    ((SchwartzMap.toLpCLM ℂ H 2 volume).comp (J s)).toLinearMap
  have hB (u : 𝓢(V, H)) : B u = schwartzSobolevCoordinate s u := by
    exact congrArg (fun v : 𝓢(V, H) ↦ v.toLp 2)
      (SchwartzMap.fourierMultiplierCLM_ofReal ℂ (hw s) u)
  obtain ⟨k, C, hC, hmoderate⟩ := moderate (n := n) s
  let d : ℕ := n + 1
  let D : ℝ := 2 ^ (k + d) *
    (Finset.Iic (k + d, 0)).sup (fun j ↦ SchwartzMap.seminorm ℂ j.1 j.2) (𝓕 f)
  have hD : 0 ≤ D := by positivity
  have hdecay (z : V) : (1 + ‖z‖) ^ k * ‖(𝓕 f) z‖ ≤
      D * (1 + ‖z‖) ^ (-(d : ℝ)) := by
    have hd : 0 < (1 + ‖z‖) ^ d := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hd]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply
      (𝕜 := ℂ) (m := (k + d, 0)) (k := k + d) (n := 0) le_rfl le_rfl (𝓕 f) z
    simpa only [norm_iteratedFDeriv_zero, D, pow_add, mul_assoc, mul_left_comm, mul_comm]
      using hb
  let A (z : V) : ℝ := (C * D) * (1 + ‖z‖) ^ (-(d : ℝ))
  have hAc : Continuous A := by
    have hc : Continuous (fun z : V ↦ (1 : ℝ) + ‖z‖) :=
      continuous_const.add continuous_norm
    exact continuous_const.mul (hc.rpow_const (fun z ↦ Or.inl (by positivity)))
  have hAi : Integrable A :=
    (integrable_one_add_norm (by simp [V, d])).const_mul (C * D)
  have hA (z : V) : 0 ≤ A z := by dsimp [A]; positivity
  have hAe (z : V) : A (-z) = A z := by simp [A]
  -- The same majorant controls every Schwartz input, independently of its seminorms.
  have hbound (u : 𝓢(V, H)) : ‖B (M u)‖ ≤ (∫ z, A z) * ‖B u‖ := by
    let g := SchwartzMap.smulLeftCLM H (w s) (𝓕 u)
    let v := SchwartzMap.smulLeftCLM H (w s) (𝓕 (M u))
    have hgnorm (y : V) : ‖g y‖ = w s y * ‖(𝓕 u) y‖ := by
      rw [SchwartzMap.smulLeftCLM_apply_apply (hw s), norm_smul,
        Real.norm_of_nonneg (by dsimp [w]; positivity)]
    have hvnorm (x : V) : ‖v x‖ = w s x * ‖(𝓕 (M u)) x‖ := by
      rw [SchwartzMap.smulLeftCLM_apply_apply (hw s), norm_smul,
        Real.norm_of_nonneg (by dsimp [w]; positivity)]
    have hv (x : V) : ‖v x‖ ≤ ∫ y, A (x - y) * ‖g y‖ := by
      have hint : Integrable (fun y ↦ A (x - y) * ‖g y‖) :=
        (hAi.comp_sub_left x).mul_bdd (c := SchwartzMap.seminorm ℂ 0 0 g)
          g.continuous.norm.aestronglyMeasurable
          (ae_of_all _ (fun y ↦ by
            rw [Real.norm_of_nonneg (norm_nonneg (g y))]
            exact SchwartzMap.norm_le_seminorm ℂ g y))
      have heq : (𝓕 (M u)) x = ∫ y, (𝓕 f) (x - y) • (𝓕 u) y := by
        rw [show M u = SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f u from rfl,
          product_fourier, SchwartzMap.convolution_apply]
        exact (congrFun (convolution_flip (ContinuousLinearMap.lsmul ℂ ℂ)
          (f := ⇑(𝓕 f : 𝓢(V, ℂ))) (g := ⇑(𝓕 u : 𝓢(V, H))) (μ := volume)) x).symm
      rw [hvnorm, heq,
        ← norm_smul_of_nonneg (show 0 ≤ w s x by dsimp [w]; positivity), ← integral_smul]
      apply norm_integral_le_of_norm_le hint
      filter_upwards with y
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by dsimp [w]; positivity), hgnorm]
      calc
        w s x * (‖(𝓕 f) (x - y)‖ * ‖(𝓕 u) y‖) ≤
            (C * (1 + ‖x - y‖) ^ k * w s y) *
              (‖(𝓕 f) (x - y)‖ * ‖(𝓕 u) y‖) := by
          gcongr
          exact hmoderate x y
        _ = C * ((1 + ‖x - y‖) ^ k * ‖(𝓕 f) (x - y)‖) *
            (w s y * ‖(𝓕 u) y‖) := by ring
        _ ≤ C * (D * (1 + ‖x - y‖) ^ (-(d : ℝ))) *
            (w s y * ‖(𝓕 u) y‖) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdecay (x - y)) hC.le)
            (by dsimp [w]; positivity)
        _ = A (x - y) * (w s y * ‖(𝓕 u) y‖) := by dsimp [A]; ring
    have hyn := young A hAc hAi hA hAe g v hv
    have hnorm (a : 𝓢(V, H)) : ‖B a‖ =
        ‖(SchwartzMap.smulLeftCLM H (w s) (𝓕 a)).toLp 2‖ := by
      have hJ : 𝓕 (J s a) = SchwartzMap.smulLeftCLM H (w s) (𝓕 a) := by
        change 𝓕 (𝓕⁻ (SchwartzMap.smulLeftCLM H
          (fun ξ ↦ (w s ξ : ℂ)) (𝓕 a))) = _
        rw [fourier_fourierInv_eq]
        exact SchwartzMap.smulLeftCLM_ofReal ℂ (hw s) (𝓕 a)
      change ‖(J s a).toLp 2 volume‖ = _
      exact (SchwartzMap.norm_fourier_toL2_eq (J s a)).symm.trans
        (congrArg (fun z : 𝓢(V, H) ↦ ‖z.toLp 2 volume‖) hJ)
    simpa only [hnorm] using hyn
  -- Extend on the actual dense Bessel-coordinate image and preserve its distribution formula.
  have hdense : DenseRange B := by
    have heq : ⇑B = schwartzSobolevCoordinate (n := n) (r := r) s := funext hB
    rw [heq]
    exact denseRange_schwartzSobolevCoordinate n r s
  let T := (B.comp M.toLinearMap).extendOfNorm B
  have hT (u : 𝓢(V, H)) : T (B u) = B (M u) :=
    LinearMap.extendOfNorm_eq hdense ⟨∫ z, A z, hbound⟩ u
  have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hformula (u : 𝓢(V, H)) :
      besselRealization n r s (T (B u)) =
        TemperedDistribution.smulLeftCLM H (fun x ↦ (χ x : ℂ))
          (besselRealization n r s (B u)) := by
    rw [hT, hB, hB, besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate]
    ext1 φ
    change (∫ x, φ x • (M u) x) =
      ∫ x, (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) x • u x
    simp only [M, SchwartzMap.pairing_apply_apply, ContinuousLinearMap.lsmul_apply,
      SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    apply integral_congr_ae
    filter_upwards with x
    change φ x • ((χ x : ℂ) • u x) = ((χ x : ℂ) * φ x) • u x
    rw [smul_smul, mul_comm]
  have hTall : ∀ v, besselRealization n r s (T v) =
      TemperedDistribution.smulLeftCLM H (fun x ↦ (χ x : ℂ))
        (besselRealization n r s v) := by
    have heq := hdense.equalizer
      ((besselRealization n r s).continuous.comp T.continuous)
      ((TemperedDistribution.smulLeftCLM H (fun x ↦ (χ x : ℂ))).continuous.comp
        (besselRealization n r s).continuous) (funext hformula)
    exact congrFun heq
  refine ⟨T, hTall, ?_⟩
  intro R hR
  apply ContinuousLinearMap.ext
  intro v
  apply besselRealization_injective
  exact (hR v).trans (hTall v).symm

/-- Actual cutoff multiplication in the Bessel coordinates of H^s. -/
def sobolevCutoffCLM (s : ℝ) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  (existsUnique_sobolevCutoffCLM s χ hχ hcχ).exists.choose

/-- The cutoff coordinate map intertwines the actual distribution multiplier. -/
theorem besselRealization_sobolevCutoffCLM (s : ℝ)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    besselRealization n r s (sobolevCutoffCLM s χ hχ hcχ f) =
      TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun x ↦ (χ x : ℂ)) (besselRealization n r s f) := by
  /- Unfold the chosen coordinate map and use its existence theorem's specification.
  This identity holds for every H^s distribution and explicitly identifies the
  operation with multiplication on scalar tests; it is not multiplication of L² coordinates. -/
  exact (existsUnique_sobolevCutoffCLM s χ hχ hcχ).exists.choose_spec f

/-- The exact symbol of χ P (1-ρ), formed by subtracting the two-sided cutoff symbol. -/
def offDiagonalSymbol (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : SymbolFunction n r q) : SymbolFunction n r q :=
  (fun x ξ ↦ χ x • p x ξ) - cutoffSymbol χ ρ p

/-- Nested cutoffs make the off-diagonal remainder a symbol of every order. -/
theorem isSmoothingSymbol_offDiagonalSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hone : tsupport χ ⊆ interior {x | ρ x = 1}) :
    IsSmoothingSymbol Set.univ (offDiagonalSymbol χ ρ p) := by
  /- Stage 1: the full expansion of cutoffSymbol χ ρ p has leading term χρp=χp.
  Every positive-degree coefficient differentiates ρ in y before setting y=x.
  On tsupport χ these derivatives vanish because ρ is one on a neighborhood;
  elsewhere the factor χ is zero. Stage 2: all positive terms vanish, so for
  every N≥1 the difference belongs to S^(m-N). These orders tend to minus infinity.
  Do not apply SG 3.5 to χ(x)(1-ρ(y))p(x,ξ), which has no compact y support. -/
  let c : SymbolFunction n r q := fun x ξ ↦ χ x • p x ξ
  have hnear (x ξ : EuclideanSpace ℝ (Fin n)) :
      (fun y ↦ cutoffAmplitude χ ρ p x y ξ) =ᶠ[nhds x] (fun _ ↦ c x ξ) := by
    by_cases hx : x ∈ tsupport χ
    · filter_upwards [isOpen_interior.mem_nhds (hone hx)] with y hy
      have hρy : ρ y = 1 := show y ∈ {y | ρ y = 1} from interior_subset hy
      simp [cutoffAmplitude, c, hρy]
    · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport hx
      exact Filter.Eventually.of_forall (fun y ↦ by simp [cutoffAmplitude, c, hχx])
  -- The same local constant germ determines every original expansion coefficient.
  have hterms (j : ℕ) : amplitudeExpansionTerm (cutoffAmplitude χ ρ p) j =
      if j = 0 then c else 0 := by
    by_cases hj : j = 0
    · subst j
      rw [amplitudeExpansionTerm_zero, ite_eq_left rfl]
      funext x ξ
      exact (hnear x ξ).eq_of_nhds
    · rw [ite_eq_right hj]
      funext x ξ
      have hy (η : EuclideanSpace ℝ (Fin n)) :
          iteratedFDeriv ℝ j (fun y ↦ cutoffAmplitude χ ρ p x y η) x = 0 := by
        simpa only [iteratedFDeriv_const_of_ne hj, Pi.zero_apply] using
          ((hnear x η).iteratedFDeriv ℝ j).eq_of_nhds
      simp [amplitudeExpansionTerm, hy]
  intro l
  obtain ⟨N, hN⟩ := exists_nat_gt (m - l)
  have h := hasSymbolExpansion_cutoffSymbol m p hp χ ρ hχ hρ hcχ hcρ (N + 1)
  have hsum : (∑ j ∈ Finset.range (N + 1),
      amplitudeExpansionTerm (cutoffAmplitude χ ρ p) j) = c := by
    simp_rw [hterms]
    simp
  rw [hsum] at h
  have hneg := (h.mono (show m - ((N + 1 : ℕ) : ℝ) ≤ l by push_cast; linarith)).smul
    isOpen_univ (-1)
  simpa only [neg_one_smul, neg_sub, offDiagonalSymbol, c] using hneg

/-- The off-diagonal symbol has compact x support supplied solely by χ. -/
theorem hasCompactSupport_offDiagonalSymbol
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ) (p : SymbolFunction n r q)
    (hcχ : HasCompactSupport χ) : HasCompactSupport (offDiagonalSymbol χ ρ p) := by
  /- Off tsupport χ, both χp and the actual amplitudeSymbol defining cutoffSymbol
  vanish at every frequency, since χ(x) factors the entire amplitude. Their
  difference thus has closed spatial support contained in the compact tsupport χ.
  This raw support statement does not require estimates, nesting, or support of ρ. -/
  -- The same spatial cutoff annihilates both raw terms at every frequency.
  apply hcχ.of_isClosed_subset isClosed_closure
  apply closure_minimal ?_ (isClosed_tsupport χ)
  intro x hx
  by_contra hxχ
  have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hxχ
  apply hx
  funext ξ
  simp [offDiagonalSymbol, cutoffSymbol, amplitudeSymbol, cutoffAmplitude, hzero]

/-- The off-diagonal symbol gives the exact difference on all Schwartz inputs. -/
theorem quantize_offDiagonalSymbol (m : ℝ) (p : SymbolFunction n r q)
    (hp : IsSymbol Set.univ m p) (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (offDiagonalSymbol χ ρ p) u x = χ x • quantize p
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun y ↦ (1 - (ρ y : ℂ))) u) x := by
  /- Quantization of χp is χ times quantization of p. Subtract the exact formula
  for cutoffSymbol χ ρ p and use linearity on Schwartz inputs. The smooth compact
  cutoff ρ has temperate growth, as does 1-ρ, so mathlib's multiplier really sends
  u to (1-ρ)u. Integrability follows from symbol growth and Schwartz Fourier decay.
  No nesting assumption is necessary for this exact identity. -/
  have hInt (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
      (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      MeasureTheory.Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        p x ξ (fourierSG u ξ)) := by
    let V := EuclideanSpace ℝ (Fin n)
    let E := EuclideanSpace ℂ (Fin r)
    let F := EuclideanSpace ℂ (Fin q)
    -- At each fixed spatial point, the symbol is a temperate frequency multiplier.
    have hg : (p x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry p) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hp.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have h := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
        apply h.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : V ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    -- The Fourier convention differs by an invertible real dilation, preserving Schwartz space.
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let e : V ≃L[ℝ] V :=
      (LinearEquiv.smulOfNeZero ℝ V ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (E →L[ℂ] F)).flip (hphase.smul hg) w).integrable
  -- Separate the original input into its cutoff and complementary parts.
  let v := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
    (fun y ↦ (ρ y : ℂ)) u
  have hρgrowth : (fun y ↦ (ρ y : ℂ)).HasTemperateGrowth :=
    (hcρ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hρ)
  have hdiff : SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
      (fun y ↦ (1 - (ρ y : ℂ))) u = u - v := by
    apply SchwartzMap.ext
    intro y
    have hd : (fun y ↦ (1 - (ρ y : ℂ))).HasTemperateGrowth :=
      (Function.HasTemperateGrowth.const (1 : ℂ)).sub hρgrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply hd]
    change (1 - (ρ y : ℂ)) • u y = u y - v y
    rw [show v y = (ρ y : ℂ) • u y from
      SchwartzMap.smulLeftCLM_apply_apply hρgrowth u y, sub_smul, one_smul]
  have hsub : quantize p (u - v) x = quantize p u x - quantize p v x := by
    have hfourier : FourierTransform.fourier (u - v) =
        FourierTransform.fourier u - FourierTransform.fourier v := by
      exact map_sub (SchwartzMap.fourierTransformCLM ℂ) u v
    simp only [quantize, fourierSG, hfourier, sub_apply, map_sub, smul_sub]
    have hu := hInt p hp u x
    have hv := hInt p hp v x
    dsimp only [fourierSG] at hu hv
    rw [integral_sub hu hv, smul_sub]
  -- Both symbol integrands are integrable before their difference is split.
  have hcInt := hInt (cutoffSymbol χ ρ p)
    (isSymbol_cutoffSymbol m p hp χ ρ hχ hρ hcχ hcρ) u x
  have hpInt := (hInt p hp u x).smul (χ x)
  have hformula : quantize (offDiagonalSymbol χ ρ p) u x =
      χ x • quantize p u x - quantize (cutoffSymbol χ ρ p) u x := by
    simp only [quantize, offDiagonalSymbol, Pi.sub_apply, sub_apply, smul_apply, smul_sub]
    simp only [smul_comm (Complex.exp _) (χ x)]
    have hi : Integrable (fun ξ ↦ χ x • (Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        p x ξ (fourierSG u ξ))) := hpInt
    rw [integral_sub hi hcInt, integral_smul, smul_sub]
    congr 1
    exact smul_comm _ _ _
  rw [hformula, quantize_cutoffSymbol m p hp χ ρ hχ hρ hcχ hcρ u x,
    hdiff, hsub, smul_sub]

set_option maxHeartbeats 800000 in

/-- SG 3.9's separated contribution is smooth for every real Sobolev input order. -/
theorem isSmoothDistributionOn_cutoff_quantizeSobolev_sub
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p) (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hone : tsupport χ ⊆ interior {x | ρ x = 1})
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    IsSmoothDistributionOn
      (TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin q))
        (fun x ↦ (χ x : ℂ))
        (besselRealization n q (s - m)
          (quantizeSobolev m s p hp hc (f - sobolevCutoffCLM s ρ hρ hcρ f)))) Set.univ := by
  /- Stage 1: the explicit off-diagonal symbol is smoothing with compact x support.
  For every desired output order t apply its order s-t Sobolev quantization.
  On Schwartz inputs the exact off-diagonal formula identifies its distribution
  with χP(1-ρ)u. The cutoff coordinate identity and density extend this equality
  to every f; all maps involved are continuous into S'. Stage 2: the displayed
  distribution consequently lies in H^t for every real t. Sobolev embedding and
  uniqueness of continuous representatives give a smooth function on all of R^n. -/
  let V := EuclideanSpace ℝ (Fin n)
  let Hr := EuclideanSpace ℂ (Fin r)
  let Hq := EuclideanSpace ℂ (Fin q)
  let Mρ := SchwartzMap.smulLeftCLM Hr (fun x ↦ (ρ x : ℂ))
  let Sρ := sobolevCutoffCLM (r := r) s ρ hρ hcρ
  let Mχ := TemperedDistribution.smulLeftCLM Hq (fun x ↦ (χ x : ℂ))
  have hρgrowth : (fun x ↦ (ρ x : ℂ)).HasTemperateGrowth :=
    (hcρ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hρ)
  have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have h1ρ : (fun x ↦ 1 - (ρ x : ℂ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hρgrowth
  have hMρ (u : 𝓢(V, Hr)) :
      TemperedDistribution.smulLeftCLM Hr (fun x ↦ (ρ x : ℂ)) (u : 𝓢'(V, Hr)) =
        ((Mρ u) : 𝓢'(V, Hr)) := by
    ext1 φ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards with x
    simp only [Mρ, SchwartzMap.smulLeftCLM_apply_apply hρgrowth, smul_eq_mul, smul_smul, mul_comm]
  have hSρ (u : 𝓢(V, Hr)) : Sρ (schwartzSobolevCoordinate s u) =
      schwartzSobolevCoordinate s (Mρ u) := by
    apply besselRealization_injective n r s
    rw [show besselRealization n r s (Sρ (schwartzSobolevCoordinate s u)) = _ from
      besselRealization_sobolevCutoffCLM s ρ hρ hcρ _,
      besselRealization_schwartzSobolevCoordinate, hMρ,
      besselRealization_schwartzSobolevCoordinate]
  have hsub (u : 𝓢(V, Hr)) : schwartzSobolevCoordinate s u - Sρ
      (schwartzSobolevCoordinate s u) = schwartzSobolevCoordinate s (u - Mρ u) := by
    rw [hSρ]
    apply besselRealization_injective n r s
    rw [map_sub, besselRealization_schwartzSobolevCoordinate,
      besselRealization_schwartzSobolevCoordinate, besselRealization_schwartzSobolevCoordinate]
    exact (map_sub (SchwartzMap.toTemperedDistributionCLM V Hr) u (Mρ u)).symm
  have hdiff (u : 𝓢(V, Hr)) :
      SchwartzMap.smulLeftCLM Hr (fun y ↦ 1 - (ρ y : ℂ)) u = u - Mρ u := by
    ext1 y
    simp only [Mρ, SchwartzMap.smulLeftCLM_apply_apply h1ρ,
      SchwartzMap.smulLeftCLM_apply_apply hρgrowth, sub_apply, sub_smul, one_smul]
  -- Each desired output order has its own bounded realization of the same smoothing symbol.
  apply isSmoothDistributionOn_of_forall_memSobolev
  intro t
  let b := offDiagonalSymbol χ ρ p
  have hb : IsSymbol Set.univ (s - t) b :=
    isSmoothingSymbol_offDiagonalSymbol m p hp χ ρ hχ hcχ hρ hcρ hone (s - t)
  have hbSupp : HasCompactSupport b := hasCompactSupport_offDiagonalSymbol χ ρ p hcχ
  obtain ⟨R, hR⟩ := exists_quantize_sobolev_extension (s - t) s b hb (tsupport b) hbSupp
    (fun x hx ξ ↦ congrFun (image_eq_zero_of_notMem_tsupport hx) ξ)
  have horder : s - (s - t) = t := by ring
  simp only [horder] at hR
  have htest (u : 𝓢(V, Hr)) :
      Mχ (besselRealization n q (s - m) (quantizeSobolev m s p hp hc
          (schwartzSobolevCoordinate s u - Sρ (schwartzSobolevCoordinate s u)))) =
        besselRealization n q t (R (schwartzSobolevCoordinate s u)) := by
    rw [hsub]
    ext1 φ
    rw [show Mχ (besselRealization n q (s - m)
        (quantizeSobolev m s p hp hc (schwartzSobolevCoordinate s (u - Mρ u)))) φ =
      besselRealization n q (s - m)
        (quantizeSobolev m s p hp hc (schwartzSobolevCoordinate s (u - Mρ u)))
          (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) from rfl,
      besselRealization_quantizeSobolev, hR]
    apply integral_congr_ae
    filter_upwards with x
    rw [show quantize b u x = χ x • quantize p
        (SchwartzMap.smulLeftCLM Hr (fun y ↦ 1 - (ρ y : ℂ)) u) x from
      quantize_offDiagonalSymbol m p hp χ ρ hχ hcχ hρ hcρ u x, hdiff,
      SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    rw [Complex.coe_smul, smul_comm]
    exact smul_assoc _ _ _
  -- Density extends the exact Schwartz identity to all input Bessel coordinates.
  have heq := (denseRange_schwartzSobolevCoordinate n r s).equalizer
    (Mχ.continuous.comp ((besselRealization n q (s - m)).continuous.comp
      ((quantizeSobolev m s p hp hc).continuous.comp
        (continuous_id.sub Sρ.continuous))))
    ((besselRealization n q t).continuous.comp R.continuous) (funext htest)
  exact (memSobolev_iff_exists_besselRealization t _).mpr
    ⟨R f, (congrFun heq f).symm⟩

set_option maxHeartbeats 800000 in

/-- SG 3.9: a spatially compact PDO creates no new singularities on any open set. -/
theorem isSmoothDistributionOn_quantizeSobolev
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hu : IsSmoothDistributionOn (besselRealization n r s f) U) :
    IsSmoothDistributionOn
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) U := by
  /- Fix x in U and choose real compact smooth χ,ρ supported in U, with χ=1 near x
  and ρ=1 on a neighborhood of tsupport χ. Stage 1: local smoothness of u makes
  ρu a smooth compactly supported function v, hence Schwartz. Bessel injectivity
  identifies its coordinates with sobolevCutoffCLM applied to f. Thus P(ρu) is
  smooth, by the exact Schwartz quantization identity. Stage 2: the separated
  contribution χP((1-ρ)u) is smooth by the preceding all-order argument. Adding
  χP(ρu) gives a smooth representative of χPu, which equals Pu near x. Glue these
  representatives over U. This uses no ellipticity and does not prove the converse
  implication, which would be elliptic regularity. The input is explicitly in H^s. -/
  let V := EuclideanSpace ℝ (Fin n)
  let Hq := EuclideanSpace ℂ (Fin q)
  let Q := quantizeSobolev m s p hp hc
  let B := besselRealization n q (s - m)
  apply (isSmoothDistributionOn_iff_disjoint_singularSupport _ U hU).mpr
  apply Set.disjoint_left.mpr
  intro x hxU hxs
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let ρ : ContDiffBump x :=
    { rIn := d / 2
      rOut := d
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let χ : ContDiffBump x :=
    { rIn := d / 8
      rOut := d / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hρU : tsupport (ρ : V → ℝ) ⊆ U := by
    rw [ρ.tsupport_eq]
    exact hdU
  have hone : tsupport (χ : V → ℝ) ⊆ interior {y | ρ y = 1} := by
    have hball : Metric.ball x ρ.rIn ⊆ {y | ρ y = 1} :=
      fun y hy ↦ ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    intro y hy
    apply (interior_maximal hball Metric.isOpen_ball)
    rw [χ.tsupport_eq] at hy
    change dist y x ≤ d / 4 at hy
    change dist y x < d / 2
    linarith
  let Sρ := sobolevCutoffCLM (r := r) s ρ ρ.contDiff ρ.hasCompactSupport
  let Mχ := TemperedDistribution.smulLeftCLM Hq (fun y ↦ (χ y : ℂ))
  have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
    (χ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp χ.contDiff)
  -- The smooth part of the input is an actual Schwartz function in the same coordinates.
  obtain ⟨v, hv⟩ := (isSmoothDistributionOn_iff_schwartz_cutoffs _ U hU).mp hu
    ρ ρ.contDiff ρ.hasCompactSupport hρU
  have hcoord : Sρ f = schwartzSobolevCoordinate s v := by
    apply besselRealization_injective n r s
    rw [show besselRealization n r s (Sρ f) = _ from
      besselRealization_sobolevCutoffCLM s ρ ρ.contDiff ρ.hasCompactSupport f,
      hv, besselRealization_schwartzSobolevCoordinate]
  obtain ⟨w, hw⟩ := exists_schwartz_quantize m p hp hc v
  have hPw : B (Q (Sρ f)) = (w : 𝓢'(V, Hq)) := by
    rw [hcoord]
    ext1 φ
    change besselRealization n q (s - m)
      (quantizeSobolev m s p hp hc (schwartzSobolevCoordinate s v)) φ = _
    rw [besselRealization_quantizeSobolev, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards with y
    change φ y • quantize p v y = φ y • w y
    rw [hw y]
  have hMχw : Mχ (w : 𝓢'(V, Hq)) =
      ((SchwartzMap.smulLeftCLM Hq (fun y ↦ (χ y : ℂ)) w) : 𝓢'(V, Hq)) := by
    ext1 φ
    simp only [Mχ, TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards with y
    simp only [SchwartzMap.smulLeftCLM_apply_apply hχgrowth, smul_eq_mul, smul_smul, mul_comm]
  have hlocal : IsSmoothDistributionOn (Mχ (B (Q (Sρ f)))) Set.univ := by
    rw [hPw, hMχw]
    exact isSmoothDistributionOn_schwartz _ Set.univ isOpen_univ
  -- The separated part is smooth at every Sobolev order, and linearity recombines the two parts.
  have hseparated : IsSmoothDistributionOn (Mχ (B (Q (f - Sρ f)))) Set.univ :=
    isSmoothDistributionOn_cutoff_quantizeSobolev_sub m s p hp hc
      χ ρ χ.contDiff χ.hasCompactSupport ρ.contDiff ρ.hasCompactSupport hone f
  have hwhole : IsSmoothDistributionOn (Mχ (B (Q f))) Set.univ := by
    have heq : Mχ (B (Q f)) = Mχ (B (Q (f - Sρ f))) + Mχ (B (Q (Sρ f))) := by
      simp only [map_sub]
      abel
    rw [heq]
    exact hseparated.add isOpen_univ hlocal
  obtain ⟨g, hg, hrepr⟩ := hwhole
  apply hxs
  refine ⟨Metric.ball x χ.rIn, Metric.isOpen_ball, Metric.mem_ball_self χ.rIn_pos,
    g, hg.mono (Set.subset_univ _), ?_⟩
  intro φ hφ hφball
  have hmult : SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ = φ := by
    ext1 y
    rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    by_cases hy : φ y = 0
    · simp [hy]
    rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall
      (hφball (subset_tsupport φ hy)))]
    simp
  have hpair := hrepr φ hφ (Set.subset_univ _)
  simpa only [Mχ, TemperedDistribution.smulLeftCLM_apply_apply, hmult] using hpair

/-- The pseudolocal property in the usual singular-support formulation. -/
theorem singularSupport_quantizeSobolev_subset
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    singularSupport
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) ⊆
        singularSupport (besselRealization n r s f) := by
  /- At a point outside the input singular support there is an open neighborhood
  on which the input distribution is smooth. Apply SG 3.9 with that same open
  set and Sobolev input to obtain a smooth output neighborhood. Taking the
  contrapositive gives the inclusion; it says nothing about ordinary support. -/
  intro x hx
  by_contra hnot
  have hnear : ∃ U : Set (EuclideanSpace ℝ (Fin n)), IsOpen U ∧ x ∈ U ∧
      IsSmoothDistributionOn (besselRealization n r s f) U := by
    simpa only [singularSupport, Set.mem_ofPred_eq, not_not] using hnot
  obtain ⟨U, hU, hxU, hu⟩ := hnear
  exact hx ⟨U, hU, hxU, isSmoothDistributionOn_quantizeSobolev m s p hp hc f U hU hu⟩

end AtiyahSinger
