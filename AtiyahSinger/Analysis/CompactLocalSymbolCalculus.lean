/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BesselSymbol
public import AtiyahSinger.Analysis.CompactQuantization
public import AtiyahSinger.Analysis.LocalComposition
public import AtiyahSinger.Analysis.SymbolExistence

import all AtiyahSinger.Analysis.SmoothingKernelSymbol
import AtiyahSinger.Analysis.SymbolCoordinateEstimates
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

/-!
# Compact local symbolic calculus

Public module ID: M0354.

Compact spatial symbols compose as actual Schwartz maps. The initial asymmetric
Fourier formula assumes proper support only for its right factor; compact spatial
support suffices on the left. Properization and the smoothing ideal later give
composition without an input-support axiom. Support-preserving Borel summation
keeps an entire correction series inside one fixed coordinate window.

For a smoothing right factor, its compact spatial symbol is jointly Schwartz;
partial Fourier transformation retains that decay, and absolutely integrable
Fubini gives the exact action. These local parametrix inputs preserve the actual
Schwartz maps and independent rectangular matrix ranks.

Sources: SG III.3.4 and III.3.10. The asymmetric support hypothesis and fixed-window
formulation are project supplements to the same Fourier and cutoff arguments.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped ContDiff SchwartzMap

variable {n r s t q : ℕ}

/-- A compact output symbol can be composed exactly with a properly supported right factor. -/
theorem quantize_compositionSymbol_of_compactSupport_left (l m : ℝ)
    (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (hpSupp : HasCompactSupport p)
    (P : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin t)))
    (Q : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s)))
    (hP : ∀ v x, P v x = quantize p v x) (hQ : ∀ u x, Q u x = quantize q u x)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hQK : HasOperatorSupport K Q)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχSupp : HasCompactSupport χ) (hone : K ⊆ interior {x | χ x = 1})
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (compositionSymbol χ p q) u x = P (Q u) x := by
  /- Stage 1: retain the supplied compact support of p and recover that of q. Let A=Q*
  be localFormalAdjoint and a=adjointSymbol χ q its exact left symbol. Its support
  is compact and the full pairing gives FourierSG(Qu)=rightSymbolFourierApply(a†)u.
  Stage 2: insert this equality into quantize p (Q u). Pull p(x,ξ) and exp(i<x,ξ>)
  inside the integrable y integral; this gives precisely leftRightAmplitude p (a†).
  Stage 3: apply the exact amplitude reduction theorem. The inverse normalization
  (2π)^(-n) occurs once, and the equality includes every lower-order and smoothing term. -/
  -- Only the right factor needs an actual input-support condition.
  have hqSupp : HasCompactSupport q := hK.of_isClosed_subset (isClosed_tsupport q)
    (tsupport_symbol_subset_of_hasOperatorSupport m q hq Q hQ K hK.isClosed hQK)
  let a := adjointSymbol χ q
  let A := localFormalAdjoint m q hq Q hQ K hK hQK
  have ha : IsSymbol Set.univ m a := isSymbol_adjointSymbol m q hq hqSupp χ hχ hχSupp
  have haSupp : HasCompactSupport a :=
    hχSupp.of_isClosed_subset (isClosed_tsupport _) (tsupport_adjointSymbol_subset χ q)
  have hb : IsSymbol Set.univ m (symbolAdjoint a) := ha.symbolAdjoint isOpen_univ
  have hbSupp : HasCompactSupport (symbolAdjoint a) := by
    simpa only [HasCompactSupport, tsupport_symbolAdjoint] using haSupp
  -- The full adjoint pairing identifies the Fourier transform of the same Q u.
  have hfourier (ξ : EuclideanSpace ℝ (Fin n)) :
      fourierSG (Q u) ξ = rightSymbolFourierApply (symbolAdjoint a) u ξ :=
    fourierSG_eq_rightSymbolFourierApply m a ha haSupp Q A
      (fun v x ↦ localFormalAdjoint_apply m q hq Q hQ K hK hQK χ hχ hχSupp hone v x)
      (isSchwartzFormalAdjoint_localFormalAdjoint m q hq Q hQ K hK hQK) u ξ
  have hreduce := quantize_amplitudeSymbol (l + m) (leftRightAmplitude p (symbolAdjoint a))
    (isAmplitude_leftRightAmplitude l m p _ hp hb)
    (hasCompactSupport_leftRightAmplitude p _ hpSupp hbSupp) u
  calc
    _ = amplitudeApply (leftRightAmplitude p (symbolAdjoint a)) u x := congrFun hreduce x
    _ = quantize p (Q u) x := by
      unfold amplitudeApply quantize
      congr 1
      apply integral_congr_ae
      filter_upwards with ξ
      rw [hfourier]
      unfold rightSymbolFourierApply
      -- At fixed frequency the right-symbol integrand is genuinely integrable in y.
      rw [← (p x ξ).integral_comp_comm
        (integrable_rightSymbolFourierApply m _ hb hbSupp u ξ), ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      have hphase : Complex.exp (Complex.I * (inner ℝ (x - y) ξ : ℂ)) =
          Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) *
            Complex.exp (-Complex.I * (inner ℝ y ξ : ℂ)) := by
        rw [← Complex.exp_add, inner_sub_left]
        congr 1
        push_cast
        ring
      simp only [leftRightAmplitude, ContinuousLinearMap.comp_apply, hphase, mul_smul, map_smul]
    _ = P (Q u) x := (hP (Q u) x).symm


/-- A fixed compact spatial support can be retained inside any prescribed open neighborhood. -/
theorem exists_symbol_expansion_with_compact_support
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (m : ℕ → ℝ) (hm : StrictAnti m)
    (hlim : Filter.Tendsto m Filter.atTop Filter.atBot)
    (terms : ℕ → SymbolFunction n r q)
    (hterms : ∀ j, IsSymbol Set.univ (m j) (terms j))
    (hsupport : ∀ j, tsupport (terms j) ⊆ K) :
    ∃ a : SymbolFunction n r q,
      HasSymbolExpansion Set.univ m a terms ∧ HasCompactSupport a ∧ tsupport a ⊆ U := by
  -- Choose one spatial plateau for the entire series, before choosing the asymptotic sum.
  obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ, _, hχsupport, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
  have hcχ : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupport] using hOc
  have hχU : tsupport χ ⊆ U := by
    simpa only [tsupport, hχsupport] using hOU
  obtain ⟨b, hb⟩ := exists_symbol_expansion Set.univ isOpen_univ m hm hlim terms hterms
  let a := zeroExtendedSymbol Set.univ χ b
  refine ⟨a, ?_, hasCompactSupport_zeroExtendedSymbol Set.univ χ b hcχ,
    (tsupport_zeroExtendedSymbol_subset Set.univ χ b).trans hχU⟩
  intro N
  -- The same cutoff fixes every original term, so it also fixes every finite partial sum.
  have hfix (j : ℕ) (x ξ : EuclideanSpace ℝ (Fin n)) :
      χ x • terms j x ξ = terms j x ξ := by
    by_cases hx : x ∈ tsupport (terms j)
    · rw [(hχone x).mp (hsupport j hx), one_smul]
    · have hz : terms j x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hz]
  have heq : a - ∑ j ∈ Finset.range N, terms j =
      zeroExtendedSymbol Set.univ χ (b - ∑ j ∈ Finset.range N, terms j) := by
    funext x ξ
    simp only [a, zeroExtendedSymbol_apply_of_mem Set.univ χ _ x ξ (Set.mem_univ x),
      Pi.sub_apply, Finset.sum_apply, smul_sub, Finset.smul_sum, Complex.coe_smul, hfix]
  rw [heq]
  -- Zero extension of each compactly cut-off remainder retains its original remainder order.
  exact isSymbol_zeroExtendedSymbol Set.univ isOpen_univ (m N) χ hχ hcχ
    (Set.subset_univ _) _ (hb N)


/-! ## Smoothing symbols and joint Schwartz functions -/

section

private theorem exists_schwartz_of_isSmoothingSymbol {n r q : ℕ}
    (c : SymbolFunction n r q) (hc : IsSmoothingSymbol Set.univ c)
    (hcc : HasCompactSupport c) :
    ∃ S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)),
      ∀ x ξ, S (x, ξ) = c x ξ := by
  let X := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hs : ContDiff ℝ ∞ (Function.uncurry c) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hc 0).1
  have hsupport : tsupport (Function.uncurry c) ⊆ Prod.fst ⁻¹' tsupport c := by
    apply closure_minimal ?_ ((isClosed_tsupport c).preimage continuous_fst)
    intro z hz
    by_contra hout
    have hzero := image_eq_zero_of_notMem_tsupport hout
    apply hz
    exact congrFun hzero z.2
  refine ⟨{ toFun := Function.uncurry c, smooth' := hs, decay' := ?_ }, fun _ _ ↦ rfl⟩
  intro k d
  obtain ⟨R, hR⟩ := hcc.isBounded.exists_norm_le
  have hbounds (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ tsupport c, ∀ ξ,
        ‖symbolDerivative c i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
    obtain ⟨C, hC, hbound⟩ := (hc (-(k : ℝ))).2 (tsupport c) (Set.subset_univ _) hcc i j
    refine ⟨C, hC, fun x hx ξ ↦ (hbound x hx ξ).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ])
      (by linarith [Nat.cast_nonneg (α := ℝ) j])
  choose C hC hbound using hbounds
  let D := ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1), C i j
  have hD : 0 ≤ D :=
    Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j))
  have hCD (i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) : C i j ≤ D := by
    have h₁ := Finset.single_le_sum (s := Finset.range (d + 1))
      (fun k _ ↦ hC i k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h₂ := Finset.single_le_sum (s := Finset.range (d + 1))
      (f := fun k ↦ ∑ j ∈ Finset.range (d + 1), C k j)
      (fun k _ ↦ Finset.sum_nonneg (fun j _ ↦ hC k j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact h₁.trans h₂
  refine ⟨(max R 1) ^ k * (2 ^ d * D), ?_⟩
  intro z
  by_cases hz : z.1 ∈ tsupport c
  · have hfull : ‖iteratedFDeriv ℝ d (Function.uncurry c) z‖ ≤
        2 ^ d * (D * (1 + ‖z.2‖) ^ (-(k : ℝ))) := by
      apply norm_iteratedFDeriv_uncurry_le_of_mixed c hs d z.1 z.2 _ (by positivity)
      intro i hi j hj
      exact (hbound i j z.1 hz z.2).trans
        (mul_le_mul_of_nonneg_right (hCD i j hi hj) (by positivity))
    have hnorm : ‖z‖ ≤ max R 1 * (1 + ‖z.2‖) := by
      rw [Prod.norm_def]
      apply max_le
      · have hx := hR z.1 hz
        nlinarith [le_max_left R 1, le_max_right R 1, norm_nonneg z.2]
      · nlinarith [le_max_right R 1, norm_nonneg z.2]
    have hcancel : (1 + ‖z.2‖) ^ k * (1 + ‖z.2‖) ^ (-(k : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), add_neg_cancel,
        Real.rpow_zero]
    calc
      _ ≤ (max R 1 * (1 + ‖z.2‖)) ^ k *
          (2 ^ d * (D * (1 + ‖z.2‖) ^ (-(k : ℝ)))) := by gcongr
      _ = ((max R 1) ^ k * (2 ^ d * D)) *
          ((1 + ‖z.2‖) ^ k * (1 + ‖z.2‖) ^ (-(k : ℝ))) := by rw [mul_pow]; ring
      _ = (max R 1) ^ k * (2 ^ d * D) := by rw [hcancel, mul_one]
  · have hout : z ∉ tsupport (Function.uncurry c) := fun h ↦ hz (hsupport h)
    have hzero : iteratedFDeriv ℝ d (Function.uncurry c) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout (tsupport_iteratedFDeriv_subset d h))
    rw [hzero, norm_zero, mul_zero]
    positivity

/-- Compact spatial symbol support makes the joint symbol a temperate multiplier. -/
private theorem hasTemperateGrowth_uncurry_of_isSymbol {n r q : ℕ}
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hcp : HasCompactSupport p) :
    Function.HasTemperateGrowth (Function.uncurry p) := by
  have hs : ContDiff ℝ ∞ (Function.uncurry p) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using hp.1
  have hsupport : tsupport (Function.uncurry p) ⊆ Prod.fst ⁻¹' tsupport p := by
    apply closure_minimal ?_ ((isClosed_tsupport p).preimage continuous_fst)
    intro z hz
    by_contra hout
    exact hz (congrFun (image_eq_zero_of_notMem_tsupport hout) z.2)
  refine ⟨hs, ?_⟩
  intro d
  have hbounds (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ tsupport p, ∀ ξ,
      ‖symbolDerivative p i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ ⌈m⌉₊ := by
    obtain ⟨C, hC, hbound⟩ := hp.2 (tsupport p) (Set.subset_univ _) hcp i j
    refine ⟨C, hC, fun x hx ξ ↦ (hbound x hx ξ).trans ?_⟩
    apply mul_le_mul_of_nonneg_left _ hC
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ])
    exact (sub_le_self _ (Nat.cast_nonneg j)).trans (Nat.le_ceil m)
  choose C hC hbound using hbounds
  let D := ∑ i ∈ Finset.range (d + 1), ∑ j ∈ Finset.range (d + 1), C i j
  have hD : 0 ≤ D :=
    Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hC i j))
  have hCD (i j : ℕ) (hi : i ≤ d) (hj : j ≤ d) : C i j ≤ D := by
    have h₁ := Finset.single_le_sum (s := Finset.range (d + 1))
      (fun k _ ↦ hC i k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have h₂ := Finset.single_le_sum (s := Finset.range (d + 1))
      (f := fun k ↦ ∑ j ∈ Finset.range (d + 1), C k j)
      (fun k _ ↦ Finset.sum_nonneg (fun j _ ↦ hC k j))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact h₁.trans h₂
  refine ⟨⌈m⌉₊, 2 ^ d * D, ?_⟩
  intro z
  by_cases hz : z.1 ∈ tsupport p
  · have hfull : ‖iteratedFDeriv ℝ d (Function.uncurry p) z‖ ≤
        2 ^ d * (D * (1 + ‖z.2‖) ^ ⌈m⌉₊) := by
      apply norm_iteratedFDeriv_uncurry_le_of_mixed p hs d z.1 z.2 _ (by positivity)
      intro i hi j hj
      exact (hbound i j z.1 hz z.2).trans
        (mul_le_mul_of_nonneg_right (hCD i j hi hj) (by positivity))
    calc
      _ ≤ 2 ^ d * (D * (1 + ‖z.2‖) ^ ⌈m⌉₊) := hfull
      _ ≤ 2 ^ d * (D * (1 + ‖z‖) ^ ⌈m⌉₊) := by
        gcongr
        exact norm_snd_le z
      _ = _ := by ring
  · have hout : z ∉ tsupport (Function.uncurry p) := fun h ↦ hz (hsupport h)
    have hzero : iteratedFDeriv ℝ d (Function.uncurry p) z = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hout (tsupport_iteratedFDeriv_subset d h))
    rw [hzero, norm_zero]
    positivity

/-- A joint Schwartz function is a symbol of every real order. -/
private theorem isSmoothingSymbol_of_schwartz {n r q : ℕ}
    (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) :
    IsSmoothingSymbol Set.univ (fun x ξ ↦ S (x, ξ)) := by
  intro m
  refine ⟨?_, ?_⟩
  · change ContDiffOn ℝ ∞ (Function.uncurry (fun x ξ ↦ S (x, ξ)))
      (Set.univ ×ˢ Set.univ)
    exact S.smooth'.contDiffOn
  · intro K _ _ i j
    let k : ℕ := ⌈(j : ℝ) - m⌉₊
    let C : ℝ := 2 ^ k * (Finset.Iic (k, i + j)).sup
      (fun d ↦ SchwartzMap.seminorm ℝ d.1 d.2) S
    have hC : 0 ≤ C := by positivity
    refine ⟨C, hC, ?_⟩
    intro x _ ξ
    have hm := norm_mixed_iteratedFDeriv_le (fun x ξ ↦ S (x, ξ)) S.smooth' i j x ξ
    have hweight : (1 + ‖ξ‖) ^ k *
        ‖symbolDerivative (fun x ξ ↦ S (x, ξ)) i j x ξ‖ ≤ C := by
      have hnorm : ‖ξ‖ ≤ ‖(x, ξ)‖ := norm_snd_le (x, ξ)
      calc
        _ ≤ (1 + ‖(x, ξ)‖) ^ k * ‖iteratedFDeriv ℝ (i + j) S (x, ξ)‖ := by
          apply mul_le_mul _ hm (norm_nonneg _) (by positivity)
          gcongr
        _ ≤ C := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
          (m := (k, i + j)) (le_refl _) (le_refl _) S (x, ξ)
    have hfirst : ‖symbolDerivative (fun x ξ ↦ S (x, ξ)) i j x ξ‖ ≤
        C * (1 + ‖ξ‖) ^ (-(k : ℝ)) := by
      apply (le_of_mul_le_mul_left ?_ (by positivity : 0 < (1 + ‖ξ‖) ^ k))
      have hc : (1 + ‖ξ‖) ^ k * (1 + ‖ξ‖) ^ (-(k : ℝ)) = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), add_neg_cancel,
          Real.rpow_zero]
      calc
        _ ≤ C := hweight
        _ = (1 + ‖ξ‖) ^ k * (C * (1 + ‖ξ‖) ^ (-(k : ℝ))) := by
          calc
            _ = C * ((1 + ‖ξ‖) ^ k * (1 + ‖ξ‖) ^ (-(k : ℝ))) := by rw [hc, mul_one]
            _ = _ := by ring
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ])
    have hk : (j : ℝ) - m ≤ (k : ℝ) := Nat.le_ceil _
    linarith

end


/-! ## Partial Fourier transformation with compact spatial support -/

section

variable {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- Partial Fourier transform preserves joint Schwartz decay under compact spatial support. -/
private def partialFourierSchwartz [CompleteSpace W] [SecondCountableTopology W]
    (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hS : tsupport S ⊆ Prod.fst ⁻¹' K) :
    𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W) := by
  let partialFourierDerivative {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W)) :
      𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ] W) := by
    let X := EuclideanSpace ℝ (Fin n)
    let D := X × X
    let R : D →L[ℝ] D :=
      (ContinuousLinearMap.inr ℝ X X).comp (ContinuousLinearMap.fst ℝ X X)
    let C : (D →L[ℝ] W) →L[ℝ] (D →L[ℝ] W) :=
      (ContinuousLinearMap.compL ℝ D D W).flip R
    let L : D →L[ℝ] D →L[ℝ] ℝ :=
      ((ContinuousLinearMap.compL ℝ D X ℝ).flip (ContinuousLinearMap.snd ℝ X X)).comp
        ((innerSL ℝ).comp (ContinuousLinearMap.fst ℝ X X))
    exact SchwartzMap.postcompCLM C (SchwartzMap.fderivCLM ℝ D W S) +
      ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) • SchwartzMap.smulRightCLM ℝ W L S
  have partialFourierDerivative_apply {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (y ξ u v : EuclideanSpace ℝ (Fin n)) :
      partialFourierDerivative S (y, ξ) (u, v) =
        fderiv ℝ S (y, ξ) (0, u) +
          ((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) • ((inner ℝ y v) • S (y, ξ)) := by
    simp [partialFourierDerivative, SchwartzMap.postcompCLM_apply,
      SchwartzMap.fderivCLM_apply, SchwartzMap.smulRightCLM_apply_apply]
  have partialFourierDerivative_support {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (K : Set (EuclideanSpace ℝ (Fin n)))
      (hS : tsupport S ⊆ Prod.fst ⁻¹' K) :
      tsupport (partialFourierDerivative S) ⊆ Prod.fst ⁻¹' K := by
    apply Set.Subset.trans (b := tsupport S) ?_ hS
    apply closure_minimal ?_ (isClosed_tsupport S)
    intro z hz
    by_contra hout
    have hzero : S z = 0 := image_eq_zero_of_notMem_tsupport hout
    have hder : fderiv ℝ S z = 0 := by
      exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hout (tsupport_fderiv_subset ℝ h))
    apply hz
    apply ContinuousLinearMap.ext
    intro v
    rcases z with ⟨y, ξ⟩
    rcases v with ⟨u, v⟩
    simp only [partialFourierDerivative_apply, hzero, hder, zero_apply,
      smul_zero, add_zero]
  /- Differentiating the partial Fourier integrand retains an actual Schwartz amplitude. -/
  have hasFDerivAt_partialFourier_integrand {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (y : EuclideanSpace ℝ (Fin n))
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      HasFDerivAt
        (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
          Complex.exp (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) •
            S (y, z.1))
        (Complex.exp (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) •
          partialFourierDerivative S (y, z.1)) z := by
    let X := EuclideanSpace ℝ (Fin n)
    let D := X × X
    let a : ℂ := (-(2 * Real.pi : ℝ) : ℂ) * Complex.I
    let L : D →L[ℝ] ℂ := a •
      (Complex.ofRealCLM.comp ((innerSL ℝ y).comp (ContinuousLinearMap.snd ℝ X X)))
    let R : D →L[ℝ] D :=
      (ContinuousLinearMap.inr ℝ X X).comp (ContinuousLinearMap.fst ℝ X X)
    have hp : HasFDerivAt (fun z ↦ Complex.exp (L z)) (Complex.exp (L z) • L) z :=
      L.hasFDerivAt.cexp
    have hf : HasFDerivAt (fun z : D ↦ S (y, z.1))
        ((fderiv ℝ S (y, z.1)).comp R) z := by
      apply (S.hasFDerivAt (y, z.1)).comp z
      exact (hasFDerivAt_const y z).prodMk (ContinuousLinearMap.fst ℝ X X).hasFDerivAt
    convert hp.smul hf using 1
    · ext w
      rfl
    · apply ContinuousLinearMap.ext
      intro w
      rcases w with ⟨u, v⟩
      simp only [partialFourierDerivative_apply, smul_apply,
        add_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.smulRight_apply, L, R, ContinuousLinearMap.inr_apply,
        Complex.ofRealCLM_apply, innerSL_apply_apply, smul_add, smul_smul, a]
      change Complex.exp (a * (inner ℝ y z.2 : ℂ)) •
          fderiv ℝ S (y, z.1) (0, u) +
            (Complex.exp (a * (inner ℝ y z.2 : ℂ)) * a) • (inner ℝ y v) • S (y, z.1) =
        Complex.exp (a * (inner ℝ y z.2 : ℂ)) •
          fderiv ℝ S (y, z.1) (0, u) +
            ((Complex.exp (a * (inner ℝ y z.2 : ℂ)) * a) * (inner ℝ y v : ℂ)) • S (y, z.1)
      rw [← Complex.coe_smul, smul_smul]
  /- Fixed compact support supplies the domination for every parameter derivative. -/
  have contDiff_integral_of_fixed_compact_support
      {P V : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
      [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
      [SecondCountableTopology V]
      (f : P → EuclideanSpace ℝ (Fin n) → V)
      (hf : ContDiff ℝ ∞ (Function.uncurry f))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hz : ∀ x y, y ∉ K → f x y = 0) :
      ContDiff ℝ ∞ (fun x ↦ ∫ y, f x y) ∧
        ∀ k x, Integrable (fun y ↦ iteratedFDeriv ℝ k (fun x ↦ f x y) x) ∧
          iteratedFDeriv ℝ k (fun x ↦ ∫ y, f x y) x =
            ∫ y, iteratedFDeriv ℝ k (fun x ↦ f x y) x := by
    apply contDiff_integral_of_compact_bounds f hf
    intro L hL k
    have hD := hf.continuous_iteratedFDeriv (by simp : (k : ℕ∞ω) ≤ ∞)
    obtain ⟨R, hR⟩ := ((hL.prod hK).image hD).isBounded.exists_norm_le
    refine ⟨K.indicator (fun _ ↦ max R 0),
      (integrable_indicator_iff hK.measurableSet).mpr
        (integrableOn_const (μ := volume) (C := max R 0) hK.measure_lt_top.ne), ?_⟩
    intro x hx y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      have hnorm := norm_mixed_iteratedFDeriv_le f hf k 0 x y
      have heq : (fun x ↦ iteratedFDeriv ℝ 0 (f x) y) =
          (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin n)) V).symm ∘
            (fun x ↦ f x y) := rfl
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero] at hnorm
      exact hnorm.trans ((hR _ ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left _ _))
    · rw [Set.indicator_of_notMem hy]
      have hzero : (fun x ↦ f x y) = 0 := funext (fun x ↦ hz x y hy)
      rw [hzero, iteratedFDeriv_zero, Pi.zero_apply, norm_zero]
  /- Partial spatial Fourier transform, with the frequency parameter retained unchanged. -/
  let partialFourier {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) : W :=
    𝓕 (fun y ↦ S (y, z.1)) z.2
  have partialFourier_eq_integral {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      partialFourier S z = ∫ y, Complex.exp
        (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) • S (y, z.1) := by
    dsimp only [partialFourier]
    rw [Real.fourier_eq']
    apply integral_congr_ae
    filter_upwards with y
    congr 2
    push_cast
    ring
  /- Uniformly compact spatial support makes the partial Fourier transform jointly smooth. -/
  have contDiff_partialFourier {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hS : tsupport S ⊆ Prod.fst ⁻¹' K) :
      ContDiff ℝ ∞ (partialFourier S) := by
    let X := EuclideanSpace ℝ (Fin n)
    let F : (X × X) → X → W := fun z y ↦ Complex.exp
      (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) • S (y, z.1)
    have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
      have hSf : ContDiff ℝ ∞ (fun z : (X × X) × X ↦ S (z.2, z.1.1)) :=
        S.smooth'.comp (contDiff_snd.prodMk contDiff_fst.fst)
      have hi : ContDiff ℝ ∞ (fun z : (X × X) × X ↦ (inner ℝ z.2 z.1.2 : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_snd.inner ℝ contDiff_fst.snd)
      exact (contDiff_const.mul hi).cexp.smul hSf
    have hzero (z : X × X) (y : X) (hy : y ∉ K) : F z y = 0 := by
      have hSz : S (y, z.1) = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hS h))
      simp only [F, hSz, smul_zero]
    have heq : partialFourier S = fun z ↦ ∫ y, F z y := by
      funext z
      exact partialFourier_eq_integral S z
    rw [heq]
    exact (contDiff_integral_of_fixed_compact_support F hF K hK hzero).1
  /- The partial transform commutes with its explicit Schwartz-valued derivative amplitude. -/
  have fderiv_partialFourier {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hS : tsupport S ⊆ Prod.fst ⁻¹' K)
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (partialFourier S) z = partialFourier (partialFourierDerivative S) z := by
    let X := EuclideanSpace ℝ (Fin n)
    let F : (X × X) → X → W := fun z y ↦ Complex.exp
      (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) • S (y, z.1)
    have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
      have hSf : ContDiff ℝ ∞ (fun z : (X × X) × X ↦ S (z.2, z.1.1)) :=
        S.smooth'.comp (contDiff_snd.prodMk contDiff_fst.fst)
      have hi : ContDiff ℝ ∞ (fun z : (X × X) × X ↦ (inner ℝ z.2 z.1.2 : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp (contDiff_snd.inner ℝ contDiff_fst.snd)
      exact (contDiff_const.mul hi).cexp.smul hSf
    have hzero (z : X × X) (y : X) (hy : y ∉ K) : F z y = 0 := by
      have hSz : S (y, z.1) = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hS h))
      simp only [F, hSz, smul_zero]
    have heq : partialFourier S = fun z ↦ ∫ y, F z y := by
      funext z
      exact partialFourier_eq_integral S z
    obtain ⟨hI, hD⟩ := contDiff_integral_of_fixed_compact_support F hF K hK hzero
    have hTD : tsupport (partialFourierDerivative S) ⊆ Prod.fst ⁻¹' K :=
      partialFourierDerivative_support S K hS
    let G : X → (X × X) →L[ℝ] W := fun y ↦ Complex.exp
      (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ)) •
        partialFourierDerivative S (y, z.1)
    have hGc : Continuous G := by
      have hp : Continuous (fun y : X ↦ Complex.exp
          (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) * (inner ℝ y z.2 : ℂ))) := by
        fun_prop
      exact hp.smul ((partialFourierDerivative S).continuous.comp
        (continuous_id.prodMk continuous_const))
    have hGs : HasCompactSupport G := by
      apply hK.of_isClosed_subset isClosed_closure
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hout
      have ht : partialFourierDerivative S (y, z.1) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hout (hTD h))
      exact hy (by simp [G, ht])
    have hGi : Integrable G := hGc.integrable_of_hasCompactSupport hGs
    apply ContinuousLinearMap.ext
    intro v
    have hOne := congrArg (fun A ↦ A (fun _ : Fin 1 ↦ v)) (hD 1 z).2
    rw [ContinuousMultilinearMap.integral_apply (hD 1 z).1] at hOne
    simp only [iteratedFDeriv_one_apply] at hOne
    rw [heq, hOne, partialFourier_eq_integral]
    change (∫ y, fderiv ℝ (fun x ↦ F x y) z v) = (∫ y, G y) v
    rw [ContinuousLinearMap.integral_apply hGi]
    apply integral_congr_ae
    filter_upwards with y
    exact congrArg (fun A ↦ A v) (hasFDerivAt_partialFourier_integrand S y z).fderiv
  /- The partial Fourier transform has rapid joint decay in the retained and dual frequencies. -/
  have partialFourier_decay {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hS : tsupport S ⊆ Prod.fst ⁻¹' K) (k : ℕ) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖z‖ ^ k * ‖partialFourier S z‖ ≤ C := by
    let X := EuclideanSpace ℝ (Fin n)
    let f : X → X → X → W := fun ξ _ y ↦ (1 + ‖ξ‖) ^ k • S (y, ξ)
    have hfs (ξ η : X) : ContDiff ℝ ∞ (f ξ η) :=
      (S.smooth'.comp (contDiff_id.prodMk contDiff_const)).const_smul _
    have hfc (ξ η : X) : tsupport (f ξ η) ⊆ K := by
      apply closure_minimal ?_ hK.isClosed
      intro y hy
      by_contra hout
      have hs : S (y, ξ) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h ↦ hout (hS h))
      exact hy (by simp [f, hs])
    have hb (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ η y, y ∈ K →
        ‖iteratedFDeriv ℝ i (f ξ η) y‖ ≤ C * (1 + ‖η‖) ^ (0 : ℕ) := by
      let C : ℝ := 2 ^ k * (Finset.Iic (k, i)).sup
        (fun j ↦ SchwartzMap.seminorm ℝ j.1 j.2) S
      have hC : 0 ≤ C := by positivity
      refine ⟨C, hC, ?_⟩
      intro ξ η y _
      have hs : ContDiff ℝ ∞ (fun y : X ↦ S (y, ξ)) :=
        S.smooth'.comp (contDiff_id.prodMk contDiff_const)
      have hm := norm_mixed_iteratedFDeriv_le (fun y ξ : X ↦ S (y, ξ)) S.smooth' i 0 y ξ
      have heq : (fun y : X ↦ iteratedFDeriv ℝ 0 (fun ξ : X ↦ S (y, ξ)) ξ) =
          (continuousMultilinearCurryFin0 ℝ X W).symm ∘ (fun y : X ↦ S (y, ξ)) := rfl
      rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero] at hm
      have hw := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (k, i)) (le_refl k) (le_refl i) S (y, ξ)
      have hnorm : ‖ξ‖ ≤ ‖(y, ξ)‖ := by
        rw [Prod.norm_def]
        exact le_max_right _ _
      dsimp only [f]
      rw [iteratedFDeriv_const_smul_apply' (hs.of_le (by simp)).contDiffAt,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      simpa only [pow_zero, mul_one] using
        (mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖ξ‖ ≤ 1 + ‖(y, ξ)‖) k)
          hm (norm_nonneg _) (by positivity)).trans hw
    obtain ⟨C, hC, hbound⟩ := fourier_diagonal_decay_of_compact_support f hfs K hK hfc
      0 hb 1 one_ne_zero k
    refine ⟨C, hC, ?_⟩
    intro z
    have hFourier : 𝓕 (f z.1 z.2) z.2 =
        (1 + ‖z.1‖) ^ k • partialFourier S z := by
      rw [Real.fourier_eq', partialFourier_eq_integral, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with y
      change Complex.exp ((-2 * Real.pi * inner ℝ y z.2 : ℝ) * Complex.I) •
          ((1 + ‖z.1‖) ^ k • S (y, z.1)) =
        (1 + ‖z.1‖) ^ k •
          (Complex.exp (((-(2 * Real.pi : ℝ) : ℂ) * Complex.I) *
            (inner ℝ y z.2 : ℂ)) • S (y, z.1))
      rw [smul_comm]
      congr 2
      push_cast
      ring
    have hvalue := hbound z.1 z.2
    rw [one_smul, hFourier, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)] at hvalue
    have hweight : ‖z‖ ≤ (1 + ‖z.1‖) * (1 + ‖z.2‖) := by
      rw [Prod.norm_def]
      apply max_le <;> nlinarith [norm_nonneg z.1, norm_nonneg z.2]
    have hcancel : (1 + ‖z.2‖) ^ k * (1 + ‖z.2‖) ^ (-(k : ℝ)) = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), add_neg_cancel,
        Real.rpow_zero]
    calc
      _ ≤ ((1 + ‖z.1‖) * (1 + ‖z.2‖)) ^ k * ‖partialFourier S z‖ := by gcongr
      _ = (1 + ‖z.2‖) ^ k * ((1 + ‖z.1‖) ^ k * ‖partialFourier S z‖) := by
        rw [mul_pow]
        ring
      _ ≤ (1 + ‖z.2‖) ^ k * (C * (1 + ‖z.2‖) ^ (-(k : ℝ))) := by gcongr
      _ = C := by rw [← mul_assoc, mul_comm _ C, mul_assoc, hcancel, mul_one]
  /- Iterating the explicit derivative amplitude proves decay at every derivative order. -/
  have partialFourier_iteratedFDeriv_decay {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
      [CompleteSpace W] [SecondCountableTopology W]
      (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n), W))
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
      (hS : tsupport S ⊆ Prod.fst ⁻¹' K) (k d : ℕ) :
      ∃ C : ℝ, ∀ z, ‖z‖ ^ k * ‖iteratedFDeriv ℝ d (partialFourier S) z‖ ≤ C := by
    induction d generalizing W with
    | zero =>
      obtain ⟨C, _, hC⟩ := partialFourier_decay S K hK hS k
      refine ⟨C, ?_⟩
      intro z
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
        LinearIsometryEquiv.norm_map] using hC z
    | succ d ih =>
      obtain ⟨C, hC⟩ := ih (partialFourierDerivative S)
        (partialFourierDerivative_support S K hS)
      refine ⟨C, ?_⟩
      intro z
      rw [← norm_iteratedFDeriv_fderiv]
      have hd : fderiv ℝ (partialFourier S) =
          partialFourier (partialFourierDerivative S) :=
        funext (fderiv_partialFourier S K hK hS)
      rw [hd]
      exact hC z
  exact {
    toFun := partialFourier S
    smooth' := contDiff_partialFourier S K hK hS
    decay' := partialFourier_iteratedFDeriv_decay S K hK hS }

end


/-! ## Product and marginal Schwartz operations -/

section

/-- External scalar multiplication preserves Schwartz decay on a product of spaces. -/
private theorem exists_schwartz_external_smul
    {P Q W : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (φ : 𝓢(P, ℂ)) (ψ : 𝓢(Q, W)) :
    ∃ f : 𝓢(P × Q, W), ∀ z : P × Q, f z = φ z.1 • ψ z.2 := by
  /- Stage 1: the function (x,y) ↦ φ(x)ψ(y) is smooth by the product rule.
  Each mixed derivative is a finite sum of products of derivatives of the
  two factors. Stage 2: the product norm is the maximum of the two norms.
  Bound each polynomial weight by the sum of the corresponding factor
  weights and use the two Schwartz decay bounds. These estimates provide
  the actual SchwartzMap smoothness and decay fields, with this function. -/
  -- Projection pullback does not increase any derivative norm.
  have hproj {D E Z : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
      [NormedAddCommGroup E] [NormedSpace ℝ E]
      [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (f : 𝓢(E, Z)) (p : D →L[ℝ] E) (hp : ‖p‖ ≤ 1)
      (i : ℕ) (z : D) :
      ‖iteratedFDeriv ℝ i (f ∘ p) z‖ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ := by
    rw [p.iteratedFDeriv_comp_right (f.smooth ⊤) z (by simp)]
    calc
      _ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ * ∏ _ : Fin i, ‖p‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ i f (p z)‖ * ∏ _ : Fin i, (1 : ℝ) := by
        gcongr
      _ = ‖iteratedFDeriv ℝ i f (p z)‖ := by simp
  have hφ : ContDiff ℝ ∞ (fun z : P × Q ↦ φ z.1) :=
    (φ.smooth ⊤).comp contDiff_fst
  have hψ : ContDiff ℝ ∞ (fun z : P × Q ↦ ψ z.2) :=
    (ψ.smooth ⊤).comp contDiff_snd
  refine ⟨⟨fun z ↦ φ z.1 • ψ z.2, hφ.smul hψ, ?_⟩, fun _ ↦ rfl⟩
  intro k j
  -- Leibniz bounds each derivative by finitely many products of factor derivatives.
  refine ⟨∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
    (SchwartzMap.seminorm ℂ k i φ * SchwartzMap.seminorm ℂ 0 (j - i) ψ +
      SchwartzMap.seminorm ℂ 0 i φ * SchwartzMap.seminorm ℂ k (j - i) ψ), ?_⟩
  intro z
  have hweight : ‖z‖ ^ k ≤ ‖z.1‖ ^ k + ‖z.2‖ ^ k := by
    rw [Prod.norm_def]
    rcases le_total ‖z.1‖ ‖z.2‖ with h | h
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
    · rw [max_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
  calc
    ‖z‖ ^ k * ‖iteratedFDeriv ℝ j (fun z : P × Q ↦ φ z.1 • ψ z.2) z‖ ≤
        ‖z‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i (fun z : P × Q ↦ φ z.1) z‖ *
          ‖iteratedFDeriv ℝ (j - i) (fun z : P × Q ↦ ψ z.2) z‖ := by
      gcongr
      exact norm_iteratedFDeriv_smul_le hφ hψ z (by simp)
    _ ≤ ‖z‖ ^ k * ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          ‖iteratedFDeriv ℝ i φ z.1‖ * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖ := by
      gcongr with i hi
      · exact hproj φ (ContinuousLinearMap.fst ℝ P Q)
          (ContinuousLinearMap.norm_fst_le ..) i z
      · exact hproj ψ (ContinuousLinearMap.snd ℝ P Q)
          (ContinuousLinearMap.norm_snd_le ..) (j - i) z
    _ = ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) *
          (‖z‖ ^ k * (‖iteratedFDeriv ℝ i φ z.1‖ *
            ‖iteratedFDeriv ℝ (j - i) ψ z.2‖)) := by
      rw [Finset.mul_sum]
      congr 1
      funext i
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      calc
        _ ≤ (‖z.1‖ ^ k + ‖z.2‖ ^ k) *
            (‖iteratedFDeriv ℝ i φ z.1‖ * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖) := by
          gcongr
        _ = (‖z.1‖ ^ k * ‖iteratedFDeriv ℝ i φ z.1‖) *
              ‖iteratedFDeriv ℝ (j - i) ψ z.2‖ +
            ‖iteratedFDeriv ℝ i φ z.1‖ *
              (‖z.2‖ ^ k * ‖iteratedFDeriv ℝ (j - i) ψ z.2‖) := by ring
        _ ≤ _ := by
          gcongr
          · exact SchwartzMap.le_seminorm ℂ k i φ z.1
          · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ ψ (j - i) z.2
          · exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ φ i z.1
          · exact SchwartzMap.le_seminorm ℂ k (j - i) ψ z.2


/-- Integrating one Euclidean variable produces a Schwartz function on the retained space. -/
private theorem exists_schwartz_integral_snd {n : ℕ} {P W : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    [SecondCountableTopology W]
    (S : 𝓢(P × EuclideanSpace ℝ (Fin n), W)) :
    ∃ T : 𝓢(P, W), ∀ x, T x = ∫ y, S (x, y) := by
  let X := EuclideanSpace ℝ (Fin n)
  let f : P → X → W := fun x y ↦ S (x, y)
  let decay : X → ℝ := fun y ↦ (1 + ‖y‖) ^ (-((n + 1 : ℕ) : ℝ))
  have hdecay : Integrable decay := integrable_one_add_norm (by simp [X])
  have hfs : ContDiff ℝ ∞ (Function.uncurry f) := S.smooth'
  -- A joint Schwartz weight controls both the retained parameter and an integrable tail.
  have hbound (k i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y,
      (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖ ≤ C * decay y := by
    let C : ℝ := 2 ^ (k + (n + 1)) * (Finset.Iic (k + (n + 1), i)).sup
      (fun d ↦ SchwartzMap.seminorm ℝ d.1 d.2) S
    refine ⟨C, by positivity, ?_⟩
    intro x y
    have hm := norm_mixed_iteratedFDeriv_le f hfs i 0 x y
    have heq : (fun x ↦ iteratedFDeriv ℝ 0 (f x) y) =
        (continuousMultilinearCurryFin0 ℝ X W).symm ∘ (fun x ↦ f x y) := rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero] at hm
    have hw : (1 + ‖x‖) ^ k * (1 + ‖y‖) ^ (n + 1) ≤
        (1 + ‖(x, y)‖) ^ (k + (n + 1)) := by
      rw [pow_add (1 + ‖(x, y)‖) k (n + 1)]
      apply mul_le_mul
      · gcongr
        exact norm_fst_le (x, y)
      · gcongr
        exact norm_snd_le (x, y)
      · positivity
      · positivity
    have hs := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (k + (n + 1), i)) (le_refl _) (le_refl _) S (x, y)
    have hfull : ((1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖) *
        (1 + ‖y‖) ^ (n + 1) ≤ C := by
      calc
        _ = ((1 + ‖x‖) ^ k * (1 + ‖y‖) ^ (n + 1)) *
            ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖ := by ring
        _ ≤ (1 + ‖(x, y)‖) ^ (k + (n + 1)) *
            ‖iteratedFDeriv ℝ i S (x, y)‖ :=
          mul_le_mul hw hm (norm_nonneg _) (by positivity)
        _ ≤ C := hs
    have hcancel : (1 + ‖y‖) ^ (n + 1) * decay y = 1 := by
      dsimp only [decay]
      rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity), add_neg_cancel,
        Real.rpow_zero]
    calc
      _ = (((1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖) *
          (1 + ‖y‖) ^ (n + 1)) * decay y := by rw [mul_assoc, hcancel, mul_one]
      _ ≤ C * decay y := mul_le_mul_of_nonneg_right hfull (by positivity)
  choose C hC hbound using hbound
  have hAll := contDiff_integral_of_compact_bounds f hfs (fun _K _hK i ↦
    ⟨fun y ↦ C 0 i * decay y, hdecay.const_mul _, fun x _ y ↦ by
      simpa only [pow_zero, one_mul] using hbound 0 i x y⟩)
  refine ⟨{ toFun := fun x ↦ ∫ y, f x y, smooth' := hAll.1, decay' := ?_ }, fun _ ↦ rfl⟩
  intro k i
  refine ⟨C k i * ∫ y, decay y, ?_⟩
  intro x
  have hI := (hAll.2 i x).1
  rw [(hAll.2 i x).2]
  calc
    _ ≤ ‖x‖ ^ k * ∫ y, ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖ := by
      gcongr
      exact norm_integral_le_integral_norm _
    _ = ∫ y, ‖x‖ ^ k * ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖ :=
      (integral_const_mul _ _).symm
    _ ≤ ∫ y, C k i * decay y := by
      apply integral_mono (hI.norm.const_mul _) (hdecay.const_mul _)
      intro y
      calc
        _ ≤ (1 + ‖x‖) ^ k * ‖iteratedFDeriv ℝ i (fun x ↦ f x y) x‖ := by
          change ‖x‖ ^ k * _ ≤ _
          gcongr
          linarith
        _ ≤ C k i * decay y := hbound k i x y
    _ = C k i * ∫ y, decay y := integral_const_mul _ _

end


/-! ## The compact smoothing composition symbol -/

section

/-- The composition integral of a compact symbol and a Schwartz Fourier amplitude is Schwartz. -/
private theorem exists_schwartz_compositionIntegral {n r s t : ℕ}
    (m : ℝ) (q : SymbolFunction n s t) (hq : IsSymbol Set.univ m q)
    (hcq : HasCompactSupport q)
    (S : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s))) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin t)),
      ∀ x ξ, T (x, ξ) = ∫ η,
        Complex.exp ((2 * Real.pi * inner ℝ x η : ℝ) * Complex.I) •
          (q x (ξ + (2 * Real.pi) • η)).comp (S (ξ, η)) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Hr := EuclideanSpace ℂ (Fin r)
  let Hs := EuclideanSpace ℂ (Fin s)
  let Ht := EuclideanSpace ℂ (Fin t)
  let D := X × (X × X)
  -- A single spatial plateau makes the external Fourier amplitude jointly Schwartz.
  obtain ⟨O, hOo, hKO, _, hOc⟩ :=
    exists_open_between_and_isCompact_closure hcq isOpen_univ (Set.subset_univ _)
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hOo
      (isClosed_tsupport q) hKO
  have hcχ : HasCompactSupport χ := by
    simpa only [HasCompactSupport, tsupport, hχsupp] using hOc
  let φ : 𝓢(X, ℂ) := (hcχ.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hχ)
  obtain ⟨A, hA⟩ := exists_schwartz_external_smul φ S
  -- Compact symbols are temperate multipliers even after the linear frequency shift.
  let R : D →L[ℝ] X × X :=
    (ContinuousLinearMap.fst ℝ X (X × X)).prod
      (((ContinuousLinearMap.fst ℝ X X).comp (ContinuousLinearMap.snd ℝ X (X × X))) +
        (2 * Real.pi) •
          ((ContinuousLinearMap.snd ℝ X X).comp (ContinuousLinearMap.snd ℝ X (X × X))))
  have hqT : (fun z : D ↦ q z.1 (z.2.1 + (2 * Real.pi) • z.2.2)).HasTemperateGrowth :=
    (hasTemperateGrowth_uncurry_of_isSymbol m q hq hcq).comp R.hasTemperateGrowth
  let B : 𝓢(D, Hr →L[ℂ] Ht) :=
    SchwartzMap.bilinLeftCLM (ContinuousLinearMap.compL ℂ Hr Hs Ht).flip hqT A
  have hinner : (fun z : D ↦ inner ℝ z.1 z.2.2).HasTemperateGrowth :=
    (innerSL ℝ).bilinear_hasTemperateGrowth
      (ContinuousLinearMap.fst ℝ X (X × X)).hasTemperateGrowth
      (((ContinuousLinearMap.snd ℝ X X).comp
        (ContinuousLinearMap.snd ℝ X (X × X))).hasTemperateGrowth)
  have hphase : (fun z : D ↦ Complex.exp
      ((2 * Real.pi * inner ℝ z.1 z.2.2 : ℝ) * Complex.I)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const (2 * Real.pi)).mul hinner)
  let F : 𝓢(D, Hr →L[ℂ] Ht) := SchwartzMap.smulLeftCLM (Hr →L[ℂ] Ht)
    (fun z : D ↦ Complex.exp
      ((2 * Real.pi * inner ℝ z.1 z.2.2 : ℝ) * Complex.I)) B
  have hF (z : D) : F z =
      Complex.exp ((2 * Real.pi * inner ℝ z.1 z.2.2 : ℝ) * Complex.I) •
        (q z.1 (z.2.1 + (2 * Real.pi) • z.2.2)).comp (S z.2) := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hphase]
    rw [SchwartzMap.bilinLeftCLM_apply]
    change _ • (q z.1 (z.2.1 + (2 * Real.pi) • z.2.2)).comp (A z) = _
    rw [hA]
    change _ • (q z.1 (z.2.1 + (2 * Real.pi) • z.2.2)).comp
      ((χ z.1 : ℂ) • S z.2) = _
    by_cases hz : z.1 ∈ tsupport q
    · rw [(hχone z.1).mp hz, Complex.ofReal_one, one_smul]
    · have hzero : q z.1 = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hzero]
  -- Reassociate variables before integrating, so the marginal theorem preserves x and ξ.
  let e : ((X × X) × X) ≃L[ℝ] D :=
    (LinearIsometryEquiv.prodAssoc ℝ X X X).toContinuousLinearEquiv
  let F' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e F
  obtain ⟨T, hT⟩ := exists_schwartz_integral_snd F'
  refine ⟨T, ?_⟩
  intro x ξ
  rw [hT]
  apply integral_congr_ae
  filter_upwards with η
  exact hF (x, ξ, η)

/-- The noncompact-input smoothing composition integral has compact output support. -/
private theorem exists_smoothing_compositionIntegral {n r s t : ℕ}
    (m : ℝ) (q : SymbolFunction n s t) (hq : IsSymbol Set.univ m q)
    (hcq : HasCompactSupport q) (c : SymbolFunction n r s)
    (hc : IsSmoothingSymbol Set.univ c) (hcc : HasCompactSupport c) :
    ∃ d : SymbolFunction n r t,
      IsSmoothingSymbol Set.univ d ∧ HasCompactSupport d ∧ tsupport d ⊆ tsupport q ∧
        ∀ x ξ, d x ξ = ∫ η,
          Complex.exp ((2 * Real.pi * inner ℝ x η : ℝ) * Complex.I) •
            (q x (ξ + (2 * Real.pi) • η)).comp (𝓕 (fun y ↦ c y ξ) η) := by
  let X := EuclideanSpace ℝ (Fin n)
  obtain ⟨S, hS⟩ := exists_schwartz_of_isSmoothingSymbol c hc hcc
  have hsupport : tsupport S ⊆ Prod.fst ⁻¹' tsupport c := by
    apply closure_minimal ?_ ((isClosed_tsupport c).preimage continuous_fst)
    intro z hz
    by_contra hout
    have hzero : c z.1 = 0 := image_eq_zero_of_notMem_tsupport hout
    exact hz (by rw [hS, hzero]; rfl)
  let F := partialFourierSchwartz S (tsupport c) hcc hsupport
  have hF (ξ η : X) : F (ξ, η) = 𝓕 (fun y ↦ c y ξ) η := by
    change 𝓕 (fun y ↦ S (y, ξ)) η = _
    have heq : (fun y ↦ S (y, ξ)) = (fun y ↦ c y ξ) := funext (fun y ↦ hS y ξ)
    rw [heq]
  obtain ⟨T, hT⟩ := exists_schwartz_compositionIntegral m q hq hcq F
  let d : SymbolFunction n r t := fun x ξ ↦ T (x, ξ)
  have hd (x ξ : X) : d x ξ = ∫ η,
      Complex.exp ((2 * Real.pi * inner ℝ x η : ℝ) * Complex.I) •
        (q x (ξ + (2 * Real.pi) • η)).comp (𝓕 (fun y ↦ c y ξ) η) := by
    change T (x, ξ) = _
    rw [hT]
    simp_rw [hF]
    rfl
  have hds : tsupport d ⊆ tsupport q := by
    apply closure_minimal ?_ (isClosed_tsupport q)
    intro x hx
    by_contra hout
    have hzero : q x = 0 := image_eq_zero_of_notMem_tsupport hout
    apply hx
    funext ξ
    rw [hd]
    simp [hzero]
  exact ⟨d, isSmoothingSymbol_of_schwartz T,
    hcq.of_isClosed_subset (isClosed_tsupport d) hds, hds, hd⟩

end


/-! ## Exact action of the smoothing composition -/

section

/-- The full Fourier kernel of a compact smoothing quantization, with both integrals justified. -/
private theorem fourier_quantizeSchwartz_of_isSmoothingSymbol {n r s : ℕ}
    (c : SymbolFunction n r s) (hc : IsSmoothingSymbol Set.univ c)
    (hcc : HasCompactSupport c)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (ζ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (quantizeSchwartz 0 c (hc 0) hcc u) ζ =
      ∫ η, (𝓕 (fun y ↦ c y ((2 * Real.pi) • η)) (ζ - η)) ((𝓕 u) η) := by
  let X := EuclideanSpace ℝ (Fin n)
  let Hr := EuclideanSpace ℂ (Fin r)
  let Hs := EuclideanSpace ℂ (Fin s)
  let a : ℝ := 2 * Real.pi
  have ha : a ≠ 0 := by dsimp [a]; positivity
  obtain ⟨S, hS⟩ := exists_schwartz_of_isSmoothingSymbol c hc hcc
  let e : (X × X) ≃L[ℝ] X × X :=
    (ContinuousLinearEquiv.refl ℝ X).prodCongr
      ((LinearEquiv.smulOfNeZero ℝ X a ha).toContinuousLinearEquiv)
  let S' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e S
  have hU : (fun z : X × X ↦ (𝓕 u) z.2).HasTemperateGrowth :=
    (𝓕 u).hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ X X).hasTemperateGrowth
  let V := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ Hs).flip hU S'
  have hinner : (fun z : X × X ↦ inner ℝ z.1 z.2).HasTemperateGrowth :=
    (innerSL ℝ).bilinear_hasTemperateGrowth
      (ContinuousLinearMap.fst ℝ X X).hasTemperateGrowth
      (ContinuousLinearMap.snd ℝ X X).hasTemperateGrowth
  have hfixed : (fun z : X × X ↦ inner ℝ z.1 ζ).HasTemperateGrowth :=
    ((innerSL ℝ).flip ζ).hasTemperateGrowth.comp
      (ContinuousLinearMap.fst ℝ X X).hasTemperateGrowth
  let phase : X × X → ℂ := fun z ↦ Complex.exp
    ((a * (inner ℝ z.1 z.2 - inner ℝ z.1 ζ) : ℝ) * Complex.I)
  have hphase : phase.HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const a).mul (hinner.sub hfixed))
  let G : 𝓢(X × X, Hs) := SchwartzMap.smulLeftCLM Hs phase V
  have hG (y η : X) : G (y, η) = phase (y, η) • c y (a • η) ((𝓕 u) η) := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hphase, SchwartzMap.bilinLeftCLM_apply]
    change phase (y, η) • S (y, a • η) ((𝓕 u) η) = _
    rw [hS]
  -- The Schwartz product is absolutely integrable, so Fourier integration may be exchanged.
  rw [SchwartzMap.fourier_coe, Real.fourier_eq']
  calc
    _ = ∫ y, ∫ η, G (y, η) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [quantizeSchwartz_apply, quantize_rescaled, ← integral_smul]
      apply integral_congr_ae
      filter_upwards with η
      rw [hG, smul_smul, ← Complex.exp_add]
      congr 2
      dsimp only [phase, a]
      push_cast
      ring
    _ = ∫ η, ∫ y, G (y, η) := integral_integral_swap G.integrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with η
      let H : X → Hr →L[ℂ] Hs := fun y ↦
        Complex.exp ((-2 * Real.pi * inner ℝ y (ζ - η) : ℝ) * Complex.I) • c y (a • η)
      have hsmooth : ContDiff ℝ ∞ (Function.uncurry c) := by
        simpa only [Set.univ_prod_univ, contDiffOn_univ] using (hc 0).1
      have hHc : Continuous H := by
        have hcs : Continuous (fun y : X ↦ c y (a • η)) :=
          hsmooth.continuous.comp (continuous_id.prodMk continuous_const)
        dsimp only [H]
        fun_prop
      have hHs : HasCompactSupport H := by
        apply hcc.of_isClosed_subset (isClosed_tsupport H)
        apply closure_minimal ?_ (isClosed_tsupport c)
        intro y hy
        by_contra hout
        have hz : c y = 0 := image_eq_zero_of_notMem_tsupport hout
        exact hy (by simp [H, hz])
      have hHi : Integrable H := hHc.integrable_of_hasCompactSupport hHs
      rw [Real.fourier_eq']
      change (∫ y, G (y, η)) = (∫ y, H y) ((𝓕 u) η)
      rw [ContinuousLinearMap.integral_apply hHi]
      apply integral_congr_ae
      filter_upwards with y
      rw [hG]
      change phase (y, η) • _ = _
      dsimp only [H, phase, a]
      rw [smul_apply]
      congr 2
      congr 1
      rw [inner_sub_right]
      push_cast
      ring

/-- Fixing one coordinate is a Schwartz restriction to an affine subspace. -/
private def schwartzSlice {E F Z : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (S : 𝓢(E × F, Z)) (x : E) : 𝓢(F, Z) := by
  have hg : (fun y : F ↦ (x, y)).HasTemperateGrowth := by
    convert (ContinuousLinearMap.inr ℝ E F).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const (x, (0 : F))) using 1
    funext y
    simp
  exact SchwartzMap.compCLM ℝ hg ⟨1, 1, fun y ↦ by
    simpa only [one_mul, pow_one] using
      (norm_snd_le (x, y)).trans (by linarith : ‖(x, y)‖ ≤ 1 + ‖(x, y)‖)⟩ S

/-- A smoothing right factor stays smoothing under compact-output quantization. -/
theorem exists_smoothingSymbol_quantize_comp_right {n r s t : ℕ}
    (m : ℝ) (q : SymbolFunction n s t) (hq : IsSymbol Set.univ m q)
    (hcq : HasCompactSupport q) (c : SymbolFunction n r s)
    (hc : IsSmoothingSymbol Set.univ c) (hcc : HasCompactSupport c) :
    ∃ d : SymbolFunction n r t,
      IsSmoothingSymbol Set.univ d ∧ HasCompactSupport d ∧ tsupport d ⊆ tsupport q ∧
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)), ∀ x,
          quantize d u x = quantize q (quantizeSchwartz 0 c (hc 0) hcc u) x := by
  let X := EuclideanSpace ℝ (Fin n)
  let Hr := EuclideanSpace ℂ (Fin r)
  let Hs := EuclideanSpace ℂ (Fin s)
  let Ht := EuclideanSpace ℂ (Fin t)
  let a : ℝ := 2 * Real.pi
  have ha : a ≠ 0 := by dsimp [a]; positivity
  obtain ⟨d, hd, hcd, hds, hdval⟩ := exists_smoothing_compositionIntegral m q hq hcq c hc hcc
  obtain ⟨S, hS⟩ := exists_schwartz_of_isSmoothingSymbol c hc hcc
  have hsupport : tsupport S ⊆ Prod.fst ⁻¹' tsupport c := by
    apply closure_minimal ?_ ((isClosed_tsupport c).preimage continuous_fst)
    intro z hz
    by_contra hout
    have hzero : c z.1 = 0 := image_eq_zero_of_notMem_tsupport hout
    exact hz (by rw [hS, hzero]; rfl)
  let F := partialFourierSchwartz S (tsupport c) hcc hsupport
  have hF (ξ η : X) : F (ξ, η) = 𝓕 (fun y ↦ c y ξ) η := by
    change 𝓕 (fun y ↦ S (y, ξ)) η = _
    rw [show (fun y ↦ S (y, ξ)) = (fun y ↦ c y ξ) from funext (fun y ↦ hS y ξ)]
  -- An invertible linear frequency change preserves joint Schwartz decay.
  let e₀ : (X × X) ≃ₗ[ℝ] X × X := {
    toFun := fun z ↦ (a • z.2, z.1 - z.2)
    invFun := fun z ↦ (a⁻¹ • z.1 + z.2, a⁻¹ • z.1)
    left_inv := by
      intro z
      apply Prod.ext
      · simp only [inv_smul_smul₀ ha]
        abel
      · exact inv_smul_smul₀ ha z.2
    right_inv := by
      intro z
      apply Prod.ext
      · exact smul_inv_smul₀ ha z.1
      · simp
    map_add' := by
      intro z w
      apply Prod.ext
      · exact smul_add _ _ _
      · exact (sub_add_sub_comm z.1 z.2 w.1 w.2).symm
    map_smul' := by
      intro b z
      apply Prod.ext
      · exact smul_comm a b z.2
      · exact (smul_sub b z.1 z.2).symm }
  let e := e₀.toContinuousLinearEquiv
  let F' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e F
  refine ⟨d, hd, hcd, hds, ?_⟩
  intro u x
  have hqT : (fun z : X × X ↦ q x (a • z.1)).HasTemperateGrowth := by
    let R := (ContinuousLinearMap.inr ℝ X X).comp
      (a • ContinuousLinearMap.fst ℝ X X)
    have hR : (fun z : X × X ↦ (x, a • z.1)).HasTemperateGrowth := by
      convert R.hasTemperateGrowth.add (Function.HasTemperateGrowth.const (x, (0 : X))) using 1
      funext z
      simp [R]
    exact (hasTemperateGrowth_uncurry_of_isSymbol m q hq hcq).comp hR
  let A := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.compL ℂ Hr Hs Ht).flip hqT F'
  let phase : X → ℂ := fun ζ ↦ Complex.exp ((a * inner ℝ x ζ : ℝ) * Complex.I)
  have hphase : phase.HasTemperateGrowth :=
    Complex.hasTemperateGrowth_exp_mul_I.comp
      ((Function.HasTemperateGrowth.const a).mul (innerSL ℝ x).hasTemperateGrowth)
  let M := SchwartzMap.smulLeftCLM (Hr →L[ℂ] Ht)
    (fun z : X × X ↦ phase z.1) A
  have hMt : (fun z : X × X ↦ phase z.1).HasTemperateGrowth :=
    hphase.comp (ContinuousLinearMap.fst ℝ X X).hasTemperateGrowth
  have hM (ζ η : X) : M (ζ, η) = phase ζ •
      (q x (a • ζ)).comp (F (a • η, ζ - η)) := by
    rw [SchwartzMap.smulLeftCLM_apply_apply hMt, SchwartzMap.bilinLeftCLM_apply]
    rfl
  have hU : (fun z : X × X ↦ (𝓕 u) z.2).HasTemperateGrowth :=
    (𝓕 u).hasTemperateGrowth.comp (ContinuousLinearMap.snd ℝ X X).hasTemperateGrowth
  let J := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ Ht).flip hU M
  have hJ (ζ η : X) : J (ζ, η) = M (ζ, η) ((𝓕 u) η) := by
    rw [SchwartzMap.bilinLeftCLM_apply]
    rfl
  let B := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.apply ℂ Hs).flip hU F'
  have hBi (ζ : X) : Integrable (fun η ↦ F (a • η, ζ - η) ((𝓕 u) η)) :=
    (schwartzSlice B ζ).integrable
  have hMi (η : X) : Integrable (fun ζ ↦ M (ζ, η)) :=
    (schwartzSlice (SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
      (ContinuousLinearEquiv.prodComm ℝ X X) M) η).integrable
  have hphase_std (ζ : X) : phase ζ =
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ζ : ℂ)) := by
    dsimp only [phase, a]
    congr 1
    push_cast
    ring
  -- Translation in the inner frequency identifies the exact symbol integral, without a remainder.
  have hMint (η : X) : ∫ ζ, M (ζ, η) = phase η • d x (a • η) := by
    rw [← integral_add_left_eq_self (fun ζ ↦ M (ζ, η)) η]
    rw [hdval, ← integral_smul]
    apply integral_congr_ae
    filter_upwards with ν
    rw [hM, add_sub_cancel_left, hF]
    change phase (η + ν) • (q x (a • (η + ν))).comp _ = _
    have hphase_add : phase (η + ν) = phase η * phase ν := by
      dsimp only [phase]
      rw [← Complex.exp_add, inner_add_right]
      congr 1
      push_cast
      ring
    rw [hphase_add, mul_smul, smul_add]
  -- Both exchanges are justified by the same joint Schwartz kernel J.
  symm
  rw [quantize_rescaled]
  calc
    _ = ∫ ζ, ∫ η, J (ζ, η) := by
      apply integral_congr_ae
      filter_upwards with ζ
      rw [fourier_quantizeSchwartz_of_isSmoothingSymbol c hc hcc u ζ]
      simp_rw [← hF]
      rw [← (q x (a • ζ)).integral_comp_comm (hBi ζ), ← integral_smul]
      apply integral_congr_ae
      filter_upwards with η
      rw [hJ, hM, hphase_std]
      rfl
    _ = ∫ η, ∫ ζ, J (ζ, η) := integral_integral_swap J.integrable
    _ = ∫ η, phase η • d x (a • η) ((𝓕 u) η) := by
      apply integral_congr_ae
      filter_upwards with η
      simp_rw [hJ]
      rw [← ContinuousLinearMap.integral_apply (hMi η), hMint]
      rfl
    _ = quantize d u x := by
      rw [quantize_rescaled]
      apply integral_congr_ae
      filter_upwards with η
      rw [hphase_std]

end


/-! ## Exact compact Schwartz operators and the local smoothing ideal

These predicates record symbols of the existing continuous maps, without introducing new operator
objects. The algebraic laws retain those maps; all-order membership uses full-symbol uniqueness.
Properization and separated tails justify both ideal compositions without an input-support axiom.
The same interfaces serve the two-sided construction and its localized-left consumer.
-/

/-- The existing continuous Schwartz-map space, named to keep the same operator witnesses. -/
abbrev LocalSchwartzOperator (n r s : ℕ) : Type :=
  𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
    𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin s))

/-- The specified operator has an exact compact spatial symbol of the given order. -/
def HasCompactSchwartzSymbol {n r s : ℕ} (m : ℝ) (P : LocalSchwartzOperator n r s) : Prop :=
  ∃ p : SymbolFunction n r s, ∃ (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p),
    P = quantizeSchwartz m p hp hc

/-- The specified operator has one compact full symbol lying in every real order. -/
def HasCompactSmoothingSchwartzSymbol {n r s : ℕ} (P : LocalSchwartzOperator n r s) : Prop :=
  ∃ p : SymbolFunction n r s,
    ∃ (hp : IsSmoothingSymbol Set.univ p) (hc : HasCompactSupport p),
      P = quantizeSchwartz 0 p (hp 0) hc

/-- Every compact output localization inside the domain has an exact smoothing symbol. -/
def IsLocallySmoothingSchwartz {n r s : ℕ}
    (U : Set (EuclideanSpace ℝ (Fin n))) (P : LocalSchwartzOperator n r s) : Prop :=
  ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ U →
      HasCompactSmoothingSchwartzSymbol
        ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp P)

/-- A compact set has a smooth compact plateau inside any open neighborhood. -/
theorem exists_compact_cutoff_one_near {n : ℕ}
    (K U : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
        K ⊆ interior {x | χ x = 1} := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨W, hWo, hVW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hVc hU hVU
  obtain ⟨χ, hχ, _, hχsupp, hχone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hWo isClosed_closure hVW
  refine ⟨χ, hχ, ?_, ?_, ?_⟩
  · simpa only [HasCompactSupport, tsupport, hχsupp] using hWc
  · simpa only [tsupport, hχsupp] using hWU
  · apply hKV.trans
    exact interior_maximal (fun x hx ↦ (hχone x).mp (subset_closure hx)) hVo

namespace HasCompactSchwartzSymbol

variable {n r s t : ℕ} {l m : ℝ}
  {P : LocalSchwartzOperator n r s} {Q : LocalSchwartzOperator n r s}

theorem mono (hP : HasCompactSchwartzSymbol l P) (hlm : l ≤ m) :
    HasCompactSchwartzSymbol m P := by
  obtain ⟨p, hp, hc, rfl⟩ := hP
  refine ⟨p, hp.mono hlm, hc, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  simp only [quantizeSchwartz_apply]

theorem add (hP : HasCompactSchwartzSymbol m P) (hQ : HasCompactSchwartzSymbol m Q) :
    HasCompactSchwartzSymbol m (P + Q) := by
  obtain ⟨p, hp, hcp, rfl⟩ := hP
  obtain ⟨q, hq, hcq, rfl⟩ := hQ
  refine ⟨p + q, hp.add isOpen_univ hq, hcp.add hcq, ?_⟩
  exact (quantizeSchwartz_add m p q hp hq hcp hcq _ _).symm

theorem smul (hP : HasCompactSchwartzSymbol m P) (a : ℂ) :
    HasCompactSchwartzSymbol m (a • P) := by
  obtain ⟨p, hp, hc, rfl⟩ := hP
  refine ⟨a • p, hp.smul isOpen_univ a, hc.smul_left, ?_⟩
  exact (quantizeSchwartz_smul m a p hp hc _ _).symm

theorem sub (hP : HasCompactSchwartzSymbol m P) (hQ : HasCompactSchwartzSymbol m Q) :
    HasCompactSchwartzSymbol m (P - Q) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using hP.add (hQ.smul (-1))

/-- Exact order addition uses proper support only on the right. -/
theorem comp {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    (hP : HasCompactSchwartzSymbol l P) (hQ : HasCompactSchwartzSymbol m Q)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hQK : HasOperatorSupport K Q) : HasCompactSchwartzSymbol (l + m) (P.comp Q) := by
  obtain ⟨p, hp, hcp, rfl⟩ := hP
  obtain ⟨q, hq, hcq, rfl⟩ := hQ
  obtain ⟨χ, hχ, hcχ, _, hχone⟩ :=
    exists_compact_cutoff_one_near K Set.univ hK isOpen_univ (Set.subset_univ _)
  have hsym := isSymbol_compositionSymbol l m p q hp hq hcp hcq χ hχ hcχ
  have hcompact : HasCompactSupport (compositionSymbol χ p q) :=
    hcp.of_isClosed_subset (isClosed_tsupport _) (tsupport_compositionSymbol_subset χ p q)
  refine ⟨compositionSymbol χ p q, hsym, hcompact, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [quantizeSchwartz_apply]
  exact (quantize_compositionSymbol_of_compactSupport_left l m p q hp hq hcp
    (quantizeSchwartz l p hp hcp) (quantizeSchwartz m q hq hcq)
    (quantizeSchwartz_apply l p hp hcp) (quantizeSchwartz_apply m q hq hcq)
    K hK hQK χ hχ hcχ hχone u x).symm

/-- Compact output cutoffs retain the full symbol order. -/
theorem cutoff (hP : HasCompactSchwartzSymbol m P)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    HasCompactSchwartzSymbol m
      ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp P) := by
  obtain ⟨p, hp, hcp, rfl⟩ := hP
  let a := zeroExtendedSymbol Set.univ χ p
  have ha := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ m χ hχ hcχ
    (Set.subset_univ _) p hp
  have hca := hasCompactSupport_zeroExtendedSymbol Set.univ χ p hcχ
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  refine ⟨a, ha, hca, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply hχT,
    quantizeSchwartz_apply, quantizeSchwartz_apply]
  dsimp only [a, quantize]
  simp only [zeroExtendedSymbol_apply_of_mem Set.univ χ p x _ (Set.mem_univ x), smul_apply]
  simp_rw [smul_comm (Complex.exp _) (χ x : ℂ)]
  rw [integral_smul]
  exact smul_comm _ _ _

/-- An improved order for the exact symbol difference improves the actual operator difference. -/
theorem sub_quantize (m l : ℝ) (p q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ m p) (hq : IsSymbol Set.univ m q)
    (hcp : HasCompactSupport p) (hcq : HasCompactSupport q)
    (hd : IsSymbol Set.univ l (p - q)) :
    HasCompactSchwartzSymbol l (quantizeSchwartz m p hp hcp - quantizeSchwartz m q hq hcq) := by
  have hn := hq.smul isOpen_univ (-1)
  have hcn : HasCompactSupport ((-1 : ℂ) • q) := hcq.smul_left
  have hs := hp.add isOpen_univ hn
  have hcs : HasCompactSupport (p + (-1 : ℂ) • q) := hcp.add hcn
  have heq : p + (-1 : ℂ) • q = p - q := by rw [neg_one_smul, sub_eq_add_neg]
  refine ⟨p - q, hd, hcp.sub hcq, ?_⟩
  calc
    _ = quantizeSchwartz m (p + (-1 : ℂ) • q) hs hcs := by
      rw [quantizeSchwartz_add m p _ hp hn hcp hcn hs hcs,
        quantizeSchwartz_smul m (-1) q hq hcq hn hcn, neg_one_smul, sub_eq_add_neg]
    _ = _ := by
      apply ContinuousLinearMap.ext
      intro u
      apply SchwartzMap.ext
      intro x
      rw [quantizeSchwartz_apply, quantizeSchwartz_apply, heq]

end HasCompactSchwartzSymbol

/-- Uniqueness of the full symbol makes separate every-order realizations one smoothing symbol. -/
theorem hasCompactSmoothingSchwartzSymbol_iff {n r s : ℕ}
    (P : LocalSchwartzOperator n r s) :
    HasCompactSmoothingSchwartzSymbol P ↔ ∀ m, HasCompactSchwartzSymbol m P := by
  constructor
  · rintro ⟨p, hp, hc, rfl⟩ m
    refine ⟨p, hp m, hc, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    simp only [quantizeSchwartz_apply]
  · intro hP
    obtain ⟨p, hp, hc, hP0⟩ := hP 0
    have hs : IsSmoothingSymbol Set.univ p := by
      intro m
      obtain ⟨q, hq, hcq, hQ⟩ := hP m
      have heq : p = q := symbol_eq_of_quantize_eq 0 m p q hp hq (fun u x ↦ by
        rw [← quantizeSchwartz_apply 0 p hp hc, ← quantizeSchwartz_apply m q hq hcq,
          ← hP0, ← hQ])
      rwa [heq]
    exact ⟨p, hs, hc, hP0⟩

namespace HasCompactSmoothingSchwartzSymbol

variable {n r s t : ℕ}

theorem order {P : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) (m : ℝ) : HasCompactSchwartzSymbol m P :=
  (hasCompactSmoothingSchwartzSymbol_iff P).mp hP m

theorem add {P Q : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) (hQ : HasCompactSmoothingSchwartzSymbol Q) :
    HasCompactSmoothingSchwartzSymbol (P + Q) := by
  apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
  intro m
  exact (hP.order m).add (hQ.order m)

theorem sub {P Q : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) (hQ : HasCompactSmoothingSchwartzSymbol Q) :
    HasCompactSmoothingSchwartzSymbol (P - Q) := by
  apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
  intro m
  exact (hP.order m).sub (hQ.order m)

theorem cutoff {P : LocalSchwartzOperator n r s} (hP : HasCompactSmoothingSchwartzSymbol P)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    HasCompactSmoothingSchwartzSymbol
      ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp P) := by
  apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
  intro m
  exact (hP.order m).cutoff χ hχ hcχ

/-- A smoothing left factor can be composed with a properly supported right factor. -/
theorem comp {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) {m : ℝ}
    (hQ : HasCompactSchwartzSymbol m Q)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hQK : HasOperatorSupport K Q) :
    HasCompactSmoothingSchwartzSymbol (P.comp Q) := by
  apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
  intro l
  convert (hP.order (l - m)).comp hQ K hK hQK using 1
  ring

/-- A smoothing right factor needs no input-support assumption. -/
theorem comp_left {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    {m : ℝ} (hP : HasCompactSchwartzSymbol m P)
    (hQ : HasCompactSmoothingSchwartzSymbol Q) :
    HasCompactSmoothingSchwartzSymbol (P.comp Q) := by
  obtain ⟨p, hp, hcp, rfl⟩ := hP
  obtain ⟨q, hq, hcq, rfl⟩ := hQ
  obtain ⟨d, hd, hcd, _, hact⟩ := exists_smoothingSymbol_quantize_comp_right m p hp hcp q hq hcq
  refine ⟨d, hd, hcd, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, quantizeSchwartz_apply, quantizeSchwartz_apply]
  exact (hact u x).symm

end HasCompactSmoothingSchwartzSymbol

/-- A separated input cutoff gives the actual compact smoothing operator. -/
theorem hasCompactSmoothingSchwartzSymbol_offDiagonal {n r s : ℕ} {m : ℝ}
    {P : LocalSchwartzOperator n r s} (hP : HasCompactSchwartzSymbol m P)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hone : tsupport χ ⊆ interior {x | ρ x = 1}) :
    HasCompactSmoothingSchwartzSymbol
      (((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp P).comp
        (ContinuousLinearMap.id ℂ _ -
          SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (ρ x : ℂ)))) := by
  obtain ⟨p, hp, hcp, rfl⟩ := hP
  have hd := isSmoothingSymbol_offDiagonalSymbol m p hp χ ρ hχ hcχ hρ hcρ hone
  have hcd := hasCompactSupport_offDiagonalSymbol χ ρ p hcχ
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hρT : (fun x ↦ (ρ x : ℂ)).HasTemperateGrowth :=
    (hcρ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hρ)
  have hcT : (fun x ↦ 1 - (ρ x : ℂ)).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 : ℂ)).sub hρT
  refine ⟨offDiagonalSymbol χ ρ p, hd, hcd, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply hχT, quantizeSchwartz_apply,
    quantizeSchwartz_apply, quantize_offDiagonalSymbol m p hp χ ρ hχ hcχ hρ hcρ]
  rw [Complex.coe_smul]
  congr 1
  apply congrArg (fun v ↦ quantize p v x)
  apply SchwartzMap.ext
  intro y
  rw [SchwartzMap.smulLeftCLM_apply_apply hcT]
  simp only [sub_apply, ContinuousLinearMap.id_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply hρT, sub_smul, one_smul]

/-- Input localization keeps the same compact symbol modulo smoothing inside the prescribed set. -/
theorem exists_proper_quantization_mod_smoothing {n r s : ℕ}
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol Set.univ m p)
    (hcp : HasCompactSupport p) (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (hpU : tsupport p ⊆ U) :
    ∃ q : SymbolFunction n r s, ∃ (hq : IsSymbol Set.univ m q) (hcq : HasCompactSupport q),
      tsupport q ⊆ U ∧
        ∃ K : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact K ∧ K ⊆ U ∧ HasOperatorSupport K (quantizeSchwartz m q hq hcq) ∧
            HasCompactSmoothingSchwartzSymbol
              (quantizeSchwartz m p hp hcp - quantizeSchwartz m q hq hcq) ∧
              IsSmoothingSymbol Set.univ (p - q) := by
  obtain ⟨χ, hχ, hcχ, hχU, hχone⟩ := exists_compact_cutoff_one_near (tsupport p) U hcp hU hpU
  obtain ⟨ρ, hρ, hcρ, hρU, hρone⟩ := exists_compact_cutoff_one_near (tsupport χ) U hcχ hU hχU
  let q := cutoffSymbol χ ρ p
  have hq : IsSymbol Set.univ m q := isSymbol_cutoffSymbol m p hp χ ρ hχ hρ hcχ hcρ
  have hsupp : tsupport q ⊆ tsupport χ := by
    apply closure_minimal ?_ (isClosed_tsupport χ)
    intro x hx
    by_contra hout
    have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport hout
    apply hx
    funext ξ
    simp [q, cutoffSymbol, amplitudeSymbol, cutoffAmplitude, hzero]
  have hcq : HasCompactSupport q := hcχ.of_isClosed_subset (isClosed_tsupport q) hsupp
  let K := tsupport χ ∪ tsupport ρ
  have hK : IsCompact K := hcχ.union hcρ
  have hKU : K ⊆ U := Set.union_subset hχU hρU
  have hreal : quantizeSchwartz m q hq hcq = amplitudeOperator m (cutoffAmplitude χ ρ p)
      (isAmplitude_cutoffAmplitude m p hp χ ρ hχ hρ)
      (hasCompactSupport_cutoffAmplitude p χ ρ hcχ hcρ) := by
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply, amplitudeOperator_apply]
    exact congrFun (quantize_amplitudeSymbol m (cutoffAmplitude χ ρ p)
      (isAmplitude_cutoffAmplitude m p hp χ ρ hχ hρ)
      (hasCompactSupport_cutoffAmplitude p χ ρ hcχ hcρ) u) x
  refine ⟨q, hq, hcq, hsupp.trans hχU, K, hK, hKU, ?_, ?_⟩
  · rw [hreal]
    exact hasOperatorSupport_cutoff m p hp χ ρ hχ hρ hcχ hcρ
  · have hfix : (fun x ξ ↦ χ x • p x ξ) = p := by
      funext x ξ
      by_cases hx : x ∈ tsupport p
      · have hχx : χ x = 1 := show x ∈ {y | χ y = 1} from interior_subset (hχone hx)
        rw [hχx, one_smul]
      · have hz : p x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hz]
    have hd : IsSmoothingSymbol Set.univ (p - q) := by
      have h := isSmoothingSymbol_offDiagonalSymbol m p hp χ ρ hχ hcχ hρ hcρ hρone
      simpa only [offDiagonalSymbol, hfix] using h
    refine ⟨?_, hd⟩
    apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
    intro l
    exact HasCompactSchwartzSymbol.sub_quantize m l p q hp hq hcp hcq (hd l)

/-- A compact smoothing left factor also tolerates a right factor with noncompact input support. -/
theorem HasCompactSmoothingSchwartzSymbol.comp_any {n r s t : ℕ}
    {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) {m : ℝ}
    (hQ : HasCompactSchwartzSymbol m Q) : HasCompactSmoothingSchwartzSymbol (P.comp Q) := by
  obtain ⟨q, hq, hcq, rfl⟩ := hQ
  obtain ⟨b, hb, hcb, _, K, hK, _, hbK, hdiff⟩ :=
    exists_proper_quantization_mod_smoothing m q hq hcq Set.univ isOpen_univ (Set.subset_univ _)
  have hmain := hP.comp (show HasCompactSchwartzSymbol m (quantizeSchwartz m b hb hcb) from
    ⟨b, hb, hcb, rfl⟩) K hK hbK
  have htail := hdiff.1.comp_left (hP.order 0)
  convert hmain.add htail using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub]
  abel

namespace IsLocallySmoothingSchwartz

variable {n r s t : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}

theorem of_smoothing {P : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) : IsLocallySmoothingSchwartz U P := by
  intro χ hχ hcχ _
  exact hP.cutoff χ hχ hcχ

theorem add {P Q : LocalSchwartzOperator n r s}
    (hP : IsLocallySmoothingSchwartz U P) (hQ : IsLocallySmoothingSchwartz U Q) :
    IsLocallySmoothingSchwartz U (P + Q) := by
  intro χ hχ hcχ hχU
  convert (hP χ hχ hcχ hχU).add (hQ χ hχ hcχ hχU) using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, add_apply, map_add]

theorem sub {P Q : LocalSchwartzOperator n r s}
    (hP : IsLocallySmoothingSchwartz U P) (hQ : IsLocallySmoothingSchwartz U Q) :
    IsLocallySmoothingSchwartz U (P - Q) := by
  intro χ hχ hcχ hχU
  convert (hP χ hχ hcχ hχU).sub (hQ χ hχ hcχ hχU) using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, sub_apply, map_sub]

/-- Local smoothing is preserved by a compact-symbol right factor. -/
theorem comp {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    (hP : IsLocallySmoothingSchwartz U P) {m : ℝ}
    (hQ : HasCompactSchwartzSymbol m Q) : IsLocallySmoothingSchwartz U (P.comp Q) := by
  intro χ hχ hcχ hχU
  exact (hP χ hχ hcχ hχU).comp_any hQ

/-- For left multiplication, localize the intermediate value and retain the separated tail. -/
theorem comp_left {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s}
    {l m : ℝ} (hP : HasCompactSchwartzSymbol l P) (hQ : HasCompactSchwartzSymbol m Q)
    (hU : IsOpen U) (hlocal : IsLocallySmoothingSchwartz U Q) :
    IsLocallySmoothingSchwartz U (P.comp Q) := by
  intro χ hχ hcχ hχU
  obtain ⟨ρ, hρ, hcρ, hρU, hρone⟩ :=
    exists_compact_cutoff_one_near (tsupport χ) U hcχ hU hχU
  have hmain := (hlocal ρ hρ hcρ hρU).comp_left (hP.cutoff χ hχ hcχ)
  have htail := (hasCompactSmoothingSchwartzSymbol_offDiagonal hP χ ρ
    hχ hcχ hρ hcρ hρone).comp_any hQ
  convert hmain.add htail using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

end IsLocallySmoothingSchwartz

/-- A common compact operator support gives a compact symbol asymptotic sum. -/
theorem exists_compact_schwartzOperator_expansion {n r s : ℕ}
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℝ)
    (P : ℕ → LocalSchwartzOperator n r s)
    (hP : ∀ j : ℕ, HasCompactSchwartzSymbol (m - j) (P j))
    (hPK : ∀ j, HasOperatorSupport K (P j)) :
    ∃ a : SymbolFunction n r s, ∃ (ha : IsSymbol Set.univ m a) (hca : HasCompactSupport a),
      tsupport a ⊆ U ∧ ∀ N : ℕ,
        HasCompactSchwartzSymbol (m - N)
          (quantizeSchwartz m a ha hca - ∑ j ∈ Finset.range N, P j) := by
  classical
  choose p hp hcp hreal using hP
  have hpK (j : ℕ) : tsupport (p j) ⊆ K := by
    apply tsupport_symbol_subset_of_hasOperatorSupport (m - j) (p j) (hp j)
      (P j) _ K hK.isClosed (hPK j)
    intro u x
    rw [hreal j, quantizeSchwartz_apply]
  have hanti : StrictAnti (fun j : ℕ ↦ m - (j : ℝ)) := by
    intro i j hij
    exact sub_lt_sub_left (Nat.cast_lt.mpr hij) _
  have hlim : Filter.Tendsto (fun j : ℕ ↦ m - (j : ℝ)) Filter.atTop Filter.atBot := by
    apply Filter.tendsto_atBot.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge (m - b)
    filter_upwards [Filter.eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ j := Nat.cast_le.mpr hj
    linarith
  obtain ⟨a, hexp, hca, haU⟩ :=
    exists_symbol_expansion_with_compact_support U K hU hK hKU _ hanti hlim p hp hpK
  have ha : IsSymbol Set.univ m a := by simpa using hexp 0
  have hsum (N : ℕ) :
      ∃ hs : IsSymbol Set.univ m (∑ j ∈ Finset.range N, p j),
      ∃ hcs : HasCompactSupport (∑ j ∈ Finset.range N, p j),
        (∑ j ∈ Finset.range N, P j) =
          quantizeSchwartz m (∑ j ∈ Finset.range N, p j) hs hcs := by
    induction N with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      refine ⟨isSymbol_zero _ _, ?_, ?_⟩
      · simp [HasCompactSupport, tsupport]
      · apply ContinuousLinearMap.ext
        intro u
        apply SchwartzMap.ext
        intro x
        simp [quantizeSchwartz_apply, quantize]
    | succ N ih =>
      obtain ⟨hs, hcs, heq⟩ := ih
      have hp' : IsSymbol Set.univ m (p N) :=
        (hp N).mono (sub_le_self _ (Nat.cast_nonneg N))
      simp only [Finset.sum_range_succ]
      refine ⟨hs.add isOpen_univ hp', hcs.add (hcp N), ?_⟩
      rw [quantizeSchwartz_add m _ _ hs hp' hcs (hcp N) _ _, heq, hreal N]
      congr 1
  refine ⟨a, ha, hca, haU, ?_⟩
  intro N
  obtain ⟨hs, hcs, heq⟩ := hsum N
  rw [heq]
  exact HasCompactSchwartzSymbol.sub_quantize m (m - N) a _ ha hs hca hcs (hexp N)

/-- The constant identity full symbol gives the exact compact multiplication operator. -/
theorem quantizeSchwartz_cutoffIdentity {n r : ℕ}
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    quantizeSchwartz 0 (zeroExtendedSymbol Set.univ χ (besselSymbol n r 0))
      (isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 0 χ hχ hcχ
        (Set.subset_univ _) (besselSymbol n r 0) (isSymbol_besselSymbol n r 0))
      (hasCompactSupport_zeroExtendedSymbol Set.univ χ (besselSymbol n r 0) hcχ) =
        SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ)) := by
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  let p := zeroExtendedSymbol Set.univ χ (besselSymbol n r 0)
  symm
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.smulLeftCLM_apply_apply hχT, quantizeSchwartz_apply]
  have hquant : quantize p u x = (χ x : ℂ) • quantize (besselSymbol n r 0) u x := by
    dsimp only [p, quantize]
    simp only [zeroExtendedSymbol_apply_of_mem Set.univ χ _ x _ (Set.mem_univ x), smul_apply]
    simp_rw [smul_comm (Complex.exp _) (χ x : ℂ)]
    rw [integral_smul]
    exact smul_comm _ _ _
  rw [hquant, quantize_besselSymbol]
  simp only [zero_div, Real.rpow_zero, SchwartzMap.fourierMultiplierCLM_const,
    one_smul, ContinuousLinearMap.id_apply]

/-- A smooth compact multiplier is an actual properly supported order-zero operator. -/
theorem compact_symbol_cutoff {n r : ℕ}
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) :
    HasCompactSchwartzSymbol 0
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ))) ∧
    HasOperatorSupport (tsupport χ)
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ))) := by
  let M := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ))
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  let p := zeroExtendedSymbol Set.univ χ (besselSymbol n r 0)
  have hp := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 0 χ hχ hcχ
    (Set.subset_univ _) (besselSymbol n r 0) (isSymbol_besselSymbol n r 0)
  have hcp := hasCompactSupport_zeroExtendedSymbol Set.univ χ (besselSymbol n r 0) hcχ
  constructor
  · refine ⟨p, hp, hcp, ?_⟩
    exact (quantizeSchwartz_cutoffIdentity χ hχ hcχ).symm
  · constructor
    · intro u
      apply closure_minimal _ (isClosed_tsupport χ)
      intro x hx
      by_contra hout
      apply hx
      rw [SchwartzMap.smulLeftCLM_apply_apply hχT,
        image_eq_zero_of_notMem_tsupport hout, Complex.ofReal_zero, zero_smul]
    · intro u hdisj
      apply SchwartzMap.ext
      intro x
      by_cases hx : x ∈ tsupport χ
      · have hu : x ∉ tsupport u := by
          intro hxu
          exact Set.disjoint_left.mp hdisj hxu hx
        rw [SchwartzMap.smulLeftCLM_apply_apply hχT,
          image_eq_zero_of_notMem_tsupport hu, smul_zero]
        rfl
      · rw [SchwartzMap.smulLeftCLM_apply_apply hχT,
          image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_smul]
        rfl

namespace HasOperatorSupport

variable {n r s : ℕ} {K L : Set (EuclideanSpace ℝ (Fin n))}
  {P Q : LocalSchwartzOperator n r s}

theorem mono (hP : HasOperatorSupport K P) (hKL : K ⊆ L) :
    HasOperatorSupport L P := by
  refine ⟨fun u ↦ (hP.1 u).trans hKL, ?_⟩
  intro u hdisj
  exact hP.2 u (hdisj.mono_right hKL)

theorem sub (hP : HasOperatorSupport K P) (hQ : HasOperatorSupport K Q)
    (hK : IsClosed K) : HasOperatorSupport K (P - Q) := by
  constructor
  · intro u
    apply closure_minimal _ hK
    intro x hx
    by_contra hout
    apply hx
    change P u x - Q u x = 0
    rw [image_eq_zero_of_notMem_tsupport (fun hx ↦ hout (hP.1 u hx)),
      image_eq_zero_of_notMem_tsupport (fun hx ↦ hout (hQ.1 u hx)), sub_self]
  · intro u hd
    simp only [sub_apply, hP.2 u hd, hQ.2 u hd, sub_self]

end HasOperatorSupport

/-- The actual composition differs from quantizing the leading product by one symbol order. -/
theorem compact_schwartzOperator_comp_sub_symbolComp {n r s t : ℕ}
    (l m : ℝ) (p : SymbolFunction n s t) (q : SymbolFunction n r s)
    (hp : IsSymbol Set.univ l p) (hq : IsSymbol Set.univ m q)
    (hcp : HasCompactSupport p) (hcq : HasCompactSupport q)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hPK : HasOperatorSupport K (quantizeSchwartz l p hp hcp))
    (hQK : HasOperatorSupport K (quantizeSchwartz m q hq hcq)) :
    ∃ hcprod : HasCompactSupport (symbolComp p q),
      HasCompactSchwartzSymbol (l + m - 1)
        ((quantizeSchwartz l p hp hcp).comp (quantizeSchwartz m q hq hcq) -
          quantizeSchwartz (l + m) (symbolComp p q)
            (hp.symbolComp isOpen_univ hq) hcprod) := by
  obtain ⟨χ, hχ, hcχ, _, hone⟩ :=
    exists_compact_cutoff_one_near K Set.univ hK isOpen_univ (Set.subset_univ _)
  have hprod : HasCompactSupport (symbolComp p q) := by
    apply hcp.of_isClosed_subset (isClosed_tsupport _)
    apply closure_mono
    intro x hx
    by_contra hout
    apply hx
    funext ξ
    simp only [symbolComp, not_not.mp hout, Pi.zero_apply, ContinuousLinearMap.zero_comp]
  have hab := isSymbol_compositionSymbol l m p q hp hq hcp hcq χ hχ hcχ
  have hcab : HasCompactSupport (compositionSymbol χ p q) :=
    hcp.of_isClosed_subset (isClosed_tsupport _) (tsupport_compositionSymbol_subset χ p q)
  have heq : (quantizeSchwartz l p hp hcp).comp (quantizeSchwartz m q hq hcq) =
      quantizeSchwartz (l + m) (compositionSymbol χ p q) hab hcab := by
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, quantizeSchwartz_apply (l + m)]
    exact (quantize_compositionSymbol l m p q hp hq _ _
      (quantizeSchwartz_apply l p hp hcp) (quantizeSchwartz_apply m q hq hcq)
      K hK hPK hQK χ hχ hcχ hone u x).symm
  refine ⟨hprod, ?_⟩
  rw [heq]
  apply HasCompactSchwartzSymbol.sub_quantize (l + m) (l + m - 1) _ _ hab
    (hp.symbolComp isOpen_univ hq) hcab hprod
  exact isSymbol_compositionSymbol_sub l m p q hp hq _ _
    (quantizeSchwartz_apply l p hp hcp) (quantizeSchwartz_apply m q hq hcq)
    K hK hPK hQK χ hχ hcχ hone

/-- Compact spatial symbols are closed under actual composition without an input support axiom. -/
theorem HasCompactSchwartzSymbol.comp_any {n r s t : ℕ}
    {P : LocalSchwartzOperator n s t} {Q : LocalSchwartzOperator n r s} {l m : ℝ}
    (hP : HasCompactSchwartzSymbol l P) (hQ : HasCompactSchwartzSymbol m Q) :
    HasCompactSchwartzSymbol (l + m) (P.comp Q) := by
  obtain ⟨q, hq, hcq, rfl⟩ := hQ
  obtain ⟨b, hb, hcb, _, K, hK, _, hbK, hdiff, _⟩ :=
    exists_proper_quantization_mod_smoothing m q hq hcq Set.univ isOpen_univ (Set.subset_univ _)
  have hmain := hP.comp (show HasCompactSchwartzSymbol m (quantizeSchwartz m b hb hcb) from
    ⟨b, hb, hcb, rfl⟩) K hK hbK
  have htail := (hdiff.comp_left hP).order (l + m)
  convert hmain.add htail using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, add_apply, sub_apply, map_sub]
  abel

theorem HasCompactSmoothingSchwartzSymbol.zero {n r s : ℕ} :
    HasCompactSmoothingSchwartzSymbol (0 : LocalSchwartzOperator n r s) := by
  have hs : IsSmoothingSymbol Set.univ (0 : SymbolFunction n r s) := by
    intro m
    exact isSymbol_zero _ m
  have hc : HasCompactSupport (0 : SymbolFunction n r s) := by
    simp [HasCompactSupport, tsupport]
  refine ⟨0, hs, hc, ?_⟩
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [quantizeSchwartz_apply 0 (0 : SymbolFunction n r s)]
  simp [quantize]

theorem HasCompactSmoothingSchwartzSymbol.neg {n r s : ℕ} {P : LocalSchwartzOperator n r s}
    (hP : HasCompactSmoothingSchwartzSymbol P) : HasCompactSmoothingSchwartzSymbol (-P) := by
  apply (hasCompactSmoothingSchwartzSymbol_iff _).mpr
  intro m
  simpa only [neg_one_smul] using (hP.order m).smul (-1)

theorem IsLocallySmoothingSchwartz.zero {n r s : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} :
    IsLocallySmoothingSchwartz U (0 : LocalSchwartzOperator n r s) :=
  IsLocallySmoothingSchwartz.of_smoothing HasCompactSmoothingSchwartzSymbol.zero

theorem IsLocallySmoothingSchwartz.neg {n r s : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {P : LocalSchwartzOperator n r s} (hP : IsLocallySmoothingSchwartz U P) :
    IsLocallySmoothingSchwartz U (-P) := by
  intro χ hχ hcχ hχU
  simpa only [ContinuousLinearMap.comp_neg] using (hP χ hχ hcχ hχU).neg

/-- A plateau is a local identity on the right, modulo the actual off-diagonal smoothing tail. -/
theorem isLocallySmoothingSchwartz_comp_cutoff_sub {n r s : ℕ} {m : ℝ}
    {P : LocalSchwartzOperator n r s} (hP : HasCompactSchwartzSymbol m P)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcθ : HasCompactSupport θ) :
    IsLocallySmoothingSchwartz (interior {x | θ x = 1})
      (P.comp (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (θ x : ℂ))) - P) := by
  intro χ hχ hcχ hχone
  have h := (hasCompactSmoothingSchwartzSymbol_offDiagonal hP χ θ
    hχ hcχ hθ hcθ hχone).neg
  convert h using 1
  apply ContinuousLinearMap.ext
  intro u
  simp only [ContinuousLinearMap.comp_apply, sub_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_sub]
  abel

/-- A plateau is an exact local identity on the left. -/
theorem isLocallySmoothingSchwartz_cutoff_comp_sub {n r s : ℕ}
    (P : LocalSchwartzOperator n r s)
    (θ : EuclideanSpace ℝ (Fin n) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hcθ : HasCompactSupport θ) :
    IsLocallySmoothingSchwartz (interior {x | θ x = 1})
      ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (θ x : ℂ))).comp P - P) := by
  intro χ hχ hcχ hχone
  have hθT : (fun x ↦ (θ x : ℂ)).HasTemperateGrowth :=
    (hcθ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hθ)
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  convert (HasCompactSmoothingSchwartzSymbol.zero (n := n) (r := r) (s := s)) using 1
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, sub_apply,
    SchwartzMap.smulLeftCLM_apply_apply hχT, SchwartzMap.smulLeftCLM_apply_apply hθT]
  by_cases hx : x ∈ tsupport χ
  · have hxθ : θ x = 1 := show x ∈ {x | θ x = 1} from interior_subset (hχone hx)
    simp [hxθ]
  · simp [image_eq_zero_of_notMem_tsupport hx]

theorem IsLocallySmoothingSchwartz.mono {n r s : ℕ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} {P : LocalSchwartzOperator n r s}
    (hP : IsLocallySmoothingSchwartz U P) (hVU : V ⊆ U) :
    IsLocallySmoothingSchwartz V P := by
  intro χ hχ hcχ hχV
  exact hP χ hχ hcχ (hχV.trans hVU)

/-- Spatial zero extension is exactly multiplication of the Schwartz output. -/
theorem quantizeSchwartz_zeroExtendedSymbol_univ {n r s : ℕ}
    (m : ℝ) (p : SymbolFunction n r s) (hp : IsSymbol Set.univ m p)
    (hcp : HasCompactSupport p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    quantizeSchwartz m (zeroExtendedSymbol Set.univ χ p)
      (isSymbol_zeroExtendedSymbol Set.univ isOpen_univ m χ hχ hcχ (Set.subset_univ _) p hp)
      (hasCompactSupport_zeroExtendedSymbol Set.univ χ p hcχ) =
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp
          (quantizeSchwartz m p hp hcp) := by
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  rw [ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply hχT,
    quantizeSchwartz_apply, quantizeSchwartz_apply]
  dsimp only [quantize]
  simp only [zeroExtendedSymbol_apply_of_mem Set.univ χ p x _ (Set.mem_univ x), smul_apply]
  simp_rw [smul_comm (Complex.exp _) (χ x : ℂ)]
  rw [integral_smul]
  exact smul_comm _ _ _

/-- The output-cutoff remainder can use a smoothing symbol with exactly that support bound. -/
theorem IsLocallySmoothingSchwartz.exists_supported_symbol {n r s : ℕ}
    {U : Set (EuclideanSpace ℝ (Fin n))} {P : LocalSchwartzOperator n r s}
    (hP : IsLocallySmoothingSchwartz U P) (hU : IsOpen U)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∃ c : SymbolFunction n r s, ∃ (hc : IsSmoothingSymbol Set.univ c)
      (hcc : HasCompactSupport c), tsupport c ⊆ tsupport χ ∧
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp P =
          quantizeSchwartz 0 c (hc 0) hcc := by
  obtain ⟨β, hβ, hcβ, hβU, hβone⟩ :=
    exists_compact_cutoff_one_near (tsupport χ) U hcχ hU hχU
  obtain ⟨b, hb, hcb, hreal⟩ := hP β hβ hcβ hβU
  let c := zeroExtendedSymbol Set.univ χ b
  have hc : IsSmoothingSymbol Set.univ c := by
    intro m
    exact isSymbol_zeroExtendedSymbol Set.univ isOpen_univ m χ hχ hcχ
      (Set.subset_univ _) b (hb m)
  have hcc := hasCompactSupport_zeroExtendedSymbol Set.univ χ b hcχ
  refine ⟨c, hc, hcc, tsupport_zeroExtendedSymbol_subset Set.univ χ b, ?_⟩
  have heq : quantizeSchwartz 0 c (hc 0) hcc =
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin s)) (fun x ↦ (χ x : ℂ))).comp
        (quantizeSchwartz 0 b (hb 0) hcb) :=
    quantizeSchwartz_zeroExtendedSymbol_univ 0 b (hb 0) hcb χ hχ hcχ
  rw [heq, ← hreal]
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hβT : (fun x ↦ (β x : ℂ)).HasTemperateGrowth :=
    (hcβ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hβ)
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply hχT,
    SchwartzMap.smulLeftCLM_apply_apply hβT]
  by_cases hx : x ∈ tsupport χ
  · have hxβ : β x = 1 := show x ∈ {x | β x = 1} from interior_subset (hβone hx)
    simp [hxβ]
  · simp [image_eq_zero_of_notMem_tsupport hx]

end AtiyahSinger
