/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConicSymbolEstimates
public import AtiyahSinger.Analysis.HomogeneousCutoff
public import AtiyahSinger.Analysis.SpatialQuantization

import all AtiyahSinger.Analysis.SymbolFourier
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# The local product-frequency cutoff and its Sobolev approximation

Public module ID: M0882.

UL02: the cutoff in SG III.13.5, printed p.250, regularizes the lift of a
first-order symbol from one factor of a product. The fixed profile below is
zero on `[0,1]` and one on `[2,infinity)`, exactly as in the book. Its extension
to negative arguments is merely the chosen smooth bump complement.

The ratio in the printed formula has a removable axis singularity after the
radial cutoff is included. At `r = 0` its correct value is `1 - phi(epsilon*s)`
for nonnegative `s`. Lean's division by zero would instead produce the wrong
value one; the definition therefore specifies the axis explicitly.

The first symbol has compact support in its own spatial variable. A second
supplied compactly supported smooth spatial cutoff makes the lifted symbol
compactly supported in the entire product base. Both base and frequency
coordinates use the same `EuclideanSpace.finAddEquivProd`; the radial frequency
is `sqrt(r^2+s^2)`, not the supremum norm on the native product model.

For positive epsilon the regularized symbol is a standard symbol of order
one. The unregularized lift and the error need not be standard product symbols.
Their error quantization is instead characterized by the original Fourier
integral and Bessel coordinates, then estimated directly using spatial
derivatives. The uniform estimate is an actual operator-norm `H^1 -> H^0`
approximation. No symbol-seminorm convergence of the unregularized lift is
assumed. The all-real parameter family includes the zero error at epsilon zero.

Source: SG III.13.5 p.250 explicitly leaves this cutoff verification as an
exercise. The detailed local estimate is a project supplement, not a numbered
book lemma. Global bundle assembly and the closed tensor domain of UL01 are
downstream applications. The compact-control symbol homotopy is established
in `GradedProductSymbolHomotopy`.
Conic frequency estimates give standard-symbol regularity; uniform spatial
Fourier estimates give the error realization and norm approximation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter FourierTransform MeasureTheory
open scoped ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 15

variable {n m r q : ℕ}

/-- SG's fixed profile, zero for nonnegative arguments at most one and one from two onwards. -/
def productCutoffProfile (t : ℝ) : ℝ :=
  1 - (⟨1, 2, by norm_num, by norm_num⟩ : ContDiffBump (0 : ℝ)) t

/-- The printed product-frequency cutoff with its continuous extension on the first axis. -/
def productFrequencyCutoff (ε r s : ℝ) : ℝ :=
  1 - productCutoffProfile (ε * Real.sqrt (r ^ 2 + s ^ 2)) *
    (if r = 0 then 1 else productCutoffProfile (ε * s / r))

/-- Lift a first-factor symbol and multiply by the specified second-factor spatial cutoff. -/
def liftedProductSymbol (a : SymbolFunction n r q)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) : SymbolFunction (n + m) r q :=
  fun x ξ ↦
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    (χ (split x).2 : ℂ) • a (split x).1 (split ξ).1

/-- The actual product-frequency regularization, in the original finite Euclidean coordinates. -/
def productCutoffSymbol (a : SymbolFunction n r q)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (ε : ℝ) : SymbolFunction (n + m) r q :=
  fun x ξ ↦
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    (productFrequencyCutoff ε ‖(split ξ).1‖ ‖(split ξ).2‖ : ℂ) •
      liftedProductSymbol a χ x ξ

/-- The original lifted symbol minus this very regularization, before quantization. -/
def productCutoffErrorSymbol (a : SymbolFunction n r q)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (ε : ℝ) : SymbolFunction (n + m) r q :=
  liftedProductSymbol a χ - productCutoffSymbol a χ ε

/- The following local scalar estimate is shared by existence and uniform approximation.
It uses the support of both exact profile factors, including the stipulated first-axis value. -/
private theorem productCutoffError_scalar_bound (ε r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    0 ≤ 1 - productFrequencyCutoff ε r s ∧
      1 - productFrequencyCutoff ε r s ≤ 1 ∧
      (0 < ε → (1 - productFrequencyCutoff ε r s) * (1 + r) ≤
        2 * ε * (1 + Real.sqrt (r ^ 2 + s ^ 2))) := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hprofile (t : ℝ) : 0 ≤ productCutoffProfile t ∧ productCutoffProfile t ≤ 1 := by
    have h₀ : 0 ≤ φ t := φ.nonneg
    have h₁ : φ t ≤ 1 := φ.le_one
    change 0 ≤ 1 - φ t ∧ 1 - φ t ≤ 1
    constructor <;> linarith
  have hzero (t : ℝ) (ht : |t| ≤ 1) : productCutoffProfile t = 0 := by
    change 1 - φ t = 0
    have ht' : t ∈ Metric.closedBall (0 : ℝ) φ.rIn := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, φ] using ht
    rw [φ.one_of_mem_closedBall ht', sub_self]
  let R := Real.sqrt (r ^ 2 + s ^ 2)
  let u := productCutoffProfile (ε * R)
  let v := if r = 0 then 1 else productCutoffProfile (ε * s / r)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hsR : s ≤ R := by
    have hsq : R ^ 2 = r ^ 2 + s ^ 2 := Real.sq_sqrt (by positivity)
    nlinarith
  have hu : 0 ≤ u ∧ u ≤ 1 := hprofile _
  have hv : 0 ≤ v ∧ v ≤ 1 := by
    by_cases h : r = 0
    · simp [v, h]
    · simpa only [v, ite_eq_right h] using hprofile (ε * s / r)
  have heq : 1 - productFrequencyCutoff ε r s = u * v := by
    dsimp [productFrequencyCutoff, u, v, R]
    ring
  rw [heq]
  have huv : 0 ≤ u * v := mul_nonneg hu.1 hv.1
  have huv1 : u * v ≤ 1 := by
    nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hv.2)]
  refine ⟨huv, huv1, ?_⟩
  intro hε
  by_cases hE : u * v = 0
  · rw [hE, zero_mul]
    positivity
  have hu0 : u ≠ 0 := left_ne_zero_of_mul hE
  have hv0 : v ≠ 0 := right_ne_zero_of_mul hE
  have hrad : 1 < ε * R := by
    by_contra h
    exact hu0 (hzero _ (by rw [abs_of_nonneg (mul_nonneg hε.le hR)]; linarith))
  have hcone : r ≤ ε * R := by
    by_cases hr0 : r = 0
    · rw [hr0]
      positivity
    have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hratio : 1 < ε * s / r := by
      by_contra h
      apply hv0
      dsimp only [v]
      rw [ite_eq_right hr0]
      apply hzero
      rw [abs_of_nonneg (div_nonneg (mul_nonneg hε.le hs) hr)]
      linarith
    have hsmall : r < ε * s := by
      simpa only [one_mul] using (lt_div_iff₀ hrpos).mp hratio
    exact hsmall.le.trans (mul_le_mul_of_nonneg_left hsR hε.le)
  calc
    u * v * (1 + r) ≤ 1 + r := by nlinarith
    _ ≤ 2 * ε * (1 + R) := by nlinarith

/- Spatial bounds are uniform in the cutoff parameter. The parameter occurs only in
one nonnegative scalar; all derivative constants are chosen from a and χ first. -/
private theorem productCutoffError_spatial_data (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ K : Set (EuclideanSpace ℝ (Fin (n + m))), IsCompact K ∧
      (∀ ε x, x ∉ K → ∀ ξ, productCutoffErrorSymbol a χ ε x ξ = 0) ∧
      (∀ ε, StronglyMeasurable (Function.uncurry (productCutoffErrorSymbol a χ ε))) ∧
      (∀ ε ξ, ContDiff ℝ ∞ (fun x ↦ productCutoffErrorSymbol a χ ε x ξ)) ∧
      (∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ξ x, x ∈ K →
        ‖iteratedFDeriv ℝ i (fun y ↦ productCutoffErrorSymbol a χ ε y ξ) x‖ ≤
          C * ((1 - productFrequencyCutoff ε
            ‖(EuclideanSpace.finAddEquivProd ξ).1‖
            ‖(EuclideanSpace.finAddEquivProd ξ).2‖) *
              (1 + ‖(EuclideanSpace.finAddEquivProd ξ).1‖))) := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let X₁ := EuclideanSpace ℝ (Fin n)
  let X₂ := EuclideanSpace ℝ (Fin m)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let split : X ≃L[ℝ] X₁ × X₂ := EuclideanSpace.finAddEquivProd
  let p₁ : X →L[ℝ] X₁ := (ContinuousLinearMap.fst ℝ X₁ X₂).comp split.toContinuousLinearMap
  let p₂ : X →L[ℝ] X₂ := (ContinuousLinearMap.snd ℝ X₁ X₂).comp split.toContinuousLinearMap
  let K : Set X := split.symm '' (tsupport a ×ˢ tsupport χ)
  have hK : IsCompact K := (haK.prod hχK).image split.symm.continuous
  have hx₁ (x : X) (hx : x ∈ K) : p₁ x ∈ tsupport a := by
    obtain ⟨z, hz, rfl⟩ := hx
    change (split (split.symm z)).1 ∈ tsupport a
    simpa only [split.apply_symm_apply] using hz.1
  have hac : ContDiff ℝ ∞ (Function.uncurry a) := by
    simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
  have has (η : X₁) : ContDiff ℝ ∞ (fun x ↦ a x η) :=
    hac.comp (contDiff_id.prodMk contDiff_const)
  let c : X → ℂ := fun x ↦ (χ (p₂ x) : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp (hχ.comp p₂.contDiff)
  have hbase (ξ : X) : ContDiff ℝ ∞ (fun x ↦ liftedProductSymbol a χ x ξ) :=
    hc.smul ((has (p₁ ξ)).comp p₁.contDiff)
  let b (ε : ℝ) (ξ : X) : ℝ :=
    1 - productFrequencyCutoff ε ‖p₁ ξ‖ ‖p₂ ξ‖
  have hb0 (ε : ℝ) (ξ : X) : 0 ≤ b ε ξ :=
    (productCutoffError_scalar_bound ε _ _ (norm_nonneg _) (norm_nonneg _)).1
  have heq (ε : ℝ) (x ξ : X) : productCutoffErrorSymbol a χ ε x ξ =
      (b ε ξ : ℂ) • liftedProductSymbol a χ x ξ := by
    simp only [productCutoffErrorSymbol, Pi.sub_apply, productCutoffSymbol, b,
      Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rfl
  refine ⟨K, hK, ?_, ?_, ?_, ?_⟩
  · intro ε x hx ξ
    rw [heq]
    have hb : liftedProductSymbol a χ x ξ = 0 := by
      by_cases h₁ : p₁ x ∈ tsupport a
      · have h₂ : p₂ x ∉ tsupport χ := by
          intro h₂
          exact hx ⟨split x, ⟨h₁, h₂⟩, split.symm_apply_apply x⟩
        change (χ (p₂ x) : ℂ) • a (p₁ x) (p₁ ξ) = 0
        rw [image_eq_zero_of_notMem_tsupport h₂, Complex.ofReal_zero, zero_smul]
      · have hz : a (p₁ x) = 0 := image_eq_zero_of_notMem_tsupport h₁
        change (χ (p₂ x) : ℂ) • a (p₁ x) (p₁ ξ) = 0
        rw [hz]
        simp only [Pi.zero_apply, smul_zero]
    rw [hb, smul_zero]
  · intro ε
    have hb : Measurable (b ε) := by
      have hp : Continuous productCutoffProfile := by
        exact continuous_const.sub (ContDiffBump.continuous _)
      have h₁ : Measurable (fun ξ : X ↦ ‖p₁ ξ‖) := p₁.continuous.measurable.norm
      have h₂ : Measurable (fun ξ : X ↦ ‖p₂ ξ‖) := p₂.continuous.measurable.norm
      have hv : Measurable (fun ξ : X ↦ if ‖p₁ ξ‖ = 0 then (1 : ℝ)
          else productCutoffProfile (ε * ‖p₂ ξ‖ / ‖p₁ ξ‖)) :=
        Measurable.ite (measurableSet_eq_fun h₁ measurable_const) measurable_const
          (hp.measurable.comp ((h₂.const_mul ε).div h₁))
      have hu : Measurable (fun ξ : X ↦
          productCutoffProfile (ε * Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2))) :=
        hp.measurable.comp ((Real.continuous_sqrt.measurable.comp
          ((h₁.pow_const 2).add (h₂.pow_const 2))).const_mul ε)
      exact measurable_const.sub (measurable_const.sub (hu.mul hv))
    have hbc : StronglyMeasurable (fun z : X × X ↦ (b ε z.2 : ℂ)) :=
      (Complex.continuous_ofReal.measurable.comp (hb.comp measurable_snd)).stronglyMeasurable
    have hbasec : Continuous (Function.uncurry (liftedProductSymbol a χ)) := by
      exact (hc.continuous.comp continuous_fst).smul
        (hac.continuous.comp ((p₁.continuous.comp continuous_fst).prodMk
          (p₁.continuous.comp continuous_snd)))
    have hh : StronglyMeasurable (fun z : X × X ↦
        (b ε z.2 : ℂ) • liftedProductSymbol a χ z.1 z.2) :=
      hbc.smul hbasec.stronglyMeasurable
    have hh' : Function.uncurry (productCutoffErrorSymbol a χ ε) =
        fun z : X × X ↦ (b ε z.2 : ℂ) • liftedProductSymbol a χ z.1 z.2 := by
      funext z
      exact heq ε z.1 z.2
    rw [hh']
    exact hh
  · intro ε ξ
    simp_rw [heq]
    exact (hbase ξ).const_smul _
  · intro i
    -- First-factor derivatives pull back along the fixed coordinate projection.
    have hader (j : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ x, x ∈ K →
        ‖iteratedFDeriv ℝ j (fun y ↦ a (p₁ y) (p₁ ξ)) x‖ ≤ A * (1 + ‖p₁ ξ‖) := by
      obtain ⟨A, hA, hAb⟩ := ha.2 (tsupport a) (Set.subset_univ _) haK j 0
      refine ⟨A * ‖p₁‖ ^ j, by positivity, ?_⟩
      intro ξ x hx
      have hd : ‖iteratedFDeriv ℝ j (fun y ↦ a y (p₁ ξ)) (p₁ x)‖ ≤
          A * (1 + ‖p₁ ξ‖) := by
        have hz : (fun y ↦ iteratedFDeriv ℝ 0 (a y) (p₁ ξ)) =
            (continuousMultilinearCurryFin0 ℝ X₁ V).symm ∘ (fun y ↦ a y (p₁ ξ)) := by
          funext y
          exact congrFun iteratedFDeriv_zero_eq_comp _
        simpa only [symbolDerivative, hz, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
          Nat.cast_zero, sub_zero, Real.rpow_one] using hAb _ (hx₁ x hx) (p₁ ξ)
      rw [show (fun y ↦ a (p₁ y) (p₁ ξ)) = (fun y ↦ a y (p₁ ξ)) ∘ p₁ from rfl,
        p₁.iteratedFDeriv_comp_right (has _) x (by simp)]
      calc
        _ ≤ ‖iteratedFDeriv ℝ j (fun y ↦ a y (p₁ ξ)) (p₁ x)‖ * ‖p₁‖ ^ j := by
          simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
            (iteratedFDeriv ℝ j (fun y ↦ a y (p₁ ξ)) (p₁ x)).norm_compContinuousLinearMap_le
              (fun _ ↦ p₁)
        _ ≤ (A * (1 + ‖p₁ ξ‖)) * ‖p₁‖ ^ j := by gcongr
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
    intro ε ξ x hx
    have hbd : ‖iteratedFDeriv ℝ i (fun y ↦ liftedProductSymbol a χ y ξ) x‖ ≤
        C * (1 + ‖p₁ ξ‖) := by
      have hle := norm_iteratedFDeriv_smul_le hc ((has (p₁ ξ)).comp p₁.contDiff) x
        (n := i) (by simp)
      apply hle.trans
      simp only [C, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      have hBj := hB j
      calc
        _ ≤ (i.choose j : ℝ) * B j * (A (i - j) * (1 + ‖p₁ ξ‖)) := by
          gcongr
          · exact hBb j x hx
          · exact hAb (i - j) ξ x hx
        _ = _ := by ring
    simp_rw [heq]
    rw [iteratedFDeriv_const_smul_apply' ((hbase ξ).contDiffAt.of_le (by simp)),
      norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb0 ε ξ)]
    calc
      _ ≤ b ε ξ * (C * (1 + ‖p₁ ξ‖)) :=
        mul_le_mul_of_nonneg_left hbd (hb0 ε ξ)
      _ = _ := by
        change b ε ξ * (C * (1 + ‖p₁ ξ‖)) = C * (b ε ξ * (1 + ‖p₁ ξ‖))
        ring

/- Fourier continuity fixes one decay constant for the entire error family. Any
pointwise bound by δ(1+|ξ|) then gives the same operator bound Cδ. -/
private theorem exists_productCutoffErrorOperator_bound (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε δ : ℝ, 0 ≤ δ →
      (∀ ξ : EuclideanSpace ℝ (Fin (n + m)),
        (1 - productFrequencyCutoff ε ‖(EuclideanSpace.finAddEquivProd ξ).1‖
          ‖(EuclideanSpace.finAddEquivProd ξ).2‖) *
            (1 + ‖(EuclideanSpace.finAddEquivProd ξ).1‖) ≤ δ * (1 + ‖ξ‖)) →
      ∃ T : Lp (EuclideanSpace ℂ (Fin r)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
        Lp (EuclideanSpace ℂ (Fin q)) 2
          (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
        ‖T‖ ≤ C * δ ∧
        ∀ u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)),
          ∀ φ : 𝓢(EuclideanSpace ℝ (Fin (n + m)), ℂ),
            besselRealization (n + m) q 0 (T (schwartzSobolevCoordinate 1 u)) φ =
              ∫ x, φ x • quantize (productCutoffErrorSymbol a χ ε) u x := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let split : X ≃L[ℝ] EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) :=
    EuclideanSpace.finAddEquivProd
  let b (ε : ℝ) (ξ : X) :=
    1 - productFrequencyCutoff ε ‖(split ξ).1‖ ‖(split ξ).2‖
  let A : X → ℝ × X → EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q) :=
    fun x p ↦ productCutoffErrorSymbol a χ p.1 x p.2
  let w : ℝ × X → ℝ := fun p ↦ b p.1 p.2 * (1 + ‖(split p.2).1‖)
  have hw0 (p : ℝ × X) : 0 ≤ w p :=
    mul_nonneg (productCutoffError_scalar_bound _ _ _ (norm_nonneg _) (norm_nonneg _)).1
      (by positivity)
  obtain ⟨K, hK, hsupp, hmeas, hsmooth, hder⟩ :=
    productCutoffError_spatial_data a ha haK χ hχ hχK
  have hderA (i : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ p x, x ∈ K →
      ‖iteratedFDeriv ℝ i (fun y ↦ A y p) x‖ ≤ C * w p := by
    obtain ⟨C, hC, hb⟩ := hder i
    exact ⟨C, hC, fun p x hx ↦ hb p.1 p.2 x hx⟩
  have hFourier (N : ℕ) := spatial_fourier_decay_of_spatial_bounds A
    (fun p ↦ hsmooth p.1 p.2) K hK (fun x hx p ↦ hsupp p.1 x hx p.2) w hw0 hderA N
  obtain ⟨C₀, hC₀, hF₀⟩ := hFourier 0
  obtain ⟨C₁, hC₁, hF₁⟩ := hFourier (n + m + 1)
  obtain ⟨C₂, hC₂, hV⟩ := hder 0
  let D : ℝ := max ((2 * (2 * Real.pi) ^ 2) ^ ((1 : ℝ) / 2)) 1
  have hD : 0 ≤ D := zero_le_one.trans (le_max_right _ _)
  let d : X → ℝ := fun ζ ↦ (1 + ‖ζ‖) ^ (-((n + m : ℕ) : ℝ) - 1)
  have hd : Continuous d := by
    apply Continuous.rpow_const (continuous_const.add continuous_norm)
    intro ζ
    left
    exact ne_of_gt (show 0 < 1 + ‖ζ‖ from by positivity)
  have hd0 (ζ : X) : 0 ≤ d ζ := by dsimp [d]; positivity
  have hdi : Integrable d := by
    have hdim : (Module.finrank ℝ X : ℝ) < ((n + m : ℕ) : ℝ) + 1 := by simp [X]
    simpa only [d, neg_add, sub_eq_add_neg] using
      (integrable_one_add_norm (E := X) (μ := volume) hdim)
  refine ⟨C₁ * D * (∫ ζ, d ζ), by positivity, ?_⟩
  intro ε δ hδ hfreq
  have hval : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖productCutoffErrorSymbol a χ ε x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (1 : ℝ) := by
    refine ⟨C₂ * δ, mul_nonneg hC₂ hδ, ?_⟩
    intro x ξ
    rw [Real.rpow_one]
    by_cases hx : x ∈ K
    · have h := hV ε ξ x hx
      simp only [norm_iteratedFDeriv_zero] at h
      exact h.trans (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hfreq ξ) hC₂)
    · rw [hsupp ε x hx ξ, norm_zero]
      positivity
  have hfourier : ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ ζ,
      ‖𝓕 (fun x ↦ productCutoffErrorSymbol a χ ε x ξ) ζ‖ ≤
        C * (1 + ‖ξ‖) ^ (1 : ℝ) := by
    refine ⟨C₀ * δ, mul_nonneg hC₀ hδ, ?_⟩
    intro ξ ζ
    have h := hF₀ (ε, ξ) ζ
    simp only [Nat.cast_zero, neg_zero, Real.rpow_zero, mul_one] at h
    rw [Real.rpow_one]
    exact h.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hfreq ξ) hC₀)
  have hweight (η : X) :
      (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) * (1 + ‖(2 * Real.pi) • η‖) ≤ D := by
    have h := spatial_weight_le_bessel (1 : ℝ) η
    rw [Real.rpow_one] at h
    calc
      _ ≤ (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (D * (1 + ‖η‖ ^ 2) ^ ((1 : ℝ) / 2)) := by gcongr
      _ = D := by
        rw [mul_left_comm, ← Real.rpow_add (by positivity)]
        norm_num
  let dδ : X → ℝ := fun ζ ↦ (C₁ * D * δ) * d ζ
  have hdδ : Continuous dδ := hd.const_mul _
  have hdδ0 (ζ : X) : 0 ≤ dδ ζ := mul_nonneg (by positivity) (hd0 ζ)
  have hdiδ : Integrable dδ := hdi.const_mul _
  have hdeδ (ζ : X) : dδ (-ζ) = dδ ζ := by simp only [dδ, d, norm_neg]
  have hbound (ξ η : X) :
      ‖((1 + ‖ξ‖ ^ 2) ^ (((1 : ℝ) - 1) / 2) * (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2))) •
        𝓕 (fun x ↦ productCutoffErrorSymbol a χ ε x ((2 * Real.pi) • η)) (ξ - η)‖ ≤
          dδ (ξ - η) := by
    have hF := hF₁ (ε, (2 * Real.pi) • η) (ξ - η)
    have hexp : -((n + m + 1 : ℕ) : ℝ) = -((n + m : ℕ) : ℝ) - 1 := by push_cast; ring
    rw [hexp] at hF
    norm_num only [sub_self, zero_div, Real.rpow_zero, one_mul]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      _ ≤ (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (C₁ * w (ε, (2 * Real.pi) • η) * d (ξ - η)) := by gcongr
      _ ≤ (1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) *
          (C₁ * (δ * (1 + ‖(2 * Real.pi) • η‖)) * d (ξ - η)) := by
        gcongr
        exact hfreq _
      _ = (C₁ * δ * d (ξ - η)) *
          ((1 + ‖η‖ ^ 2) ^ (-((1 : ℝ) / 2)) * (1 + ‖(2 * Real.pi) • η‖)) := by ring
      _ ≤ (C₁ * δ * d (ξ - η)) * D :=
        mul_le_mul_of_nonneg_left (hweight η) (by positivity)
      _ = dδ (ξ - η) := by dsimp only [dδ]; ring
  obtain ⟨T, hTnorm, hT⟩ := exists_quantize_sobolev_extension_of_spatial_bounds
    1 1 (productCutoffErrorSymbol a χ ε) (hmeas ε) (hsmooth ε) hval hfourier
    K hK (hsupp ε) dδ hdδ hdδ0 hdiδ hdeδ (by simpa only [neg_div] using hbound)
  refine ⟨T, ?_, ?_⟩
  · apply hTnorm.trans_eq
    rw [integral_const_mul]
    ring
  · simpa only [sub_self] using hT

/- Both bounds use the very same Euclidean splitting. Operator norms of its two
projections absorb the change from the joint Euclidean norm to the two factor norms. -/
private theorem productCutoffError_frequency_bounds (n m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ ε : ℝ, ∀ ξ : EuclideanSpace ℝ (Fin (n + m)),
        (1 - productFrequencyCutoff ε ‖(EuclideanSpace.finAddEquivProd ξ).1‖
          ‖(EuclideanSpace.finAddEquivProd ξ).2‖) *
            (1 + ‖(EuclideanSpace.finAddEquivProd ξ).1‖) ≤ B * (1 + ‖ξ‖)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ ξ : EuclideanSpace ℝ (Fin (n + m)),
        (1 - productFrequencyCutoff ε ‖(EuclideanSpace.finAddEquivProd ξ).1‖
          ‖(EuclideanSpace.finAddEquivProd ξ).2‖) *
            (1 + ‖(EuclideanSpace.finAddEquivProd ξ).1‖) ≤ B * ε * (1 + ‖ξ‖)) := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let X₁ := EuclideanSpace ℝ (Fin n)
  let X₂ := EuclideanSpace ℝ (Fin m)
  let split : X ≃L[ℝ] X₁ × X₂ := EuclideanSpace.finAddEquivProd
  let p₁ : X →L[ℝ] X₁ := (ContinuousLinearMap.fst ℝ X₁ X₂).comp split.toContinuousLinearMap
  let p₂ : X →L[ℝ] X₂ := (ContinuousLinearMap.snd ℝ X₁ X₂).comp split.toContinuousLinearMap
  let B : ℝ := 2 * (1 + ‖p₁‖ + ‖p₂‖)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, ?_, ?_⟩
  · intro ε ξ
    have hb := (productCutoffError_scalar_bound ε ‖p₁ ξ‖ ‖p₂ ξ‖
      (norm_nonneg _) (norm_nonneg _)).2.1
    have h₁ := p₁.le_opNorm ξ
    have h₂ := norm_nonneg p₂
    have hξ := norm_nonneg ξ
    change (1 - productFrequencyCutoff ε ‖p₁ ξ‖ ‖p₂ ξ‖) * (1 + ‖p₁ ξ‖) ≤ _
    calc
      _ ≤ 1 + ‖p₁ ξ‖ := by nlinarith [norm_nonneg (p₁ ξ)]
      _ ≤ B * (1 + ‖ξ‖) := by dsimp [B]; nlinarith [norm_nonneg p₁]
  · intro ε hε ξ
    have hb := (productCutoffError_scalar_bound ε ‖p₁ ξ‖ ‖p₂ ξ‖
      (norm_nonneg _) (norm_nonneg _)).2.2 hε
    have hR : Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2) ≤ ‖p₁ ξ‖ + ‖p₂ ξ‖ := by
      have hs := Real.sq_sqrt (show 0 ≤ ‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2 by positivity)
      have h₀ := Real.sqrt_nonneg (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2)
      nlinarith [norm_nonneg (p₁ ξ), norm_nonneg (p₂ ξ),
        mul_nonneg (norm_nonneg (p₁ ξ)) (norm_nonneg (p₂ ξ))]
    have hsp : 2 * (1 + Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2)) ≤ B * (1 + ‖ξ‖) := by
      have h₁ := p₁.le_opNorm ξ
      have h₂ := p₂.le_opNorm ξ
      dsimp [B]
      nlinarith [norm_nonneg p₁, norm_nonneg p₂, norm_nonneg ξ]
    apply hb.trans
    nlinarith [mul_le_mul_of_nonneg_right hsp hε.le]

/- Axis patching establishes genuine smoothness before any derivative estimate.
The high-frequency tail is degree zero and is supported in the first-frequency cone. -/
private theorem productFrequencyCutoff_regularity (n m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let f := fun ξ ↦ productFrequencyCutoff ε ‖(split ξ).1‖ ‖(split ξ).2‖
    ContDiff ℝ ∞ f ∧
      (∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ,
        ‖iteratedFDeriv ℝ j f ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(j : ℝ))) ∧
      (∀ ξ, 2 ≤ ε * Real.sqrt (‖(split ξ).1‖ ^ 2 + ‖(split ξ).2‖ ^ 2) →
        2 * ‖(split ξ).1‖ ≤ ε * ‖(split ξ).2‖ → f ξ = 0) := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let X₁ := EuclideanSpace ℝ (Fin n)
  let X₂ := EuclideanSpace ℝ (Fin m)
  let split : X ≃L[ℝ] X₁ × X₂ := EuclideanSpace.finAddEquivProd
  let p₁ : X →L[ℝ] X₁ := (ContinuousLinearMap.fst ℝ X₁ X₂).comp split.toContinuousLinearMap
  let p₂ : X →L[ℝ] X₂ := (ContinuousLinearMap.snd ℝ X₁ X₂).comp split.toContinuousLinearMap
  let R : X → ℝ := fun ξ ↦ Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2)
  let f : X → ℝ := fun ξ ↦ productFrequencyCutoff ε ‖p₁ ξ‖ ‖p₂ ξ‖
  let g : X → ℝ := fun ξ ↦ if ‖p₁ ξ‖ = 0 then 0 else
    1 - productCutoffProfile (ε * ‖p₂ ξ‖ / ‖p₁ ξ‖)
  have hp : ContDiff ℝ ∞ productCutoffProfile := contDiff_const.sub (ContDiffBump.contDiff _)
  have hp0 (t : ℝ) (ht : |t| ≤ 1) : productCutoffProfile t = 0 := by
    let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    change 1 - φ t = 0
    rw [φ.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, φ] using ht), sub_self]
  have hp1 (t : ℝ) (ht : 2 ≤ t) : productCutoffProfile t = 1 := by
    let φ : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
    change 1 - φ t = 1
    rw [φ.zero_of_le_dist (by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by linarith : 0 ≤ t), φ] using ht),
      sub_zero]
  have hRc : Continuous R :=
    Real.continuous_sqrt.comp ((p₁.continuous.norm.pow 2).add (p₂.continuous.norm.pow 2))
  have hR0 (ξ : X) : 0 ≤ R ξ := Real.sqrt_nonneg _
  have hg0 (ξ : X) (hcone : 2 * ‖p₁ ξ‖ ≤ ε * ‖p₂ ξ‖) : g ξ = 0 := by
    by_cases h₁ : ‖p₁ ξ‖ = 0
    · simp only [g, h₁, ite_true]
    · have hpos : 0 < ‖p₁ ξ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h₁)
      have hratio : 2 ≤ ε * ‖p₂ ξ‖ / ‖p₁ ξ‖ := (le_div_iff₀ hpos).mpr hcone
      simp only [g, ite_eq_right h₁, hp1 _ hratio, sub_self]
  have hg1 (ξ : X) (hcone : ε * ‖p₂ ξ‖ < ‖p₁ ξ‖) : g ξ = 1 := by
    have hpos : 0 < ‖p₁ ξ‖ := lt_of_le_of_lt (by positivity) hcone
    have hratio : |ε * ‖p₂ ξ‖ / ‖p₁ ξ‖| ≤ 1 := by
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_one hpos).mpr hcone.le
    simp only [g, ite_eq_right hpos.ne', hp0 _ hratio, sub_zero]
  have hgs (ξ : X) (hξ : p₁ ξ ≠ 0 ∨ p₂ ξ ≠ 0) : ContDiffAt ℝ ∞ g ξ := by
    by_cases h₁ : p₁ ξ = 0
    · have h₂ : p₂ ξ ≠ 0 := hξ.resolve_left (not_not.mpr h₁)
      have hcone : 2 * ‖p₁ ξ‖ < ε * ‖p₂ ξ‖ := by
        rw [h₁, norm_zero, mul_zero]
        exact mul_pos hε (norm_pos_iff.mpr h₂)
      have heq : g =ᶠ[𝓝 ξ] (fun _ ↦ 0) := by
        filter_upwards [(isOpen_lt (p₁.continuous.norm.const_mul 2)
          (p₂.continuous.norm.const_mul ε)).mem_nhds hcone] with ζ hζ
        exact hg0 ζ hζ.le
      exact contDiffAt_const.congr_of_eventuallyEq heq
    by_cases h₂ : p₂ ξ = 0
    · have hcone : ε * ‖p₂ ξ‖ < ‖p₁ ξ‖ := by
        rw [h₂, norm_zero, mul_zero]
        exact norm_pos_iff.mpr h₁
      have heq : g =ᶠ[𝓝 ξ] (fun _ ↦ 1) := by
        filter_upwards [(isOpen_lt (p₂.continuous.norm.const_mul ε)
          p₁.continuous.norm).mem_nhds hcone] with ζ hζ
        exact hg1 ζ hζ
      exact contDiffAt_const.congr_of_eventuallyEq heq
    have hr : ContDiffAt ℝ ∞ (fun ζ ↦ ε * ‖p₂ ζ‖ / ‖p₁ ζ‖) ξ :=
      (contDiffAt_const.mul (p₂.contDiff.contDiffAt.norm ℝ h₂)).div
        (p₁.contDiff.contDiffAt.norm ℝ h₁) (norm_ne_zero_iff.mpr h₁)
    have heq : g =ᶠ[𝓝 ξ] (fun ζ ↦ 1 - productCutoffProfile (ε * ‖p₂ ζ‖ / ‖p₁ ζ‖)) := by
      filter_upwards [(isOpen_ne.preimage p₁.continuous).mem_nhds h₁] with ζ hζ
      exact ite_eq_right (norm_ne_zero_iff.mpr hζ)
    exact (contDiffAt_const.sub (hp.contDiffAt.comp ξ hr)).congr_of_eventuallyEq heq
  have hformula (ξ : X) : f ξ = 1 - productCutoffProfile (ε * R ξ) * (1 - g ξ) := by
    by_cases h₁ : ‖p₁ ξ‖ = 0
    · simp only [f, productFrequencyCutoff, g, R, h₁, ite_true, sub_zero]
    · simp only [f, productFrequencyCutoff, g, ite_eq_right h₁]
      dsimp only [R]
      ring
  have hfs : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro ξ
    by_cases hξ : p₁ ξ = 0 ∧ p₂ ξ = 0
    · have hrad : ε * R ξ < 1 := by
        change ε * Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2) < 1
        rw [hξ.1, hξ.2, norm_zero, norm_zero]
        norm_num
      have heq : f =ᶠ[𝓝 ξ] (fun _ ↦ 1) := by
        filter_upwards [((hRc.const_mul ε).continuousAt.eventually (gt_mem_nhds hrad))]
          with ζ hζ
        have hz : productCutoffProfile (ε * R ζ) = 0 :=
          hp0 _ (by rw [abs_of_nonneg (mul_nonneg hε.le (hR0 ζ))]; exact hζ.le)
        rw [hformula, hz, zero_mul, sub_zero]
      exact contDiffAt_const.congr_of_eventuallyEq heq
    · have hnonzero : p₁ ξ ≠ 0 ∨ p₂ ξ ≠ 0 := not_and_or.mp hξ
      have hsq : ‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2 ≠ 0 := by
        rcases hnonzero with h₁ | h₂
        · have h := norm_pos_iff.mpr h₁
          positivity
        · have h := norm_pos_iff.mpr h₂
          positivity
      have hRs : ContDiffAt ℝ ∞ R ξ :=
        ((p₁.contDiff.contDiffAt.norm_sq ℝ).add (p₂.contDiff.contDiffAt.norm_sq ℝ)).sqrt hsq
      have heq : f = fun ζ ↦ 1 - productCutoffProfile (ε * R ζ) * (1 - g ζ) := funext hformula
      rw [heq]
      exact contDiffAt_const.sub ((hp.contDiffAt.comp ξ (contDiffAt_const.mul hRs)).mul
        (contDiffAt_const.sub (hgs ξ hnonzero)))
  have hfg (ξ : X) (hrad : 2 ≤ ε * R ξ) : f ξ = g ξ := by
    rw [hformula, hp1 _ hrad]
    ring
  have hghom (ξ : X) (t : ℝ) (ht : 0 < t) : g (t • ξ) = g ξ := by
    have hn (p : X →L[ℝ] X₁) : ‖p (t • ξ)‖ = t * ‖p ξ‖ := by
      rw [p.map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    have hn₂ : ‖p₂ (t • ξ)‖ = t * ‖p₂ ξ‖ := by
      rw [p₂.map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp only [g]
    rw [hn p₁, hn₂]
    by_cases h₁ : ‖p₁ ξ‖ = 0
    · simp [h₁]
    · rw [ite_eq_right (mul_ne_zero ht.ne' h₁), ite_eq_right h₁]
      have hratio : ε * (t * ‖p₂ ξ‖) / (t * ‖p₁ ξ‖) = ε * ‖p₂ ξ‖ / ‖p₁ ξ‖ := by
        field_simp
      rw [hratio]
  let L : ℝ := 1 + ‖split.symm.toContinuousLinearMap‖
  have hL : 0 < L := by dsimp [L]; positivity
  have hjoint (ξ : X) : ‖ξ‖ ≤ L * R ξ := by
    have hs := Real.sq_sqrt (show 0 ≤ ‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2 by positivity)
    have hr := hR0 ξ
    have h₁ : ‖p₁ ξ‖ ≤ R ξ := by dsimp [R] at *; nlinarith [norm_nonneg (p₁ ξ)]
    have h₂ : ‖p₂ ξ‖ ≤ R ξ := by dsimp [R] at *; nlinarith [norm_nonneg (p₂ ξ)]
    have hnorm : ‖split ξ‖ ≤ R ξ := max_le h₁ h₂
    have h := split.symm.toContinuousLinearMap.le_opNorm (split ξ)
    simp only [ContinuousLinearEquiv.coe_coe, split.symm_apply_apply] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr))
  refine ⟨hfs, ?_, fun ξ hrad hcone ↦ (hfg ξ hrad).trans (hg0 ξ hcone)⟩
  intro j
  apply exists_iteratedFDeriv_bound_of_eventually_homogeneous_zero f g hfs hghom (2 * L / ε)
  intro ξ hξ
  apply hfg
  have h := (div_le_iff₀ hε).mp hξ
  have h' := mul_le_mul_of_nonneg_right (hjoint ξ) hε.le
  nlinarith

/-- Positive-parameter regularization restores the joint standard symbol estimates. -/
theorem isSymbol_productCutoffSymbol (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (χ : EuclideanSpace ℝ (Fin m) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (ε : ℝ) (hε : 0 < ε) :
    IsSymbol Set.univ 1 (productCutoffSymbol a χ ε) := by
  let X := EuclideanSpace ℝ (Fin (n + m))
  let X₁ := EuclideanSpace ℝ (Fin n)
  let X₂ := EuclideanSpace ℝ (Fin m)
  let split : X ≃L[ℝ] X₁ × X₂ := EuclideanSpace.finAddEquivProd
  let p₁ : X →L[ℝ] X₁ := (ContinuousLinearMap.fst ℝ X₁ X₂).comp split.toContinuousLinearMap
  let p₂ : X →L[ℝ] X₂ := (ContinuousLinearMap.snd ℝ X₁ X₂).comp split.toContinuousLinearMap
  let R : X → ℝ := fun ξ ↦ Real.sqrt (‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2)
  let τ : X → ℝ := fun ξ ↦ productFrequencyCutoff ε ‖p₁ ξ‖ ‖p₂ ξ‖
  obtain ⟨hτ, hτbound, hτzero⟩ := productFrequencyCutoff_regularity n m ε hε
  -- The coordinate inverse bounds the joint norm by both factor norms and by the radial norm.
  let L : ℝ := 1 + ‖split.symm.toContinuousLinearMap‖
  have hL : 0 < L := by dsimp [L]; positivity
  have hjoint (ξ : X) : ‖ξ‖ ≤ L * (‖p₁ ξ‖ + ‖p₂ ξ‖) := by
    have hnorm : ‖split ξ‖ ≤ ‖p₁ ξ‖ + ‖p₂ ξ‖ :=
      max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have h := split.symm.toContinuousLinearMap.le_opNorm (split ξ)
    simp only [ContinuousLinearEquiv.coe_coe, split.symm_apply_apply] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) (by positivity)))
  have hradial (ξ : X) : ‖ξ‖ ≤ L * R ξ := by
    have hs := Real.sq_sqrt (show 0 ≤ ‖p₁ ξ‖ ^ 2 + ‖p₂ ξ‖ ^ 2 by positivity)
    have hr : 0 ≤ R ξ := Real.sqrt_nonneg _
    have h₁ : ‖p₁ ξ‖ ≤ R ξ := by dsimp [R] at *; nlinarith [norm_nonneg (p₁ ξ)]
    have h₂ : ‖p₂ ξ‖ ≤ R ξ := by dsimp [R] at *; nlinarith [norm_nonneg (p₂ ξ)]
    have hnorm : ‖split ξ‖ ≤ R ξ := max_le h₁ h₂
    have h := split.symm.toContinuousLinearMap.le_opNorm (split ξ)
    simp only [ContinuousLinearEquiv.coe_coe, split.symm_apply_apply] at h
    exact h.trans ((mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_right (by dsimp [L]; linarith) hr))
  let R₀ : ℝ := 2 * L / ε
  let A : ℝ := L * (1 + 2 / ε)
  let B : ℝ := 1 + R₀ + A
  have hR₀ : 0 ≤ R₀ := by dsimp [R₀]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hzero (ξ : X) (hξ : B * (1 + ‖p₁ ξ‖) < 1 + ‖ξ‖) : τ ξ = 0 := by
    -- Outside this fixed cone the radial profile is one and the angular profile is one.
    have hnorm : R₀ < ‖ξ‖ := by
      have hn := mul_nonneg hB (norm_nonneg (p₁ ξ))
      dsimp [B] at *
      nlinarith
    have hrad : 2 ≤ ε * R ξ := by
      have h := (div_lt_iff₀ hε).mp hnorm
      have h' := mul_le_mul_of_nonneg_right (hradial ξ) hε.le
      nlinarith
    apply hτzero ξ hrad
    by_contra hcone
    have hs : ‖p₂ ξ‖ ≤ (2 / ε) * ‖p₁ ξ‖ := by
      apply le_of_lt
      have hc : ‖p₂ ξ‖ * ε < 2 * ‖p₁ ξ‖ := by
        have hc := lt_of_not_ge hcone
        change ε * ‖p₂ ξ‖ < 2 * ‖p₁ ξ‖ at hc
        nlinarith
      have h := (lt_div_iff₀ hε).mpr hc
      convert h using 1
      ring
    have hu : ‖ξ‖ ≤ A * ‖p₁ ξ‖ := by
      apply (hjoint ξ).trans
      calc
        _ ≤ L * (‖p₁ ξ‖ + (2 / ε) * ‖p₁ ξ‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hs) hL.le
        _ = _ := by dsimp [A]; ring
    have hupper : 1 + ‖ξ‖ ≤ B * (1 + ‖p₁ ξ‖) := by
      have hBA : A ≤ B := by dsimp [B]; linarith
      have hB1 : 1 ≤ B := by dsimp [B]; linarith
      nlinarith [mul_le_mul_of_nonneg_right hBA (norm_nonneg (p₁ ξ))]
    exact (not_lt.mpr hupper) hξ
  -- Rescaling on the active cone controls every original mixed derivative, including χ.
  have hsym := isSymbol_linearPullback_of_conicCutoff a ha p₁
    (fun x ↦ χ (p₂ x)) τ (hχ.comp p₂.contDiff) hτ hτbound B hzero
  have heq : productCutoffSymbol a χ ε =
      fun x ξ ↦ (χ (p₂ x) * τ ξ) • a (p₁ x) (p₁ ξ) := by
    funext x ξ
    change (τ ξ : ℂ) • ((χ (p₂ x) : ℂ) • a (p₁ x) (p₁ ξ)) = _
    ext v z
    simp only [smul_apply, PiLp.smul_apply, smul_eq_mul,
      Complex.real_smul, Complex.ofReal_mul]
    ring
  rw [heq]
  exact hsym

/-- The actual error integral has a unique bounded realization in the fixed Bessel coordinates. -/
theorem existsUnique_productCutoffErrorOperator (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) (ε : ℝ) :
    ∃! T : Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))),
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r)),
        ∀ φ : 𝓢(EuclideanSpace ℝ (Fin (n + m)), ℂ),
          besselRealization (n + m) q 0 (T (schwartzSobolevCoordinate 1 u)) φ =
            ∫ x, φ x • quantize (productCutoffErrorSymbol a χ ε) u x := by
  -- Uniform spatial Fourier bounds construct the actual bounded realization for every ε.
  obtain ⟨B, hB, hfreq, _⟩ := productCutoffError_frequency_bounds n m
  obtain ⟨C, _, hC⟩ := exists_productCutoffErrorOperator_bound a ha haK χ hχ hχK
  obtain ⟨T, _, hT⟩ := hC ε B hB (hfreq ε)
  refine ⟨T, hT, ?_⟩
  intro S hS
  -- Equality on the dense Schwartz Bessel coordinates follows from the original tests.
  have htest (u : 𝓢(EuclideanSpace ℝ (Fin (n + m)), EuclideanSpace ℂ (Fin r))) :
      S (schwartzSobolevCoordinate 1 u) = T (schwartzSobolevCoordinate 1 u) := by
    apply besselRealization_injective (n + m) q 0
    ext1 φ
    rw [hS u φ, hT u φ]
  exact DFunLike.ext' ((denseRange_schwartzSobolevCoordinate (n + m) r 1).equalizer
    S.continuous T.continuous (funext htest))

/-- The unique error operator specified by the original Fourier integral on Schwartz inputs. -/
def productCutoffErrorOperator (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) (ε : ℝ) :
    Lp (EuclideanSpace ℂ (Fin r)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) →L[ℂ]
      Lp (EuclideanSpace ℂ (Fin q)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (n + m)))) :=
  Classical.choose (existsUnique_productCutoffErrorOperator a ha haK χ hχ hχK ε).exists

/-- SG's local approximation has a uniform linear error bound and tends to zero in operator norm. -/
theorem productCutoffErrorOperator_approximation (a : SymbolFunction n r q)
    (ha : IsSymbol Set.univ 1 a) (haK : HasCompactSupport a)
    (χ : EuclideanSpace ℝ (Fin m) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχK : HasCompactSupport χ) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖productCutoffErrorOperator a ha haK χ hχ hχK ε‖ ≤ C * ε) ∧
    Tendsto (fun ε : ℝ ↦ productCutoffErrorOperator a ha haK χ hχ hχK ε)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  -- The support of the exact error factor supplies a uniform linear small-parameter bound.
  obtain ⟨B, hB, _, hfreq⟩ := productCutoffError_frequency_bounds n m
  obtain ⟨C, hC, hbound⟩ := exists_productCutoffErrorOperator_bound a ha haK χ hχ hχK
  have hnorm (ε : ℝ) (hε : 0 < ε) :
      ‖productCutoffErrorOperator a ha haK χ hχ hχK ε‖ ≤ (C * B) * ε := by
    obtain ⟨T, hTnorm, hT⟩ := hbound ε (B * ε) (mul_nonneg hB hε.le) (hfreq ε hε)
    -- Uniqueness identifies the Schur realization with the specified operator family.
    have heq : T = productCutoffErrorOperator a ha haK χ hχ hχK ε :=
      (existsUnique_productCutoffErrorOperator a ha haK χ hχ hχK ε).unique hT
        (Classical.choose_spec
          (existsUnique_productCutoffErrorOperator a ha haK χ hχ hχK ε).exists)
    rw [← heq]
    simpa only [mul_assoc] using hTnorm
  refine ⟨⟨C * B, mul_nonneg hC hB, fun ε hε _ ↦ hnorm ε hε⟩, ?_⟩
  -- The positive-sided limit follows in the norm topology of continuous linear maps.
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hmajor : Tendsto (fun ε : ℝ ↦ (C * B) * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ ↦ (C * B) * ε) := continuous_const.mul continuous_id
    simpa only [mul_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ norm_nonneg _)) ?_ hmajor
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hnorm ε hε

end AtiyahSinger
