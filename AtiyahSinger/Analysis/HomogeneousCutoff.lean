/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalQuantization
public import AtiyahSinger.Analysis.SymbolQuotient

/-!
# An explicit cutoff for homogeneous symbols

Public module ID: M0740.

D05/A03: remove the zero-frequency singularity before global quantization.
The cutoff is a specified mathlib bump complement. SG III.13 (13.5) uses
homogeneous data at infinity; no full polyhomogeneous expansion is required.
Only positive real dilations and smoothness off zero are assumed. The cutoff, its exact
support conventions and all compact-local mixed derivative estimates are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff Topology

open Set Function

set_option maxSynthPendingDepth 20

variable {n r q : ℕ}

/-- The complement of a fixed smooth bump, zero on the half-ball and one outside the unit ball. -/
def highFrequencyCutoff (n : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) : ℝ :=
  1 - (⟨1 / 2, 1, by norm_num, by norm_num⟩ :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) ξ

/-- The frequency cutoff is smooth even at the origin. -/
theorem contDiff_highFrequencyCutoff : ContDiff ℝ ∞ (highFrequencyCutoff n) := by
  -- The chosen bump is globally smooth, so its complement is smooth at zero as well.
  exact contDiff_const.sub (ContDiffBump.contDiff _)

/-- The cutoff vanishes on a whole neighborhood of the zero frequency. -/
theorem highFrequencyCutoff_eq_zero (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ ≤ 1 / 2) :
    highFrequencyCutoff n ξ = 0 := by
  -- The bump equals one throughout the fixed inner closed ball.
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨1 / 2, 1, by norm_num, by norm_num⟩
  change 1 - φ ξ = 0
  rw [φ.one_of_mem_closedBall (by simpa [φ] using hξ)]
  exact sub_self 1

/-- At and beyond unit frequency the cutoff is exactly one. -/
theorem highFrequencyCutoff_eq_one (ξ : EuclideanSpace ℝ (Fin n)) (hξ : 1 ≤ ‖ξ‖) :
    highFrequencyCutoff n ξ = 1 := by
  -- At the outer radius and beyond, the prescribed bump vanishes.
  let φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    ⟨1 / 2, 1, by norm_num, by norm_num⟩
  change 1 - φ ξ = 1
  rw [φ.zero_of_le_dist (by simpa [φ] using hξ)]
  exact sub_zero 1

/-- The actual frequency-cutoff formula, with the value at zero automatically suppressed. -/
def frequencyCutoffSymbol (a : SymbolFunction n r q) : SymbolFunction n r q :=
  fun x ξ ↦ (highFrequencyCutoff n ξ : ℂ) • a x ξ

/-- Away from the unit ball the regularization agrees exactly with the supplied data. -/
theorem frequencyCutoffSymbol_eq_of_one_le_norm (a : SymbolFunction n r q)
    (x ξ : EuclideanSpace ℝ (Fin n)) (hξ : 1 ≤ ‖ξ‖) :
    frequencyCutoffSymbol a x ξ = a x ξ := by
  -- Use the same specified cutoff, without any assumption on the original data.
  simp only [frequencyCutoffSymbol, highFrequencyCutoff_eq_one ξ hξ, Complex.ofReal_one,
    one_smul]

/-- The regularization does not use the arbitrary values of the data near zero. -/
theorem frequencyCutoffSymbol_eq_zero_of_norm_le (a : SymbolFunction n r q)
    (x ξ : EuclideanSpace ℝ (Fin n)) (hξ : ‖ξ‖ ≤ 1 / 2) :
    frequencyCutoffSymbol a x ξ = 0 := by
  -- Multiplication by the zero cutoff suppresses even arbitrary original values.
  simp only [frequencyCutoffSymbol, highFrequencyCutoff_eq_zero ξ hξ, Complex.ofReal_zero,
    zero_smul]

/-- The explicit cutoff realizes smooth punctured homogeneous data as a genuine symbol. -/
theorem isSymbol_frequencyCutoffSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (hU : IsOpen U) (m : ℝ) (a : SymbolFunction n r q)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ {ξ | ξ ≠ 0}))
    (hhom : IsHomogeneousSymbol U m a) : IsSymbol U m (frequencyCutoffSymbol a) := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let b := frequencyCutoffSymbol a
  -- Smoothness is patched from the zero neighborhood and the punctured-frequency formula.
  have hcut : ContDiff ℝ ∞ (fun p : V × V ↦ (highFrequencyCutoff n p.2 : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_highFrequencyCutoff.comp contDiff_snd)
  have hsm : ContDiffOn ℝ ∞ (Function.uncurry b) (U ×ˢ Set.univ) := by
    intro p hp
    by_cases hξ : p.2 = 0
    · have heq : Function.uncurry b =ᶠ[𝓝 p] (fun _ ↦ 0) := by
        have hsmall : ‖p.2‖ < (1 / 2 : ℝ) := by simp [hξ]
        filter_upwards [continuous_snd.norm.continuousAt.eventually (gt_mem_nhds hsmall)]
          with z hz
        exact frequencyCutoffSymbol_eq_zero_of_norm_le a z.1 z.2 hz.le
      exact (contDiffAt_const.congr_of_eventuallyEq heq).contDiffWithinAt
    · have ha := hsmooth.contDiffAt
        ((hU.prod (isOpen_ne : IsOpen {ξ : V | ξ ≠ 0})).mem_nhds ⟨hp.1, hξ⟩)
      exact (hcut.contDiffAt.smul ha).contDiffWithinAt
  refine ⟨hsm, ?_⟩
  -- Full derivatives commute with invertible linear dilations, including totalized derivatives.
  have deriv_comp_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
      iteratedFDeriv ℝ j (fun ζ ↦ f (t • ζ)) ξ =
        t ^ j • iteratedFDeriv ℝ j f (t • ξ) := by
    let e : V ≃L[ℝ] V := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
    have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := ξ) (mem_univ _) j
    simp only [preimage_univ, iteratedFDerivWithin_univ] at h
    change iteratedFDeriv ℝ j (f ∘ e) ξ = _
    rw [h]
    ext v
    change (iteratedFDeriv ℝ j f (t • ξ)) (fun i ↦ t • v i) = _
    rw [ContinuousMultilinearMap.map_smul_univ]
    simp
  have deriv_smul {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] (t : ℝ) (ht : t ≠ 0) (f : V → W) (j : ℕ) (ξ : V) :
      iteratedFDeriv ℝ j (fun ζ ↦ t • f ζ) ξ = t • iteratedFDeriv ℝ j f ξ := by
    let e : W ≃L[ℝ] W := ContinuousLinearEquiv.smulLeft (Units.mk0 t ht)
    have h := e.iteratedFDeriv_comp_left (f := f) (x := ξ) (i := j)
    change iteratedFDeriv ℝ j (e ∘ f) ξ = _
    rw [h]
    rfl
  -- Differentiate homogeneity first in frequency and then on the original open base domain.
  have hscale (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) (hξ : ξ ≠ 0) (t : ℝ) (ht : 0 < t) :
      symbolDerivative a i j x (t • ξ) = t ^ (m - (j : ℝ)) • symbolDerivative a i j x ξ := by
    have hfreq (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ U) :
        iteratedFDeriv ℝ j (a y) (t • ξ) =
          t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (a y) ξ := by
      have heq : (fun ζ ↦ a y (t • ζ)) =ᶠ[𝓝 ξ] (fun ζ ↦ (t ^ m) • a y ζ) := by
        filter_upwards [(isOpen_ne : IsOpen {ζ : EuclideanSpace ℝ (Fin n) | ζ ≠ 0}).mem_nhds hξ]
          with ζ hζ
        exact hhom y hy ζ hζ t ht
      have hd := (heq.iteratedFDeriv ℝ j).eq_of_nhds
      rw [deriv_comp_smul t ht.ne', deriv_smul (t ^ m) (Real.rpow_pos_of_pos ht m).ne'] at hd
      calc
        _ = (t ^ j)⁻¹ • (t ^ j • iteratedFDeriv ℝ j (a y) (t • ξ)) := by
          rw [inv_smul_smul₀ (pow_ne_zero _ ht.ne')]
        _ = ((t ^ j)⁻¹ * t ^ m) • iteratedFDeriv ℝ j (a y) ξ := by rw [hd, smul_smul]
        _ = _ := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
          congr 2
          ring
    have heq : (fun y ↦ iteratedFDeriv ℝ j (a y) (t • ξ)) =ᶠ[𝓝 x]
        (fun y ↦ t ^ (m - (j : ℝ)) • iteratedFDeriv ℝ j (a y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfreq y hy
    have hd := (heq.iteratedFDeriv ℝ i).eq_of_nhds
    rw [deriv_smul _ (Real.rpow_pos_of_pos ht _).ne'] at hd
    exact hd
  have hparametric {P Q R : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
      [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup R] [NormedSpace ℝ R]
      (f : P → Q → R) (x : P) (y : Q)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, y)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × Q ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, y) := by
    -- Parameter differentiation remains smooth; each step differentiates and uncurries once.
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ Q R).symm : _ →L[ℝ] Q [×0]→L[ℝ] R)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × Q ↦ fun z : Q ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, y), y) := ih.comp ((x, y), y) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × Q ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, y) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ Q) R).symm :
          _ →L[ℝ] Q [×(j + 1)]→L[ℝ] R)
  have hmixed (f : SymbolFunction n r q) (p : V × V)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) p) (i j : ℕ) :
      ContDiffAt ℝ ∞ (fun z : V × V ↦ symbolDerivative f i j z.1 z.2) p := by
    have hξ := hparametric f p.1 p.2 hf j
    have hswap : ContDiffAt ℝ ∞
        (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ j (f x) ξ)) (p.2, p.1) :=
      hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
    exact (hparametric _ p.2 p.1 hswap i).comp p
      (contDiffAt_snd.prodMk contDiffAt_fst)
  -- Comparing homogeneous and inhomogeneous weights must also cover negative symbol orders.
  have hweight (k t : ℝ) (ht : 1 ≤ t) :
      t ^ k ≤ (2 : ℝ) ^ |k| * (1 + t) ^ k := by
    have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
    by_cases hk : 0 ≤ k
    · have htwo : (1 : ℝ) ≤ 2 ^ |k| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
      calc
        t ^ k ≤ (1 + t) ^ k := Real.rpow_le_rpow htpos.le (by linarith) hk
        _ ≤ 2 ^ |k| * (1 + t) ^ k := le_mul_of_one_le_left (by positivity) htwo
    · have hk' : k ≤ 0 := (lt_of_not_ge hk).le
      have hcomp : (2 * t) ^ k ≤ (1 + t) ^ k :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hk'
      calc
        t ^ k = 2 ^ |k| * (2 * t) ^ k := by
          rw [Real.mul_rpow (by norm_num) htpos.le, abs_of_nonpos hk', ← mul_assoc,
            ← Real.rpow_add (by norm_num), neg_add_cancel, Real.rpow_zero, one_mul]
        _ ≤ 2 ^ |k| * (1 + t) ^ k := mul_le_mul_of_nonneg_left hcomp (by positivity)
  intro K hKU hK i j
  let k := m - (j : ℝ)
  -- Compactness controls the smooth cutoff on the full low-frequency ball.
  have hlowcont : ContinuousOn
      (fun p : V × V ↦ ‖symbolDerivative b i j p.1 p.2‖ / (1 + ‖p.2‖) ^ k)
      (K ×ˢ Metric.closedBall 0 2) := by
    intro p hp
    have hf := hsm.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hKU hp.1, mem_univ _⟩)
    have hnorm := (hmixed b p hf i j).continuousAt.norm
    have hbase : Continuous (fun p : V × V ↦ (1 : ℝ) + ‖p.2‖) :=
      continuous_const.add continuous_snd.norm
    have hw : ContinuousAt (fun p : V × V ↦ (1 + ‖p.2‖) ^ k) p :=
      hbase.continuousAt.rpow_const
        (Or.inl (ne_of_gt (by positivity)))
    exact (hnorm.div hw (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _))).continuousWithinAt
  obtain ⟨C₀, hC₀⟩ := ((hK.prod (isCompact_closedBall (0 : V) 2)).image_of_continuousOn
    hlowcont).bddAbove
  -- On the unit sphere all mixed derivatives of the original data are uniformly bounded.
  have hsphere : ContinuousOn (fun p : V × V ↦ ‖symbolDerivative a i j p.1 p.2‖)
      (K ×ˢ Metric.sphere 0 1) := by
    intro p hp
    have hnorm : ‖p.2‖ = 1 := by simpa using hp.2
    have hne : p.2 ≠ 0 := by intro hz; simp [hz] at hnorm
    have hf := hsmooth.contDiffAt
      ((hU.prod (isOpen_ne : IsOpen {ξ : V | ξ ≠ 0})).mem_nhds ⟨hKU hp.1, hne⟩)
    exact (hmixed a p hf i j).continuousAt.norm.continuousWithinAt
  obtain ⟨C₁, hC₁⟩ := ((hK.prod (isCompact_sphere (0 : V) 1)).image_of_continuousOn
    hsphere).bddAbove
  let D := max C₁ 0
  refine ⟨max C₀ 0 + D * 2 ^ |k|, by dsimp only [D]; positivity, ?_⟩
  intro x hx ξ
  by_cases hlow : ‖ξ‖ ≤ 2
  · have hmem : ξ ∈ Metric.closedBall (0 : V) 2 := by simpa using hlow
    have hbound := hC₀ ⟨(x, ξ), ⟨hx, hmem⟩, rfl⟩
    have hC : C₀ ≤ max C₀ 0 + D * 2 ^ |k| := by
      have hnonneg : 0 ≤ D * 2 ^ |k| := by dsimp only [D]; positivity
      linarith [le_max_left C₀ 0]
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mp (hbound.trans hC)
  · have hlarge : 2 < ‖ξ‖ := lt_of_not_ge hlow
    have hξpos : 0 < ‖ξ‖ := lt_trans (by norm_num) hlarge
    let η := ‖ξ‖⁻¹ • ξ
    have hηnorm : ‖η‖ = 1 := by
      simp only [η, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg _)]
      exact inv_mul_cancel₀ hξpos.ne'
    have hηne : η ≠ 0 := by intro hz; simp [hz] at hηnorm
    have hreconstruct : ‖ξ‖ • η = ξ := smul_inv_smul₀ hξpos.ne' ξ
    -- Away from the cutoff transition, equality on a neighborhood identifies full derivatives.
    have hder : symbolDerivative b i j x ξ = symbolDerivative a i j x ξ := by
      have heq (y : V) : b y =ᶠ[𝓝 ξ] a y := by
        filter_upwards [continuous_norm.continuousAt.eventually
          (lt_mem_nhds (show (1 : ℝ) < ‖ξ‖ by linarith))] with ζ hζ
        exact frequencyCutoffSymbol_eq_of_one_le_norm a y ζ hζ.le
      have hfunctions : (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) =
          (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) :=
        funext (fun y ↦ ((heq y).iteratedFDeriv ℝ j).eq_of_nhds)
      unfold symbolDerivative
      rw [hfunctions]
    have hbound : ‖symbolDerivative a i j x η‖ ≤ D := by
      apply (hC₁ ⟨(x, η), ⟨hx, ?_⟩, rfl⟩).trans (le_max_left C₁ 0)
      simpa using hηnorm
    have hnorm : ‖symbolDerivative b i j x ξ‖ =
        ‖ξ‖ ^ k * ‖symbolDerivative a i j x η‖ := by
      rw [hder]
      conv_lhs => rw [← hreconstruct, hscale i j x (hKU hx) η hηne ‖ξ‖ hξpos]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hξpos _)]
    calc
      _ = ‖ξ‖ ^ k * ‖symbolDerivative a i j x η‖ := hnorm
      _ ≤ ‖ξ‖ ^ k * D := mul_le_mul_of_nonneg_left hbound (by positivity)
      _ ≤ (2 ^ |k| * (1 + ‖ξ‖) ^ k) * D :=
        mul_le_mul_of_nonneg_right (hweight k ‖ξ‖ (by linarith)) (le_max_right C₁ 0)
      _ ≤ (max C₀ 0 + D * 2 ^ |k|) * (1 + ‖ξ‖) ^ k := by
        have hnonneg : 0 ≤ max C₀ 0 * (1 + ‖ξ‖) ^ k := by positivity
        nlinarith

end AtiyahSinger
