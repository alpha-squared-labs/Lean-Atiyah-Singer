/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactJetIntegral
public import AtiyahSinger.Analysis.Quantization
public import AtiyahSinger.Analysis.SymbolQuotient

/-!
# Integration of uniform symbol families

Public module ID: M0362.

A finite measure on a compact parameter preserves the original symbol order
when the spatial jets are jointly continuous and each weighted mixed derivative
has one bound valid for the whole parameter set. The integral is taken in the
original finite-dimensional matrix space. Its mixed derivatives are the actual
integrals of the original mixed derivatives.

Joint jets of the uncurried symbols and of their mixed derivatives are explicit
regularity hypotheses. Uniform estimates are separate: pointwise membership in
the symbol class does not supply a parameter-independent seminorm bound.
These are the local analytic inputs required by compact-group PDO averaging.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ContDiff Manifold Topology

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y) [IsFiniteMeasure μ]
  {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
  {m : ℝ} (a : Y → SymbolFunction n r q)
  (ha : ∀ y, IsSymbol U m (a y))
  (hmixed : ∀ i j : ℕ, ContinuousOn
    (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
      symbolDerivative (a p.1) i j p.2.1 p.2.2) (univ ×ˢ (U ×ˢ univ)))

include hU ha hmixed

/-- Every mixed derivative commutes with integration of a compact continuous jet family. -/
theorem symbolDerivative_integral_of_continuous_jets (i j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) (ξ : EuclideanSpace ℝ (Fin n)) :
    symbolDerivative (fun x ξ ↦ ∫ y, a y x ξ ∂μ) i j x ξ =
      ∫ y, symbolDerivative (a y) i j x ξ ∂μ := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  have hpartial (y : Y) (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : X × X ↦ iteratedFDeriv ℝ k (a y z.1) z.2) (U ×ˢ univ) := by
    intro z hz
    have hs : ContDiffAt ℝ ∞ (Function.uncurry (a y)) z :=
      (ha y).1.contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)
    have hj : ContDiffAt ℝ ∞
        (fun z : X × X ↦ iteratedFDeriv ℝ k (a y z.1) z.2) z := by
      -- Ordinary parameter differentiation avoids changing the native product charted space.
      induction k with
      | zero =>
        exact hs.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ X V).symm : _ →L[ℝ] X [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun p : X × X ↦ fun η : X ↦
              iteratedFDeriv ℝ k (a y p.1) η)) (z, z.2) :=
          ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun p : X × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (a y p.1)) p.2) z :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) V).symm :
            _ →L[ℝ] X [×(k + 1)]→L[ℝ] V)
    exact hj.contDiffWithinAt
  -- First commute all frequency derivatives at each fixed base point.
  have hfrequency (z : X) (hz : z ∈ U) :
      iteratedFDeriv ℝ j (fun η ↦ ∫ y, a y z η ∂μ) ξ =
        ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ := by
    apply iteratedFDeriv_integral_of_continuous_jets μ isOpen_univ
      (fun y ↦ (ha y).1.comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun η _ ↦ ⟨hz, mem_univ η⟩))
    · intro k
      let C := continuousMultilinearCurryFin0 ℝ X (X [×k]→L[ℝ] V)
      have hc : ContinuousOn (fun p : Y × X ↦ C (symbolDerivative (a p.1) 0 k z p.2))
          (univ ×ˢ univ) := C.continuous.comp_continuousOn ((hmixed 0 k).comp
        (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
          (fun p _ ↦ ⟨mem_univ p.1, hz, mem_univ p.2⟩))
      change ContinuousOn
        (fun p : Y × X ↦ (iteratedFDeriv ℝ 0
          (fun z ↦ iteratedFDeriv ℝ k (a p.1 z) p.2) z).curry0) (univ ×ˢ univ) at hc
      simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply,
        Function.comp_def, Function.uncurry, id_eq] using hc
    · exact mem_univ ξ
  -- The frequency-derivative family is smooth in the base and has continuous base jets.
  have hbase :
      iteratedFDeriv ℝ i (fun z ↦ ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ) x =
        ∫ y, iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (a y z) ξ) x ∂μ := by
    apply iteratedFDeriv_integral_of_continuous_jets μ hU
      (fun y ↦ (hpartial y j).comp (contDiffOn_id.prodMk contDiffOn_const)
        (fun z hz ↦ ⟨hz, mem_univ ξ⟩))
    · intro k
      exact (hmixed k j).comp
        (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
          (fun p hp ↦ ⟨mem_univ p.1, hp.2, mem_univ ξ⟩)
    · exact hx
  -- The inner equality holds on the open base neighborhood, so ambient derivatives agree.
  have hnear : (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ ∫ y, a y z η ∂μ) ξ) =ᶠ[𝓝 x]
      (fun z ↦ ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hfrequency
  exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans hbase

/-- A compact finite-measure integral preserves the order of a uniform symbol family. -/
theorem isSymbol_integral_of_continuous_jets
    (hjoint : ∀ k : ℕ, ContinuousOn
      (fun p : Y × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
        iteratedFDeriv ℝ k (Function.uncurry (a p.1)) p.2) (univ ×ˢ (U ×ˢ univ)))
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Y, ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative (a y) i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ))) :
    IsSymbol U m (fun x ξ ↦ ∫ y, a y x ξ ∂μ) := by
  constructor
  · -- Joint smoothness follows from the integrated Taylor series on the original open domain.
    exact contDiffOn_integral_of_continuous_jets μ (hU.prod isOpen_univ)
      (fun y ↦ (ha y).1) hjoint
  · intro K hKU hK i j
    obtain ⟨C, hC, hbound⟩ := hbound K hKU hK i j
    refine ⟨μ.real univ * C, mul_nonneg measureReal_nonneg hC, ?_⟩
    intro x hx ξ
    rw [symbolDerivative_integral_of_continuous_jets μ hU a ha hmixed i j (hKU hx) ξ]
    have hc : Continuous (fun y ↦ symbolDerivative (a y) i j x ξ) := by
      apply continuousOn_univ.mp
      exact (hmixed i j).comp
        (continuous_id.prodMk (continuous_const (y := (x, ξ)))).continuousOn
        (fun y _ ↦ ⟨mem_univ y, hKU hx, mem_univ ξ⟩)
    have hi := hc.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ ∫ y, ‖symbolDerivative (a y) i j x ξ‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ _ : Y, C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) ∂μ :=
        integral_mono_ae hi.norm (integrable_const _)
          (Filter.Eventually.of_forall (fun y ↦ hbound y x hx ξ))
      _ = (C * (1 + ‖ξ‖) ^ (m - (j : ℝ))) * μ.real univ := by
        rw [integral_const, smul_eq_mul, mul_comm]
      _ = _ := by ring

omit hU ha hmixed in
/-- Quantization commutes with a compact parameter integral having a uniform polynomial bound. -/
theorem quantize_integral_of_uniform_bound
    (u : SchwartzMap (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n))
    (hc : Continuous (fun p : Y × EuclideanSpace ℝ (Fin n) ↦ a p.1 x p.2))
    (hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y ξ,
      ‖a y x ξ‖ ≤ C * (1 + ‖ξ‖) ^ m) :
    quantize (fun z ξ ↦ ∫ y, a y z ξ ∂μ) u x = ∫ y, quantize (a y) u x ∂μ := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin q)
  let c : ℝ := 2 * Real.pi
  let v := FourierTransform.fourier u
  let w (η : X) : ℝ := (1 + ‖c • η‖) ^ m
  obtain ⟨C, hC, hbound⟩ := hbound
  -- A fixed smooth polynomial weight dominates the original real-order frequency weight.
  have hweight : Integrable (fun η ↦ w η * ‖v η‖) := by
    let k : ℕ := ⌈m⌉₊
    let b (η : X) : ℝ := (1 + ‖c • η‖ ^ 2) ^ k
    have hb : b.HasTemperateGrowth := by
      have hn : (fun η : X ↦ ‖c • η‖ ^ 2).HasTemperateGrowth :=
        (Function.hasTemperateGrowth_norm_sq X).comp (by fun_prop)
      dsimp [b]
      fun_prop
    have hb0 (η : X) : 0 ≤ b η := by dsimp [b]; positivity
    have hi : Integrable (fun η ↦ b η * ‖v η‖) := by
      simpa only [SchwartzMap.smulLeftCLM_apply_apply hb, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (hb0 _)] using
          (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) b v).integrable.norm
    apply (hi.const_mul (2 ^ k)).mono'
    · exact ((Continuous.rpow_const (by fun_prop) (fun η ↦ Or.inl (by positivity))).mul
        v.continuous.norm).aestronglyMeasurable
    · filter_upwards [] with η
      rw [Real.norm_eq_abs, abs_of_nonneg (by dsimp [w]; positivity)]
      calc
        w η * ‖v η‖ ≤ (1 + ‖c • η‖) ^ k * ‖v η‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact (Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg (c • η)])
            (Nat.le_ceil m)).trans_eq (Real.rpow_natCast _ _)
        _ ≤ (2 * (1 + ‖c • η‖ ^ 2)) ^ k * ‖v η‖ := by
          gcongr
          nlinarith [sq_nonneg (‖c • η‖ - 1)]
        _ = 2 ^ k * (b η * ‖v η‖) := by simp only [b, mul_pow]; ring
  let phase (η : X) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ))
  have hphase (η : X) : ‖phase η‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  let H (y : Y) (η : X) : V := phase η • a y x (c • η) (v η)
  have hHc : Continuous (Function.uncurry H) := by
    have ha := hc.comp (continuous_fst.prodMk (continuous_snd.const_smul c))
    have hp : Continuous (fun p : Y × X ↦ phase p.2) := by
      dsimp [phase]
      fun_prop
    exact hp.smul (ha.clm_apply (v.continuous.comp continuous_snd))
  have hHbound (y : Y) (η : X) : ‖H y η‖ ≤ C * (w η * ‖v η‖) := by
    dsimp only [H]
    rw [norm_smul, hphase, one_mul, ← mul_assoc]
    exact ((a y x (c • η)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hbound y (c • η)) (norm_nonneg _))
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    apply ((integrable_const (1 : ℝ) : Integrable (fun _ : Y ↦ (1 : ℝ)) μ).mul_prod
      (hweight.const_mul C)).mono'
    · exact hHc.aestronglyMeasurable
    · filter_upwards [] with p
      simpa only [one_mul, Function.uncurry] using hHbound p.1 p.2
  -- Absolute product integrability justifies exchanging the parameter and Fourier variables.
  rw [quantize_rescaled]
  calc
    _ = ∫ η, ∫ y, H y η ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with η
      have hi : Integrable (fun y ↦ a y x (c • η)) μ :=
        (hc.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      let T : (EuclideanSpace ℂ (Fin r) →L[ℂ] V) →L[ℂ] V :=
        phase η • ContinuousLinearMap.apply ℂ V (v η)
      change T (∫ y, a y x (c • η) ∂μ) = ∫ y, T (a y x (c • η)) ∂μ
      exact (T.integral_comp_comm hi).symm
    _ = ∫ y, (∫ η, H y η) ∂μ := (integral_integral_swap hHi).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      exact (quantize_rescaled (a y) u x).symm

end AtiyahSinger
