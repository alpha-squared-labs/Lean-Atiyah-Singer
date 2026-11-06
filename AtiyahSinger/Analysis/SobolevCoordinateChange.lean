/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BesselSymbol
public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.Pseudolocal

import AtiyahSinger.Analysis.CompactQuantization
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Sobolev bounds for compact coordinate pullback

Public module ID: M0991.

Compactly supported pullback by an actual smooth coordinate equivalence is bounded
at every real Sobolev order. Transport the positive Bessel quadratic form through
the compact coordinate symbol calculus, retaining the absolute inverse
Jacobian. Opposite Sobolev weights then bound this same quadratic form. This is the
coordinate estimate used in SG III.2.14; no global Sobolev duality or reverse smooth
kernel characterization is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff Manifold SchwartzMap

/-- Smooth compact coordinate pullback preserves every real Sobolev order. -/
theorem exists_norm_cutoffPullback_sobolev_le {n r : ℕ}
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (he : ContDiffOn ℝ ∞ e e.source) (hψ : ContDiffOn ℝ ∞ e.symm e.target)
    (χ : EuclideanSpace ℝ (Fin n) → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ e.source) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
        ‖schwartzSobolevCoordinate s
          (cutoffPullbackCLM e.source e.open_source e he χ hχ hcχ hχU u)‖ ≤
            C * ‖schwartzSobolevCoordinate s u‖ := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  -- Choose all spatial controls before the input; the same controls enter both sides.
  have plateau (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
      ∃ δ : X → ℝ, ContDiff ℝ ∞ δ ∧ HasCompactSupport δ ∧
        tsupport δ ⊆ U ∧ K ⊆ interior {x | δ x = 1} := by
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
      exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
      exists_open_between_and_isCompact_closure hOc hU hOU
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
    have hδsupport : tsupport δ = closure O' := congrArg closure hsδ
    refine ⟨δ, hδ, by simpa [HasCompactSupport, hδsupport] using hO'c,
      by rwa [hδsupport], ?_⟩
    intro x hx
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hx⟩
    intro y hy
    exact (honeδ y).mp (subset_closure hy)
  obtain ⟨δ, hδ, hcδ, hδU, hδone⟩ := plateau (tsupport χ) e.source hcχ e.open_source hχU
  have hcimage : IsCompact (e '' tsupport χ) :=
    hcχ.image_of_continuousOn (e.continuousOn.mono hχU)
  have himage : e '' tsupport χ ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hχU hx)
  obtain ⟨ρ, hρ, hcρ, hρV, hρone⟩ :=
    plateau (e '' tsupport χ) e.target hcimage e.open_target himage
  -- Extend the actual inverse Jacobian smoothly across the target chart boundary.
  have jacobian_extension (C : Set X) (hC : IsCompact C) (hCV : C ⊆ e.target) :
      ∃ η : X → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧ tsupport η ⊆ e.target ∧
        ∀ y ∈ C, η y = |(fderiv ℝ e.symm y).det| := by
    classical
    let X := EuclideanSpace ℝ (Fin n)
    -- A smooth cutoff separates the compact set from the boundary of the target chart.
    obtain ⟨O, hOo, hCO, hOV, hOc⟩ :=
      exists_open_between_and_isCompact_closure hC e.open_target hCV
    obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hC.isClosed hCO
    have hχsupport : tsupport χ = closure O := congrArg closure hsχ
    have hcχ : HasCompactSupport χ := by
      simpa only [HasCompactSupport, hχsupport] using hOc
    have hχV : tsupport χ ⊆ e.target := by
      rwa [hχsupport]
    -- The derivative of the actual inverse has nonzero determinant throughout its target.
    -- Hence the absolute determinant is smooth without choosing an orientation sign.
    have hdet (y : X) (hy : y ∈ e.target) :
        ContDiffAt ℝ ∞ (fun w ↦ |(fderiv ℝ e.symm w).det|) y := by
      have hψAt := hψ.contDiffAt (e.open_target.mem_nhds hy)
      have hD := hψAt.fderiv_right (m := ∞) (by simp)
      have hs : ContDiffAt ℝ ∞ (fun w ↦ (fderiv ℝ e.symm w).det) y := by
        let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        simp only [ContinuousLinearMap.det, ← LinearMap.det_toMatrix b, Matrix.det_apply']
        apply ContDiffAt.sum
        intro σ hσ
        apply ContDiffAt.mul contDiffAt_const
        apply contDiffAt_prod
        intro i hi
        simp only [LinearMap.toMatrix_apply]
        exact (b.coord (σ i)).toContinuousLinearMap.contDiff.contDiffAt.comp y
          (hD.clm_apply contDiffAt_const)
      apply hs.abs
      have hforward := (he.contDiffAt
        (e.open_source.mem_nhds (e.map_target hy))).differentiableAt (by simp)
      have hright : (fderiv ℝ e (e.symm y)).comp (fderiv ℝ e.symm y) =
          ContinuousLinearMap.id ℝ X := by
        apply (hforward.hasFDerivAt.comp y
          (hψAt.differentiableAt (by simp)).hasFDerivAt).unique
        apply (hasFDerivAt_id y).congr_of_eventuallyEq
        filter_upwards [e.open_target.mem_nhds hy] with z hz
        exact e.right_inv hz
      have hd := congrArg ContinuousLinearMap.det hright
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
        LinearMap.det_comp, ContinuousLinearMap.coe_id, LinearMap.det_id] at hd
      exact right_ne_zero_of_mul_eq_one hd
    -- Multiply inside the chart and extend by zero; its support stays inside the cutoff support.
    let η : X → ℝ := fun y ↦ if y ∈ e.target then χ y * |(fderiv ℝ e.symm y).det| else 0
    have hsupp : Function.support η ⊆ tsupport χ := by
      intro y hy
      by_contra hyχ
      have hz : χ y = 0 :=
        Function.notMem_support.mp (fun h ↦ hyχ (subset_tsupport _ h))
      exact hy (by simp only [η, hz, zero_mul, ite_self])
    have hts : tsupport η ⊆ tsupport χ := closure_minimal hsupp (isClosed_tsupport χ)
    have hη : ContDiff ℝ ∞ η := by
      rw [contDiff_iff_contDiffAt]
      intro y
      by_cases hy : y ∈ tsupport χ
      · apply (hχ.contDiffAt.mul (hdet y (hχV hy))).congr_of_eventuallyEq
        filter_upwards [e.open_target.mem_nhds (hχV hy)] with z hz
        exact ite_eq_left hz
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hy] with z hz
        exact Function.notMem_support.mp (fun h ↦ hz (hsupp h))
    refine ⟨η, hη, hcχ.of_isClosed_subset (isClosed_tsupport η) hts, hts.trans hχV, ?_⟩
    intro y hy
    simp only [η, ite_eq_left (hCV hy), (honeχ y).mp hy, one_mul]
  obtain ⟨η, hη, hcη, hηV, hηeq⟩ := jacobian_extension (tsupport ρ) hcρ hρV
  have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hηgrowth : (fun x ↦ (η x : ℂ)).HasTemperateGrowth :=
    (hcη.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hη)
  let T := cutoffPullbackCLM (r := r) e.source e.open_source e he χ hχ hcχ hχU
  let S := SchwartzMap.smulLeftCLM V (fun x ↦ (χ x : ℂ))
  let J := SchwartzMap.fourierMultiplierCLM V
    (fun ξ : X ↦ (1 + ‖ξ‖ ^ 2) ^ ((2 * s) / 2))
  let p := besselSymbol n r (2 * s)
  have hp : IsSymbol Set.univ (2 * s) p := isSymbol_besselSymbol n r (2 * s)
  let a := cutoffAmplitude χ χ p
  have ha : IsAmplitude (2 * s) a := isAmplitude_cutoffAmplitude _ _ hp χ χ hχ hχ
  have hca : HasCompactSupport (Function.uncurry a) :=
    hasCompactSupport_cutoffAmplitude p χ χ hcχ hcχ
  let P := amplitudeOperator (2 * s) a ha hca
  have hPapply (u : 𝓢(X, V)) (x : X) : P u x = χ x • J (S u) x := by
    rw [amplitudeOperator_apply, amplitudeApply_cutoffAmplitude _ _ hp χ χ hχ hχ hcχ hcχ]
    exact congrArg (fun v : V ↦ χ x • v) (quantize_besselSymbol n r (2 * s) (S u) x)
  have hP : ∀ u x, P u x = quantize (cutoffSymbol χ χ p) u x := by
    intro u x
    exact (amplitudeOperator_apply _ a ha hca u x).trans
      (congrFun (quantize_amplitudeSymbol _ a ha hca u) x).symm
  have hp' := isSymbol_cutoffSymbol (2 * s) p hp χ χ hχ hχ hcχ hcχ
  have hPK : HasOperatorSupport (tsupport χ) P := by
    simpa only [Set.union_self] using hasOperatorSupport_cutoff (2 * s) p hp
      χ χ hχ hχ hcχ hcχ
  -- The exact compact conjugate has a compact symbol of order 2s, including its remainder.
  obtain ⟨a', b, ha', hca', hb, hcb, hact, _⟩ :=
    exists_coordinatePushforward_amplitude e he hψ δ ρ hδ hcδ hδU hρ hcρ hρV
      (2 * s) (cutoffSymbol χ χ p) hp' P hP (tsupport χ) hcχ hχU hPK hδone hρone
  let q := amplitudeSymbol a' + b
  have hqa := isSymbol_amplitudeSymbol (2 * s) a' ha' hca'
  have hcqa := hasCompactSupport_amplitudeSymbol a' hca'
  have hq : IsSymbol Set.univ (2 * s) q := hqa.add isOpen_univ (hb (2 * s))
  have hcq : HasCompactSupport q := hcqa.add hcb
  let Q := coordinatePushforward e he hψ δ ρ hδ hcδ hδU hρ hcρ hρV P
  have hQ (u : 𝓢(X, V)) (x : X) : Q u x = quantize q u x := by
    have hsum := congrArg (fun A ↦ A u x)
      (quantizeSchwartz_add (2 * s) (amplitudeSymbol a') b hqa (hb (2 * s))
        hcqa hcb hq hcq)
    simp only [add_apply, quantizeSchwartz_apply] at hsum
    rw [quantize_amplitudeSymbol (2 * s) a' ha' hca' u] at hsum
    exact (hact u x).trans hsum.symm
  have hinput (u : 𝓢(X, V)) :
      S (cutoffPullbackCLM e.source e.open_source e he δ hδ hcδ hδU u) = T u := by
    apply SchwartzMap.ext
    intro x
    dsimp only [S, T]
    rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    rw [cutoffPullbackCLM_apply e.source e.open_source e he δ hδ hcδ hδU u x,
      cutoffPullbackCLM_apply e.source e.open_source e he χ hχ hcχ hχU u x]
    simp only [Complex.coe_smul, smul_smul]
    by_cases hx : χ x = 0
    · simp only [hx, zero_mul, zero_smul]
    · have hxδ : δ x = 1 := interior_subset (s := {x | δ x = 1}) (hδone (subset_tsupport χ hx))
      rw [hxδ, mul_one]
  have hQapply (u : 𝓢(X, V)) (y : X) :
      Q u y = ρ y • (χ (e.symm y) • J (T u) (e.symm y)) := by
    change cutoffPullbackCLM e.target e.open_target e.symm hψ ρ hρ hcρ hρV
      (P (cutoffPullbackCLM e.source e.open_source e he δ hδ hcδ hδU u)) y = _
    rw [cutoffPullbackCLM_apply, hPapply, hinput]
  let R : 𝓢(X, V) →L[ℂ] 𝓢(X, V) :=
    (SchwartzMap.smulLeftCLM V (fun y ↦ (η y : ℂ))).comp Q
  -- Change variables in the same positive form. The absolute Jacobian covers either orientation.
  have henergy (u : 𝓢(X, V)) :
      ((‖schwartzSobolevCoordinate s (T u)‖ ^ 2 : ℝ) : ℂ) =
        ∫ y, inner ℂ (u y) (R u y) := by
    rw [norm_schwartzSobolevCoordinate_sq_eq_integral]
    simp_rw [quantize_besselSymbol]
    let f : X → ℂ := fun x ↦ inner ℂ (T u x) (J (T u) x)
    have hfzero (x : X) (hx : x ∉ e.source) : f x = 0 := by
      have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hχU h))
      simp only [f, T, cutoffPullbackCLM_apply, hχx, zero_smul, inner_zero_left]
    have hchange : (∫ x, f x) =
        ∫ y in e.target, |(fderiv ℝ e.symm y).det| • f (e.symm y) := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hfzero]
      exact integral_target_eq_integral_abs_det_fderiv_smul volume (f := e.symm)
        (fun y hy ↦ ((hψ.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
          (by simp)).hasFDerivAt) f
    have hRzero (y : X) (hy : y ∉ e.target) : inner ℂ (u y) (R u y) = 0 := by
      have hρy : ρ y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hρV h))
      simp only [R, ContinuousLinearMap.comp_apply,
        SchwartzMap.smulLeftCLM_apply_apply hηgrowth, hQapply, hρy,
        zero_smul, smul_zero, inner_zero_right]
    change (∫ x, f x) = _
    rw [hchange, ← setIntegral_eq_integral_of_forall_compl_eq_zero hRzero]
    apply setIntegral_congr_fun e.open_target.measurableSet
    intro y hy
    simp only [f, T, cutoffPullbackCLM_apply, e.right_inv hy, R,
      ContinuousLinearMap.comp_apply, SchwartzMap.smulLeftCLM_apply_apply hηgrowth,
      hQapply, Complex.coe_smul, inner_smul_left_eq_smul, inner_smul_right_eq_smul]
    by_cases hz : χ (e.symm y) = 0
    · simp only [hz, zero_smul, smul_zero]
    · have hyimage : y ∈ e '' tsupport χ :=
        ⟨e.symm y, subset_tsupport χ hz, e.right_inv hy⟩
      have hyρ : ρ y = 1 := interior_subset (s := {y | ρ y = 1}) (hρone hyimage)
      have hyη : η y = |(fderiv ℝ e.symm y).det| :=
        hηeq y (subset_tsupport ρ (show ρ y ≠ 0 by rw [hyρ]; norm_num))
      simp only [hyρ, hyη, one_smul]
  -- Identify the two already bounded local maps in Bessel coordinates.
  let B := quantizeSobolev (2 * s) s q hq hcq
  have hsub : s - 2 * s = -s := by ring
  have hQcoord (u : 𝓢(X, V)) :
      schwartzSobolevCoordinate (-s) (Q u) = B (schwartzSobolevCoordinate s u) := by
    apply besselRealization_injective n r (-s)
    rw [besselRealization_schwartzSobolevCoordinate, ← hsub]
    ext1 φ
    rw [besselRealization_quantizeSobolev, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards with x
    rw [hQ]
  let W := (sobolevCutoffCLM (r := r) (-s) η hη hcη).comp B
  have hRcoord (u : 𝓢(X, V)) :
      schwartzSobolevCoordinate (-s) (R u) = W (schwartzSobolevCoordinate s u) := by
    apply besselRealization_injective n r (-s)
    rw [besselRealization_schwartzSobolevCoordinate]
    change _ = besselRealization n r (-s)
      (sobolevCutoffCLM (-s) η hη hcη (B (schwartzSobolevCoordinate s u)))
    rw [besselRealization_sobolevCutoffCLM, ← hQcoord,
      besselRealization_schwartzSobolevCoordinate]
    ext1 φ
    simp only [TemperedDistribution.smulLeftCLM_apply_apply, SchwartzMap.coe_apply]
    apply integral_congr_ae
    filter_upwards with y
    simp only [R, ContinuousLinearMap.comp_apply]
    rw [SchwartzMap.smulLeftCLM_apply_apply hηgrowth,
      SchwartzMap.smulLeftCLM_apply_apply hηgrowth]
    simp only [smul_eq_mul, smul_smul, mul_comm]
  refine ⟨Real.sqrt ‖W‖, Real.sqrt_nonneg _, fun u ↦ ?_⟩
  have hsquare : ‖schwartzSobolevCoordinate s (T u)‖ ^ 2 ≤
      ‖W‖ * ‖schwartzSobolevCoordinate s u‖ ^ 2 := by
    have hid := (henergy u).trans (sobolev_pairing_schwartz s u (R u)).symm
    have habs := congrArg norm hid
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
      (sq_nonneg (‖schwartzSobolevCoordinate s (T u)‖))] at habs
    calc
      _ = ‖inner ℂ (schwartzSobolevCoordinate s u)
          (schwartzSobolevCoordinate (-s) (R u))‖ := habs
      _ ≤ ‖schwartzSobolevCoordinate s u‖ *
          ‖schwartzSobolevCoordinate (-s) (R u)‖ := norm_inner_le_norm _ _
      _ = ‖schwartzSobolevCoordinate s u‖ * ‖W (schwartzSobolevCoordinate s u)‖ := by
        rw [hRcoord]
      _ ≤ ‖schwartzSobolevCoordinate s u‖ * (‖W‖ * ‖schwartzSobolevCoordinate s u‖) :=
        mul_le_mul_of_nonneg_left (W.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  simpa only [mul_pow, Real.sq_sqrt (norm_nonneg W)] using hsquare

end AtiyahSinger
