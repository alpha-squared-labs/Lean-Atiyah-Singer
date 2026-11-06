/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricTensorSobolev
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-!
# Local Fourier reconstruction for product H1 density

Public module ID: M0608.

Frequency translation constructs the actual modulated Schwartz functions.
Its L2 continuity is inherited from measure-preserving translation, and its
first derivative graph supplies the stronger H1 control needed for localized
Fourier reconstruction. No C0 density statement is promoted to H1 density.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory FourierTransform
open scoped SchwartzMap Real

set_option maxSynthPendingDepth 30
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℂ (Fin r)

/-- Plane-wave multiplication, constructed by translating the original Fourier transform. -/
def schwartzModulation (ξ : X) (u : 𝓢(X, V)) : 𝓢(X, V) :=
  𝓕⁻ (SchwartzMap.compSubConstCLM ℂ ξ (𝓕 u))

/-- The Fourier-translation construction has the literal plane-wave value. -/
theorem schwartzModulation_apply (ξ : X) (u : 𝓢(X, V)) (x : X) :
    schwartzModulation ξ u x = Real.fourierChar (inner ℝ ξ x) • u x := by
  -- Translate the integration variable in the inverse Fourier integral.
  rw [schwartzModulation, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  change (∫ η : X, Real.fourierChar (inner ℝ η x) • (𝓕 u) (η - ξ)) = _
  have heq (η : X) :
      Real.fourierChar (inner ℝ (η + ξ) x) • (𝓕 u) (η + ξ - ξ) =
        Real.fourierChar (inner ℝ ξ x) •
          (Real.fourierChar (inner ℝ η x) • (𝓕 u) η) := by
    rw [add_sub_cancel_right, inner_add_left, AddChar.map_add_eq_mul, mul_smul, smul_comm]
  have htrans := integral_add_right_eq_self (μ := (volume : Measure X))
    (fun η : X ↦ Real.fourierChar (inner ℝ η x) • (𝓕 u) (η - ξ)) ξ
  calc
    _ = ∫ η : X, Real.fourierChar (inner ℝ (η + ξ) x) • (𝓕 u) (η + ξ - ξ) :=
      htrans.symm
    _ = ∫ η : X, Real.fourierChar (inner ℝ ξ x) •
        (Real.fourierChar (inner ℝ η x) • (𝓕 u) η) := by
      exact integral_congr_ae (Filter.Eventually.of_forall heq)
    _ = _ := ?_
  simp only [Circle.smul_def]
  rw [integral_smul]
  congr 1
  have hinv : (𝓕⁻ (𝓕 u : 𝓢(X, V)) : 𝓢(X, V)) = u := fourierInv_fourier_eq u
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq, Circle.smul_def] using
    congrArg (fun f : 𝓢(X, V) ↦ f x) hinv

/-- Plane-wave modulation preserves the actual L2 norm. -/
theorem norm_schwartzModulation_toLp (ξ : X) (u : 𝓢(X, V)) :
    ‖(schwartzModulation ξ u).toLp 2‖ = ‖u.toLp 2‖ := by
  rw [SchwartzMap.norm_toLp' (by norm_num) (by norm_num),
    SchwartzMap.norm_toLp' (by norm_num) (by norm_num)]
  simp only [schwartzModulation_apply, Circle.norm_smul]

/-- The original L2 modulation depends continuously on its frequency. -/
theorem continuous_schwartzModulation_toLp (u : 𝓢(X, V)) :
    Continuous (fun ξ : X ↦ (schwartzModulation ξ u).toLp 2) := by
  let c (ξ : X) : C(X, X) := ⟨fun η ↦ η - ξ, continuous_id.sub continuous_const⟩
  have hc : Continuous c := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_snd.sub continuous_fst
  have hm (ξ : X) : MeasurePreserving (c ξ) volume volume := by
    simpa only [c, ContinuousMap.coe_mk, sub_eq_add_neg] using
      measurePreserving_add_right (volume : Measure X) (-ξ)
  -- Translation is continuous in L2; the original unitary inverse Fourier map preserves it.
  have ht := (continuous_const (y := (𝓕 u).toLp 2)).compMeasurePreservingLp hc hm
    (by norm_num : (2 : ENNReal) ≠ ⊤)
  have heq (ξ : X) : (schwartzModulation ξ u).toLp 2 =
      𝓕⁻ (Lp.compMeasurePreserving (c ξ) (hm ξ) ((𝓕 u).toLp 2)) := by
    rw [schwartzModulation, ← SchwartzMap.toLp_fourierInv_eq]
    congr 1
  simp_rw [heq]
  exact continuous_fourierInv.comp ht

/-- A directional derivative of a modulated function adds the exact frequency multiplier. -/
theorem lineDerivOp_schwartzModulation (ξ d : X) (u : 𝓢(X, V)) :
    LineDeriv.lineDerivOp d (schwartzModulation ξ u) =
      schwartzModulation ξ (LineDeriv.lineDerivOp d u) +
        (2 * Real.pi * Complex.I * (inner ℝ ξ d : ℂ)) • schwartzModulation ξ u := by
  -- In frequency space this is the decomposition η = (η - ξ) + ξ.
  apply (fourierEquiv ℂ 𝓢(X, V)).injective
  change 𝓕 (LineDeriv.lineDerivOp d (schwartzModulation ξ u)) =
    𝓕 (schwartzModulation ξ (LineDeriv.lineDerivOp d u) +
      (2 * Real.pi * Complex.I * (inner ℝ ξ d : ℂ)) • schwartzModulation ξ u)
  rw [SchwartzMap.fourier_lineDerivOp_eq, FourierTransform.fourier_add,
    FourierTransform.fourier_smul]
  simp only [schwartzModulation, fourier_fourierInv_eq, SchwartzMap.fourier_lineDerivOp_eq]
  have hd : (fun η : X ↦ inner ℝ η d).HasTemperateGrowth := by fun_prop
  apply SchwartzMap.ext
  intro η
  simp only [smul_apply, add_apply, SchwartzMap.compSubConstCLM_apply,
    SchwartzMap.smulLeftCLM_apply_apply hd, inner_sub_left,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  rw [← add_smul]
  apply congrArg (fun z : ℂ ↦ z • (𝓕 u : 𝓢(X, V)) (η - ξ))
  simp only [RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_sub, mul_sub, sub_add_cancel]

/-- Modulated coordinate functions depend continuously on frequency in the full H1 graph. -/
theorem continuous_schwartzModulation_h1Graph (u : 𝓢(X, V)) :
    Continuous (fun ξ : X ↦ schwartzToH1Graph n r (schwartzModulation ξ u)) := by
  have hcoord (a : Option (Fin n)) :
      Continuous (fun ξ : X ↦ (schwartzH1Jet n r (schwartzModulation ξ u)).ofLp a) := by
    cases a with
    | none => exact continuous_schwartzModulation_toLp u
    | some a =>
      let d := EuclideanSpace.single a (1 : ℝ)
      have heq (ξ : X) :
          (schwartzH1Jet n r (schwartzModulation ξ u)).ofLp (some a) =
            ((2 * Real.pi)⁻¹ : ℂ) •
              ((schwartzModulation ξ (LineDeriv.lineDerivOp d u)).toLp 2 volume +
                (2 * Real.pi * Complex.I * (inner ℝ ξ d : ℂ)) •
                  (schwartzModulation ξ u).toLp 2 volume) := by
        change ((2 * Real.pi)⁻¹ : ℂ) •
          (LineDeriv.lineDerivOp d (schwartzModulation ξ u)).toLp 2 volume = _
        rw [lineDerivOp_schwartzModulation]
        congr 1
      simp_rw [heq]
      exact ((continuous_schwartzModulation_toLp (LineDeriv.lineDerivOp d u)).fun_add
        ((show Continuous (fun ξ : X ↦ (2 * Real.pi * Complex.I * (inner ℝ ξ d : ℂ))) by
          fun_prop).fun_smul (continuous_schwartzModulation_toLp u))).fun_const_smul
            ((2 * Real.pi)⁻¹ : ℂ)
  exact ((PiLp.continuous_toLp 2 _).comp (continuous_pi hcoord)).subtype_mk _

/-- The first Sobolev norm of a modulated Schwartz function has at most linear frequency growth. -/
theorem exists_norm_schwartzModulation_h1Graph_le (u : 𝓢(X, V)) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : X,
      ‖schwartzToH1Graph n r (schwartzModulation ξ u)‖ ≤ C * (1 + ‖ξ‖) := by
  classical
  let b : Option (Fin n) → ℝ
    | none => ‖u.toLp 2 volume‖
    | some a => (2 * Real.pi)⁻¹ *
        ‖(LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u).toLp 2 volume‖ +
          ‖u.toLp 2 volume‖
  have hb (a : Option (Fin n)) : 0 ≤ b a := by cases a <;> dsimp [b] <;> positivity
  have hnonneg : 0 ≤ ∑ a, b a := Finset.sum_nonneg (fun a _ ↦ hb a)
  refine ⟨1 + ∑ a, b a, by linarith, ?_⟩
  intro ξ
  -- Differentiate the actual plane wave; its scaled derivative contributes only ξ_a.
  have hcoord (a : Option (Fin n)) :
      ‖(schwartzH1Jet n r (schwartzModulation ξ u)).ofLp a‖ ≤ b a * (1 + ‖ξ‖) := by
    cases a with
    | none =>
      change ‖(schwartzModulation ξ u).toLp 2 volume‖ ≤ ‖u.toLp 2 volume‖ * (1 + ‖ξ‖)
      rw [norm_schwartzModulation_toLp]
      nlinarith [norm_nonneg ξ, norm_nonneg (u.toLp 2 volume)]
    | some a =>
      let d := EuclideanSpace.single a (1 : ℝ)
      let c : ℂ := (2 * Real.pi)⁻¹
      have hc : ‖c‖ = (2 * Real.pi)⁻¹ := by
        simp [c, abs_of_pos Real.pi_pos]
      have hprod : c * (2 * Real.pi * Complex.I * (inner ℝ ξ d : ℂ)) =
          Complex.I * (ξ a : ℂ) := by
        have hp : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
        simp only [d, EuclideanSpace.inner_single_right, one_mul, c]
        field_simp
        simp
      have heq : (schwartzH1Jet n r (schwartzModulation ξ u)).ofLp (some a) =
          c • (schwartzModulation ξ (LineDeriv.lineDerivOp d u)).toLp 2 volume +
            (Complex.I * (ξ a : ℂ)) • (schwartzModulation ξ u).toLp 2 volume := by
        change c • (SchwartzMap.toLpCLM ℂ V 2 volume)
          (LineDeriv.lineDerivOp d (schwartzModulation ξ u)) = _
        rw [lineDerivOp_schwartzModulation, map_add, map_smul, smul_add, smul_smul, hprod]
        simp only [SchwartzMap.toLpCLM_apply]
      rw [heq]
      have hξ : ‖ξ a‖ ≤ ‖ξ‖ := PiLp.norm_apply_le ξ a
      calc
        _ ≤ ‖c • (schwartzModulation ξ (LineDeriv.lineDerivOp d u)).toLp 2 volume‖ +
            ‖(Complex.I * (ξ a : ℂ)) • (schwartzModulation ξ u).toLp 2 volume‖ :=
          norm_add_le _ _
        _ = (2 * Real.pi)⁻¹ * ‖(LineDeriv.lineDerivOp d u).toLp 2 volume‖ +
            ‖ξ a‖ * ‖u.toLp 2 volume‖ := by
          simp only [norm_smul, hc, norm_mul, Complex.norm_I, Complex.norm_real,
            one_mul, norm_schwartzModulation_toLp]
        _ ≤ (2 * Real.pi)⁻¹ * ‖(LineDeriv.lineDerivOp d u).toLp 2 volume‖ +
            ‖ξ‖ * ‖u.toLp 2 volume‖ := by gcongr
        _ ≤ b (some a) * (1 + ‖ξ‖) := by
          dsimp [b, d]
          nlinarith [norm_nonneg ξ, norm_nonneg (u.toLp 2 volume),
            mul_nonneg (inv_nonneg.mpr (by positivity : 0 ≤ 2 * Real.pi))
              (norm_nonneg
                ((LineDeriv.lineDerivOp (EuclideanSpace.single a (1 : ℝ)) u).toLp 2 volume))]
  -- The finite Hilbert norm is bounded by the sum of the component norms.
  have hsum : ‖schwartzH1Jet n r (schwartzModulation ξ u)‖ ≤
      ∑ a : Option (Fin n), ‖(schwartzH1Jet n r (schwartzModulation ξ u)).ofLp a‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mp
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ ↦ norm_nonneg _)
  change ‖schwartzH1Jet n r (schwartzModulation ξ u)‖ ≤ _
  calc
    _ ≤ ∑ a : Option (Fin n), ‖(schwartzH1Jet n r (schwartzModulation ξ u)).ofLp a‖ := hsum
    _ ≤ ∑ a, b a * (1 + ‖ξ‖) := Finset.sum_le_sum (fun a _ ↦ hcoord a)
    _ = (∑ a, b a) * (1 + ‖ξ‖) := (Finset.sum_mul ..).symm
    _ ≤ (1 + ∑ a, b a) * (1 + ‖ξ‖) := by gcongr; linarith

/-- Schwartz decay makes the modulated Fourier reconstruction integrable in the actual H1 graph. -/
theorem integrable_schwartzModulation_h1Graph (f : 𝓢(X, ℂ)) (u : 𝓢(X, V)) :
    Integrable (fun ξ : X ↦ (𝓕 f) ξ • schwartzToH1Graph n r (schwartzModulation ξ u)) := by
  let : SecondCountableTopologyEither X (EuclideanH1Graph n r) := ⟨Or.inl inferInstance⟩
  let F : 𝓢(X, ℂ) := 𝓕 f
  obtain ⟨C, hC, hbound⟩ := exists_norm_schwartzModulation_h1Graph_le u
  have hweight : Integrable (fun ξ : X ↦ ‖F ξ‖ * (1 + ‖ξ‖)) := by
    have h := F.integrable.norm.add (F.integrable_pow_mul volume 1)
    convert h using 1
    funext ξ
    simp only [Pi.add_apply, pow_one]
    ring
  apply (hweight.const_mul C).mono'
  · exact ((𝓕 f : 𝓢(X, ℂ)).continuous.fun_smul
      (continuous_schwartzModulation_h1Graph u)).aestronglyMeasurable
  · filter_upwards [] with ξ
    change ‖F ξ • schwartzToH1Graph n r (schwartzModulation ξ u)‖ ≤
      C * (‖F ξ‖ * (1 + ‖ξ‖))
    rw [norm_smul]
    calc
      _ ≤ ‖F ξ‖ * (C * (1 + ‖ξ‖)) := by gcongr; exact hbound ξ
      _ = C * (‖F ξ‖ * (1 + ‖ξ‖)) := mul_left_comm ..

/-- Fourier reconstruction with a Schwartz cutoff holds in the full first-derivative graph. -/
theorem integral_schwartzModulation_h1Graph (f : 𝓢(X, ℂ)) (u : 𝓢(X, V)) :
    (∫ ξ : X, (𝓕 f) ξ • schwartzToH1Graph n r (schwartzModulation ξ u)) =
      schwartzToH1Graph n r
        (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f u) := by
  let J := euclideanH1GraphValue n r
  have hJ (v : 𝓢(X, V)) :
      euclideanH1GraphValue n r (schwartzToH1Graph n r v) = v.toLp 2 := rfl
  have hi := integrable_schwartzModulation_h1Graph f u
  -- The L2 value determines the derivative graph; its projection commutes with integration.
  apply euclideanH1GraphValue_injective n r
  rw [← J.integral_comp_comm hi]
  simp only [J, map_smul, hJ]
  let D := Lp.toTemperedDistributionCLM V (volume : Measure X) 2
  have hD : Function.Injective D :=
    LinearMap.ker_eq_bot.mp Lp.ker_toTemperedDistributionCLM_eq_bot
  have hiL : Integrable (fun ξ : X ↦ (𝓕 f) ξ • (schwartzModulation ξ u).toLp 2) := by
    simpa only [J, map_smul, hJ] using J.integrable_comp hi
  apply hD
  apply DFunLike.ext
  intro φ
  let T : Lp V 2 (volume : Measure X) →L[ℂ] V :=
    (PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) _ φ).comp D
  have heval (v : 𝓢(X, V)) : T (v.toLp 2) = ∫ x, φ x • v x := by
    change (D (v.toLp 2 volume)) φ = _
    rw [Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_toLp_eq]
    exact SchwartzMap.toTemperedDistributionCLM_apply_apply volume v φ
  have hT (v : Lp V 2 (volume : Measure X)) : T v = D v φ := rfl
  simp only [← hT]
  rw [← T.integral_comp_comm hiL]
  simp only [map_smul, heval]
  -- Fourier bilinear duality identifies the original vector against every Schwartz test.
  let g : 𝓢(X, V) := SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) φ u
  have htest (ξ : X) : (∫ x : X, φ x • schwartzModulation ξ u x) = (𝓕⁻ g) ξ := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [schwartzModulation_apply, real_inner_comm ξ x]
    change φ x • (Real.fourierChar (inner ℝ ξ x) • u x) =
      Real.fourierChar (inner ℝ ξ x) • (φ x • u x)
    exact smul_comm _ _ _
  simp_rw [htest]
  have hFourier := SchwartzMap.integral_fourierInv_smul_eq (𝓕 f : 𝓢(X, ℂ)) g
  rw [fourierInv_fourier_eq] at hFourier
  rw [← hFourier]
  apply integral_congr_ae
  filter_upwards [] with x
  change f x • (φ x • u x) = φ x • (f x • u x)
  exact smul_comm _ _ _

/-- A Schwartz multiple is approximated in H1 by finite linear combinations of modulations.
Separated cutoffs have separated modulations, giving the local tensor-density step. -/
theorem schwartzToH1Graph_pairing_mem_closure_span_modulation
    (f : 𝓢(X, ℂ)) (u : 𝓢(X, V)) :
    schwartzToH1Graph n r (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) f u) ∈
      (Submodule.span ℂ (Set.range fun ξ : X ↦
        schwartzToH1Graph n r (schwartzModulation ξ u))).topologicalClosure := by
  let S := Submodule.span ℂ (Set.range fun ξ : X ↦
    schwartzToH1Graph n r (schwartzModulation ξ u))
  let C := S.topologicalClosure
  let F : X → C := fun ξ ↦
    ⟨(𝓕 f) ξ • schwartzToH1Graph n r (schwartzModulation ξ u),
      C.smul_mem _ (S.le_topologicalClosure (Submodule.subset_span ⟨ξ, rfl⟩))⟩
  let : SecondCountableTopologyEither X C := ⟨Or.inl inferInstance⟩
  have hFc : Continuous F :=
    ((𝓕 f : 𝓢(X, ℂ)).continuous.fun_smul
      (continuous_schwartzModulation_h1Graph u)).subtype_mk _
  have hFi : Integrable F :=
    (integrable_schwartzModulation_h1Graph f u).norm.mono'
      hFc.aestronglyMeasurable (Filter.Eventually.of_forall (fun _ ↦ le_rfl))
  -- Integrating in the closed subspace keeps the reconstruction in the same H1 closure.
  have hval : (∫ ξ : X, (𝓕 f) ξ • schwartzToH1Graph n r (schwartzModulation ξ u)) =
      (∫ ξ : X, F ξ : C).val := C.subtypeL.integral_comp_comm hFi
  have hmem : (∫ ξ : X, (𝓕 f) ξ • schwartzToH1Graph n r (schwartzModulation ξ u)) ∈ C := by
    rw [hval]
    exact (∫ ξ : X, F ξ : C).property
  rwa [integral_schwartzModulation_h1Graph f u] at hmem

end AtiyahSinger
