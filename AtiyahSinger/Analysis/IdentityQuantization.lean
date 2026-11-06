/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalEllipticSymbol
public import AtiyahSinger.Analysis.ParametricQuantization

import Mathlib.Tactic.Ring

/-!
# Exact quantization of frequency-independent symbols

Public module ID: M2285.

Fourier inversion identifies the original local quantization of a frequency-independent
matrix with pointwise multiplication by that matrix. For the existing global identity
symbol, each original patch therefore acts as its input weight times the identity.
The output cutoff equals one on that input support, so it contributes no extra weight.
The actual finite partition then makes the fixed quantization exactly the identity.
This is equality of the original section maps, before taking any principal quotient.

Sources: SG III.3's Kohn-Nirenberg formula and Fourier inversion, implemented by the
existing quantizer and mathlib's Schwartz Fourier pair. The global identity calculation
is a supplement for the project's given `QuantizationPresentation`; no new quantizer
or adjustable smoothing remainder is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open FourierTransform MeasureTheory Bundle
open scoped SchwartzMap ContDiff Manifold

/-- The original Fourier formula quantizes a frequency-independent matrix by multiplication. -/
theorem quantize_frequency_independent {n r q : ℕ}
    (b : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin n)) :
    quantize (fun z _ ↦ b z) u x = b x (u x) := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r)
  let fu : 𝓢(X, V) := 𝓕 u
  let phase (η : X) : ℂ :=
    Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x η : ℂ))
  have hphase (η : X) : ‖phase η‖ = 1 := by
    simp [phase, Complex.norm_exp, Complex.mul_re]
  -- The unit-modulus inverse phase preserves the Fourier transform's L¹ bound.
  have hi : Integrable (fun η : X ↦ phase η • fu η) := by
    apply fu.integrable.norm.mono' (f := fun η : X ↦ phase η • fu η)
    · have hc : Continuous phase := by
        dsimp [phase]
        fun_prop
      exact (hc.smul fu.continuous).aestronglyMeasurable
    · filter_upwards [] with η
      rw [norm_smul, hphase, one_mul]
  have hinv : (∫ η : X, phase η • fu η) = u x := by
    have h := congrArg (fun v : 𝓢(X, V) ↦ v x)
      (show (𝓕⁻ (𝓕 u : 𝓢(X, V)) : 𝓢(X, V)) = u from
        FourierTransform.fourierInv_fourier_eq u)
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
    convert h using 1
    congr 1
    funext η
    simp only [phase, Complex.ofReal_mul, Complex.ofReal_ofNat]
    congr 2
    rw [real_inner_comm η x]
    ring
  -- Pull the same fixed fiber matrix through the integrable inverse Fourier integral.
  rw [quantize_rescaled]
  calc
    _ = ∫ η : X, b x (phase η • fu η) := by
      apply integral_congr_ae
      filter_upwards [] with η
      simp only [map_smul, phase, fu]
    _ = b x (∫ η : X, phase η • fu η) := (b x).integral_comp_comm hi
    _ = b x (u x) := by rw [hinv]

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- Every original identity patch multiplies the same section by its exact input weight. -/
theorem QuantizationPatch.toLinearMap_id_apply
    (Q : QuantizationPatch (n := n) (r := r) (q := r) E E)
    (u : smoothSections (n := n) (r := r) E) (x : M) :
    (((Q.toPiece (globalIdentitySymbol (n := n) (r := r) (E := E))).toLinearMap u).val x) =
      (Q.weight x : ℂ) • u.val x := by
  classical
  let I : globalSymbolSpace (n := n) (r := r) (q := r) E E 0 := globalIdentitySymbol
  let v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) :=
    Q.input.localize Q.chart_mem_atlas u
  have hfreq : Q.localSymbol I.val = fun z _ ↦ Q.localSymbol I.val z 0 := by
    funext z ξ
    rfl
  have hop (z : EuclideanSpace ℝ (Fin n)) :
      (Q.toPiece I).operator v z = Q.localSymbol I.val z 0 (v z) := by
    rw [(Q.toPiece I).operator_apply]
    change AtiyahSinger.quantize (Q.localSymbol I.val) v z = _
    rw [hfreq]
    exact quantize_frequency_independent (fun y ↦ Q.localSymbol I.val y 0) v z
  change Q.output.extendedFunction ((Q.toPiece I).operator v) x =
    (Q.weight x : ℂ) • u.val x
  by_cases hx : x ∈ Q.chart.source
  · by_cases hs : Q.chart x ∈ tsupport Q.input.cutoff
    · -- On the active input support both original frames are valid and output equals one.
      let := Q.input.frame_mem_atlas
      let := Q.output.frame_mem_atlas
      have he : x ∈ Q.input.frame.baseSet := by
        simpa only [Set.mem_preimage, Q.chart.left_inv hx] using
          (Q.input.support_subset hs).2
      have hf : x ∈ Q.output.frame.baseSet := by
        simpa only [Set.mem_preimage, Q.chart.left_inv hx] using
          Q.input_support_in_output_frame hs
      have hd : Q.chart x ∈ symbolChartDomain E E Q.chart Q.input.frame Q.output.frame :=
        ⟨⟨Q.chart.map_source hx,
          by simpa only [Set.mem_preimage, Q.chart.left_inv hx] using he⟩,
          by simpa only [Set.mem_preimage, Q.chart.left_inv hx] using hf⟩
      have hout : Q.output.cutoff (Q.chart x) = 1 := Q.output_eq_one _ hs
      have hv : v (Q.chart x) = (Q.input.cutoff (Q.chart x) : ℂ) •
          Q.input.frame.continuousLinearMapAt ℂ x (u.val x) := by
        change Q.input.localizedFunction u (Q.chart x) = _
        simp only [BundleChartCutoff.localizedFunction,
          ite_eq_left (Q.chart.map_source hx), sectionInChart,
          Q.input.frame.continuousLinearMapAt_apply_of_mem ℂ he]
        rw [Q.chart.left_inv hx]
      have hlocal : Q.localSymbol I.val (Q.chart x) 0 (v (Q.chart x)) =
          (Q.input.cutoff (Q.chart x) : ℂ) •
            Q.output.frame.continuousLinearMapAt ℂ x (u.val x) := by
        simp only [QuantizationPatch.localSymbol, zeroExtendedSymbol, ite_eq_left hd,
          hout, Complex.ofReal_one, one_smul, globalSymbolInChart, I, globalIdentitySymbol,
          globalSymbolId, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
          hv, map_smul]
        rw [Q.chart.left_inv hx, Q.input.frame.symmL_continuousLinearMapAt he]
      simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx, hop, hlocal,
        hout, Complex.ofReal_one, one_smul, map_smul,
        Q.output.frame.symmL_continuousLinearMapAt hf, QuantizationPatch.weight]
    · -- At an inactive input point the exact multiplication formula is zero.
      have hcut : Q.input.cutoff (Q.chart x) = 0 := image_eq_zero_of_notMem_tsupport hs
      have hv : v (Q.chart x) = 0 := by
        change Q.input.localizedFunction u (Q.chart x) = 0
        simp [BundleChartCutoff.localizedFunction, hcut]
      simp [BundleChartCutoff.extendedFunction, hx, hop, hv,
        QuantizationPatch.weight, hcut]
  · -- The original extension and the original input weight are both zero off the chart.
    simp [BundleChartCutoff.extendedFunction, QuantizationPatch.weight, hx]

/-- The given partition quantizes the existing global identity symbol
as the exact identity on smooth sections. -/
theorem QuantizationPresentation.toLinearMap_id
    (C : QuantizationPresentation (n := n) (r := r) (q := r) E E) :
    C.toLinearMap (globalIdentitySymbol (n := n) (r := r) (E := E)) = LinearMap.id := by
  classical
  let I : globalSymbolSpace (n := n) (r := r) (q := r) E E 0 := globalIdentitySymbol
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  -- First identify every original patch as multiplication by its input weight.
  have hpatch (j : Fin C.size) :
      (((C.patch j).toPiece I).toLinearMap u).val x =
        ((C.patch j).weight x : ℂ) • u.val x :=
    (C.patch j).toLinearMap_id_apply u x
  -- Sum the same patch actions and use the actual partition identity at this point.
  change (C.toLinearMap I u).val x = u.val x
  simp only [QuantizationPresentation.toLinearMap, LinearMap.sum_apply, Submodule.coe_sum,
    Finset.sum_apply, hpatch, ← Finset.sum_smul, ← Complex.ofReal_sum, C.sum_weight,
    Complex.ofReal_one, one_smul]

variable [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] globalSymbolTopology

/-- The same identity quantization is exactly identity on the fixed order-zero Sobolev space. -/
theorem QuantizationPresentation.sobolevQuantizationCLM_id
    (C : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (A : SmoothBundlePresentation (n := n) (r := r) E) :
    (show A.SobolevSpace 0 →L[ℂ] A.SobolevSpace 0 from
      (Eq.ndrec (motive := fun t : ℝ ↦ A.SobolevSpace 0 →L[ℂ] A.SobolevSpace t)
        (C.sobolevQuantizationCLM μ A A 0 0
          (globalIdentitySymbol (n := n) (r := r) (E := E))) (sub_zero (0 : ℝ)))) =
      ContinuousLinearMap.id ℂ (A.SobolevSpace 0) := by
  /- The order arithmetic is transported explicitly before comparing two endomorphisms.
  On the same concrete Sobolev space, the defining smooth-input action and the exact
  section identity agree on a dense subspace. Density gives equality everywhere. -/
  have htransport (t : ℝ) (ht : t = 0)
      (T : A.SobolevSpace 0 →L[ℂ] A.SobolevSpace t)
      (hT : ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev 0 u) = A.smoothToSobolev t u) :
      (Eq.ndrec (motive := fun s : ℝ ↦ A.SobolevSpace 0 →L[ℂ] A.SobolevSpace s)
        T ht) =
        ContinuousLinearMap.id ℂ (A.SobolevSpace 0) := by
    subst t
    change T = ContinuousLinearMap.id ℂ (A.SobolevSpace 0)
    have hfun : (T : A.SobolevSpace 0 → A.SobolevSpace 0) =
        (ContinuousLinearMap.id ℂ (A.SobolevSpace 0) :
          A.SobolevSpace 0 → A.SobolevSpace 0) := by
      apply (A.denseRange_smoothToSobolev 0).equalizer T.continuous
        (ContinuousLinearMap.id ℂ (A.SobolevSpace 0)).continuous
      funext u
      exact hT u
    exact ContinuousLinearMap.ext (fun v ↦ congrFun hfun v)
  have haction (u : smoothSections (n := n) (r := r) E) :
      C.sobolevQuantizationCLM μ A A 0 0 globalIdentitySymbol (A.smoothToSobolev 0 u) =
        A.smoothToSobolev (0 - 0) u := by
    rw [C.sobolevQuantizationCLM_smoothToSobolev μ A A 0 0 globalIdentitySymbol u]
    change A.smoothToSobolev (0 - 0) (C.toLinearMap globalIdentitySymbol u) =
      A.smoothToSobolev (0 - 0) u
    rw [C.toLinearMap_id]
    rfl
  exact htransport (0 - 0) (sub_zero 0)
    (C.sobolevQuantizationCLM μ A A 0 0 globalIdentitySymbol) haction

end AtiyahSinger
