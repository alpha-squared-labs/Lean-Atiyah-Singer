/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FrequencyScalingContinuity
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.SemiclassicalGlobalComposition
public import AtiyahSinger.Analysis.SmallParameterInverse

/-!
# Zero index for an everywhere invertible full symbol

Public module ID: M2308.

Sources: SG III.3.17(iii), III.7.8 and III.7.10--7.11, together with the
quantitative supplementary estimate in M2306 and the Banach inverse criterion
in M2286. SG means H. Blaine Lawson, Jr. and Marie-Louise Michelsohn,
*Spin Geometry* (Princeton University Press, 1989).

The same original quantizer acts on the two full order-zero inverse symbols.
Its actual smooth Sobolev composition errors extend by density to operator norm
bounds on the same Sobolev completion. A strictly positive small parameter
therefore gives an invertible sample. Full-symbol ellipticity and continuity
along a positive interval transfer that sample's index to parameter one.
The construction uses no norm continuity at parameter zero and introduces no
homogeneity requirement on the original full symbol.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 15

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] globalSymbolTopology

include hM hT2 hSC hC hE hμ

/-- An everywhere invertible elliptic full symbol has zero original quantized index. -/
theorem QuantizationPresentation.index_quantize_eq_zero_of_isElliptic_of_inverse
    (C : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (a b : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := r) E E 0 a.val)
    (hab : ∀ x ξ, (a.val x ξ).comp (b.val x ξ) = ContinuousLinearMap.id ℂ (E x))
    (hba : ∀ x ξ, (b.val x ξ).comp (a.val x ξ) = ContinuousLinearMap.id ℂ (E x)) :
    (C.quantize μ a).toLinearMap.index = 0 := by
  /- Keep one fixed Sobolev completion. Transport only the arithmetic identity
  s - 0 = s, retaining the original quantized smooth action and index. -/
  let s : ℝ := 0
  let T (d : globalSymbolSpace (n := n) (r := r) (q := r) E E 0) :
      A.SobolevSpace s →L[ℂ] A.SobolevSpace s :=
    Eq.ndrec (motive := fun v : ℝ ↦ A.SobolevSpace s →L[ℂ] A.SobolevSpace v)
      (C.sobolevQuantizationCLM μ A A s 0 d) (sub_zero s)
  have hcastAction (v : ℝ) (hv : v = s)
      (U : A.SobolevSpace s →L[ℂ] A.SobolevSpace v)
      (d : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
      (hU : ∀ u : smoothSections (n := n) (r := r) E,
        U (A.smoothToSobolev s u) = A.smoothToSobolev v (C.toLinearMap d u)) :
      ∀ u : smoothSections (n := n) (r := r) E,
        (Eq.ndrec (motive := fun w : ℝ ↦ A.SobolevSpace s →L[ℂ] A.SobolevSpace w)
          U hv) (A.smoothToSobolev s u) = A.smoothToSobolev s (C.toLinearMap d u) := by
    subst v
    exact hU
  have hTAction (d : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
      (u : smoothSections (n := n) (r := r) E) :
      T d (A.smoothToSobolev s u) = A.smoothToSobolev s (C.toLinearMap d u) :=
    hcastAction (s - 0) (sub_zero s) (C.sobolevQuantizationCLM μ A A s 0 d) d
      (C.sobolevQuantizationCLM_smoothToSobolev μ A A s 0 d) u
  have hcastIndex (v : ℝ) (hv : v = s)
      (U : A.SobolevSpace s →L[ℂ] A.SobolevSpace v)
      (d : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
      (hi : U.toLinearMap.index = (C.quantize μ d).toLinearMap.index) :
      (Eq.ndrec (motive := fun w : ℝ ↦ A.SobolevSpace s →L[ℂ] A.SobolevSpace w)
        U hv).toLinearMap.index = (C.quantize μ d).toLinearMap.index := by
    subst v
    exact hi
  have hTIndex (d : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
      (hd : IsEllipticFullGlobalSymbol (r := r) (q := r) E E 0 d.val) :
      (T d).toLinearMap.index = (C.quantize μ d).toLinearMap.index := by
    have helliptic :=
      (PseudodifferentialOperator.isElliptic_quantize_iff (μ := μ) C d).mpr hd
    exact hcastIndex (s - 0) (sub_zero s) (C.sobolevQuantizationCLM μ A A s 0 d) d
      ((C.quantize μ d).index_sobolevExtension_eq_of_isElliptic A A helliptic s)
  -- Lift a closed norm inequality from the actual dense smooth range.
  have hlift (U : A.SobolevSpace s →L[ℂ] A.SobolevSpace s)
      (K : ℝ) (hK : 0 ≤ K)
      (hU : ∀ u : smoothSections (n := n) (r := r) E,
        ‖U (A.smoothToSobolev s u)‖ ≤ K * ‖A.smoothToSobolev s u‖) : ‖U‖ ≤ K := by
    apply U.opNorm_le_bound hK
    intro v
    exact (A.denseRange_smoothToSobolev s).induction_on v
      (isClosed_le U.continuous.norm (continuous_const.mul continuous_norm)) hU
  obtain ⟨K, hK, hbound⟩ := C.exists_frequencyScale_inverse_error_sobolev_bound
    A s a b hab hba
  -- Define the two actual maps only on the valid positive parameter interval.
  let P (t : ℝ) : A.SobolevSpace s →L[ℂ] A.SobolevSpace s :=
    if ht : 0 < t ∧ t ≤ 1 then T (frequencyScaleGlobalSymbolSpace a t ht.1 ht.2) else 0
  let Q (t : ℝ) : A.SobolevSpace s →L[ℂ] A.SobolevSpace s :=
    if ht : 0 < t ∧ t ≤ 1 then T (frequencyScaleGlobalSymbolSpace b t ht.1 ht.2) else 0
  have hleft (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
      ‖(Q t).comp (P t) - ContinuousLinearMap.id ℂ (A.SobolevSpace s)‖ ≤ K * t := by
    apply hlift _ (K * t) (mul_nonneg hK ht.le)
    intro u
    simp only [P, Q, dite_eq_left (show 0 < t ∧ t ≤ 1 from ⟨ht, ht₁⟩),
      sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hTAction]
    rw [← map_sub]
    exact (hbound t ht ht₁ u).1
  have hright (t : ℝ) (ht : 0 < t) (ht₁ : t ≤ 1) :
      ‖(P t).comp (Q t) - ContinuousLinearMap.id ℂ (A.SobolevSpace s)‖ ≤ K * t := by
    apply hlift _ (K * t) (mul_nonneg hK ht.le)
    intro u
    simp only [P, Q, dite_eq_left (show 0 < t ∧ t ≤ 1 from ⟨ht, ht₁⟩),
      sub_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hTAction]
    rw [← map_sub]
    exact (hbound t ht ht₁ u).2
  obtain ⟨t, ht, ht₁, hzero⟩ := exists_pos_index_eq_zero_of_comp_error_bound
    P Q K hK hleft hright
  have hscaledZero :
      (C.quantize μ (frequencyScaleGlobalSymbolSpace a t ht ht₁)).toLinearMap.index = 0 := by
    simp only [P, dite_eq_left (show 0 < t ∧ t ≤ 1 from ⟨ht, ht₁⟩)] at hzero
    rw [hTIndex (frequencyScaleGlobalSymbolSpace a t ht ht₁)
      (ha.frequencyScale t ht)] at hzero
    exact hzero
  -- Follow an elliptic full-symbol path entirely within the positive interval.
  let f : unitInterval → ↥(Icc t 1) := fun τ ↦
    ⟨t + (1 - t) * τ.val, by
      constructor
      · exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ht₁) τ.property.1)
      · have hmul := mul_le_mul_of_nonneg_left τ.property.2 (sub_nonneg.mpr ht₁)
        linarith⟩
  have hf : Continuous f :=
    (continuous_const.add (continuous_const.mul continuous_subtype_val)).subtype_mk _
  let p : unitInterval → globalSymbolSpace (n := n) (r := r) (q := r) E E 0 :=
    fun τ ↦ frequencyScaleGlobalSymbolSpace a (f τ).val
      (ht.trans_le (f τ).property.1) (f τ).property.2
  have hp : Continuous p :=
    (continuous_frequencyScaleGlobalSymbolSpace a t ht).comp hf
  have he (τ : unitInterval) :
      IsEllipticFullGlobalSymbol (r := r) (q := r) E E 0 (p τ).val :=
    ha.frequencyScale (f τ).val (ht.trans_le (f τ).property.1)
  have hind := C.index_quantize_eq_of_continuous_of_isElliptic (μ := μ) A A 0 p hp he
  have hf0 : (f 0).val = t := by simp [f]
  have hf1 : (f 1).val = 1 := by simp [f]
  have hp0 : p 0 = frequencyScaleGlobalSymbolSpace a t ht ht₁ := by
    apply Subtype.ext
    change frequencyScaleGlobalSymbol (f 0).val a.val = frequencyScaleGlobalSymbol t a.val
    rw [hf0]
  have hp1 : p 1 = a := by
    apply Subtype.ext
    change frequencyScaleGlobalSymbol (f 1).val a.val = a.val
    rw [hf1]
    funext x ξ
    simp only [frequencyScaleGlobalSymbol, one_smul]
  rw [hp0, hp1] at hind
  exact hind.symm.trans hscaledZero

end AtiyahSinger
