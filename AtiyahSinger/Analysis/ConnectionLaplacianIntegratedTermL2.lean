/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ConnectionLaplacianIntegratedTerm
public import AtiyahSinger.Analysis.FiniteResolventPatchSobolevDecay
public import AtiyahSinger.Analysis.SmoothSectionBochnerIntegral

/-!
# The integrated finite-parametrix term on the original metric L2 space

Public module ID: M0391.

The original fixed-family Sobolev decay makes the weighted term integrable above
the continuous embedding threshold. Its already proved actual fiber integral then
identifies the Sobolev Bochner integral, and the original metric comparison sends
that identity to the prescribed L2 completion. No L2 point evaluation is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

set_option maxSynthPendingDepth 30

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]

namespace FiniteResolventPatch

variable {L : DifferentialOperator (n := n) (r := r) (q := r) E E 2}

/-- The same integrated PDO term is the Bochner integral in the original metric L2 completion. -/
theorem integrableOn_smul_term_smoothToL2_and_integratedTerm
    (P : FiniteResolventPatch L) (h : SmoothHermitianMetric (n := n) (r := r) E)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (j : ℕ) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (u : smoothSections (n := n) (r := r) E) :
    IntegrableOn (fun t : ℝ ↦ t ^ (-p) • h.smoothToL2 μ (P.positiveTerm j t u))
        (Ioi 0) ∧
      h.smoothToL2 μ ((P.integratedTerm j p hp hp1).toLinearMap u) =
        ∫ t in Ioi (0 : ℝ), t ^ (-p) • h.smoothToL2 μ (P.positiveTerm j t u) := by
  let s : ℝ := (n : ℝ) / 2 + 1
  let : SecondCountableTopologyEither ℂ (A.SobolevSpace s) := ⟨Or.inl inferInstance⟩
  let : SecondCountableTopologyEither ℝ (A.SobolevSpace s) := ⟨Or.inl inferInstance⟩
  have hs : (n : ℝ) / 2 < s := by dsimp only [s]; linarith
  let ν : Measure ℝ := volume.restrict (Ioi 0)
  let f (t : ℝ) : smoothSections (n := n) (r := r) E :=
    ((t ^ (-p) : ℝ) : ℂ) • P.positiveTerm j t u
  -- The same actual term has a continuous realization with resolvent decay in high order.
  obtain ⟨T, hTcont, ⟨C, _hC, hTbound⟩, hT⟩ :=
    P.exists_continuous_decay_sobolev_term A s j
  let base (t : ℝ) : ℝ := t ^ (-p) * (1 + t) ^ (-1 : ℝ)
  have hbaseInt : Integrable base ν := by
    have hbase := ((resolvent_weight_integral p hp hp1 0).2 1 zero_lt_one).1
    change IntegrableOn base (Ioi 0)
    exact IntegrableOn.congr_fun hbase (fun t _ ↦ by
      dsimp only [base]
      norm_num) measurableSet_Ioi
  have hw : AEStronglyMeasurable (fun t : ℝ ↦ ((t ^ (-p) : ℝ) : ℂ)) ν :=
    (Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const (fun t (ht : t ∈ Ioi (0 : ℝ)) ↦
        Or.inl (ne_of_gt ht)))).aestronglyMeasurable measurableSet_Ioi
  have hraw : Continuous (fun t : ℝ ↦ T t (A.smoothToSobolev s u)) :=
    hTcont.clm_apply continuous_const
  have hweighted : Integrable
      (fun t : ℝ ↦ ((t ^ (-p) : ℝ) : ℂ) • T t (A.smoothToSobolev s u)) ν := by
    apply (hbaseInt.const_mul (C * ‖A.smoothToSobolev s u‖)).mono'
      (hw.smul hraw.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change ‖((t ^ (-p) : ℝ) : ℂ) • T t (A.smoothToSobolev s u)‖ ≤
      (C * ‖A.smoothToSobolev s u‖) * base t
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    calc
      _ ≤ t ^ (-p) * (‖T t‖ * ‖A.smoothToSobolev s u‖) :=
        mul_le_mul_of_nonneg_left ((T t).le_opNorm _) (Real.rpow_nonneg ht.le _)
      _ ≤ t ^ (-p) * ((C / (1 + t)) * ‖A.smoothToSobolev s u‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hTbound t ht) (norm_nonneg _))
          (Real.rpow_nonneg ht.le _)
      _ = (C * ‖A.smoothToSobolev s u‖) * base t := by
        simp only [base, Real.rpow_neg_one, div_eq_mul_inv]
        ring
  have hsame : (fun t : ℝ ↦ A.smoothToSobolev s (f t)) =ᵐ[ν]
      (fun t : ℝ ↦ ((t ^ (-p) : ℝ) : ℂ) • T t (A.smoothToSobolev s u)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change A.smoothToSobolev s
      (((t ^ (-p) : ℝ) : ℂ) • P.positiveTerm j t u) = _
    rw [(A.smoothToSobolev s).map_smul]
    rw [positiveTerm, dite_eq_left (show 0 < t from ht), hT t ht u]
  have hf : Integrable (fun t : ℝ ↦ A.smoothToSobolev s (f t)) ν :=
    hweighted.congr hsame.symm
  -- The actual smooth output was identified pointwise using the same symbols and cutoffs.
  have hpoint (x : M) : ((P.integratedTerm j p hp hp1).toLinearMap u).val x =
      ∫ t, (f t).val x ∂ν := by
    have hfpoint (t : ℝ) : (f t).val x =
        t ^ (-p) • (P.positiveTerm j t u).val x := by
      change ((t ^ (-p) : ℝ) : ℂ) • (P.positiveTerm j t u).val x = _
      rw [Complex.coe_smul]
    simp_rw [hfpoint]
    exact (P.integrableOn_smul_term_and_integratedTerm_apply j p hp hp1 u x).2
  have hmetric := h.integrable_and_smoothToL2_eq_integral_of_pointwise μ A ν s hs
    f hf ((P.integratedTerm j p hp hp1).toLinearMap u) hpoint
  have hfmetric (t : ℝ) : h.smoothToL2 μ (f t) =
      t ^ (-p) • h.smoothToL2 μ (P.positiveTerm j t u) := by
    change h.smoothToL2 μ (((t ^ (-p) : ℝ) : ℂ) • P.positiveTerm j t u) = _
    rw [(h.smoothToL2 μ).map_smul, Complex.coe_smul]
  simp_rw [hfmetric] at hmetric
  exact hmetric

end FiniteResolventPatch

end AtiyahSinger
