/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSymbolTopology
public import AtiyahSinger.Analysis.PseudodifferentialRegularity
public import AtiyahSinger.Analysis.QuantizationBounds

import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Operator-norm continuity of fixed quantization

Public module ID: M0848.

A03/A08: the Fourier/Schur estimate in SG III.3.2 uses finitely many symbol
derivatives. A fixed finite quantization presentation therefore gives a continuous
linear map from the symbol seminorm topology to bounded Sobolev operators.
This supplies the analytic continuity input for SG III.7.10--7.11, p.204, for
general symbol-topology continuous parameter families, beyond a fixed finite span.
Joint pointwise continuity alone is not substituted for symbol-seminorm control.
Ellipticity, Fredholmness, and constancy of the index still require separate bridges.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

-- Continuity below always uses the weighted derivative topology on the source.
attribute [local instance] globalSymbolTopology

namespace QuantizationPresentation

variable (C : QuantizationPresentation (n := n) (r := r) (q := q) E F)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F) (s m : ℝ)

include hM hT2 hSC hC hE hF hμ

/-- A fixed quantizer has an operator-norm estimate using finitely many symbol seminorms. -/
theorem exists_sobolevQuantization_seminorm_bound :
    ∃ (J : Finset (GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F))
      (K : ℝ≥0), ∀ p : globalSymbolSpace (n := n) (r := r) (q := q) E F m,
        ‖C.sobolevQuantizationLinearMap μ A B s m p‖ ≤
          (K : ℝ) * (J.sup (globalSymbolSeminorm E F m)) p := by
  /- Stage 1: trace SG III.3.2's integration-by-parts and Schur bounds for each
  localized symbol. Only finitely many derivatives are used for fixed real s,m;
  cutoffs confine the spatial estimates to compact subsets of valid domains.
  Stage 2: the fixed frame/chart changes and Sobolev presentations contribute
  fixed bounded maps. Sum the finitely many local estimates and absorb constants
  and the finite sum into a nonnegative multiple of the finite supremum.
  The constant and the seminorm indices are chosen before p, not separately for
  each symbol. Empty presentations give the zero operator and allow an empty J. -/
  classical
  -- Each fixed patch retains its original localization, coordinate symbol and extension.
  have hpatch (Q : QuantizationPatch (n := n) (r := r) (q := q) E F) :
      ∃ (J : Finset (GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F))
        (c : ℝ≥0), ∀ (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
        (u : smoothSections (n := n) (r := r) E),
          ‖B.smoothToSobolev (s - m) ((Q.toPiece p).toLinearMap u)‖ ≤
            (c : ℝ) * (J.sup (globalSymbolSeminorm E F m)) p *
              ‖A.smoothToSobolev s u‖ := by
    let := Q.input.frame_mem_atlas
    let := Q.output.frame_mem_atlas
    let U := symbolChartDomain E F Q.chart Q.input.frame Q.output.frame
    have hU : IsOpen U := isOpen_symbolChartDomain E F Q.chart Q.input.frame Q.output.frame
    obtain ⟨J, c, hc⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
      (r := r) (q := q) U hU m s Q.output.cutoff Q.output.smooth_cutoff
      Q.output.compact_support Q.output_support_subset_domain
    let index (j : SymbolSeminormIndex U) :
        GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F :=
      { chart := Q.chart
        mem_atlas := Q.chart_mem_atlas
        inputFrame := Q.input.frame
        outputFrame := Q.output.frame
        input_mem_atlas := Q.input.frame_mem_atlas
        output_mem_atlas := Q.output.frame_mem_atlas
        localIndex := j }
    let J' := J.image index
    obtain ⟨Ci, hCi, hinput⟩ :=
      Q.input.exists_norm_localize_sobolev_le Q.chart_mem_atlas A s
    obtain ⟨Co, hCo, houtput⟩ :=
      Q.output.exists_norm_extend_sobolev_le Q.chart_mem_atlas B (s - m)
    refine ⟨J', ⟨Co * (c : ℝ) * Ci, mul_nonneg (mul_nonneg hCo c.coe_nonneg) hCi⟩, ?_⟩
    intro p u
    let localP := globalSymbolInChartSpace E F m p Q.chart Q.chart_mem_atlas
      Q.input.frame Q.output.frame
    have hsup : (J.sup (symbolSeminorm hU m)) localP ≤
        (J'.sup (globalSymbolSeminorm E F m)) p := by
      apply Seminorm.finset_sup_apply_le
      · exact apply_nonneg _ p
      · intro j hj
        change globalSymbolSeminorm E F m (index j) p ≤ _
        exact Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    let v := Q.input.localize Q.chart_mem_atlas u
    let w := (Q.toPiece p).operator v
    have hlocal : ‖schwartzSobolevCoordinate (s - m) w‖ ≤
        (c : ℝ) * (J'.sup (globalSymbolSeminorm E F m)) p *
          ‖schwartzSobolevCoordinate s v‖ := by
      exact (hc localP v).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup c.coe_nonneg)
          (norm_nonneg _))
    change ‖B.smoothToSobolev (s - m) (Q.output.extend Q.chart_mem_atlas w)‖ ≤ _
    calc
      _ ≤ Co * ‖schwartzSobolevCoordinate (s - m) w‖ := houtput w
      _ ≤ Co * ((c : ℝ) * (J'.sup (globalSymbolSeminorm E F m)) p *
          ‖schwartzSobolevCoordinate s v‖) := mul_le_mul_of_nonneg_left hlocal hCo
      _ ≤ Co * ((c : ℝ) * (J'.sup (globalSymbolSeminorm E F m)) p *
          (Ci * ‖A.smoothToSobolev s u‖)) := by
        gcongr
        exact hinput u
      _ = _ := by
        change Co * ((c : ℝ) * (J'.sup (globalSymbolSeminorm E F m)) p *
          (Ci * ‖A.smoothToSobolev s u‖)) =
            (Co * (c : ℝ) * Ci) * (J'.sup (globalSymbolSeminorm E F m)) p *
              ‖A.smoothToSobolev s u‖
        ring
  choose J c hc using fun j ↦ hpatch (C.patch j)
  let L : Finset (GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :=
    Finset.univ.biUnion J
  refine ⟨L, ∑ j, c j, ?_⟩
  intro p
  let b : ℝ := (L.sup (globalSymbolSeminorm E F m)) p
  have hb : 0 ≤ b := apply_nonneg _ p
  have hsup (j : Fin C.size) : (J j).sup (globalSymbolSeminorm E F m) p ≤ b := by
    apply Seminorm.finset_sup_apply_le hb
    intro k hk
    exact Seminorm.le_finset_sup_apply (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hk⟩)
  -- The finite sum is bounded on actual smooth sections; its unique extension has the same norm.
  have hsmooth (u : smoothSections (n := n) (r := r) E) :
      ‖C.sobolevQuantizationLinearMap μ A B s m p (A.smoothToSobolev s u)‖ ≤
        ((∑ j, c j : ℝ≥0) : ℝ) * b * ‖A.smoothToSobolev s u‖ := by
    change ‖(C.quantize μ p).sobolevExtension A B s (A.smoothToSobolev s u)‖ ≤ _
    rw [PseudodifferentialOperator.sobolevExtension_smoothToSobolev]
    change ‖B.smoothToSobolev (s - m) ((∑ j, ((C.patch j).toPiece p).toLinearMap) u)‖ ≤ _
    rw [LinearMap.sum_apply, map_sum]
    calc
      _ ≤ ∑ j, ‖B.smoothToSobolev (s - m) (((C.patch j).toPiece p).toLinearMap u)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, (c j : ℝ) * (J j).sup (globalSymbolSeminorm E F m) p *
          ‖A.smoothToSobolev s u‖ := Finset.sum_le_sum (fun j _ ↦ hc j p u)
      _ ≤ ∑ j, (c j : ℝ) * b * ‖A.smoothToSobolev s u‖ := by
        gcongr with j hj
        exact hsup j
      _ = _ := by simp only [← Finset.sum_mul, NNReal.coe_sum]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (NNReal.coe_nonneg _) hb)
  intro u
  exact (A.denseRange_smoothToSobolev s).induction_on u
    (isClosed_le (C.sobolevQuantizationLinearMap μ A B s m p).continuous.norm
      (continuous_const.mul continuous_norm)) hsmooth

/-- Fixed quantization is continuous into the operator norm on H^s -> H^(s-m). -/
theorem continuous_sobolevQuantizationLinearMap :
    Continuous (C.sobolevQuantizationLinearMap μ A B s m) := by
  /- The preceding bound controls the norm seminorm of the linear map by a
  nonnegative multiple of a finite supremum of source seminorms. Use
  WithSeminorms.continuous_normedSpace_rng with withSeminorms_globalSymbolTopology.
  The codomain topology is the norm topology of continuous linear maps. -/
  obtain ⟨J, c, hc⟩ := C.exists_sobolevQuantization_seminorm_bound μ A B s m
  apply WithSeminorms.continuous_normedSpace_rng _
    (withSeminorms_globalSymbolTopology E F m)
  exact ⟨J, c, hc⟩

/-- The existing linear quantization, with continuity for the explicit symbol topology. -/
def sobolevQuantizationCLM :
    globalSymbolSpace (n := n) (r := r) (q := q) E F m →L[ℂ]
      (A.SobolevSpace s →L[ℂ] B.SobolevSpace (s - m)) where
  toLinearMap := C.sobolevQuantizationLinearMap μ A B s m
  cont := C.continuous_sobolevQuantizationLinearMap μ A B s m

/-- Any continuous family in the symbol seminorm topology yields a norm-continuous family. -/
theorem continuous_sobolevQuantization {Z : Type*} [TopologicalSpace Z]
    (p : Z → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : Continuous p) :
    Continuous (fun z ↦ (C.quantize μ (p z)).sobolevExtension A B s) := by
  /- Compose hp with the continuous fixed quantization map. Its defining
  function is precisely the unique critical Sobolev extension of C.quantize.
  No finite-dimensional span, compact parameter space, or parameter derivative
  is assumed. The quantization presentation and real order remain fixed. -/
  exact (C.continuous_sobolevQuantizationLinearMap μ A B s m).comp hp

/-- Convergence in all symbol seminorms implies convergence of the quantized operators. -/
theorem tendsto_sobolevQuantization {Z : Type*} (l : Filter Z)
    (p : Z → globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (b : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : Tendsto p l (𝓝 b)) :
    Tendsto (fun z ↦ (C.quantize μ (p z)).sobolevExtension A B s) l
      (𝓝 ((C.quantize μ b).sobolevExtension A B s)) := by
  /- Continuity of the quantization map at b transports the supplied filter
  convergence into the normed operator space. The source convergence can be
  checked using tendsto_globalSymbolTopology_iff on symbol differences. -/
  exact (C.continuous_sobolevQuantizationLinearMap μ A B s m).continuousAt.tendsto.comp hp

/-- The continuous quantization still acts as the original operator on smooth sections. -/
theorem sobolevQuantizationCLM_smoothToSobolev
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (u : smoothSections (n := n) (r := r) E) :
    C.sobolevQuantizationCLM μ A B s m p (A.smoothToSobolev s u) =
      B.smoothToSobolev (s - m) ((C.quantize μ p).toLinearMap u) := by
  /- Unfold the continuous and linear quantization wrappers. The resulting
  operator is the existing Sobolev extension of C.quantize μ p. Its defining
  smooth-section action gives the displayed equality with no additional choice. -/
  exact (C.quantize μ p).sobolevExtension_smoothToSobolev A B s u

end QuantizationPresentation

end AtiyahSinger
