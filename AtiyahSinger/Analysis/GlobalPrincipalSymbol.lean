/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Analysis.GlobalPseudodifferentialOperator
public import AtiyahSinger.Analysis.GlobalSymbol
public import AtiyahSinger.Analysis.SymbolLocality

import AtiyahSinger.Analysis.CompactKernelSymbol
import AtiyahSinger.Analysis.SmoothSectionMultiplication

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The principal symbol of a global pseudodifferential operator

Public module ID: M0673.

Spin Geometry III.3.18-3.19, pp.187-188. Each local piece gives an actual
global Hom-valued symbol by multiplying its symbol by both cutoffs and extending
through its chart and frames. The sum of these symbols is independent of the local
representation modulo one lower order. This constructs a class in the concrete
global quotient, without selecting a homogeneous representative.

The operator acts on actual smooth sections of fixed-rank complex bundles over a
closed smooth manifold. The positive density describes the smoothing remainder;
the principal class is independent of that density. No metric or connection is
needed here. SG's subsequent canonical quantization is a separate construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

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

namespace PseudodifferentialPiece

variable {m : ℝ} (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)

/-- Transport the cutoff product times the local symbol to actual cotangent and bundle fibers. -/
def globalSymbolFunction : GlobalSymbolFunction (n := n) E F := by
  classical
  letI := L.input.frame_mem_atlas
  letI := L.output.frame_mem_atlas
  exact fun x ξ ↦
    if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
      ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
        (L.output.frame.symmL ℂ x).comp
          ((L.symbol (L.chart x) (covectorInChart L.chart x ξ)).comp
            (L.input.frame.continuousLinearMapAt ℂ x))
    else 0

/-- The symbol vanishes outside the inverse image of the common cutoff support. -/
theorem globalSymbolFunction_eq_zero (x : M)
    (hx : x ∉ L.chart.symm '' (tsupport L.output.cutoff ∩ tsupport L.input.cutoff))
    (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
    L.globalSymbolFunction x ξ = 0 := by
  /- Outside the chart/frame overlap this is the zero-extension branch. Inside
  it, the inverse-chart identity and hx imply at least one cutoff vanishes.
  Thus their product is zero. No support condition in the frequency is asserted. -/
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  -- Nonzero cutoffs would put the original point back in the specified closed support.
  unfold globalSymbolFunction
  split_ifs with h
  · have hcut : L.output.cutoff (L.chart x) = 0 ∨ L.input.cutoff (L.chart x) = 0 := by
      by_contra hne
      push Not at hne
      apply hx
      exact ⟨L.chart x, ⟨subset_tsupport _ (by exact hne.1),
        subset_tsupport _ (by exact hne.2)⟩, L.chart.left_inv h.1.1⟩
    rcases hcut with hcut | hcut <;> simp [hcut]
  · rfl

/-- In its own valid coordinates the global symbol retains both cutoff factors. -/
theorem globalSymbolInChart_globalSymbolFunction
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    (z η : EuclideanSpace ℝ (Fin n))
    (hz : z ∈ symbolChartDomain E F L.chart L.input.frame L.output.frame) :
    letI := L.input.frame_mem_atlas
    letI := L.output.frame_mem_atlas
    globalSymbolInChart E F L.globalSymbolFunction L.chart L.input.frame L.output.frame z η =
      ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z η := by
  /- hz selects the nonzero-extension branch at L.chart.symm z. Both frame maps
  cancel their inverses there; covectorInChart_covectorFromChart recovers η.
  The remaining scalar is the product of the two original cutoffs, not either
  cutoff separately and not an exact full symbol of the cutoff operator. -/
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  have hx : L.chart.symm z ∈ L.chart.source ∩ L.input.frame.baseSet ∩
      L.output.frame.baseSet := ⟨⟨L.chart.map_target hz.1.1, hz.1.2⟩, hz.2⟩
  -- On the valid overlap, the original covector and both frame inverses cancel.
  unfold globalSymbolInChart globalSymbolFunction
  rw [ite_eq_left hx, L.chart.right_inv hz.1.1,
    covectorInChart_covectorFromChart L.chart L.chart_mem_atlas _ hx.1.1]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, smul_apply, map_smul]
  rw [L.output.frame.continuousLinearMapAt_symmL hx.2,
    L.input.frame.continuousLinearMapAt_symmL hx.1.2]

/-- The exact cutoff symbol and the transported global representative differ in order m-1. -/
theorem isSymbol_cutoffSymbol_sub_globalSymbolInChart
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] :
    letI := L.input.frame_mem_atlas
    letI := L.output.frame_mem_atlas
    IsSymbol (symbolChartDomain E F L.chart L.input.frame L.output.frame) (m - 1)
      (cutoffSymbol L.output.cutoff L.input.cutoff L.symbol -
        globalSymbolInChart E F L.globalSymbolFunction L.chart L.input.frame L.output.frame) := by
  /- Stage 1: specialize hasSymbolExpansion_cutoffSymbol to N=1. Its diagonal
  zeroth term is precisely outputCutoff(x) * inputCutoff(x) * symbol(x,ξ).
  Stage 2: restrict to the open common chart/frame domain and use the preceding
  coordinate formula. Equal functions on this open domain have the same derivatives
  there. Hence the full symbol minus the global representative has order m-1. -/
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let U := symbolChartDomain E F L.chart L.input.frame L.output.frame
  have hU : IsOpen U := isOpen_symbolChartDomain E F L.chart L.input.frame L.output.frame
  let a : SymbolFunction n r q := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol -
    fun x ξ ↦ cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol x x ξ
  let b : SymbolFunction n r q := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol -
    globalSymbolInChart E F L.globalSymbolFunction L.chart L.input.frame L.output.frame
  have ha : IsSymbol U (m - 1) a := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol
      L.output.cutoff L.input.cutoff L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support 1
    simp only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] at h
    refine ⟨h.1.mono (Set.prod_mono (Set.subset_univ U) (Set.Subset.refl _)), ?_⟩
    intro K _ hK i j
    exact h.2 K (Set.subset_univ K) hK i j
  have heq (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) : b x ξ = a x ξ := by
    dsimp only [a, b, Pi.sub_apply]
    rw [L.globalSymbolInChart_globalSymbolFunction x ξ hx]
    simp only [cutoffAmplitude, Complex.coe_smul]
  -- Equality on the open chart domain identifies all local mixed derivatives.
  have hder (i j : ℕ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ U)
      (ξ : EuclideanSpace ℝ (Fin n)) : symbolDerivative b i j x ξ =
        symbolDerivative a i j x ξ := by
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      rw [show b y = a y from funext (heq y hy)]
    exact (hnear.iteratedFDeriv ℝ i).eq_of_nhds
  refine ⟨ha.1.congr (fun z hz ↦ heq z.1 hz.1 z.2), ?_⟩
  intro K hK hcompact i j
  obtain ⟨C, hC, hbound⟩ := ha.2 K hK hcompact i j
  refine ⟨C, hC, ?_⟩
  intro x hx ξ
  change ‖symbolDerivative b i j x ξ‖ ≤ _
  rw [hder i j x (hK hx) ξ]
  exact hbound x hx ξ

/-- Compact base support makes this extension an actual global order-m symbol. -/
theorem isGlobalSymbol_globalSymbolFunction
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F] :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m L.globalSymbolFunction := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  have hD : IsOpen D := (L.chart.open_source.inter L.input.frame.open_baseSet).inter
    L.output.frame.open_baseSet
  let K := L.chart.symm '' tsupport L.output.cutoff
  have hK : IsCompact K := L.output.compact_support.image_of_continuousOn
    (L.chart.continuousOn_symm.mono (fun y hy ↦ (L.output.support_subset hy).1))
  have hKD : K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
      L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
  have hzero (x : M) (hx : x ∉ K) (ξ) : L.globalSymbolFunction x ξ = 0 :=
    L.globalSymbolFunction_eq_zero x
      (fun h ↦ hx ((Set.image_mono Set.inter_subset_left) h)) ξ
  -- On an open set, equality of the original functions gives all actual mixed derivatives.
  have congrSymbol {V : Set X} (hV : IsOpen V) (p q : SymbolFunction n r q)
      (hp : IsSymbol V m p) (hpq : ∀ x ∈ V, ∀ ξ, p x ξ = q x ξ) :
      IsSymbol V m q := by
    refine ⟨hp.1.congr (fun z hz ↦ (hpq z.1 hz.1 z.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := hp.2 C hCV hC i j
    refine ⟨B, hB, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (p y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (q y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      rw [funext (hpq y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  let p₀ : SymbolFunction n r q := fun z ξ ↦
    ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z ξ
  have hp₀ : IsSymbol Set.univ m p₀ := by
    let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
      fun z ↦ ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q))
    let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
      fun _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))
    have hA : ContDiffOn ℝ ∞ A Set.univ :=
      ((Complex.ofRealCLM.contDiff.comp
        (L.output.smooth_cutoff.mul L.input.smooth_cutoff)).smul contDiff_const).contDiffOn
    have hB : ContDiffOn ℝ ∞ B Set.univ := contDiffOn_const
    have hp := isSymbol_matrixSymbol Set.univ isOpen_univ m L.symbol L.isSymbol A B hA hB
    convert hp using 1
    funext z ξ
    simp [matrixSymbol, p₀, A, B]
  intro c hc e f _ _
  let U := symbolChartDomain E F c e f
  let p := globalSymbolInChart E F L.globalSymbolFunction c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  apply IsSymbol.of_locally hU
  intro z hz
  by_cases hzK : c.symm z ∈ K
  · -- Near the compact support, use the original chart transition and the same two frames.
    let V := U ∩ c.symm ⁻¹' D
    have hV : IsOpen V :=
      (c.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU hD
    have hzV : z ∈ V := ⟨hz, hKD hzK⟩
    let t : OpenPartialHomeomorph X X := L.chart.symm.trans c
    have ht : ContDiffOn ℝ ∞ t t.source := by
      intro y hy
      exact (((contMDiffAt_of_mem_maximalAtlas hcM hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1)).contDiffAt).contDiffWithinAt
    have hts : ContDiffOn ℝ ∞ t.symm t.target := by
      intro y hy
      exact (((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1)).contDiffAt).contDiffWithinAt
    have hVt : V ⊆ t.target := fun y hy ↦ ⟨hy.1.1.1, hy.2.1.1⟩
    have hpt : IsSymbol V m (cotangentSymbol t p₀) :=
      (isSymbol_cotangentSymbol t ht hts m p₀
        (hp₀.restrict (Set.subset_univ _))).restrict hVt
    let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
      fun y ↦ (L.output.frame.coordChangeL ℂ f (c.symm y)).toContinuousLinearMap
    let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
      fun y ↦ (L.input.frame.coordChangeL ℂ e (c.symm y)).symm.toContinuousLinearMap
    have hcV : ContMDiffOn I I ∞ c.symm V := by
      intro y hy
      exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1.1).contMDiffWithinAt
    have hA : ContDiffOn ℝ ∞ A V := contDiffOn_coordChangeL_comp F
      L.output.frame f V c.symm hcV (fun y hy ↦ ⟨hy.2.2, hy.1.2⟩)
    have hB : ContDiffOn ℝ ∞ B V := contDiffOn_symm_coordChangeL_comp E
      L.input.frame e V c.symm hcV (fun y hy ↦ ⟨hy.2.1.2, hy.1.1.2⟩)
    refine ⟨V, hV, hzV, Set.inter_subset_left,
      congrSymbol hV _ p (isSymbol_matrixSymbol V hV m _ hpt A B hA hB) ?_⟩
    intro y hy η
    -- The frequency change is the adjoint derivative of precisely this chart transition.
    have hfreq : covectorInChart L.chart (c.symm y)
        (covectorFromChart c (c.symm y) η) =
          (fderiv ℝ t (t.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (L.chart (c.symm y))
        (by
          simpa only [L.chart.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hy.1.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hdM (L.chart.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [L.chart.left_inv hsource] at hcomp
      have htcomp : fderiv ℝ t (t.symm y) =
          (mfderiv I I c (c.symm y)).comp
            (mfderiv I I L.chart.symm (L.chart (c.symm y))) := hcomp
      ext j
      change inner ℝ η ((mfderiv I I c (c.symm y))
          ((mfderiv I I L.chart.symm (L.chart (c.symm y)))
            (EuclideanSpace.single j 1))) =
        ((fderiv ℝ t (t.symm y)).adjoint η) j
      have hadj := (fderiv ℝ t (t.symm y)).adjoint_inner_left
        (EuclideanSpace.single j 1) η
      calc
        _ = inner ℝ η ((fderiv ℝ t (t.symm y)) (EuclideanSpace.single j 1)) := by
          rw [htcomp]
          rfl
        _ = inner ℝ ((fderiv ℝ t (t.symm y)).adjoint η)
            (EuclideanSpace.single j 1) := hadj.symm
        _ = _ := by
          simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) j 1
            ((fderiv ℝ t (t.symm y)).adjoint η)
    have h_old : L.chart (c.symm y) ∈
        symbolChartDomain E F L.chart L.input.frame L.output.frame := by
      refine ⟨⟨L.chart.map_source hy.2.1.1, ?_⟩, ?_⟩
      · change L.chart.symm (L.chart (c.symm y)) ∈ L.input.frame.baseSet
        simpa only [L.chart.left_inv hy.2.1.1] using hy.2.1.2
      · change L.chart.symm (L.chart (c.symm y)) ∈ L.output.frame.baseSet
        simpa only [L.chart.left_inv hy.2.1.1] using hy.2.2
    have hchange := globalSymbolInChart_transition E F L.globalSymbolFunction L.chart c
      L.chart_mem_atlas hc L.input.frame e L.output.frame f (c.symm y)
      hy.2.1.1 (c.map_target hy.1.1.1) ⟨hy.2.1.2, hy.1.1.2⟩ ⟨hy.2.2, hy.1.2⟩
      (covectorFromChart c (c.symm y) η)
    rw [covectorInChart_covectorFromChart c hc (c.symm y) (c.map_target hy.1.1.1) η,
      c.right_inv hy.1.1.1,
      L.globalSymbolInChart_globalSymbolFunction _ _ h_old, hfreq] at hchange
    exact hchange.symm
  · -- The complement of the compact base support is open, and the original symbol is zero there.
    let V := U ∩ c.symm ⁻¹' Kᶜ
    have hV : IsOpen V :=
      (c.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU
        hK.isClosed.isOpen_compl
    refine ⟨V, hV, ⟨hz, hzK⟩, Set.inter_subset_left,
      congrSymbol hV 0 p (isSymbol_zero V m) ?_⟩
    intro y hy η
    change 0 = globalSymbolInChart E F L.globalSymbolFunction c e f y η
    simp only [globalSymbolInChart, hzero (c.symm y) hy.2,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]

/-- The exact symbol in a second chart has the transported leading class.
This private adapter retains the original two cutoff supports and both frames. -/
private theorem exists_localized_symbol
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
    [IsSmoothComplexBundle (n := n) (r := r) E]
    [IsSmoothComplexBundle (n := n) (r := q) F]
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (hbase : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
      interior {z | A.cutoff z = 1})
    (hoverlap : tsupport A.cutoff ⊆ c.symm ⁻¹'
      (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) :
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    ∃ p : SymbolFunction n r q, IsSymbol Set.univ m p ∧
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) z,
        quantize p u z = B.localize hc (L.toLinearMap (A.extend hc u)) z) ∧
      IsSymbol (symbolChartDomain E F c A.frame B.frame ∩ c.symm ⁻¹'
        (L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet)) (m - 1)
        (p - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) := by
  classical
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  let V := symbolChartDomain E F c A.frame B.frame ∩ c.symm ⁻¹' D
  have hV : IsOpen V :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_symbolChartDomain E F c A.frame B.frame)
      ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  have hKD : L.chart.symm '' K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
        L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
    · exact ⟨⟨L.chart.map_target (L.input.support_subset hz).1,
        (L.input.support_subset hz).2⟩, L.input_support_in_output_frame hz⟩
  let t : OpenPartialHomeomorph X X := L.chart.symm.trans c
  have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have ht : ContDiffOn ℝ ∞ t t.source := by
    intro y hy
    exact (((contMDiffAt_of_mem_maximalAtlas hcM hy.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1)).contDiffAt).contDiffWithinAt
  have hts : ContDiffOn ℝ ∞ t.symm t.target := by
    intro y hy
    exact (((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y
      (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1)).contDiffAt).contDiffWithinAt
  have hKt : K ⊆ t.source := by
    intro z hz
    have hb := hbase ⟨z, hz, rfl⟩
    exact ⟨by
      rcases hz with hz | hz
      · exact (L.output.support_subset hz).1
      · exact (L.input.support_subset hz).1, hb.1.1⟩
  have hVt : V ⊆ t.target := fun z hz ↦ ⟨hz.1.1.1, hz.2.1.1⟩
  have htarget : IsCompact (t '' K) := hK.image_of_continuousOn (t.continuousOn.mono hKt)
  have htargetOne : t '' K ⊆ interior {z | A.cutoff z = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hone ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩
  -- Choose the auxiliary source cutoff to be one on a whole neighborhood of the support.
  obtain ⟨O, hOo, hKO, hOt, hOc⟩ :=
    exists_open_between_and_isCompact_closure hK t.open_source hKt
  obtain ⟨O', hO'o, hOO', hO't, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc t.open_source hOt
  obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
  have hcχ : HasCompactSupport χ := by simpa [HasCompactSupport, hχsupport] using hO'c
  have hχt : tsupport χ ⊆ t.source := by rwa [hχsupport]
  have hχone : K ⊆ interior {z | χ z = 1} := by
    intro z hz
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hz⟩
    intro w hw
    exact (honeχ w).mp (subset_closure hw)
  let p₀ := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp₀ : IsSymbol univ m p₀ := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff L.output.compact_support L.input.compact_support
  have hP₀ : ∀ u z, L.coordinateOperator u z = quantize p₀ u z :=
    L.coordinateOperator_eq_quantize
  let P := coordinatePushforward t ht hts χ A.cutoff hχ hcχ hχt
    A.smooth_cutoff A.compact_support (hAV.trans hVt) L.coordinateOperator
  obtain ⟨s, hs, hPs, hrem⟩ := exists_symbol_coordinatePushforward t ht hts χ A.cutoff
    hχ hcχ hχt A.smooth_cutoff A.compact_support (hAV.trans hVt) m p₀ hp₀
    L.coordinateOperator hP₀ K hK hKt L.hasOperatorSupport_coordinateOperator
    hχone htargetOne
  have hPK : HasOperatorSupport (t '' K) P := hasOperatorSupport_coordinatePushforward
    t ht hts χ A.cutoff hχ hcχ hχt A.smooth_cutoff A.compact_support (hAV.trans hVt)
    L.coordinateOperator K hK hKt L.hasOperatorSupport_coordinateOperator
  let Fout : X → EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
    fun z ↦ L.output.frame.coordChangeL ℂ B.frame (c.symm z)
  let Finp : X → EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin r) :=
    fun z ↦ L.input.frame.coordChangeL ℂ A.frame (c.symm z)
  have hcV : ContMDiffOn I I ∞ c.symm V := by
    intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1.1.1).contMDiffWithinAt
  have hFout : ContDiffOn ℝ ∞ (fun z ↦ (Fout z).toContinuousLinearMap) V :=
    contDiffOn_coordChangeL_comp F L.output.frame B.frame V c.symm hcV
      (fun z hz ↦ ⟨hz.2.2, hz.1.2⟩)
  have hFinp : ContDiffOn ℝ ∞ (fun z ↦ (Finp z).symm.toContinuousLinearMap) V :=
    contDiffOn_symm_coordChangeL_comp E L.input.frame A.frame V c.symm hcV
      (fun z hz ↦ ⟨hz.2.1.2, hz.1.1.2⟩)
  let p := frameChangeSymbol Fout Finp A.cutoff s
  have hp : IsSymbol univ m p := isSymbol_frameChangeSymbol V hV Fout Finp hFout hFinp
    A.cutoff A.smooth_cutoff A.compact_support hAV m s hs
  let Tin := matrixMultiplierCLM (cutoffMatrix A.cutoff
    (fun z ↦ (Finp z).symm.toContinuousLinearMap))
    (contDiff_cutoffMatrix V hV _ hFinp A.cutoff A.smooth_cutoff hAV)
    (hasCompactSupport_cutoffMatrix A.cutoff _ A.compact_support)
  have hTin (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      Tin u z = A.cutoff z • (Finp z).symm (u z) := by
    rw [matrixMultiplierCLM_apply]
    rfl
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun w ↦ (L.input.cutoff w : ℂ))
          (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) =
        L.input.localize L.chart_mem_atlas (A.extend hc u) := by
    apply SchwartzMap.ext
    intro w
    have hgrowth : (fun w ↦ (L.input.cutoff w : ℂ)).HasTemperateGrowth :=
      (L.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, cutoffPullbackCLM_apply, hTin]
    by_cases hw : w ∈ tsupport L.input.cutoff
    · have hwK : w ∈ K := Or.inr hw
      have hwt := hKt hwK
      have hbasew := hbase ⟨w, hwK, rfl⟩
      have hχw : χ w = 1 := interior_subset (s := {z : X | χ z = 1}) (hχone hwK)
      have hwchart : w ∈ L.chart.target := hwt.1
      have hcw : c.symm (t w) = L.chart.symm w := c.left_inv hbasew.1.1
      change (L.input.cutoff w : ℂ) •
          (χ w • (A.cutoff (t w) • (Finp (t w)).symm (u (t w)))) =
        L.input.localizedFunction (A.extend hc u) w
      rw [hχw, one_smul]
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left hwchart, sectionInChart,
        BundleChartCutoff.extend, BundleChartCutoff.extendedFunction, ite_eq_left hbasew.1.1]
      rw [show Finp (t w) = L.input.frame.coordChangeL ℂ A.frame (L.chart.symm w) from
        congrArg (fun x ↦ L.input.frame.coordChangeL ℂ A.frame x) hcw]
      rw [L.input.frame.symm_coordChangeL A.frame ⟨hbasew.1.2,
        (L.input.support_subset hw).2⟩]
      rw [A.frame.coordChangeL_apply L.input.frame ⟨hbasew.1.2,
        (L.input.support_subset hw).2⟩, A.frame.symmL_apply hbasew.1.2]
      change (L.input.cutoff w : ℂ) •
          (A.cutoff (t w) • (L.input.frame.linearEquivAt ℂ _
            (L.input.support_subset hw).2)
              ((A.frame.linearEquivAt ℂ _ hbasew.1.2).symm (u (t w)))) =
        (L.input.cutoff w : ℂ) •
          (L.input.frame.linearEquivAt ℂ _ (L.input.support_subset hw).2)
            ((A.cutoff (t w) : ℂ) •
              (A.frame.linearEquivAt ℂ _ hbasew.1.2).symm (u (t w)))
      rw [map_smul]
      simp only [Complex.coe_smul]
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  have happly : ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) z,
      quantize p u z = B.localize hc (L.toLinearMap (A.extend hc u)) z := by
    intro u z
    rw [show quantize p u z = frameChangeOperator V hV Fout Finp hFout hFinp
      A.cutoff A.smooth_cutoff A.compact_support hAV P u z from
        quantize_frameChangeSymbol V hV Fout Finp hFout hFinp A.cutoff
          A.smooth_cutoff A.compact_support hAV P m s hs hPs u z]
    change matrixMultiplierCLM _ _ _ (P (Tin u)) z = _
    rw [matrixMultiplierCLM_apply]
    by_cases hz : z ∈ tsupport A.cutoff
    · have hzV := hAV hz
      have hzt := hVt hzV
      rw [show P (Tin u) z = L.coordinateOperator
        (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) (t.symm z) from
          coordinatePushforward_apply t ht hts χ A.cutoff hχ hcχ hχt
            A.smooth_cutoff A.compact_support (hAV.trans hVt) L.coordinateOperator K hKt
            L.hasOperatorSupport_coordinateOperator
            (fun w hw ↦ interior_subset (s := {z : X | A.cutoff z = 1}) (htargetOne hw))
            (Tin u) z hzt]
      rw [L.coordinateOperator_apply, hinput]
      change A.cutoff z • (Fout z)
          (L.output.cutoff (L.chart (c.symm z)) •
            L.operator (L.input.localize L.chart_mem_atlas (A.extend hc u))
              (L.chart (c.symm z))) = B.localizedFunction (L.toLinearMap (A.extend hc u)) z
      change A.cutoff z • (Fout z) _ =
        if z ∈ c.target then (B.cutoff z : ℂ) •
          (B.frame ⟨c.symm z, L.output.extendedFunction
            (L.operator (L.input.localize L.chart_mem_atlas (A.extend hc u))) (c.symm z)⟩).2
        else 0
      have hzc : z ∈ c.target := hzV.1.1.1
      have hzd : c.symm z ∈ L.chart.source := hzV.2.1.1
      rw [ite_eq_left hzc, BundleChartCutoff.extendedFunction, ite_eq_left hzd, ← hAB]
      rw [show Fout z = L.output.frame.coordChangeL ℂ B.frame (c.symm z) from rfl,
        L.output.frame.coordChangeL_apply B.frame ⟨hzV.2.2, hzV.1.2⟩,
        L.output.frame.symmL_apply hzV.2.2]
      change A.cutoff z • (B.frame.linearEquivAt ℂ _ hzV.1.2)
          ((L.output.frame.linearEquivAt ℂ _ hzV.2.2).symm
            (L.output.cutoff (L.chart (c.symm z)) • _)) =
        (A.cutoff z : ℂ) • (B.frame.linearEquivAt ℂ _ hzV.1.2)
          ((L.output.cutoff (L.chart (c.symm z)) : ℂ) •
            (L.output.frame.linearEquivAt ℂ _ hzV.2.2).symm _)
      rw [← Complex.coe_smul (L.output.cutoff (L.chart (c.symm z))), map_smul]
      simp only [Complex.coe_smul]
    · have hAz : A.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hBz : B.cutoff z = 0 := by rwa [← hAB]
      simp [cutoffMatrix, BundleChartCutoff.localize, BundleChartCutoff.localizedFunction, hAz, hBz]
  -- Coordinate change, frame change, and cutoff reduction each contribute one lower order.
  let pdiag : SymbolFunction n r q := fun z ξ ↦
    ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z ξ
  have hdiag : IsSymbol univ (m - 1) (p₀ - pdiag) := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero,
      cutoffAmplitude, p₀, pdiag, Complex.coe_smul] using h
  have h₁ : IsSymbol V (m - 1) (p - frameSymbol Fout Finp s) :=
    isSymbol_frameChangeSymbol_sub V hV Fout Finp hFout hFinp A.cutoff
      A.smooth_cutoff A.compact_support hAV P m s hs hPs (t '' K) htarget.isClosed
      hPK htargetOne
  have h₂ := isSymbol_frameSymbol V hV Fout Finp hFout hFinp (m - 1)
    (s - cotangentSymbol t p₀) (hrem.restrict hVt)
  have h₃ := isSymbol_frameSymbol V hV Fout Finp hFout hFinp (m - 1)
    (cotangentSymbol t (p₀ - pdiag))
      ((isSymbol_cotangentSymbol t ht hts (m - 1) (p₀ - pdiag)
        (hdiag.restrict (Set.subset_univ _))).restrict hVt)
  have htotal : IsSymbol V (m - 1)
      (p - frameSymbol Fout Finp (cotangentSymbol t pdiag)) := by
    convert IsSymbol.add hV (IsSymbol.add hV h₁ h₂) h₃ using 1
    ext z ξ v
    simp only [Pi.add_apply, Pi.sub_apply, frameSymbol, matrixSymbol, cotangentSymbol,
      add_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel_nf
  have hsame (y : X) (hy : y ∈ V) (η : X) :
      frameSymbol Fout Finp (cotangentSymbol t pdiag) y η =
        globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame y η := by
    -- The covector is transformed by the derivative of this very chart transition.
    have hfreq : covectorInChart L.chart (c.symm y)
        (covectorFromChart c (c.symm y) η) =
          (fderiv ℝ t (t.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (L.chart (c.symm y))
        (by
          simpa only [L.chart.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hy.1.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hdM (L.chart.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [L.chart.left_inv hsource] at hcomp
      have htcomp : fderiv ℝ t (t.symm y) =
          (mfderiv I I c (c.symm y)).comp
            (mfderiv I I L.chart.symm (L.chart (c.symm y))) := hcomp
      ext j
      change inner ℝ η ((mfderiv I I c (c.symm y))
          ((mfderiv I I L.chart.symm (L.chart (c.symm y)))
            (EuclideanSpace.single j 1))) =
        ((fderiv ℝ t (t.symm y)).adjoint η) j
      have hadj := (fderiv ℝ t (t.symm y)).adjoint_inner_left
        (EuclideanSpace.single j 1) η
      calc
        _ = inner ℝ η ((fderiv ℝ t (t.symm y)) (EuclideanSpace.single j 1)) := by
          rw [htcomp]
          rfl
        _ = inner ℝ ((fderiv ℝ t (t.symm y)).adjoint η)
            (EuclideanSpace.single j 1) := hadj.symm
        _ = _ := by
          simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) j 1
            ((fderiv ℝ t (t.symm y)).adjoint η)
    have h_old : L.chart (c.symm y) ∈
        symbolChartDomain E F L.chart L.input.frame L.output.frame := by
      refine ⟨⟨L.chart.map_source hy.2.1.1, ?_⟩, ?_⟩
      · change L.chart.symm (L.chart (c.symm y)) ∈ L.input.frame.baseSet
        simpa only [L.chart.left_inv hy.2.1.1] using hy.2.1.2
      · change L.chart.symm (L.chart (c.symm y)) ∈ L.output.frame.baseSet
        simpa only [L.chart.left_inv hy.2.1.1] using hy.2.2
    have hchange := globalSymbolInChart_transition E F L.globalSymbolFunction L.chart c
      L.chart_mem_atlas hc L.input.frame A.frame L.output.frame B.frame (c.symm y)
      hy.2.1.1 (c.map_target hy.1.1.1) ⟨hy.2.1.2, hy.1.1.2⟩ ⟨hy.2.2, hy.1.2⟩
      (covectorFromChart c (c.symm y) η)
    rw [covectorInChart_covectorFromChart c hc (c.symm y) (c.map_target hy.1.1.1) η,
      c.right_inv hy.1.1.1,
      L.globalSymbolInChart_globalSymbolFunction _ _ h_old, hfreq] at hchange
    exact hchange.symm
  refine ⟨p, hp, happly, ?_⟩
  -- Equality on the open overlap identifies all original mixed derivatives there.
  refine ⟨htotal.1.congr (fun z hz ↦ ?_), ?_⟩
  · change p z.1 z.2 - _ = p z.1 z.2 - _
    rw [hsame z.1 hz.1 z.2]
  · intro C hCV hC i j
    obtain ⟨R, hR, hbound⟩ := htotal.2 C hCV hC i j
    refine ⟨R, hR, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j
        ((p - frameSymbol Fout Finp (cotangentSymbol t pdiag)) y) ξ) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ j
        ((p - globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame) y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      congr 1
      funext η
      exact congrArg (fun v ↦ p y η - v) (hsame y hy η)
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- The actual order-m symbol of a local piece, before taking its principal class. -/
def globalSymbol : globalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  ⟨L.globalSymbolFunction, L.isGlobalSymbol_globalSymbolFunction⟩

end PseudodifferentialPiece

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

omit [MeasurableSpace M] [BorelSpace M] in
/-- A finite family has exact symbols in common coordinates after one two-sided cutoff.
The original global representatives are retained on a smaller neighborhood. -/
private theorem exists_common_local_symbols {m : ℝ} {ι : Type*} [Finite ι]
    (J : ι → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F c e f) :
    ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
        (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
        (V : Set (EuclideanSpace ℝ (Fin n))) (p : ι → SymbolFunction n r q),
      IsOpen V ∧ z ∈ V ∧ V ⊆ symbolChartDomain E F c e f ∧
        (∀ j, IsSymbol Set.univ m (p j)) ∧
        (∀ j, IsSymbol V (m - 1)
          (p j - globalSymbolInChart E F (J j).globalSymbolFunction c e f)) ∧
        ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) y,
          quantize (p j) u y = B.localize hc
            (smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
              ((J j).toLinearMap
                (smoothSectionMul E (fun x ↦ (χ x : ℂ))
                  (Complex.ofRealCLM.contMDiff.comp hχ) (A.extend hc u)))) y := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let x := c.symm z
  let D := c.source ∩ e.baseSet ∩ f.baseSet
  let D' (j : ι) := (J j).chart.source ∩ (J j).input.frame.baseSet ∩
    (J j).output.frame.baseSet
  let K (j : ι) := (J j).chart.symm ''
    (tsupport (J j).output.cutoff ∪ tsupport (J j).input.cutoff)
  have hK (j : ι) : IsCompact (K j) :=
    ((J j).output.compact_support.union (J j).input.compact_support).image_of_continuousOn
      ((J j).chart.continuousOn_symm.mono (by
        intro y hy
        rcases hy with hy | hy
        · exact ((J j).output.support_subset hy).1
        · exact ((J j).input.support_subset hy).1))
  have hKD (j : ι) : K j ⊆ D' j := by
    rintro y ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · exact ⟨⟨(J j).chart.map_target ((J j).output.support_subset hw).1,
        (J j).output_support_in_input_frame hw⟩, ((J j).output.support_subset hw).2⟩
    · exact ⟨⟨(J j).chart.map_target ((J j).input.support_subset hw).1,
        ((J j).input.support_subset hw).2⟩, (J j).input_support_in_output_frame hw⟩
  -- One finite intersection handles every active piece and removes every inactive piece.
  let W' (j : ι) := if x ∈ K j then D' j else (K j)ᶜ
  have hW' (j : ι) : IsOpen (W' j) := by
    by_cases hj : x ∈ K j
    · simpa only [W', ite_eq_left hj] using
        (((J j).chart.open_source.inter (J j).input.frame.open_baseSet).inter
          (J j).output.frame.open_baseSet)
    · simpa only [W', ite_eq_right hj] using (hK j).isClosed.isOpen_compl
  have hxW' (j : ι) : x ∈ W' j := by
    by_cases hj : x ∈ K j
    · simpa only [W', ite_eq_left hj] using hKD j hj
    · simpa only [W', ite_eq_right hj, mem_compl_iff] using hj
  let W := D ∩ ⋂ j, W' j
  have hW : IsOpen W := ((c.open_source.inter e.open_baseSet).inter f.open_baseSet).inter
    (isOpen_iInter_of_finite hW')
  have hxW : x ∈ W := ⟨⟨⟨c.map_target hz.1.1, hz.1.2⟩, hz.2⟩, mem_iInter.mpr hxW'⟩
  obtain ⟨C, hC, hxC, hCW⟩ := exists_compact_subset hW hxW
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := I) (n := ⊤) isClosed_singleton
    (show ({x} : Set M) ⊆ interior C from singleton_subset_iff.mpr hxC)
  have hχC : tsupport χ ⊆ C := by
    apply closure_minimal ?_ hC.isClosed
    intro y hy
    by_contra hyC
    exact hy (hχzero y hyC)
  have hcχ : HasCompactSupport χ := hC.of_isClosed_subset (isClosed_tsupport _) hχC
  have hχW : tsupport χ ⊆ W := hχC.trans hCW
  have hχD : tsupport χ ⊆ D := hχW.trans inter_subset_left
  have hxOne : x ∈ interior {y | χ y = 1} := by
    apply mem_interior_iff_mem_nhds.mpr
    change ∀ᶠ y in nhds x, χ y = 1
    simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hχone
  let T := c.target ∩ c.symm ⁻¹' W
  have hT : IsOpen T := c.isOpen_inter_preimage_symm hW
  have himage : c '' tsupport χ ⊆ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨c.map_source (hχD hy).1.1, by
      change c.symm (c y) ∈ W
      rw [c.left_inv (hχD hy).1.1]
      exact hχW hy⟩
  have hcimage : IsCompact (c '' tsupport χ) := hcχ.image_of_continuousOn
    (c.continuousOn.mono (fun y hy ↦ (hχD hy).1.1))
  -- The common chart cutoff is one near the entire new support and remains in W.
  obtain ⟨O, hOo, hKO, hOT, hOc⟩ :=
    exists_open_between_and_isCompact_closure hcimage hT himage
  obtain ⟨O', hO'o, hOO', hO'T, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc hT hOT
  obtain ⟨ρ, hρ, _, hsρ, honeρ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hρsupport : tsupport ρ = closure O' := congrArg closure hsρ
  have hcρ : HasCompactSupport ρ := by simpa [HasCompactSupport, hρsupport] using hO'c
  have hρT : tsupport ρ ⊆ T := by rwa [hρsupport]
  have hρone : c '' tsupport χ ⊆ interior {y | ρ y = 1} := by
    intro y hy
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hy⟩
    intro w hw
    exact (honeρ w).mp (subset_closure hw)
  let A : BundleChartCutoff (r := r) E c :=
    { frame := e
      frame_mem_atlas := inferInstance
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.1.2⟩ }
  let B : BundleChartCutoff (r := q) F c :=
    { frame := f
      frame_mem_atlas := inferInstance
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.2⟩ }
  let V := c.target ∩ c.symm ⁻¹' (W ∩ interior {y | χ y = 1})
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (hW.inter isOpen_interior)
  have hzV : z ∈ V := ⟨hz.1.1, hxW, hxOne⟩
  have hVU : V ⊆ symbolChartDomain E F c e f :=
    fun y hy ↦ ⟨⟨hy.1, hy.2.1.1.1.2⟩, hy.2.1.1.2⟩
  let Tin := smoothSectionMul (n := n) (r := r) E (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  let Tout := smoothSectionMul (n := n) (r := q) F (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  -- Absorb the same global cutoff into the existing input and output coordinate cutoffs.
  have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ atlas X M)
      (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
      ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport a
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) (hs hy)
      exact ha.contDiffAt.mul ((χ.contMDiff.contMDiffAt.comp y hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  let input (j : ι) : BundleChartCutoff (r := r) E (J j).chart :=
    { (J j).input with
      cutoff := fun y ↦ (J j).input.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).input.smooth_cutoff
        (fun y hy ↦ ((J j).input.support_subset hy).1)
      compact_support := (J j).input.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).input.support_subset }
  let output (j : ι) : BundleChartCutoff (r := q) F (J j).chart :=
    { (J j).output with
      cutoff := fun y ↦ (J j).output.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).output.smooth_cutoff
        (fun y hy ↦ ((J j).output.support_subset hy).1)
      compact_support := (J j).output.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).output.support_subset }
  let R (j : ι) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { J j with
      input := input j
      output := output j
      input_support_in_output_frame :=
        tsupport_mul_subset_left.trans (J j).input_support_in_output_frame
      output_support_in_input_frame :=
        tsupport_mul_subset_left.trans (J j).output_support_in_input_frame }
  have hinput (j : ι) (u : smoothSections (n := n) (r := r) E) :
      (input j).localize (J j).chart_mem_atlas u =
        (J j).input.localize (J j).chart_mem_atlas (Tin u) := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ tsupport (J j).input.cutoff
    · have hyc := ((J j).input.support_subset hy).1
      have hyf := ((J j).input.support_subset hy).2
      let := (J j).input.frame_mem_atlas
      change (input j).localizedFunction u y = (J j).input.localizedFunction (Tin u) y
      simp only [BundleChartCutoff.localizedFunction, hyc, ↓reduceIte]
      dsimp only [input]
      change _ = ((J j).input.cutoff y : ℂ) •
        ((J j).input.frame.linearEquivAt ℂ ((J j).chart.symm y) hyf)
          ((χ ((J j).chart.symm y) : ℂ) • u.val ((J j).chart.symm y))
      rw [map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        input, image_eq_zero_of_notMem_tsupport hy]
  have houtput (j : ι) (v : 𝓢(X, EuclideanSpace ℂ (Fin q))) :
      (output j).extend (J j).chart_mem_atlas v =
        Tout ((J j).output.extend (J j).chart_mem_atlas v) := by
    apply Subtype.ext
    funext y
    change (output j).extendedFunction v y = (χ y : ℂ) • (J j).output.extendedFunction v y
    by_cases hy : y ∈ (J j).chart.source
    · simp only [BundleChartCutoff.extendedFunction, hy, ↓reduceIte]
      dsimp only [output]
      rw [(J j).chart.left_inv hy, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [BundleChartCutoff.extendedFunction, hy]
  have hpiece (j : ι) : (R j).toLinearMap = Tout.comp ((J j).toLinearMap.comp Tin) := by
    apply LinearMap.ext
    intro u
    change (output j).extend (J j).chart_mem_atlas
      ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = _
    rw [hinput, houtput]
    rfl
  have hproductSupport (d : OpenPartialHomeomorph M X) (a : X → ℝ)
      (hs : tsupport a ⊆ d.target) :
      d.symm '' tsupport (fun y ↦ a y * χ (d.symm y)) ⊆ tsupport χ := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hout
    have hy' : y ∈ d.target := hs (tsupport_mul_subset_left hy)
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
      (d.continuousOn_symm.continuousAt (d.open_target.mem_nhds hy'))
    have hprod : (fun w ↦ a w * χ (d.symm w)) =ᶠ[nhds y] 0 := by
      filter_upwards [hzero] with w hw
      simp only [Function.comp_def, Pi.zero_apply] at hw
      simp [hw]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hy
  have hRsupp (j : ι) : (R j).chart.symm ''
      (tsupport (R j).output.cutoff ∪ tsupport (R j).input.cutoff) ⊆ tsupport χ := by
    rw [image_union]
    apply union_subset
    · exact hproductSupport _ _ (fun y hy ↦ ((J j).output.support_subset hy).1)
    · exact hproductSupport _ _ (fun y hy ↦ ((J j).input.support_subset hy).1)
  have hglobal (j : ι) (y : M) (hy : χ y = 1) (ξ) :
      (R j).globalSymbolFunction y ξ = (J j).globalSymbolFunction y ξ := by
    let := (J j).input.frame_mem_atlas
    let := (J j).output.frame_mem_atlas
    unfold PseudodifferentialPiece.globalSymbolFunction
    dsimp only [R, input, output]
    split_ifs with hdomain
    · rw [(J j).chart.left_inv hdomain.1.1, hy]
      simp
    · rfl
  -- Equality on an open set retains the complete mixed-derivative symbol estimates.
  have congrSymbol (a b : SymbolFunction n r q) (ha : IsSymbol V (m - 1) a)
      (hab : ∀ y ∈ V, ∀ η, a y η = b y η) : IsSymbol V (m - 1) b := by
    refine ⟨ha.1.congr (fun w hw ↦ (hab w.1 hw.1 w.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := ha.2 C hCV hC i j
    refine ⟨B, hB, fun y hy η ↦ ?_⟩
    have hnear : (fun w ↦ iteratedFDeriv ℝ j (a w) η) =ᶠ[nhds y]
        (fun w ↦ iteratedFDeriv ℝ j (b w) η) := by
      filter_upwards [hV.mem_nhds (hCV hy)] with w hw
      rw [funext (hab w hw)]
    change ‖iteratedFDeriv ℝ i _ y‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound y hy η
  have hsymbols (j : ι) : ∃ p : SymbolFunction n r q, IsSymbol Set.univ m p ∧
      IsSymbol V (m - 1) (p - globalSymbolInChart E F (J j).globalSymbolFunction c e f) ∧
      ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) y,
        quantize p u y = B.localize hc (Tout ((J j).toLinearMap (Tin (A.extend hc u)))) y := by
    by_cases hj : x ∈ K j
    · have hactive : W ⊆ D' j := by
        intro y hy
        simpa only [W', ite_eq_left hj] using mem_iInter.mp hy.2 j
      obtain ⟨p, hp, hpaction, hplower⟩ := (R j).exists_localized_symbol c hc A B rfl
        ((hRsupp j).trans hχD)
        ((image_mono (hRsupp j)).trans hρone)
        (fun y hy ↦ hactive (hρT hy).2)
      refine ⟨p, hp, ?_, ?_⟩
      · apply congrSymbol _ _ (hplower.restrict (fun y hy ↦ ⟨hVU hy, hactive hy.2.1⟩))
        intro y hy η
        have hχy : χ (c.symm y) = 1 := by
          have hmem : c.symm y ∈ {w | χ w = 1} := interior_subset hy.2.2
          exact hmem
        simp only [Pi.sub_apply, globalSymbolInChart, hglobal j _ hχy]
        rfl
      · intro u y
        rw [hpaction, hpiece]
        rfl
    · have hzeroInput : (input j).cutoff = 0 := by
        funext y
        by_cases hy : (J j).input.cutoff y = 0
        · simp [input, hy]
        · have hyK : (J j).chart.symm y ∈ K j :=
            ⟨y, Or.inr (subset_tsupport _ hy), rfl⟩
          have hχy : χ ((J j).chart.symm y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by
              intro hyχ
              have hnot := mem_iInter.mp (hχW hyχ).2 j
              exact (show (J j).chart.symm y ∉ K j by
                simpa only [W', ite_eq_right hj, mem_compl_iff] using hnot) hyK)
          simp [input, hχy]
      have hRzero : (R j).toLinearMap = 0 := by
        apply LinearMap.ext
        intro u
        have hin : (input j).localize (J j).chart_mem_atlas u = 0 := by
          apply SchwartzMap.ext
          intro y
          change (input j).localizedFunction u y = 0
          simp [BundleChartCutoff.localizedFunction, hzeroInput]
        change (output j).extendLinearMap (J j).chart_mem_atlas
          ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = 0
        rw [hin, map_zero, map_zero]
      refine ⟨0, isSymbol_zero _ _, ?_, ?_⟩
      · apply congrSymbol 0 _ (isSymbol_zero _ _)
        intro y hy η
        have hyK : c.symm y ∉ K j := by
          simpa only [W', ite_eq_right hj, mem_compl_iff] using mem_iInter.mp hy.2.1.2 j
        have hzero := (J j).globalSymbolFunction_eq_zero (c.symm y)
          (fun h ↦ hyK ((image_mono (fun w hw ↦ Or.inl hw.1)) h))
        simp [globalSymbolInChart, hzero]
      · intro u y
        change quantize 0 u y = B.localize hc
          ((Tout.comp ((J j).toLinearMap.comp Tin)) (A.extend hc u)) y
        rw [← hpiece, hRzero]
        change quantize 0 u y = (B.localizeLinearMap hc) 0 y
        simp [quantize]
  choose p hp hplower hpaction using hsymbols
  exact ⟨χ, χ.contMDiff, A, B, V, p, hV, hzV, hVU, hp, hplower, hpaction⟩

omit [MeasurableSpace M] [BorelSpace M] in
/-- A common local normal form retains the cutoffs needed to reconstruct the same section maps.
The common cutoff equals one near the specified point; the two chart cutoffs agree and
are one on its support. These controls allow finite localization of order bounds and
composition without choosing unrelated symbols or changing the original operators. -/
theorem exists_common_local_symbols_with_cutoffs {m : ℝ} {ι : Type*} [Finite ι]
    (J : ι → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ symbolChartDomain E F c e f) :
    ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
        (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
        (V : Set (EuclideanSpace ℝ (Fin n))) (p : ι → SymbolFunction n r q),
      HasCompactSupport χ ∧ tsupport χ ⊆ c.source ∩ e.baseSet ∩ f.baseSet ∧
        A.frame = e ∧ B.frame = f ∧ A.cutoff = B.cutoff ∧
        (∀ y ∈ c '' tsupport χ, A.cutoff y = 1) ∧
        (∀ y ∈ V, χ (c.symm y) = 1) ∧
        IsOpen V ∧ z ∈ V ∧ V ⊆ symbolChartDomain E F c e f ∧
        (∀ j, IsSymbol Set.univ m (p j)) ∧
        (∀ j, IsSymbol V (m - 1)
          (p j - globalSymbolInChart E F (J j).globalSymbolFunction c e f)) ∧
        ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) y,
          quantize (p j) u y = B.localize hc
            (smoothSectionMul F (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
              ((J j).toLinearMap
                (smoothSectionMul E (fun x ↦ (χ x : ℂ))
                  (Complex.ofRealCLM.contMDiff.comp hχ) (A.extend hc u)))) y := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let x := c.symm z
  let D := c.source ∩ e.baseSet ∩ f.baseSet
  let D' (j : ι) := (J j).chart.source ∩ (J j).input.frame.baseSet ∩
    (J j).output.frame.baseSet
  let K (j : ι) := (J j).chart.symm ''
    (tsupport (J j).output.cutoff ∪ tsupport (J j).input.cutoff)
  have hK (j : ι) : IsCompact (K j) :=
    ((J j).output.compact_support.union (J j).input.compact_support).image_of_continuousOn
      ((J j).chart.continuousOn_symm.mono (by
        intro y hy
        rcases hy with hy | hy
        · exact ((J j).output.support_subset hy).1
        · exact ((J j).input.support_subset hy).1))
  have hKD (j : ι) : K j ⊆ D' j := by
    rintro y ⟨w, hw, rfl⟩
    rcases hw with hw | hw
    · exact ⟨⟨(J j).chart.map_target ((J j).output.support_subset hw).1,
        (J j).output_support_in_input_frame hw⟩, ((J j).output.support_subset hw).2⟩
    · exact ⟨⟨(J j).chart.map_target ((J j).input.support_subset hw).1,
        ((J j).input.support_subset hw).2⟩, (J j).input_support_in_output_frame hw⟩
  -- One finite intersection handles every active piece and removes every inactive piece.
  let W' (j : ι) := if x ∈ K j then D' j else (K j)ᶜ
  have hW' (j : ι) : IsOpen (W' j) := by
    by_cases hj : x ∈ K j
    · simpa only [W', ite_eq_left hj] using
        (((J j).chart.open_source.inter (J j).input.frame.open_baseSet).inter
          (J j).output.frame.open_baseSet)
    · simpa only [W', ite_eq_right hj] using (hK j).isClosed.isOpen_compl
  have hxW' (j : ι) : x ∈ W' j := by
    by_cases hj : x ∈ K j
    · simpa only [W', ite_eq_left hj] using hKD j hj
    · simpa only [W', ite_eq_right hj, mem_compl_iff] using hj
  let W := D ∩ ⋂ j, W' j
  have hW : IsOpen W := ((c.open_source.inter e.open_baseSet).inter f.open_baseSet).inter
    (isOpen_iInter_of_finite hW')
  have hxW : x ∈ W := ⟨⟨⟨c.map_target hz.1.1, hz.1.2⟩, hz.2⟩, mem_iInter.mpr hxW'⟩
  obtain ⟨C, hC, hxC, hCW⟩ := exists_compact_subset hW hxW
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := I) (n := ⊤) isClosed_singleton
    (show ({x} : Set M) ⊆ interior C from singleton_subset_iff.mpr hxC)
  have hχC : tsupport χ ⊆ C := by
    apply closure_minimal ?_ hC.isClosed
    intro y hy
    by_contra hyC
    exact hy (hχzero y hyC)
  have hcχ : HasCompactSupport χ := hC.of_isClosed_subset (isClosed_tsupport _) hχC
  have hχW : tsupport χ ⊆ W := hχC.trans hCW
  have hχD : tsupport χ ⊆ D := hχW.trans inter_subset_left
  have hxOne : x ∈ interior {y | χ y = 1} := by
    apply mem_interior_iff_mem_nhds.mpr
    change ∀ᶠ y in nhds x, χ y = 1
    simpa only [nhdsSet_singleton, Filter.EventuallyEq] using hχone
  let T := c.target ∩ c.symm ⁻¹' W
  have hT : IsOpen T := c.isOpen_inter_preimage_symm hW
  have himage : c '' tsupport χ ⊆ T := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨c.map_source (hχD hy).1.1, by
      change c.symm (c y) ∈ W
      rw [c.left_inv (hχD hy).1.1]
      exact hχW hy⟩
  have hcimage : IsCompact (c '' tsupport χ) := hcχ.image_of_continuousOn
    (c.continuousOn.mono (fun y hy ↦ (hχD hy).1.1))
  -- The common chart cutoff is one near the entire new support and remains in W.
  obtain ⟨O, hOo, hKO, hOT, hOc⟩ :=
    exists_open_between_and_isCompact_closure hcimage hT himage
  obtain ⟨O', hO'o, hOO', hO'T, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc hT hOT
  obtain ⟨ρ, hρ, _, hsρ, honeρ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hρsupport : tsupport ρ = closure O' := congrArg closure hsρ
  have hcρ : HasCompactSupport ρ := by simpa [HasCompactSupport, hρsupport] using hO'c
  have hρT : tsupport ρ ⊆ T := by rwa [hρsupport]
  have hρone : c '' tsupport χ ⊆ interior {y | ρ y = 1} := by
    intro y hy
    apply mem_interior.mpr
    refine ⟨O, ?_, hOo, hKO hy⟩
    intro w hw
    exact (honeρ w).mp (subset_closure hw)
  let A : BundleChartCutoff (r := r) E c :=
    { frame := e
      frame_mem_atlas := inferInstance
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.1.2⟩ }
  let B : BundleChartCutoff (r := q) F c :=
    { frame := f
      frame_mem_atlas := inferInstance
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.2⟩ }
  let V := c.target ∩ c.symm ⁻¹' (W ∩ interior {y | χ y = 1})
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (hW.inter isOpen_interior)
  have hzV : z ∈ V := ⟨hz.1.1, hxW, hxOne⟩
  have hVU : V ⊆ symbolChartDomain E F c e f :=
    fun y hy ↦ ⟨⟨hy.1, hy.2.1.1.1.2⟩, hy.2.1.1.2⟩
  let Tin := smoothSectionMul (n := n) (r := r) E (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  let Tout := smoothSectionMul (n := n) (r := q) F (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  -- Absorb the same global cutoff into the existing input and output coordinate cutoffs.
  have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ atlas X M)
      (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
      ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport a
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) (hs hy)
      exact ha.contDiffAt.mul ((χ.contMDiff.contMDiffAt.comp y hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  let input (j : ι) : BundleChartCutoff (r := r) E (J j).chart :=
    { (J j).input with
      cutoff := fun y ↦ (J j).input.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).input.smooth_cutoff
        (fun y hy ↦ ((J j).input.support_subset hy).1)
      compact_support := (J j).input.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).input.support_subset }
  let output (j : ι) : BundleChartCutoff (r := q) F (J j).chart :=
    { (J j).output with
      cutoff := fun y ↦ (J j).output.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).output.smooth_cutoff
        (fun y hy ↦ ((J j).output.support_subset hy).1)
      compact_support := (J j).output.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).output.support_subset }
  let R (j : ι) : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    { J j with
      input := input j
      output := output j
      input_support_in_output_frame :=
        tsupport_mul_subset_left.trans (J j).input_support_in_output_frame
      output_support_in_input_frame :=
        tsupport_mul_subset_left.trans (J j).output_support_in_input_frame }
  have hinput (j : ι) (u : smoothSections (n := n) (r := r) E) :
      (input j).localize (J j).chart_mem_atlas u =
        (J j).input.localize (J j).chart_mem_atlas (Tin u) := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ tsupport (J j).input.cutoff
    · have hyc := ((J j).input.support_subset hy).1
      have hyf := ((J j).input.support_subset hy).2
      let := (J j).input.frame_mem_atlas
      change (input j).localizedFunction u y = (J j).input.localizedFunction (Tin u) y
      simp only [BundleChartCutoff.localizedFunction, hyc, ↓reduceIte]
      dsimp only [input]
      change _ = ((J j).input.cutoff y : ℂ) •
        ((J j).input.frame.linearEquivAt ℂ ((J j).chart.symm y) hyf)
          ((χ ((J j).chart.symm y) : ℂ) • u.val ((J j).chart.symm y))
      rw [map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        input, image_eq_zero_of_notMem_tsupport hy]
  have houtput (j : ι) (v : 𝓢(X, EuclideanSpace ℂ (Fin q))) :
      (output j).extend (J j).chart_mem_atlas v =
        Tout ((J j).output.extend (J j).chart_mem_atlas v) := by
    apply Subtype.ext
    funext y
    change (output j).extendedFunction v y = (χ y : ℂ) • (J j).output.extendedFunction v y
    by_cases hy : y ∈ (J j).chart.source
    · simp only [BundleChartCutoff.extendedFunction, hy, ↓reduceIte]
      dsimp only [output]
      rw [(J j).chart.left_inv hy, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [BundleChartCutoff.extendedFunction, hy]
  have hpiece (j : ι) : (R j).toLinearMap = Tout.comp ((J j).toLinearMap.comp Tin) := by
    apply LinearMap.ext
    intro u
    change (output j).extend (J j).chart_mem_atlas
      ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = _
    rw [hinput, houtput]
    rfl
  have hproductSupport (d : OpenPartialHomeomorph M X) (a : X → ℝ)
      (hs : tsupport a ⊆ d.target) :
      d.symm '' tsupport (fun y ↦ a y * χ (d.symm y)) ⊆ tsupport χ := by
    rintro _ ⟨y, hy, rfl⟩
    by_contra hout
    have hy' : y ∈ d.target := hs (tsupport_mul_subset_left hy)
    have hzero := (notMem_tsupport_iff_eventuallyEq.mp hout).comp_tendsto
      (d.continuousOn_symm.continuousAt (d.open_target.mem_nhds hy'))
    have hprod : (fun w ↦ a w * χ (d.symm w)) =ᶠ[nhds y] 0 := by
      filter_upwards [hzero] with w hw
      simp only [Function.comp_def, Pi.zero_apply] at hw
      simp [hw]
    exact (notMem_tsupport_iff_eventuallyEq.mpr hprod) hy
  have hRsupp (j : ι) : (R j).chart.symm ''
      (tsupport (R j).output.cutoff ∪ tsupport (R j).input.cutoff) ⊆ tsupport χ := by
    rw [image_union]
    apply union_subset
    · exact hproductSupport _ _ (fun y hy ↦ ((J j).output.support_subset hy).1)
    · exact hproductSupport _ _ (fun y hy ↦ ((J j).input.support_subset hy).1)
  have hglobal (j : ι) (y : M) (hy : χ y = 1) (ξ) :
      (R j).globalSymbolFunction y ξ = (J j).globalSymbolFunction y ξ := by
    let := (J j).input.frame_mem_atlas
    let := (J j).output.frame_mem_atlas
    unfold PseudodifferentialPiece.globalSymbolFunction
    dsimp only [R, input, output]
    split_ifs with hdomain
    · rw [(J j).chart.left_inv hdomain.1.1, hy]
      simp
    · rfl
  -- Equality on an open set retains the complete mixed-derivative symbol estimates.
  have congrSymbol (a b : SymbolFunction n r q) (ha : IsSymbol V (m - 1) a)
      (hab : ∀ y ∈ V, ∀ η, a y η = b y η) : IsSymbol V (m - 1) b := by
    refine ⟨ha.1.congr (fun w hw ↦ (hab w.1 hw.1 w.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := ha.2 C hCV hC i j
    refine ⟨B, hB, fun y hy η ↦ ?_⟩
    have hnear : (fun w ↦ iteratedFDeriv ℝ j (a w) η) =ᶠ[nhds y]
        (fun w ↦ iteratedFDeriv ℝ j (b w) η) := by
      filter_upwards [hV.mem_nhds (hCV hy)] with w hw
      rw [funext (hab w hw)]
    change ‖iteratedFDeriv ℝ i _ y‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound y hy η
  have hsymbols (j : ι) : ∃ p : SymbolFunction n r q, IsSymbol Set.univ m p ∧
      IsSymbol V (m - 1) (p - globalSymbolInChart E F (J j).globalSymbolFunction c e f) ∧
      ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) y,
        quantize p u y = B.localize hc (Tout ((J j).toLinearMap (Tin (A.extend hc u)))) y := by
    by_cases hj : x ∈ K j
    · have hactive : W ⊆ D' j := by
        intro y hy
        simpa only [W', ite_eq_left hj] using mem_iInter.mp hy.2 j
      obtain ⟨p, hp, hpaction, hplower⟩ := (R j).exists_localized_symbol c hc A B rfl
        ((hRsupp j).trans hχD)
        ((image_mono (hRsupp j)).trans hρone)
        (fun y hy ↦ hactive (hρT hy).2)
      refine ⟨p, hp, ?_, ?_⟩
      · apply congrSymbol _ _ (hplower.restrict (fun y hy ↦ ⟨hVU hy, hactive hy.2.1⟩))
        intro y hy η
        have hχy : χ (c.symm y) = 1 := by
          have hmem : c.symm y ∈ {w | χ w = 1} := interior_subset hy.2.2
          exact hmem
        simp only [Pi.sub_apply, globalSymbolInChart, hglobal j _ hχy]
        rfl
      · intro u y
        rw [hpaction, hpiece]
        rfl
    · have hzeroInput : (input j).cutoff = 0 := by
        funext y
        by_cases hy : (J j).input.cutoff y = 0
        · simp [input, hy]
        · have hyK : (J j).chart.symm y ∈ K j :=
            ⟨y, Or.inr (subset_tsupport _ hy), rfl⟩
          have hχy : χ ((J j).chart.symm y) = 0 :=
            image_eq_zero_of_notMem_tsupport (by
              intro hyχ
              have hnot := mem_iInter.mp (hχW hyχ).2 j
              exact (show (J j).chart.symm y ∉ K j by
                simpa only [W', ite_eq_right hj, mem_compl_iff] using hnot) hyK)
          simp [input, hχy]
      have hRzero : (R j).toLinearMap = 0 := by
        apply LinearMap.ext
        intro u
        have hin : (input j).localize (J j).chart_mem_atlas u = 0 := by
          apply SchwartzMap.ext
          intro y
          change (input j).localizedFunction u y = 0
          simp [BundleChartCutoff.localizedFunction, hzeroInput]
        change (output j).extendLinearMap (J j).chart_mem_atlas
          ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = 0
        rw [hin, map_zero, map_zero]
      refine ⟨0, isSymbol_zero _ _, ?_, ?_⟩
      · apply congrSymbol 0 _ (isSymbol_zero _ _)
        intro y hy η
        have hyK : c.symm y ∉ K j := by
          simpa only [W', ite_eq_right hj, mem_compl_iff] using mem_iInter.mp hy.2.1.2 j
        have hzero := (J j).globalSymbolFunction_eq_zero (c.symm y)
          (fun h ↦ hyK ((image_mono (fun w hw ↦ Or.inl hw.1)) h))
        simp [globalSymbolInChart, hzero]
      · intro u y
        change quantize 0 u y = B.localize hc
          ((Tout.comp ((J j).toLinearMap.comp Tin)) (A.extend hc u)) y
        rw [← hpiece, hRzero]
        change quantize 0 u y = (B.localizeLinearMap hc) 0 y
        simp [quantize]
  choose p hp hplower hpaction using hsymbols
  refine ⟨χ, χ.contMDiff, A, B, V, p, hcχ, hχD, rfl, rfl, rfl, ?_, ?_,
    hV, hzV, hVU, hp, hplower, hpaction⟩
  · intro y hy
    exact interior_subset (s := {y | ρ y = 1}) (hρone hy)
  · intro y hy
    exact interior_subset (s := {y | χ y = 1}) hy.2.2

/-- Local representations differing by a smooth kernel determine the same global principal class. -/
theorem globalPrincipalSymbolClass_sum_eq_of_isSmoothingOperator (m : ℝ) (N N' : ℕ)
    (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (L' : Fin N' → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (h : IsSmoothingOperator μ ((∑ j, (L j).toLinearMap) - ∑ j, (L' j).toLinearMap)) :
    globalPrincipalSymbolClass E F m (∑ j, (L j).globalSymbol) =
      globalPrincipalSymbolClass E F m (∑ j, (L' j).globalSymbol) := by
  /- Localize both finite families using the same scalar cutoff and fixed chart/frame pair.
  The exact common-coordinate symbols differ from the original global representatives by
  order m-1. The same two-sided cutoff of the given smooth kernel represents their
  operator difference. Full-symbol injectivity identifies that difference with its
  smoothing kernel symbol; locality then gives the original quotient equality. -/
  classical
  rw [globalPrincipalSymbolClass_eq_iff]
  intro c hc e f _ _
  let X := EuclideanSpace ℝ (Fin n)
  let U := symbolChartDomain E F c e f
  have hU : IsOpen U := isOpen_symbolChartDomain E F c e f
  apply IsSymbol.of_locally hU
  intro z hz
  -- The same local coordinates and the same scalar cutoff apply to both finite representations.
  let J : Fin N ⊕ Fin N' → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    Sum.elim L L'
  obtain ⟨χ, hχ, A, B, V, p, hV, hzV, hVU, hp, hplower, hpaction⟩ :=
    exists_common_local_symbols J c hc e f z hz
  let Tin := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let Tout := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  obtain ⟨K, hK⟩ := h
  -- The original smooth kernel acquires exactly the same two scalar multipliers.
  let K' : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ ((χ x : ℂ) * (χ y : ℂ)) • K.toFun x y
      isSmooth := by
        intro e f _ _
        have hw : ContMDiff
            (𝓘(ℝ, X).prod 𝓘(ℝ, X)) 𝓘(ℝ, ℂ) ∞
            (fun w : M × M ↦ (χ w.1 : ℂ) * (χ w.2 : ℂ)) :=
          (contDiff_fst.mul contDiff_snd :
            ContDiff ℝ ∞ (fun w : ℂ × ℂ ↦ w.1 * w.2)).contMDiff.comp
              (((Complex.ofRealCLM.contMDiff.comp hχ).comp contMDiff_fst).prodMk_space
                ((Complex.ofRealCLM.contMDiff.comp hχ).comp contMDiff_snd))
        have hsmul : ContDiff ℝ ∞ (fun w : ℂ ×
            (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ w.1 • w.2) :=
          (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
        apply (hsmul.contMDiff.comp_contMDiffOn
          (hw.contMDiffOn.prodMk_space (K.isSmooth e f))).congr
        intro w hw
        simp only [kernelInFrames, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul]
        rfl }
  have hkernel : K'.toLinearMap μ = Tout.comp ((K.toLinearMap μ).comp Tin) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, ((χ x : ℂ) * (χ y : ℂ)) • K.toFun x y (u.val y) ∂μ) =
      (χ x : ℂ) • ∫ y, K.toFun x y ((χ y : ℂ) • u.val y) ∂μ
    simp_rw [map_smul, mul_smul]
    exact integral_smul _ _
  obtain ⟨k, hk, hck, hkact⟩ := K'.exists_bundleChartCutoff_kernel μ c c hc hc A B
  let a : SymbolFunction n r q := (∑ j : Fin N, p (Sum.inl j)) - ∑ j : Fin N', p (Sum.inr j)
  have ha : IsSymbol Set.univ m a := (symbolSpace Set.univ isOpen_univ m r q).sub_mem
    ((symbolSpace Set.univ isOpen_univ m r q).sum_mem (fun j _ ↦ hp (Sum.inl j)))
    ((symbolSpace Set.univ isOpen_univ m r q).sum_mem (fun j _ ↦ hp (Sum.inr j)))
  -- Frequency integrability makes quantization linear in these full symbols.
  have hInt (b : SymbolFunction n r q) (hb : IsSymbol Set.univ m b)
      (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      Integrable (fun ξ ↦ Complex.exp (Complex.I * (inner ℝ x ξ : ℂ)) •
        b x ξ (fourierSG u ξ)) := by
    let Er := EuclideanSpace ℂ (Fin r)
    let Eq := EuclideanSpace ℂ (Fin q)
    have hg : (b x).HasTemperateGrowth := by
      refine ⟨?_, ?_⟩
      · have hs : ContDiff ℝ ∞ (Function.uncurry b) := by
          simpa only [Set.univ_prod_univ, contDiffOn_univ] using hb.1
        exact hs.comp (contDiff_const.prodMk contDiff_id)
      · intro j
        obtain ⟨C, hC, hbound⟩ := hb.2 {x} (Set.subset_univ _) isCompact_singleton 0 j
        refine ⟨⌈m - (j : ℝ)⌉₊, C, fun ξ ↦ ?_⟩
        have hbound' := hbound x (Set.mem_singleton x) ξ
        simp only [symbolDerivative, norm_iteratedFDeriv_zero] at hbound'
        apply hbound'.trans
        apply mul_le_mul_of_nonneg_left _ hC
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg ξ]) (Nat.le_ceil _)
    have hphase : (fun ξ : X ↦
        Complex.exp (Complex.I * (inner ℝ x ξ : ℂ))).HasTemperateGrowth := by
      simpa [Function.comp_def, mul_comm] using
        Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ x).hasTemperateGrowth
    have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
      inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
    let d : X ≃L[ℝ] X :=
      (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
    let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (FourierTransform.fourier u)
    exact (SchwartzMap.bilinLeftCLM
      (ContinuousLinearMap.id ℂ (Er →L[ℂ] Eq)).flip (hphase.smul hg) w).integrable
  have hquant (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      quantize a u x = (∑ j : Fin N, quantize (p (Sum.inl j)) u x) -
        ∑ j : Fin N', quantize (p (Sum.inr j)) u x := by
    let Q : symbolSpace Set.univ isOpen_univ m r q →ₗ[ℂ] EuclideanSpace ℂ (Fin q) :=
      { toFun := fun b ↦ quantize b.val u x
        map_add' := by
          intro b d
          simp only [quantize, Submodule.coe_add, Pi.add_apply, add_apply, smul_add]
          rw [integral_add (hInt b.val b.property u x) (hInt d.val d.property u x), smul_add]
        map_smul' := by
          intro t b
          simp only [quantize, Submodule.coe_smul, Pi.smul_apply, smul_apply,
            RingHom.id_apply, smul_comm (Complex.exp _), integral_smul]
          exact smul_comm _ _ _ }
    have hQ := map_sub Q
      (∑ j : Fin N, (⟨p (Sum.inl j), hp (Sum.inl j)⟩ :
        symbolSpace Set.univ isOpen_univ m r q))
      (∑ j : Fin N', (⟨p (Sum.inr j), hp (Sum.inr j)⟩ :
        symbolSpace Set.univ isOpen_univ m r q))
    simpa only [map_sum, Q, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_sub, Submodule.coe_sum] using hQ
  have haeq : a = compactKernelSymbol k := by
    apply symbol_eq_of_quantize_eq m m a (compactKernelSymbol k) ha
      (isSmoothingSymbol_compactKernelSymbol k hk hck m)
    intro u x
    rw [hquant, quantize_compactKernelSymbol k hk hck, ← hkact]
    simp_rw [hpaction]
    rw [hkernel, hK]
    change (∑ j : Fin N, B.localizeLinearMap hc
        (Tout ((L j).toLinearMap (Tin (A.extend hc u)))) x) -
      (∑ j : Fin N', B.localizeLinearMap hc
        (Tout ((L' j).toLinearMap (Tin (A.extend hc u)))) x) = B.localizeLinearMap hc
      (Tout (((∑ j : Fin N, (L j).toLinearMap) -
        ∑ j : Fin N', (L' j).toLinearMap) (Tin (A.extend hc u)))) x
    simp
  -- The exact localized difference is smoothing; its discrepancy from the original
  -- global representatives was already shown to have one lower order on V.
  have halower : IsSymbol V (m - 1) a := by
    rw [haeq]
    exact (isSmoothingSymbol_compactKernelSymbol k hk hck (m - 1)).restrict (Set.subset_univ _)
  let g : SymbolFunction n r q := globalSymbolInChart E F
    ((∑ j : Fin N, (L j).globalSymbol).val - (∑ j : Fin N', (L' j).globalSymbol).val) c e f
  have hrem : IsSymbol V (m - 1) (a - g) := by
    have hh : IsSymbol V (m - 1)
        ((∑ j : Fin N, (p (Sum.inl j) -
          globalSymbolInChart E F (J (Sum.inl j)).globalSymbolFunction c e f)) -
        ∑ j : Fin N', (p (Sum.inr j) -
          globalSymbolInChart E F (J (Sum.inr j)).globalSymbolFunction c e f)) :=
      (symbolSpace V hV (m - 1) r q).sub_mem
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inl j)))
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inr j)))
    convert hh using 1
    ext y η v
    simp [a, g, J, globalSymbolInChart, PseudodifferentialPiece.globalSymbol,
      Finset.sum_sub_distrib]
    abel
  refine ⟨V, hV, hzV, hVU, ?_⟩
  have hdiff := (symbolSpace V hV (m - 1) r q).sub_mem halower hrem
  change IsSymbol V (m - 1) (a - (a - g)) at hdiff
  change IsSymbol V (m - 1) g
  simpa only [sub_sub_cancel] using hdiff

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- SG 3.19: all finite local representations specify one unique global principal class. -/
theorem existsUnique_principalSymbol :
    ∃! σ : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m,
      ∀ (N : ℕ) (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m),
        IsSmoothingOperator μ (P.toLinearMap - ∑ j, (L j).toLinearMap) →
          globalPrincipalSymbolClass E F m (∑ j, (L j).globalSymbol) = σ := by
  /- Existence: choose a finite representation supplied by P's defining property
  and take the quotient class of its actual sum of global symbols. For any second
  representation, subtract the two smoothing remainders and apply the preceding
  independence theorem. Uniqueness: evaluate both candidate specifications on
  the initial representation. No representative or uniqueness field is added to P. -/
  classical
  obtain ⟨N, L, K, hK⟩ := P.isPseudodifferentialOperator
  let σ := globalPrincipalSymbolClass E F m (∑ j, (L j).globalSymbol)
  have hspec (N' : ℕ)
      (L' : Fin N' → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (hL' : IsSmoothingOperator μ (P.toLinearMap - ∑ j, (L' j).toLinearMap)) :
      globalPrincipalSymbolClass E F m (∑ j, (L' j).globalSymbol) = σ := by
    obtain ⟨K', hK'⟩ := hL'
    -- Subtract the two actual kernels, retaining the same original density and fibers.
    let R : SmoothKernel (n := n) (r := r) (q := q) E F :=
      { toFun := fun x y ↦ K.toFun x y - K'.toFun x y
        isSmooth := by
          intro e f _ _
          apply ((K.isSmooth e f).sub (K'.isSmooth e f)).congr
          intro z hz
          simp only [kernelInFrames, ContinuousLinearMap.sub_comp,
            ContinuousLinearMap.comp_sub] }
    have hR : R.toLinearMap μ = K.toLinearMap μ - K'.toLinearMap μ := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
      change (∫ y, (K.toFun x y - K'.toFun x y) (u.val y) ∂μ) =
        (∫ y, K.toFun x y (u.val y) ∂μ) - ∫ y, K'.toFun x y (u.val y) ∂μ
      simp only [sub_apply]
      exact integral_sub (K.integrable_apply μ u x) (K'.integrable_apply μ u x)
    apply globalPrincipalSymbolClass_sum_eq_of_isSmoothingOperator (μ := μ) m N' N L' L
    refine ⟨R, ?_⟩
    rw [hR, hK, hK']
    abel
  refine ⟨σ, hspec, ?_⟩
  -- Evaluating every candidate on this one original representation forces uniqueness.
  intro τ hτ
  exact (hτ N L ⟨K, hK⟩).symm

/-- The global principal symbol in the actual S^m(E,F)/S^(m-1)(E,F) quotient. -/
def principalSymbol : GlobalPrincipalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  Classical.choose P.existsUnique_principalSymbol.exists

/-- Any valid finite local representation computes the chosen principal class. -/
theorem principalSymbol_eq_of_representation (N : ℕ)
    (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
    (h : IsSmoothingOperator μ (P.toLinearMap - ∑ j, (L j).toLinearMap)) :
    P.principalSymbol = globalPrincipalSymbolClass E F m (∑ j, (L j).globalSymbol) := by
  /- Apply the specification from existsUnique_principalSymbol to N,L,h and
  reverse its equality. Classical choice selected a quotient element satisfying
  this specification; it did not select a preferred full or homogeneous symbol. -/
  exact ((Classical.choose_spec P.existsUnique_principalSymbol.exists) N L h).symm

/-- Smoothing operators have zero principal class at every prescribed real order. -/
theorem principalSymbol_eq_zero_of_isSmoothingOperator
    (h : IsSmoothingOperator μ P.toLinearMap) : P.principalSymbol = 0 := by
  /- Use the empty family in principalSymbol_eq_of_representation. The operator
  remainder is P itself by h. The sum of its symbol family is zero, and the
  canonical quotient projection is complex-linear and therefore preserves zero. -/
  classical
  let L : Fin 0 → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
    Fin.elim0
  -- The empty local representation leaves precisely the given smooth kernel.
  have hL : IsSmoothingOperator μ (P.toLinearMap - ∑ j, (L j).toLinearMap) := by
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero] using h
  rw [P.principalSymbol_eq_of_representation 0 L hL]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, map_zero]

/-- The principal class depends only on the actual operator, independently of the density. -/
theorem principalSymbol_eq_of_toLinearMap_eq
    (ν : Measure M) [IsSmoothPositiveMeasure (n := n) ν]
    (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F ν m)
    (h : P.toLinearMap = Q.toLinearMap) : P.principalSymbol = Q.principalSymbol := by
  /- Choose a local representation of P. A kernel for μ becomes a kernel for ν
  by multiplying in the input variable by the smooth positive density ratio.
  Hence the same local family represents Q by h. Apply the representation formula
  to both operators: the global symbol sum and its quotient use no measure. -/
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  -- Reweight the genuine remainder kernel while preserving the entire local family.
  have hL' : IsSmoothingOperator ν (Q.toLinearMap - ∑ j, (L j).toLinearMap) := by
    rw [← h]
    exact (isSmoothingOperator_measure_iff μ ν _).mp hL
  rw [P.principalSymbol_eq_of_representation N L hL,
    Q.principalSymbol_eq_of_representation N L hL']

end PseudodifferentialOperator

end AtiyahSinger
