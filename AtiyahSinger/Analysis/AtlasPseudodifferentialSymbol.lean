/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGlobalSymbol
public import AtiyahSinger.Analysis.AtlasPseudodifferentialOperator

import AtiyahSinger.Analysis.AtlasGlobalSymbolTopology
import AtiyahSinger.Analysis.AtlasSmoothingKernel
import AtiyahSinger.Analysis.CompactKernelSymbol
import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.SymbolLocality
import AtiyahSinger.Analysis.CoordinateChange
import AtiyahSinger.Analysis.FrameChange
import AtiyahSinger.Geometry.AtlasFrameTransition
import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# The principal symbol of a locally finite-rank bundle PDO

Public module ID: M0295.

D05: each local Fourier piece determines a genuine Hom-valued symbol on the
original cotangent and bundle fibers, multiplied by its two actual cutoffs.
Its class in S^m / S^(m-1) is invariant under all finite local representations
of the original section operator modulo the all-order smoothing remainder.

Sources: SG III.3.18--3.19, pp.187--188, and the two-sided cutoff leading-term
formula. Only principal classes are identified; equality modulo one lower
order is not equality modulo smoothing and is not a full homogeneous expansion.
The original local ranks remain independent. No global fiber norm is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

namespace AtlasPseudodifferentialPiece

variable {A B} {m : ℝ} (L : AtlasPseudodifferentialPiece A B m)

/-- Transport the actual two-cutoff symbol back to the original fibers, with zero extension. -/
def globalSymbolFunction : AtlasSymbolFunction (n := n) E F := by
  classical
  exact fun x ξ ↦
    if h : x ∈ L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
        (B.chart L.output.frameIndex).baseSet then
      ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) •
        ((B.frameLinearEquiv L.output.frameIndex x h.2).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ).toLinearMap).comp
          ((L.symbol (L.chart x) (covectorInChart L.chart x ξ)).toLinearMap.comp
            (((EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ).symm.toLinearMap).comp
              (A.frameLinearEquiv L.input.frameIndex x h.1.2).toLinearMap))
    else 0

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]

include hM hT in
/-- The actual cutoff transport is an order-m symbol in every original atlas chart. -/
theorem isAtlasGlobalSymbol_globalSymbolFunction :
    IsAtlasGlobalSymbol A B m L.globalSymbolFunction := by
  /- Stage 1: in the specified overlap, express this actual fiber map in
  any second pair of atlas frames and a second manifold chart. The result
  is the original local symbol with the frequency transformed by the real
  cotangent derivative, between the two smooth frame-change matrices.
  On a compact overlap their derivatives are bounded; the coordinate
  covector transform is uniformly invertible there. The chain rule gives
  the original order m with the same loss per frequency derivative.
  Stage 2: the product of the two cutoffs has compact support inside the
  common chart and both frames. Its zero extension is locally zero at the
  boundary. Glue the local estimates and smoothness there. Overlapping
  charts have equivalent fibers; no global rank equality is imposed. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
    (B.chart L.output.frameIndex).baseSet
  have hD : IsOpen D := (L.chart.open_source.inter (A.chart L.input.frameIndex).open_baseSet).inter
    (B.chart L.output.frameIndex).open_baseSet
  let K := L.chart.symm '' tsupport L.output.cutoff
  have hK : IsCompact K := L.output.compact_support.image_of_continuousOn
    (L.chart.continuousOn_symm.mono (fun y hy ↦ (L.output.support_subset hy).1))
  have hKD : K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨⟨L.chart.map_target (L.output.support_subset hz).1,
      L.output_support_in_input_frame hz⟩, (L.output.support_subset hz).2⟩
  have hzero (x : M) (hx : x ∉ K) (ξ) : L.globalSymbolFunction x ξ = 0 := by
    by_cases hvalid : x ∈ D
    · have hcut : L.chart x ∉ tsupport L.output.cutoff := by
        intro hz
        exact hx ⟨L.chart x, hz, L.chart.left_inv hvalid.1.1⟩
      simp [globalSymbolFunction, D, hvalid, image_eq_zero_of_notMem_tsupport hcut]
    · simp [globalSymbolFunction, D, hvalid]
  -- On an open set, equality of the original functions gives all actual mixed derivatives.
  have congrSymbol {V : Set X} (hV : IsOpen V) {r q : ℕ} (p q : SymbolFunction n r q)
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
  let p₀ : SymbolFunction n (A.rank L.input.frameIndex) (B.rank L.output.frameIndex) := fun z ξ ↦
    ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z ξ
  have hp₀ : IsSymbol Set.univ m p₀ := by
    let R₀ : X → (EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex))) :=
      fun z ↦ ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex)))
    let S₀ : X → (EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex))) :=
      fun _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex)))
    have hA : ContDiffOn ℝ ∞ R₀ Set.univ :=
      ((Complex.ofRealCLM.contDiff.comp
        (L.output.smooth_cutoff.mul L.input.smooth_cutoff)).smul contDiff_const).contDiffOn
    have hB : ContDiffOn ℝ ∞ S₀ Set.univ := contDiffOn_const
    have hp := isSymbol_matrixSymbol Set.univ isOpen_univ m L.symbol L.isSymbol R₀ S₀ hA hB
    convert hp using 1
    funext z ξ
    simp [matrixSymbol, p₀, R₀, S₀]
  intro c hc e f
  let U := atlasSymbolChartDomain A B c e f
  let p := atlasGlobalSymbolInChart A B L.globalSymbolFunction c e f
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B c e f
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
    let R₀ := fun y ↦ B.coordChangeL L.output.frameIndex f (c.symm y)
    let S₀ := fun y ↦ A.coordChangeL e L.input.frameIndex (c.symm y)
    have hcV : ContMDiffOn I I ∞ c.symm V := by
      intro y hy
      exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1.1).contMDiffWithinAt
    have hR : ContDiffOn ℝ ∞ R₀ V :=
      B.contDiffOn_coordChangeL_comp L.output.frameIndex f V c.symm hcV
        (fun y hy ↦ ⟨hy.2.2, hy.1.2⟩)
    have hS : ContDiffOn ℝ ∞ S₀ V :=
      A.contDiffOn_coordChangeL_comp e L.input.frameIndex V c.symm hcV
        (fun y hy ↦ ⟨hy.1.1.2, hy.2.1.2⟩)
    refine ⟨V, hV, hzV, Set.inter_subset_left,
      congrSymbol hV _ p (isSymbol_matrixSymbol V hV m _ hpt R₀ S₀ hR hS) ?_⟩
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
    -- Identify the two rectangular factors using the original fiber vectors.
    let x := c.symm y
    let ei := EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ
    let eo := EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ
    let ee := EuclideanSpace.equiv (Fin (A.rank e)) ℂ
    let ef := EuclideanSpace.equiv (Fin (B.rank f)) ℂ
    have hin (u : EuclideanSpace ℂ (Fin (A.rank e))) :
        S₀ y u = ei.symm ((A.frameLinearEquiv L.input.frameIndex x hy.2.1.2)
          ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))) := by
      have h := (A.coordChangeL_apply e L.input.frameIndex x
        ⟨hy.1.1.2, hy.2.1.2⟩ ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))).symm
      change S₀ y (ee.symm ((A.frameLinearEquiv e x hy.1.1.2)
        ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u)))) =
          ei.symm ((A.frameLinearEquiv L.input.frameIndex x hy.2.1.2)
            ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))) at h
      simpa only [LinearEquiv.apply_symm_apply, ee.symm_apply_apply] using h
    have hout (u : EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex))) :
        R₀ y u = ef.symm ((B.frameLinearEquiv f x hy.1.2)
          ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))) := by
      have h := (B.coordChangeL_apply L.output.frameIndex f x ⟨hy.2.2, hy.1.2⟩
        ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))).symm
      change R₀ y (eo.symm ((B.frameLinearEquiv L.output.frameIndex x hy.2.2)
        ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u)))) =
          ef.symm ((B.frameLinearEquiv f x hy.1.2)
            ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))) at h
      simpa only [LinearEquiv.apply_symm_apply, eo.symm_apply_apply] using h
    have hframes : c.symm y ∈ (A.chart e).baseSet ∧ c.symm y ∈ (B.chart f).baseSet :=
      ⟨hy.1.1.2, hy.1.2⟩
    have hvalid : c.symm y ∈ L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
        (B.chart L.output.frameIndex).baseSet := hy.2
    apply ContinuousLinearMap.ext
    intro u
    simp only [matrixSymbol, ContinuousLinearMap.comp_apply, cotangentSymbol, p₀,
      smul_apply, map_smul, hin, hout]
    simp only [p, atlasGlobalSymbolInChart, dite_eq_left hframes, globalSymbolFunction,
      dite_eq_left hvalid, hfreq, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rfl
  · -- The complement of the compact base support is open, and the original symbol is zero there.
    let V := U ∩ c.symm ⁻¹' Kᶜ
    have hV : IsOpen V :=
      (c.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU
        hK.isClosed.isOpen_compl
    refine ⟨V, hV, ⟨hz, hzK⟩, Set.inter_subset_left,
      congrSymbol hV 0 p (isSymbol_zero V m) ?_⟩
    intro y hy η
    change 0 = atlasGlobalSymbolInChart A B L.globalSymbolFunction c e f y η
    simp [atlasGlobalSymbolInChart, hzero (c.symm y) hy.2]

/-- Exact local Fourier realization in another chart and pair of original atlas frames.
The two cutoff maps and all lower-order coordinate and matrix corrections are retained. -/
private theorem exists_localized_symbol
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c)
    (hAB : D₀.cutoff = K₀.cutoff)
    (hbase : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      c.source ∩ (A.chart D₀.frameIndex).baseSet ∩ (B.chart K₀.frameIndex).baseSet)
    (hone : c '' (L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)) ⊆
      interior {z | D₀.cutoff z = 1})
    (hoverlap : tsupport D₀.cutoff ⊆ c.symm ⁻¹'
      (L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
        (B.chart L.output.frameIndex).baseSet)) :
    ∃ p : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex), IsSymbol Set.univ m p ∧
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) z,
        quantize p u z = K₀.localize hc (L.toLinearMap (D₀.extend hc u)) z) ∧
      IsSymbol (atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∩ c.symm ⁻¹'
        (L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
          (B.chart L.output.frameIndex).baseSet)) (m - 1)
        (p - atlasGlobalSymbolInChart A B L.globalSymbolFunction c
          D₀.frameIndex K₀.frameIndex) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
    (B.chart L.output.frameIndex).baseSet
  let V := atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∩ c.symm ⁻¹' D
  have hV : IsOpen V :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex)
      ((L.chart.open_source.inter (A.chart L.input.frameIndex).open_baseSet).inter
        (B.chart L.output.frameIndex).open_baseSet)
  have hAV : tsupport D₀.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨D₀.support_subset hz, (K₀.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
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
  have htargetOne : t '' K ⊆ interior {z | D₀.cutoff z = 1} := by
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
  let P₀ := amplitudeOperator m (cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol)
    (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude L.symbol _ _
      L.output.compact_support L.input.compact_support)
  have hP₀ : ∀ u z, P₀ u z = quantize p₀ u z := by
    intro u z
    rw [amplitudeOperator_apply]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m L.symbol L.isSymbol _ _
        L.output.smooth_cutoff L.input.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude L.symbol _ _
        L.output.compact_support L.input.compact_support) u) z).symm
  have hP₀support : HasOperatorSupport K P₀ :=
    hasOperatorSupport_cutoff m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support
  have hP₀apply (u) (z) : P₀ u z = L.output.cutoff z • L.operator
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex)))
        (fun w ↦ (L.input.cutoff w : ℂ)) u) z := by
    rw [amplitudeOperator_apply, amplitudeApply_cutoffAmplitude m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support, L.operator_apply]
  let P := coordinatePushforward t ht hts χ D₀.cutoff hχ hcχ hχt
    D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt) P₀
  obtain ⟨s, hs, hPs, hrem⟩ := exists_symbol_coordinatePushforward t ht hts χ D₀.cutoff
    hχ hcχ hχt D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt) m p₀ hp₀
    P₀ hP₀ K hK hKt hP₀support
    hχone htargetOne
  have hPK : HasOperatorSupport (t '' K) P := hasOperatorSupport_coordinatePushforward
    t ht hts χ D₀.cutoff hχ hcχ hχt D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt)
    P₀ K hK hKt hP₀support
  let Fout := fun z ↦ B.coordChangeL L.output.frameIndex K₀.frameIndex (c.symm z)
  let Finp := fun z ↦ A.coordChangeL D₀.frameIndex L.input.frameIndex (c.symm z)
  have hcV : ContMDiffOn I I ∞ c.symm V := by
    intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1.1.1).contMDiffWithinAt
  have hFout : ContDiffOn ℝ ∞ Fout V :=
    B.contDiffOn_coordChangeL_comp L.output.frameIndex K₀.frameIndex V c.symm hcV
      (fun z hz ↦ ⟨hz.2.2, hz.1.2⟩)
  have hFinp : ContDiffOn ℝ ∞ Finp V :=
    A.contDiffOn_coordChangeL_comp D₀.frameIndex L.input.frameIndex V c.symm hcV
      (fun z hz ↦ ⟨hz.1.1.2, hz.2.1.2⟩)
  let Cout := cutoffMatrix D₀.cutoff Fout
  let Cin := cutoffMatrix D₀.cutoff Finp
  have hCout : ContDiff ℝ ∞ Cout :=
    contDiff_cutoffMatrix V hV _ hFout D₀.cutoff D₀.smooth_cutoff hAV
  have hCin : ContDiff ℝ ∞ Cin :=
    contDiff_cutoffMatrix V hV _ hFinp D₀.cutoff D₀.smooth_cutoff hAV
  have hcCout : HasCompactSupport Cout :=
    hasCompactSupport_cutoffMatrix D₀.cutoff _ D₀.compact_support
  have hcCin : HasCompactSupport Cin :=
    hasCompactSupport_cutoffMatrix D₀.cutoff _ D₀.compact_support
  let p := amplitudeSymbol (matrixAmplitude Cout Cin s)
  have hp : IsSymbol univ m p := isSymbol_amplitudeSymbol m _
    (isAmplitude_matrixAmplitude m s hs Cout Cin hCout hCin)
    (hasCompactSupport_matrixAmplitude Cout Cin s hcCout hcCin)
  let Tin := matrixMultiplierCLM Cin hCin hcCin
  have hTin (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) (z : X) :
      Tin u z = D₀.cutoff z • Finp z (u z) := by
    rw [matrixMultiplierCLM_apply]
    rfl
  -- The frame matrices act on the very fiber vectors used by cutoff extension.
  have hFout_apply (z : X) (hz : z ∈ V)
      (v : EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex))) :
      Fout z v = (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
        ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hz.1.2)
          ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hz.2.2).symm
            ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ) v))) := by
    have h := (B.coordChangeL_apply L.output.frameIndex K₀.frameIndex (c.symm z)
      ⟨hz.2.2, hz.1.2⟩
      ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hz.2.2).symm
        ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ) v))).symm
    change Fout z ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ).symm
      ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hz.2.2)
        ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hz.2.2).symm
          ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ) v)))) =
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hz.1.2)
            ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hz.2.2).symm
              ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ) v))) at h
    simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using h
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex)))
          (fun w ↦ (L.input.cutoff w : ℂ))
          (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) =
        L.input.localize L.chart_mem_atlas (D₀.extend hc u) := by
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
      have hcw : c.symm (t w) = L.chart.symm w := c.left_inv hbasew.1.1
      have hframe : Finp (t w) (u (t w)) =
          (EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv L.input.frameIndex (L.chart.symm w)
              (L.input.support_subset hw).2)
              ((A.frameLinearEquiv D₀.frameIndex (L.chart.symm w) hbasew.1.2).symm
                ((EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ) (u (t w))))) := by
        rw [show Finp (t w) = A.coordChangeL D₀.frameIndex L.input.frameIndex
          (L.chart.symm w) from
            congrArg (A.coordChangeL D₀.frameIndex L.input.frameIndex) hcw]
        let ei := EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ
        let ec := EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ
        have h := (A.coordChangeL_apply D₀.frameIndex L.input.frameIndex (L.chart.symm w)
          ⟨hbasew.1.2, (L.input.support_subset hw).2⟩
          ((A.frameLinearEquiv D₀.frameIndex (L.chart.symm w) hbasew.1.2).symm
            (ec (u (t w))))).symm
        change A.coordChangeL D₀.frameIndex L.input.frameIndex (L.chart.symm w)
          (ec.symm ((A.frameLinearEquiv D₀.frameIndex (L.chart.symm w) hbasew.1.2)
            ((A.frameLinearEquiv D₀.frameIndex (L.chart.symm w) hbasew.1.2).symm
              (ec (u (t w)))))) =
          ei.symm ((A.frameLinearEquiv L.input.frameIndex (L.chart.symm w)
            (L.input.support_subset hw).2)
            ((A.frameLinearEquiv D₀.frameIndex (L.chart.symm w) hbasew.1.2).symm
              (ec (u (t w))))) at h
        simpa only [LinearEquiv.apply_symm_apply, ec.symm_apply_apply] using h
      rw [hχw, one_smul, hframe]
      change _ = L.input.localizedFunction (D₀.extend hc u) w
      have hwchart : w ∈ L.chart.target := hwt.1
      simp only [AtlasChartCutoff.localizedFunction, ite_eq_left hwchart, atlasSectionInChart,
        AtlasChartCutoff.extend, AtlasChartCutoff.extendedFunction, dite_eq_left hbasew.1]
      change _ = (L.input.cutoff w : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ).symm
          ((A.frameLinearEquiv L.input.frameIndex (L.chart.symm w)
            (L.input.support_subset hw).2)
            ((D₀.cutoff (t w) : ℂ) • _))
      rw [map_smul, map_smul]
      simp only [Complex.coe_smul]
      rfl
    · simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  have happly : ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) z,
      quantize p u z = K₀.localize hc (L.toLinearMap (D₀.extend hc u)) z := by
    intro u z
    rw [show quantize p u z = Cout z (P (Tin u) z) from by
      rw [hPs]
      exact quantize_matrixAmplitude m s hs Cout Cin hCout hcCout hCin hcCin u z]
    by_cases hz : z ∈ tsupport D₀.cutoff
    · have hzV := hAV hz
      have hzt := hVt hzV
      rw [show P (Tin u) z = P₀
        (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) (t.symm z) from
          coordinatePushforward_apply t ht hts χ D₀.cutoff hχ hcχ hχt
            D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt) P₀ K hKt hP₀support
            (fun w hw ↦ interior_subset (s := {z : X | D₀.cutoff z = 1}) (htargetOne hw))
            (Tin u) z hzt]
      rw [hP₀apply, hinput]
      change D₀.cutoff z • Fout z _ = K₀.localizedFunction (L.toLinearMap (D₀.extend hc u)) z
      rw [hFout_apply z hzV]
      change _ = if z ∈ c.target then (K₀.cutoff z : ℂ) •
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.chart K₀.frameIndex) ⟨c.symm z, L.output.extendedFunction
            (L.operator (L.input.localize L.chart_mem_atlas (D₀.extend hc u))) (c.symm z)⟩).2
        else 0
      have hzc : z ∈ c.target := hzV.1.1.1
      have hzd : c.symm z ∈ L.chart.source ∩ (B.chart L.output.frameIndex).baseSet :=
        ⟨hzV.2.1.1, hzV.2.2⟩
      rw [ite_eq_left hzc, AtlasChartCutoff.extendedFunction, dite_eq_left hzd, ← hAB]
      change D₀.cutoff z •
          (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
            ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hzV.1.2)
              ((B.frameLinearEquiv L.output.frameIndex (c.symm z) hzV.2.2).symm
                ((EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ)
                  (L.output.cutoff (L.chart (c.symm z)) • _)))) =
        (D₀.cutoff z : ℂ) •
          (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
            ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hzV.1.2)
              ((L.output.cutoff (L.chart (c.symm z)) : ℂ) • _))
      simp only [← Complex.coe_smul, map_smul]
      rfl
    · have hDz : D₀.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hKz : K₀.cutoff z = 0 := by rwa [← hAB]
      simp [Cout, cutoffMatrix, AtlasChartCutoff.localize,
        AtlasChartCutoff.localizedFunction, hDz, hKz]
  -- Coordinate change, frame change, and cutoff reduction each contribute one lower order.
  let pdiag : SymbolFunction n (A.rank L.input.frameIndex) (B.rank L.output.frameIndex) := fun z ξ ↦
    ((L.output.cutoff z * L.input.cutoff z : ℝ) : ℂ) • L.symbol z ξ
  have hdiag : IsSymbol univ (m - 1) (p₀ - pdiag) := by
    have h := hasSymbolExpansion_cutoffSymbol m L.symbol L.isSymbol _ _
      L.output.smooth_cutoff L.input.smooth_cutoff
      L.output.compact_support L.input.compact_support 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero,
      cutoffAmplitude, p₀, pdiag, Complex.coe_smul] using h
  have h₁ : IsSymbol V (m - 1) (p - matrixSymbol Fout Finp s) := by
    have h := isSymbol_amplitudeSymbol_matrixAmplitude_sub m s hs Cout Cin
      hCout hcCout hCin hcCin
    have hsK := tsupport_symbol_subset_of_hasOperatorSupport m s hs P hPs
      (t '' K) htarget.isClosed hPK
    have hsame : matrixSymbol Cout Cin s = matrixSymbol Fout Finp s := by
      funext z ξ
      by_cases hz : z ∈ t '' K
      · have hcut : D₀.cutoff z = 1 :=
          interior_subset (s := {z : X | D₀.cutoff z = 1}) (htargetOne hz)
        simp [Cout, Cin, matrixSymbol, cutoffMatrix, hcut]
      · have hzero : s z = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h ↦ hz (hsK h))
        simp [matrixSymbol, hzero]
    rw [hsame] at h
    exact h.restrict (Set.subset_univ V)
  have h₂ := isSymbol_matrixSymbol V hV (m - 1)
    (s - cotangentSymbol t p₀) (hrem.restrict hVt) Fout Finp hFout hFinp
  have h₃ := isSymbol_matrixSymbol V hV (m - 1)
    (cotangentSymbol t (p₀ - pdiag))
      ((isSymbol_cotangentSymbol t ht hts (m - 1) (p₀ - pdiag)
        (hdiag.restrict (Set.subset_univ _))).restrict hVt) Fout Finp hFout hFinp
  have htotal : IsSymbol V (m - 1)
      (p - matrixSymbol Fout Finp (cotangentSymbol t pdiag)) := by
    convert IsSymbol.add hV (IsSymbol.add hV h₁ h₂) h₃ using 1
    ext z ξ v
    simp only [Pi.add_apply, Pi.sub_apply, matrixSymbol, cotangentSymbol,
      add_apply, sub_apply, ContinuousLinearMap.comp_apply, map_sub]
    abel_nf
  have hsame (y : X) (hy : y ∈ V) (η : X) :
      matrixSymbol Fout Finp (cotangentSymbol t pdiag) y η =
        atlasGlobalSymbolInChart A B L.globalSymbolFunction c D₀.frameIndex K₀.frameIndex y η := by
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
    -- Identify the two rectangular factors using the original fiber vectors.
    let x := c.symm y
    let ei := EuclideanSpace.equiv (Fin (A.rank L.input.frameIndex)) ℂ
    let eo := EuclideanSpace.equiv (Fin (B.rank L.output.frameIndex)) ℂ
    let ee := EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ
    let ef := EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ
    have hin (u : EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))) :
        Finp y u = ei.symm ((A.frameLinearEquiv L.input.frameIndex x hy.2.1.2)
          ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))) := by
      have h := (A.coordChangeL_apply D₀.frameIndex L.input.frameIndex x
        ⟨hy.1.1.2, hy.2.1.2⟩ ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))).symm
      change Finp y (ee.symm ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2)
        ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u)))) =
          ei.symm ((A.frameLinearEquiv L.input.frameIndex x hy.2.1.2)
            ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))) at h
      simpa only [LinearEquiv.apply_symm_apply, ee.symm_apply_apply] using h
    have hout (u : EuclideanSpace ℂ (Fin (B.rank L.output.frameIndex))) :
        Fout y u = ef.symm ((B.frameLinearEquiv K₀.frameIndex x hy.1.2)
          ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))) := by
      have h := (B.coordChangeL_apply L.output.frameIndex K₀.frameIndex x ⟨hy.2.2, hy.1.2⟩
        ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))).symm
      change Fout y (eo.symm ((B.frameLinearEquiv L.output.frameIndex x hy.2.2)
        ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u)))) =
          ef.symm ((B.frameLinearEquiv K₀.frameIndex x hy.1.2)
            ((B.frameLinearEquiv L.output.frameIndex x hy.2.2).symm (eo u))) at h
      simpa only [LinearEquiv.apply_symm_apply, eo.symm_apply_apply] using h
    have hframes : c.symm y ∈ (A.chart D₀.frameIndex).baseSet ∧
        c.symm y ∈ (B.chart K₀.frameIndex).baseSet :=
      ⟨hy.1.1.2, hy.1.2⟩
    have hvalid : c.symm y ∈ L.chart.source ∩ (A.chart L.input.frameIndex).baseSet ∩
        (B.chart L.output.frameIndex).baseSet := hy.2
    apply ContinuousLinearMap.ext
    intro u
    simp only [matrixSymbol, ContinuousLinearMap.comp_apply, cotangentSymbol, pdiag,
      smul_apply, map_smul, hin, hout]
    simp only [atlasGlobalSymbolInChart, dite_eq_left hframes, globalSymbolFunction,
      dite_eq_left hvalid, hfreq, LinearMap.coe_toContinuousLinearMap',
      LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
    rfl
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
        ((p - matrixSymbol Fout Finp (cotangentSymbol t pdiag)) y) ξ) =ᶠ[nhds x]
      (fun y ↦ iteratedFDeriv ℝ j
        ((p - atlasGlobalSymbolInChart A B L.globalSymbolFunction c
          D₀.frameIndex K₀.frameIndex) y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      congr 1
      funext η
      exact congrArg (fun v ↦ p y η - v) (hsame y hy η)
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ

/-- The transported piece as an element of the actual global symbol module. -/
def globalSymbol : atlasGlobalSymbolSpace A B m :=
  ⟨L.globalSymbolFunction, L.isAtlasGlobalSymbol_globalSymbolFunction⟩

end AtlasPseudodifferentialPiece

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

/-- Common local full symbols retaining the geometric plateau needed for order reduction. -/
private theorem exists_common_local_symbols_with_cutoffs {m : ℝ} {ι : Type*} [Finite ι]
    (J : ι → AtlasPseudodifferentialPiece A B m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : A.Index) (f : B.Index)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ atlasSymbolChartDomain A B c e f) :
    ∃ (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
      (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
      D₀.frameIndex = e ∧ K₀.frameIndex = f ∧
      HasCompactSupport χ ∧
      tsupport χ ⊆ c.source ∩ (A.chart e).baseSet ∩ (B.chart f).baseSet ∧
      D₀.cutoff = K₀.cutoff ∧ (∀ y ∈ c '' tsupport χ, D₀.cutoff y = 1) ∧
      ∃ (V : Set (EuclideanSpace ℝ (Fin n)))
        (p : ι → SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)),
        IsOpen V ∧ z ∈ V ∧ V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
          (∀ y ∈ V, χ (c.symm y) = 1) ∧
          (∀ j, IsSymbol Set.univ m (p j)) ∧
          (∀ j, IsSymbol V (m - 1) (p j - atlasGlobalSymbolInChart A B
            (J j).globalSymbolFunction c D₀.frameIndex K₀.frameIndex)) ∧
          ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
              EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
            quantize (p j) u y = K₀.localize hc
              (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
                ((J j).toLinearMap
                  (atlasSectionMul A (fun x ↦ (χ x : ℂ))
                    (Complex.ofRealCLM.contMDiff.comp hχ) (D₀.extend hc u)))) y := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let x := c.symm z
  let D := c.source ∩ (A.chart e).baseSet ∩ (B.chart f).baseSet
  let D' (j : ι) := (J j).chart.source ∩ (A.chart (J j).input.frameIndex).baseSet ∩
    (B.chart (J j).output.frameIndex).baseSet
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
        (((J j).chart.open_source.inter (A.chart (J j).input.frameIndex).open_baseSet).inter
          (B.chart (J j).output.frameIndex).open_baseSet)
    · simpa only [W', ite_eq_right hj] using (hK j).isClosed.isOpen_compl
  have hxW' (j : ι) : x ∈ W' j := by
    by_cases hj : x ∈ K j
    · simpa only [W', ite_eq_left hj] using hKD j hj
    · simpa only [W', ite_eq_right hj, mem_compl_iff] using hj
  let W := D ∩ ⋂ j, W' j
  have hW : IsOpen W :=
    ((c.open_source.inter (A.chart e).open_baseSet).inter (B.chart f).open_baseSet).inter
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
  let D₀ : AtlasChartCutoff A c :=
    { frameIndex := e
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.1.2⟩ }
  let K₀ : AtlasChartCutoff B c :=
    { frameIndex := f
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun y hy ↦ ⟨(hρT hy).1, (hρT hy).2.1.2⟩ }
  let V := c.target ∩ c.symm ⁻¹' (W ∩ interior {y | χ y = 1})
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (hW.inter isOpen_interior)
  have hzV : z ∈ V := ⟨hz.1.1, hxW, hxOne⟩
  have hVU : V ⊆ atlasSymbolChartDomain A B c e f :=
    fun y hy ↦ ⟨⟨hy.1, hy.2.1.1.1.2⟩, hy.2.1.1.2⟩
  let Tin := atlasSectionMul A (fun y ↦ (χ y : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  let Tout := atlasSectionMul B (fun y ↦ (χ y : ℂ))
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
  let input (j : ι) : AtlasChartCutoff A (J j).chart :=
    { (J j).input with
      cutoff := fun y ↦ (J j).input.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).input.smooth_cutoff
        (fun y hy ↦ ((J j).input.support_subset hy).1)
      compact_support := (J j).input.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).input.support_subset }
  let output (j : ι) : AtlasChartCutoff B (J j).chart :=
    { (J j).output with
      cutoff := fun y ↦ (J j).output.cutoff y * χ ((J j).chart.symm y)
      smooth_cutoff := hcutoff _ (J j).chart_mem_atlas _ (J j).output.smooth_cutoff
        (fun y hy ↦ ((J j).output.support_subset hy).1)
      compact_support := (J j).output.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans (J j).output.support_subset }
  let R (j : ι) : AtlasPseudodifferentialPiece A B m :=
    { J j with
      input := input j
      output := output j
      input_support_in_output_frame :=
        tsupport_mul_subset_left.trans (J j).input_support_in_output_frame
      output_support_in_input_frame :=
        tsupport_mul_subset_left.trans (J j).output_support_in_input_frame }
  have hinput (j : ι) (u : A.smoothSections) :
      (input j).localize (J j).chart_mem_atlas u =
        (J j).input.localize (J j).chart_mem_atlas (Tin u) := by
    apply DFunLike.ext
    intro y
    by_cases hy : y ∈ tsupport (J j).input.cutoff
    · have hyc := ((J j).input.support_subset hy).1
      have hyf := ((J j).input.support_subset hy).2
      change (input j).localizedFunction u y = (J j).input.localizedFunction (Tin u) y
      simp only [AtlasChartCutoff.localizedFunction, hyc, ↓reduceIte]
      dsimp only [input]
      change _ = ((J j).input.cutoff y : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank (J j).input.frameIndex)) ℂ).symm
          ((A.frameLinearEquiv (J j).input.frameIndex ((J j).chart.symm y) hyf)
            ((χ ((J j).chart.symm y) : ℂ) • u.val ((J j).chart.symm y)))
      rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
        input, image_eq_zero_of_notMem_tsupport hy]
  have houtput (j : ι)
      (v : 𝓢(X, EuclideanSpace ℂ (Fin (B.rank (J j).output.frameIndex)))) :
      (output j).extend (J j).chart_mem_atlas v =
        Tout ((J j).output.extend (J j).chart_mem_atlas v) := by
    apply Subtype.ext
    funext y
    change (output j).extendedFunction v y = (χ y : ℂ) • (J j).output.extendedFunction v y
    by_cases hy : y ∈ (J j).chart.source ∩ (B.chart (J j).output.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, output, dite_eq_left hy]
      rw [(J j).chart.left_inv hy.1, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [AtlasChartCutoff.extendedFunction, output, hy]
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
    unfold AtlasPseudodifferentialPiece.globalSymbolFunction
    dsimp only [R, input, output]
    split_ifs with hdomain
    · rw [(J j).chart.left_inv hdomain.1.1, hy]
      simp
    · rfl
  -- Equality on an open set retains the complete mixed-derivative symbol estimates.
  have congrSymbol (a b : SymbolFunction n (A.rank e) (B.rank f)) (ha : IsSymbol V (m - 1) a)
      (hab : ∀ y ∈ V, ∀ η, a y η = b y η) : IsSymbol V (m - 1) b := by
    refine ⟨ha.1.congr (fun w hw ↦ (hab w.1 hw.1 w.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨K₀, hB, hbound⟩ := ha.2 C hCV hC i j
    refine ⟨K₀, hB, fun y hy η ↦ ?_⟩
    have hnear : (fun w ↦ iteratedFDeriv ℝ j (a w) η) =ᶠ[nhds y]
        (fun w ↦ iteratedFDeriv ℝ j (b w) η) := by
      filter_upwards [hV.mem_nhds (hCV hy)] with w hw
      rw [funext (hab w hw)]
    change ‖iteratedFDeriv ℝ i _ y‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound y hy η
  have hsymbols (j : ι) : ∃ p : SymbolFunction n (A.rank e) (B.rank f), IsSymbol Set.univ m p ∧
      IsSymbol V (m - 1) (p - atlasGlobalSymbolInChart A B (J j).globalSymbolFunction c e f) ∧
      ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank e)))) y,
        quantize p u y = K₀.localize hc (Tout ((J j).toLinearMap (Tin (D₀.extend hc u)))) y := by
    by_cases hj : x ∈ K j
    · have hactive : W ⊆ D' j := by
        intro y hy
        simpa only [W', ite_eq_left hj] using mem_iInter.mp hy.2 j
      obtain ⟨p, hp, hpaction, hplower⟩ := (R j).exists_localized_symbol c hc D₀ K₀ rfl
        ((hRsupp j).trans hχD)
        ((image_mono (hRsupp j)).trans hρone)
        (fun y hy ↦ hactive (hρT hy).2)
      refine ⟨p, hp, ?_, ?_⟩
      · apply congrSymbol _ _ (hplower.restrict (fun y hy ↦ ⟨hVU hy, hactive hy.2.1⟩))
        intro y hy η
        have hχy : χ (c.symm y) = 1 := by
          have hmem : c.symm y ∈ {w | χ w = 1} := interior_subset hy.2.2
          exact hmem
        simp only [Pi.sub_apply, atlasGlobalSymbolInChart, hglobal j _ hχy]
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
          simp [AtlasChartCutoff.localizedFunction, hzeroInput]
        change (output j).extendLinearMap (J j).chart_mem_atlas
          ((J j).operator ((input j).localize (J j).chart_mem_atlas u)) = 0
        rw [hin, map_zero, map_zero]
      refine ⟨0, isSymbol_zero _ _, ?_, ?_⟩
      · apply congrSymbol 0 _ (isSymbol_zero _ _)
        intro y hy η
        have hyK : c.symm y ∉ K j := by
          simpa only [W', ite_eq_right hj, mem_compl_iff] using mem_iInter.mp hy.2.1.2 j
        have hzero (ξ) : (J j).globalSymbolFunction (c.symm y) ξ = 0 := by
          by_cases hvalid : c.symm y ∈ D' j
          · have hcut : (J j).chart (c.symm y) ∉ tsupport (J j).output.cutoff := by
              intro hmem
              exact hyK ⟨(J j).chart (c.symm y), Or.inl hmem,
                (J j).chart.left_inv hvalid.1.1⟩
            simp [AtlasPseudodifferentialPiece.globalSymbolFunction, D', hvalid,
              image_eq_zero_of_notMem_tsupport hcut]
          · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, D', hvalid]
        simp [atlasGlobalSymbolInChart, hzero]
      · intro u y
        change quantize 0 u y = K₀.localize hc
          ((Tout.comp ((J j).toLinearMap.comp Tin)) (D₀.extend hc u)) y
        rw [← hpiece, hRzero]
        change quantize 0 u y = (K₀.localizeLinearMap hc) 0 y
        simp [quantize]
  choose p hp hplower hpaction using hsymbols
  refine ⟨χ, χ.contMDiff, D₀, K₀, rfl, rfl, hcχ, hχD, rfl, ?_,
    V, p, hV, hzV, hVU, ?_, hp, hplower, hpaction⟩
  · intro y hy
    exact (interior_subset (s := {y | ρ y = 1})) (hρone hy)
  · intro y hy
    exact (interior_subset (s := {y | χ y = 1})) hy.2.2

/-- Common local full symbols for a finite family, with the original two cutoff actions. -/
private theorem exists_common_local_symbols {m : ℝ} {ι : Type*} [Finite ι]
    (J : ι → AtlasPseudodifferentialPiece A B m)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : A.Index) (f : B.Index)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ atlasSymbolChartDomain A B c e f) :
    ∃ (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c),
      D₀.frameIndex = e ∧ K₀.frameIndex = f ∧
      ∃ (V : Set (EuclideanSpace ℝ (Fin n)))
        (p : ι → SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)),
        IsOpen V ∧ z ∈ V ∧ V ⊆ atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∧
          (∀ j, IsSymbol Set.univ m (p j)) ∧
          (∀ j, IsSymbol V (m - 1) (p j - atlasGlobalSymbolInChart A B
            (J j).globalSymbolFunction c D₀.frameIndex K₀.frameIndex)) ∧
          ∀ j (u : 𝓢(EuclideanSpace ℝ (Fin n),
              EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
            quantize (p j) u y = K₀.localize hc ((J j).toLinearMap (D₀.extend hc u)) y := by
  classical
  obtain ⟨χ, hχ, D₀, K₀, he, hf, _, _, _, _, V, p, hV, hzV, hVU,
    _, hp, hplower, hpaction⟩ :=
    exists_common_local_symbols_with_cutoffs A B J c hc e f z hz
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let Tin := atlasSectionMul A (fun y ↦ (χ y : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
  let Tout := atlasSectionMul B (fun y ↦ (χ y : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
  have hcutoff (d : OpenPartialHomeomorph M X) (hd : d ∈ atlas X M)
      (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ d.target) :
      ContDiff ℝ ∞ (fun y ↦ a y * χ (d.symm y)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport a
    · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd) (hs hy)
      exact ha.contDiffAt.mul ((hχ.contMDiffAt.comp y hchart).contDiffAt)
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hy] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  -- Absorb the same scalar χ into the returned two atlas cutoffs. Their frame
  -- indices are exactly e and f, so the original local symbol has these ranks.
  let Dχ : AtlasChartCutoff A c :=
    { D₀ with
      cutoff := fun y ↦ D₀.cutoff y * χ (c.symm y)
      smooth_cutoff := hcutoff c hc _ D₀.smooth_cutoff (fun y hy ↦ (D₀.support_subset hy).1)
      compact_support := D₀.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans D₀.support_subset }
  let Kχ : AtlasChartCutoff B c :=
    { K₀ with
      cutoff := fun y ↦ K₀.cutoff y * χ (c.symm y)
      smooth_cutoff := hcutoff c hc _ K₀.smooth_cutoff (fun y hy ↦ (K₀.support_subset hy).1)
      compact_support := K₀.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans K₀.support_subset }
  have hDχ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) :
      Dχ.extend hc u = Tin (D₀.extend hc u) := by
    apply Subtype.ext
    funext x
    change Dχ.extendedFunction u x = (χ x : ℂ) • D₀.extendedFunction u x
    by_cases hx : x ∈ c.source ∩ (A.chart D₀.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, Dχ, dite_eq_left hx]
      rw [c.left_inv hx.1, Complex.ofReal_mul, smul_smul, mul_comm]
    · simp [AtlasChartCutoff.extendedFunction, Dχ, hx]
  have hKχ (v : B.smoothSections) : Kχ.localize hc v = K₀.localize hc (Tout v) := by
    apply SchwartzMap.ext
    intro y
    by_cases hy : y ∈ tsupport K₀.cutoff
    · have hyc := (K₀.support_subset hy).1
      have hyf := (K₀.support_subset hy).2
      change Kχ.localizedFunction v y = K₀.localizedFunction (Tout v) y
      simp only [AtlasChartCutoff.localizedFunction, ite_eq_left hyc, atlasSectionInChart]
      dsimp only [Kχ]
      change _ = (K₀.cutoff y : ℂ) •
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.frameLinearEquiv K₀.frameIndex (c.symm y) hyf)
            ((χ (c.symm y) : ℂ) • v.val (c.symm y)))
      rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
      rfl
    · simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
        Kχ, image_eq_zero_of_notMem_tsupport hy]
  refine ⟨Dχ, Kχ, he, hf, V, p, hV, hzV, hVU, hp, hplower, ?_⟩
  intro j u y
  rw [hDχ, hKχ]
  exact hpaction j u y

/-- Exact common local symbols identify the principal classes of smoothing-equivalent sums. -/
private theorem atlasGlobalPrincipalSymbolClass_sum_eq_of_isAtlasSmoothingOperator
    (m : ℝ) (N N' : ℕ)
    (L : Fin N → AtlasPseudodifferentialPiece A B m)
    (L' : Fin N' → AtlasPseudodifferentialPiece A B m)
    (h : IsAtlasSmoothingOperator A B ((∑ j, (L j).toLinearMap) - ∑ j, (L' j).toLinearMap)) :
    atlasGlobalPrincipalSymbolClass A B m (∑ j, (L j).globalSymbol) =
      atlasGlobalPrincipalSymbolClass A B m (∑ j, (L' j).globalSymbol) := by
  /- Localize both finite families using the same cutoffs and fixed
  chart/frame pair. Their exact common-coordinate symbols differ from the
  original global representatives by order m-1. The all-order smoothing
  hypothesis supplies a compact smooth kernel for this localized operator
  difference. Full-symbol injectivity identifies its exact local symbol
  with that kernel's smoothing symbol. The lower-order discrepancies and
  locality then give equality of the original principal quotient classes. -/
  classical
  rw [atlasGlobalPrincipalSymbolClass_eq_iff]
  intro c hc e f
  let X := EuclideanSpace ℝ (Fin n)
  let U := atlasSymbolChartDomain A B c e f
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B c e f
  apply IsSymbol.of_locally hU
  intro z hz
  -- The same local coordinates and the same scalar cutoff apply to both finite representations.
  let J : Fin N ⊕ Fin N' → AtlasPseudodifferentialPiece A B m :=
    Sum.elim L L'
  obtain ⟨D₀, K₀, rfl, rfl, V, p, hV, hzV, hVU, hp, hplower, hpaction⟩ :=
    exists_common_local_symbols A B J c hc e f z hz
  -- The two returned atlas cutoffs include exactly the common scalar multiplier.
  -- Apply the all-order smoothing kernel bridge to this original operator difference.
  obtain ⟨k, hk, hck, hkact⟩ := h.exists_compactKernel _ c hc D₀ K₀
  let r := A.rank D₀.frameIndex
  let q := B.rank K₀.frameIndex
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
    change (∑ j : Fin N, K₀.localizeLinearMap hc
        ((L j).toLinearMap (D₀.extend hc u)) x) -
      (∑ j : Fin N', K₀.localizeLinearMap hc
        ((L' j).toLinearMap (D₀.extend hc u)) x) = K₀.localizeLinearMap hc
      (((∑ j : Fin N, (L j).toLinearMap) -
        ∑ j : Fin N', (L' j).toLinearMap) (D₀.extend hc u)) x
    simp
  -- The exact localized difference is smoothing; its discrepancy from the original
  -- global representatives was already shown to have one lower order on V.
  have halower : IsSymbol V (m - 1) a := by
    rw [haeq]
    exact (isSmoothingSymbol_compactKernelSymbol k hk hck (m - 1)).restrict (Set.subset_univ _)
  let g : SymbolFunction n r q := atlasGlobalSymbolInChart A B
    ((∑ j : Fin N, (L j).globalSymbol).val - (∑ j : Fin N', (L' j).globalSymbol).val)
    c D₀.frameIndex K₀.frameIndex
  have hrem : IsSymbol V (m - 1) (a - g) := by
    have hh : IsSymbol V (m - 1)
        ((∑ j : Fin N, (p (Sum.inl j) -
          atlasGlobalSymbolInChart A B (J (Sum.inl j)).globalSymbolFunction c
            D₀.frameIndex K₀.frameIndex)) -
        ∑ j : Fin N', (p (Sum.inr j) -
          atlasGlobalSymbolInChart A B (J (Sum.inr j)).globalSymbolFunction c
            D₀.frameIndex K₀.frameIndex)) :=
      (symbolSpace V hV (m - 1) r q).sub_mem
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inl j)))
      ((symbolSpace V hV (m - 1) r q).sum_mem (t := Finset.univ)
        (fun j _ ↦ hplower (Sum.inr j)))
    convert hh using 1
    ext y η v
    by_cases hframes : c.symm y ∈ (A.chart D₀.frameIndex).baseSet ∧
        c.symm y ∈ (B.chart K₀.frameIndex).baseSet
    all_goals
      simp [a, g, J, atlasGlobalSymbolInChart, AtlasPseudodifferentialPiece.globalSymbol,
        Finset.sum_sub_distrib, hframes]
    all_goals abel
  refine ⟨V, hV, hzV, hVU, ?_⟩
  have hdiff := (symbolSpace V hV (m - 1) r q).sub_mem halower hrem
  change IsSymbol V (m - 1) (a - (a - g)) at hdiff
  change IsSymbol V (m - 1) g
  simpa only [sub_sub_cancel] using hdiff

namespace AtlasPseudodifferentialOperator

variable {A B} {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)

/-- SG 3.19: all actual local representations determine one unique principal quotient class. -/
theorem existsUnique_principalSymbol :
    ∃! σ : AtlasGlobalPrincipalSymbolSpace A B m,
      ∀ (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A B m),
        IsAtlasSmoothingOperator A B (P.toLinearMap - ∑ j, (L j).toLinearMap) →
          atlasGlobalPrincipalSymbolClass A B m (∑ j, (L j).globalSymbol) = σ := by
  /- Existence: choose the finite representation in P's defining property.
  Its actual sum of transported symbols has order m and hence a quotient
  class. Given a second representation, their difference has bounded
  extensions between every pair of Sobolev orders. Localize input/output
  in a common chart. The local all-order characterization yields a smooth
  kernel, including cross-component terms away from the diagonal.
  The two-sided Fourier symbol reduction and coordinate transformation
  identify its leading difference with the difference of the displayed
  symbols modulo order m-1. Thus the classes agree in every chart.
  Uniqueness: apply both candidate specifications to the original chosen
  representation. No class or uniqueness certificate is a field of P. -/
  classical
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  let σ := atlasGlobalPrincipalSymbolClass A B m (∑ j, (L j).globalSymbol)
  have hspec (N' : ℕ) (L' : Fin N' → AtlasPseudodifferentialPiece A B m)
      (hL' : IsAtlasSmoothingOperator A B (P.toLinearMap - ∑ j, (L' j).toLinearMap)) :
      atlasGlobalPrincipalSymbolClass A B m (∑ j, (L' j).globalSymbol) = σ := by
    apply atlasGlobalPrincipalSymbolClass_sum_eq_of_isAtlasSmoothingOperator A B m N' N L' L
    -- Subtract the actual extensions on each original pair of Sobolev completions.
    intro D K s t
    obtain ⟨T, hT⟩ := hL D K s t
    obtain ⟨T', hT'⟩ := hL' D K s t
    refine ⟨T - T', fun u ↦ ?_⟩
    rw [sub_apply, hT, hT', ← map_sub]
    congr 1
    simp only [LinearMap.sub_apply]
    abel
  refine ⟨σ, hspec, ?_⟩
  intro τ hτ
  exact (hτ N L hL).symm

/-- The actual principal class selected by its representation-independent specification. -/
def principalSymbol : AtlasGlobalPrincipalSymbolSpace A B m :=
  Classical.choose P.existsUnique_principalSymbol.exists

/-- Any specified finite local representation computes the same chosen principal class. -/
theorem principalSymbol_eq_of_representation (N : ℕ)
    (L : Fin N → AtlasPseudodifferentialPiece A B m)
    (h : IsAtlasSmoothingOperator A B (P.toLinearMap - ∑ j, (L j).toLinearMap)) :
    P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m (∑ j, (L j).globalSymbol) := by
  /- The chosen class satisfies the specification for this exact family
  and its actual smoothing remainder. Apply that specification and reverse
  its equality. No choice of another representative or section action occurs. -/
  exact ((Classical.choose_spec P.existsUnique_principalSymbol.exists) N L h).symm

/-- Vanishing of the principal class means precisely one lower operator order. -/
theorem principalSymbol_eq_zero_iff :
    P.principalSymbol = 0 ↔
      IsAtlasPseudodifferentialOperator A B (m - 1) P.toLinearMap := by
  /- Forward: localize the original section map in finitely many common
  chart/frame neighborhoods. Zero principal class means that each complete
  local symbol has order m-1, after the usual lower-order coordinate and
  two-cutoff corrections. The same smoothing remainder handles terms
  away from the diagonal. These local symbols give an order-(m-1)
  representation of the original action, not an unrelated operator.
  Reverse: view an order-(m-1) representation as order m. Every transported
  symbol lies in the quotient denominator, and the smoothing remainder
  contributes zero. In dimension zero the quotient is trivial while
  operators themselves may be nonzero smoothing maps. The supported K class
  also records the source and target bundles, so it need not vanish. -/
  classical
  -- Finite sums and all-order remainders use exactly the original section maps.
  have hzeroSmooth : IsAtlasSmoothingOperator A B 0 := by
    intro D K s t
    exact ⟨0, by intro u; simp⟩
  have hsmooth (l : ℝ) (T : A.smoothSections →ₗ[ℂ] B.smoothSections)
      (hT : IsAtlasSmoothingOperator A B T) : IsAtlasPseudodifferentialOperator A B l T := by
    refine ⟨0, Fin.elim0, ?_⟩
    simpa only [Fin.sum_univ_zero, sub_zero] using hT
  have hpiece {l : ℝ} (R : AtlasPseudodifferentialPiece A B l) :
      IsAtlasPseudodifferentialOperator A B l R.toLinearMap := by
    refine ⟨1, fun _ ↦ R, ?_⟩
    simpa only [Fin.sum_univ_one, sub_self] using hzeroSmooth
  have hadd {l : ℝ} (T S : A.smoothSections →ₗ[ℂ] B.smoothSections)
      (hT : IsAtlasPseudodifferentialOperator A B l T)
      (hS : IsAtlasPseudodifferentialOperator A B l S) :
      IsAtlasPseudodifferentialOperator A B l (T + S) := by
    obtain ⟨N, J, hJ⟩ := hT
    obtain ⟨N', J', hJ'⟩ := hS
    let L : Fin (N + N') → AtlasPseudodifferentialPiece A B l := Fin.append J J'
    refine ⟨N + N', L, ?_⟩
    have hsum : (∑ j, (L j).toLinearMap) =
        (∑ j, (J j).toLinearMap) + ∑ j, (J' j).toLinearMap := by
      rw [Fin.sum_univ_add]
      simp only [L, Fin.append_left, Fin.append_right]
    rw [hsum]
    intro D K s t
    obtain ⟨U, hU⟩ := hJ D K s t
    obtain ⟨V, hV⟩ := hJ' D K s t
    refine ⟨U + V, fun u ↦ ?_⟩
    rw [add_apply, hU, hV, ← map_add]
    congr 1
    simp only [LinearMap.sub_apply, LinearMap.add_apply]
    abel
  have hsum {l : ℝ} {ι : Type} (J : ι → A.smoothSections →ₗ[ℂ] B.smoothSections)
      (s : Finset ι) (hJ : ∀ j ∈ s, IsAtlasPseudodifferentialOperator A B l (J j)) :
      IsAtlasPseudodifferentialOperator A B l (∑ j ∈ s, J j) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using hsmooth l 0 hzeroSmooth
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact hadd _ _ (hJ j (Finset.mem_insert_self _ _))
        (ih (fun i hi ↦ hJ i (Finset.mem_insert_of_mem hi)))
  -- Stage 1: retain the exact cutoff operator when its full symbol has lower order.
  have hpieceLower {m l : ℝ}
      (R : AtlasPseudodifferentialPiece A B m)
      (hR : IsSymbol Set.univ l (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol)) :
      IsAtlasPseudodifferentialOperator A B l R.toLinearMap := by
    let X := EuclideanSpace ℝ (Fin n)
    let U := R.chart.target ∩ R.chart.symm ⁻¹'
      ((A.chart R.input.frameIndex).baseSet ∩ (B.chart R.output.frameIndex).baseSet)
    let K := tsupport R.output.cutoff ∪ tsupport R.input.cutoff
    have hU : IsOpen U := R.chart.isOpen_inter_preimage_symm
      ((A.chart R.input.frameIndex).open_baseSet.inter (B.chart R.output.frameIndex).open_baseSet)
    have hK : IsCompact K := R.output.compact_support.union R.input.compact_support
    have hKU : K ⊆ U := by
      intro z hz
      rcases hz with hz | hz
      · exact ⟨(R.output.support_subset hz).1, R.output_support_in_input_frame hz,
          (R.output.support_subset hz).2⟩
      · exact ⟨(R.input.support_subset hz).1, (R.input.support_subset hz).2,
          R.input_support_in_output_frame hz⟩
    obtain ⟨O, hOo, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
    obtain ⟨δ, hδ, _, hsδ, honeδ⟩ := exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo hK.isClosed hKO
    have hδsupport : tsupport δ = closure O := congrArg closure hsδ
    have hcδ : HasCompactSupport δ := by simpa [HasCompactSupport, hδsupport] using hOc
    have hδU : tsupport δ ⊆ U := by rwa [hδsupport]
    have hδone (z : X) (hz : z ∈ K) : δ z = 1 := (honeδ z).mp hz
    let D₀ : AtlasChartCutoff A R.chart :=
      { frameIndex := R.input.frameIndex
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.1⟩ }
    let K₀ : AtlasChartCutoff B R.chart :=
      { frameIndex := R.output.frameIndex
        cutoff := δ
        smooth_cutoff := hδ
        compact_support := hcδ
        support_subset := fun z hz ↦ ⟨(hδU hz).1, (hδU hz).2.2⟩ }
    let T := amplitudeOperator m (cutoffAmplitude R.output.cutoff R.input.cutoff R.symbol)
      (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol _ _
        R.output.smooth_cutoff R.input.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude R.symbol _ _
        R.output.compact_support R.input.compact_support)
    have hTquant : ∀ u z, T u z =
        quantize (cutoffSymbol R.output.cutoff R.input.cutoff R.symbol) u z := by
      intro u z
      rw [amplitudeOperator_apply]
      exact (congrFun (quantize_amplitudeSymbol m _
        (isAmplitude_cutoffAmplitude m R.symbol R.isSymbol _ _
          R.output.smooth_cutoff R.input.smooth_cutoff)
        (hasCompactSupport_cutoffAmplitude R.symbol _ _
          R.output.compact_support R.input.compact_support) u) z).symm
    have hTapply (u) (z) : T u z = R.output.cutoff z • R.operator
        (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank R.input.frameIndex)))
          (fun w ↦ (R.input.cutoff w : ℂ)) u) z := by
      rw [hTquant, quantize_cutoffSymbol m R.symbol R.isSymbol _ _
        R.output.smooth_cutoff R.input.smooth_cutoff
        R.output.compact_support R.input.compact_support, R.operator_apply]
    let L : AtlasPseudodifferentialPiece A B l :=
      { chart := R.chart
        chart_mem_atlas := R.chart_mem_atlas
        input := D₀
        output := K₀
        input_support_in_output_frame := fun z hz ↦ (hδU hz).2.2
        output_support_in_input_frame := fun z hz ↦ (hδU hz).2.1
        operator := T
        symbol := cutoffSymbol R.output.cutoff R.input.cutoff R.symbol
        isSymbol := hR
        operator_apply := hTquant }
    have hg : (fun z ↦ (R.input.cutoff z : ℂ)).HasTemperateGrowth :=
      (R.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp R.input.smooth_cutoff)
    have hinput (u : A.smoothSections) :
        SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank R.input.frameIndex)))
          (fun z ↦ (R.input.cutoff z : ℂ)) (D₀.localize R.chart_mem_atlas u) =
            R.input.localize R.chart_mem_atlas u := by
      apply SchwartzMap.ext
      intro z
      rw [SchwartzMap.smulLeftCLM_apply_apply hg]
      change (R.input.cutoff z : ℂ) • D₀.localizedFunction u z = R.input.localizedFunction u z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzt := (R.input.support_subset hz).1
        have hone : δ z = 1 := hδone z (Or.inr hz)
        simp only [AtlasChartCutoff.localizedFunction, hzt, ↓reduceIte]
        change (R.input.cutoff z : ℂ) • ((δ z : ℂ) • _) = _
        rw [hone, Complex.ofReal_one, one_smul]
      · simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
    have heq : L.toLinearMap = R.toLinearMap := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change K₀.extendedFunction (T (D₀.localize R.chart_mem_atlas u)) x =
        R.output.extendedFunction (R.operator (R.input.localize R.chart_mem_atlas u)) x
      by_cases hx : x ∈ R.chart.source ∩ (B.chart R.output.frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, K₀, dite_eq_left hx]
        rw [hTapply, hinput, ← Complex.coe_smul, map_smul, map_smul, smul_smul]
        by_cases hz : R.chart x ∈ tsupport R.output.cutoff
        · rw [hδone _ (Or.inl hz), Complex.ofReal_one, one_mul]
        · simp [image_eq_zero_of_notMem_tsupport hz]
      · simp only [AtlasChartCutoff.extendedFunction, K₀, dite_eq_right hx]
    rw [← heq]
    exact hpiece L
  -- Stage 2: disjoint scalar cutoffs annihilate the leading diagonal symbol.
  have hoffDiagonal {m : ℝ}
      (R : AtlasPseudodifferentialPiece A B m)
      (φ ψ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ)
      (hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ ψ)
      (hzero : ∀ x, φ x * ψ x = 0) :
      IsAtlasPseudodifferentialOperator A B (m - 1)
        ((atlasSectionMul B (fun x ↦ (φ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hφ)).comp
          (R.toLinearMap.comp
            (atlasSectionMul A (fun x ↦ (ψ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hψ)))) := by
    let X := EuclideanSpace ℝ (Fin n)
    let I := 𝓘(ℝ, X)
    let T := atlasSectionMul A (fun x ↦ (ψ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hψ)
    let S := atlasSectionMul B (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    have hcutoff (a : X → ℝ) (ha : ContDiff ℝ ∞ a) (hs : tsupport a ⊆ R.chart.target)
        (χ : M → ℝ) (hχ : ContMDiff I 𝓘(ℝ) ∞ χ) :
        ContDiff ℝ ∞ (fun z ↦ a z * χ (R.chart.symm z)) := by
      apply contDiff_iff_contDiffAt.mpr
      intro z
      by_cases hz : z ∈ tsupport a
      · have hchart := contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (I := I) (n := ∞) R.chart_mem_atlas) (hs hz)
        exact ha.contDiffAt.mul ((hχ.contMDiffAt.comp z hchart).contDiffAt)
      · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hz] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
    let D₀ : AtlasChartCutoff A R.chart :=
      { R.input with
        cutoff := fun z ↦ R.input.cutoff z * ψ (R.chart.symm z)
        smooth_cutoff := hcutoff _ R.input.smooth_cutoff
          (fun z hz ↦ (R.input.support_subset hz).1) ψ hψ
        compact_support := R.input.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans R.input.support_subset }
    let K₀ : AtlasChartCutoff B R.chart :=
      { R.output with
        cutoff := fun z ↦ R.output.cutoff z * φ (R.chart.symm z)
        smooth_cutoff := hcutoff _ R.output.smooth_cutoff
          (fun z hz ↦ (R.output.support_subset hz).1) φ hφ
        compact_support := R.output.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left
        support_subset := tsupport_mul_subset_left.trans R.output.support_subset }
    let L : AtlasPseudodifferentialPiece A B m :=
      { R with input := D₀, output := K₀
               input_support_in_output_frame :=
                 tsupport_mul_subset_left.trans R.input_support_in_output_frame
               output_support_in_input_frame :=
                 tsupport_mul_subset_left.trans R.output_support_in_input_frame }
    have hinput (u : A.smoothSections) :
        D₀.localize R.chart_mem_atlas u = R.input.localize R.chart_mem_atlas (T u) := by
      apply SchwartzMap.ext
      intro z
      by_cases hz : z ∈ tsupport R.input.cutoff
      · have hzc := (R.input.support_subset hz).1
        have hzf := (R.input.support_subset hz).2
        change D₀.localizedFunction u z = R.input.localizedFunction (T u) z
        simp only [AtlasChartCutoff.localizedFunction, hzc, ↓reduceIte]
        change ((R.input.cutoff z * ψ (R.chart.symm z) : ℝ) : ℂ) •
          (EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv R.input.frameIndex (R.chart.symm z) hzf)
              (u.val (R.chart.symm z))) =
          (R.input.cutoff z : ℂ) •
            (EuclideanSpace.equiv (Fin (A.rank R.input.frameIndex)) ℂ).symm
              ((A.frameLinearEquiv R.input.frameIndex (R.chart.symm z) hzf)
                ((ψ (R.chart.symm z) : ℂ) • u.val (R.chart.symm z)))
        rw [map_smul, map_smul, Complex.ofReal_mul, smul_smul]
      · simp [AtlasChartCutoff.localize, AtlasChartCutoff.localizedFunction,
          D₀, image_eq_zero_of_notMem_tsupport hz]
    have houtput (v : 𝓢(X, EuclideanSpace ℂ (Fin (B.rank R.output.frameIndex)))) :
        K₀.extend R.chart_mem_atlas v = S (R.output.extend R.chart_mem_atlas v) := by
      apply Subtype.ext
      funext x
      change K₀.extendedFunction v x = (φ x : ℂ) • R.output.extendedFunction v x
      by_cases hx : x ∈ R.chart.source ∩ (B.chart R.output.frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, K₀, dite_eq_left hx]
        rw [R.chart.left_inv hx.1, Complex.ofReal_mul, smul_smul, mul_comm]
      · simp [AtlasChartCutoff.extendedFunction, K₀, hx]
    have heq : L.toLinearMap = S.comp (R.toLinearMap.comp T) := by
      apply LinearMap.ext
      intro u
      change K₀.extend R.chart_mem_atlas (R.operator (D₀.localize R.chart_mem_atlas u)) = _
      rw [hinput, houtput]
      rfl
    have hsymbol : IsSymbol Set.univ (m - 1) (cutoffSymbol K₀.cutoff D₀.cutoff R.symbol) := by
      have h := hasSymbolExpansion_cutoffSymbol m R.symbol R.isSymbol
        K₀.cutoff D₀.cutoff K₀.smooth_cutoff D₀.smooth_cutoff
        K₀.compact_support D₀.compact_support 1
      have hdiag : (fun x ξ ↦ cutoffAmplitude K₀.cutoff D₀.cutoff R.symbol x x ξ) = 0 := by
        funext x ξ
        have hz : K₀.cutoff x * D₀.cutoff x = 0 := by
          change (R.output.cutoff x * φ (R.chart.symm x)) *
            (R.input.cutoff x * ψ (R.chart.symm x)) = 0
          calc
            _ = (R.output.cutoff x * R.input.cutoff x) *
                (φ (R.chart.symm x) * ψ (R.chart.symm x)) := by ring
            _ = 0 := by rw [hzero, mul_zero]
        simp only [cutoffAmplitude, Pi.zero_apply, hz, zero_smul]
      simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero,
        hdiag, sub_zero] using h
    rw [← heq]
    exact hpieceLower L hsymbol
  have hcoordCutoff
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
      (hcompact : HasCompactSupport χ) (hsupp : tsupport χ ⊆ c.source) :
      ∃ b : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ tsupport b ⊆ c '' tsupport χ ∧
          ∀ z, b z = if z ∈ c.target then χ (c.symm z) else 0 := by
    classical
    let K := c '' tsupport χ
    let b : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun z ↦ if z ∈ c.target then χ (c.symm z) else 0
    have hK : IsCompact K := hcompact.image_of_continuousOn
      (c.continuousOn.mono hsupp)
    have hsub : tsupport b ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro z hz
      have htarget : z ∈ c.target := by
        by_contra h
        exact hz (by simp [b, h])
      have hx : c.symm z ∈ tsupport χ := by
        by_contra h
        exact hz (by simp [b, htarget, image_eq_zero_of_notMem_tsupport h])
      exact ⟨c.symm z, hx, c.right_inv htarget⟩
    refine ⟨b, ?_, hK.of_isClosed_subset (isClosed_tsupport _) hsub, hsub, fun _ ↦ rfl⟩
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨x, hx, rfl⟩ := hz
      have htarget := c.map_source (hsupp hx)
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (n := ∞) hc) htarget
      have hlocal := (hχ.contMDiffAt.comp (c x) hchart).contDiffAt
      apply hlocal.congr_of_eventuallyEq
      filter_upwards [c.open_target.mem_nhds htarget] with y hy
      simp [b, hy]
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hz] with y hy
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hy (hsub h))
  -- Stage 3: a local lower-order symbol realizes the exact doubly localized action.
  have hnearDiagonal {l : ℝ}
      (T : A.smoothSections →ₗ[ℂ] B.smoothSections)
      (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c)
      (hAB : D₀.cutoff = K₀.cutoff)
      (χ : M → ℝ) (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
      (hχc : tsupport χ ⊆ c.source)
      (hone : ∀ y ∈ c '' tsupport χ, D₀.cutoff y = 1)
      (V : Set (EuclideanSpace ℝ (Fin n))) (hV : IsOpen V)
      (hVone : ∀ y ∈ V, χ (c.symm y) = 1)
      (p : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)) (hp : IsSymbol V l p)
      (hact : ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) y,
        quantize p u y = K₀.localize hc
          (atlasSectionMul B (fun x ↦ (χ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hχ)
            (T (atlasSectionMul A (fun x ↦ (χ x : ℂ))
              (Complex.ofRealCLM.contMDiff.comp hχ) (D₀.extend hc u)))) y)
      (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ)
      (hφsupp : tsupport φ ⊆ c.source ∩ c ⁻¹' V) :
      IsAtlasPseudodifferentialOperator A B l
        ((atlasSectionMul B (fun x ↦ (φ x : ℂ)) (Complex.ofRealCLM.contMDiff.comp hφ)).comp
          (T.comp (atlasSectionMul A (fun x ↦ (χ x : ℂ))
            (Complex.ofRealCLM.contMDiff.comp hχ)))) := by
    let Tin := atlasSectionMul A (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)
    let Tout := atlasSectionMul B (fun x ↦ (χ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hχ)
    let S := atlasSectionMul B (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    have hcφ : HasCompactSupport φ := isCompact_univ.of_isClosed_subset
      (isClosed_tsupport φ) (Set.subset_univ _)
    obtain ⟨a, ha, hca, hs, heval⟩ := hcoordCutoff c hc φ hφ hcφ
      (fun x hx ↦ (hφsupp hx).1)
    have haV : tsupport a ⊆ V := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hs hz
      exact (hφsupp hx).2
    let p' := zeroExtendedSymbol V a p
    have hp' : IsSymbol Set.univ l p' := isSymbol_zeroExtendedSymbol V hV l a ha hca haV p hp
    have hcp' : HasCompactSupport p' := hasCompactSupport_zeroExtendedSymbol V a p hca
    let L : AtlasPseudodifferentialPiece A B l :=
      { chart := c
        chart_mem_atlas := hc
        input := D₀
        output := K₀
        input_support_in_output_frame := by
          intro z hz
          exact (K₀.support_subset (by rwa [hAB] at hz)).2
        output_support_in_input_frame := by
          intro z hz
          exact (D₀.support_subset (by rwa [← hAB] at hz)).2
        operator := quantizeSchwartz l p' hp' hcp'
        symbol := p'
        isSymbol := hp'
        operator_apply := quantizeSchwartz_apply l p' hp' hcp' }
    have hrow (z η : EuclideanSpace ℝ (Fin n)) : p' z η = (a z : ℂ) • p z η := by
      by_cases hz : z ∈ V
      · exact zeroExtendedSymbol_apply_of_mem V a p z η hz
      · have haz : a z = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hz (haV h))
        simp [p', zeroExtendedSymbol, hz, haz]
    have hquant (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) z :
        quantize p' u z = (a z : ℂ) • quantize p u z := by
      simp only [quantize, hrow, smul_apply]
      simp_rw [smul_comm _ (a z : ℂ)]
      rw [integral_smul, smul_comm]
    have hinput (u : A.smoothSections) :
        Tin (D₀.extend hc (D₀.localize hc u)) = Tin u := by
      apply Subtype.ext
      funext x
      change (χ x : ℂ) • D₀.extendedFunction (D₀.localize hc u) x = (χ x : ℂ) • u.val x
      by_cases hx : χ x = 0
      · simp [hx]
      · have hxχ : x ∈ tsupport χ := subset_tsupport χ hx
        have hxc := hχc hxχ
        have hcut : D₀.cutoff (c x) = 1 := hone _ ⟨x, hxχ, rfl⟩
        have hxs : c x ∈ tsupport D₀.cutoff := subset_tsupport _
          (show D₀.cutoff (c x) ≠ 0 by rw [hcut]; norm_num)
        have hxf : x ∈ (A.chart D₀.frameIndex).baseSet := by
          have h := (D₀.support_subset hxs).2
          change c.symm (c x) ∈ (A.chart D₀.frameIndex).baseSet at h
          rwa [c.left_inv hxc] at h
        have hdom : x ∈ c.source ∩ (A.chart D₀.frameIndex).baseSet := ⟨hxc, hxf⟩
        simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hdom, hcut,
          Complex.ofReal_one, one_smul]
        change (χ x : ℂ) • (A.frameLinearEquiv D₀.frameIndex x hxf).symm
          ((EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ)
            (D₀.localizedFunction u (c x))) = _
        have hcoord : atlasSectionInChart A c D₀.frameIndex u.val (c x) =
            (EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ).symm
              ((A.chart D₀.frameIndex ⟨x, u.val x⟩).2) := by
          unfold atlasSectionInChart
          congr 2
          exact congrArg (fun y ↦ A.chart D₀.frameIndex
            (⟨y, u.val y⟩ : TotalSpace Unit E)) (c.left_inv hxc)
        simp only [AtlasChartCutoff.localizedFunction, ite_eq_left (c.map_source hxc),
          hcut, Complex.ofReal_one, one_smul, hcoord,
          ContinuousLinearEquiv.apply_symm_apply]
        change (χ x : ℂ) • (A.frameLinearEquiv D₀.frameIndex x hxf).symm
          ((A.frameLinearEquiv D₀.frameIndex x hxf) (u.val x)) = _
        rw [LinearEquiv.symm_apply_apply]
    have heq : L.toLinearMap = S.comp (T.comp Tin) := by
      apply LinearMap.ext
      intro u
      apply Subtype.ext
      funext x
      change K₀.extendedFunction (L.operator (D₀.localize hc u)) x = (φ x : ℂ) • (T (Tin u)).val x
      by_cases hx : φ x = 0
      · rw [hx, Complex.ofReal_zero, zero_smul]
        by_cases hxc : x ∈ c.source ∩ (B.chart K₀.frameIndex).baseSet
        · simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hxc]
          rw [L.operator_apply, hquant, heval, ite_eq_left (c.map_source hxc.1),
            c.left_inv hxc.1, hx]
          simp
        · simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hxc]
      · have hxs := subset_tsupport φ hx
        have hxc := (hφsupp hxs).1
        have hxV := (hφsupp hxs).2
        have hxχ : χ x = 1 := by simpa only [c.left_inv hxc] using hVone (c x) hxV
        have hxχs : x ∈ tsupport χ := subset_tsupport _ (show χ x ≠ 0 by rw [hxχ]; norm_num)
        have hcut : K₀.cutoff (c x) = 1 := by rw [← hAB]; exact hone _ ⟨x, hxχs, rfl⟩
        have hxf : x ∈ (B.chart K₀.frameIndex).baseSet := by
          have h := (K₀.support_subset (subset_tsupport _ (show K₀.cutoff (c x) ≠ 0 by
            rw [hcut]; norm_num))).2
          change c.symm (c x) ∈ (B.chart K₀.frameIndex).baseSet at h
          rwa [c.left_inv hxc] at h
        have hdom : x ∈ c.source ∩ (B.chart K₀.frameIndex).baseSet := ⟨hxc, hxf⟩
        simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hdom, hcut,
          Complex.ofReal_one, one_smul]
        rw [L.operator_apply, hquant, heval, ite_eq_left (c.map_source hxc), c.left_inv hxc,
          hact]
        change (B.frameLinearEquiv K₀.frameIndex x hxf).symm
          ((EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ)
            ((φ x : ℂ) • K₀.localize hc (Tout (T (Tin (D₀.extend hc (D₀.localize hc u)))))
              (c x))) = _
        rw [hinput]
        have hcoord : atlasSectionInChart B c K₀.frameIndex (Tout (T (Tin u))).val (c x) =
            (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
              ((B.chart K₀.frameIndex ⟨x, (Tout (T (Tin u))).val x⟩).2) := by
          unfold atlasSectionInChart
          congr 2
          exact congrArg (fun y ↦ B.chart K₀.frameIndex
            (⟨y, (Tout (T (Tin u))).val y⟩ : TotalSpace Unit F)) (c.left_inv hxc)
        change (B.frameLinearEquiv K₀.frameIndex x hxf).symm
          ((EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ)
            ((φ x : ℂ) • K₀.localizedFunction (Tout (T (Tin u))) (c x))) = _
        simp only [AtlasChartCutoff.localizedFunction, ite_eq_left (c.map_source hxc),
          hcut, Complex.ofReal_one, one_smul, hcoord, map_smul,
          ContinuousLinearEquiv.apply_symm_apply]
        change (φ x : ℂ) • (B.frameLinearEquiv K₀.frameIndex x hxf).symm
          ((B.frameLinearEquiv K₀.frameIndex x hxf) ((χ x : ℂ) • (T (Tin u)).val x)) = _
        rw [LinearEquiv.symm_apply_apply, hxχ, Complex.ofReal_one, one_smul]
    rw [← heq]
    exact hpiece L
  -- Stage 4: combine overlapping symbols, then glue by a finite output partition.
  have hfamilyLower {m : ℝ} {N : ℕ}
      (J : Fin N → AtlasPseudodifferentialPiece A B m)
      (hglobal : IsAtlasGlobalSymbol A B (m - 1)
        (∑ j, (J j).globalSymbol).val) :
      IsAtlasPseudodifferentialOperator A B (m - 1) (∑ j, (J j).toLinearMap) := by
    let T := ∑ j, (J j).toLinearMap
    -- Combine the symbols of all overlapping pieces before using cancellation.
    have hlocal (x : M) : ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
        ∀ (φ : M → ℝ) (hφ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ φ),
          tsupport φ ⊆ U → IsAtlasPseudodifferentialOperator A B (m - 1)
            ((atlasSectionMul B (fun y ↦ (φ y : ℂ))
              (Complex.ofRealCLM.contMDiff.comp hφ)).comp T) := by
      let c := chartAt (EuclideanSpace ℝ (Fin n)) x
      obtain ⟨e, he⟩ := A.covers x
      obtain ⟨f, hf⟩ := B.covers x
      have hxc : x ∈ c.source := mem_chart_source _ x
      have hz : c x ∈ atlasSymbolChartDomain A B c e f := by
        refine ⟨⟨c.map_source hxc, ?_⟩, ?_⟩
        · simpa only [Set.mem_preimage, c.left_inv hxc] using he
        · simpa only [Set.mem_preimage, c.left_inv hxc] using hf
      obtain ⟨χ, hχ, D₀, K₀, rfl, rfl, _, hχsupp, hAB, hone,
        V, p, hV, hxV, hVD, hVone, hp, hdiff, hact⟩ :=
        exists_common_local_symbols_with_cutoffs A B J c (chart_mem_atlas _ x) e f (c x) hz
      let Tin := atlasSectionMul A (fun y ↦ (χ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hχ)
      let Tout := atlasSectionMul B (fun y ↦ (χ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hχ)
      let pSum : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex) := ∑ j, p j
      have hcoord : atlasGlobalSymbolInChart A B (∑ j, (J j).globalSymbol).val
          c D₀.frameIndex K₀.frameIndex =
          ∑ j, atlasGlobalSymbolInChart A B (J j).globalSymbolFunction
            c D₀.frameIndex K₀.frameIndex := by
        funext z η
        apply ContinuousLinearMap.ext
        intro v
        by_cases hframes : c.symm z ∈ (A.chart D₀.frameIndex).baseSet ∧
            c.symm z ∈ (B.chart K₀.frameIndex).baseSet
        all_goals
          simp [atlasGlobalSymbolInChart, hframes, AtlasPseudodifferentialPiece.globalSymbol]
      have hpSum : IsSymbol V (m - 1) pSum := by
        have hd : IsSymbol V (m - 1)
            (∑ j, (p j - atlasGlobalSymbolInChart A B (J j).globalSymbolFunction
              c D₀.frameIndex K₀.frameIndex)) :=
          (symbolSpace V hV (m - 1) (A.rank D₀.frameIndex) (B.rank K₀.frameIndex)).sum_mem
            (fun j _ ↦ hdiff j)
        have hg := (hglobal c (chart_mem_atlas _ x) D₀.frameIndex K₀.frameIndex).restrict hVD
        rw [hcoord] at hg
        have h := hd.add hV hg
        simpa only [Finset.sum_sub_distrib, sub_add_cancel] using h
      -- Symbol growth and Schwartz decay make every frequency integrand integrable.
      have hInt (a : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex))
          (ha : IsSymbol Set.univ m a)
          (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))))
          (z : EuclideanSpace ℝ (Fin n)) :
          Integrable (fun η ↦ Complex.exp (Complex.I * (inner ℝ z η : ℂ)) •
            a z η (fourierSG u η)) := by
        let X := EuclideanSpace ℝ (Fin n)
        have hg : (a z).HasTemperateGrowth := by
          refine ⟨?_, ?_⟩
          · have hs : ContDiff ℝ ∞ (Function.uncurry a) := by
              simpa only [Set.univ_prod_univ, contDiffOn_univ] using ha.1
            exact hs.comp (contDiff_const.prodMk contDiff_id)
          · intro j
            obtain ⟨C, hC, hbound⟩ := ha.2 {z} (Set.subset_univ _) isCompact_singleton 0 j
            refine ⟨⌈m - (j : ℝ)⌉₊, C, fun η ↦ ?_⟩
            have h := hbound z (Set.mem_singleton z) η
            simp only [symbolDerivative, norm_iteratedFDeriv_zero] at h
            apply h.trans
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.rpow_natCast]
            exact Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg η]) (Nat.le_ceil _)
        have hphase :
            (fun η : X ↦ Complex.exp (Complex.I * (inner ℝ z η : ℂ))).HasTemperateGrowth := by
          simpa [Function.comp_def, mul_comm] using
            Complex.hasTemperateGrowth_exp_mul_I.comp (innerSL ℝ z).hasTemperateGrowth
        have hπ : (2 * Real.pi)⁻¹ ≠ 0 :=
          inv_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        let d : X ≃L[ℝ] X :=
          (LinearEquiv.smulOfNeZero ℝ X ((2 * Real.pi)⁻¹) hπ).toContinuousLinearEquiv
        let w := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ d (FourierTransform.fourier u)
        exact (SchwartzMap.bilinLeftCLM
          (ContinuousLinearMap.id ℂ
            (EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)) →L[ℂ]
              EuclideanSpace ℂ (Fin (B.rank K₀.frameIndex)))).flip
            (hphase.smul hg) w).integrable
      have hquant
          (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))))
          (z : EuclideanSpace ℝ (Fin n)) :
          quantize pSum u z = ∑ j, quantize (p j) u z := by
        simp only [quantize, pSum, Finset.sum_apply, _root_.sum_apply,
          Finset.smul_sum]
        rw [integral_finsetSum _ (fun j _ ↦ hInt (p j) (hp j) u z), Finset.smul_sum]
      have hsumact
          (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))))
          (z : EuclideanSpace ℝ (Fin n)) :
          quantize pSum u z = K₀.localize (chart_mem_atlas _ x)
            (Tout (T (Tin (D₀.extend (chart_mem_atlas _ x) u)))) z := by
        rw [hquant]
        simp only [hact]
        change (∑ j, K₀.localizeLinearMap (chart_mem_atlas _ x)
            (Tout ((J j).toLinearMap (Tin (D₀.extend (chart_mem_atlas _ x) u)))) z) =
          K₀.localizeLinearMap (chart_mem_atlas _ x)
            (Tout (T (Tin (D₀.extend (chart_mem_atlas _ x) u)))) z
        simp only [T, LinearMap.sum_apply, map_sum, _root_.sum_apply]
      refine ⟨c.source ∩ c ⁻¹' V, c.isOpen_inter_preimage hV, ⟨hxc, hxV⟩, ?_⟩
      intro φ hφ hφsupp
      let S := atlasSectionMul B (fun y ↦ (φ y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hφ)
      let hψ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ (fun y ↦ 1 - χ y) :=
        contMDiff_const.sub hχ
      let Tin' := atlasSectionMul A (fun y ↦ ((1 - χ y : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp hψ)
      have hnear : IsAtlasPseudodifferentialOperator A B (m - 1) (S.comp (T.comp Tin)) :=
        hnearDiagonal T c (chart_mem_atlas _ x) D₀ K₀ hAB χ hχ
          (fun y hy ↦ (hχsupp hy).1.1) hone V hV hVone pSum hpSum hsumact φ hφ hφsupp
      have hzero (y : M) : φ y * (1 - χ y) = 0 := by
        by_cases hy : φ y = 0
        · simp [hy]
        · have hs := hφsupp (subset_tsupport _ hy)
          have hχy : χ y = 1 := by
            simpa only [c.left_inv hs.1] using hVone (c y) hs.2
          simp [hχy]
      have hfar : IsAtlasPseudodifferentialOperator A B (m - 1) (S.comp (T.comp Tin')) := by
        have hj (j : Fin N) : IsAtlasPseudodifferentialOperator A B (m - 1)
            (S.comp ((J j).toLinearMap.comp Tin')) :=
          hoffDiagonal (J j) φ (fun y ↦ 1 - χ y) hφ hψ hzero
        have h := hsum (fun j ↦ S.comp ((J j).toLinearMap.comp Tin'))
          Finset.univ (fun j _ ↦ hj j)
        have heq : S.comp (T.comp Tin') = ∑ j, S.comp ((J j).toLinearMap.comp Tin') := by
          ext u
          simp only [LinearMap.comp_apply, T, LinearMap.sum_apply, map_sum]
        rw [heq]
        exact h
      have hsplit : S.comp T = S.comp (T.comp Tin) + S.comp (T.comp Tin') := by
        have hin : Tin + Tin' = LinearMap.id := by
          ext u y
          change (χ y : ℂ) • u.val y + ((1 - χ y : ℝ) : ℂ) • u.val y = u.val y
          rw [← add_smul, ← Complex.ofReal_add]
          simp
        rw [← LinearMap.comp_add, ← LinearMap.comp_add, hin, LinearMap.comp_id]
      rw [hsplit]
      exact hadd _ _ hnear hfar
    -- A finite smooth output partition glues the exact local lower-order maps.
    choose U hU hxU hcut using hlocal
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU
      (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
    let index : Fin s.card ≃ s := s.equivFin.symm
    let V (j : Fin s.card) := U (index j)
    have hcover : Set.univ ⊆ ⋃ j, V j := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs hx)
      exact Set.mem_iUnion.mpr ⟨index.symm ⟨y, hy⟩, by simpa [V] using hxy⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ V
      (fun j ↦ hU (index j)) hcover
    let L (j : Fin s.card) :=
      (atlasSectionMul B (fun y ↦ (ρ j y : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (ρ j).contMDiff)).comp T
    have hL (j : Fin s.card) : IsAtlasPseudodifferentialOperator A B (m - 1) (L j) :=
      hcut (index j) (ρ j) (ρ j).contMDiff (hρ j)
    have hsumEq : (∑ j, L j) = T := by
      ext u y
      simp only [LinearMap.sum_apply, Submodule.coe_sum, Finset.sum_apply]
      change (∑ j, (ρ j y : ℂ) • (T u).val y) = (T u).val y
      rw [← Finset.sum_smul, ← Complex.ofReal_sum, ← finsum_eq_sum_of_fintype,
        ρ.sum_eq_one (Set.mem_univ y)]
      simp
    change IsAtlasPseudodifferentialOperator A B (m - 1) T
    rw [← hsumEq]
    exact hsum L Finset.univ (fun j _ ↦ hL j)
  -- Apply order reduction to the combined original symbols, then restore its same remainder.
  constructor
  · intro hP
    obtain ⟨N, J, hJ⟩ := P.isPseudodifferentialOperator
    have hg : IsAtlasGlobalSymbol A B (m - 1) (∑ j, (J j).globalSymbol).val := by
      have hclass : atlasGlobalPrincipalSymbolClass A B m (∑ j, (J j).globalSymbol) =
          atlasGlobalPrincipalSymbolClass A B m 0 := by
        rw [← P.principalSymbol_eq_of_representation N J hJ, map_zero]
        exact hP
      simpa only [Submodule.coe_zero, sub_zero] using
        (atlasGlobalPrincipalSymbolClass_eq_iff A B m _ 0).mp hclass
    have hfamily := hfamilyLower J hg
    have hrem := hsmooth (m - 1) (P.toLinearMap - ∑ j, (J j).toLinearMap) hJ
    have heq : P.toLinearMap = (∑ j, (J j).toLinearMap) +
        (P.toLinearMap - ∑ j, (J j).toLinearMap) := by abel
    rw [heq]
    exact hadd _ _ hfamily hrem
  · intro hP
    obtain ⟨N, L, hL⟩ := hP
    let L' (j : Fin N) : AtlasPseudodifferentialPiece A B m :=
      { L j with isSymbol := (L j).isSymbol.mono (by linarith) }
    rw [P.principalSymbol_eq_of_representation N L' hL]
    rw [← map_zero (atlasGlobalPrincipalSymbolClass A B m),
      atlasGlobalPrincipalSymbolClass_eq_iff]
    have hsame (j : Fin N) : (L' j).globalSymbol.val = (L j).globalSymbol.val := rfl
    simp only [Submodule.coe_sum, hsame, Submodule.coe_zero, sub_zero]
    have hlow := (∑ j, (L j).globalSymbol).property
    change IsAtlasGlobalSymbol A B (m - 1) (∑ j, (L j).globalSymbol).val at hlow
    simpa only [Submodule.coe_sum] using hlow

end AtlasPseudodifferentialOperator

end AtiyahSinger
