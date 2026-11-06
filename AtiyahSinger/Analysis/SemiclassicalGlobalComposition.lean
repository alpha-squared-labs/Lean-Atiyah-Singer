/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalQuantization
public import AtiyahSinger.Analysis.IdentityQuantization
public import AtiyahSinger.Analysis.PseudodifferentialCutoff
public import AtiyahSinger.Analysis.SemiclassicalCoordinateChange
public import AtiyahSinger.Analysis.SemiclassicalFrameChange
public import AtiyahSinger.Analysis.SemiclassicalGlobalQuantization
public import AtiyahSinger.Analysis.SemiclassicalRawComposition
public import AtiyahSinger.Analysis.SobolevLocalization

import all AtiyahSinger.Analysis.CoordinateChange
import all AtiyahSinger.Analysis.GlobalComposition
import all AtiyahSinger.Analysis.SemiclassicalCoordinateChange
import all AtiyahSinger.Analysis.SemiclassicalFrameChange
import all AtiyahSinger.Analysis.SemiclassicalRawComposition

/-!
# Estimates for the original global scaled quantization pieces

Public module ID: M2306.

Sources: SG III.3.9 and III.3.17(iii), with the quantitative supplementary
amplitude and raw-composition bounds of M2295 and M2305. SG means H. Blaine
Lawson, Jr. and Marie-Louise Michelsohn, *Spin Geometry* (Princeton University
Press, 1989).

The original patch, chart, frames and cutoffs stay fixed before frequency
scaling. An additional pair of scalar multipliers whose pointwise product is
zero gives an actual zero-diagonal amplitude. Its common first-order Sobolev
bound includes the entire original global section action. Compact plateaus are
chosen internally only to localize and extend that same action exactly once.

The native common-chart leading estimate retains the original cutoff amplitude,
coordinate pullbacks and both frame multipliers in one actual small error.

The original finite presentation gives both inverse-product errors with one
common positive-scale bound on the same smooth Sobolev inputs. The original
partition and exact identity patch actions remain in both factors of this assembly. No
zero-index conclusion or norm continuity at parameter zero is asserted here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold Set
open scoped Manifold ContDiff SchwartzMap

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option maxSynthPendingDepth 15

set_option maxHeartbeats 400000 in
-- Bound the kernel budget after the recorded native-record timeout; keep fixed fields explicit.
/-- Fixed scalar cutoffs preserve the common bound of the same scaled native patch. -/
private theorem QuantizationPatch.exists_frequencyScale_cutoff_sobolev_bound
    (Q : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (f g : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ g) (s : ℝ)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖B.smoothToSobolev s
          (((Q.toPiece
              (frequencyScaleGlobalSymbolSpace a t ht ht₁)).cutoff f g hf hg).toLinearMap u)‖ ≤
          C * ‖A.smoothToSobolev s u‖ := by
  /- The multiplied input and output cutoffs have fixed chart supports. Compose
  their original Sobolev bounds with the common bound of the original raw symbol. -/
  let input := Q.input.mulSmooth Q.chart_mem_atlas g hg
  let output := Q.output.mulSmooth Q.chart_mem_atlas f hf
  obtain ⟨Ci, hCi, hinput⟩ := input.exists_norm_localize_sobolev_le Q.chart_mem_atlas A s
  obtain ⟨Co, hCo, houtput⟩ := output.exists_norm_extend_sobolev_le Q.chart_mem_atlas B s
  obtain ⟨Cp, hCp, hraw⟩ := exists_frequencyScale_raw_sobolev_bound
    (Q.isSymbol_localSymbol a) (Q.hasCompactSupport_localSymbol a.val) s
  refine ⟨Co * Cp * Ci, mul_nonneg (mul_nonneg hCo hCp) hCi, ?_⟩
  intro t ht ht₁ u
  let scaled := frequencyScaleGlobalSymbolSpace a t ht ht₁
  let Pt := (Q.toPiece scaled).operator
  have hPt (v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
      (x : EuclideanSpace ℝ (Fin n)) :
      Pt v x = quantize (frequencyScaleSymbol t (Q.localSymbol a.val)) v x := by
    rw [(Q.toPiece scaled).operator_apply]
    change quantize (Q.localSymbol (frequencyScaleGlobalSymbol t a.val)) v x = _
    rw [Q.localSymbol_frequencyScale]
  have hp := hraw t ht ht₁ Pt hPt (input.localize Q.chart_mem_atlas u)
  change ‖B.smoothToSobolev s
    (output.extend Q.chart_mem_atlas (Pt (input.localize Q.chart_mem_atlas u)))‖ ≤ _
  calc
    _ ≤ Co * ‖schwartzSobolevCoordinate s
        (Pt (input.localize Q.chart_mem_atlas u))‖ := houtput _
    _ ≤ Co * (Cp * ‖schwartzSobolevCoordinate s
        (input.localize Q.chart_mem_atlas u)‖) :=
      mul_le_mul_of_nonneg_left hp hCo
    _ ≤ Co * (Cp * (Ci * ‖A.smoothToSobolev s u‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hinput u) hCp) hCo
    _ = _ := by ring

set_option maxHeartbeats 1500000 in
-- Use the actual zero-diagonal amplitude, retaining its complete global section action.
/-- Disjoint scalar factors give a uniform small bound for the original scaled global patch. -/
theorem QuantizationPatch.exists_frequencyScale_cutoff_sobolev_bound_of_mul_eq_zero
    (Q : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (f g : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ g)
    (hfg : ∀ x, f x * g x = 0) (s : ℝ)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖B.smoothToSobolev s
          (((Q.toPiece
              (frequencyScaleGlobalSymbolSpace a t ht ht₁)).cutoff f g hf hg).toLinearMap u)‖ ≤
          C * t * ‖A.smoothToSobolev s u‖ := by
  /- Choose a plateau for the complete original input support and another for
  the complete output support. The original input/output factors remain in the
  actual amplitude, whose diagonal vanishes by f*g=0. The two plateaus merely
  identify the same Schwartz action with its original global section action. -/
  classical
  let := Q.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let L := (Q.toPiece a).cutoff f g hf hg
  let Ui := Q.chart.target ∩ Q.chart.symm ⁻¹' L.input.frame.baseSet
  let Uo := Q.chart.target ∩ Q.chart.symm ⁻¹' L.output.frame.baseSet
  have hUi : IsOpen Ui := Q.chart.isOpen_inter_preimage_symm L.input.frame.open_baseSet
  have hUo : IsOpen Uo := Q.chart.isOpen_inter_preimage_symm L.output.frame.open_baseSet
  obtain ⟨ρ, hρ, hcρ, hρUi, hρone⟩ := exists_compact_cutoff_one_near
    (tsupport L.input.cutoff) Ui L.input.compact_support hUi L.input.support_subset
  obtain ⟨σ, hσ, hcσ, hσUo, hσone⟩ := exists_compact_cutoff_one_near
    (tsupport L.output.cutoff) Uo L.output.compact_support hUo L.output.support_subset
  let I : BundleChartCutoff (r := r) E Q.chart :=
    { L.input with
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := hρUi }
  let O : BundleChartCutoff (r := q) F Q.chart :=
    { L.output with
      cutoff := σ
      smooth_cutoff := hσ
      compact_support := hcσ
      support_subset := hσUo }
  let d := cutoffAmplitude L.output.cutoff L.input.cutoff (Q.localSymbol a.val)
  have hd : IsAmplitude 0 d := isAmplitude_cutoffAmplitude 0 (Q.localSymbol a.val)
    (Q.isSymbol_localSymbol a) _ _ L.output.smooth_cutoff L.input.smooth_cutoff
  have hcd : HasCompactSupport (Function.uncurry d) :=
    hasCompactSupport_cutoffAmplitude _ _ _ L.output.compact_support L.input.compact_support
  have hdiag (x ξ : X) : d x x ξ = 0 := by
    have hscalar : L.output.cutoff x * L.input.cutoff x = 0 := by
      change (Q.output.cutoff x * f (Q.chart.symm x)) *
        (Q.input.cutoff x * g (Q.chart.symm x)) = 0
      calc
        _ = (Q.output.cutoff x * Q.input.cutoff x) *
            (f (Q.chart.symm x) * g (Q.chart.symm x)) := by ring
        _ = 0 := by rw [hfg, mul_zero]
    change (L.output.cutoff x * L.input.cutoff x) • Q.localSymbol a.val x ξ = 0
    rw [hscalar, zero_smul]
  obtain ⟨Cd, hCd, hsmall⟩ := hd.exists_frequencyScale_sobolev_bound_of_diag_eq_zero hcd hdiag s
  obtain ⟨Ci, hCi, hinput⟩ := I.exists_norm_localize_sobolev_le Q.chart_mem_atlas A s
  obtain ⟨Co, hCo, houtput⟩ := O.exists_norm_extend_sobolev_le Q.chart_mem_atlas B s
  have hgrowth : (fun x ↦ (L.input.cutoff x : ℂ)).HasTemperateGrowth :=
    (L.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff)
  have hI (u : smoothSections (n := n) (r := r) E) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun x ↦ (L.input.cutoff x : ℂ)) (I.localize Q.chart_mem_atlas u) =
        L.input.localize L.chart_mem_atlas u := by
    apply SchwartzMap.ext
    intro x
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth]
    change (L.input.cutoff x : ℂ) •
        (if x ∈ Q.chart.target then (ρ x : ℂ) •
          sectionInChart E Q.chart Q.input.frame u.val x else 0) =
      if x ∈ Q.chart.target then (L.input.cutoff x : ℂ) •
        sectionInChart E Q.chart Q.input.frame u.val x else 0
    by_cases hx : x ∈ tsupport L.input.cutoff
    · have hxt : x ∈ Q.chart.target := (L.input.support_subset hx).1
      have hρx : ρ x = 1 := interior_subset (s := {x | ρ x = 1}) (hρone hx)
      simp only [ite_eq_left hxt, hρx, Complex.ofReal_one, one_smul]
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero,
        zero_smul, ite_self]
  refine ⟨Co * Cd * Ci, mul_nonneg (mul_nonneg hCo hCd) hCi, ?_⟩
  intro t ht ht₁ u
  let Lt := (Q.toPiece (frequencyScaleGlobalSymbolSpace a t ht ht₁)).cutoff f g hf hg
  have hscale : frequencyScaleAmplitude t d =
      cutoffAmplitude Lt.output.cutoff Lt.input.cutoff Lt.symbol := by
    rw [show Lt.symbol = Q.localSymbol (frequencyScaleGlobalSymbol t a.val) from rfl,
      Q.localSymbol_frequencyScale]
    rfl
  have hsame : amplitudeOperator 0 (frequencyScaleAmplitude t d)
      (hd.frequencyScale t ht ht₁) (hasCompactSupport_frequencyScaleAmplitude t hcd) =
        Lt.coordinateOperator := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    rw [amplitudeOperator_apply, PseudodifferentialPiece.coordinateOperator,
      amplitudeOperator_apply, hscale]
  have hsmall' : ‖schwartzSobolevCoordinate s
      (Lt.coordinateOperator (I.localize Q.chart_mem_atlas u))‖ ≤
        Cd * t * ‖schwartzSobolevCoordinate s (I.localize Q.chart_mem_atlas u)‖ := by
    simpa only [hsame] using hsmall t ht ht₁ (I.localize Q.chart_mem_atlas u)
  have hvalue (z : X) : Lt.coordinateOperator (I.localize Q.chart_mem_atlas u) z =
      (L.output.cutoff z : ℂ) • Lt.operator (L.input.localize L.chart_mem_atlas u) z := by
    rw [Lt.coordinateOperator_apply]
    change L.output.cutoff z •
        Lt.operator (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun y ↦ (L.input.cutoff y : ℂ)) (I.localize Q.chart_mem_atlas u)) z =
      (L.output.cutoff z : ℂ) • Lt.operator (L.input.localize L.chart_mem_atlas u) z
    rw [hI]
    exact (Complex.coe_smul _ _).symm
  have hreconstruct : O.extend Q.chart_mem_atlas
      (Lt.coordinateOperator (I.localize Q.chart_mem_atlas u)) = Lt.toLinearMap u := by
    apply Subtype.ext
    funext x
    change (if x ∈ Q.chart.source then (σ (Q.chart x) : ℂ) •
        Q.output.frame.symmL ℂ x
          (Lt.coordinateOperator (I.localize Q.chart_mem_atlas u) (Q.chart x)) else 0) =
      if x ∈ Q.chart.source then (L.output.cutoff (Q.chart x) : ℂ) •
        Q.output.frame.symmL ℂ x
          (Lt.operator (L.input.localize L.chart_mem_atlas u) (Q.chart x)) else 0
    by_cases hx : x ∈ Q.chart.source
    · simp only [ite_eq_left hx]
      rw [hvalue, map_smul, smul_smul]
      by_cases hz : Q.chart x ∈ tsupport L.output.cutoff
      · have hσx : σ (Q.chart x) = 1 :=
          interior_subset (s := {x | σ x = 1}) (hσone hz)
        rw [hσx, Complex.ofReal_one, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, mul_zero]
    · simp only [ite_eq_right hx]
  rw [← hreconstruct]
  calc
    _ ≤ Co * ‖schwartzSobolevCoordinate s
        (Lt.coordinateOperator (I.localize Q.chart_mem_atlas u))‖ := houtput _
    _ ≤ Co * (Cd * t * ‖schwartzSobolevCoordinate s
        (I.localize Q.chart_mem_atlas u)‖) := mul_le_mul_of_nonneg_left hsmall' hCo
    _ ≤ Co * (Cd * t * (Ci * ‖A.smoothToSobolev s u‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hinput u) (mul_nonneg hCd ht.le)) hCo
    _ = _ := by ring

set_option maxHeartbeats 2500000 in
-- Three actual positive-scale errors retain the same chart and both native frames.
omit [SecondCountableTopology M] in
/-- The same native cutoff patch has a fixed common-chart leading symbol and a small error. -/
private theorem QuantizationPatch.exists_frequencyScale_localized_leading_symbol
    (Q : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (f g : M → ℝ)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ g)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (A : BundleChartCutoff (r := r) E c) (B : BundleChartCutoff (r := q) F c)
    (hAB : A.cutoff = B.cutoff)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hbase : Q.chart.symm ''
      (tsupport ((Q.toPiece a).cutoff f g hf hg).output.cutoff ∪
        tsupport ((Q.toPiece a).cutoff f g hf hg).input.cutoff) ⊆
          c.source ∩ A.frame.baseSet ∩ B.frame.baseSet)
    (hone : c '' (Q.chart.symm ''
      (tsupport ((Q.toPiece a).cutoff f g hf hg).output.cutoff ∪
        tsupport ((Q.toPiece a).cutoff f g hf hg).input.cutoff)) ⊆
          interior {z | A.cutoff z = 1})
    (hoverlap : tsupport A.cutoff ⊆ c.symm ⁻¹'
      (Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet)) (s : ℝ) :
    letI := A.frame_mem_atlas
    letI := B.frame_mem_atlas
    let L := (Q.toPiece a).cutoff f g hf hg
    let V := symbolChartDomain E F c A.frame B.frame ∩ c.symm ⁻¹'
      (Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet)
    ∃ d : SymbolFunction n r q, IsSymbol univ 0 d ∧ HasCompactSupport d ∧
      tsupport d ⊆ tsupport A.cutoff ∧
      (∀ x ∈ V, ∀ ξ,
        d x ξ = globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame x ξ) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
        ∀ D : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)) →L[ℂ]
          𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
        (∀ u x, D u x = quantize (frequencyScaleSymbol h d) u x) →
        ∀ u, ‖schwartzSobolevCoordinate s
          (B.localize hc (((Q.toPiece
            (frequencyScaleGlobalSymbolSpace a h hh hh₁)).cutoff f g hf hg).toLinearMap
              (A.extend hc u)) - D u)‖ ≤ C * h * ‖schwartzSobolevCoordinate s u‖ := by
  /- Choose source, common-chart and frame controls before h. The actual native
  cutoff amplitude first differs from its diagonal quantizer by O(h). Transport
  this complete error through the same fixed coordinate maps. The actual raw
  coordinate change and the actual matrix change contribute two further O(h)
  errors. Their diagonal is the original native global symbol, including both
  cutoffs. No arbitrary localized full symbol or smoothing norm is substituted. -/
  classical
  let L := (Q.toPiece a).cutoff f g hf hg
  let := L.input.frame_mem_atlas
  let := L.output.frame_mem_atlas
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let U := L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
  let V := symbolChartDomain E F c A.frame B.frame ∩ c.symm ⁻¹' U
  have hV : IsOpen V :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_symbolChartDomain E F c A.frame B.frame)
      ((L.chart.open_source.inter L.input.frame.open_baseSet).inter L.output.frame.open_baseSet)
  have hAV : tsupport A.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨A.support_subset hz, (B.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  let e : OpenPartialHomeomorph X X := L.chart.symm.trans c
  have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
  have hqM := subset_maximalAtlas (I := I) (n := ∞) L.chart_mem_atlas
  have he : ContDiffOn ℝ ∞ e e.source := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hcM hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hqM hz.1)).contDiffAt).contDiffWithinAt
  have hψ : ContDiffOn ℝ ∞ e.symm e.target := by
    intro z hz
    exact (((contMDiffAt_of_mem_maximalAtlas hqM hz.2).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1)).contDiffAt).contDiffWithinAt
  have hKe : K ⊆ e.source := by
    intro z hz
    have hb := hbase ⟨z, hz, rfl⟩
    refine ⟨?_, hb.1.1⟩
    rcases hz with hz | hz
    · exact (L.output.support_subset hz).1
    · exact (L.input.support_subset hz).1
  have hVe : V ⊆ e.target := fun z hz ↦ ⟨hz.1.1.1, hz.2.1.1⟩
  have heKone : e '' K ⊆ interior {z | A.cutoff z = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hone ⟨L.chart.symm z, ⟨z, hz, rfl⟩, rfl⟩
  obtain ⟨χ, hχ, hcχ, hχe, hχone⟩ :=
    exists_compact_cutoff_one_near K e.source hK e.open_source hKe
  -- The actual source amplitude and its fixed diagonal retain every original cutoff.
  let amp := cutoffAmplitude L.output.cutoff L.input.cutoff L.symbol
  have hamp : IsAmplitude 0 amp := isAmplitude_cutoffAmplitude 0 L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
  have hcamp : HasCompactSupport (Function.uncurry amp) :=
    hasCompactSupport_cutoffAmplitude _ _ _ L.output.compact_support L.input.compact_support
  let d₀ : SymbolFunction n r q := fun x ξ ↦
    ((L.output.cutoff x * L.input.cutoff x : ℝ) : ℂ) • L.symbol x ξ
  have hd₀ : IsSymbol univ 0 d₀ := by
    let A₀ : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
      fun x ↦ ((L.output.cutoff x * L.input.cutoff x : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin q))
    let B₀ : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
      fun _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))
    have hA₀ : ContDiffOn ℝ ∞ A₀ univ :=
      ((Complex.ofRealCLM.contDiff.comp
        (L.output.smooth_cutoff.mul L.input.smooth_cutoff)).smul contDiff_const).contDiffOn
    have hB₀ : ContDiffOn ℝ ∞ B₀ univ := contDiffOn_const
    convert isSymbol_matrixSymbol univ isOpen_univ 0 L.symbol L.isSymbol
      A₀ B₀ hA₀ hB₀ using 1
    funext x ξ
    simp [d₀, A₀, B₀, matrixSymbol]
  have hcd₀ : HasCompactSupport d₀ := by
    apply L.output.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport L.output.cutoff)
    intro x hx
    by_contra hn
    apply hx
    funext ξ
    simp [d₀, image_eq_zero_of_notMem_tsupport hn]
  have hdiag (x ξ : X) : amp x x ξ = d₀ x ξ := by
    exact (Complex.coe_smul _ _).symm
  obtain ⟨C₀, hC₀, hcut⟩ := hamp.exists_frequencyScale_diagonal_error_sobolev_bound
    hcamp d₀ hd₀ hcd₀ hdiag s
  -- The actual common-chart leading symbol is obtained before applying the fixed frame maps.
  let d₁ := zeroExtendedSymbol e.target A.cutoff
    (fun x ξ ↦ (χ (e.symm x) : ℂ) • cotangentSymbol e d₀ x ξ)
  obtain ⟨hd₁, hcd₁⟩ := raw_coordinate_leading_symbol_properties d₀ hd₀ e he hψ
    χ A.cutoff hχ hcχ hχe A.smooth_cutoff A.compact_support (hAV.trans hVe)
  obtain ⟨C₁, hC₁, hcoord⟩ := exists_frequencyScale_raw_coordinatePushforward_sobolev_bound
    d₀ hd₀ e he hψ χ A.cutoff hχ hcχ hχe
    A.smooth_cutoff A.compact_support (hAV.trans hVe) s
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
  let Cout := cutoffMatrix A.cutoff (fun z ↦ (Fout z).toContinuousLinearMap)
  let Cin := cutoffMatrix A.cutoff (fun z ↦ (Finp z).symm.toContinuousLinearMap)
  have hCout : ContDiff ℝ ∞ Cout :=
    contDiff_cutoffMatrix V hV _ hFout A.cutoff A.smooth_cutoff hAV
  have hcCout : HasCompactSupport Cout :=
    hasCompactSupport_cutoffMatrix A.cutoff _ A.compact_support
  have hCin : ContDiff ℝ ∞ Cin :=
    contDiff_cutoffMatrix V hV _ hFinp A.cutoff A.smooth_cutoff hAV
  have hcCin : HasCompactSupport Cin :=
    hasCompactSupport_cutoffMatrix A.cutoff _ A.compact_support
  let d := matrixSymbol Cout Cin d₁
  obtain ⟨hd, hcd⟩ := raw_matrix_leading_symbol_properties d₁ hd₁
    Cout Cin hCout hcCout hCin hcCin
  obtain ⟨C₂, hC₂, hframe⟩ := exists_frequencyScale_raw_matrixMultiplier_sobolev_bound
    d₁ hd₁ Cout Cin hCout hcCout hCin hcCin s
  let MA := matrixMultiplierCLM Cout hCout hcCout
  let MB := matrixMultiplierCLM Cin hCin hcCin
  let Ti := cutoffPullbackCLM (r := r) e.source e.open_source e he χ hχ hcχ hχe
  let To := cutoffPullbackCLM (r := q) e.target e.open_target e.symm hψ A.cutoff
    A.smooth_cutoff A.compact_support (hAV.trans hVe)
  obtain ⟨Ci, hCi, hTi⟩ := exists_norm_cutoffPullback_sobolev_le e he hψ
    χ hχ hcχ hχe s
  obtain ⟨Co, hCo, hTo⟩ := exists_norm_cutoffPullback_sobolev_le e.symm hψ he
    A.cutoff A.smooth_cutoff A.compact_support (hAV.trans hVe) s
  obtain ⟨CmA, hCmA, hMA⟩ := exists_norm_matrixMultiplier_sobolev_le Cout hCout hcCout s
  obtain ⟨CmB, hCmB, hMB⟩ := exists_norm_matrixMultiplier_sobolev_le Cin hCin hcCin s
  have hsupp : tsupport d ⊆ tsupport A.cutoff := by
    apply closure_minimal ?_ (isClosed_tsupport A.cutoff)
    intro z hz
    by_contra hn
    apply hz
    funext ξ
    simp [d, matrixSymbol, Cout, cutoffMatrix, image_eq_zero_of_notMem_tsupport hn]
  -- Identify the transformed covector and both frame maps for this very original native symbol.
  have hglobal (y : X) (hy : y ∈ V) (η : X) :
      frameSymbol Fout Finp (cotangentSymbol e d₀) y η =
        globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame y η := by
    have hfreq : covectorInChart L.chart (c.symm y)
        (covectorFromChart c (c.symm y) η) =
          (fderiv ℝ e (e.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (L.chart (c.symm y))
        (by
          simpa only [L.chart.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hy.1.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hqM (L.chart.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [L.chart.left_inv hsource] at hcomp
      have hecomp : fderiv ℝ e (e.symm y) =
          (mfderiv I I c (c.symm y)).comp
            (mfderiv I I L.chart.symm (L.chart (c.symm y))) := hcomp
      ext j
      change inner ℝ η ((mfderiv I I c (c.symm y))
          ((mfderiv I I L.chart.symm (L.chart (c.symm y)))
            (EuclideanSpace.single j 1))) =
        ((fderiv ℝ e (e.symm y)).adjoint η) j
      have hadj := (fderiv ℝ e (e.symm y)).adjoint_inner_left
        (EuclideanSpace.single j 1) η
      calc
        _ = inner ℝ η ((fderiv ℝ e (e.symm y)) (EuclideanSpace.single j 1)) := by
          rw [hecomp]
          rfl
        _ = inner ℝ ((fderiv ℝ e (e.symm y)).adjoint η)
            (EuclideanSpace.single j 1) := hadj.symm
        _ = _ := by
          simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) j 1
            ((fderiv ℝ e (e.symm y)).adjoint η)
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
      c.right_inv hy.1.1.1, L.globalSymbolInChart_globalSymbolFunction _ _ h_old, hfreq] at hchange
    exact hchange.symm
  have hlead (x : X) (hx : x ∈ V) (ξ : X) :
      d x ξ = globalSymbolInChart E F L.globalSymbolFunction c A.frame B.frame x ξ := by
    rw [← hglobal x hx ξ]
    by_cases hxK : e.symm x ∈ K
    · have hχx : χ (e.symm x) = 1 :=
        interior_subset (s := {z | χ z = 1}) (hχone hxK)
      have hAx : A.cutoff x = 1 :=
        interior_subset (s := {z | A.cutoff z = 1})
          (heKone ⟨e.symm x, hxK, e.right_inv (hVe hx)⟩)
      simp [d, d₁, matrixSymbol, Cout, Cin, cutoffMatrix, zeroExtendedSymbol,
        hVe hx, hχx, hAx, frameSymbol]
    · have hzero : d₀ (e.symm x) = 0 := by
        have hn : e.symm x ∉ tsupport L.output.cutoff := fun h ↦ hxK (Or.inl h)
        funext η
        simp [d₀, image_eq_zero_of_notMem_tsupport hn]
      simp [d, d₁, matrixSymbol, Cout, Cin, cutoffMatrix, zeroExtendedSymbol,
        hVe hx, cotangentSymbol, hzero, frameSymbol]
  -- The fixed input conversion is exact on the complete original native input support.
  have hMBvalue (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      MB u z = A.cutoff z • (Finp z).symm (u z) := by
    rw [matrixMultiplierCLM_apply]
    rfl
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
          (fun w ↦ (L.input.cutoff w : ℂ)) (Ti (MB u)) =
        L.input.localize L.chart_mem_atlas (A.extend hc u) := by
    apply SchwartzMap.ext
    intro w
    have hgrowth : (fun w ↦ (L.input.cutoff w : ℂ)).HasTemperateGrowth :=
      (L.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, cutoffPullbackCLM_apply, hMBvalue]
    by_cases hw : w ∈ tsupport L.input.cutoff
    · have hwK : w ∈ K := Or.inr hw
      have hwe := hKe hwK
      have hb := hbase ⟨w, hwK, rfl⟩
      change L.chart.symm w ∈ c.source ∩ A.frame.baseSet ∩ B.frame.baseSet at hb
      have hχw : χ w = 1 := interior_subset (s := {z | χ z = 1}) (hχone hwK)
      have hwchart : w ∈ L.chart.target := hwe.1
      have hcw : c.symm (e w) = L.chart.symm w := c.left_inv hb.1.1
      change (L.input.cutoff w : ℂ) •
          (χ w • (A.cutoff (e w) • (Finp (e w)).symm (u (e w)))) =
        L.input.localizedFunction (A.extend hc u) w
      rw [hχw, one_smul]
      simp only [BundleChartCutoff.localizedFunction, ite_eq_left hwchart, sectionInChart,
        BundleChartCutoff.extend, BundleChartCutoff.extendedFunction]
      rw [ite_eq_left hb.1.1]
      rw [show Finp (e w) = L.input.frame.coordChangeL ℂ A.frame (L.chart.symm w) from
        congrArg (fun x ↦ L.input.frame.coordChangeL ℂ A.frame x) hcw]
      rw [L.input.frame.symm_coordChangeL A.frame ⟨hb.1.2,
        (L.input.support_subset hw).2⟩]
      rw [A.frame.coordChangeL_apply L.input.frame ⟨hb.1.2,
        (L.input.support_subset hw).2⟩, A.frame.symmL_apply hb.1.2]
      change (L.input.cutoff w : ℂ) •
          (A.cutoff (e w) • (L.input.frame.linearEquivAt ℂ _
            (L.input.support_subset hw).2)
              ((A.frame.linearEquivAt ℂ _ hb.1.2).symm (u (e w)))) =
        (L.input.cutoff w : ℂ) •
          (L.input.frame.linearEquivAt ℂ _ (L.input.support_subset hw).2)
            ((A.cutoff (e w) : ℂ) • (A.frame.linearEquivAt ℂ _ hb.1.2).symm (u (e w)))
      rw [map_smul]
      simp only [Complex.coe_smul]
    · simp [BundleChartCutoff.localize, BundleChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  refine ⟨d, hd, hcd, hsupp, hlead,
    CmA * Co * C₀ * Ci * CmB + CmA * C₁ * CmB + C₂, ?_, ?_⟩
  · exact add_nonneg
      (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCmA hCo) hC₀) hCi) hCmB)
        (mul_nonneg (mul_nonneg hCmA hC₁) hCmB)) hC₂
  intro h hh hh₁ D hD u
  let Lt := (Q.toPiece (frequencyScaleGlobalSymbolSpace a h hh hh₁)).cutoff f g hf hg
  let ah := frequencyScaleAmplitude h amp
  let Aop := amplitudeOperator 0 ah (hamp.frequencyScale h hh hh₁)
    (hasCompactSupport_frequencyScaleAmplitude h hcamp)
  have hAop : Aop = Lt.coordinateOperator := by
    apply ContinuousLinearMap.ext
    intro v
    apply SchwartzMap.ext
    intro x
    rw [amplitudeOperator_apply, PseudodifferentialPiece.coordinateOperator,
      amplitudeOperator_apply]
    congr 1
    change frequencyScaleAmplitude h amp =
      cutoffAmplitude L.output.cutoff L.input.cutoff
        (Q.localSymbol (frequencyScaleGlobalSymbol h a.val))
    rw [Q.localSymbol_frequencyScale]
    rfl
  let d₀h := frequencyScaleSymbol h d₀
  let d₁h := frequencyScaleSymbol h d₁
  let D₀ := quantizeSchwartz 0 d₀h (hd₀.frequencyScale h hh hh₁)
    (hcd₀.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset d₀ h))
  let D₁ := quantizeSchwartz 0 d₁h (hd₁.frequencyScale h hh hh₁)
    (hcd₁.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset d₁ h))
  have hD₀ (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      D₀ v x = quantize d₀h v x := quantizeSchwartz_apply _ _ _ _ v x
  have hD₁ (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (x : X) :
      D₁ v x = quantize d₁h v x := quantizeSchwartz_apply _ _ _ _ v x
  let PA := coordinatePushforward e he hψ χ A.cutoff hχ hcχ hχe
    A.smooth_cutoff A.compact_support (hAV.trans hVe) Aop
  let P₀ := coordinatePushforward e he hψ χ A.cutoff hχ hcχ hχe
    A.smooth_cutoff A.compact_support (hAV.trans hVe) D₀
  have hactual (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      MA (PA (MB v)) = B.localize hc (Lt.toLinearMap (A.extend hc v)) := by
    apply SchwartzMap.ext
    intro z
    rw [matrixMultiplierCLM_apply]
    by_cases hz : z ∈ tsupport A.cutoff
    · have hzV := hAV hz
      have hze := hVe hzV
      have hPA : PA (MB v) z = Lt.coordinateOperator (Ti (MB v)) (e.symm z) := by
        change coordinatePushforward e he hψ χ A.cutoff hχ hcχ hχe
          A.smooth_cutoff A.compact_support (hAV.trans hVe) Aop (MB v) z = _
        rw [hAop]
        exact coordinatePushforward_apply e he hψ χ A.cutoff hχ hcχ hχe
          A.smooth_cutoff A.compact_support (hAV.trans hVe) Lt.coordinateOperator K hKe
          Lt.hasOperatorSupport_coordinateOperator
          (fun w hw ↦ interior_subset (s := {z | A.cutoff z = 1}) (heKone hw))
          (MB v) z hze
      change A.cutoff z • (Fout z) (PA (MB v) z) = _
      rw [hPA, Lt.coordinateOperator_apply]
      change A.cutoff z • (Fout z)
          (L.output.cutoff (e.symm z) •
            Lt.operator (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
              (fun w ↦ (L.input.cutoff w : ℂ)) (Ti (MB v))) (e.symm z)) = _
      rw [hinput]
      change A.cutoff z • (Fout z)
          (L.output.cutoff (L.chart (c.symm z)) •
            Lt.operator (L.input.localize L.chart_mem_atlas (A.extend hc v))
              (L.chart (c.symm z))) = B.localizedFunction (Lt.toLinearMap (A.extend hc v)) z
      change A.cutoff z • (Fout z) _ =
        if z ∈ c.target then (B.cutoff z : ℂ) •
          (B.frame ⟨c.symm z, L.output.extendedFunction
            (Lt.operator (L.input.localize L.chart_mem_atlas (A.extend hc v))) (c.symm z)⟩).2
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
      simp [Cout, cutoffMatrix, BundleChartCutoff.localize,
        BundleChartCutoff.localizedFunction, hAz, hBz]
  have hcutEq : MA (PA (MB u) - P₀ (MB u)) =
      MA (To (Aop (Ti (MB u)) - D₀ (Ti (MB u)))) := by
    simp only [PA, P₀, coordinatePushforward, ContinuousLinearMap.comp_apply]
    rw [← map_sub]
  have hcutBound : ‖schwartzSobolevCoordinate s (MA (PA (MB u) - P₀ (MB u)))‖ ≤
      (CmA * Co * C₀ * Ci * CmB) * h * ‖schwartzSobolevCoordinate s u‖ := by
    rw [hcutEq]
    calc
      _ ≤ CmA * ‖schwartzSobolevCoordinate s
          (To (Aop (Ti (MB u)) - D₀ (Ti (MB u))))‖ := hMA _
      _ ≤ CmA * (Co * ‖schwartzSobolevCoordinate s
          (Aop (Ti (MB u)) - D₀ (Ti (MB u)))‖) :=
        mul_le_mul_of_nonneg_left (hTo _) hCmA
      _ ≤ CmA * (Co * (C₀ * h * ‖schwartzSobolevCoordinate s (Ti (MB u))‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcut h hh hh₁ D₀ hD₀ (Ti (MB u))) hCo) hCmA
      _ ≤ CmA * (Co * (C₀ * h * (Ci * ‖schwartzSobolevCoordinate s (MB u)‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hTi _) (mul_nonneg hC₀ hh.le)) hCo) hCmA
      _ ≤ CmA * (Co * (C₀ * h * (Ci * (CmB * ‖schwartzSobolevCoordinate s u‖)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hMB _) hCi) (mul_nonneg hC₀ hh.le)) hCo) hCmA
      _ = _ := by ring
  have hcoordBound : ‖schwartzSobolevCoordinate s (MA (P₀ (MB u) - D₁ (MB u)))‖ ≤
      (CmA * C₁ * CmB) * h * ‖schwartzSobolevCoordinate s u‖ := by
    calc
      _ ≤ CmA * ‖schwartzSobolevCoordinate s (P₀ (MB u) - D₁ (MB u))‖ := hMA _
      _ ≤ CmA * (C₁ * h * ‖schwartzSobolevCoordinate s (MB u)‖) :=
        mul_le_mul_of_nonneg_left (hcoord h hh hh₁ D₀ D₁ hD₀ hD₁ (MB u)) hCmA
      _ ≤ CmA * (C₁ * h * (CmB * ‖schwartzSobolevCoordinate s u‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hMB _) (mul_nonneg hC₁ hh.le)) hCmA
      _ = _ := by ring
  have hframeBound : ‖schwartzSobolevCoordinate s (MA (D₁ (MB u)) - D u)‖ ≤
      C₂ * h * ‖schwartzSobolevCoordinate s u‖ := hframe h hh hh₁ D₁ D hD₁ hD u
  have hsum : MA (PA (MB u)) - D u =
      (MA (PA (MB u) - P₀ (MB u)) + MA (P₀ (MB u) - D₁ (MB u))) +
        (MA (D₁ (MB u)) - D u) := by
    rw [map_sub, map_sub]
    abel
  rw [← hactual, hsum, schwartzSobolevCoordinate_add, schwartzSobolevCoordinate_add]
  calc
    _ ≤ (‖schwartzSobolevCoordinate s (MA (PA (MB u) - P₀ (MB u)))‖ +
        ‖schwartzSobolevCoordinate s (MA (P₀ (MB u) - D₁ (MB u)))‖) +
        ‖schwartzSobolevCoordinate s (MA (D₁ (MB u)) - D u)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (CmA * Co * C₀ * Ci * CmB) * h * ‖schwartzSobolevCoordinate s u‖ +
        (CmA * C₁ * CmB) * h * ‖schwartzSobolevCoordinate s u‖ +
        C₂ * h * ‖schwartzSobolevCoordinate s u‖ :=
      add_le_add (add_le_add hcutBound hcoordBound) hframeBound
    _ = _ := by ring


section ThreeBundles

variable {k : ℕ} {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin k)) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin k)) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]
  [IsSmoothComplexBundle (n := n) (r := k) G]

omit [∀ x, NormedSpace ℂ (E x)] [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedSpace ℂ (F x)] [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := r) E] [IsSmoothComplexBundle (n := n) (r := q) F]
  [∀ x, NormedSpace ℂ (G x)] [VectorBundle ℂ (EuclideanSpace ℂ (Fin k)) G]
  [IsSmoothComplexBundle (n := n) (r := k) G] in
/-- One fixed pair of native patches admits nested cutoffs in the original left input chart. -/
private theorem exists_native_pair_cutoffs
    (Q : QuantizationPatch (n := n) (r := q) (q := k) F G)
    (P : QuantizationPatch (n := n) (r := r) (q := q) E F) :
    let DP := P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet
    let DQ := Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet
    let K := (P.chart.symm '' tsupport P.output.cutoff) ∩
      (Q.chart.symm '' tsupport Q.input.cutoff)
    ∃ (χ β : M → ℝ) (ρ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ ∧
      HasCompactSupport χ ∧ tsupport χ ⊆ DP ∩ DQ ∧
      K ⊆ interior {x | χ x = 1} ∧
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ β ∧
      HasCompactSupport β ∧ tsupport β ⊆ DP ∩ DQ ∧
      tsupport χ ⊆ interior {x | β x = 1} ∧
      ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ P.chart.target ∩ P.chart.symm ⁻¹' (DP ∩ DQ) ∧
      P.chart '' tsupport β ⊆ interior {z | ρ z = 1} := by
  /- The middle support is the intersection of the original right output and
  left input supports. Keep exactly this support, and choose both manifold
  plateaus and the final coordinate plateau before any symbol or parameter. -/
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace X M
  let KP := P.chart.symm '' tsupport P.output.cutoff
  let KQ := Q.chart.symm '' tsupport Q.input.cutoff
  let K := KP ∩ KQ
  let DP := P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet
  let DQ := Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet
  let D := DP ∩ DQ
  have hKP : IsCompact KP := P.output.compact_support.image_of_continuousOn
    (P.chart.continuousOn_symm.mono (fun z hz ↦ (P.output.support_subset hz).1))
  have hKQ : IsCompact KQ := Q.input.compact_support.image_of_continuousOn
    (Q.chart.continuousOn_symm.mono (fun z hz ↦ (Q.input.support_subset hz).1))
  have hK : IsCompact K := hKP.inter hKQ
  have hD : IsOpen D :=
    ((P.chart.open_source.inter P.input.frame.open_baseSet).inter P.output.frame.open_baseSet).inter
      ((Q.chart.open_source.inter Q.input.frame.open_baseSet).inter Q.output.frame.open_baseSet)
  have hKD : K ⊆ D := by
    rintro x ⟨⟨z, hz, rfl⟩, ⟨w, hw, heq⟩⟩
    refine ⟨⟨⟨P.chart.map_target (P.output.support_subset hz).1,
      P.output_support_in_input_frame hz⟩, (P.output.support_subset hz).2⟩, ?_⟩
    rw [← heq]
    exact ⟨⟨Q.chart.map_target (Q.input.support_subset hw).1,
      (Q.input.support_subset hw).2⟩, Q.input_support_in_output_frame hw⟩
  -- Smooth compact plateaus exist on each of these original compact supports.
  have hcutoff (S U : Set M) (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
      ∃ χ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ U ∧ S ⊆ interior {x | χ x = 1} := by
    obtain ⟨W, hW, hSW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hS hU hSU
    obtain ⟨χ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := I) (n := ⊤) hS.isClosed (hSW.trans hW.subset_interior_closure)
    have hs : tsupport χ ⊆ closure W := by
      apply closure_minimal ?_ hWc.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero x hn)
    refine ⟨χ, χ.contMDiff, hWc.of_isClosed_subset (isClosed_tsupport _) hs,
      hs.trans hWU, ?_⟩
    exact subset_interior_iff_mem_nhdsSet.mpr hone
  obtain ⟨χ, hχ, hcχ, hsχ, honeχ⟩ := hcutoff K D hK hD hKD
  obtain ⟨β, hβ, hcβ, hsβ, honeβ⟩ := hcutoff (tsupport χ) D hcχ hD hsχ
  -- The same right input chart covers the entire fixed intermediate compact set.
  let c := P.chart
  let U := c.target ∩ c.symm ⁻¹' D
  have hU : IsOpen U := c.isOpen_inter_preimage_symm hD
  have hbaseβ : tsupport β ⊆ c.source := fun x hx ↦ (hsβ hx).1.1.1
  have himage : IsCompact (c '' tsupport β) := hcβ.image_of_continuousOn
    (c.continuousOn.mono hbaseβ)
  have himageU : c '' tsupport β ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact ⟨c.map_source (hbaseβ hx), by
      rw [Set.mem_preimage, c.left_inv (hbaseβ hx)]
      exact hsβ hx⟩
  obtain ⟨O, hO, hKO, hOU, hOc⟩ := exists_open_between_and_isCompact_closure himage hU himageU
  obtain ⟨O', hO', hOO', hO'U, hO'c⟩ := exists_open_between_and_isCompact_closure hOc hU hOU
  obtain ⟨ρ, hρ, _, hsρ', honeρ'⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO' hOc.isClosed hOO'
  have htsρ : tsupport ρ = closure O' := congrArg closure hsρ'
  have hcρ : HasCompactSupport ρ := by simpa only [HasCompactSupport, htsρ] using hO'c
  have hsρ : tsupport ρ ⊆ U := by rwa [htsρ]
  have honeρ : c '' tsupport β ⊆ interior {z | ρ z = 1} := by
    apply hKO.trans
    apply interior_maximal ?_ hO
    intro z hz
    exact (honeρ' z).mp (subset_closure hz)
  exact ⟨χ, β, ρ, hχ, hcχ, hsχ, honeχ, hβ, hcβ, hsβ, honeβ, hρ, hcρ, hsρ, honeρ⟩

/-- Nested cutoffs preserve the original native pair up to a uniformly small complete error. -/
private theorem QuantizationPatch.exists_frequencyScale_native_pair_cutoff_sobolev_bound
    (Q : QuantizationPatch (n := n) (r := q) (q := k) F G)
    (P : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    (C : SmoothBundlePresentation (n := n) (r := k) G)
    (χ β : M → ℝ)
    (hχ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ χ)
    (hβ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ β)
    (honeχ : (P.chart.symm '' tsupport P.output.cutoff) ∩
      (Q.chart.symm '' tsupport Q.input.cutoff) ⊆ interior {x | χ x = 1})
    (honeβ : tsupport χ ⊆ interior {x | β x = 1}) (s : ℝ)
    (b : globalSymbolSpace (n := n) (r := q) (q := k) F G 0)
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, ∀ ht : 0 < t, ∀ ht₁ : t ≤ 1,
      let Pt := P.toPiece (frequencyScaleGlobalSymbolSpace a t ht ht₁)
      let Qt := Q.toPiece (frequencyScaleGlobalSymbolSpace b t ht ht₁)
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖C.smoothToSobolev s
          ((Qt.toLinearMap.comp Pt.toLinearMap -
            (Qt.cutoff β χ hβ hχ).toLinearMap.comp
              (Pt.cutoff χ β hχ hβ).toLinearMap) u)‖ ≤ K * t * ‖A.smoothToSobolev s u‖ := by
  /- On the original intermediate support χ² is exactly one. The two terms
  removed by the outer β cutoffs have scalar product zero, so their complete
  native amplitudes have C*t bounds. Compose them with the uniform bounds of
  the retained native pieces and add. All four constants precede t. -/
  classical
  let KP := P.chart.symm '' tsupport P.output.cutoff
  let KQ := Q.chart.symm '' tsupport Q.input.cutoff
  have hχK (x : M) (hx : x ∈ KP ∩ KQ) : χ x = 1 :=
    interior_subset (s := {x | χ x = 1}) (honeχ hx)
  have hβχ (x : M) (hx : x ∈ tsupport χ) : β x = 1 :=
    interior_subset (s := {x | β x = 1}) (honeβ hx)
  have hzleft (x : M) : (1 - β x) * χ x = 0 := by
    by_cases hx : x ∈ tsupport χ
    · rw [hβχ x hx, sub_self, zero_mul]
    · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hzright (x : M) : χ x * (1 - β x) = 0 := by
    rw [mul_comm]
    exact hzleft x
  obtain ⟨Cl, hCl, hl⟩ := Q.exists_frequencyScale_cutoff_sobolev_bound_of_mul_eq_zero
    B C (fun x ↦ 1 - β x) χ (contMDiff_const.sub hβ) hχ hzleft s b
  obtain ⟨Cr, hCr, hr⟩ := P.exists_frequencyScale_cutoff_sobolev_bound_of_mul_eq_zero
    A B χ (fun x ↦ 1 - β x) hχ (contMDiff_const.sub hβ) hzright s a
  obtain ⟨Cx, hCx, hx⟩ := P.exists_frequencyScale_cutoff_sobolev_bound
    A B χ (fun _ ↦ 1) hχ contMDiff_const s a
  obtain ⟨Cq, hCq, hq⟩ := Q.exists_frequencyScale_cutoff_sobolev_bound
    B C β χ hβ hχ s b
  let Yχ := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hχ)
  let Xβ := smoothSectionMul (n := n) (r := r) E (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  let Zβ := smoothSectionMul (n := n) (r := k) G (fun x ↦ (β x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp hβ)
  have hminusE :
      smoothSectionMul E (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Xβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  have hminusG :
      smoothSectionMul G (fun x ↦ ((1 - β x : ℝ) : ℂ))
        (Complex.ofRealCLM.contMDiff.comp (contMDiff_const.sub hβ)) = LinearMap.id - Zβ := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change ((1 - β x : ℝ) : ℂ) • u.val x = u.val x - (β x : ℂ) • u.val x
    rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
  refine ⟨Cl * Cx + Cq * Cr, add_nonneg (mul_nonneg hCl hCx) (mul_nonneg hCq hCr), ?_⟩
  intro t ht ht₁
  let Pt := P.toPiece (frequencyScaleGlobalSymbolSpace a t ht ht₁)
  let Qt := Q.toPiece (frequencyScaleGlobalSymbolSpace b t ht ht₁)
  change ∀ u : smoothSections (n := n) (r := r) E,
    ‖C.smoothToSobolev s
      ((Qt.toLinearMap.comp Pt.toLinearMap -
        (Qt.cutoff β χ hβ hχ).toLinearMap.comp (Pt.cutoff χ β hχ hβ).toLinearMap) u)‖ ≤
      (Cl * Cx + Cq * Cr) * t * ‖A.smoothToSobolev s u‖
  let P₁ := Pt.cutoff χ β hχ hβ
  let Q₁ := Qt.cutoff β χ hβ hχ
  let X₀ := Pt.cutoff χ (fun _ ↦ 1) hχ contMDiff_const
  let L := Qt.cutoff (fun x ↦ 1 - β x) χ (contMDiff_const.sub hβ) hχ
  let R := Pt.cutoff χ (fun x ↦ 1 - β x) hχ (contMDiff_const.sub hβ)
  have hX₀ : X₀.toLinearMap = Yχ.comp Pt.toLinearMap := by
    rw [PseudodifferentialPiece.toLinearMap_cutoff]
    simp only [Complex.ofReal_one, smoothSectionMul_one, LinearMap.comp_id]
    rfl
  -- The original support intersection is unchanged by frequency contraction.
  have hcentral : Qt.toLinearMap.comp (Yχ.comp (Yχ.comp Pt.toLinearMap)) =
      Qt.toLinearMap.comp Pt.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Qt.toLinearMap_eq_of_eq_on_support
    intro x hxQ
    by_cases hxP : x ∈ KP
    · change (χ x : ℂ) • ((χ x : ℂ) • (Pt.toLinearMap u).val x) = _
      rw [hχK x ⟨hxP, hxQ⟩, Complex.ofReal_one, one_smul, one_smul]
    · have hzero := Pt.toLinearMap_eq_zero u x hxP
      change (χ x : ℂ) • ((χ x : ℂ) • (Pt.toLinearMap u).val x) = _
      rw [hzero, smul_zero, smul_zero]
  have hsumEq : L.toLinearMap.comp X₀.toLinearMap + Q₁.toLinearMap.comp R.toLinearMap =
      Qt.toLinearMap.comp Pt.toLinearMap - Q₁.toLinearMap.comp P₁.toLinearMap := by
    rw [hX₀]
    simp only [L, R, P₁, Q₁, PseudodifferentialPiece.toLinearMap_cutoff, hminusE, hminusG]
    change ((LinearMap.id - Zβ).comp (Qt.toLinearMap.comp Yχ)).comp
        (Yχ.comp Pt.toLinearMap) +
      (Zβ.comp (Qt.toLinearMap.comp Yχ)).comp
        (Yχ.comp (Pt.toLinearMap.comp (LinearMap.id - Xβ))) =
      Qt.toLinearMap.comp Pt.toLinearMap -
        (Zβ.comp (Qt.toLinearMap.comp Yχ)).comp (Yχ.comp (Pt.toLinearMap.comp Xβ))
    simp only [LinearMap.sub_comp, LinearMap.comp_sub, LinearMap.id_comp,
      LinearMap.comp_id, LinearMap.comp_assoc]
    rw [hcentral]
    abel
  intro u
  change ‖C.smoothToSobolev s
    ((Qt.toLinearMap.comp Pt.toLinearMap - Q₁.toLinearMap.comp P₁.toLinearMap) u)‖ ≤ _
  rw [← hsumEq, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply, map_add]
  calc
    _ ≤ ‖C.smoothToSobolev s (L.toLinearMap (X₀.toLinearMap u))‖ +
        ‖C.smoothToSobolev s (Q₁.toLinearMap (R.toLinearMap u))‖ := norm_add_le _ _
    _ ≤ Cl * t * ‖B.smoothToSobolev s (X₀.toLinearMap u)‖ +
        Cq * ‖B.smoothToSobolev s (R.toLinearMap u)‖ :=
      add_le_add (hl t ht ht₁ (X₀.toLinearMap u)) (hq t ht ht₁ (R.toLinearMap u))
    _ ≤ Cl * t * (Cx * ‖A.smoothToSobolev s u‖) +
        Cq * (Cr * t * ‖A.smoothToSobolev s u‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hx t ht ht₁ u) (mul_nonneg hCl ht.le))
        (mul_le_mul_of_nonneg_left (hr t ht ht₁ u) hCq)
    _ = (Cl * Cx + Cq * Cr) * t * ‖A.smoothToSobolev s u‖ := by ring


end ThreeBundles

section Endomorphisms

set_option maxHeartbeats 2500000 in
-- Keep the actual native pair and its entire common-chart error before summing patches.
/-- Pointwise inverse symbols give the same original native pair a small identity-pair error. -/
private theorem QuantizationPatch.exists_frequencyScale_inverse_pair_sobolev_bound
    (Q P : QuantizationPatch (n := n) (r := r) (q := r) E E)
    (R : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ)
    (b a : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
    (hba : ∀ x ξ, (b.val x ξ).comp (a.val x ξ) = ContinuousLinearMap.id ℂ (E x)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
      let Qt := Q.toPiece (frequencyScaleGlobalSymbolSpace b h hh hh₁)
      let Pt := P.toPiece (frequencyScaleGlobalSymbolSpace a h hh hh₁)
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖R.smoothToSobolev s
          ((Qt.toLinearMap.comp Pt.toLinearMap -
            (Q.toPiece globalIdentitySymbol).toLinearMap.comp
              (P.toPiece globalIdentitySymbol).toLinearMap) u)‖ ≤
          K * h * ‖R.smoothToSobolev s u‖ := by
  /- First localize the same two native patches with internally chosen nested
  cutoffs; both full discarded tails already have O(h) bounds. In P's original
  chart, the two actual localized operators differ by O(h) from fixed leading
  quantizers. Apply the complete raw product bound, preserving the same middle
  frame. The leading product is frequency independent because b*a=id in the
  original fiber. Fourier inversion and exact chart/frame round trips identify
  it with the original two identity patch actions. All constants precede h. -/
  classical
  let := P.input.frame_mem_atlas
  let := P.output.frame_mem_atlas
  let := Q.input.frame_mem_atlas
  let := Q.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let KP := P.chart.symm '' tsupport P.output.cutoff
  let KQ := Q.chart.symm '' tsupport Q.input.cutoff
  let K := KP ∩ KQ
  let DP := P.chart.source ∩ P.input.frame.baseSet ∩ P.output.frame.baseSet
  let DQ := Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet
  let D := DP ∩ DQ
  obtain ⟨χ, β, ρ, hχ, hcχ, hsχ, honeχ, hβ, hcβ, hsβ, honeβ,
    hρ, hcρ, hsρ, honeρ⟩ := exists_native_pair_cutoffs Q P
  have hχK (x : M) (hx : x ∈ K) : χ x = 1 :=
    interior_subset (s := {x | χ x = 1}) (honeχ hx)
  have hβχ (x : M) (hx : x ∈ tsupport χ) : β x = 1 :=
    interior_subset (s := {x | β x = 1}) (honeβ hx)
  have hχβ : tsupport χ ⊆ tsupport β := by
    intro x hx
    exact subset_tsupport β (by
      change β x ≠ 0
      rw [hβχ x hx]
      exact one_ne_zero)
  let P₁ := (P.toPiece a).cutoff χ β hχ hβ
  let Q₁ := (Q.toPiece b).cutoff β χ hβ hχ
  -- Multiplying a native cutoff cannot introduce support outside that same scalar multiplier.
  have hsupport (d : OpenPartialHomeomorph M X) (v : X → ℝ)
      (hv : tsupport v ⊆ d.target) (f : M → ℝ) (hcf : HasCompactSupport f)
      (hsf : tsupport f ⊆ d.source) :
      d.symm '' tsupport (fun z ↦ v z * f (d.symm z)) ⊆ tsupport f := by
    have hcompact : IsCompact (d '' tsupport f) := hcf.image_of_continuousOn
      (d.continuousOn.mono hsf)
    have hsub : tsupport (fun z ↦ v z * f (d.symm z)) ⊆ d '' tsupport f := by
      apply closure_minimal ?_ hcompact.isClosed
      intro z hz
      have hne : v z ≠ 0 ∧ f (d.symm z) ≠ 0 := mul_ne_zero_iff.mp hz
      exact ⟨d.symm z, subset_tsupport _ hne.2, d.right_inv (hv (subset_tsupport _ hne.1))⟩
    rintro x ⟨z, hz, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hsub hz
    rwa [d.left_inv (hsf hy)]
  have hP₁ : P₁.chart.symm ''
      (tsupport P₁.output.cutoff ∪ tsupport P₁.input.cutoff) ⊆ tsupport β := by
    rw [Set.image_union]
    apply Set.union_subset
    · exact (hsupport P.chart P.output.cutoff (fun z hz ↦ (P.output.support_subset hz).1)
        χ hcχ (fun x hx ↦ (hsχ hx).1.1.1)).trans hχβ
    · exact hsupport P.chart P.input.cutoff (fun z hz ↦ (P.input.support_subset hz).1)
        β hcβ (fun x hx ↦ (hsβ hx).1.1.1)
  have hQ₁ : Q₁.chart.symm ''
      (tsupport Q₁.output.cutoff ∪ tsupport Q₁.input.cutoff) ⊆ tsupport β := by
    rw [Set.image_union]
    apply Set.union_subset
    · exact hsupport Q.chart Q.output.cutoff (fun z hz ↦ (Q.output.support_subset hz).1)
        β hcβ (fun x hx ↦ (hsβ hx).2.1.1)
    · exact (hsupport Q.chart Q.input.cutoff (fun z hz ↦ (Q.input.support_subset hz).1)
        χ hcχ (fun x hx ↦ (hsχ hx).2.1.1)).trans hχβ
  let c := P.chart
  let A : BundleChartCutoff (r := r) E c :=
    { frame := P.input.frame
      frame_mem_atlas := P.input.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.1.2⟩ }
  let B : BundleChartCutoff (r := r) E c :=
    { frame := P.output.frame
      frame_mem_atlas := P.output.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.1.2⟩ }
  let C : BundleChartCutoff (r := r) E c :=
    { frame := Q.output.frame
      frame_mem_atlas := Q.output.frame_mem_atlas
      cutoff := ρ
      smooth_cutoff := hρ
      compact_support := hcρ
      support_subset := fun z hz ↦ ⟨(hsρ hz).1, (hsρ hz).2.2.2⟩ }
  let := A.frame_mem_atlas
  let := B.frame_mem_atlas
  let := C.frame_mem_atlas
  have hbaseP : P.chart.symm ''
      (tsupport P₁.output.cutoff ∪ tsupport P₁.input.cutoff) ⊆
        c.source ∩ A.frame.baseSet ∩ B.frame.baseSet := by
    intro x hx
    exact ⟨⟨(hsβ (hP₁ hx)).1.1.1, (hsβ (hP₁ hx)).1.1.2⟩, (hsβ (hP₁ hx)).1.2⟩
  have hbaseQ : Q.chart.symm ''
      (tsupport Q₁.output.cutoff ∪ tsupport Q₁.input.cutoff) ⊆
        c.source ∩ B.frame.baseSet ∩ C.frame.baseSet := by
    intro x hx
    exact ⟨⟨(hsβ (hQ₁ hx)).1.1.1, (hsβ (hQ₁ hx)).1.2⟩, (hsβ (hQ₁ hx)).2.2⟩
  obtain ⟨p, hp, hcp, hsuppp, hplead, Cp, hCp, hPerror⟩ :=
    P.exists_frequencyScale_localized_leading_symbol χ β hχ hβ c P.chart_mem_atlas A B rfl
      a hbaseP ((Set.image_mono hP₁).trans honeρ) (fun z hz ↦ (hsρ hz).2.1) s
  obtain ⟨qSym, hq, hcq, hsuppq, hqlead, Cq, hCq, hQerror⟩ :=
    Q.exists_frequencyScale_localized_leading_symbol β χ hβ hχ c P.chart_mem_atlas B C rfl
      b hbaseQ ((Set.image_mono hQ₁).trans honeρ) (fun z hz ↦ (hsρ hz).2.2) s
  obtain ⟨Cn, hCn, hn⟩ := Q.exists_frequencyScale_native_pair_cutoff_sobolev_bound
    P R R R χ β hχ hβ honeχ honeβ s b a
  obtain ⟨Co, hCo, hCextend⟩ := C.exists_norm_extend_sobolev_le P.chart_mem_atlas R s
  obtain ⟨Ci, hCi, hAlocalize⟩ := A.exists_norm_localize_sobolev_le P.chart_mem_atlas R s
  obtain ⟨Cm, hCm, hBextend⟩ := B.exists_norm_extend_sobolev_le P.chart_mem_atlas R s
  obtain ⟨Cl, hCl, hClocalize⟩ := C.exists_norm_localize_sobolev_le P.chart_mem_atlas R s
  obtain ⟨Cu, hCu, hQuniform⟩ := Q.exists_frequencyScale_cutoff_sobolev_bound
    R R β χ hβ hχ s b
  obtain ⟨Cd, hCd, hDpUniform⟩ := exists_frequencyScale_raw_sobolev_bound hp hcp s
  obtain ⟨Cr, hCr, hraw⟩ := exists_frequencyScale_raw_composition_sobolev_bound
    qSym p hq hp hcq hcp s
  -- Restore the original native principal product; all auxiliary factors cancel on its support.
  have hcut (L : PseudodifferentialPiece (n := n) (r := r) (q := r) E E 0)
      (f g : M → ℝ)
      (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ f)
      (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ g)
      (x : M) (ξ : CotangentFiber (n := n) x) :
      (L.cutoff f g hf hg).globalSymbolFunction x ξ =
        ((f x * g x : ℝ) : ℂ) • L.globalSymbolFunction x ξ := by
    let := L.input.frame_mem_atlas
    let := L.output.frame_mem_atlas
    -- Keep the same native fields explicit while comparing the two scalar products.
    let d : E x →L[ℂ] E x := (L.output.frame.symmL ℂ x).comp
      ((L.symbol (L.chart x) (covectorInChart L.chart x ξ)).comp
        (L.input.frame.continuousLinearMapAt ℂ x))
    change (if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
        (((L.output.cutoff (L.chart x) * f (L.chart.symm (L.chart x))) *
          (L.input.cutoff (L.chart x) * g (L.chart.symm (L.chart x))) : ℝ) : ℂ) • d
      else 0) =
      ((f x * g x : ℝ) : ℂ) •
        (if x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet then
          ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) • d
        else 0)
    by_cases hx : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    · simp only [ite_eq_left hx, L.chart.left_inv hx.1.1]
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · simp only [ite_eq_right hx, smul_zero]
  have hPcut (x : M) (ξ) : P₁.globalSymbolFunction x ξ =
      ((χ x * β x : ℝ) : ℂ) • (P.toPiece a).globalSymbolFunction x ξ :=
    hcut (P.toPiece a) χ β hχ hβ x ξ
  have hQcut (x : M) (ξ) : Q₁.globalSymbolFunction x ξ =
      ((β x * χ x : ℝ) : ℂ) • (Q.toPiece b).globalSymbolFunction x ξ :=
    hcut (Q.toPiece b) β χ hβ hχ x ξ
  have hprod : globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
      globalSymbolComp (Q.toPiece b).globalSymbolFunction (P.toPiece a).globalSymbolFunction := by
    funext x ξ
    by_cases hx : x ∈ K
    · have hxχ : x ∈ tsupport χ := subset_tsupport χ (by
        change χ x ≠ 0
        rw [hχK x hx]
        exact one_ne_zero)
      simp [globalSymbolComp, hPcut, hQcut, hχK x hx, hβχ x hxχ]
    · by_cases hxP : x ∈ KP
      · have hxQ : x ∉ KQ := fun h ↦ hx ⟨hxP, h⟩
        have hzero := (Q.toPiece b).globalSymbolFunction_eq_zero x
          (fun h ↦ hxQ ((Set.image_mono Set.inter_subset_right) h)) ξ
        simp [globalSymbolComp, hQcut, hzero]
      · have hzero := (P.toPiece a).globalSymbolFunction_eq_zero x
          (fun h ↦ hxP ((Set.image_mono Set.inter_subset_left) h)) ξ
        simp [globalSymbolComp, hPcut, hzero]
  let w : M → ℝ := fun x ↦ Q.weight x * P.weight x
  have hprodId : globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction =
      fun x _ ↦ (w x : ℂ) • ContinuousLinearMap.id ℂ (E x) := by
    rw [hprod, Q.globalSymbolFunction_toPiece b, P.globalSymbolFunction_toPiece a]
    funext x ξ
    simp only [globalSymbolComp, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul, smul_smul, hba, w, Complex.ofReal_mul]
    rw [mul_comm]
  let r₀ := symbolComp qSym p
  have hr₀ : IsSymbol univ 0 r₀ := by
    simpa only [zero_add] using hq.symbolComp isOpen_univ hp
  have hcr₀ : HasCompactSupport r₀ := by
    apply hcq.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport qSym)
    intro x hx
    by_contra hn
    apply hx
    funext ξ
    simp [r₀, symbolComp, image_eq_zero_of_notMem_tsupport hn]
  have hr₀value (z : X) (hz : z ∈ tsupport ρ) (ξ : X) :
      r₀ z ξ = globalSymbolInChart E E
        (fun x _ ↦ (w x : ℂ) • ContinuousLinearMap.id ℂ (E x)) c A.frame C.frame z ξ := by
    have hzP : z ∈ symbolChartDomain E E c A.frame B.frame ∩ c.symm ⁻¹' DP :=
      ⟨⟨⟨(hsρ hz).1, (hsρ hz).2.1.1.2⟩, (hsρ hz).2.1.2⟩, (hsρ hz).2.1⟩
    have hzQ : z ∈ symbolChartDomain E E c B.frame C.frame ∩ c.symm ⁻¹' DQ :=
      ⟨⟨⟨(hsρ hz).1, (hsρ hz).2.1.2⟩, (hsρ hz).2.2.2⟩, (hsρ hz).2.2⟩
    calc
      _ = symbolComp
          (globalSymbolInChart E E Q₁.globalSymbolFunction c B.frame C.frame)
          (globalSymbolInChart E E P₁.globalSymbolFunction c A.frame B.frame) z ξ := by
        change (qSym z ξ).comp (p z ξ) = _
        rw [hqlead z hzQ ξ, hplead z hzP ξ]
        rfl
      _ = globalSymbolInChart E E
          (globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction)
          c A.frame C.frame z ξ :=
        (globalSymbolInChart_globalSymbolComp Q₁.globalSymbolFunction P₁.globalSymbolFunction
          c A.frame B.frame C.frame z ξ (hsρ hz).2.1.2).symm
      _ = _ := by rw [hprodId]
  have hr₀freq : r₀ = fun z _ ↦ r₀ z 0 := by
    funext z ξ
    by_cases hz : z ∈ tsupport ρ
    · rw [hr₀value z hz ξ, hr₀value z hz 0]
      rfl
    · have hqz : qSym z = 0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz (hsuppq h))
      simp [r₀, symbolComp, hqz]
  -- Nonzero product weights are inside the original middle support, without any rank premise.
  have hwK (x : M) (hx : w x ≠ 0) : x ∈ K := by
    have hne : Q.weight x ≠ 0 ∧ P.weight x ≠ 0 := mul_ne_zero_iff.mp hx
    have hxP : x ∈ P.chart.source := by
      by_contra hn
      exact hne.2 (by simp [QuantizationPatch.weight, hn])
    have hxQ : x ∈ Q.chart.source := by
      by_contra hn
      exact hne.1 (by simp [QuantizationPatch.weight, hn])
    have hPi : P.chart x ∈ tsupport P.input.cutoff := subset_tsupport _ (by
      change P.input.cutoff (P.chart x) ≠ 0
      simpa only [QuantizationPatch.weight, ite_eq_left hxP] using hne.2)
    have hPo : P.chart x ∈ tsupport P.output.cutoff := subset_tsupport _ (by
      change P.output.cutoff (P.chart x) ≠ 0
      rw [P.output_eq_one _ hPi]
      exact one_ne_zero)
    have hQi : Q.chart x ∈ tsupport Q.input.cutoff := subset_tsupport _ (by
      change Q.input.cutoff (Q.chart x) ≠ 0
      simpa only [QuantizationPatch.weight, ite_eq_left hxQ] using hne.1)
    exact ⟨⟨P.chart x, hPo, P.chart.left_inv hxP⟩,
      ⟨Q.chart x, hQi, Q.chart.left_inv hxQ⟩⟩
  have hρw (x : M) (hx : w x ≠ 0) : ρ (c x) = 1 := by
    have hxχ : x ∈ tsupport χ := subset_tsupport χ (by
      change χ x ≠ 0
      rw [hχK x (hwK x hx)]
      exact one_ne_zero)
    exact interior_subset (s := {z | ρ z = 1}) (honeρ ⟨x, hχβ hxχ, rfl⟩)
  have hρweight (x : M) : ρ (c x) * ρ (c x) * w x = w x := by
    by_cases hx : w x = 0
    · simp [hx]
    · rw [hρw x hx, one_mul, one_mul]
  have hρβ (x : M) (hx : x ∈ tsupport β) : ρ (c x) = 1 :=
    interior_subset (s := {z | ρ z = 1}) (honeρ ⟨x, hx, rfl⟩)
  have hpieceSupport (T : PseudodifferentialPiece (n := n) (r := r) (q := r) E E 0)
      (hs : T.chart.symm '' (tsupport T.output.cutoff ∪ tsupport T.input.cutoff) ⊆ tsupport β)
      (v : smoothSections (n := n) (r := r) E) :
      ∀ x : M, x ∉ tsupport β → (T.toLinearMap v).val x = 0 := by
    intro x hx
    exact T.toLinearMap_eq_zero v x
      (fun h ↦ hx (hs ((Set.image_mono Set.subset_union_left) h)))
  -- Exact pointwise chart/frame round trips on the original compact intermediate support.
  have hroundAt (Z : BundleChartCutoff (r := r) E c)
      (v : smoothSections (n := n) (r := r) E) (x : M)
      (hxc : x ∈ c.source) (hxf : x ∈ Z.frame.baseSet) (hone : Z.cutoff (c x) = 1) :
      (Z.extend P.chart_mem_atlas (Z.localize P.chart_mem_atlas v)).val x = v.val x := by
    let := Z.frame_mem_atlas
    change Z.extendedFunction (Z.localize P.chart_mem_atlas v) x = _
    simp only [BundleChartCutoff.extendedFunction, ite_eq_left hxc]
    change (Z.cutoff (c x) : ℂ) • Z.frame.symmL ℂ x (Z.localizedFunction v (c x)) = _
    rw [hone, Complex.ofReal_one, one_smul]
    simp only [BundleChartCutoff.localizedFunction, ite_eq_left (c.map_source hxc), sectionInChart]
    rw [c.left_inv hxc, ← Z.frame.continuousLinearMapAt_apply_of_mem ℂ hxf]
    rw [hone, Complex.ofReal_one, one_smul, Z.frame.symmL_continuousLinearMapAt hxf]
  have hroundSupport (Z : BundleChartCutoff (r := r) E c) (hZ : Z.cutoff = ρ)
      (hframe : tsupport β ⊆ Z.frame.baseSet)
      (v : smoothSections (n := n) (r := r) E)
      (hv : ∀ x : M, x ∉ tsupport β → v.val x = 0) :
      Z.extend P.chart_mem_atlas (Z.localize P.chart_mem_atlas v) = v := by
    let := Z.frame_mem_atlas
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ tsupport β
    · exact hroundAt Z v x (hsβ hx).1.1.1 (hframe hx) (by rw [hZ]; exact hρβ x hx)
    · have hz : v.val x = 0 := hv x hx
      change Z.extendedFunction (Z.localize P.chart_mem_atlas v) x = _
      by_cases hxc : x ∈ c.source
      · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hxc]
        change (Z.cutoff (c x) : ℂ) • Z.frame.symmL ℂ x (Z.localizedFunction v (c x)) = _
        simp only [BundleChartCutoff.localizedFunction, ite_eq_left (c.map_source hxc),
          sectionInChart]
        rw [c.left_inv hxc, hz]
        by_cases hxf : x ∈ Z.frame.baseSet
        · rw [show (Z.frame ⟨x, (0 : E x)⟩).2 = 0 from (Z.frame.linear ℂ hxf).map_zero]
          simp
        · rw [Z.frame.symmL_apply_of_notMem (R := ℂ) hxf]
          simp
      · simp [BundleChartCutoff.extendedFunction, hxc, hz]
  refine ⟨Cn + Co * ((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * Ci, ?_, ?_⟩
  · exact add_nonneg hCn (mul_nonneg (mul_nonneg hCo
      (add_nonneg (add_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg hCl hCu) hCm) hCp)
        (mul_nonneg hCq hCd)) hCr)) hCi)
  intro h hh hh₁
  -- Expose the same section quantifier beneath the two original native-piece lets.
  dsimp only
  let Qt := Q.toPiece (frequencyScaleGlobalSymbolSpace b h hh hh₁)
  let Pt := P.toPiece (frequencyScaleGlobalSymbolSpace a h hh hh₁)
  let Qₜ := Qt.cutoff β χ hβ hχ
  let Pₜ := Pt.cutoff χ β hχ hβ
  -- Obtain genuine continuous Schwartz realizations of these same two native actions.
  obtain ⟨_, Tp, _, _, _, _, _, _, _, hTpaction, _⟩ :=
    Pₜ.exists_supported_localized_symbol c P.chart_mem_atlas A B rfl hbaseP
      ((Set.image_mono hP₁).trans honeρ) (fun z hz ↦ (hsρ hz).2.1)
  obtain ⟨_, Tq, _, _, _, _, _, _, _, hTqaction, _⟩ :=
    Qₜ.exists_supported_localized_symbol c P.chart_mem_atlas B C rfl hbaseQ
      ((Set.image_mono hQ₁).trans honeρ) (fun z hz ↦ (hsρ hz).2.2)
  have hTp (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      Tp v = B.localize P.chart_mem_atlas (Pₜ.toLinearMap (A.extend P.chart_mem_atlas v)) :=
    SchwartzMap.ext (hTpaction v)
  have hTq (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      Tq v = C.localize P.chart_mem_atlas (Qₜ.toLinearMap (B.extend P.chart_mem_atlas v)) :=
    SchwartzMap.ext (hTqaction v)
  let ph := frequencyScaleSymbol h p
  let qh := frequencyScaleSymbol h qSym
  let Dp := quantizeSchwartz 0 ph (hp.frequencyScale h hh hh₁)
    (hcp.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset p h))
  let Dq := quantizeSchwartz 0 qh (hq.frequencyScale h hh hh₁)
    (hcq.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset qSym h))
  let rh := frequencyScaleSymbol h r₀
  let Rop := quantizeSchwartz 0 rh (hr₀.frequencyScale h hh hh₁)
    (hcr₀.of_isClosed_subset (isClosed_tsupport _) (tsupport_frequencyScaleSymbol_subset r₀ h))
  have hDp (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) : Dp v z = quantize ph v z :=
    quantizeSchwartz_apply _ _ _ _ v z
  have hDq (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) : Dq v z = quantize qh v z :=
    quantizeSchwartz_apply _ _ _ _ v z
  have hRop (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) :
      Rop v z = quantize (symbolComp qh ph) v z := by
    calc
      _ = quantize rh v z := quantizeSchwartz_apply _ _ _ _ v z
      _ = _ := rfl
  have hRp (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) (z : X) : Rop v z = r₀ z 0 (v z) := by
    have hfreq : rh = fun y _ ↦ r₀ y 0 := by
      funext y ξ
      exact congrFun (congrFun hr₀freq y) (h • ξ)
    calc
      _ = quantize rh v z := quantizeSchwartz_apply _ _ _ _ v z
      _ = _ := by
        rw [hfreq]
        exact quantize_frequency_independent (fun y ↦ r₀ y 0) v z
  have hTqUniform (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      ‖schwartzSobolevCoordinate s (Tq v)‖ ≤ (Cl * Cu * Cm) * ‖schwartzSobolevCoordinate s v‖ := by
    rw [hTq]
    calc
      _ ≤ Cl * ‖R.smoothToSobolev s
          (Qₜ.toLinearMap (B.extend P.chart_mem_atlas v))‖ := hClocalize _
      _ ≤ Cl * (Cu * ‖R.smoothToSobolev s (B.extend P.chart_mem_atlas v)‖) :=
        mul_le_mul_of_nonneg_left (hQuniform h hh hh₁ _) hCl
      _ ≤ Cl * (Cu * (Cm * ‖schwartzSobolevCoordinate s v‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hBextend v) hCu) hCl
      _ = _ := by ring
  have hTpError (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      ‖schwartzSobolevCoordinate s (Tp v - Dp v)‖ ≤
        Cp * h * ‖schwartzSobolevCoordinate s v‖ := by
    rw [hTp]
    exact hPerror h hh hh₁ Dp hDp v
  have hTqError (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      ‖schwartzSobolevCoordinate s (Tq v - Dq v)‖ ≤
        Cq * h * ‖schwartzSobolevCoordinate s v‖ := by
    rw [hTq]
    exact hQerror h hh hh₁ Dq hDq v
  have hlocal (v : 𝓢(X, EuclideanSpace ℂ (Fin r))) :
      ‖schwartzSobolevCoordinate s (Tq (Tp v) - Rop v)‖ ≤
        ((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * h * ‖schwartzSobolevCoordinate s v‖ := by
    have heq : Tq (Tp v) - Rop v =
        (Tq (Tp v - Dp v) + (Tq (Dp v) - Dq (Dp v))) + (Dq (Dp v) - Rop v) := by
      rw [map_sub]
      abel
    rw [heq, schwartzSobolevCoordinate_add, schwartzSobolevCoordinate_add]
    calc
      _ ≤ (‖schwartzSobolevCoordinate s (Tq (Tp v - Dp v))‖ +
          ‖schwartzSobolevCoordinate s (Tq (Dp v) - Dq (Dp v))‖) +
          ‖schwartzSobolevCoordinate s (Dq (Dp v) - Rop v)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ((Cl * Cu * Cm) * ‖schwartzSobolevCoordinate s (Tp v - Dp v)‖ +
          Cq * h * ‖schwartzSobolevCoordinate s (Dp v)‖) +
          Cr * h * ‖schwartzSobolevCoordinate s v‖ :=
        add_le_add (add_le_add (hTqUniform _) (hTqError _))
          (hraw h hh hh₁ Dq Dp Rop hDq hDp hRop v)
      _ ≤ ((Cl * Cu * Cm) * (Cp * h * ‖schwartzSobolevCoordinate s v‖) +
          Cq * h * (Cd * ‖schwartzSobolevCoordinate s v‖)) +
          Cr * h * ‖schwartzSobolevCoordinate s v‖ :=
        add_le_add (add_le_add
          (mul_le_mul_of_nonneg_left (hTpError v) (mul_nonneg (mul_nonneg hCl hCu) hCm))
          (mul_le_mul_of_nonneg_left (hDpUniform h hh hh₁ Dp hDp v)
            (mul_nonneg hCq hh.le))) le_rfl
      _ = _ := by ring
  -- The original input, middle and output round trips recover the actual truncated native pair.
  have hinput (u : smoothSections (n := n) (r := r) E) :
      Pₜ.toLinearMap (A.extend P.chart_mem_atlas (A.localize P.chart_mem_atlas u)) =
        Pₜ.toLinearMap u := by
    apply Pₜ.toLinearMap_eq_of_eq_on_support
    intro x hx
    have hxβ := hP₁ ((Set.image_mono Set.subset_union_right) hx)
    exact hroundAt A u x (hsβ hxβ).1.1.1 (hsβ hxβ).1.1.2 (hρβ x hxβ)
  have hmiddle (u : smoothSections (n := n) (r := r) E) :
      B.extend P.chart_mem_atlas (B.localize P.chart_mem_atlas (Pₜ.toLinearMap u)) =
        Pₜ.toLinearMap u := by
    apply hroundSupport B rfl (fun x hx ↦ (hsβ hx).1.2)
    exact hpieceSupport Pₜ hP₁ u
  have houtput (v : smoothSections (n := n) (r := r) E) :
      C.extend P.chart_mem_atlas (C.localize P.chart_mem_atlas (Qₜ.toLinearMap v)) =
        Qₜ.toLinearMap v := by
    apply hroundSupport C rfl (fun x hx ↦ (hsβ hx).2.2)
    exact hpieceSupport Qₜ hQ₁ v
  have hactual (u : smoothSections (n := n) (r := r) E) :
      C.extend P.chart_mem_atlas (Tq (Tp (A.localize P.chart_mem_atlas u))) =
        Qₜ.toLinearMap (Pₜ.toLinearMap u) := by
    rw [hTp, hTq, hmiddle, hinput, houtput]
  have hleading (u : smoothSections (n := n) (r := r) E) :
      C.extend P.chart_mem_atlas (Rop (A.localize P.chart_mem_atlas u)) =
        (Q.toPiece globalIdentitySymbol).toLinearMap
          ((P.toPiece globalIdentitySymbol).toLinearMap u) := by
    apply Subtype.ext
    funext x
    have hI : ((Q.toPiece globalIdentitySymbol).toLinearMap
        ((P.toPiece globalIdentitySymbol).toLinearMap u)).val x = (w x : ℂ) • u.val x := by
      rw [Q.toLinearMap_id_apply, P.toLinearMap_id_apply, smul_smul, ← Complex.ofReal_mul]
    rw [hI]
    change C.extendedFunction (Rop (A.localize P.chart_mem_atlas u)) x = _
    by_cases hx : x ∈ c.source
    · simp only [BundleChartCutoff.extendedFunction, ite_eq_left hx, hRp]
      by_cases hz : c x ∈ tsupport ρ
      · have hxf : x ∈ A.frame.baseSet := by
          simpa only [Set.mem_preimage, c.left_inv hx] using (A.support_subset hz).2
        have hxg : x ∈ C.frame.baseSet := by
          simpa only [Set.mem_preimage, c.left_inv hx] using (C.support_subset hz).2
        rw [hr₀value (c x) hz 0]
        change (ρ (c x) : ℂ) • C.frame.symmL ℂ x
          (globalSymbolInChart E E
            (fun y _ ↦ (w y : ℂ) • ContinuousLinearMap.id ℂ (E y)) c A.frame C.frame
            (c x) 0 (A.localizedFunction u (c x))) = _
        simp only [BundleChartCutoff.localizedFunction, ite_eq_left (c.map_source hx),
          sectionInChart, globalSymbolInChart, ContinuousLinearMap.comp_apply,
          smul_apply, ContinuousLinearMap.id_apply, c.left_inv hx, map_smul]
        rw [c.left_inv hx]
        rw [← A.frame.continuousLinearMapAt_apply_of_mem ℂ hxf,
          A.frame.symmL_continuousLinearMapAt hxf,
          C.frame.symmL_continuousLinearMapAt hxg]
        change (ρ (c x) : ℂ) • (ρ (c x) : ℂ) • (w x : ℂ) • u.val x = _
        calc
          _ = ((ρ (c x) * ρ (c x) * w x : ℝ) : ℂ) • u.val x := by
            simp only [smul_smul, Complex.ofReal_mul]
            congr 1
            ring
          _ = _ := by rw [hρweight]
      · have hzero : ρ (c x) = 0 := image_eq_zero_of_notMem_tsupport hz
        have hw : w x = 0 := by
          by_contra hn
          rw [hρw x hn] at hzero
          exact one_ne_zero hzero
        simp [C, hzero, hw]
    · have hw : w x = 0 := by
        by_contra hn
        exact hx (hsχ (subset_tsupport χ (by
          change χ x ≠ 0
          rw [hχK x (hwK x hn)]
          exact one_ne_zero))).1.1.1
      simp [BundleChartCutoff.extendedFunction, hx, hw]
  intro u
  have hinner : ‖R.smoothToSobolev s
      (Qₜ.toLinearMap (Pₜ.toLinearMap u) -
        (Q.toPiece globalIdentitySymbol).toLinearMap
          ((P.toPiece globalIdentitySymbol).toLinearMap u))‖ ≤
      Co * ((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * Ci * h * ‖R.smoothToSobolev s u‖ := by
    rw [← hactual, ← hleading]
    have hext : C.extend P.chart_mem_atlas
        (Tq (Tp (A.localize P.chart_mem_atlas u)) - Rop (A.localize P.chart_mem_atlas u)) =
      C.extend P.chart_mem_atlas (Tq (Tp (A.localize P.chart_mem_atlas u))) -
        C.extend P.chart_mem_atlas (Rop (A.localize P.chart_mem_atlas u)) :=
      (C.extendLinearMap P.chart_mem_atlas).map_sub _ _
    rw [← hext]
    calc
      _ ≤ Co * ‖schwartzSobolevCoordinate s
          (Tq (Tp (A.localize P.chart_mem_atlas u)) - Rop (A.localize P.chart_mem_atlas u))‖ :=
        hCextend _
      _ ≤ Co * (((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * h *
          ‖schwartzSobolevCoordinate s (A.localize P.chart_mem_atlas u)‖) :=
        mul_le_mul_of_nonneg_left (hlocal _) hCo
      _ ≤ Co * (((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * h *
          (Ci * ‖R.smoothToSobolev s u‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hAlocalize u)
          (mul_nonneg (add_nonneg (add_nonneg
            (mul_nonneg (mul_nonneg (mul_nonneg hCl hCu) hCm) hCp)
            (mul_nonneg hCq hCd)) hCr) hh.le)) hCo
      _ = _ := by ring
  have heq : (Qt.toLinearMap.comp Pt.toLinearMap -
      (Q.toPiece globalIdentitySymbol).toLinearMap.comp
        (P.toPiece globalIdentitySymbol).toLinearMap) u =
    (Qt.toLinearMap.comp Pt.toLinearMap - Qₜ.toLinearMap.comp Pₜ.toLinearMap) u +
      (Qₜ.toLinearMap (Pₜ.toLinearMap u) - (Q.toPiece globalIdentitySymbol).toLinearMap
        ((P.toPiece globalIdentitySymbol).toLinearMap u)) := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply]
    abel
  rw [heq, map_add]
  calc
    _ ≤ ‖R.smoothToSobolev s
        ((Qt.toLinearMap.comp Pt.toLinearMap - Qₜ.toLinearMap.comp Pₜ.toLinearMap) u)‖ +
      ‖R.smoothToSobolev s
        (Qₜ.toLinearMap (Pₜ.toLinearMap u) - (Q.toPiece globalIdentitySymbol).toLinearMap
          ((P.toPiece globalIdentitySymbol).toLinearMap u))‖ := norm_add_le _ _
    _ ≤ Cn * h * ‖R.smoothToSobolev s u‖ +
        Co * ((Cl * Cu * Cm) * Cp + Cq * Cd + Cr) * Ci * h * ‖R.smoothToSobolev s u‖ :=
      add_le_add (hn h hh hh₁ u) hinner
    _ = _ := by ring

end Endomorphisms


section EndomorphismAssemblies

set_option maxHeartbeats 5000000 in
-- Allow the finite double-sum conversion of the same native patch-pair estimates.
/-- Summing the original native inverse pairs gives a bound for the same finite quantization. -/
private theorem QuantizationPresentation.exists_frequencyScale_inverse_comp_sobolev_bound
    (C : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ)
    (b a : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
    (hba : ∀ x ξ, (b.val x ξ).comp (a.val x ξ) = ContinuousLinearMap.id ℂ (E x)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖A.smoothToSobolev s
          ((C.toLinearMap (frequencyScaleGlobalSymbolSpace b h hh hh₁)).comp
            (C.toLinearMap (frequencyScaleGlobalSymbolSpace a h hh hh₁)) u - u)‖ ≤
          K * h * ‖A.smoothToSobolev s u‖ := by
  /- Choose one constant for every ordered original patch pair before h. Keep
  that scalar family as a witness, then use the finite norm sum with an explicit
  linear norm map. The two original identity actions still sum to Id*Id. -/
  classical
  let V := smoothSections (n := n) (r := r) E
  let W := A.SobolevSpace s
  -- Sum arbitrary error maps on the same section space and original finite patch family.
  have hfinite (N : V →ₗ[ℂ] W) (D : Fin C.size → Fin C.size → V →ₗ[ℂ] V)
      (k : Fin C.size → Fin C.size → ℝ)
      (hD : ∀ i j v, ‖N (D i j v)‖ ≤ k i j * ‖N v‖) (v : V) :
      ‖N ((∑ i, ∑ j, D i j) v)‖ ≤ (∑ i, ∑ j, k i j) * ‖N v‖ := by
    simp only [LinearMap.sum_apply, map_sum]
    calc
      _ ≤ ∑ i, ‖∑ j, N (D i j v)‖ := norm_sum_le _ _
      _ ≤ ∑ i, ∑ j, ‖N (D i j v)‖ :=
        Finset.sum_le_sum (fun i _ ↦ norm_sum_le _ _)
      _ ≤ ∑ i, ∑ j, k i j * ‖N v‖ :=
        Finset.sum_le_sum (fun i _ ↦ Finset.sum_le_sum (fun j _ ↦ hD i j v))
      _ = _ := by simp only [Finset.sum_mul]
  let N : V →ₗ[ℂ] W := A.smoothToSobolev s
  let D (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) (i j : Fin C.size) : V →ₗ[ℂ] V :=
    ((C.patch i).toPiece (frequencyScaleGlobalSymbolSpace b h hh hh₁)).toLinearMap.comp
        ((C.patch j).toPiece (frequencyScaleGlobalSymbolSpace a h hh hh₁)).toLinearMap -
      ((C.patch i).toPiece globalIdentitySymbol).toLinearMap.comp
        ((C.patch j).toPiece globalIdentitySymbol).toLinearMap
  -- A single choice on ordered pairs leaves the actual scalar family as an opaque witness.
  have hpairs (ij : Fin C.size × Fin C.size) :
      ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1, ∀ v : V,
        ‖N (D h hh hh₁ ij.1 ij.2 v)‖ ≤ L * h * ‖N v‖ :=
    (C.patch ij.1).exists_frequencyScale_inverse_pair_sobolev_bound
      (C.patch ij.2) A s b a hba
  obtain ⟨K, hpair⟩ := Classical.axiomOfChoice hpairs
  have hK (i j : Fin C.size) : 0 ≤ K (i, j) := (hpair (i, j)).1
  have hbound (h : ℝ) (hh : 0 < h) (hh₁ : h ≤ 1) (i j : Fin C.size) (v : V) :
      ‖N (D h hh hh₁ i j v)‖ ≤ K (i, j) * h * ‖N v‖ := (hpair (i, j)).2 h hh hh₁ v
  have hsum (b a : globalSymbolSpace (n := n) (r := r) (q := r) E E 0) :
      (C.toLinearMap b).comp (C.toLinearMap a) =
        ∑ i, ∑ j, ((C.patch i).toPiece b).toLinearMap.comp
          ((C.patch j).toPiece a).toLinearMap := by
    apply LinearMap.ext
    intro u
    simp only [QuantizationPresentation.toLinearMap, LinearMap.comp_apply,
      LinearMap.sum_apply, map_sum]
    exact Finset.sum_comm
  have hidentity :
      (∑ i, ∑ j, ((C.patch i).toPiece globalIdentitySymbol).toLinearMap.comp
        ((C.patch j).toPiece globalIdentitySymbol).toLinearMap) = LinearMap.id := by
    rw [← hsum globalIdentitySymbol globalIdentitySymbol]
    simp only [C.toLinearMap_id, LinearMap.id_comp]
  refine ⟨∑ i, ∑ j, K (i, j), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hK i j))
  intro h hh hh₁ u
  let bh := frequencyScaleGlobalSymbolSpace b h hh hh₁
  let ah := frequencyScaleGlobalSymbolSpace a h hh hh₁
  have hsumError : (C.toLinearMap bh).comp (C.toLinearMap ah) - LinearMap.id =
      ∑ i, ∑ j, D h hh hh₁ i j := by
    rw [hsum, ← hidentity]
    simp only [D, bh, ah, Finset.sum_sub_distrib]
  -- Rewrite the actual section evaluation before applying the same Sobolev map.
  have herrorEval : (C.toLinearMap bh).comp (C.toLinearMap ah) u - u =
      ((C.toLinearMap bh).comp (C.toLinearMap ah) -
        (LinearMap.id : V →ₗ[ℂ] V)) u := by
    simp only [LinearMap.sub_apply, LinearMap.id_apply]
  rw [herrorEval, hsumError]
  have hfinal : ‖N ((∑ i, ∑ j, D h hh hh₁ i j) u)‖ ≤
      (∑ i, ∑ j, K (i, j) * h) * ‖N u‖ :=
    hfinite N (D h hh hh₁) (fun i j ↦ K (i, j) * h)
      (fun i j v ↦ hbound h hh hh₁ i j v) u
  dsimp only [N] at hfinal
  calc
    _ ≤ (∑ i, ∑ j, K (i, j) * h) * ‖A.smoothToSobolev s u‖ := hfinal
    _ = _ := by simp only [Finset.sum_mul]

/-- Both original Sobolev errors for pointwise inverse order-zero symbols have one small bound. -/
theorem QuantizationPresentation.exists_frequencyScale_inverse_error_sobolev_bound
    (C : QuantizationPresentation (n := n) (r := r) (q := r) E E)
    (A : SmoothBundlePresentation (n := n) (r := r) E) (s : ℝ)
    (a b : globalSymbolSpace (n := n) (r := r) (q := r) E E 0)
    (hab : ∀ x ξ, (a.val x ξ).comp (b.val x ξ) = ContinuousLinearMap.id ℂ (E x))
    (hba : ∀ x ξ, (b.val x ξ).comp (a.val x ξ) = ContinuousLinearMap.id ℂ (E x)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : ℝ, ∀ hh : 0 < h, ∀ hh₁ : h ≤ 1,
      ∀ u : smoothSections (n := n) (r := r) E,
        ‖A.smoothToSobolev s
          ((C.toLinearMap (frequencyScaleGlobalSymbolSpace b h hh hh₁)).comp
            (C.toLinearMap (frequencyScaleGlobalSymbolSpace a h hh hh₁)) u - u)‖ ≤
          K * h * ‖A.smoothToSobolev s u‖ ∧
        ‖A.smoothToSobolev s
          ((C.toLinearMap (frequencyScaleGlobalSymbolSpace a h hh hh₁)).comp
            (C.toLinearMap (frequencyScaleGlobalSymbolSpace b h hh hh₁)) u - u)‖ ≤
          K * h * ‖A.smoothToSobolev s u‖ := by
  /- Apply the same complete finite-presentation result in both orders. Use the
  sum of the two preselected nonnegative constants, keeping one common scale,
  one original quantizer, one original Sobolev presentation and the same u. -/
  obtain ⟨Cl, hCl, hl⟩ := C.exists_frequencyScale_inverse_comp_sobolev_bound A s b a hba
  obtain ⟨Cr, hCr, hr⟩ := C.exists_frequencyScale_inverse_comp_sobolev_bound A s a b hab
  refine ⟨Cl + Cr, add_nonneg hCl hCr, ?_⟩
  intro h hh hh₁ u
  constructor
  · calc
      _ ≤ Cl * h * ‖A.smoothToSobolev s u‖ := hl h hh hh₁ u
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCr) hh.le) (norm_nonneg _)
  · calc
      _ ≤ Cr * h * ‖A.smoothToSobolev s u‖ := hr h hh hh₁ u
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCl) hh.le) (norm_nonneg _)

end EndomorphismAssemblies


end AtiyahSinger
