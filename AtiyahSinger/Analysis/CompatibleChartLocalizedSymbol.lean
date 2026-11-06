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
# Full localized symbols from compatible charts

Public module ID: M0370.

The same complete section map, originally written in a compatible chart,
has a full symbol in a supplied original atlas chart and supplied original
frames. Its principal expression is the intrinsic two-cutoff fiber map.
Both exact action and every lower-order coordinate/frame correction are
retained. This is the local comparison needed to identify the intrinsic
principal class of the positive associated product regularization.

The proof extends the existing raw-chart symbol-localization argument, using
specified actual localization and extension maps instead of changing the atlas.
Source: SG III.3.12--3.19.
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

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]

open scoped Classical in
/-- Full local action and its intrinsic leading symbol survive a compatible source chart. -/
theorem exists_localized_symbol_of_mem_maximalAtlas {m : ℝ}
    (C : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hC : C ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A C) (Dout : AtlasChartCutoff B C)
    (hio : tsupport Din.cutoff ⊆ C.symm ⁻¹' (B.chart Dout.frameIndex).baseSet)
    (hoi : tsupport Dout.cutoff ⊆ C.symm ⁻¹' (A.chart Din.frameIndex).baseSet)
    (T : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
      →L[ℂ] 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))))
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : IsSymbol univ m a) (hT : ∀ u x, T u x = quantize a u x)
    (I : A.smoothSections →ₗ[ℂ]
      𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))))
    (O : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
      →ₗ[ℂ] B.smoothSections)
    (hI : ∀ u z, I u z = Din.localizedFunction u z)
    (hO : ∀ v x, (O v).val x = Dout.extendedFunction v x)
    (g : AtlasSymbolFunction (n := n) E F)
    (hg : ∀ x ξ, g x ξ =
      if h : x ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
          (B.chart Dout.frameIndex).baseSet then
        ((Dout.cutoff (C x) * Din.cutoff (C x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv Dout.frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ).toLinearMap).comp
            ((a (C x) (covectorInChart C x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv Din.frameIndex x h.1.2).toLinearMap))
      else 0)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (D₀ : AtlasChartCutoff A c) (K₀ : AtlasChartCutoff B c)
    (hAB : D₀.cutoff = K₀.cutoff)
    (hbase : C.symm '' (tsupport Dout.cutoff ∪ tsupport Din.cutoff) ⊆
      c.source ∩ (A.chart D₀.frameIndex).baseSet ∩ (B.chart K₀.frameIndex).baseSet)
    (hone : c '' (C.symm '' (tsupport Dout.cutoff ∪ tsupport Din.cutoff)) ⊆
      interior {z | D₀.cutoff z = 1})
    (hoverlap : tsupport D₀.cutoff ⊆ c.symm ⁻¹'
      (C.source ∩ (A.chart Din.frameIndex).baseSet ∩
        (B.chart Dout.frameIndex).baseSet)) :
    ∃ p : SymbolFunction n (A.rank D₀.frameIndex) (B.rank K₀.frameIndex), IsSymbol Set.univ m p ∧
      (∀ (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) z,
        quantize p u z = K₀.localize hc ((O.comp (T.toLinearMap.comp I)) (D₀.extend hc u)) z) ∧
      IsSymbol (atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∩ c.symm ⁻¹'
        (C.source ∩ (A.chart Din.frameIndex).baseSet ∩
          (B.chart Dout.frameIndex).baseSet)) (m - 1)
        (p - atlasGlobalSymbolInChart A B g c
          D₀.frameIndex K₀.frameIndex) := by
  classical
  let S := O.comp (T.toLinearMap.comp I)
  let X := EuclideanSpace ℝ (Fin n)
  let IM := 𝓘(ℝ, X)
  let D := C.source ∩ (A.chart Din.frameIndex).baseSet ∩
    (B.chart Dout.frameIndex).baseSet
  let V := atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex ∩ c.symm ⁻¹' D
  have hV : IsOpen V :=
    (c.continuousOn_symm.mono (fun z hz ↦ hz.1.1)).isOpen_inter_preimage
      (isOpen_atlasSymbolChartDomain A B c D₀.frameIndex K₀.frameIndex)
      ((C.open_source.inter (A.chart Din.frameIndex).open_baseSet).inter
        (B.chart Dout.frameIndex).open_baseSet)
  have hAV : tsupport D₀.cutoff ⊆ V := by
    intro z hz
    exact ⟨⟨D₀.support_subset hz, (K₀.support_subset (by rwa [← hAB])).2⟩, hoverlap hz⟩
  let K := tsupport Dout.cutoff ∪ tsupport Din.cutoff
  have hK : IsCompact K := Dout.compact_support.union Din.compact_support
  have hKD : C.symm '' K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    rcases hz with hz | hz
    · exact ⟨⟨C.map_target (Dout.support_subset hz).1,
        hoi hz⟩, (Dout.support_subset hz).2⟩
    · exact ⟨⟨C.map_target (Din.support_subset hz).1,
        (Din.support_subset hz).2⟩, hio hz⟩
  let t : OpenPartialHomeomorph X X := C.symm.trans c
  have hcM := subset_maximalAtlas (I := IM) (n := ∞) hc
  have hdM := hC
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
      · exact (Dout.support_subset hz).1
      · exact (Din.support_subset hz).1, hb.1.1⟩
  have hVt : V ⊆ t.target := fun z hz ↦ ⟨hz.1.1.1, hz.2.1.1⟩
  have htarget : IsCompact (t '' K) := hK.image_of_continuousOn (t.continuousOn.mono hKt)
  have htargetOne : t '' K ⊆ interior {z | D₀.cutoff z = 1} := by
    rintro _ ⟨z, hz, rfl⟩
    exact hone ⟨C.symm z, ⟨z, hz, rfl⟩, rfl⟩
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
  let p₀ := cutoffSymbol Dout.cutoff Din.cutoff a
  have hp₀ : IsSymbol univ m p₀ := isSymbol_cutoffSymbol m a ha _ _
    Dout.smooth_cutoff Din.smooth_cutoff Dout.compact_support Din.compact_support
  let P₀ := amplitudeOperator m (cutoffAmplitude Dout.cutoff Din.cutoff a)
    (isAmplitude_cutoffAmplitude m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff)
    (hasCompactSupport_cutoffAmplitude a _ _
      Dout.compact_support Din.compact_support)
  have hP₀ : ∀ u z, P₀ u z = quantize p₀ u z := by
    intro u z
    rw [amplitudeOperator_apply]
    exact (congrFun (quantize_amplitudeSymbol m _
      (isAmplitude_cutoffAmplitude m a ha _ _
        Dout.smooth_cutoff Din.smooth_cutoff)
      (hasCompactSupport_cutoffAmplitude a _ _
        Dout.compact_support Din.compact_support) u) z).symm
  have hP₀support : HasOperatorSupport K P₀ :=
    hasOperatorSupport_cutoff m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff
      Dout.compact_support Din.compact_support
  have hP₀apply (u) (z) : P₀ u z = Dout.cutoff z • T
      (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
        (fun w ↦ (Din.cutoff w : ℂ)) u) z := by
    rw [amplitudeOperator_apply, amplitudeApply_cutoffAmplitude m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff
      Dout.compact_support Din.compact_support, hT]
  let P := coordinatePushforward t ht hts χ D₀.cutoff hχ hcχ hχt
    D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt) P₀
  obtain ⟨s, hs, hPs, hrem⟩ := exists_symbol_coordinatePushforward t ht hts χ D₀.cutoff
    hχ hcχ hχt D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt) m p₀ hp₀
    P₀ hP₀ K hK hKt hP₀support
    hχone htargetOne
  have hPK : HasOperatorSupport (t '' K) P := hasOperatorSupport_coordinatePushforward
    t ht hts χ D₀.cutoff hχ hcχ hχt D₀.smooth_cutoff D₀.compact_support (hAV.trans hVt)
    P₀ K hK hKt hP₀support
  let Fout := fun z ↦ B.coordChangeL Dout.frameIndex K₀.frameIndex (c.symm z)
  let Finp := fun z ↦ A.coordChangeL D₀.frameIndex Din.frameIndex (c.symm z)
  have hcV : ContMDiffOn IM IM ∞ c.symm V := by
    intro z hz
    exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1.1.1).contMDiffWithinAt
  have hFout : ContDiffOn ℝ ∞ Fout V :=
    B.contDiffOn_coordChangeL_comp Dout.frameIndex K₀.frameIndex V c.symm hcV
      (fun z hz ↦ ⟨hz.2.2, hz.1.2⟩)
  have hFinp : ContDiffOn ℝ ∞ Finp V :=
    A.contDiffOn_coordChangeL_comp D₀.frameIndex Din.frameIndex V c.symm hcV
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
      (v : EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))) :
      Fout z v = (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
        ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hz.1.2)
          ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hz.2.2).symm
            ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ) v))) := by
    have h := (B.coordChangeL_apply Dout.frameIndex K₀.frameIndex (c.symm z)
      ⟨hz.2.2, hz.1.2⟩
      ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hz.2.2).symm
        ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ) v))).symm
    change Fout z ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ).symm
      ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hz.2.2)
        ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hz.2.2).symm
          ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ) v)))) =
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hz.1.2)
            ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hz.2.2).symm
              ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ) v))) at h
    simpa only [LinearEquiv.apply_symm_apply, ContinuousLinearEquiv.symm_apply_apply] using h
  have hinput (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
          (fun w ↦ (Din.cutoff w : ℂ))
          (cutoffPullbackCLM t.source t.open_source t ht χ hχ hcχ hχt (Tin u)) =
        I (D₀.extend hc u) := by
    apply SchwartzMap.ext
    intro w
    have hgrowth : (fun w ↦ (Din.cutoff w : ℂ)).HasTemperateGrowth :=
      (Din.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp Din.smooth_cutoff)
    rw [SchwartzMap.smulLeftCLM_apply_apply hgrowth, cutoffPullbackCLM_apply, hTin]
    rw [hI]
    by_cases hw : w ∈ tsupport Din.cutoff
    · have hwK : w ∈ K := Or.inr hw
      have hwt := hKt hwK
      have hbasew := hbase ⟨w, hwK, rfl⟩
      have hχw : χ w = 1 := interior_subset (s := {z : X | χ z = 1}) (hχone hwK)
      have hcw : c.symm (t w) = C.symm w := c.left_inv hbasew.1.1
      have hframe : Finp (t w) (u (t w)) =
          (EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm
            ((A.frameLinearEquiv Din.frameIndex (C.symm w)
              (Din.support_subset hw).2)
              ((A.frameLinearEquiv D₀.frameIndex (C.symm w) hbasew.1.2).symm
                ((EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ) (u (t w))))) := by
        rw [show Finp (t w) = A.coordChangeL D₀.frameIndex Din.frameIndex
          (C.symm w) from
            congrArg (A.coordChangeL D₀.frameIndex Din.frameIndex) hcw]
        let ei := EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ
        let ec := EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ
        have h := (A.coordChangeL_apply D₀.frameIndex Din.frameIndex (C.symm w)
          ⟨hbasew.1.2, (Din.support_subset hw).2⟩
          ((A.frameLinearEquiv D₀.frameIndex (C.symm w) hbasew.1.2).symm
            (ec (u (t w))))).symm
        change A.coordChangeL D₀.frameIndex Din.frameIndex (C.symm w)
          (ec.symm ((A.frameLinearEquiv D₀.frameIndex (C.symm w) hbasew.1.2)
            ((A.frameLinearEquiv D₀.frameIndex (C.symm w) hbasew.1.2).symm
              (ec (u (t w)))))) =
          ei.symm ((A.frameLinearEquiv Din.frameIndex (C.symm w)
            (Din.support_subset hw).2)
            ((A.frameLinearEquiv D₀.frameIndex (C.symm w) hbasew.1.2).symm
              (ec (u (t w))))) at h
        simpa only [LinearEquiv.apply_symm_apply, ec.symm_apply_apply] using h
      rw [hχw, one_smul, hframe]
      change _ = Din.localizedFunction (D₀.extend hc u) w
      have hwchart : w ∈ C.target := hwt.1
      simp only [AtlasChartCutoff.localizedFunction, ite_eq_left hwchart, atlasSectionInChart,
        AtlasChartCutoff.extend, AtlasChartCutoff.extendedFunction, dite_eq_left hbasew.1]
      change _ = (Din.cutoff w : ℂ) •
        (EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm
          ((A.frameLinearEquiv Din.frameIndex (C.symm w)
            (Din.support_subset hw).2)
            ((D₀.cutoff (t w) : ℂ) • _))
      rw [map_smul, map_smul]
      simp only [Complex.coe_smul]
      rfl
    · simp [AtlasChartCutoff.localizedFunction,
        image_eq_zero_of_notMem_tsupport hw]
  have happly : ∀ (u : 𝓢(X, EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex)))) z,
      quantize p u z = K₀.localize hc (S (D₀.extend hc u)) z := by
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
      change D₀.cutoff z • Fout z _ = K₀.localizedFunction (S (D₀.extend hc u)) z
      simp only [AtlasChartCutoff.localizedFunction, atlasSectionInChart, S,
        LinearMap.comp_apply, ContinuousLinearMap.coe_coe, hO]
      rw [hFout_apply z hzV]
      change _ = if z ∈ c.target then (K₀.cutoff z : ℂ) •
        (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
          ((B.chart K₀.frameIndex) ⟨c.symm z, Dout.extendedFunction
            (T (I (D₀.extend hc u))) (c.symm z)⟩).2
        else 0
      have hzc : z ∈ c.target := hzV.1.1.1
      have hzd : c.symm z ∈ C.source ∩ (B.chart Dout.frameIndex).baseSet :=
        ⟨hzV.2.1.1, hzV.2.2⟩
      rw [ite_eq_left hzc, AtlasChartCutoff.extendedFunction, dite_eq_left hzd, ← hAB]
      change D₀.cutoff z •
          (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
            ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hzV.1.2)
              ((B.frameLinearEquiv Dout.frameIndex (c.symm z) hzV.2.2).symm
                ((EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ)
                  (Dout.cutoff (C (c.symm z)) • _)))) =
        (D₀.cutoff z : ℂ) •
          (EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ).symm
            ((B.frameLinearEquiv K₀.frameIndex (c.symm z) hzV.1.2)
              ((Dout.cutoff (C (c.symm z)) : ℂ) • _))
      simp only [← Complex.coe_smul, map_smul]
      rfl
    · have hDz : D₀.cutoff z = 0 := image_eq_zero_of_notMem_tsupport hz
      have hKz : K₀.cutoff z = 0 := by rwa [← hAB]
      simp [Cout, cutoffMatrix, AtlasChartCutoff.localize,
        AtlasChartCutoff.localizedFunction, hDz, hKz]
  -- Coordinate change, frame change, and cutoff reduction each contribute one lower order.
  let pdiag : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex) := fun z ξ ↦
    ((Dout.cutoff z * Din.cutoff z : ℝ) : ℂ) • a z ξ
  have hdiag : IsSymbol univ (m - 1) (p₀ - pdiag) := by
    have h := hasSymbolExpansion_cutoffSymbol m a ha _ _
      Dout.smooth_cutoff Din.smooth_cutoff
      Dout.compact_support Din.compact_support 1
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
        atlasGlobalSymbolInChart A B g c D₀.frameIndex K₀.frameIndex y η := by
    -- The covector is transformed by the derivative of this very chart transition.
    have hfreq : covectorInChart C (c.symm y)
        (covectorFromChart c (c.symm y) η) =
          (fderiv ℝ t (t.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := IM) (I' := IM) (I'' := IM) (C (c.symm y))
        (by
          simpa only [C.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hy.1.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hdM (C.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [C.left_inv hsource] at hcomp
      have htcomp : fderiv ℝ t (t.symm y) =
          (mfderiv IM IM c (c.symm y)).comp
            (mfderiv IM IM C.symm (C (c.symm y))) := hcomp
      ext j
      change inner ℝ η ((mfderiv IM IM c (c.symm y))
          ((mfderiv IM IM C.symm (C (c.symm y)))
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
    let ei := EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ
    let eo := EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ
    let ee := EuclideanSpace.equiv (Fin (A.rank D₀.frameIndex)) ℂ
    let ef := EuclideanSpace.equiv (Fin (B.rank K₀.frameIndex)) ℂ
    have hin (u : EuclideanSpace ℂ (Fin (A.rank D₀.frameIndex))) :
        Finp y u = ei.symm ((A.frameLinearEquiv Din.frameIndex x hy.2.1.2)
          ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))) := by
      have h := (A.coordChangeL_apply D₀.frameIndex Din.frameIndex x
        ⟨hy.1.1.2, hy.2.1.2⟩ ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))).symm
      change Finp y (ee.symm ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2)
        ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u)))) =
          ei.symm ((A.frameLinearEquiv Din.frameIndex x hy.2.1.2)
            ((A.frameLinearEquiv D₀.frameIndex x hy.1.1.2).symm (ee u))) at h
      simpa only [LinearEquiv.apply_symm_apply, ee.symm_apply_apply] using h
    have hout (u : EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))) :
        Fout y u = ef.symm ((B.frameLinearEquiv K₀.frameIndex x hy.1.2)
          ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))) := by
      have h := (B.coordChangeL_apply Dout.frameIndex K₀.frameIndex x ⟨hy.2.2, hy.1.2⟩
        ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))).symm
      change Fout y (eo.symm ((B.frameLinearEquiv Dout.frameIndex x hy.2.2)
        ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u)))) =
          ef.symm ((B.frameLinearEquiv K₀.frameIndex x hy.1.2)
            ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))) at h
      simpa only [LinearEquiv.apply_symm_apply, eo.symm_apply_apply] using h
    have hframes : c.symm y ∈ (A.chart D₀.frameIndex).baseSet ∧
        c.symm y ∈ (B.chart K₀.frameIndex).baseSet :=
      ⟨hy.1.1.2, hy.1.2⟩
    have hvalid : c.symm y ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
        (B.chart Dout.frameIndex).baseSet := hy.2
    apply ContinuousLinearMap.ext
    intro u
    simp only [matrixSymbol, ContinuousLinearMap.comp_apply, cotangentSymbol, pdiag,
      smul_apply, map_smul, hin, hout]
    simp only [atlasGlobalSymbolInChart, dite_eq_left hframes, hg,
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
        ((p - atlasGlobalSymbolInChart A B g c
          D₀.frameIndex K₀.frameIndex) y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      congr 1
      funext η
      exact congrArg (fun v ↦ p y η - v) (hsame y hy η)
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← (hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hbound x hx ξ

end AtiyahSinger
