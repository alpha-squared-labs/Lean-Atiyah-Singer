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
# Intrinsic symbols transported from a compatible chart

Public module ID: M0369.

The two specified cutoffs transport a full local symbol to the original
cotangent and bundle fibers. Smooth compatibility of the base chart suffices
to prove symbol estimates in every original atlas chart. This extends the
existing raw-chart proof without changing the atlas or defining a second
intrinsic symbol object.

This is the order estimate needed for the actual compatible-chart principal
comparison. It alone does not identify the principal class of a section map.
Source: SG III.3.12--3.19, cotangent and original-frame covariance.
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
/-- The actual two-cutoff fiber symbol in a compatible chart has the original atlas order. -/
theorem isAtlasGlobalSymbol_of_mem_maximalAtlas {m : ℝ}
    (C : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hC : C ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A C) (Dout : AtlasChartCutoff B C)
    (hoi : tsupport Dout.cutoff ⊆ C.symm ⁻¹' (A.chart Din.frameIndex).baseSet)
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
    (ha : IsSymbol univ m a) :
    IsAtlasGlobalSymbol A B m (fun x ξ ↦
      if h : x ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
          (B.chart Dout.frameIndex).baseSet then
        ((Dout.cutoff (C x) * Din.cutoff (C x) : ℝ) : ℂ) •
          ((B.frameLinearEquiv Dout.frameIndex x h.2).symm.toLinearMap.comp
            (EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ).toLinearMap).comp
            ((a (C x) (covectorInChart C x ξ)).toLinearMap.comp
              (((EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm.toLinearMap).comp
                (A.frameLinearEquiv Din.frameIndex x h.1.2).toLinearMap))
      else 0) := by
  classical
  let g : AtlasSymbolFunction (n := n) E F := fun x ξ ↦
    if h : x ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
        (B.chart Dout.frameIndex).baseSet then
      ((Dout.cutoff (C x) * Din.cutoff (C x) : ℝ) : ℂ) •
        ((B.frameLinearEquiv Dout.frameIndex x h.2).symm.toLinearMap.comp
          (EuclideanSpace.equiv (Fin (B.rank Dout.frameIndex)) ℂ).toLinearMap).comp
          ((a (C x) (covectorInChart C x ξ)).toLinearMap.comp
            (((EuclideanSpace.equiv (Fin (A.rank Din.frameIndex)) ℂ).symm.toLinearMap).comp
              (A.frameLinearEquiv Din.frameIndex x h.1.2).toLinearMap))
    else 0
  change IsAtlasGlobalSymbol A B m g
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := C.source ∩ (A.chart Din.frameIndex).baseSet ∩
    (B.chart Dout.frameIndex).baseSet
  have hD : IsOpen D := (C.open_source.inter (A.chart Din.frameIndex).open_baseSet).inter
    (B.chart Dout.frameIndex).open_baseSet
  let K := C.symm '' tsupport Dout.cutoff
  have hK : IsCompact K := Dout.compact_support.image_of_continuousOn
    (C.continuousOn_symm.mono (fun y hy ↦ (Dout.support_subset hy).1))
  have hKD : K ⊆ D := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨⟨C.map_target (Dout.support_subset hz).1,
      hoi hz⟩, (Dout.support_subset hz).2⟩
  have hzero (x : M) (hx : x ∉ K) (ξ) : g x ξ = 0 := by
    by_cases hvalid : x ∈ D
    · have hcut : C x ∉ tsupport Dout.cutoff := by
        intro hz
        exact hx ⟨C x, hz, C.left_inv hvalid.1.1⟩
      simp [g, image_eq_zero_of_notMem_tsupport hcut]
    · exact dite_eq_right hvalid
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
  let p₀ : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex) := fun z ξ ↦
    ((Dout.cutoff z * Din.cutoff z : ℝ) : ℂ) • a z ξ
  have hp₀ : IsSymbol Set.univ m p₀ := by
    let R₀ : X → (EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))) :=
      fun z ↦ ((Dout.cutoff z * Din.cutoff z : ℝ) : ℂ) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex)))
    let S₀ : X → (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank Din.frameIndex))) :=
      fun _ ↦ ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin (A.rank Din.frameIndex)))
    have hA : ContDiffOn ℝ ∞ R₀ Set.univ :=
      ((Complex.ofRealCLM.contDiff.comp
        (Dout.smooth_cutoff.mul Din.smooth_cutoff)).smul contDiff_const).contDiffOn
    have hB : ContDiffOn ℝ ∞ S₀ Set.univ := contDiffOn_const
    have hp := isSymbol_matrixSymbol Set.univ isOpen_univ m a ha R₀ S₀ hA hB
    convert hp using 1
    funext z ξ
    simp [matrixSymbol, p₀, R₀, S₀]
  intro c hc e f
  let U := atlasSymbolChartDomain A B c e f
  let p := atlasGlobalSymbolInChart A B g c e f
  have hU : IsOpen U := isOpen_atlasSymbolChartDomain A B c e f
  have hcM := subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := hC
  apply IsSymbol.of_locally hU
  intro z hz
  by_cases hzK : c.symm z ∈ K
  · -- Near the compact support, use the original chart transition and the same two frames.
    let V := U ∩ c.symm ⁻¹' D
    have hV : IsOpen V :=
      (c.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU hD
    have hzV : z ∈ V := ⟨hz, hKD hzK⟩
    let t : OpenPartialHomeomorph X X := C.symm.trans c
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
    let R₀ := fun y ↦ B.coordChangeL Dout.frameIndex f (c.symm y)
    let S₀ := fun y ↦ A.coordChangeL e Din.frameIndex (c.symm y)
    have hcV : ContMDiffOn I I ∞ c.symm V := by
      intro y hy
      exact (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1.1.1).contMDiffWithinAt
    have hR : ContDiffOn ℝ ∞ R₀ V :=
      B.contDiffOn_coordChangeL_comp Dout.frameIndex f V c.symm hcV
        (fun y hy ↦ ⟨hy.2.2, hy.1.2⟩)
    have hS : ContDiffOn ℝ ∞ S₀ V :=
      A.contDiffOn_coordChangeL_comp e Din.frameIndex V c.symm hcV
        (fun y hy ↦ ⟨hy.1.1.2, hy.2.1.2⟩)
    refine ⟨V, hV, hzV, Set.inter_subset_left,
      congrSymbol hV _ p (isSymbol_matrixSymbol V hV m _ hpt R₀ S₀ hR hS) ?_⟩
    intro y hy η
    -- The frequency change is the adjoint derivative of precisely this chart transition.
    have hfreq : covectorInChart C (c.symm y)
        (covectorFromChart c (c.symm y) η) =
          (fderiv ℝ t (t.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (C (c.symm y))
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
          (mfderiv I I c (c.symm y)).comp
            (mfderiv I I C.symm (C (c.symm y))) := hcomp
      ext j
      change inner ℝ η ((mfderiv I I c (c.symm y))
          ((mfderiv I I C.symm (C (c.symm y)))
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
    let ee := EuclideanSpace.equiv (Fin (A.rank e)) ℂ
    let ef := EuclideanSpace.equiv (Fin (B.rank f)) ℂ
    have hin (u : EuclideanSpace ℂ (Fin (A.rank e))) :
        S₀ y u = ei.symm ((A.frameLinearEquiv Din.frameIndex x hy.2.1.2)
          ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))) := by
      have h := (A.coordChangeL_apply e Din.frameIndex x
        ⟨hy.1.1.2, hy.2.1.2⟩ ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))).symm
      change S₀ y (ee.symm ((A.frameLinearEquiv e x hy.1.1.2)
        ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u)))) =
          ei.symm ((A.frameLinearEquiv Din.frameIndex x hy.2.1.2)
            ((A.frameLinearEquiv e x hy.1.1.2).symm (ee u))) at h
      simpa only [LinearEquiv.apply_symm_apply, ee.symm_apply_apply] using h
    have hout (u : EuclideanSpace ℂ (Fin (B.rank Dout.frameIndex))) :
        R₀ y u = ef.symm ((B.frameLinearEquiv f x hy.1.2)
          ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))) := by
      have h := (B.coordChangeL_apply Dout.frameIndex f x ⟨hy.2.2, hy.1.2⟩
        ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))).symm
      change R₀ y (eo.symm ((B.frameLinearEquiv Dout.frameIndex x hy.2.2)
        ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u)))) =
          ef.symm ((B.frameLinearEquiv f x hy.1.2)
            ((B.frameLinearEquiv Dout.frameIndex x hy.2.2).symm (eo u))) at h
      simpa only [LinearEquiv.apply_symm_apply, eo.symm_apply_apply] using h
    have hframes : c.symm y ∈ (A.chart e).baseSet ∧ c.symm y ∈ (B.chart f).baseSet :=
      ⟨hy.1.1.2, hy.1.2⟩
    have hvalid : c.symm y ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
        (B.chart Dout.frameIndex).baseSet := hy.2
    apply ContinuousLinearMap.ext
    intro u
    simp only [matrixSymbol, ContinuousLinearMap.comp_apply, cotangentSymbol, p₀,
      smul_apply, map_smul, hin, hout]
    simp only [p, atlasGlobalSymbolInChart, dite_eq_left hframes, g,
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
    change 0 = atlasGlobalSymbolInChart A B g c e f y η
    simp [atlasGlobalSymbolInChart, hzero (c.symm y) hy.2]

end AtiyahSinger
