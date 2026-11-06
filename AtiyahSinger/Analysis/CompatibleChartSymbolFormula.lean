/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompatibleChartGlobalSymbol
public import AtiyahSinger.Analysis.CoordinateChange
public import AtiyahSinger.Analysis.FrameChange
public import AtiyahSinger.Geometry.AtlasFrameTransition

/-!
# Exact coordinate formula for the original localized symbol

On the actual overlap, the specified intrinsic symbol has the original forward
cotangent adjoint and both prescribed frame transitions. This formula does not
assume symbol estimates or replace the original global representative. It is
used to transfer actual associated chart estimates through the same tensor
frames and finite sums.
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

set_option maxSynthPendingDepth 30 in
open scoped Classical in
/-- The specified localized symbol has the exact original cotangent and frame expression. -/
theorem atlasGlobalSymbolInChart_eq_matrixSymbol_of_localized
    (C : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hC : C ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (Din : AtlasChartCutoff A C) (Dout : AtlasChartCutoff B C)
    (a : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex))
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
    (hc : c ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (e : A.Index) (f : B.Index) (y : EuclideanSpace ℝ (Fin n))
    (hy₀ : y ∈ atlasSymbolChartDomain A B c e f)
    (hy₁ : c.symm y ∈ C.source ∩ (A.chart Din.frameIndex).baseSet ∩
      (B.chart Dout.frameIndex).baseSet) (η : EuclideanSpace ℝ (Fin n)) :
    let p₀ : SymbolFunction n (A.rank Din.frameIndex) (B.rank Dout.frameIndex) :=
      fun z ξ ↦ ((Dout.cutoff z * Din.cutoff z : ℝ) : ℂ) • a z ξ
    atlasGlobalSymbolInChart A B g c e f y η =
      matrixSymbol (fun z ↦ B.coordChangeL Dout.frameIndex f (c.symm z))
        (fun z ↦ A.coordChangeL e Din.frameIndex (c.symm z))
        (cotangentSymbol (C.symm.trans c) p₀) y η := by
  classical
  intro p₀
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let U := atlasSymbolChartDomain A B c e f
  let D := C.source ∩ (A.chart Din.frameIndex).baseSet ∩
    (B.chart Dout.frameIndex).baseSet
  have hy : y ∈ U ∩ c.symm ⁻¹' D := ⟨hy₀, hy₁⟩
  let t := C.symm.trans c
  let hcM := hc
  let hdM := hC
  let R₀ := fun z ↦ B.coordChangeL Dout.frameIndex f (c.symm z)
  let S₀ := fun z ↦ A.coordChangeL e Din.frameIndex (c.symm z)
  let p := atlasGlobalSymbolInChart A B g c e f
  change p y η = matrixSymbol R₀ S₀ (cotangentSymbol t p₀) y η
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
  symm
  apply ContinuousLinearMap.ext
  intro u
  simp only [matrixSymbol, ContinuousLinearMap.comp_apply, cotangentSymbol, p₀,
    smul_apply, map_smul, hin, hout]
  simp only [p, atlasGlobalSymbolInChart, dite_eq_left hframes, hg,
    dite_eq_left hvalid, hfreq, LinearMap.coe_toContinuousLinearMap',
    LinearMap.comp_apply, LinearMap.smul_apply, map_smul]
  rfl

end AtiyahSinger
