/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasFrameTransition
public import AtiyahSinger.Geometry.HermitianFlagIsometricCharts
public import AtiyahSinger.Geometry.SmoothAtlasOrthonormalFrames

/-!
# Local flag products from the specified smooth bundle atlas

Public module ID: M1400.

Orthonormalizing one of the supplied smooth frames gives a local flag product
in the original topology. Its coordinate matrices in every other supplied
frame are smooth on the actual overlap. Native continuous frames are used
only to compare total-space topologies, without assuming they are smooth.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable (r : ℕ) {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E)
  (A : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    SmoothComplexBundleAtlas (n := n) E)
  (hh : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    A.IsSmoothHermitianMetric h)

attribute [local instance] hermitianFlagTopology

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

include hh

/-- A local flag product has smooth forward and inverse matrices in every original frame. -/
theorem exists_smoothHermitianFlagLocalProduct (x : M) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      ∃ s : ∀ y : M, EuclideanSpace ℂ (Fin r) ≃L[ℂ] E y,
      ∃ hs : ∀ y ∈ U, ∀ u v,
        (h.toCore y).inner (s y u) (s y v) = inner ℂ u v,
      ∃ t : Trivialization
          (HermitianFlagSpace r (EuclideanSpace ℂ (Fin r)) InnerProductSpace.toCore)
          (hermitianFlagProjection r E h : HermitianFlagBundle r E h → M),
      t.baseSet = U ∧
        (∀ p : HermitianFlagBundle r E h, ∀ hp : p.1 ∈ U,
          t p = (p.1, hermitianFlagEquivOfIsometry (h.toCore p.1) (s p.1) (hs p.1 hp) p.2)) ∧
        (∀ (y : M) (Q : HermitianFlagSpace r (EuclideanSpace ℂ (Fin r))
            InnerProductSpace.toCore) (hy : y ∈ U),
          t.toPartialEquiv.symm (y, Q) =
            ⟨y, (hermitianFlagEquivOfIsometry (h.toCore y) (s y) (hs y hy)).symm Q⟩) ∧
      ∃ a : ∀ i : A.Index, M → EuclideanSpace ℂ (Fin r) →L[ℂ]
          EuclideanSpace ℂ (Fin (A.rank i)),
      ∃ b : ∀ i : A.Index, M → EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
          EuclideanSpace ℂ (Fin r),
        (∀ i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))) ∞
          (a i) ((U : Set M) ∩ (A.chart i).baseSet)) ∧
        (∀ i, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          (b i) ((U : Set M) ∩ (A.chart i).baseSet)) ∧
        (∀ i y (_hy : y ∈ U) (hi : y ∈ (A.chart i).baseSet) (v : E y),
          a i y ((s y).symm v) =
            (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm (A.frameLinearEquiv i y hi v)) ∧
        ∀ i y (_hy : y ∈ U) (hi : y ∈ (A.chart i).baseSet) (v : E y),
          b i y ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
            (A.frameLinearEquiv i y hi v)) = (s y).symm v := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let V := EuclideanSpace ℂ (Fin r)
  let : ∀ y, FiniteDimensional ℂ (E y) := fun y ↦
    VectorBundle.finiteDimensional ℂ V E y
  obtain ⟨i₀, hx₀⟩ := A.covers x
  let W := EuclideanSpace ℂ (Fin (A.rank i₀))
  let ev := EuclideanSpace.equiv (Fin (A.rank i₀)) ℂ
  let native := trivializationAt V E x
  let U : TopologicalSpace.Opens M :=
    ⟨(A.chart i₀).baseSet ∩ native.baseSet, (A.chart i₀).open_baseSet.inter native.open_baseSet⟩
  have hrank : A.rank i₀ = r := by
    have h₁ := (A.frameLinearEquiv i₀ x hx₀).finrank_eq
    have h₂ := (native.linearEquivAt ℂ x (mem_baseSet_trivializationAt V E x)).finrank_eq
    simpa only [V, Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one,
      finrank_euclideanSpace] using h₁.symm.trans h₂
  obtain ⟨R, hR⟩ : ∃ R : V ≃L[ℂ] W,
      ∀ u v, inner ℂ (R u) (R v) = inner ℂ u v := by
    have htransport (p q : ℕ) (hpq : p = q) :
        ∃ T : EuclideanSpace ℂ (Fin p) ≃L[ℂ] EuclideanSpace ℂ (Fin q),
          ∀ u v, inner ℂ (T u) (T v) = inner ℂ u v := by
      subst q
      exact ⟨ContinuousLinearEquiv.refl ℂ _, fun _ _ ↦ rfl⟩
    exact htransport r (A.rank i₀) hrank.symm
  obtain ⟨e, he, heSmooth, heInv⟩ := A.exists_orthonormalFrameCoordinates h hh i₀
  let L (y : M) (hy : y ∈ (A.chart i₀).baseSet) : W ≃L[ℂ] E y :=
    ev.trans (A.frameLinearEquiv i₀ y hy).symm.toContinuousLinearEquiv
  let s (y : M) : V ≃L[ℂ] E y :=
    if hy : y ∈ (A.chart i₀).baseSet then (R.trans (e y)).trans (L y hy)
    else ((trivializationAt V E y).linearEquivAt ℂ y
      (mem_baseSet_trivializationAt V E y)).symm.toContinuousLinearEquiv
  have hsval (y : M) (hy : y ∈ (A.chart i₀).baseSet) :
      s y = (R.trans (e y)).trans (L y hy) := dite_eq_left hy
  have hs : ∀ y ∈ U, ∀ u v, (h.toCore y).inner (s y u) (s y v) = inner ℂ u v := by
    intro y hy u v
    rw [hsval y hy.1]
    exact (he y hy.1 (R u) (R v)).trans (hR u v)
  -- Native comparison uses only continuous original total-space charts.
  have hsection (v : V) : ContinuousOn (fun y ↦ (⟨y, s y v⟩ : TotalSpace Unit E)) U := by
    have hc : ContinuousOn (fun y ↦ ev (e y (R v))) (A.chart i₀).baseSet :=
      ev.continuous.comp_continuousOn
        (heSmooth.continuousOn.clm_apply continuousOn_const)
    have hinv : ContinuousOn (fun y ↦ (A.chart i₀).toOpenPartialHomeomorph.symm
        (y, ev (e y (R v)))) U := (A.chart i₀).toOpenPartialHomeomorph.continuousOn_symm.comp
      (continuous_id.continuousOn.prodMk (hc.mono (fun _ hy ↦ hy.1)))
      (fun y hy ↦ (A.chart i₀).mem_target.mpr hy.1)
    apply hinv.congr
    intro y hy
    have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
      ((A.chart i₀).proj_symm_apply' (x := ev (e y (R v))) hy.1)
      ((A.chart i₀).toOpenPartialHomeomorph.symm (y, ev (e y (R v)))).2
    refine (congrArg (fun T : V ≃L[ℂ] E y ↦ (⟨y, T v⟩ : TotalSpace Unit E))
      (hsval y hy.1)).trans ?_
    exact hpoint
  have hA : ContinuousOn (fun y ↦ (native.continuousLinearMapAt ℂ y).comp
      (s y).toContinuousLinearMap) U := by
    apply continuousOn_clm_apply.mpr
    intro v
    have hv := (continuous_unitTotalEquiv V E).comp_continuousOn (hsection v)
    have hc := (native.continuousOn.comp hv
      (fun _ hy ↦ native.mem_source.mpr hy.2)).snd
    apply hc.congr
    intro y hy
    exact native.continuousLinearMapAt_apply_of_mem ℂ hy.2 (s y v)
  have hB : ContinuousOn (fun y ↦ (s y).symm.toContinuousLinearMap.comp
      (native.symmL ℂ y)) U := by
    apply continuousOn_clm_apply.mpr
    intro v
    have hv : ContinuousOn (fun y ↦ (⟨y, native.symmL ℂ y v⟩ : TotalSpace V E)) U := by
      have hc : ContinuousOn (fun y ↦ native.toOpenPartialHomeomorph.symm (y, v)) U :=
        native.toOpenPartialHomeomorph.continuousOn_symm.comp
        (continuous_id.continuousOn.prodMk (continuous_const (y := v)).continuousOn)
        (fun _ hy ↦ native.mem_target.mpr hy.2)
      apply hc.congr
      intro y hy
      simpa only [native.symmL_apply hy.2] using native.mk_symm hy.2 v
    have hu : ContinuousOn
        (fun y ↦ (⟨y, native.symmL ℂ y v⟩ : TotalSpace Unit E)) U :=
      (continuous_unitTotalEquiv_symm V E).comp_continuousOn hv
    have hc : ContinuousOn
        (fun y ↦ A.chart i₀ (⟨y, native.symmL ℂ y v⟩ : TotalSpace Unit E)) U := by
      have hchart : ContinuousOn (A.chart i₀) (A.chart i₀).source :=
        (A.chart i₀).toOpenPartialHomeomorph.continuousOn
      exact hchart.comp hu (fun _ hy ↦ (A.chart i₀).mem_source.mpr hy.1)
    have hvec := ev.symm.continuous.comp_continuousOn hc.snd
    have hinv := R.symm.continuous.comp_continuousOn
      ((heInv.continuousOn.mono (fun _ hy ↦ hy.1)).clm_apply hvec)
    apply hinv.congr
    intro y hy
    exact congrArg (fun T : V ≃L[ℂ] E y ↦ T.symm (native.symmL ℂ y v)) (hsval y hy.1)
  obtain ⟨t, ht, htForward, htInverse⟩ :=
    exists_hermitianFlagTrivialization_of_isometries r E h x U (fun _ hy ↦ hy.2) s hs hA hB
  -- Reuse the original rectangular transitions; both coordinates describe the same fiber vector.
  have hchange (i j : A.Index) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank j))) ∞ (A.coordChangeL i j)
      ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
    apply contMDiffOn_finsetSum
    intro k _
    let ej := (EuclideanSpace.equiv (Fin (A.rank j)) ℂ).symm.toContinuousLinearMap
    have hcol := (ej.restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn
      (A.contMDiffOn_coordChange i j k)
    let C := ContinuousLinearMap.smulRightL ℂ
      (EuclideanSpace ℂ (Fin (A.rank i))) (EuclideanSpace ℂ (Fin (A.rank j)))
      ((ContinuousLinearMap.proj k).comp
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toContinuousLinearMap)
    exact (C.restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn hcol
  have hcomp {p q k : ℕ} (S : Set M)
      (f : M → EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin k))
      (g : M → EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (hf : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin k)) ∞ f S)
      (hg : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ g S) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin p) →L[ℂ] EuclideanSpace ℂ (Fin k)) ∞
        (fun y ↦ (f y).comp (g y)) S := by
    let B := (ContinuousLinearMap.compL ℂ (EuclideanSpace ℂ (Fin p))
      (EuclideanSpace ℂ (Fin q)) (EuclideanSpace ℂ (Fin k))).bilinearRestrictScalars ℝ
    have hc := (B.contDiff.comp contDiff_fst).clm_apply contDiff_snd (n := ∞)
    exact hc.contMDiff.comp_contMDiffOn (hf.prodMk_space hg)
  let a (i : A.Index) (y : M) :=
    (A.coordChangeL i₀ i y).comp ((e y).toContinuousLinearMap.comp R.toContinuousLinearMap)
  let b (i : A.Index) (y : M) :=
    R.symm.toContinuousLinearMap.comp
      ((e y).symm.toContinuousLinearMap.comp (A.coordChangeL i i₀ y))
  have ha (i : A.Index) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, V →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))) ∞
      (a i) ((U : Set M) ∩ (A.chart i).baseSet) :=
    hcomp _ _ _ ((hchange i₀ i).mono (fun _ hy ↦ ⟨hy.1.1, hy.2⟩))
      (hcomp _ _ _ (heSmooth.mono (fun _ hy ↦ hy.1.1)) contMDiffOn_const)
  have hb (i : A.Index) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] V) ∞
      (b i) ((U : Set M) ∩ (A.chart i).baseSet) :=
    hcomp _ _ _ contMDiffOn_const
      (hcomp _ _ _ (heInv.mono (fun _ hy ↦ hy.1.1))
        ((hchange i i₀).mono (fun _ hy ↦ ⟨hy.2, hy.1.1⟩)))
  refine ⟨U, ⟨hx₀, mem_baseSet_trivializationAt V E x⟩, s, hs, t, ht,
    htForward, htInverse, a, b, ha, hb, ?_, ?_⟩
  · intro i y hy hi v
    rw [hsval y hy.1]
    change A.coordChangeL i₀ i y ((e y) (R (R.symm ((e y).symm
      (ev.symm (A.frameLinearEquiv i₀ y hy.1 v)))))) = _
    rw [R.apply_symm_apply, (e y).apply_symm_apply]
    exact (A.coordChangeL_apply i₀ i y ⟨hy.1, hi⟩ v).symm
  · intro i y hy hi v
    rw [hsval y hy.1]
    change R.symm ((e y).symm (A.coordChangeL i i₀ y
      ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm (A.frameLinearEquiv i y hi v)))) = _
    exact congrArg (fun z ↦ R.symm ((e y).symm z))
      (A.coordChangeL_apply i i₀ y ⟨hi, hy.1⟩ v).symm

end AtiyahSinger.ComplexBundle
