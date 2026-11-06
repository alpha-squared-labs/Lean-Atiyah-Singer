/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbolKClass

/-!
# Full atlas symbols as continuous maps on the original cotangent pullbacks

Public module ID: M2297.

The original full-symbol estimates give smooth coordinate matrices at every frequency,
including zero. Joint evaluation through the supplied atlas frames yields a continuous
bundle map without choosing norms on the original fibers or a constant global rank.
This map is the boundary map needed for the general elliptic compact-support triple.

Sources: SG III.3.18 and I.9.26. The explicit atlas and pullback transport is a project
supplement to the standard full-symbol construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The full atlas symbol acts continuously on the original cotangent pullbacks. -/
theorem IsAtlasGlobalSymbol.continuous_totalMap {m : ℝ}
    {a : AtlasSymbolFunction (n := n) E F} (ha : IsAtlasGlobalSymbol A B m a) :
    let p := (cotangentProjection (n := n) (M := M) : _ → M)
    Continuous (fun z : TotalSpace Unit (p *ᵖ E) ↦
      (⟨z.proj, a z.proj.proj z.proj.snd z.snd⟩ : TotalSpace Unit (p *ᵖ F))) := by
  /- Use the supplied source and target frames around the original cotangent point.
  The coordinate symbol is smooth in the base and all frequencies; evaluation on the
  actual input frame coordinates is continuous. Transport this output through the
  same target frame and retain the unchanged cotangent base in the pullback topology. -/
  classical
  let p := (cotangentProjection (n := n) (M := M) : _ → M)
  let D := TotalSpace Unit (p *ᵖ E)
  have hproj : Continuous (fun z : D ↦ z.proj) :=
    Pullback.continuous_proj Unit E p
  have hinput : Continuous (fun z : D ↦ (⟨z.proj.proj, z.snd⟩ : TotalSpace Unit E)) :=
    Pullback.continuous_lift Unit E p
  -- First prove continuity in the original target total space, using only its atlas frames.
  have houtput : Continuous (fun z : D ↦
      (⟨z.proj.proj, a z.proj.proj z.proj.snd z.snd⟩ : TotalSpace Unit F)) := by
    apply continuous_iff_continuousAt.mpr
    intro z₀
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let c := chartAt (EuclideanSpace ℝ (Fin n)) z₀.proj.proj
    let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) z₀.proj.proj
    obtain ⟨i, hi₀⟩ := A.covers z₀.proj.proj
    obtain ⟨j, hj₀⟩ := B.covers z₀.proj.proj
    have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ _
    have hx₀ : z₀.proj.proj ∈ c.source := mem_chart_source _ _
    have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
      (fun z : D ↦ z.proj) (x₀ := z₀)).mp
        hproj.continuousAt
    have hbase := hsource.1
    have hchart : ContinuousAt
        (fun z : D ↦ c z.proj.proj) z₀ :=
      (c.continuousAt hx₀).comp
        (f := fun z : D ↦ z.proj.proj) hbase
    have hξ : ContinuousAt (fun z : D ↦
        z.proj.snd.comp (t.symmL ℝ z.proj.proj)) z₀ := by
      have h := hsource.2
      change ContinuousAt (fun z : D ↦
        ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj.proj).comp
          (z.proj.snd.comp (t.symmL ℝ z.proj.proj))) z₀ at h
      simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_comp] using h
    -- The moving covector is evaluated on the inverse chart differential in native coordinates.
    have hcm : c ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.subset_maximalAtlas (I := I) hc
    have hd₀ := ((contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx₀)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt
    unfold inTangentCoordinates at hd₀
    simp only [c.left_inv hx₀] at hd₀
    have hd := hd₀.comp
      (f := fun z : D ↦ c z.proj.proj) hchart
    have hdual (v : EuclideanSpace ℝ (Fin n)) : ContinuousAt
        (fun z : D ↦
          z.proj.snd ((mfderiv I I c.symm (c z.proj.proj)) v)) z₀ := by
      apply (hξ.clm_apply (hd.clm_apply (continuousAt_const (y := v)))).congr_of_eventuallyEq
      filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
      dsimp only [Function.comp_apply, ContinuousLinearMap.inCoordinates, Function.id_def]
      simp only [TangentBundle.symmL_model_space]
      erw [c.left_inv hz]
      change z.proj.snd ((mfderiv I I c.symm (c z.proj.proj)) v) =
        z.proj.snd (t.symmL ℝ z.proj.proj (t.continuousLinearMapAt ℝ z.proj.proj
          ((mfderiv I I c.symm (c z.proj.proj)) v)))
      exact congrArg z.proj.snd
        (t.symmL_continuousLinearMapAt (R := ℝ) hz
          ((mfderiv I I c.symm (c z.proj.proj)) v)).symm
    have hcoord : ContinuousAt (fun z : D ↦
        covectorInChart c z.proj.proj z.proj.snd) z₀ := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp
      apply continuousAt_pi.mpr
      intro j
      exact hdual (EuclideanSpace.single j 1)
    -- The original chartwise smoothness is now composed with these actual cotangent coordinates.
    -- Full-symbol smoothness also covers the zero cotangent vector.
    have hdomain : (c z₀.proj.proj,
        covectorInChart c z₀.proj.proj z₀.proj.snd) ∈
        atlasSymbolChartDomain A B c i j ×ˢ Set.univ := by
      refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, Set.mem_univ _⟩
      · simpa only [Set.mem_preimage, c.left_inv hx₀] using hi₀
      · simpa only [Set.mem_preimage, c.left_inv hx₀] using hj₀
    have hopen : IsOpen (atlasSymbolChartDomain A B c i j) := by
      simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.continuousOn_symm.isOpen_inter_preimage c.open_target
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    have hoperator := ((ha c hc i j).1.continuousOn.continuousAt
      ((hopen.prod isOpen_univ).mem_nhds hdomain)).comp
        (f := fun z : D ↦ (c z.proj.proj,
          covectorInChart c z.proj.proj z.proj.snd)) (hchart.prodMk hcoord)
    have hcoordinates : ContinuousAt (fun z : D ↦
        WithLp.toLp 2 (A.chart i (⟨z.proj.proj, z.snd⟩ : TotalSpace Unit E)).2) z₀ :=
      (PiLp.continuous_toLp 2 (fun _ : Fin (A.rank i) ↦ ℂ)).continuousAt.comp
        (((A.chart i).toOpenPartialHomeomorph.continuousAt
          ((A.chart i).mem_source.mpr hi₀)).comp hinput.continuousAt).snd
    have hvalue := (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).continuous.continuousAt.comp
      (hoperator.clm_apply hcoordinates)
    have hchartFormula (z : EuclideanSpace ℝ (Fin n)) (y : M) (hy : c.symm z = y)
        (hi : y ∈ (A.chart i).baseSet) (hj : y ∈ (B.chart j).baseSet)
        (η : EuclideanSpace ℝ (Fin n)) (v : E y) :
        (B.chart j (⟨y, a y (covectorFromChart c y η) v⟩ : TotalSpace Unit F)).2 =
          (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
            (atlasGlobalSymbolInChart A B a c i j z η
              (WithLp.toLp 2 (A.chart i (⟨y, v⟩ : TotalSpace Unit E)).2)) := by
      subst y
      dsimp only [atlasGlobalSymbolInChart]
      rw [dite_eq_left ⟨hi, hj⟩]
      change B.frameLinearEquiv j (c.symm z) hj
          (a (c.symm z) (covectorFromChart c (c.symm z) η) v) =
        (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
          ((EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
            (B.frameLinearEquiv j (c.symm z) hj
              (a (c.symm z) (covectorFromChart c (c.symm z) η)
                ((A.frameLinearEquiv i (c.symm z) hi).symm
                  (A.frameLinearEquiv i (c.symm z) hi v)))))
      rw [(EuclideanSpace.equiv (Fin (B.rank j)) ℂ).apply_symm_apply,
        (A.frameLinearEquiv i (c.symm z) hi).symm_apply_apply]
    have hformula (x : M) (hx : x ∈ c.source)
        (hi : x ∈ (A.chart i).baseSet) (hj : x ∈ (B.chart j).baseSet)
        (ξ : CotangentFiber (n := n) x) (v : E x) :
        (B.chart j (⟨x, a x ξ v⟩ : TotalSpace Unit F)).2 =
          (EuclideanSpace.equiv (Fin (B.rank j)) ℂ)
            (atlasGlobalSymbolInChart A B a c i j (c x) (covectorInChart c x ξ)
              (WithLp.toLp 2 (A.chart i (⟨x, v⟩ : TotalSpace Unit E)).2)) := by
      simpa only [covectorFromChart_covectorInChart c hc x hx] using
        hchartFormula (c x) x (c.left_inv hx) hi hj (covectorInChart c x ξ) v
    -- Transport the coordinate evaluation back through the same original target frame.
    apply (B.chart j).continuousAt_of_comp_left hbase hj₀
    apply (hbase.prodMk hvalue).congr_of_eventuallyEq
    filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀),
      hbase.preimage_mem_nhds ((A.chart i).open_baseSet.mem_nhds hi₀),
      hbase.preimage_mem_nhds ((B.chart j).open_baseSet.mem_nhds hj₀)] with z hz hi hj
    apply Prod.ext
    · exact (B.chart j).coe_fst' hj
    · exact hformula z.proj.proj hz hi hj z.proj.snd z.snd
  -- The target pullback topology retains this same cotangent base and output vector.
  rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
  exact hproj.prodMk houtput

/-- The specified full atlas symbol as an actual Hom of the original pullbacks. -/
def atlasFullSymbolBundleHom {m : ℝ} (a : atlasGlobalSymbolSpace A B m) :
    Hom ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) where
  linearMap := fun z ↦ a.val z.proj z.snd
  continuous_total := IsAtlasGlobalSymbol.continuous_totalMap A B a.property

end AtiyahSinger
