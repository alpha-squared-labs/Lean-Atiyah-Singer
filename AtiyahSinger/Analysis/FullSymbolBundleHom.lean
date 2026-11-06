/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PuncturedSymbol
public import AtiyahSinger.Topology.ModelBundleHom

/-!
# Full symbols as actual continuous maps of cotangent pullback bundles

Public module ID: M0651.

The original chartwise symbol smoothness gives continuity of the full Hom
section, including zero covectors. Its joint evaluation is therefore an actual
bundle homomorphism on the original cotangent pullbacks. This full-frequency
statement is needed for graded products along both frequency axes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]


/-- The full symbol is continuous in the original Hom total space, including zero covectors. -/
theorem IsGlobalSymbol.continuous_total {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsGlobalSymbol (r := r) (q := q) E F m a) :
    Continuous (fun z : CotangentTotalSpace (n := n) (M := M) ↦
      (⟨z.proj, a z.proj z.snd⟩ : TotalSpace
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
        (fun x ↦ E x →L[ℂ] F x))) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let c := chartAt (EuclideanSpace ℝ (Fin n)) z₀.proj
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.proj
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.proj
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) z₀.proj
  have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ _
  have hx₀ : z₀.proj ∈ c.source := mem_chart_source _ _
  have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
    (fun z : CotangentTotalSpace (n := n) (M := M) ↦ z) (x₀ := z₀)).mp
      continuous_id.continuousAt
  have hbase := hsource.1
  have hchart : ContinuousAt
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦ c z.proj) z₀ :=
    (c.continuousAt hx₀).comp
      (f := fun z : CotangentTotalSpace (n := n) (M := M) ↦ z.proj) hbase
  have hξ : ContinuousAt (fun z : CotangentTotalSpace (n := n) (M := M) ↦
      z.snd.comp (t.symmL ℝ z.proj)) z₀ := by
    have h := hsource.2
    change ContinuousAt (fun z : CotangentTotalSpace (n := n) (M := M) ↦
      ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.proj).comp
        (z.snd.comp (t.symmL ℝ z.proj))) z₀ at h
    simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp] using h
  -- The moving covector is evaluated on the inverse chart differential in native coordinates.
  have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
  have hd₀ := ((contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx₀)).mfderiv_const
    (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt
  unfold inTangentCoordinates at hd₀
  simp only [c.left_inv hx₀] at hd₀
  have hd := hd₀.comp
    (f := fun z : CotangentTotalSpace (n := n) (M := M) ↦ c z.proj) hchart
  have hdual (v : EuclideanSpace ℝ (Fin n)) : ContinuousAt
      (fun z : CotangentTotalSpace (n := n) (M := M) ↦
        z.snd ((mfderiv I I c.symm (c z.proj)) v)) z₀ := by
    apply (hξ.clm_apply (hd.clm_apply (continuousAt_const (y := v)))).congr_of_eventuallyEq
    filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
    dsimp only [Function.comp_apply, ContinuousLinearMap.inCoordinates, Function.id_def]
    simp only [TangentBundle.symmL_model_space]
    erw [c.left_inv hz]
    change z.snd ((mfderiv I I c.symm (c z.proj)) v) =
      z.snd (t.symmL ℝ z.proj (t.continuousLinearMapAt ℝ z.proj
        ((mfderiv I I c.symm (c z.proj)) v)))
    exact congrArg z.snd
      (t.symmL_continuousLinearMapAt (R := ℝ) hz
        ((mfderiv I I c.symm (c z.proj)) v)).symm
  have hcoord : ContinuousAt (fun z : CotangentTotalSpace (n := n) (M := M) ↦
      covectorInChart c z.proj z.snd) z₀ := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    exact hdual (EuclideanSpace.single j 1)
  -- The original chartwise smoothness is now composed with these actual cotangent coordinates.
  have hdomain : (c z₀.proj, covectorInChart c z₀.proj z₀.snd) ∈
      symbolChartDomain E F c e f ×ˢ Set.univ := by
    refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, Set.mem_univ _⟩ <;>
      simpa only [Set.mem_preimage, c.left_inv hx₀] using mem_baseSet_trivializationAt _ _ _
  have hvalue := ((ha c hc e f).1.continuousOn.continuousAt
    (((isOpen_symbolChartDomain E F c e f).prod isOpen_univ).mem_nhds hdomain)).comp
      (f := fun z : CotangentTotalSpace (n := n) (M := M) ↦
        (c z.proj, covectorInChart c z.proj z.snd)) (hchart.prodMk hcoord)
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase, ?_⟩
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
  change (f.continuousLinearMapAt ℂ z.proj).comp
    ((a z.proj z.snd).comp (e.symmL ℂ z.proj)) =
    globalSymbolInChart E F a c e f (c z.proj)
      (covectorInChart c z.proj z.snd)
  rw [globalSymbolInChart_covectorInChart E F _ c hc e f z.proj hz]

/-- The specified full symbol acts by its exact maps on the original cotangent pullbacks. -/
def fullSymbolBundleHom {m : ℝ}
    (a : globalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.Hom ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E)
      ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F) :=
  ComplexBundle.modelPullbackHom (EuclideanSpace ℂ (Fin r)) (EuclideanSpace ℂ (Fin q))
    (cotangentProjection (n := n) (M := M)) (fun z ↦ a.val z.proj z.snd)
    a.property.continuous_total

end AtiyahSinger
