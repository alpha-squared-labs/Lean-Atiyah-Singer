/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.EquivariantFrameFamilies
public import AtiyahSinger.Analysis.SmoothKernelIntegral
public import AtiyahSinger.Geometry.EquivariantDensityFamilies
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral
public import AtiyahSinger.Analysis.SmoothKernelDensity
public import AtiyahSinger.Geometry.DensityDiffeomorph
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Weighted compact averages of conjugated smooth kernels

Public module ID: M0578.

The forward parameter supplies a joint smooth kernel for conjugation by its
inverse. Its input density is the actual inverse-action pushforward relative to
the original measure. Continuous inversion in the compact parameter, followed
by integration against its pushforward measure, gives the requested weighted conjugate
average without a Lie group or an invariant base measure.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]

set_option maxHeartbeats 1500000 in
-- Joint kernel transport, the original measure change and the average share the same fibers.
/-- Continuous weighted Haar averages of geometric smooth-kernel conjugates are smooth kernels. -/
theorem SmoothKernel.exists_weighted_conjugate_integral
    (K : SmoothKernel (n := n) (r := r) (q := q) E F)
    (w : G → ℂ) (hw : Continuous w) :
    ∃ L : SmoothKernel (n := n) (r := r) (q := q) E F,
      ∀ (u : smoothSections (n := n) (r := r) E) (x : M),
        (L.toLinearMap μ u).val x =
          ∫ g, w g • ((σF.smoothSectionRepresentation IG hσF g)
            (K.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE g⁻¹) u))).val x
            ∂(Measure.haarMeasure (⊤ : PositiveCompacts G)) := by
  /- Use the forward parameter h for conjugation by h⁻¹. The raw kernel uses
  the inverse output action, the original kernel at (h*x,h*y), and the input
  action. Multiply by the actual inverse-pushforward density in the input
  variable. This whole family is smooth in h; only its final parameter change
  uses group inversion, for which continuity suffices. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let (x : M) : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let J := IG.prod (I.prod I)
  let C (g : G) (x : M) : F x ≃ₗ[ℂ] F (g • x) :=
    LinearEquiv.ofBijective (σF.linearMap g x) (σF.linearMap_bijective g x)
  let L (g : G) (x y : M) : E y →L[ℂ] F x :=
    (C g x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((K.toFun (g • x) (g • y)).comp (σE.linearMap g y).toContinuousLinearMap)
  obtain ⟨R, hR, hRpos, hRmeasure⟩ := exists_smooth_inv_smul_density (n := n) (G := G) IG μ
  -- Joint smoothness is established on the actual moving overlap of four original frames.
  have hL
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      ContMDiffOn J
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun p : G × (M × M) ↦ kernelInFrames E F (L p.1) e f p.2)
        (Set.univ ×ˢ (f.baseSet ×ˢ e.baseSet)) := by
    intro p hp
    let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p.1 • p.2.2)
    let k := trivializationAt (EuclideanSpace ℂ (Fin q)) F (p.1 • p.2.1)
    let U : Set (G × (M × M)) := {z | z.2.1 ∈ f.baseSet ∧ z.2.2 ∈ e.baseSet ∧
      z.1 • z.2.1 ∈ k.baseSet ∧ z.1 • z.2.2 ∈ d.baseSet}
    have hmoveX : ContMDiff J I ∞ (fun z : G × (M × M) ↦ z.1 • z.2.1) :=
      contMDiff_fst.smul contMDiff_snd.fst
    have hmoveY : ContMDiff J I ∞ (fun z : G × (M × M) ↦ z.1 • z.2.2) :=
      contMDiff_fst.smul contMDiff_snd.snd
    have hU : IsOpen U := (f.open_baseSet.preimage continuous_snd.fst).inter
      ((e.open_baseSet.preimage continuous_snd.snd).inter
        ((k.open_baseSet.preimage hmoveX.continuous).inter
          (d.open_baseSet.preimage hmoveY.continuous)))
    have hpU : p ∈ U := ⟨hp.2.1, hp.2.2, mem_baseSet_trivializationAt _ _ _,
      mem_baseSet_trivializationAt _ _ _⟩
    let A (z : G × (M × M)) := (k.continuousLinearMapAt ℂ (z.1 • z.2.1)).comp
      ((σF.linearMap z.1 z.2.1).toContinuousLinearMap.comp (f.symmL ℂ z.2.1))
    let B (z : G × (M × M)) := (d.continuousLinearMapAt ℂ (z.1 • z.2.2)).comp
      ((σE.linearMap z.1 z.2.2).toContinuousLinearMap.comp (e.symmL ℂ z.2.2))
    have hA : ContMDiffOn J
        𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ A U :=
      (σF.contMDiffOn_frameMap IG hσF f k).comp
        (contMDiff_fst.prodMk contMDiff_snd.fst).contMDiffOn
        (fun z hz ↦ ⟨hz.1, hz.2.2.1⟩)
    have hB : ContMDiffOn J
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞ B U :=
      (σE.contMDiffOn_frameMap IG hσE e d).comp
        (contMDiff_fst.prodMk contMDiff_snd.snd).contMDiffOn
        (fun z hz ↦ ⟨hz.2.1, hz.2.2.2⟩)
    let T (z : G × (M × M)) (hz : z ∈ U) :
        EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
      (((f.linearEquivAt ℂ z.2.1 hz.1).symm.trans (C z.1 z.2.1)).trans
        (k.linearEquivAt ℂ (z.1 • z.2.1) hz.2.2.1)).toContinuousLinearEquiv
    have hT (z : G × (M × M)) (hz : z ∈ U) : (T z hz).toContinuousLinearMap = A z := by
      apply ContinuousLinearMap.ext
      intro v
      simp [T, A, C, f.symmL_apply hz.1,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.linearEquivAt_apply,
        k.continuousLinearMapAt_apply_of_mem ℂ hz.2.2.1]
    have hinversion := (contDiffAt_map_inverse (n := ∞) (T p hpU)).restrict_scalars ℝ
    rw [hT p hpU] at hinversion
    have hinv := hinversion.comp_contMDiffAt (hA.contMDiffAt (hU.mem_nhds hpU))
    have hK := (K.isSmooth d k).comp (hmoveX.prodMk hmoveY).contMDiffOn
      (s := U) (fun z hz ↦ ⟨hz.2.2.1, hz.2.2.2⟩)
    have hcomp : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1.comp z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    have hcomp' : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ↦ z.1.comp z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    have hright := hcomp'.comp_contMDiffAt
      ((hK.contMDiffAt (hU.mem_nhds hpU)).prodMk_space
        (hB.contMDiffAt (hU.mem_nhds hpU)))
    have hlocal := hcomp.comp_contMDiffAt (hinv.prodMk_space hright)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds hpU] with z hz
    change kernelInFrames E F (L z.1) e f z.2 =
      (A z).inverse.comp ((kernelInFrames E F K.toFun d k
        (z.1 • z.2.1, z.1 • z.2.2)).comp (B z))
    rw [← hT z hz, ContinuousLinearMap.inverse_equiv]
    apply ContinuousLinearMap.ext
    intro v
    simp [kernelInFrames, L, T, B, ContinuousLinearMap.comp_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply, d.symmL_apply hz.2.2.2,
      f.continuousLinearMapAt_apply_of_mem ℂ hz.1,
      d.continuousLinearMapAt_apply_of_mem ℂ hz.2.2.2,
      k.continuousLinearMapAt_apply_of_mem ℂ hz.2.2.1,
      d.symm_apply_apply_mk hz.2.2.2, k.symm_apply_apply_mk hz.2.2.1]
  let B (g : G) (x y : M) : E y →L[ℂ] F x := (R g y : ℂ) • L g x y
  have hfamily
      (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q))
        (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f] :
      ContMDiffOn J
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
        (fun p : G × (M × M) ↦ kernelInFrames E F (B p.1) e f p.2)
        (Set.univ ×ˢ (f.baseSet ×ˢ e.baseSet)) := by
    have hscalar : ContMDiff J 𝓘(ℝ, ℂ) ∞
        (fun p : G × (M × M) ↦ (R p.1 p.2.2 : ℂ)) :=
      Complex.ofRealCLM.contMDiff.comp (hR.comp (contMDiff_fst.prodMk contMDiff_snd.snd))
    have hsmul : ContDiff ℝ ∞ (fun z : ℂ ×
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1 • z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
    apply (hsmul.contMDiff.comp_contMDiffOn
      (hscalar.contMDiffOn.prodMk_space (hL e f))).congr
    intro p _
    simp only [kernelInFrames, B, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
    rfl
  let K' (g : G) : SmoothKernel (n := n) (r := r) (q := q) E F := {
    toFun := B g
    isSmooth := by
      intro e f _ _
      exact (hfamily e f).comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn
        (fun z hz ↦ ⟨Set.mem_univ g, hz⟩) }
  -- The density and the base change identify the same actual smooth-section operator.
  have hoperator (g : G) (u : smoothSections (n := n) (r := r) E) (x : M) :
      ((K' g).toLinearMap μ u).val x =
        ((σF.smoothSectionRepresentation IG hσF g⁻¹)
          (K.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE g) u))).val x := by
    let v := σE.smoothSectionRepresentation IG hσE g u
    let D := (C g x).symm.toContinuousLinearEquiv
    let ν := Measure.map (Diffeomorph.smul (M := M) IG I ∞ g).symm μ
    have hinput (y : M) :
        K.toFun (g • x) (g • (g⁻¹ • y))
          (σE.linearMap g (g⁻¹ • y) (u.val (g⁻¹ • y))) =
            K.toFun (g • x) y (v.val y) := by
      have ht := σE.mk_sectionLinearMap g u.val y
      change (⟨y, v.val y⟩ : TotalSpace Unit E) =
        ⟨g • (g⁻¹ • y), σE.linearMap g (g⁻¹ • y) (u.val (g⁻¹ • y))⟩ at ht
      exact congrArg (fun z : TotalSpace Unit E ↦ K.toFun (g • x) z.proj z.snd) ht.symm
    have houtput (s : ∀ y, F y) : D (s (g • x)) = σF.sectionLinearMap g⁻¹ s x := by
      apply TotalSpace.mk_injective (F := Unit) x
      apply (MulAction.injective g)
      change (⟨g • x, C g x ((C g x).symm (s (g • x)))⟩ : TotalSpace Unit F) = _
      rw [LinearEquiv.apply_symm_apply]
      have ht := σF.mk_sectionLinearMap g⁻¹ s x
      change (⟨x, σF.sectionLinearMap g⁻¹ s x⟩ : TotalSpace Unit F) =
        g⁻¹ • (⟨(g⁻¹)⁻¹ • x, s ((g⁻¹)⁻¹ • x)⟩ : TotalSpace Unit F) at ht
      rw [inv_inv] at ht
      rw [ht]
      exact (smul_inv_smul g _).symm
    change (∫ y, (R g y : ℂ) • L g x y (u.val y) ∂μ) =
      σF.sectionLinearMap g⁻¹ (K.toLinearMap μ v).val x
    have hRg : Measurable (R g) :=
      (hR.comp (contMDiff_const.prodMk contMDiff_id)).continuous.measurable
    calc
      _ = ∫ y, L g x y (u.val y) ∂ν := by
        rw [show ν = μ.withDensity (fun y ↦ ENNReal.ofReal (R g y)) from hRmeasure g,
          integral_withDensity_eq_integral_toReal_smul
            hRg.ennreal_ofReal
            (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
        apply integral_congr_ae
        filter_upwards with y
        rw [ENNReal.toReal_ofReal (hRpos g y).le]
        exact Complex.coe_smul _ _
      _ = ∫ y, L g x (g⁻¹ • y) (u.val (g⁻¹ • y)) ∂μ :=
        integral_map_equiv (Homeomorph.smul g⁻¹).toMeasurableEquiv _
      _ = ∫ y, D (K.toFun (g • x) y (v.val y)) ∂μ := by
        apply integral_congr_ae
        filter_upwards with y
        exact congrArg D (hinput y)
      _ = D (K.apply μ v (g • x)) := D.integral_comp_comm _
      _ = _ := houtput (K.toLinearMap μ v).val
  let η := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let ζ := Measure.map (MeasurableEquiv.inv G) η
  obtain ⟨Kbar, hKbar⟩ := SmoothKernel.exists_weighted_integral (μ := μ) IG ζ K'
    hfamily (fun g ↦ w g⁻¹) (hw.comp continuous_inv)
  refine ⟨Kbar, ?_⟩
  intro u x
  rw [hKbar]
  calc
    _ = ∫ g, w g⁻¹ • ((σF.smoothSectionRepresentation IG hσF g⁻¹)
        (K.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE (g⁻¹)⁻¹) u))).val x ∂ζ := by
      apply integral_congr_ae
      filter_upwards with g
      rw [inv_inv, hoperator]
    _ = _ := by
      have hchange := integral_map_equiv (MeasurableEquiv.inv G)
        (fun g ↦ w g⁻¹ • ((σF.smoothSectionRepresentation IG hσF g⁻¹)
          (K.toLinearMap μ ((σE.smoothSectionRepresentation IG hσE (g⁻¹)⁻¹) u))).val x)
        (μ := η)
      have hinverse (g : G) : MeasurableEquiv.inv G g = g⁻¹ := rfl
      simpa only [hinverse, inv_inv] using hchange

end AtiyahSinger
