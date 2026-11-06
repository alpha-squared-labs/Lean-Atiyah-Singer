/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleFiberScale
public import AtiyahSinger.Geometry.TubularRescaling
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# Rescaling a map in the original vector bundle

Public module ID: M1112.

Conjugating by fiber dilation extends continuously through scale zero when the
map fixes the zero section and its normal derivative there is identity. The
proof works in the selected original bundle chart at the point in question;
the map may move the base point and need not preserve fibers.

The coordinate derivative is used only at that point. Hadamard's formula
controls simultaneous changes of the parameter, base point, and fiber vector.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Set Topology
open scoped ContDiff

variable {EB B F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB] [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]

/-- Conjugation by fiber dilation, extended by the identity at zero scale. -/
def rescaleBundleMap (f : TotalSpace F V → TotalSpace F V)
    (p : ℝ × TotalSpace F V) : TotalSpace F V :=
  if p.1 = 0 then p.2 else
    bundleFiberScale p.1⁻¹ (f (bundleFiberScale p.1 p.2))

/-- Identity normal derivative in the actual chosen chart gives joint continuity at zero scale. -/
theorem continuousAt_rescaleBundleMap_zero (f : TotalSpace F V → TotalSpace F V)
    {U : Set (TotalSpace F V)}
    (hf : ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ f U)
    (hU : IsOpen U) (hzero : ∀ x : B, f ⟨x, 0⟩ = ⟨x, 0⟩)
    (x : B) (v : V x) (hx : (⟨x, 0⟩ : TotalSpace F V) ∈ U)
    (hnormal :
      let c := extChartAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (⟨x, 0⟩ : TotalSpace F V)
      (fderiv ℝ (fun z : EB × F ↦ (c (f (c.symm z))).2) (c ⟨x, 0⟩)).comp
        (ContinuousLinearMap.inr ℝ EB F) = ContinuousLinearMap.id ℝ F) :
    ContinuousAt (rescaleBundleMap f) (0, (⟨x, v⟩ : TotalSpace F V)) := by
  let I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F)
  let z₀ : TotalSpace F V := ⟨x, 0⟩
  let z : TotalSpace F V := ⟨x, v⟩
  let e := trivializationAt F V x
  let c : OpenPartialHomeomorph (TotalSpace F V) (EB × F) :=
    { toPartialEquiv := extChartAt I z₀
      open_source := isOpen_extChartAt_source z₀
      open_target := isOpen_extChartAt_target z₀
      continuousOn_toFun := continuousOn_extChartAt z₀
      continuousOn_invFun := continuousOn_extChartAt_symm z₀ }
  have hc₀ : z₀ ∈ c.source := mem_extChartAt_source z₀
  -- The original bundle chart has a fiber-saturated source and commutes with dilation.
  have hsrc (a : ℝ) (w : TotalSpace F V) :
      bundleFiberScale a w ∈ c.source ↔ w ∈ c.source := by
    change _ ∈ (extChartAt I z₀).source ↔ _ ∈ (extChartAt I z₀).source
    simp only [extChartAt_source, FiberBundle.chartedSpace_chartAt,
      OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.prod_source,
      OpenPartialHomeomorph.refl_source, mem_inter_iff, mem_preimage, mem_prod,
      mem_univ, and_true, Trivialization.mem_source]
    change ((bundleFiberScale a w).proj ∈ e.baseSet ∧
      (e (bundleFiberScale a w)).1 ∈ (chartAt EB x).source) ↔
        (w.proj ∈ e.baseSet ∧ (e w).1 ∈ (chartAt EB x).source)
    by_cases hw : w.proj ∈ e.baseSet
    · rw [e.coe_fst' (show (bundleFiberScale a w).proj ∈ e.baseSet from hw), e.coe_fst' hw]
      rfl
    · simp [bundleFiberScale, hw]
  have hbase (w : TotalSpace F V) (hw : w ∈ c.source) : w.proj ∈ e.baseSet := by
    change w ∈ (extChartAt I z₀).source at hw
    rw [extChartAt_source, FiberBundle.chartedSpace_chartAt] at hw
    exact e.mem_source.mp hw.1
  have hscale (a : ℝ) (w : TotalSpace F V) (hw : w ∈ c.source) :
      c (bundleFiberScale a w) = ((c w).1, a • (c w).2) := by
    have hw' := hbase w hw
    change extChartAt I z₀ _ = ((extChartAt I z₀ w).1, a • (extChartAt I z₀ w).2)
    dsimp only [I, z₀]
    simp only [FiberBundle.extChartAt, PartialEquiv.trans_apply, PartialEquiv.prod_coe,
      PartialEquiv.refl_coe, id_eq]
    change ((extChartAt 𝓘(ℝ, EB) x) (e (bundleFiberScale a w)).1,
        (e (bundleFiberScale a w)).2) =
      ((extChartAt 𝓘(ℝ, EB) x) (e w).1, a • (e w).2)
    rw [e.coe_fst' (show (bundleFiberScale a w).proj ∈ e.baseSet from hw'), e.coe_fst' hw']
    apply Prod.ext
    · rfl
    · change (e ⟨w.proj, a • w.2⟩).2 = a • (e w).2
      simp only [← e.continuousLinearMapAt_apply_of_mem ℝ hw', map_smul]
  have hcz : z ∈ c.source := (hsrc 0 z).mp (by simpa [bundleFiberScale, z, z₀] using hc₀)
  have hc0 : c z₀ = ((c z).1, 0) := by
    simpa [bundleFiberScale, z, z₀] using hscale 0 z hcz
  let a : EB := (c z).1
  let g : EB × F → EB × F := c ∘ f ∘ c.symm
  let Ω : Set (EB × F) := c.target ∩ c.symm ⁻¹' (U ∩ f ⁻¹' c.source)
  have hΩ : IsOpen Ω := c.symm.isOpen_inter_preimage
    (hf.continuousOn.isOpen_inter_preimage hU c.open_source)
  have haΩ : (a, 0) ∈ Ω := by
    rw [← hc0]
    exact ⟨c.map_source hc₀, by
      simpa only [mem_preimage, mem_inter_iff, c.left_inv hc₀, z₀, hzero x] using
        And.intro hx hc₀⟩
  have hcs : ContMDiffOn I 𝓘(ℝ, EB × F) ∞ c c.source := by
    change ContMDiffOn I 𝓘(ℝ, EB × F) ∞ (extChartAt I z₀) (extChartAt I z₀).source
    simpa only [extChartAt_source] using! (contMDiffOn_extChartAt (I := I) (x := z₀))
  have hci : ContMDiffOn 𝓘(ℝ, EB × F) I ∞ c.symm c.target :=
    contMDiffOn_extChartAt_symm z₀
  have hg : ContDiffOn ℝ ∞ g Ω := by
    apply ContMDiffOn.contDiffOn
    exact hcs.comp (hf.comp (hci.mono (fun _ hp ↦ hp.1)) (fun _ hp ↦ hp.2.1))
      (fun _ hp ↦ hp.2.2)
  -- Choose a local rectangle, whose fiber ball contains every contracted radial segment.
  obtain ⟨W, hW, A, hA, hWA⟩ := mem_nhds_prod_iff.mp (hΩ.mem_nhds haΩ)
  obtain ⟨W', hW'W, hW'o, haW'⟩ := mem_nhds_iff.mp hW
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA
  let s : Set (EB × F) := W' ×ˢ Metric.ball 0 r
  have hs : IsOpen s := hW'o.prod Metric.isOpen_ball
  have hsΩ : s ⊆ Ω := prod_mono hW'W hrA |>.trans hWA
  have has : (a, 0) ∈ s := ⟨haW', by simpa using hr⟩
  have hstar : ∀ w ∈ s, ∀ t ∈ Icc (0 : ℝ) 1, (w.1, t • w.2) ∈ s := by
    intro w hw t ht
    refine ⟨hw.1, ?_⟩
    have hv : ‖w.2‖ < r := by simpa using hw.2
    have ht' : ‖t‖ ≤ 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    simpa only [Metric.mem_ball, dist_zero_right, norm_smul] using
      (mul_le_mul_of_nonneg_right ht' (norm_nonneg w.2)).trans_lt (by simpa using hv)
  have hgzero (b : EB) (hb : (b, 0) ∈ s) : g (b, 0) = (b, 0) := by
    have hb' := hsΩ hb
    have hw := c.map_target hb'.1
    have hzeroVector : bundleFiberScale 0 (c.symm (b, 0)) = c.symm (b, 0) := by
      apply c.injOn ((hsrc _ _).mpr hw) hw
      rw [hscale _ _ hw, c.right_inv hb'.1]
      simp
    change c (f (c.symm (b, 0))) = (b, 0)
    rw [← hzeroVector]
    change c (f ⟨(c.symm (b, 0)).proj, 0 • (c.symm (b, 0)).2⟩) = (b, 0)
    rw [zero_smul, hzero]
    rw [show (⟨(c.symm (b, 0)).proj, 0⟩ : TotalSpace F V) = c.symm (b, 0) by
      simpa only [bundleFiberScale, zero_smul] using hzeroVector]
    exact c.right_inv hb'.1
  have hn : (fderiv ℝ (fun w ↦ (g w).2) (a, 0)).comp
      (ContinuousLinearMap.inr ℝ EB F) = ContinuousLinearMap.id ℝ F := by
    change (fderiv ℝ (fun w ↦ (g w).2) (c z₀)).comp _ = _ at hnormal
    simpa only [hc0] using hnormal
  have hrescale := continuousAt_rescaleAlongFibers_zero g (hg.mono hsΩ) hs hstar hgzero
    a (c z).2 has hn
  have hcoordinates : ContinuousAt (fun p : ℝ × TotalSpace F V ↦ (p.1, c p.2)) (0, z) :=
    continuous_fst.continuousAt.prodMk
      ((c.continuousAt hcz).comp_of_eq continuous_snd.continuousAt rfl)
  have hcrescale := hrescale.comp_of_eq hcoordinates rfl
  have hback := (c.continuousAt_symm (c.map_source hcz)).comp_of_eq hcrescale
    (by simp only [Function.comp_apply, rescaleAlongFibers, ↓reduceIte])
  have hinput : ContinuousAt (fun p : ℝ × TotalSpace F V ↦ bundleFiberScale p.1 p.2) (0, z) :=
    continuous_bundleFiberScale_of_vectorBundle.continuousAt
  have hfinput : ContinuousAt (fun p : ℝ × TotalSpace F V ↦ f (bundleFiberScale p.1 p.2))
      (0, z) := by
    exact (hf.continuousOn.continuousAt (hU.mem_nhds hx)).comp_of_eq hinput
      (by simp only [bundleFiberScale, zero_smul, z])
  -- The two coordinate dilations represent the exact same original bundle map near the point.
  apply hback.congr_of_eventuallyEq
  filter_upwards [continuous_snd.continuousAt (c.open_source.mem_nhds hcz),
    hfinput (by simpa only [bundleFiberScale, zero_smul, z, z₀, hzero] using
      c.open_source.mem_nhds hc₀)] with p hp hfp
  by_cases ht : p.1 = 0
  · simp only [Function.comp_apply, rescaleBundleMap, rescaleAlongFibers, ht, ↓reduceIte]
    exact (c.left_inv hp).symm
  · have hd := (hsrc p.1 p.2).mpr hp
    have hds := c.left_inv hd
    have hcscale := hscale p.1 p.2 hp
    simp only [rescaleBundleMap, ht, ↓reduceIte, Function.comp_apply]
    change bundleFiberScale p.1⁻¹ (f (bundleFiberScale p.1 p.2)) =
      c.symm (rescaleAlongFibers g (p.1, c p.2))
    rw [rescaleAlongFibers, ite_eq_right ht]
    change _ = c.symm ((g ((c p.2).1, p.1 • (c p.2).2)).1,
      p.1⁻¹ • (g ((c p.2).1, p.1 • (c p.2).2)).2)
    rw [← hcscale]
    simp only [g, Function.comp_apply, hds]
    rw [← hscale p.1⁻¹ _ hfp]
    exact (c.left_inv ((hsrc _ _).mpr hfp)).symm

/-- Normalization along the zero section gives continuity on the entire rescaled source. -/
theorem continuousOn_rescaleBundleMap (f : TotalSpace F V → TotalSpace F V)
    {U : Set (TotalSpace F V)}
    (hf : ContMDiffOn (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) ∞ f U)
    (hU : IsOpen U) (hzero : ∀ x : B, f ⟨x, 0⟩ = ⟨x, 0⟩)
    (hnormal : ∀ x : B,
      let c := extChartAt (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (⟨x, 0⟩ : TotalSpace F V)
      (fderiv ℝ (fun z : EB × F ↦ (c (f (c.symm z))).2) (c ⟨x, 0⟩)).comp
        (ContinuousLinearMap.inr ℝ EB F) = ContinuousLinearMap.id ℝ F) :
    ContinuousOn (rescaleBundleMap f) {p | bundleFiberScale p.1 p.2 ∈ U} := by
  intro p hp
  by_cases ht : p.1 = 0
  · rcases p with ⟨t, x, v⟩
    change t = 0 at ht
    subst t
    have hx : (⟨x, 0⟩ : TotalSpace F V) ∈ U := by
      simpa only [mem_ofPred_eq, bundleFiberScale, zero_smul] using hp
    exact (continuousAt_rescaleBundleMap_zero f hf hU hzero x v hx (hnormal x)).continuousWithinAt
  · have hscale : ContinuousAt
        (fun p : ℝ × TotalSpace F V ↦ bundleFiberScale p.1 p.2) p :=
      continuous_bundleFiberScale_of_vectorBundle.continuousAt
    have hvalue : ContinuousAt
        (fun p : ℝ × TotalSpace F V ↦ f (bundleFiberScale p.1 p.2)) p :=
      (hf.continuousOn.continuousAt (hU.mem_nhds hp)).comp_of_eq hscale rfl
    have hR : ContinuousAt (fun p : ℝ × TotalSpace F V ↦
        bundleFiberScale p.1⁻¹ (f (bundleFiberScale p.1 p.2))) p :=
      continuous_bundleFiberScale_of_vectorBundle.continuousAt.comp_of_eq
        ((continuous_fst.continuousAt.inv₀ ht).prodMk hvalue) rfl
    apply ContinuousAt.continuousWithinAt
    apply hR.congr_of_eventuallyEq
    filter_upwards [continuous_fst.continuousAt (isOpen_ne.mem_nhds ht)] with q hq
    change q.1 ≠ 0 at hq
    simp only [rescaleBundleMap, hq, ↓reduceIte]

end AtiyahSinger
