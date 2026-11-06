/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSchwartzKernel
public import AtiyahSinger.Analysis.AtlasSobolevLocalization
public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Continuous test pairings in the original atlas

Public module ID: M0258.

Compact cutoff extensions admit uniform finite-frame bounds. Integrability of
fixed compact smooth pairings therefore gives continuous seminorm estimates
for the actual two-test pairings, with arbitrary independent charts and ranks.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set Topology
open scoped ComplexConjugate ContDiff Manifold SchwartzMap

set_option maxSynthPendingDepth 40

/-- A smooth positive chart density is locally finite, without compactness of the base. -/
theorem isLocallyFiniteMeasure_of_smoothPositiveMeasure
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [MeasurableSpace M] [BorelSpace M]
    (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ] : IsLocallyFiniteMeasure μ := by
  constructor
  intro x
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  have hx : x ∈ c.source := mem_chart_source _ x
  have hcx : c x ∈ c.target := c.map_source hx
  obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
  have hwcont : ContinuousAt w (c x) :=
    hw.continuousOn.continuousAt (c.open_target.mem_nhds hcx)
  have hneigh : c.target ∩ {z | w z < w (c x) + 1} ∈ nhds (c x) :=
    Filter.inter_mem (c.open_target.mem_nhds hcx)
      (hwcont.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hneigh
  let U := c ⁻¹' Metric.ball (c x) ε ∩ c.source
  have hUnhds : U ∈ nhds x :=
    Filter.inter_mem ((c.continuousAt hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
      (c.open_source.mem_nhds hx)
  refine ⟨U, hUnhds, ?_⟩
  -- The chart pushforward measures the same restricted neighborhood.
  have heq : μ U = ((volume.restrict c.target).withDensity
      (fun z ↦ ENNReal.ofReal (w z))) (Metric.ball (c x) ε) := by
    rw [← hmap, Measure.map_apply_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableSet_ball,
      Measure.restrict_apply' c.open_source.measurableSet]
  rw [heq, withDensity_apply _ measurableSet_ball]
  have hbound : (∫⁻ z in Metric.ball (c x) ε, ENNReal.ofReal (w z)
      ∂(volume.restrict c.target)) ≤ ENNReal.ofReal (w (c x) + 1) *
        volume (Metric.ball (c x) ε) := by
    calc
      _ ≤ ∫⁻ _z in Metric.ball (c x) ε, ENNReal.ofReal (w (c x) + 1)
          ∂(volume.restrict c.target) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        exact ENNReal.ofReal_le_ofReal (hball hz).2.le
      _ ≤ _ := by
        rw [lintegral_const, Measure.restrict_apply_univ]
        exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)

/-- A product of continuous seminorms controlling a semibilinear scalar form
makes the form jointly continuous. Additivity controls its change at every point. -/
theorem continuous_semibilinear_of_seminorm_bound
    {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] {σ : ℂ →+* ℂ}
    (b : X →ₛₗ[σ] Y →ₗ[ℂ] ℂ) (p : Seminorm ℂ X) (q : Seminorm ℂ Y)
    (hp : Continuous p) (hq : Continuous q) (C : ℝ)
    (hbound : ∀ x y, ‖b x y‖ ≤ C * p x * q y) :
    Continuous (fun z : X × Y ↦ b z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hdiff (z : X × Y) : b z.1 z.2 - b z₀.1 z₀.2 =
      b (z.1 - z₀.1) z.2 + b z₀.1 (z.2 - z₀.2) := by
    simp only [map_sub, LinearMap.sub_apply]
    ring
  have hmajor (z : X × Y) : ‖b z.1 z.2 - b z₀.1 z₀.2‖ ≤
      C * p (z.1 - z₀.1) * q z.2 + C * p z₀.1 * q (z.2 - z₀.2) := by
    rw [hdiff]
    exact (norm_add_le _ _).trans (add_le_add (hbound _ _) (hbound _ _))
  have hlim : Tendsto (fun z : X × Y ↦
      C * p (z.1 - z₀.1) * q z.2 + C * p z₀.1 * q (z.2 - z₀.2)) (𝓝 z₀) (𝓝 0) := by
    have hcont : Continuous (fun z : X × Y ↦
        C * p (z.1 - z₀.1) * q z.2 + C * p z₀.1 * q (z.2 - z₀.2)) :=
      ((hp.comp (continuous_fst.sub continuous_const)).const_mul C |>.mul
        (hq.comp continuous_snd)).add
        ((hq.comp (continuous_snd.sub continuous_const)).const_mul (C * p z₀.1))
    simpa only [sub_self, map_zero, mul_zero, zero_mul, add_zero] using hcont.tendsto z₀
  exact (tendsto_sub_nhds_zero_iff).mp (squeeze_zero_norm hmajor hlim)

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "V" => EuclideanSpace ℝ (Fin n)

omit [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] in
/-- Compact cutoff extension in a fixed frame has a finite smooth section expansion
with the original test coordinates as coefficients. -/
theorem AtlasChartCutoff.exists_expansion_sections
    {c : OpenPartialHomeomorph M V} (D : AtlasChartCutoff A c)
    (hc : c ∈ atlas V M) :
    ∃ u : Fin (A.rank D.frameIndex) → A.smoothSections,
      (∀ i, IsCompact (closure {x : M | (u i).val x ≠ 0})) ∧
      ∀ (v : 𝓢(V, EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) (x : M),
        (D.extend hc v).val x = ∑ i, (v (c x) i) • (u i).val x := by
  classical
  let r := A.rank D.frameIndex
  let ev := EuclideanSpace.equiv (Fin r) ℂ
  obtain ⟨R, hR, hsR⟩ := D.compact_support.isBounded.subset_closedBall_lt 0 (0 : V)
  let β : ContDiffBump (0 : V) :=
    { rIn := R, rOut := R + 1, rIn_pos := hR, rIn_lt_rOut := by linarith }
  let δ : 𝓢(V, ℂ) :=
    (β.hasCompactSupport.comp_left (g := Complex.ofReal) rfl).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp β.contDiff)
  let u (i : Fin r) := D.extend hc (schwartzBasisVector i δ)
  have hδ (z : V) (hz : z ∈ tsupport D.cutoff) : δ z = 1 := by
    change (β z : ℂ) = 1
    rw [β.one_of_mem_closedBall (hsR hz), Complex.ofReal_one]
  have hcompact : IsCompact (c.symm '' tsupport D.cutoff) :=
    D.compact_support.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ (D.support_subset hz).1))
  refine ⟨u, ?_, ?_⟩
  · intro i
    apply hcompact.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hcompact.isClosed
    intro x hx
    by_contra hxK
    exact hx ((D.extendedFunction_properties hc (schwartzBasisVector i δ)).2 x hxK)
  intro v x
  by_cases hx : x ∈ c.source ∩ (A.chart D.frameIndex).baseSet
  · have hu (i : Fin r) : (u i).val x = (D.cutoff (c x) : ℂ) •
        (A.frameLinearEquiv D.frameIndex x hx.2).symm
          (ev (schwartzBasisVector i δ (c x))) := by
      change D.extendedFunction (schwartzBasisVector i δ) x = _
      simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hx, ev, r]
    change D.extendedFunction v x = _
    simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hx]
    by_cases hcut : D.cutoff (c x) = 0
    · simp [hu, hcut]
    have hδx := hδ (c x) (subset_tsupport _ hcut)
    have hval (i : Fin r) : ev (schwartzBasisVector i δ (c x)) = Pi.single i 1 := by
      change ev (δ (c x) • EuclideanSpace.single i 1) = _
      rw [hδx, one_smul]
      rfl
    have hsum := (Pi.basisFun ℂ (Fin r)).sum_repr (ev (v (c x)))
    simp only [Pi.basisFun_repr, Pi.basisFun_apply] at hsum
    rw [← hsum, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hu, hval, map_smul]
    exact smul_comm _ _ _
  · have hzero (w : 𝓢(V, EuclideanSpace ℂ (Fin r))) : (D.extend hc w).val x = 0 := by
      change D.extendedFunction w x = 0
      simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hx]
    simp only [hzero, u, smul_zero, Finset.sum_const_zero]

/-- A smooth bundle multiplier between two independently cut off tests defines
an actual jointly continuous sesquilinear Schwartz pairing. -/
theorem exists_atlasCutoffPairing
    (h : ComplexBundle.ContinuousHermitianMetric F) (hh : B.IsSmoothHermitianMetric h)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (c : ∀ x : M, E x →ₗ[ℂ] F x) (hc : IsSmoothAtlasBundleMap A B c)
    {d e : OpenPartialHomeomorph M V} (hd : d ∈ atlas V M) (he : e ∈ atlas V M)
    (D : AtlasChartCutoff B d) (E' : AtlasChartCutoff A e) :
    ∃ Q : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) →ₗ⋆[ℂ]
        𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) →ₗ[ℂ] ℂ,
      Continuous (fun z : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) ×
          𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) ↦ Q z.1 z.2) ∧ ∀ v w,
        Q v w = ∫ x : M, (h.toCore x).inner ((D.extend hd v).val x)
          (c x ((E'.extend he w).val x)) ∂μ := by
  classical
  let : IsLocallyFiniteMeasure μ := isLocallyFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let X := 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex)))
  let Y := 𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex)))
  let U : X →ₗ[ℂ] B.smoothSections := D.extendLinearMap hd
  let W : Y →ₗ[ℂ] B.smoothSections :=
    (atlasSmoothSectionMap A B c hc).comp (E'.extendLinearMap he)
  -- One compactly supported smooth section makes the original pairing integrable.
  have hsection (u w : B.smoothSections) (hu : IsCompact (closure {x | u.val x ≠ 0})) :
      Integrable (fun x ↦ (h.toCore x).inner (u.val x) (w.val x)) μ := by
    have hsupport : Function.support (fun x ↦ (h.toCore x).inner (u.val x) (w.val x)) ⊆
        {x | u.val x ≠ 0} := by
      intro x hx hz
      apply hx
      change (h.toCore x).inner (u.val x) (w.val x) = 0
      rw [hz]
      let : InnerProductSpace.Core ℂ (F x) := h.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    exact (B.contMDiff_pairing h hh u w).continuous.integrable_of_hasCompactSupport
      (hu.of_isClosed_subset isClosed_closure (closure_mono hsupport))
  have hDcompact : IsCompact (d.symm '' tsupport D.cutoff) :=
    D.compact_support.image_of_continuousOn
      (d.continuousOn_symm.mono (fun z hz ↦ (D.support_subset hz).1))
  have hUcompact (v : X) : IsCompact (closure {x | (U v).val x ≠ 0}) := by
    apply hDcompact.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hDcompact.isClosed
    intro x hx
    by_contra hxK
    exact hx ((D.extendedFunction_properties hd v).2 x hxK)
  let b (x : M) : F x →ₗ⋆[ℂ] F x →ₗ[ℂ] ℂ := by
    let : InnerProductSpace.Core ℂ (F x) := h.toCore x
    exact LinearMap.mk₂'ₛₗ _ _ (h.toCore x).inner
      (h.toCore x).add_left (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_add_right _ _ _)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
  let ℓ (x : M) : X →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ :=
    ((b x).comp ((LinearMap.proj x).comp (B.smoothSections.subtype.comp U))).compl₂
      ((LinearMap.proj x).comp (B.smoothSections.subtype.comp W))
  have hI (v : X) (w : Y) : Integrable (fun x ↦ ℓ x v w) μ :=
    hsection (U v) (W w) (hUcompact v)
  let Q : X →ₗ⋆[ℂ] Y →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ _ _
    (fun v w ↦ ∫ x, ℓ x v w ∂μ)
    (fun v v' w ↦ by
      simp only [map_add, LinearMap.add_apply]
      exact integral_add (hI v w) (hI v' w))
    (fun a v w ↦ by
      simp only [map_smulₛₗ, LinearMap.smul_apply]
      exact integral_smul _ _)
    (fun v w w' ↦ by
      simp only [map_add]
      exact integral_add (hI v w) (hI v w'))
    (fun a v w ↦ by
      simp only [map_smul]
      exact integral_smul _ _)
  obtain ⟨u, hu, huval⟩ := D.exists_expansion_sections B hd
  obtain ⟨v, hv, hvval⟩ := E'.exists_expansion_sections A he
  let k (i : Fin (B.rank D.frameIndex)) (j : Fin (A.rank E'.frameIndex)) (x : M) : ℂ :=
    (h.toCore x).inner ((u i).val x) (c x ((v j).val x))
  have hkI (i j) : Integrable (k i j) μ :=
    hsection (u i) (atlasSmoothSectionMap A B c hc (v j)) (hu i)
  -- Expand both original inverse frames; all fixed matrix coefficients are integrable.
  have hmatrix (f : X) (g : Y) (x : M) : ℓ x f g = ∑ i, ∑ j,
      conj (f (d x) i) * k i j x * g (e x) j := by
    change b x ((D.extend hd f).val x) (c x ((E'.extend he g).val x)) = _
    rw [huval f x, hvval g x]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change g (e x) j * (conj (f (d x) i) * k i j x) = _
    simp only [starRingEnd_apply]
    ring
  let p : Seminorm ℂ X := SchwartzMap.seminorm ℂ 0 0
  let q : Seminorm ℂ Y := SchwartzMap.seminorm ℂ 0 0
  let C : ℝ := ∫ x, ∑ i, ∑ j, ‖k i j x‖ ∂μ
  have hmajorI : Integrable (fun x ↦ ∑ i, ∑ j, ‖k i j x‖) μ :=
    integrable_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ (hkI i j).norm))
  have hnorm (f : X) (g : Y) : ‖Q f g‖ ≤ C * p f * q g := by
    have hf (x : V) (i : Fin (B.rank D.frameIndex)) : ‖f x i‖ ≤ p f := by
      apply (PiLp.norm_apply_le (f x) i).trans
      simpa only [norm_iteratedFDeriv_zero] using
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ f 0 x
    have hg (x : V) (j : Fin (A.rank E'.frameIndex)) : ‖g x j‖ ≤ q g := by
      apply (PiLp.norm_apply_le (g x) j).trans
      simpa only [norm_iteratedFDeriv_zero] using
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℂ g 0 x
    have hpoint (x : M) : ‖ℓ x f g‖ ≤ (∑ i, ∑ j, ‖k i j x‖) * p f * q g := by
      rw [hmatrix]
      calc
        _ ≤ ∑ i, ∑ j, ‖conj (f (d x) i) * k i j x * g (e x) j‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum (fun _ _ ↦ norm_sum_le _ _))
        _ ≤ ∑ i, ∑ j, ‖k i j x‖ * p f * q g := by
          gcongr with i _ j _
          simp only [norm_mul, starRingEnd_apply, norm_star]
          calc
            _ ≤ p f * ‖k i j x‖ * q g := by gcongr; exacts [hf _ _, hg _ _]
            _ = _ := by ring
        _ = _ := by simp only [Finset.sum_mul]
    calc
      _ ≤ ∫ x, ‖ℓ x f g‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, (∑ i, ∑ j, ‖k i j x‖) * p f * q g ∂μ :=
        integral_mono (hI f g).norm ((hmajorI.mul_const _).mul_const _) hpoint
      _ = C * p f * q g := by rw [integral_mul_const, integral_mul_const]
  refine ⟨Q, ?_, fun _ _ ↦ rfl⟩
  exact continuous_semibilinear_of_seminorm_bound Q p q
    ((schwartz_withSeminorms ℂ V _).continuous_seminorm (0, 0))
    ((schwartz_withSeminorms ℂ V _).continuous_seminorm (0, 0)) C hnorm

omit [SecondCountableTopology M] [BorelSpace M] in
/-- Continuous original vector test pairings give the unique atlas kernel, using
scalar conjugation exactly in the first Hermitian slot specified by the kernel. -/
theorem exists_atlasSchwartzKernel_of_pairings
    (h : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (hP : ∀ (c d : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
      (D : AtlasChartCutoff B c) (E' : AtlasChartCutoff A d),
      ∃ Q : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) →ₗ⋆[ℂ]
          𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) →ₗ[ℂ] ℂ,
        Continuous (fun z : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) ×
            𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) ↦ Q z.1 z.2) ∧ ∀ v w,
          Q v w = ∫ x : M, (h.toCore x).inner ((D.extend hc v).val x)
            ((P (E'.extend hd w)).val x) ∂μ) :
    ∃! κ : AtlasSchwartzKernel A B, IsAtlasSchwartzKernel A B h μ P κ := by
  classical
  have hentry (c d : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
      (D : AtlasChartCutoff B c) (E' : AtlasChartCutoff A d)
      (a : Fin (B.rank D.frameIndex)) (b : Fin (A.rank E'.frameIndex)) :
      ∃ K : 𝓢'(V × V, ℂ), ∀ φ ψ : 𝓢(V, ℂ),
        K (schwartzTensor φ ψ) = ∫ x : M, (h.toCore x).inner
          ((D.extend hc (schwartzBasisVector a (schwartzConj φ))).val x)
          ((P (E'.extend hd (schwartzBasisVector b ψ))).val x) ∂μ := by
    obtain ⟨Q, hQ, hQval⟩ := hP c d hc hd D E'
    let R : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, EuclideanSpace ℂ (Fin (A.rank E'.frameIndex))) :=
      SchwartzMap.postcompCLM
        ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single b 1))
    let S : 𝓢(V, ℂ) →L[ℂ] 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) :=
      SchwartzMap.postcompCLM
        ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single a 1))
    let C : 𝓢(V, ℂ) →L[ℝ] 𝓢(V, ℂ) :=
      SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
    let L : 𝓢(V, ℂ) →ₗ⋆[ℂ] 𝓢(V, EuclideanSpace ℂ (Fin (B.rank D.frameIndex))) :=
      { toFun := fun f ↦ S (C f)
        map_add' := fun f g ↦ by rw [map_add, map_add]
        map_smul' := fun c f ↦ by
          apply SchwartzMap.ext
          intro x
          change conj (c * f x) • EuclideanSpace.single a (1 : ℂ) =
            conj c • (conj (f x) • EuclideanSpace.single a (1 : ℂ))
          rw [map_mul, smul_smul] }
    let B₀ : 𝓢(V, ℂ) →ₗ[ℂ] 𝓢(V, ℂ) →ₗ[ℂ] ℂ :=
      (Q.comp L).compl₂ R.toLinearMap
    have hB₀ : Continuous (fun z : 𝓢(V, ℂ) × 𝓢(V, ℂ) ↦ B₀ z.1 z.2) :=
      hQ.comp (((S.continuous.comp C.continuous).comp continuous_fst).prodMk
        (R.continuous.comp continuous_snd))
    obtain ⟨K, hK, _⟩ := existsUnique_temperedKernel B₀ hB₀
    exact ⟨K, fun φ ψ ↦ (hK φ ψ).trans (hQval _ _)⟩
  choose κ hκ using hentry
  refine ⟨κ, hκ, ?_⟩
  intro η hη
  exact IsAtlasSchwartzKernel.unique A B h μ P η κ hη hκ

end AtiyahSinger
