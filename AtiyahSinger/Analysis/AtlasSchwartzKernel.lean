/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.SchwartzKernel
public import AtiyahSinger.Geometry.AtlasChartLocalization
public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import AtiyahSinger.Geometry.AtlasSectionMaps
public import AtiyahSinger.Geometry.HermitianPairing

/-!
# Genuine Schwartz kernels in the original varying-rank bundle charts

Public module ID: M0300.

Each local matrix entry is an actual tempered distribution on two independent
coordinate variables. Its evaluations on tensor tests are specified by the
original section operator, original target Hermitian form and original density.
The output test is conjugated before insertion into the first Hermitian slot;
the resulting kernel is complex linear in both scalar tests.

All pairs of original manifold charts, bundle frames and compact cutoffs are
used. The exact same-section pairing supplies overlap compatibility. Positive
metric and density identify this family with the usual distributional Hom
kernel, retaining its support. The support below is built from actual dsupport
of these distributions, not from the nullspace or section-support predicate.

This is the local distribution representation of the Schwartz kernel theorem
used in SG III.13.4. The bundle-atlas and metric-pairing formulations are explicit
project supplements. There is no compact-base or uniform-rank assumption.
Kernels uniquely determine compact-test actions; no claim identifies arbitrary
algebraic operators on all smooth sections solely from their compact tests.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

local notation "V" => EuclideanSpace ℝ (Fin n)

/-- The scalar Schwartz function placed in one actual coordinate basis direction. -/
def schwartzBasisVector {r : ℕ} (a : Fin r) (φ : 𝓢(V, ℂ)) :
    𝓢(V, EuclideanSpace ℂ (Fin r)) :=
  SchwartzMap.postcompCLM
    ((ContinuousLinearMap.id ℂ ℂ).smulRight (EuclideanSpace.single a 1)) φ

/-- A local distributional matrix in every pair of original cutoff charts. -/
abbrev AtlasSchwartzKernel : Type _ :=
  ∀ (c d : OpenPartialHomeomorph M V),
    c ∈ atlas V M → d ∈ atlas V M →
      (Lo : AtlasChartCutoff B c) → (Li : AtlasChartCutoff A d) →
      Fin (B.rank Lo.frameIndex) → Fin (A.rank Li.frameIndex) → 𝓢'(V × V, ℂ)

/-- The global distributional support read from the actual local two-variable kernels. -/
def atlasSchwartzKernelSupport (κ : AtlasSchwartzKernel A B) : Set (M × M) :=
  closure {z | ∃ (c d : OpenPartialHomeomorph M V)
    (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
    (Lo : AtlasChartCutoff B c) (Li : AtlasChartCutoff A d)
    (a : Fin (B.rank Lo.frameIndex)) (b : Fin (A.rank Li.frameIndex)) (w : V × V),
      w ∈ Distribution.dsupport (κ c d hc hd Lo Li a b) ∧
        w.1 ∈ c.target ∧ w.2 ∈ d.target ∧ z = (c.symm w.1, d.symm w.2)}

/-- Swap the original chart, frame and cutoff pairs and conjugate transpose each actual kernel. -/
def atlasSchwartzKernelAdjoint (κ : AtlasSchwartzKernel A B) : AtlasSchwartzKernel B A :=
  fun c d hc hd Lo Li a b ↦ temperedConjSwap (κ d c hd hc Li Lo b a)

variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [MeasurableSpace M]

/-- The actual kernel pairing for the original section map and specified target metric/density. -/
def IsAtlasSchwartzKernel (hF : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) (κ : AtlasSchwartzKernel A B) : Prop :=
  ∀ (c d : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
    (Lo : AtlasChartCutoff B c) (Li : AtlasChartCutoff A d)
    (a : Fin (B.rank Lo.frameIndex)) (b : Fin (A.rank Li.frameIndex))
    (φ ψ : 𝓢(V, ℂ)),
    κ c d hc hd Lo Li a b (schwartzTensor φ ψ) =
      ∫ x : M, (hF.toCore x).inner
        ((Lo.extend hc (schwartzBasisVector a (schwartzConj φ))).val x)
        ((P (Li.extend hd (schwartzBasisVector b ψ))).val x) ∂μ

/-- The same original operator pairing determines its entire local distribution family uniquely. -/
theorem IsAtlasSchwartzKernel.unique
    (hF : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) (κ η : AtlasSchwartzKernel A B)
    (hκ : IsAtlasSchwartzKernel A B hF μ P κ)
    (hη : IsAtlasSchwartzKernel A B hF μ P η) : κ = η := by
  -- The original operator, metric and measure give the same scalar tensor pairings.
  funext c d hc hd Lo Li a b
  apply temperedKernel_ext
  intro φ ψ
  exact (hκ c d hc hd Lo Li a b φ ψ).trans (hη c d hc hd Lo Li a b φ ψ).symm

variable [SecondCountableTopology M] [BorelSpace M]

set_option linter.unusedSectionVars false in
/-- The local kernel matrices reconstruct the same original pairing on arbitrary vector tests. -/
theorem IsAtlasSchwartzKernel.pairing
    (hF : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    [IsSmoothPositiveMeasure (n := n) μ]
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) (κ : AtlasSchwartzKernel A B)
    (hκ : IsAtlasSchwartzKernel A B hF μ P κ)
    (c d : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
    (Lo : AtlasChartCutoff B c) (Li : AtlasChartCutoff A d)
    (v : 𝓢(V, EuclideanSpace ℂ (Fin (B.rank Lo.frameIndex))))
    (u : 𝓢(V, EuclideanSpace ℂ (Fin (A.rank Li.frameIndex)))) :
    ∑ a : Fin (B.rank Lo.frameIndex), ∑ b : Fin (A.rank Li.frameIndex),
      κ c d hc hd Lo Li a b
        (schwartzTensor
          (schwartzConj (SchwartzMap.postcompCLM (EuclideanSpace.proj a) v))
          (SchwartzMap.postcompCLM (EuclideanSpace.proj b) u)) =
      ∫ x : M, (hF.toCore x).inner
        ((Lo.extend hc v).val x) ((P (Li.extend hd u)).val x) ∂μ := by
  /- Stage 1: expand each finite-dimensional coordinate Schwartz test in
  its own original coordinate basis. The extension maps are complex linear
  and retain the original inverse frames. Apply the defining scalar kernel
  formula to each pair of coordinates, cancelling the two conjugations in
  the output test. Stage 2: sum the original Hermitian pairing using its
  sesquilinearity and P's linearity. Compact cutoff support makes each
  pairing integrable for a smooth positive density in the applications.
  The equality identifies every local expression with the very same
  original-section pairing; in particular overlapping charts cannot supply
  independent kernels or different input/output identifications. -/
  classical
  -- Local finiteness follows from the given smooth density on coordinate balls.
  let hμ : IsSmoothPositiveMeasure (n := n) μ := inferInstance
  let : IsLocallyFiniteMeasure μ := by
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
  -- Reconstruct each test in its own original finite coordinate basis.
  have hexpand {r : ℕ} (w : 𝓢(V, EuclideanSpace ℂ (Fin r))) :
      ∑ a, schwartzBasisVector a (SchwartzMap.postcompCLM (EuclideanSpace.proj a) w) =
        w := by
    ext z j
    simp [schwartzBasisVector, sum_apply, Pi.single_apply]
  have hconj (f : 𝓢(V, ℂ)) : schwartzConj (schwartzConj f) = f := by
    ext x
    change starRingEnd ℂ (starRingEnd ℂ (f x)) = f x
    simp
  let vo (a : Fin (B.rank Lo.frameIndex)) :=
    schwartzBasisVector a (SchwartzMap.postcompCLM (EuclideanSpace.proj a) v)
  let ui (b : Fin (A.rank Li.frameIndex)) :=
    schwartzBasisVector b (SchwartzMap.postcompCLM (EuclideanSpace.proj b) u)
  have hLo : ∑ a, Lo.extend hc (vo a) = Lo.extend hc v := by
    change ∑ a, Lo.extendLinearMap hc (vo a) = _
    rw [← map_sum]
    exact congrArg (Lo.extend hc) (hexpand v)
  have hLi : ∑ b, Li.extend hd (ui b) = Li.extend hd u := by
    change ∑ b, Li.extendLinearMap hd (ui b) = _
    rw [← map_sum]
    exact congrArg (Li.extend hd) (hexpand u)
  -- Each scalar summand is continuous and has the fixed output cutoff support.
  have hint (a : Fin (B.rank Lo.frameIndex)) (b : Fin (A.rank Li.frameIndex)) :
      Integrable (fun x ↦ (hF.toCore x).inner ((Lo.extend hc (vo a)).val x)
        ((P (Li.extend hd (ui b))).val x)) μ := by
    let : TopologicalSpace (TotalSpace Unit (F ×ᵇ F)) := ComplexBundle.sumTopology
    have hcont : Continuous (fun x ↦ (hF.toCore x).inner
        ((Lo.extend hc (vo a)).val x) ((P (Li.extend hd (ui b))).val x)) := by
      have hp : Continuous (fun x ↦ (⟨x,
          ((Lo.extend hc (vo a)).val x, (P (Li.extend hd (ui b))).val x)⟩ :
            TotalSpace Unit (F ×ᵇ F))) := by
        apply continuous_induced_rng.mpr
        exact (B.continuous_section _ (Lo.extend hc (vo a)).property).prodMk
          (B.continuous_section _ (P (Li.extend hd (ui b))).property)
      exact hF.continuous_pairing.comp hp
    apply hcont.integrable_of_hasCompactSupport
    have hK : IsCompact (c.symm '' tsupport Lo.cutoff) :=
      Lo.compact_support.image_of_continuousOn
        (c.continuousOn_symm.mono (fun z hz ↦ (Lo.support_subset hz).1))
    apply hK.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra h
    have hz := (Lo.extendedFunction_properties hc (vo a)).2 x h
    apply hx
    change (hF.toCore x).inner (Lo.extendedFunction (vo a) x) _ = 0
    rw [hz]
    let := hF.toCore x
    exact InnerProductSpace.Core.inner_zero_left _
  -- Evaluate the original scalar kernels, then move the finite sums through the integral.
  simp only [hκ c d hc hd Lo Li, hconj]
  change (∑ a, ∑ b, ∫ x, (hF.toCore x).inner ((Lo.extend hc (vo a)).val x)
    ((P (Li.extend hd (ui b))).val x) ∂μ) = _
  calc
    _ = ∫ x, ∑ a, ∑ b, (hF.toCore x).inner ((Lo.extend hc (vo a)).val x)
        ((P (Li.extend hd (ui b))).val x) ∂μ := by
      rw [integral_finsetSum _ (fun a _ ↦ integrable_finsetSum _ (fun b _ ↦ hint a b))]
      apply Finset.sum_congr rfl
      intro a _
      exact (integral_finsetSum _ (fun b _ ↦ hint a b)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      let := hF.toCore x
      let H : F x →ₗ⋆[ℂ] F x →ₗ[ℂ] ℂ :=
        LinearMap.mk₂'ₛₗ _ _ (hF.toCore x).inner
          (fun a b c ↦ (hF.toCore x).add_left a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
          (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
          (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
      have ho : ∑ a, (Lo.extend hc (vo a)).val x = (Lo.extend hc v).val x := by
        simpa using congrArg (fun w : B.smoothSections ↦ w.val x) hLo
      have hi : ∑ b, (P (Li.extend hd (ui b))).val x = (P (Li.extend hd u)).val x := by
        simpa only [map_sum, Submodule.coe_sum, Finset.sum_apply] using
          congrArg (fun w : A.smoothSections ↦ (P w).val x) hLi
      change (∑ a, ∑ b, H ((Lo.extend hc (vo a)).val x)
        ((P (Li.extend hd (ui b))).val x)) = H _ _
      rw [← ho, ← hi]
      simp only [map_sum, LinearMap.sum_apply]
      exact Finset.sum_comm

set_option linter.unusedSectionVars false in
/-- Actual two-sided section support controls the genuine two-variable distributional kernel. -/
theorem IsAtlasSchwartzKernel.support_subset
    (hF : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    [IsSmoothPositiveMeasure (n := n) μ]
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections) (κ : AtlasSchwartzKernel A B)
    (hκ : IsAtlasSchwartzKernel A B hF μ P κ)
    (L : Set M) (hL : IsClosed L) (hP : HasAtlasSectionOperatorSupport A B L P) :
    atlasSchwartzKernelSupport A B κ ⊆ L ×ˢ L := by
  classical
  -- It suffices to control each original local dsupport before taking the closed union.
  apply closure_minimal ?_ (hL.prod hL)
  rintro _ ⟨c, d, hc, hd, Lo, Li, a, b, w, hw, hwc, hwd, rfl⟩
  constructor
  · by_contra hout
    let s : Set V := c.target ∩ c.symm ⁻¹' Lᶜ
    have hs : IsOpen s :=
      c.continuousOn_symm.isOpen_inter_preimage c.open_target hL.isOpen_compl
    apply (notMem_dsupport_of_tensor_tests (κ c d hc hd Lo Li a b) hs isOpen_univ w
      ⟨⟨hwc, hout⟩, Set.mem_univ _⟩ ?_) hw
    intro φ ψ hφ _
    rw [hκ c d hc hd Lo Li a b φ ψ]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    by_cases hxL : x ∈ L
    · -- On L the localized output test vanishes, by its original chart support.
      have houtput : (Lo.extend hc (schwartzBasisVector a (schwartzConj φ))).val x = 0 := by
        change Lo.extendedFunction _ x = 0
        by_cases hx : x ∈ c.source ∩ (B.chart Lo.frameIndex).baseSet
        · have hφx : φ (c x) = 0 := by
            by_contra hne
            have hxout := (hφ (subset_tsupport φ hne)).2
            change c.symm (c x) ∉ L at hxout
            rw [c.left_inv hx.1] at hxout
            exact hxout hxL
          simp [AtlasChartCutoff.extendedFunction, hx, schwartzBasisVector,
            schwartzConj, SchwartzMap.postcompCLM_apply, hφx]
        · simp [AtlasChartCutoff.extendedFunction, hx]
      rw [houtput]
      let := hF.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    · -- Off L the actual operator output vanishes, with no metric or density inference.
      have houtput : (P (Li.extend hd (schwartzBasisVector b ψ))).val x = 0 := by
        by_contra hne
        exact hxL (hP.1 _ (subset_closure hne))
      rw [houtput]
      let := hF.toCore x
      exact InnerProductSpace.Core.inner_zero_right _
  · by_contra hout
    let t : Set V := d.target ∩ d.symm ⁻¹' Lᶜ
    have ht : IsOpen t :=
      d.continuousOn_symm.isOpen_inter_preimage d.open_target hL.isOpen_compl
    apply (notMem_dsupport_of_tensor_tests (κ c d hc hd Lo Li a b) isOpen_univ ht w
      ⟨Set.mem_univ _, ⟨hwd, hout⟩⟩ ?_) hw
    intro φ ψ _ hψ
    let u := Li.extend hd (schwartzBasisVector b ψ)
    let C : Set M := d.symm '' (tsupport Li.cutoff ∩ tsupport ψ)
    have hC : IsCompact C :=
      (Li.compact_support.inter_right (isClosed_tsupport ψ)).image_of_continuousOn
        (d.continuousOn_symm.mono (fun y hy ↦ (Li.support_subset hy.1).1))
    -- The same inverse-frame extension is supported in a compact set disjoint from L.
    have huC : closure {x | u.val x ≠ 0} ⊆ C := by
      apply closure_minimal ?_ hC.isClosed
      intro x hx
      by_cases hvalid : x ∈ d.source ∩ (A.chart Li.frameIndex).baseSet
      · have hcut : Li.cutoff (d x) ≠ 0 := by
          intro hzero
          apply hx
          change Li.extendedFunction _ x = 0
          simp [AtlasChartCutoff.extendedFunction, hvalid, hzero]
        have htest : ψ (d x) ≠ 0 := by
          intro hzero
          apply hx
          change Li.extendedFunction _ x = 0
          simp [AtlasChartCutoff.extendedFunction, hvalid, schwartzBasisVector,
            SchwartzMap.postcompCLM_apply, hzero]
        exact ⟨d x, ⟨subset_tsupport Li.cutoff hcut, subset_tsupport ψ htest⟩,
          d.left_inv hvalid.1⟩
      · exact (hx (by
          change Li.extendedFunction _ x = 0
          simp [AtlasChartCutoff.extendedFunction, hvalid])).elim
    have hCL : Disjoint C L := by
      apply Set.disjoint_left.mpr
      rintro x ⟨y, hy, rfl⟩ hxL
      exact (hψ hy.2).2 hxL
    have hPu : P u = 0 := hP.2 u (Set.disjoint_of_subset_left huC hCL)
    rw [hκ c d hc hd Lo Li a b φ ψ]
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    change (hF.toCore x).inner _ ((P u).val x) = 0
    rw [hPu]
    change (hF.toCore x).inner _ 0 = 0
    let := hF.toCore x
    exact InnerProductSpace.Core.inner_zero_right _

set_option linter.unusedSectionVars false in
/-- Metric formal adjunction on compact tests gives the actual conjugate-transposed kernel. -/
theorem isAtlasSchwartzKernel_adjoint
    (hE : ComplexBundle.ContinuousHermitianMetric E)
    (hF : ComplexBundle.ContinuousHermitianMetric F) (μ : Measure M)
    [IsSmoothPositiveMeasure (n := n) μ]
    (P : A.smoothSections →ₗ[ℂ] B.smoothSections)
    (Q : B.smoothSections →ₗ[ℂ] A.smoothSections)
    (κ : AtlasSchwartzKernel A B) (hκ : IsAtlasSchwartzKernel A B hF μ P κ)
    (hPQ : ∀ (u : A.smoothSections) (v : B.smoothSections),
      IsCompact (closure {x | u.val x ≠ 0}) →
      IsCompact (closure {x | v.val x ≠ 0}) →
      (∫ x : M, (hF.toCore x).inner ((P u).val x) (v.val x) ∂μ) =
        ∫ x : M, (hE.toCore x).inner (u.val x) ((Q v).val x) ∂μ) :
    IsAtlasSchwartzKernel B A hE μ Q (atlasSchwartzKernelAdjoint A B κ) := by
  /- Stage 1: both cutoff extensions in the defining tensor test are
  actual compactly supported smooth sections of the original two bundles.
  Apply hPQ to these sections with input and output roles reversed.
  Stage 2: Hermitian symmetry and conjugation of the same scalar integral
  exchange the two slots. Test conjugation and variable swap give exactly
  f ↦ conj(κ(conj(f∘swap))), with the original two frame indices exchanged.
  Stage 3: equality on tensor tests identifies the actual transposed
  distributions. Both metrics and the same density are retained throughout;
  in nonunitary frames their Gram factors are already present in the
  original pairings. No inverse for an exterior bundle map is substituted
  for its metric adjoint, and no compact-base assumption is needed. -/
  intro c d hc hd Lo Li a b φ ψ
  -- Both sections use exactly the cutoff, chart and frame from the transposed entry.
  let u := Lo.extend hc (schwartzBasisVector a (schwartzConj φ))
  let v := Li.extend hd (schwartzBasisVector b ψ)
  have hcu : IsCompact (closure {x | u.val x ≠ 0}) := by
    have hK : IsCompact (c.symm '' tsupport Lo.cutoff) :=
      Lo.compact_support.image_of_continuousOn
        (c.continuousOn_symm.mono (fun z hz ↦ (Lo.support_subset hz).1))
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra h
    exact hx ((Lo.extendedFunction_properties hc _).2 x h)
  have hcv : IsCompact (closure {x | v.val x ≠ 0}) := by
    have hK : IsCompact (d.symm '' tsupport Li.cutoff) :=
      Li.compact_support.image_of_continuousOn
        (d.continuousOn_symm.mono (fun z hz ↦ (Li.support_subset hz).1))
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal ?_ hK.isClosed
    intro x hx
    by_contra h
    exact hx ((Li.extendedFunction_properties hd _).2 x h)
  have hconj (f : 𝓢(V, ℂ)) : schwartzConj (schwartzConj f) = f := by
    ext x
    change starRingEnd ℂ (starRingEnd ℂ (f x)) = f x
    simp
  have htensor : schwartzConjSwap (schwartzTensor φ ψ) =
      schwartzTensor (schwartzConj ψ) (schwartzConj φ) := by
    ext z
    change starRingEnd ℂ (schwartzTensor φ ψ z.swap) = _
    simp only [schwartzTensor_apply]
    change starRingEnd ℂ (φ z.2 * ψ z.1) =
      starRingEnd ℂ (ψ z.1) * starRingEnd ℂ (φ z.2)
    rw [map_mul, mul_comm]
  -- Conjugate the scalar kernel pairing, then use Hermitian symmetry and hPQ.
  change starRingEnd ℂ (κ d c hd hc Li Lo b a
    (schwartzConjSwap (schwartzTensor φ ψ))) = _
  rw [htensor, hκ, hconj, ← integral_conj]
  calc
    _ = ∫ x : M, (hF.toCore x).inner ((P u).val x) (v.val x) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      let := hF.toCore x
      exact InnerProductSpace.Core.inner_conj_symm _ _
    _ = _ := hPQ u v hcu hcv

set_option linter.unusedSectionVars false in
/-- Conjugate transposition reverses the two factors of the global genuine kernel support. -/
theorem atlasSchwartzKernelSupport_adjoint (κ : AtlasSchwartzKernel A B) :
    atlasSchwartzKernelSupport B A (atlasSchwartzKernelAdjoint A B κ) =
      Prod.swap '' atlasSchwartzKernelSupport A B κ := by
  /- Apply dsupport_temperedConjSwap to every actual local distribution.
  Swapping the charts, cutoffs and frame indices is an involution on the
  complete indexing family; inverse charts also swap their two coordinates.
  The swap homeomorphism commutes with the union and its closure. Thus the
  assertion is about the actual distributional support of the full family. -/
  -- The swap homeomorphism commutes with taking the closed global support.
  unfold atlasSchwartzKernelSupport
  rw [show Prod.swap = ⇑(Homeomorph.prodComm M M) from rfl,
    (Homeomorph.prodComm M M).image_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨c, d, hc, hd, Lo, Li, a, b, w, hw, hc', hd', rfl⟩
    change w ∈ Distribution.dsupport (temperedConjSwap (κ d c hd hc Li Lo b a)) at hw
    rw [dsupport_temperedConjSwap] at hw
    obtain ⟨w, hw, rfl⟩ := hw
    refine ⟨(d.symm w.1, c.symm w.2), ?_, rfl⟩
    exact ⟨d, c, hd, hc, Li, Lo, b, a, w, hw, hd', hc', rfl⟩
  · rintro ⟨z, ⟨c, d, hc, hd, Lo, Li, a, b, w, hw, hc', hd', rfl⟩, rfl⟩
    refine ⟨d, c, hd, hc, Li, Lo, b, a, w.swap, ?_, hd', hc', rfl⟩
    change w.swap ∈ Distribution.dsupport (temperedConjSwap (κ c d hc hd Lo Li a b))
    rw [dsupport_temperedConjSwap]
    exact ⟨w, hw, rfl⟩

end AtiyahSinger
