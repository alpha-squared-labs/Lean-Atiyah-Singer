/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ExternalTensorL2Density
public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Analysis.HilbertTensorOperator
public import AtiyahSinger.Geometry.ExternalTensorBundle
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Geometric L2 sections as the completed tensor of the original factor spaces

Public module ID: M0614.

The specified product measure and tensor metric give the actual external
tensor bundle its integral Hilbert space. Its unitary comparison with the
completed Hilbert tensor product is fixed on every original pair of smooth
sections. The comparison is derived from Fubini and density, never supplied
as geometric input. No auxiliary fiber norm, manifold atlas, product measure,
or tensor-chart witness is independently reselected.

Sources: SG III.13.5, equations (13.12)--(13.14), pp.249--250, uses this
geometric tensor interpretation. The completion and density argument below
is the standard functional-analytic supplement making that interpretation
explicit. Its conclusion concerns L2 only; identification of the unbounded
operator domain with geometric H1 is a separate theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff TensorProduct

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [hTM : T2Space M] [hTN : T2Space N]
  [hSCM : SecondCountableTopology M] [hSCN : SecondCountableTopology N]
  [MeasurableSpace M] [hBM : BorelSpace M]
  [MeasurableSpace N] [hBN : BorelSpace N]
  (μ : Measure M) (ν : Measure N)
  [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := m) ν]

include hM hN hTM hTN hSCM hSCN hBM hBN hμ hν

-- Keep the original manifold assumptions while the local measure argument needs only charts.
set_option linter.unusedSectionVars false in
/-- The actual product of the two smooth positive measures is smooth in the fixed product atlas. -/
theorem isSmoothPositiveMeasure_prod :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    IsSmoothPositiveMeasure (n := n + m) (μ.prod ν) := by
  /- Use the original positive chart densities to obtain sigma finiteness, then
  multiply them on chart products. The specified coordinate concatenation is
  volume preserving, so transporting this density gives the required formula
  in every chart of the fixed product atlas, including zero-dimensional factors. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let W := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let e : Z ≃L[ℝ] V × W := EuclideanSpace.finAddEquivProd
  -- Bounded densities on small coordinate balls give local finiteness in each factor.
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
  let : SigmaFinite μ := inferInstance
  let : IsLocallyFiniteMeasure ν := by
    constructor
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin m)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hcx : c x ∈ c.target := c.map_source hx
    obtain ⟨w, hw, hwpos, hmap⟩ := hν.exists_smooth_density c (chart_mem_atlas _ x)
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
    have heq : ν U = ((volume.restrict c.target).withDensity
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
  let : SigmaFinite ν := inferInstance
  -- Every selected product chart is an original chart pair followed by e.symm.
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  constructor
  rintro c ⟨a, ha, b, hb, rfl⟩
  change b ∈ {e.symm.toHomeomorph.toOpenPartialHomeomorph} at hb
  obtain rfl := Set.mem_singleton_iff.mp hb
  rcases ha with ⟨c, hc, d, hd, rfl⟩
  obtain ⟨u, hu, hupos, hcu⟩ := hμ.exists_smooth_density c hc
  obtain ⟨v, hv, hvpos, hdv⟩ := hν.exists_smooth_density d hd
  have ht : (c.prod d ≫ₕ e.symm.toHomeomorph.toOpenPartialHomeomorph).target =
      e ⁻¹' (c.target ×ˢ d.target) := by
    simp only [mfld_simps]
    rfl
  have hs : (c.prod d ≫ₕ e.symm.toHomeomorph.toOpenPartialHomeomorph).source =
      c.source ×ˢ d.source := by
    simp only [mfld_simps]
  -- The density is the product of the original densities in the fixed concatenated coordinates.
  have hw : ContDiffOn ℝ ∞ (fun z ↦ u (e z).1 * v (e z).2)
      (e ⁻¹' (c.target ×ˢ d.target)) := by
    apply ContDiffOn.mul
    · exact hu.comp (e.contDiff.fst.contDiffOn) (fun _ hz ↦ hz.1)
    · exact hv.comp (e.contDiff.snd.contDiffOn) (fun _ hz ↦ hz.2)
  refine ⟨fun z ↦ u (e z).1 * v (e z).2, ht ▸ hw, ?_, ?_⟩
  · intro z hz
    rw [ht] at hz
    exact mul_pos (hupos _ hz.1) (hvpos _ hz.2)
  · -- Coordinate reindexing and the L2 product identification both preserve volume.
    have he : MeasurePreserving e := by
      exact (WithLp.volume_preserving_ofLp V W).comp
        ((LinearIsometryEquiv.measurePreserving
          (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin m ↦ ℝ))).comp
          (LinearIsometryEquiv.measurePreserving
            (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm)))
    have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv := he
    have hrestr := (he'.restrict_preimage
      (c.open_target.measurableSet.prod d.open_target.measurableSet)).symm
    -- Fubini identifies the pushforward by the pair of original restricted charts.
    have hcm := c.continuousOn.aemeasurable (μ := μ) c.open_source.measurableSet
    have hdm := d.continuousOn.aemeasurable (μ := ν) d.open_source.measurableSet
    have hup := hu.continuousOn.aemeasurable (μ := volume) c.open_target.measurableSet
    have hvp := hv.continuousOn.aemeasurable (μ := volume) d.open_target.measurableSet
    have hp := Measure.map_prod_map_of_aemeasurable _ _ hcm hdm
    rw [hcu, hdv, prod_withDensity₀ hup.ennreal_ofReal hvp.ennreal_ofReal,
      Measure.prod_restrict, Measure.prod_restrict] at hp
    have hprodmeas : AEMeasurable (Prod.map c d)
        ((μ.prod ν).restrict (c.source ×ˢ d.source)) := by
      rw [← Measure.prod_restrict]
      exact hcm.prodMap hdm
    rw [hs, ht]
    change Measure.map (e.symm ∘ Prod.map c d) _ = _
    rw [← (e.symm.continuous.measurable.aemeasurable.map_map_of_aemeasurable hprodmeas),
      ← hp]
    -- Transport the weighted measure through the same volume-preserving concatenation.
    ext A hA
    rw [Measure.map_apply e.symm.continuous.measurable hA,
      withDensity_apply _ (hA.preimage e.symm.continuous.measurable), withDensity_apply _ hA]
    calc
      _ = ∫⁻ p in e.symm ⁻¹' A,
          ENNReal.ofReal (u (e (e.symm p)).1 * v (e (e.symm p)).2)
            ∂(volume.restrict (c.target ×ˢ d.target)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_of_ae
          (ae_restrict_mem (c.open_target.measurableSet.prod d.open_target.measurableSet))]
          with p hp
        simp only [ContinuousLinearEquiv.apply_symm_apply,
          ENNReal.ofReal_mul (hupos _ hp.1).le]
      _ = _ := hrestr.setLIntegral_comp_preimage_emb
        e.symm.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun z ↦ ENNReal.ofReal (u (e z).1 * v (e z).2)) A


variable {r s : ℕ} {E : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := m) (r := s) F]
  [hCM : CompactSpace M] [hCN : CompactSpace N]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := m) (r := s) F)

include hE hF hCM hCN

/-- Fubini and smooth density identify the completed tensor with the actual product-bundle L2. -/
theorem existsUnique_externalTensorL2Equiv :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    ∃! U : HilbertTensorProduct (h.L2SectionSpace μ) (k.L2SectionSpace ν) ≃ₗᵢ[ℂ]
        (externalTensorMetric h k).L2SectionSpace (μ.prod ν),
      ∀ (u : smoothSections (n := n) (r := r) E)
        (v : smoothSections (n := m) (r := s) F),
        U ((UniformSpace.Completion.toComplL
          (S := ℂ) (α := h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν))
            (h.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v)) =
          (externalTensorMetric h k).smoothToL2 (μ.prod ν)
            (externalTensorSection E F u v) := by
  /- Stage 1: on pairs of pure smooth sections, the tensor metric pairing is
  the product of the two given scalar pairings. Fubini for the specified
  finite smooth measures identifies its integral with the Hilbert tensor
  inner product. Sesquilinearity extends this identity to all finite sums,
  so the actual pointwise tensor map is a well-defined linear isometry there.
  Stage 2: smooth sections are dense in each original integral completion;
  their algebraic pure tensors are consequently dense in the completed Hilbert
  tensor product. Extend the displayed isometry uniquely to that completion.
  Stage 3: the original factor frames, weighted by their partition functions,
  give a finite decomposition of every smooth product section; positive sums
  of squared weights normalize its global smooth coefficients. Complex
  Stone-Weierstrass approximates these coefficients uniformly by separated
  smooth products. The original Hermitian L2 multiplication bound transfers
  this approximation to sections, proving density in the geometric completion.
  Thus the geometric image is dense. A complete isometric image is closed,
  hence equals the entire original product-bundle integral completion.
  Stage 4: the specified values on dense pure smooth tensors determine the
  continuous extension uniquely. Empty bases and zero-rank fibers give zero
  Hilbert spaces and are included. No H1-domain assertion follows merely from
  this L2 unitary, and no other metric or product density is silently chosen. -/
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
  let := externalTensorFiberNormedSpace (r := r) (s := s) E F
  let := externalTensorTopology (r := r) (s := s) E F
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
  let := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : IsFiniteMeasure ν := isFiniteMeasure_of_smoothPositiveMeasure (n := m) ν
  let g := externalTensorMetric h k
  let SE := smoothSections (n := n) (r := r) E
  let SF := smoothSections (n := m) (r := s) F
  let H := HilbertTensorProduct (h.L2SectionSpace μ) (k.L2SectionSpace ν)
  let K := g.L2SectionSpace (μ.prod ν)
  -- The algebraic tensor map uses the original pointwise tensor section, not a new bundle model.
  let B : SE →ₗ[ℂ] SF →ₗ[ℂ]
      smoothSections (n := n + m) (r := r * s) (externalTensorFiber E F) :=
    LinearMap.mk₂ ℂ (fun u v ↦ externalTensorSection E F u v)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.add_tmul _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact (TensorProduct.smul_tmul' _ _ _).symm)
      (by
        intro u v w
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_add _ _ _)
      (by
        intro c u v
        apply Subtype.ext
        funext z
        exact TensorProduct.tmul_smul _ _ _)
  let T : SE ⊗[ℂ] SF →ₗ[ℂ] K :=
    (g.smoothToL2 (μ.prod ν)).comp (TensorProduct.lift B)
  let J : SE ⊗[ℂ] SF →ₗ[ℂ] H :=
    (UniformSpace.Completion.toComplL (S := ℂ)
      (α := h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν)).toLinearMap.comp
        (TensorProduct.map (h.smoothToL2 μ) (k.smoothToL2 ν))
  have hT (u : SE) (v : SF) : T (u ⊗ₜ[ℂ] v) =
      g.smoothToL2 (μ.prod ν) (externalTensorSection E F u v) := rfl
  have hJ (u : SE) (v : SF) : J (u ⊗ₜ[ℂ] v) =
      ((h.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v :
        h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν) : H) := rfl
  -- Fubini identifies pairings on pure tensors for exactly the given measures and metric.
  have hpure (u u' : SE) (v v' : SF) :
      inner ℂ (T (u ⊗ₜ[ℂ] v)) (T (u' ⊗ₜ[ℂ] v')) =
        inner ℂ (J (u ⊗ₜ[ℂ] v)) (J (u' ⊗ₜ[ℂ] v')) := by
    rw [hT, hT, hJ, hJ, g.inner_smoothToL2, UniformSpace.Completion.inner_coe,
      TensorProduct.inner_tmul, h.inner_smoothToL2, k.inner_smoothToL2]
    change (∫ z : M × N,
      (externalTensorMetric h k).pairing z (u.val z.1 ⊗ₜ[ℂ] v.val z.2)
        (u'.val z.1 ⊗ₜ[ℂ] v'.val z.2) ∂μ.prod ν) =
      (∫ x, h.pairing x (u.val x) (u'.val x) ∂μ) *
        ∫ y, k.pairing y (v.val y) (v'.val y) ∂ν
    simp_rw [externalTensorMetric_pairing]
    exact integral_prod_mul (μ := μ) (ν := ν) (L := ℂ)
      (fun x ↦ h.pairing x (u.val x) (u'.val x))
      (fun y ↦ k.pairing y (v.val y) (v'.val y))
  have hinner (x y : SE ⊗[ℂ] SF) : inner ℂ (T x) (T y) = inner ℂ (J x) (J y) := by
    induction x using TensorProduct.inductionOn with
    | tmul u v =>
      induction y using TensorProduct.inductionOn with
      | tmul u' v' => exact hpure u u' v v'
      | add x y hx hy =>
        simp only [map_add]
        exact (inner_add_right (T (u ⊗ₜ[ℂ] v)) (T x) (T y)).trans
          ((congrArg₂ (· + ·) hx hy).trans
            (inner_add_right (J (u ⊗ₜ[ℂ] v)) (J x) (J y)).symm)
    | add x y hx hy =>
      simp only [map_add]
      exact (inner_add_left (T x) (T y) (T _)).trans
        ((congrArg₂ (· + ·) hx hy).trans (inner_add_left (J x) (J y) (J _)).symm)
  have hnorm (x : SE ⊗[ℂ] SF) : ‖T x‖ = ‖J x‖ := by
    have hi := congrArg Complex.re (hinner x x)
    apply (sq_eq_sq₀ (norm_nonneg (T x)) (norm_nonneg (J x))).mp
    have hk : (inner ℂ (T x) (T x)).re = ‖T x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (T x)
    have hh : (inner ℂ (J x) (J x)).re = ‖J x‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) (J x)
    exact hk.symm.trans (hi.trans hh)
  -- Density of the original smooth factors gives a dense algebraic tensor inclusion.
  have hJdense : DenseRange J := by
    have hd := dense_span_hilbertTensorProduct
      (Set.range (h.smoothToL2 μ)) (Set.range (k.smoothToL2 ν))
      (h.denseRange_smoothToL2 μ) (k.denseRange_smoothToL2 ν)
    apply hd.mono
    change _ ≤ LinearMap.range J
    apply Submodule.span_le.mpr
    rintro z ⟨⟨u, v⟩, rfl⟩
    obtain ⟨u', hu⟩ := u.property
    obtain ⟨v', hv⟩ := v.property
    refine ⟨(u' : SE) ⊗ₜ[ℂ] (v' : SF), ?_⟩
    rw [hJ, hu, hv]
  -- The geometric density proof uses finite weighted factor frames and uniform approximation.
  have hTdense : DenseRange T := by
    have hd := dense_span_externalTensorL2 (E := E) (F := F) (μ.prod ν) g
    apply hd.mono
    change _ ≤ LinearMap.range T
    apply Submodule.span_le.mpr
    rintro z ⟨⟨u, v⟩, rfl⟩
    exact ⟨u ⊗ₜ[ℂ] v, hT u v⟩
  let V : H →ₗᵢ[ℂ] K := T.extendOfIsometry hJdense hnorm
  have hV (z : SE ⊗[ℂ] SF) : V (J z) = T z := T.extendOfIsometry_eq hJdense hnorm z
  have hVdense : DenseRange V := by
    apply hTdense.mono
    rintro z ⟨x, rfl⟩
    exact ⟨J x, hV x⟩
  have hsurj : Function.Surjective V := by
    have hc : IsClosed (Set.range V) := V.isometry.isClosedEmbedding.isClosed_range
    apply Set.range_eq_univ.mp
    rw [← hc.closure_eq]
    exact hVdense.closure_range
  let U : H ≃ₗᵢ[ℂ] K := LinearIsometryEquiv.ofSurjective V hsurj
  have hU (u : SE) (v : SF) : U (J (u ⊗ₜ[ℂ] v)) = T (u ⊗ₜ[ℂ] v) := hV _
  refine ⟨U, ?_, ?_⟩
  · intro u v
    exact hU u v
  · -- The values on the same dense smooth pure tensors determine the whole unitary.
    intro W hW
    have hWJ : W.toLinearEquiv.toLinearMap.comp J = T := by
      apply TensorProduct.ext
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      exact hW u v
    have heq : (W : H → K) = U := by
      apply hJdense.equalizer W.continuous U.continuous
      funext z
      change W (J z) = V (J z)
      rw [hV]
      exact LinearMap.congr_fun hWJ z
    exact LinearIsometryEquiv.ext (congrFun heq)

/-- The canonical unitary sends the completed factor tensor into the actual geometric L2 space. -/
def externalTensorL2Equiv :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    HilbertTensorProduct (h.L2SectionSpace μ) (k.L2SectionSpace ν) ≃ₗᵢ[ℂ]
      (externalTensorMetric h k).L2SectionSpace (μ.prod ν) :=
  (existsUnique_externalTensorL2Equiv μ ν h k).exists.choose

/-- The selected unitary retains the actual pointwise tensor of the two original smooth sections. -/
theorem externalTensorL2Equiv_smooth (u : smoothSections (n := n) (r := r) E)
    (v : smoothSections (n := m) (r := s) F) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s) E F
    letI := externalTensorFiberNormedSpace (r := r) (s := s) E F
    letI := externalTensorTopology (r := r) (s := s) E F
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s) E F
    letI := isSmoothPositiveMeasure_prod (n := n) (m := m) μ ν
    externalTensorL2Equiv μ ν h k
        ((UniformSpace.Completion.toComplL
          (S := ℂ) (α := h.L2SectionSpace μ ⊗[ℂ] k.L2SectionSpace ν))
            (h.smoothToL2 μ u ⊗ₜ[ℂ] k.smoothToL2 ν v)) =
      (externalTensorMetric h k).smoothToL2 (μ.prod ν)
        (externalTensorSection E F u v) := by
  /- Read the dense pure-tensor formula from the same witness used to define
  externalTensorL2Equiv. In particular its output is the given geometric
  section in the specified tensor metric and actual product measure. -/
  exact (existsUnique_externalTensorL2Equiv μ ν h k).exists.choose_spec u v

end AtiyahSinger
