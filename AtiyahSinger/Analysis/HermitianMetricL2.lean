/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.L2Sections
public import AtiyahSinger.Geometry.HermitianMetricComparison
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Integral completions for explicit Hermitian metrics

Public module ID: M0723.

D02/A07: each chosen metric and positive density defines its own tagged space of
smooth sections and integral Hilbert completion. Uniform comparison on a compact
base extends the identity on sections to a canonical bounded equivalence. It is
not generally an isometry. The existing instance-based L² model is compared to
the explicit metric obtained from those same inner products by an isometry.

Sources: Spin Geometry III.2 and III.5, pp.194–195; Husemoller III.9 for the metric
data. The comparison maps are project deductions, not separately numbered source
lemmas. The proofs use the original positive integral forms and native completion
extensions. No fiber norm instance is replaced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  [MeasurableSpace M] (μ : Measure M)

/-- Integrate the explicitly chosen fiber form, with the fixed auxiliary density. -/
def sectionPairing (u v : smoothSections (n := n) (r := r) E) : ℂ :=
  ∫ x, h.pairing x (u.val x) (v.val x) ∂μ

variable [BorelSpace M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hμ

/-- On the compact base every metric pairing of smooth sections is integrable. -/
theorem integrable_pairing (u v : smoothSections (n := n) (r := r) E) :
    Integrable (fun x ↦ h.pairing x (u.val x) (v.val x)) μ := by
  /- Smooth Gram coefficients give a continuous scalar pairing, bounded on the
  compact base. A smooth positive density has finite mass, giving integrability. -/
  classical
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  -- Expand the same scalar pairing in a valid local frame with smooth Gram coefficients.
  have hcont : Continuous (fun x ↦ h.pairing x (u.val x) (v.val x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoord (u : smoothSections (n := n) (r := r) E) (i : Fin r) :
        ContinuousOn (fun y ↦ (e ⟨y, u.val y⟩).2 i) e.baseSet :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).continuous.comp_continuousOn
        (u.property e inferInstance).continuousOn
    have hsum : ContinuousOn (fun y ↦ ∑ i, ∑ j,
        conj ((e ⟨y, u.val y⟩).2 i) * h.gramMatrix e y i j *
          (e ⟨y, v.val y⟩).2 j) e.baseSet := by
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      exact ((hcoord u i).star.mul (h.contMDiffOn_gram e i j).continuousOn).mul (hcoord v j)
    have heval (y : M) (hy : y ∈ e.baseSet) :
        h.pairing y (u.val y) (v.val y) = ∑ i, ∑ j,
          conj ((e ⟨y, u.val y⟩).2 i) * h.gramMatrix e y i j *
            (e ⟨y, v.val y⟩).2 j :=
      h.pairing_eq_gramMatrix e y hy _ _
    exact (hsum.congr heval).continuousAt (e.open_baseSet.mem_nhds hx)
  -- The compact base has finite mass for the original smooth positive measure.
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)


set_option linter.unusedSectionVars false in
/-- Integration preserves Hermitian symmetry. -/
theorem sectionPairing_conj_symm (u v : smoothSections (n := n) (r := r) E) :
    conj (h.sectionPairing μ v u) = h.sectionPairing μ u v := by
  /- Apply pointwise Hermitian symmetry and commute complex conjugation with
  the integrable Bochner integral. -/
  unfold sectionPairing
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ (h.toCore x).conj_inner_symm (u.val x) (v.val x)

/-- The integrated quadratic form is nonnegative. -/
theorem sectionPairing_re_self_nonneg (u : smoothSections (n := n) (r := r) E) :
    0 ≤ (h.sectionPairing μ u u).re := by
  /- Move real part through the integral and integrate pointwise nonnegativity. -/
  have hint := h.integrable_pairing μ u u
  have hre : (h.sectionPairing μ u u).re =
      ∫ x, (h.pairing x (u.val x) (u.val x)).re ∂μ := by
    symm
    simpa only [sectionPairing, RCLike.re_eq_complex_re] using integral_re hint
  rw [hre]
  exact integral_nonneg fun x ↦ (h.toCore x).re_inner_nonneg (u.val x)

/-- The section pairing is additive in its first variable. -/
theorem sectionPairing_add_left (u v w : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ (u + v) w = h.sectionPairing μ u w + h.sectionPairing μ v w := by
  /- Expand fiberwise additivity, then use integrability of both scalar functions
  to split their integral. -/
  change (∫ x, h.pairing x (u.val x + v.val x) (w.val x) ∂μ) = _
  have hadd (x : M) : h.pairing x (u.val x + v.val x) (w.val x) =
      h.pairing x (u.val x) (w.val x) + h.pairing x (v.val x) (w.val x) :=
    (h.toCore x).add_left _ _ _
  simp_rw [hadd]
  exact integral_add (h.integrable_pairing μ u w) (h.integrable_pairing μ v w)


set_option linter.unusedSectionVars false in
/-- The first section variable is conjugate-linear. -/
theorem sectionPairing_smul_left (u v : smoothSections (n := n) (r := r) E) (c : ℂ) :
    h.sectionPairing μ (c • u) v = conj c * h.sectionPairing μ u v := by
  /- Pull the conjugate scalar out of each fiber pairing and then out of the integral. -/
  change (∫ x, h.pairing x (c • u.val x) (v.val x) ∂μ) = _
  have hsmul (x : M) : h.pairing x (c • u.val x) (v.val x) =
      conj c * h.pairing x (u.val x) (v.val x) := (h.toCore x).smul_left _ _ _
  simp_rw [hsmul]
  exact integral_const_mul (conj c) _

/-- A zero integral squared norm forces the smooth section to vanish everywhere. -/
theorem sectionPairing_self_eq_zero_iff (u : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ u u = 0 ↔ u = 0 := by
  /- Positive chart densities give every nonempty open set positive mass. A zero
  integral of the nonnegative self-pairing therefore makes u zero almost
  everywhere. Continuous local frame coordinates upgrade this to pointwise
  zero. The converse follows by integrating the zero fiber pairing. -/
  classical
  -- Strictly positive coordinate densities give every nonempty open set positive mass.
  let : μ.IsOpenPosMeasure := by
    constructor
    intro U hU hUne hzero
    obtain ⟨x, hxU⟩ := hUne
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    let A := c '' (c.source ∩ U)
    have hAopen : IsOpen A := c.isOpen_image_source_inter hU
    have hAnon : A.Nonempty := ⟨c x, ⟨x, ⟨hx, hxU⟩, rfl⟩⟩
    have hAsub : A ⊆ c.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact c.map_source hy.1
    have hpre : c ⁻¹' A ∩ c.source ⊆ U := by
      rintro y ⟨⟨z, hz, hzy⟩, hy⟩
      have heq : z = y := c.injOn hz.1 hy hzy
      simpa only [← heq] using hz.2
    have hAnull : ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) A = 0 := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hAopen.measurableSet,
        Measure.restrict_apply' c.open_source.measurableSet]
      exact measure_mono_null hpre hzero
    -- Positivity makes coordinate Lebesgue measure absolutely continuous in the density.
    have hac : volume.restrict c.target ≪ (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z)) := by
      apply withDensity_absolutelyContinuous'
        (hw.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_pos.mpr (hwpos z hz)).ne'
    have hvol := hac hAnull
    rw [Measure.restrict_apply hAopen.measurableSet,
      Set.inter_eq_left.mpr hAsub] at hvol
    exact hAopen.measure_ne_zero volume hAnon hvol
  constructor
  · intro hzero
    -- A zero integral forces the nonnegative real self-pairing to vanish almost everywhere.
    have hint := h.integrable_pairing μ u u
    have hrealint : Integrable (fun x ↦ (h.pairing x (u.val x) (u.val x)).re) μ :=
      Complex.reCLM.integrable_comp hint
    have hrealzero : (∫ x, (h.pairing x (u.val x) (u.val x)).re ∂μ) = 0 := by
      calc
        _ = (∫ x, h.pairing x (u.val x) (u.val x) ∂μ).re := by
          simpa only [RCLike.re_eq_complex_re] using integral_re hint
        _ = 0 := congrArg Complex.re hzero
    have hae : ∀ᵐ x ∂μ, u.val x = 0 := by
      have hz := (integral_eq_zero_iff_of_nonneg
        (fun x ↦ (h.toCore x).re_inner_nonneg (u.val x)) hrealint).mp hrealzero
      filter_upwards [hz] with x hx
      by_contra hu
      exact (ne_of_gt (h.pairing_self_pos x (u.val x) hu)) hx
    -- Continuous frame coordinates upgrade almost-everywhere zero to pointwise zero.
    apply Subtype.ext
    funext x
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoordae : (fun y ↦ (e ⟨y, u.val y⟩).2) =ᵐ[μ.restrict e.baseSet]
        (fun _ ↦ (0 : EuclideanSpace ℂ (Fin r))) := by
      filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem e.open_baseSet.measurableSet]
        with y hy hye
      rw [hy, ← e.continuousLinearMapAt_apply_of_mem ℂ hye, map_zero]
    have hcoordzero := Measure.eqOn_open_of_ae_eq hcoordae e.open_baseSet
      (u.property e inferInstance).continuousOn continuousOn_const hx
    change u.val x = 0
    apply (e.continuousLinearEquivAt ℂ x hx).injective
    simpa only [map_zero, Trivialization.continuousLinearEquivAt_apply] using hcoordzero
  · rintro rfl
    have hz (x : M) : h.pairing x 0 0 = 0 := by
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      exact InnerProductSpace.Core.inner_zero_left _
    simp only [sectionPairing]
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall hz)


set_option linter.unusedSectionVars false in
/-- The integrated change formula keeps the density fixed. -/
theorem sectionPairing_change (k : SmoothHermitianMetric (n := n) (r := r) E)
    (u v : smoothSections (n := n) (r := r) E) :
    h.sectionPairing μ u (h.changeSections k v) = k.sectionPairing μ u v := by
  /- Integrate h(u,Bv)=k(u,v); the section change has exactly those pointwise values. -/
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  change h.pairing x (u.val x) ((h.changeSections k v).val x) = _
  rw [h.changeSections_apply]
  exact h.pairing_change k x (u.val x) (v.val x)

/-- Smooth sections tagged by both the explicit metric and the integration measure. -/
def SmoothL2Section (_h : SmoothHermitianMetric (n := n) (r := r) E)
    (_μ : Measure M) : Type _ := smoothSections (n := n) (r := r) E

/-- The usual section addition on the tagged carrier. -/
@[instance_reducible]
def smoothL2SectionAddCommGroup : AddCommGroup (h.SmoothL2Section μ) :=
  inferInstanceAs (AddCommGroup (smoothSections (n := n) (r := r) E))

attribute [instance] smoothL2SectionAddCommGroup

/-- The usual complex scalar multiplication on the tagged carrier. -/
@[instance_reducible]
def smoothL2SectionModule : Module ℂ (h.SmoothL2Section μ) :=
  inferInstanceAs (Module ℂ (smoothSections (n := n) (r := r) E))

attribute [instance] smoothL2SectionModule

/-- The integral pairing gives a positive definite pre-Hilbert structure. -/
@[instance_reducible]
def smoothL2SectionCore : InnerProductSpace.Core ℂ (h.SmoothL2Section μ) where
  inner := h.sectionPairing μ
  conj_inner_symm := h.sectionPairing_conj_symm μ
  re_inner_nonneg := h.sectionPairing_re_self_nonneg μ
  add_left := h.sectionPairing_add_left μ
  smul_left := h.sectionPairing_smul_left μ
  definite := fun u hu ↦ (h.sectionPairing_self_eq_zero_iff μ u).mp hu

/-- The integral norm is installed only on the new metric-tagged section type. -/
@[instance_reducible]
def smoothL2SectionNormedAddCommGroup : NormedAddCommGroup (h.SmoothL2Section μ) :=
  (h.smoothL2SectionCore μ).toNormedAddCommGroup

attribute [instance] smoothL2SectionNormedAddCommGroup

/-- The tagged norm and integral inner product are compatible. -/
@[instance_reducible]
def smoothL2SectionInnerProductSpace : InnerProductSpace ℂ (h.SmoothL2Section μ) :=
  InnerProductSpace.ofCore (h.smoothL2SectionCore μ).toCore

attribute [instance] smoothL2SectionInnerProductSpace

/-- The actual uniform completion for the chosen metric and density. -/
abbrev L2SectionSpace : Type _ := UniformSpace.Completion (h.SmoothL2Section μ)

/-- The canonical inclusion of smooth sections into this integral completion. -/
def smoothToL2 : smoothSections (n := n) (r := r) E →ₗ[ℂ] h.L2SectionSpace μ :=
  (UniformSpace.Completion.toComplL (S := ℂ) (α := h.SmoothL2Section μ)).toLinearMap

/-- On smooth inputs the completion inner product is the specified integral. -/
theorem inner_smoothToL2 (u v : smoothSections (n := n) (r := r) E) :
    inner ℂ (h.smoothToL2 μ u) (h.smoothToL2 μ v) = h.sectionPairing μ u v := by
  /- The canonical completion map preserves the pre-Hilbert inner product. -/
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ) (E := h.SmoothL2Section μ) u v

/-- The squared completion norm is the integral of the squared metric norm. -/
theorem norm_smoothToL2_sq (u : smoothSections (n := n) (r := r) E) :
    ‖h.smoothToL2 μ u‖ ^ 2 = (h.sectionPairing μ u u).re := by
  /- Apply norm-squared equals real inner product and the preceding pairing identity. -/
  rw [← h.inner_smoothToL2 μ u u]
  simp [← Complex.ofReal_pow]

/-- The canonical smooth-section inclusion is injective. -/
theorem smoothToL2_injective : Function.Injective (h.smoothToL2 μ) := by
  /- The integral norm is positive definite, so the completion map of this
  separated normed space is injective. -/
  exact UniformSpace.Completion.coe_injective (h.SmoothL2Section μ)

/-- Smooth sections are dense in their integral completion. -/
theorem denseRange_smoothToL2 : DenseRange (h.smoothToL2 μ) := by
  /- This is the dense range property of the canonical uniform completion map. -/
  exact UniformSpace.Completion.denseRange_coe (α := h.SmoothL2Section μ)

variable (k : SmoothHermitianMetric (n := n) (r := r) E)

/-- Uniform fiber comparison gives two-sided bounds for the integral norms. -/
theorem exists_l2_norm_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      c * ‖h.smoothToL2 μ u‖ ≤ ‖k.smoothToL2 μ u‖ ∧
        ‖k.smoothToL2 μ u‖ ≤ C * ‖h.smoothToL2 μ u‖ := by
  /- Integrate the uniform quadratic-form bounds. Both diagonal integrands are
  integrable. Taking nonnegative square roots gives the two norm inequalities,
  with positive square roots of the original constants. -/
  obtain ⟨c, C, hc, hC, hbound⟩ := h.exists_uniform_bounds k
  refine ⟨Real.sqrt c, Real.sqrt C, Real.sqrt_pos.mpr hc, Real.sqrt_pos.mpr hC, ?_⟩
  intro u
  -- Integrate the original uniform quadratic-form bounds with the same fixed measure.
  have hh : Integrable (fun x ↦ (h.pairing x (u.val x) (u.val x)).re) μ :=
    Complex.reCLM.integrable_comp (h.integrable_pairing μ u u)
  have hk : Integrable (fun x ↦ (k.pairing x (u.val x) (u.val x)).re) μ :=
    Complex.reCLM.integrable_comp (k.integrable_pairing μ u u)
  have hintegral (g : SmoothHermitianMetric (n := n) (r := r) E) :
      (∫ x, (g.pairing x (u.val x) (u.val x)).re ∂μ) = ‖g.smoothToL2 μ u‖ ^ 2 := by
    rw [g.norm_smoothToL2_sq]
    simpa only [sectionPairing, RCLike.re_eq_complex_re]
      using integral_re (g.integrable_pairing μ u u)
  have hlower : c * ‖h.smoothToL2 μ u‖ ^ 2 ≤ ‖k.smoothToL2 μ u‖ ^ 2 := by
    have hi := integral_mono (hh.const_mul c) hk (fun x ↦ (hbound x (u.val x)).1)
    simpa only [integral_const_mul, hintegral] using hi
  have hupper : ‖k.smoothToL2 μ u‖ ^ 2 ≤ C * ‖h.smoothToL2 μ u‖ ^ 2 := by
    have hi := integral_mono hk (hh.const_mul C) (fun x ↦ (hbound x (u.val x)).2)
    simpa only [integral_const_mul, hintegral] using hi
  -- Nonnegativity allows taking square roots without changing either completed norm.
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg _)) (norm_nonneg _)).mp
    simpa only [mul_pow, Real.sq_sqrt hc.le] using hlower
  · apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt hC.le] using hupper

/-- Identity on smooth sections extends uniquely to the two integral completions. -/
theorem existsUnique_l2Equiv :
    ∃! T : h.L2SectionSpace μ ≃L[ℂ] k.L2SectionSpace μ,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (h.smoothToL2 μ u) = k.smoothToL2 μ u := by
  /- Two-sided norm comparison extends the identity and its inverse continuously
  to the completions. Their compositions are identities by density. Agreement
  on all smooth inputs also forces uniqueness of a continuous extension. -/
  obtain ⟨c, C, hc, _, hbound⟩ := h.exists_l2_norm_comparison μ k
  let f := LinearEquiv.refl ℂ (smoothSections (n := n) (r := r) E)
  have hforward : ∃ C, ∀ u, ‖k.smoothToL2 μ (f u)‖ ≤ C * ‖h.smoothToL2 μ u‖ :=
    ⟨C, fun u ↦ (hbound u).2⟩
  have hreverse : ∃ C, ∀ u, ‖h.smoothToL2 μ (f.symm u)‖ ≤ C * ‖k.smoothToL2 μ u‖ := by
    refine ⟨c⁻¹, ?_⟩
    intro u
    calc
      ‖h.smoothToL2 μ (f.symm u)‖ ≤ ‖k.smoothToL2 μ u‖ / c :=
        (le_div_iff₀ hc).mpr (by
          simpa only [f, LinearEquiv.refl_symm, LinearEquiv.refl_apply, mul_comm]
            using (hbound u).1)
      _ = c⁻¹ * ‖k.smoothToL2 μ u‖ := by ring
  -- Extend the identity using both bounds and the specified dense inclusions.
  let T := f.extend (h.smoothToL2 μ) (k.smoothToL2 μ)
    (h.denseRange_smoothToL2 μ) hforward (k.denseRange_smoothToL2 μ) hreverse
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (h.smoothToL2 μ u) = k.smoothToL2 μ u :=
    f.extend_eq _ _ _ _ _ _ u
  refine ⟨T, hT, ?_⟩
  -- Continuous maps agreeing on the original smooth sections agree everywhere.
  intro S hS
  apply ContinuousLinearEquiv.ext
  apply (h.denseRange_smoothToL2 μ).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

/-- The bounded metric comparison preserving the underlying smooth section. -/
def l2Equiv : h.L2SectionSpace μ ≃L[ℂ] k.L2SectionSpace μ :=
  Classical.choose (h.existsUnique_l2Equiv μ k).exists

/-- The comparison sends each smooth section to itself in the other completion. -/
theorem l2Equiv_smoothToL2 (u : smoothSections (n := n) (r := r) E) :
    h.l2Equiv μ k (h.smoothToL2 μ u) = k.smoothToL2 μ u := by
  /- Read off the dense-domain specification of the chosen equivalence. -/
  exact Classical.choose_spec (h.existsUnique_l2Equiv μ k).exists u

/-- Comparing a metric with itself gives the identity completion map. -/
theorem l2Equiv_self : h.l2Equiv μ h = ContinuousLinearEquiv.refl ℂ (h.L2SectionSpace μ) := by
  /- The identity satisfies the same dense-domain specification. Apply uniqueness. -/
  apply ContinuousLinearEquiv.ext
  apply (h.denseRange_smoothToL2 μ).equalizer (h.l2Equiv μ h).continuous continuous_id
  funext u
  exact h.l2Equiv_smoothToL2 μ h u

/-- The reversed comparison is the inverse bounded map. -/
theorem l2Equiv_symm : (h.l2Equiv μ k).symm = k.l2Equiv μ h := by
  /- Evaluate both sides on the dense set of smooth sections, where they are
  inverse identity maps, and use continuity. -/
  apply ContinuousLinearEquiv.ext
  apply (k.denseRange_smoothToL2 μ).equalizer
    (h.l2Equiv μ k).symm.continuous (k.l2Equiv μ h).continuous
  funext u
  change (h.l2Equiv μ k).symm (k.smoothToL2 μ u) = k.l2Equiv μ h (k.smoothToL2 μ u)
  rw [k.l2Equiv_smoothToL2 μ h u, ← h.l2Equiv_smoothToL2 μ k u]
  exact (h.l2Equiv μ k).symm_apply_apply _

/-- Identity comparisons through an intermediate metric compose canonically. -/
theorem l2Equiv_trans (l : SmoothHermitianMetric (n := n) (r := r) E) :
    (h.l2Equiv μ k).trans (k.l2Equiv μ l) = h.l2Equiv μ l := by
  /- Both continuous equivalences preserve every underlying smooth section.
  Their equality follows from the unique dense-domain specification. -/
  apply ContinuousLinearEquiv.ext
  apply (h.denseRange_smoothToL2 μ).equalizer
    ((h.l2Equiv μ k).trans (k.l2Equiv μ l)).continuous (h.l2Equiv μ l).continuous
  funext u
  change k.l2Equiv μ l (h.l2Equiv μ k (h.smoothToL2 μ u)) =
    h.l2Equiv μ l (h.smoothToL2 μ u)
  rw [h.l2Equiv_smoothToL2 μ k u, k.l2Equiv_smoothToL2 μ l u,
    h.l2Equiv_smoothToL2 μ l u]

end AtiyahSinger.SmoothHermitianMetric

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]
  [IsSmoothPositiveMeasure (n := n) μ]


set_option linter.unusedSectionVars false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The explicit installed metric reproduces the original integral pairing exactly. -/
theorem sectionPairing_ofInnerProduct (u v : smoothSections (n := n) (r := r) E) :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).sectionPairing μ u v =
      smoothSectionPairing μ E u v := by
  /- The two integrands are equal pointwise by pairing_ofInnerProduct. -/
  unfold SmoothHermitianMetric.sectionPairing smoothSectionPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦
    SmoothHermitianMetric.pairing_ofInnerProduct (n := n) (r := r) E x (u.val x) (v.val x)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The explicit metric model and existing L² model have a unique identity isometry. -/
theorem existsUnique_l2OfInnerProductEquiv :
    ∃! T : (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).L2SectionSpace μ
        ≃ₗᵢ[ℂ] L2SectionSpace (n := n) (r := r) μ E,
      ∀ u : smoothSections (n := n) (r := r) E,
        T ((SmoothHermitianMetric.ofInnerProduct E).smoothToL2 μ u) = smoothToL2 μ E u := by
  /- The dense smooth subspaces have exactly the same integral inner product.
  Extend their identity isometry to the completions and similarly extend its
  inverse. Density proves the inverse laws and uniqueness. -/
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  let f := LinearEquiv.refl ℂ (smoothSections (n := n) (r := r) E)
  have hnorm (u : smoothSections (n := n) (r := r) E) :
      ‖smoothToL2 μ E (f u)‖ = ‖h.smoothToL2 μ u‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖smoothToL2 μ E u‖ ^ 2 = ‖h.smoothToL2 μ u‖ ^ 2
    rw [h.norm_smoothToL2_sq, sectionPairing_ofInnerProduct, ← inner_smoothToL2 μ E u u]
    simp [← Complex.ofReal_pow]
  -- The two dense inclusions have equal norms for exactly the installed metric.
  let T := f.extendOfIsometry (h.smoothToL2 μ) (smoothToL2 μ E)
    (h.denseRange_smoothToL2 μ) (denseRange_smoothToL2 μ E) hnorm
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (h.smoothToL2 μ u) = smoothToL2 μ E u :=
    f.extendOfIsometry_eq _ _ _ _ _ u
  refine ⟨T, hT, ?_⟩
  -- Density determines the whole isometry from its action on smooth sections.
  intro S hS
  have heq : (S : h.L2SectionSpace μ → L2SectionSpace μ E) = T := by
    apply (h.denseRange_smoothToL2 μ).equalizer S.continuous T.continuous
    funext u
    exact (hS u).trans (hT u).symm
  exact LinearIsometryEquiv.ext (congrFun heq)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical isometry from the explicit installed metric to the original L² model. -/
def l2OfInnerProductEquiv :
    (SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E).L2SectionSpace μ
      ≃ₗᵢ[ℂ] L2SectionSpace (n := n) (r := r) μ E :=
  Classical.choose (existsUnique_l2OfInnerProductEquiv μ E).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The existing-model comparison preserves the actual smooth-section inclusion. -/
theorem l2OfInnerProductEquiv_smoothToL2 (u : smoothSections (n := n) (r := r) E) :
    l2OfInnerProductEquiv μ E
      ((SmoothHermitianMetric.ofInnerProduct E).smoothToL2 μ u) = smoothToL2 μ E u := by
  /- Use the specified action of the chosen unique isometry on the dense domain. -/
  exact Classical.choose_spec (existsUnique_l2OfInnerProductEquiv μ E).exists u

end AtiyahSinger
