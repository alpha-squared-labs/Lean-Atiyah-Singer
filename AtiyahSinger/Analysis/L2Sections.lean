/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalSobolev
public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Completion

import AtiyahSinger.Geometry.HermitianMetric
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The integral L² completion and its comparison with H⁰

Public module ID: M0777.

The pre-Hilbert space consists of actual smooth sections, with inner product
∫ ⟪u(x),v(x)⟫ dμ. A type synonym keeps this integral norm separate from other section
topologies. Its uniform completion is L². The comparison with the localized H⁰ model
extends the identity on smooth sections; it is bounded in both directions, not in
general isometric. No measurable-section quotient or Riemannian-volume bridge is
claimed here. Sources: Spin Geometry III.2, (2.1), (2.17), Proposition 2.14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

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
/-- Conjugate symmetry of the actual integral pairing. -/
theorem smoothSectionPairing_conj_symm (u v : smoothSections (n := n) (r := r) E) :
    conj (smoothSectionPairing μ E v u) = smoothSectionPairing μ E u v := by
  /- The pointwise Hermitian products are conjugate symmetric. Conjugation is a
  continuous real-linear map and commutes with the integrable Bochner integral. -/
  -- Move conjugation inside the integral and use the fiberwise Hermitian symmetry.
  unfold smoothSectionPairing
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ inner_conj_symm (𝕜 := ℂ) (u.val x) (v.val x)

set_option linter.unusedSectionVars false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The real part of the integral squared norm is nonnegative. -/
theorem smoothSectionPairing_re_self_nonneg (u : smoothSections (n := n) (r := r) E) :
    0 ≤ (smoothSectionPairing μ E u u).re := by
  /- Move real part through the integrable Bochner integral. The integrand becomes
  the squared fiber norm, which is nonnegative; apply positivity of the integral. -/
  -- Real part commutes with integration because the original pairing is integrable.
  have hint := integrable_inner_smoothSections (n := n) μ E u u
  have hre : (smoothSectionPairing μ E u u).re =
      ∫ x, (inner ℂ (u.val x) (u.val x)).re ∂μ := by
    symm
    simpa only [smoothSectionPairing, RCLike.re_eq_complex_re] using integral_re hint
  rw [hre]
  exact integral_nonneg fun x ↦ inner_self_nonneg (𝕜 := ℂ) (x := u.val x)

set_option linter.unusedSectionVars false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Additivity of the integral pairing in the first variable. -/
theorem smoothSectionPairing_add_left (u v w : smoothSections (n := n) (r := r) E) :
    smoothSectionPairing μ E (u + v) w =
      smoothSectionPairing μ E u w + smoothSectionPairing μ E v w := by
  /- Fiberwise addition of sections and additivity of the Hermitian product identify
  the integrand with a sum. Both terms are integrable on the compact base, so the
  integral of that sum is the sum of their integrals. -/
  -- Both summands are integrable, so pointwise additivity passes to the integral.
  change (∫ x, inner ℂ (u.val x + v.val x) (w.val x) ∂μ) = _
  simp_rw [inner_add_left]
  exact integral_add (integrable_inner_smoothSections (n := n) μ E u w)
    (integrable_inner_smoothSections (n := n) μ E v w)

set_option linter.unusedSectionVars false in
-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Conjugate linearity of the integral pairing in the first variable. -/
theorem smoothSectionPairing_smul_left (u v : smoothSections (n := n) (r := r) E) (c : ℂ) :
    smoothSectionPairing μ E (c • u) v = conj c * smoothSectionPairing μ E u v := by
  /- The pointwise inner product pulls the scalar out as its complex conjugate.
  The Bochner integral commutes with multiplication by this fixed scalar. -/
  -- The scalar is conjugated in the first slot before it leaves the integral.
  change (∫ x, inner ℂ (c • u.val x) (v.val x) ∂μ) = _
  simp_rw [inner_smul_left]
  exact integral_const_mul (conj c) _

-- The Hermitian Prop includes smoothness; retain both original proofs on the same bundle.
set_option linter.overlappingInstances false in
/-- Smooth sections tagged by the measure whose integral norm will be used. -/
def SmoothL2Section (_μ : Measure M) : Type _ := smoothSections (n := n) (r := r) E

-- The Hermitian Prop includes smoothness; retain both original proofs on the same bundle.
set_option linter.overlappingInstances false in
/-- The usual addition on the tagged smooth section space. -/
@[instance_reducible]
def smoothL2SectionAddCommGroup : AddCommGroup (SmoothL2Section (n := n) (r := r) E μ) :=
  inferInstanceAs (AddCommGroup (smoothSections (n := n) (r := r) E))

attribute [instance] smoothL2SectionAddCommGroup

-- The Hermitian Prop includes smoothness; retain both original proofs on the same bundle.
set_option linter.overlappingInstances false in
/-- The usual complex scalar action on the tagged smooth section space. -/
@[instance_reducible]
def smoothL2SectionModule : Module ℂ (SmoothL2Section (n := n) (r := r) E μ) :=
  inferInstanceAs (Module ℂ (smoothSections (n := n) (r := r) E))

attribute [instance] smoothL2SectionModule

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The pre-Hilbert structure has the explicit integral pairing as its inner product. -/
@[instance_reducible]
def smoothL2SectionCore : InnerProductSpace.Core ℂ (SmoothL2Section (n := n) (r := r) E μ) where
  inner := smoothSectionPairing μ E
  conj_inner_symm := smoothSectionPairing_conj_symm μ E
  re_inner_nonneg := smoothSectionPairing_re_self_nonneg μ E
  add_left := smoothSectionPairing_add_left μ E
  smul_left := smoothSectionPairing_smul_left μ E
  definite := fun u h ↦ (smoothSectionPairing_self_eq_zero_iff μ E u).mp h

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The integral norm, obtained from the specified positive definite inner product. -/
@[instance_reducible]
def smoothL2SectionNormedAddCommGroup :
    NormedAddCommGroup (SmoothL2Section (n := n) (r := r) E μ) :=
  (smoothL2SectionCore μ E).toNormedAddCommGroup

attribute [instance] smoothL2SectionNormedAddCommGroup

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The integral inner product is compatible with the integral norm. -/
@[instance_reducible]
def smoothL2SectionInnerProductSpace :
    InnerProductSpace ℂ (SmoothL2Section (n := n) (r := r) E μ) :=
  InnerProductSpace.ofCore (smoothL2SectionCore μ E).toCore

attribute [instance] smoothL2SectionInnerProductSpace

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- L² sections as the completion of actual smooth sections in the integral norm. -/
abbrev L2SectionSpace : Type _ := UniformSpace.Completion (SmoothL2Section (n := n) (r := r) E μ)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The actual smooth-section inclusion into the integral completion. -/
def smoothToL2 : smoothSections (n := n) (r := r) E →ₗ[ℂ] L2SectionSpace (n := n) (r := r) μ E :=
  (UniformSpace.Completion.toComplL
    (S := ℂ) (α := SmoothL2Section (n := n) (r := r) E μ)).toLinearMap

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The completion inner product agrees with the original geometric integral. -/
theorem inner_smoothToL2 (u v : smoothSections (n := n) (r := r) E) :
    inner ℂ (smoothToL2 μ E u) (smoothToL2 μ E v) = smoothSectionPairing μ E u v := by
  /- The canonical embedding into an inner-product completion preserves the inner
  product. On the dense pre-Hilbert space that product was defined by this integral. -/
  -- The original inclusion is the canonical map into the inner-product completion.
  exact UniformSpace.Completion.inner_coe (𝕜 := ℂ)
    (E := SmoothL2Section (n := n) (r := r) E μ) u v

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The squared L² norm is exactly the integral of the pointwise squared fiber norm. -/
theorem norm_smoothToL2_sq (u : smoothSections (n := n) (r := r) E) :
    ‖smoothToL2 μ E u‖ ^ 2 = ∫ x, ‖u.val x‖ ^ 2 ∂μ := by
  /- Apply the inner-product norm identity and the preceding comparison on smooth
  sections. Taking real parts commutes with integration and turns ⟪u,u⟫ into ‖u‖². -/
  -- Express the completion norm by its self-pairing and then move real part inside.
  have hint := integrable_inner_smoothSections (n := n) μ E u u
  calc
    ‖smoothToL2 μ E u‖ ^ 2 = (inner ℂ (smoothToL2 μ E u) (smoothToL2 μ E u)).re := by
      simp [← Complex.ofReal_pow]
    _ = (smoothSectionPairing μ E u u).re := congrArg Complex.re (inner_smoothToL2 μ E u u)
    _ = ∫ x, (inner ℂ (u.val x) (u.val x)).re ∂μ := by
      symm
      simpa only [smoothSectionPairing, RCLike.re_eq_complex_re] using integral_re hint
    _ = ∫ x, ‖u.val x‖ ^ 2 ∂μ := by simp [← Complex.ofReal_pow]

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- No distinct smooth sections are identified by the integral completion. -/
theorem smoothToL2_injective : Function.Injective (smoothToL2 (n := n) (r := r) μ E) := by
  /- The integral inner product is positive definite because the density is positive
  on every nonempty open set. Thus the pre-Hilbert norm separates points, and its
  canonical embedding into the Hausdorff completion is injective. -/
  -- Positive definiteness has already made the source a separated normed space.
  exact UniformSpace.Completion.coe_injective (SmoothL2Section (n := n) (r := r) E μ)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- Smooth sections are dense in the integral L² completion by construction. -/
theorem denseRange_smoothToL2 : DenseRange (smoothToL2 (n := n) (r := r) μ E) := by
  /- The map is the canonical embedding of the normed smooth-section space into its
  uniform completion. The image of any uniform space is dense in its completion. -/
  -- The inclusion has dense range in the completion of this same normed space.
  exact UniformSpace.Completion.denseRange_coe
    (α := SmoothL2Section (n := n) (r := r) E μ)

namespace SmoothBundlePresentation

variable {E} (A : SmoothBundlePresentation (n := n) (r := r) E)

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The localized order-zero norm and the specified integral L² norm are equivalent. -/
theorem exists_l2_norm_comparison :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : smoothSections (n := n) (r := r) E,
      c * ‖A.smoothToSobolev 0 u‖ ≤ ‖smoothToL2 μ E u‖ ∧
        ‖smoothToL2 μ E u‖ ≤ C * ‖A.smoothToSobolev 0 u‖ := by
  /- Stage 1: J⁰ is the identity, so the coordinate norm is the sum of the local
  squared Euclidean L² norms of χ_j u. On each compact support the smooth positive
  density and positive definite Gram matrix have uniform upper and lower bounds.
  Stage 2: compare these local integrals with ∫χ_j²‖u‖² dμ. Nonnegative weights
  with sum one satisfy 1/N≤Σχ_j²≤1 when N>0. Sum and take square roots.
  For N=0 the partition identity forces the base to be empty and both spaces are zero. -/
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let h := SmoothHermitianMetric.ofInnerProduct (n := n) (r := r) E
  choose w hw hwpos hmap using
    (fun j : Fin A.size ↦ IsSmoothPositiveMeasure.exists_smooth_density
      (μ := μ) (A.chart j) (A.chart_mem_atlas j))
  -- Compare the given density and metric with each original coordinate norm on its support.
  have hlocal (j : Fin A.size) :
      letI := A.frame_mem_atlas j
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ x ∈ tsupport (A.cutoff j), ∀ z : V,
        a * ‖z‖ ^ 2 ≤ w j (A.chart j x) * ‖(A.frame j).symmL ℂ x z‖ ^ 2 ∧
          w j (A.chart j x) * ‖(A.frame j).symmL ℂ x z‖ ^ 2 ≤ b * ‖z‖ ^ 2 := by
    let e := A.frame j
    let := A.frame_mem_atlas j
    let K := tsupport (A.cutoff j)
    let S := Metric.sphere (0 : V) 1
    let Q (x : M) (z : V) : ℝ :=
      (∑ i, ∑ k, conj (z i) * h.gramMatrix e x i k * z k).re
    let R (p : M × V) := w j (A.chart j p.1) * Q p.1 p.2
    have hQeq (x : M) (hx : x ∈ e.baseSet) (z : V) :
        Q x z = ‖e.symmL ℂ x z‖ ^ 2 := by
      have hz : (e ⟨x, e.symmL ℂ x z⟩).2 = z := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
        exact e.continuousLinearMapAt_symmL hx z
      have heq := h.pairing_eq_gramMatrix e x hx (e.symmL ℂ x z) (e.symmL ℂ x z)
      rw [hz] at heq
      dsimp only [Q]
      rw [← heq]
      simp [h, SmoothHermitianMetric.pairing_ofInnerProduct, ← Complex.ofReal_pow]
    have hK := A.compact_support j
    have hS : IsCompact S := isCompact_sphere _ _
    have hcoeff (i k : Fin r) : ContinuousOn
        (fun p : M × V ↦ h.gramMatrix e p.1 i k) (K ×ˢ S) :=
      (h.contMDiffOn_gram e i k).continuousOn.comp continuous_fst.continuousOn
        (fun p hp ↦ (A.support_subset j hp.1).2)
    have hQcont : ContinuousOn (fun p : M × V ↦ Q p.1 p.2) (K ×ˢ S) := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro k _
      have hi : Continuous (fun p : M × V ↦ p.2 i) :=
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i).comp continuous_snd
      have hk : Continuous (fun p : M × V ↦ p.2 k) :=
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) k).comp continuous_snd
      exact ((hi.star.continuousOn).mul (hcoeff i k)).mul hk.continuousOn
    have hwK : ContinuousOn (fun x : M ↦ w j (A.chart j x)) K :=
      (hw j).continuousOn.comp
        ((A.chart j).continuousOn.mono (fun x hx ↦ (A.support_subset j hx).1))
        (fun x hx ↦ (A.chart j).map_source (A.support_subset j hx).1)
    have hRcont : ContinuousOn R (K ×ˢ S) :=
      (hwK.comp continuous_fst.continuousOn (fun _ hp ↦ hp.1)).mul hQcont
    have hRpos (p : M × V) (hp : p ∈ K ×ˢ S) : 0 < R p := by
      have hx := A.support_subset j hp.1
      have hz : p.2 ≠ 0 := by
        intro hz
        simp [S, hz] at hp
      have hinv : e.symmL ℂ p.1 p.2 ≠ 0 := by
        intro heq
        apply hz
        have he := e.continuousLinearMapAt_symmL (R := ℂ) hx.2 p.2
        simpa [heq] using he.symm
      dsimp only [R]
      rw [hQeq p.1 hx.2]
      exact mul_pos (hwpos j _ ((A.chart j).map_source hx.1))
        (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hinv))
    obtain ⟨a, ha, halower⟩ := (hK.prod hS).exists_forall_le' hRcont hRpos
    obtain ⟨b, hupper⟩ := ((hK.prod hS).image_of_continuousOn hRcont).bddAbove
    refine ⟨a, max b 1, ha, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro x hx z
    have hxe := (A.support_subset j hx).2
    by_cases hz : z = 0
    · subst z
      simp
    let y : V := (‖z‖⁻¹ : ℂ) • z
    have hy : y ∈ S := by
      simpa [S, y, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hz
    have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hscale : (‖z‖ : ℂ) • y = z := by
      simp [y, smul_smul, hz0]
    have hRscale : w j (A.chart j x) * ‖e.symmL ℂ x z‖ ^ 2 =
        R (x, y) * ‖z‖ ^ 2 := by
      dsimp only [R]
      rw [hQeq x hxe]
      conv_lhs => rw [← hscale]
      rw [map_smul, norm_smul]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]
      ring
    have hlo := halower (x, y) ⟨hx, hy⟩
    have hup := (hupper ⟨(x, y), ⟨hx, hy⟩, rfl⟩).trans (le_max_left b 1)
    rw [hRscale]
    exact ⟨mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖z‖),
      mul_le_mul_of_nonneg_right hup (sq_nonneg ‖z‖)⟩
  choose a b ha hb hab using hlocal
  let := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  have hnormcont (u : smoothSections (n := n) (r := r) E) :
      Continuous (fun x : M ↦ ‖u.val x‖ ^ 2) := by
    simpa [Function.comp_def, h, SmoothHermitianMetric.pairing_ofInnerProduct,
      ← Complex.ofReal_pow]
      using Complex.continuous_re.comp (h.contMDiff_pairing u u).continuous
  -- The defining measure equality transports the actual cutoff-weighted integral.
  have htransport (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
      (∫ x, A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2 ∂μ) =
        ∫ z in (A.chart j).target, w j z *
          (A.cutoff j ((A.chart j).symm z) ^ 2 *
            ‖u.val ((A.chart j).symm z)‖ ^ 2) := by
    let c := A.chart j
    let f (x : M) := A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2
    let g (z : EuclideanSpace ℝ (Fin n)) := f (c.symm z)
    have hfcont : Continuous f := ((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)
    have hgcont : ContinuousOn g c.target := hfcont.comp_continuousOn c.symm.continuousOn
    have hgd : AEStronglyMeasurable g ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w j z))) :=
      AEStronglyMeasurable.mono_ac (withDensity_absolutelyContinuous _ _)
        (hgcont.aestronglyMeasurable c.open_target.measurableSet)
    have hgmap : AEStronglyMeasurable g (Measure.map c (μ.restrict c.source)) := by
      change AEStronglyMeasurable g
        (Measure.map (A.chart j) (μ.restrict (A.chart j).source))
      rw [hmap j]
      exact hgd
    have hwmeas : AEMeasurable (fun z ↦ ENNReal.ofReal (w j z))
        (volume.restrict c.target) :=
      (ENNReal.continuous_ofReal.comp_continuousOn
        (hw j).continuousOn).aemeasurable c.open_target.measurableSet
    calc
      _ = ∫ x in c.source, f x ∂μ := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        have hχ : A.cutoff j x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          exact fun hxK ↦ hx (A.support_subset j hxK).1
        simp [f, hχ]
      _ = ∫ x in c.source, g (c x) ∂μ := by
        apply setIntegral_congr_fun c.open_source.measurableSet
        intro x hx
        simp [g, c.left_inv hx]
      _ = ∫ z, g z ∂Measure.map c (μ.restrict c.source) :=
        (integral_map (c.continuousOn.aemeasurable c.open_source.measurableSet) hgmap).symm
      _ = ∫ z, g z ∂(volume.restrict c.target).withDensity
          (fun z ↦ ENNReal.ofReal (w j z)) := by rw [hmap j]
      _ = ∫ z in c.target, w j z * g z := by
        rw [integral_withDensity_eq_integral_toReal_smul₀ hwmeas
          (Filter.Eventually.of_forall fun z ↦ ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
        rw [ENNReal.toReal_ofReal (hwpos j z hz).le, smul_eq_mul]
  -- Pointwise bounds are integrated in the same original chart, including its zero extension.
  have hchart (j : Fin A.size) (u : smoothSections (n := n) (r := r) E) :
      a j * (∫ z, ‖A.localize j u z‖ ^ 2) ≤
          ∫ x, A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2 ∂μ ∧
        (∫ x, A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2 ∂μ) ≤
          b j * (∫ z, ‖A.localize j u z‖ ^ 2) := by
    let := A.frame_mem_atlas j
    let c := A.chart j
    let e := A.frame j
    let G (z : EuclideanSpace ℝ (Fin n)) :=
      w j z * (A.cutoff j (c.symm z) ^ 2 * ‖u.val (c.symm z)‖ ^ 2)
    have hFnorm (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
        ‖A.localize j u z‖ ^ 2 =
          A.cutoff j (c.symm z) ^ 2 * ‖(e ⟨c.symm z, u.val (c.symm z)⟩).2‖ ^ 2 := by
      change ‖A.localizedFunction j u z‖ ^ 2 = _
      rw [localizedFunction, ite_eq_left hz]
      simp only [sectionInChart, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
        sq_abs]
      rfl
    have hpoint (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target) :
        a j * ‖A.localize j u z‖ ^ 2 ≤ G z ∧ G z ≤ b j * ‖A.localize j u z‖ ^ 2 := by
      rw [hFnorm z hz]
      by_cases hχ : A.cutoff j (c.symm z) = 0
      · simp [G, hχ]
      have hxK : c.symm z ∈ tsupport (A.cutoff j) := subset_tsupport _ hχ
      have hxe := (A.support_subset j hxK).2
      have heinv : e.symmL ℂ (c.symm z) (e ⟨c.symm z, u.val (c.symm z)⟩).2 =
          u.val (c.symm z) := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hxe]
        exact e.symmL_continuousLinearMapAt hxe _
      have h := hab j (c.symm z) hxK (e ⟨c.symm z, u.val (c.symm z)⟩).2
      rw [heinv, c.right_inv hz] at h
      constructor
      · have hmul := mul_le_mul_of_nonneg_left h.1 (sq_nonneg (A.cutoff j (c.symm z)))
        dsimp only [G]
        nlinarith only [hmul]
      · have hmul := mul_le_mul_of_nonneg_left h.2 (sq_nonneg (A.cutoff j (c.symm z)))
        dsimp only [G]
        nlinarith only [hmul]
    have hFint : Integrable (fun z ↦ ‖A.localize j u z‖ ^ 2) :=
      ((A.localize j u).memLp 2 volume).integrable_norm_pow (by decide)
    have hFtarget : (∫ z in c.target, ‖A.localize j u z‖ ^ 2) =
        ∫ z, ‖A.localize j u z‖ ^ 2 := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      change z ∉ (A.chart j).target at hz
      simp [localize, localizedFunction, hz]
    have hGcont : ContinuousOn G c.target :=
      (hw j).continuousOn.mul
        ((((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)).comp_continuousOn
          c.symm.continuousOn)
    have hGint : Integrable G (volume.restrict c.target) := by
      apply ((hFint.restrict (s := c.target)).const_mul (b j)).mono'
        (hGcont.aestronglyMeasurable c.open_target.measurableSet)
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      have hGpos : 0 ≤ G z := mul_nonneg (hwpos j z hz).le
        (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      simpa only [Real.norm_eq_abs, abs_of_nonneg hGpos] using (hpoint z hz).2
    rw [htransport j u]
    constructor
    · have hi := integral_mono_ae ((hFint.restrict (s := c.target)).const_mul (a j)) hGint
        (by
          filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
          exact (hpoint z hz).1)
      simpa only [integral_const_mul, hFtarget] using hi
    · have hi := integral_mono_ae hGint ((hFint.restrict (s := c.target)).const_mul (b j))
        (by
          filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
          exact (hpoint z hz).2)
      simpa only [integral_const_mul, hFtarget] using hi
  -- At order zero the Bessel multiplier is identity, with the original Euclidean L² norm.
  have hcoord (v : SchwartzMap (EuclideanSpace ℝ (Fin n)) V) :
      ‖schwartzSobolevCoordinate 0 v‖ ^ 2 = ∫ z, ‖v z‖ ^ 2 := by
    have hz : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
      simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
        SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
    rw [hz, SchwartzMap.norm_toLp' (by simp) (by simp)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sq_sqrt]
    exact integral_nonneg fun z ↦ sq_nonneg _
  have hSob (u : smoothSections (n := n) (r := r) E) :
      ‖A.smoothToSobolev 0 u‖ ^ 2 = ∑ j, ∫ z, ‖A.localize j u z‖ ^ 2 := by
    rw [A.norm_smoothToSobolev_sq]
    exact Finset.sum_congr rfl (fun j _ ↦ hcoord (A.localize j u))
  let α : ℝ := 1 + ∑ j, (a j)⁻¹
  let β : ℝ := 1 + ∑ j, b j
  let δ : ℝ := (A.size : ℝ) + 1
  have hα : 0 < α := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun j _ ↦ (inv_pos.mpr (ha j)).le)
  have hβ : 0 < β := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun j _ ↦ (hb j).le)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hαj (j : Fin A.size) : (a j)⁻¹ ≤ α := by
    have hj := Finset.single_le_sum (fun k _ ↦ (inv_pos.mpr (ha k)).le)
      (Finset.mem_univ j)
    dsimp only [α]
    linarith
  have hβj (j : Fin A.size) : b j ≤ β := by
    have hj := Finset.single_le_sum (fun k _ ↦ (hb k).le) (Finset.mem_univ j)
    dsimp only [β]
    linarith
  refine ⟨Real.sqrt α⁻¹, Real.sqrt (δ * β), Real.sqrt_pos.mpr (inv_pos.mpr hα),
    Real.sqrt_pos.mpr (mul_pos hδ hβ), ?_⟩
  intro u
  let B (j : Fin A.size) := ∫ z, ‖A.localize j u z‖ ^ 2
  let I (j : Fin A.size) := ∫ x, A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2 ∂μ
  have hBpos (j : Fin A.size) : 0 ≤ B j := integral_nonneg fun z ↦ sq_nonneg _
  have hIpos (j : Fin A.size) : 0 ≤ I j :=
    integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hIint (j : Fin A.size) :
      Integrable (fun x ↦ A.cutoff j x ^ 2 * ‖u.val x‖ ^ 2) μ :=
    (((A.smooth_cutoff j).continuous.pow 2).mul (hnormcont u)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsumint : Integrable
      (fun x ↦ (∑ j, A.cutoff j x ^ 2) * ‖u.val x‖ ^ 2) μ := by
    simpa only [← Finset.sum_mul] using
      integrable_finsetSum Finset.univ (fun j _ ↦ hIint j)
  have hsumI : (∑ j, I j) = ∫ x, (∑ j, A.cutoff j x ^ 2) * ‖u.val x‖ ^ 2 ∂μ := by
    simpa only [Finset.sum_mul, I] using
      (integral_finsetSum Finset.univ (fun j _ ↦ hIint j)).symm
  -- The partition identity controls its squared weights without a nonempty-index assumption.
  have hcutupper (x : M) : (∑ j, A.cutoff j x ^ 2) ≤ 1 := by
    simpa only [A.sum_cutoff, one_pow] using
      Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (fun j _ ↦ A.cutoff_nonneg j x)
  have hcutlower (x : M) : 1 ≤ δ * ∑ j, A.cutoff j x ^ 2 := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun j : Fin A.size ↦ A.cutoff j x) (fun _ ↦ (1 : ℝ))
    have hzero : 0 ≤ ∑ j, A.cutoff j x ^ 2 :=
      Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    have hlo : 1 ≤ (A.size : ℝ) * ∑ j, A.cutoff j x ^ 2 := by
      simpa [A.sum_cutoff, mul_comm] using hcs
    exact hlo.trans (mul_le_mul_of_nonneg_right (by dsimp only [δ]; linarith) hzero)
  have hnormint : Integrable (fun x ↦ ‖u.val x‖ ^ 2) μ :=
    (hnormcont u).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpartupper : (∑ j, I j) ≤ ‖smoothToL2 μ E u‖ ^ 2 := by
    rw [hsumI, norm_smoothToL2_sq]
    exact integral_mono hsumint hnormint
      (fun x ↦ by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (hcutupper x) (sq_nonneg ‖u.val x‖))
  have hpartlower : ‖smoothToL2 μ E u‖ ^ 2 ≤ δ * ∑ j, I j := by
    rw [norm_smoothToL2_sq, hsumI, ← integral_const_mul]
    apply integral_mono hnormint (hsumint.const_mul δ)
    intro x
    simpa only [one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right (hcutlower x) (sq_nonneg ‖u.val x‖)
  have hBsum : (∑ j, B j) ≤ α * ∑ j, I j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    calc
      B j ≤ I j / a j := (le_div_iff₀ (ha j)).mpr (by
        change B j * a j ≤ I j
        rw [mul_comm]
        exact (hchart j u).1)
      _ = (a j)⁻¹ * I j := by ring
      _ ≤ α * I j := mul_le_mul_of_nonneg_right (hαj j) (hIpos j)
  have hIsum : (∑ j, I j) ≤ β * ∑ j, B j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact (hchart j u).2.trans (mul_le_mul_of_nonneg_right (hβj j) (hBpos j))
  have hlower : ‖A.smoothToSobolev 0 u‖ ^ 2 ≤ α * ‖smoothToL2 μ E u‖ ^ 2 :=
    (hSob u).le.trans (hBsum.trans
      (mul_le_mul_of_nonneg_left hpartupper hα.le))
  have hupper : ‖smoothToL2 μ E u‖ ^ 2 ≤ (δ * β) * ‖A.smoothToSobolev 0 u‖ ^ 2 := by
    calc
      _ ≤ δ * ∑ j, I j := hpartlower
      _ ≤ δ * (β * ∑ j, B j) := mul_le_mul_of_nonneg_left hIsum hδ.le
      _ = _ := by rw [hSob]; simp only [B, mul_assoc]
  -- Positive square roots turn these integral quadratic bounds into the original norms.
  constructor
  · apply (sq_le_sq₀
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt (inv_pos.mpr hα).le]
    have hdiv : ‖A.smoothToSobolev 0 u‖ ^ 2 / α ≤ ‖smoothToL2 μ E u‖ ^ 2 :=
      (div_le_iff₀ hα).mpr (by rw [mul_comm]; exact hlower)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · apply (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    simpa only [mul_pow, Real.sq_sqrt (mul_pos hδ hβ).le] using hupper

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The identity on smooth sections gives a unique continuous linear H⁰–L² equivalence. -/
theorem existsUnique_sobolevZeroEquivL2 :
    ∃! T : A.SobolevSpace 0 ≃L[ℂ] L2SectionSpace (n := n) (r := r) μ E,
      ∀ u : smoothSections (n := n) (r := r) E,
        T (A.smoothToSobolev 0 u) = smoothToL2 μ E u := by
  /- Extend the identity on smooth sections using the two norm comparison bounds.
  Both spaces are completions of that same vector space. The extensions in the two
  directions compose to the identity on dense images, hence everywhere; density also
  forces uniqueness of the resulting continuous linear equivalence. -/
  obtain ⟨c, C, hc, _, hbound⟩ := A.exists_l2_norm_comparison μ
  let f := LinearEquiv.refl ℂ (smoothSections (n := n) (r := r) E)
  have hforward : ∃ C, ∀ u,
      ‖smoothToL2 μ E (f u)‖ ≤ C * ‖A.smoothToSobolev 0 u‖ :=
    ⟨C, fun u ↦ (hbound u).2⟩
  have hreverse : ∃ C, ∀ u,
      ‖A.smoothToSobolev 0 (f.symm u)‖ ≤ C * ‖smoothToL2 μ E u‖ := by
    refine ⟨c⁻¹, ?_⟩
    intro u
    calc
      _ ≤ ‖smoothToL2 μ E u‖ / c := (le_div_iff₀ hc).mpr (by
        simpa only [f, LinearEquiv.refl_symm, LinearEquiv.refl_apply, mul_comm]
          using (hbound u).1)
      _ = c⁻¹ * ‖smoothToL2 μ E u‖ := by ring
  -- Extend the identity in both directions along the specified dense smooth inclusions.
  let T := f.extend (A.smoothToSobolev 0) (smoothToL2 μ E)
    (A.denseRange_smoothToSobolev 0) hforward (denseRange_smoothToL2 μ E) hreverse
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (A.smoothToSobolev 0 u) = smoothToL2 μ E u :=
    f.extend_eq _ _ _ _ _ _ u
  refine ⟨T, hT, ?_⟩
  -- Density forces equality of the actual bounded maps, hence of the equivalences.
  intro S hS
  apply ContinuousLinearEquiv.ext
  apply (A.denseRange_smoothToSobolev 0).equalizer S.continuous T.continuous
  funext u
  exact (hS u).trans (hT u).symm

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The canonical H⁰–L² identification, specified on actual smooth sections. -/
def sobolevZeroEquivL2 : A.SobolevSpace 0 ≃L[ℂ] L2SectionSpace (n := n) (r := r) μ E :=
  Classical.choose (A.existsUnique_sobolevZeroEquivL2 μ).exists

-- The Hermitian Prop includes smoothness; the public type retains both coherent Prop proofs.
set_option linter.overlappingInstances false in
/-- The H⁰–L² identification sends a smooth section to that same section. -/
theorem sobolevZeroEquivL2_smoothToSobolev
    (u : smoothSections (n := n) (r := r) E) :
    A.sobolevZeroEquivL2 μ (A.smoothToSobolev 0 u) = smoothToL2 μ E u := by
  /- Apply the witness property of the unique equivalence. It records equality of
  the two canonical embeddings of each smooth section, not equality of their norms. -/
  exact (Classical.choose_spec (A.existsUnique_sobolevZeroEquivL2 μ).exists) u

end SmoothBundlePresentation

end AtiyahSinger
