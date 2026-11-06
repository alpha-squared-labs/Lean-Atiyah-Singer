/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CircleFourierOperator
public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.MeasureTheory.Group.Circle

/-!
# Smooth circle sections and the original Fourier Hilbert space

Public module ID: M1240.

AR02 uses mathlib's actual circle manifold and its trivial complex line. The
positive map from the circle of period `2π` is `AddCircle.homeomorphCircle'`,
which sends the class of `t` to `Circle.exp t`, without complex conjugation.
The probability measure is the pushforward of the original normalized Haar
measure. The smooth-to-L² map evaluates a section in its fixed trivial frame
and uses the original continuous-function embedding in the Fourier L² space.

Source: Atiyah--Singer I, section 8, pp.525--526. These constructions implement
the source's scalar functions on the circle using the project's existing
bundle and measure interfaces. The smooth measure has angular density
`1 / (2π)`; arbitrary atlas coordinates also include the positive absolute
Jacobian.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

/-- The ordinary trivial complex line on the actual smooth circle. -/
abbrev FourierCircleLine : Circle → Type :=
  Bundle.Trivial Circle (EuclideanSpace ℂ (Fin 1))

/-- The specified trivial frame gives a smooth complex line bundle. -/
theorem isSmoothComplexBundle_fourierCircleLine :
    IsSmoothComplexBundle (n := 1) (r := 1) FourierCircleLine := by
  /- The trivial bundle atlas has its global standard frame. Its transition
  maps are the identity complex-linear map, hence real-smooth on overlaps.
  Use the original trivial-bundle atlas, rather than assigning a second
  topology or a different smooth structure to the line. -/
  -- The designated native atlas contains only the original global frame.
  constructor
  intro e e' he he'
  obtain rfl := Bundle.Trivial.eq_trivialization Circle (EuclideanSpace ℂ (Fin 1)) e
  obtain rfl := Bundle.Trivial.eq_trivialization Circle (EuclideanSpace ℂ (Fin 1)) e'
  simp_rw [Bundle.Trivial.trivialization.coordChangeL]
  exact contMDiff_const.contMDiffOn

attribute [local instance] isSmoothComplexBundle_fourierCircleLine

/-- Normalized Haar measure transported by the positive angular homeomorphism. -/
def fourierCircleMeasure : Measure Circle :=
  Measure.map AddCircle.homeomorphCircle'
    (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive)

open Set Function Metric in
open scoped Topology in
/-- The transported probability measure is a positive smooth density. -/
theorem isSmoothPositiveMeasure_fourierCircleMeasure :
    IsSmoothPositiveMeasure (n := 1) fourierCircleMeasure := by
  /- Stage 1: on the open interval between successive lifts of the deleted
  pole, of length 2π, normalized Haar measure is dt/(2π). The specified
  homeomorphism is t ↦ exp(it), so the
  resulting local measure has the positive constant angular density 1/(2π).
  Stage 2: change from angular coordinates to any chart of the original
  circle atlas. Multiply by the absolute determinant of the inverse chart
  derivative. Smooth chart compatibility and an invertible derivative give
  the strictly positive smooth density required by IsSmoothPositiveMeasure.
  Restrict to chart sources before pushing forward, as in that definition. -/
  classical
  constructor
  intro c₀ hc₀
  -- The original sphere atlas deletes one pole; the positive angular covering
  -- identifies its complement with the open interval between two lifts of that pole.
  let : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  change ∃ v : sphere (0 : ℂ) 1, c₀ = stereographic' 1 v at hc₀
  obtain ⟨v, rfl⟩ := hc₀
  let V := EuclideanSpace ℝ (Fin 1)
  let I := 𝓘(ℝ, V)
  let c : OpenPartialHomeomorph Circle V := stereographic' 1 v
  let l : V ≃ₗᵢ[ℝ] ℝ := (OrthonormalBasis.singleton (Fin 1) ℝ).repr.symm
  let T : ℝ := 2 * Real.pi
  let : Fact (0 < T) := circlePeriodPositive
  let a : ℝ := Complex.arg (v : ℂ)
  let b : OpenPartialHomeomorph ℝ Circle :=
    (AddCircle.openPartialHomeomorphCoe T a).trans
      AddCircle.homeomorphCircle'.toOpenPartialHomeomorph
  have hbfun (t : ℝ) : b t = Circle.exp t := rfl
  have hbS : b.source = Ioo a (a + T) := by
    simp [b]
  have hbT : b.target = c.source := by
    ext z
    simp only [b, OpenPartialHomeomorph.trans_target,
      Homeomorph.toOpenPartialHomeomorph_target, mem_inter_iff, mem_univ, true_and,
      AddCircle.openPartialHomeomorphCoe_target, mem_preimage, mem_compl_iff,
      mem_singleton_iff, Homeomorph.toOpenPartialHomeomorph_symm_apply]
    change AddCircle.homeomorphCircle'.symm z ≠ (a : AddCircle T) ↔ z ∈ c.source
    have hpole : AddCircle.homeomorphCircle' (a : AddCircle T) = (v : Circle) := by
      change Circle.exp a = (v : Circle)
      exact Circle.exp_arg (v : Circle)
    have heq : AddCircle.homeomorphCircle'.symm z = (a : AddCircle T) ↔ z = (v : Circle) := by
      constructor
      · intro hz
        have hh : AddCircle.homeomorphCircle' (AddCircle.homeomorphCircle'.symm z) =
            AddCircle.homeomorphCircle' (a : AddCircle T) :=
          congrArg (fun x : AddCircle T ↦ AddCircle.homeomorphCircle' x) hz
        exact (AddCircle.homeomorphCircle'.apply_symm_apply z).symm.trans (hh.trans hpole)
      · intro hz
        rw [hz, ← hpole, AddCircle.homeomorphCircle'.symm_apply_apply]
    simp only [c, stereographic'_source]
    exact not_congr heq
  let e : OpenPartialHomeomorph ℝ ℝ :=
    (b.trans c).trans l.toHomeomorph.toOpenPartialHomeomorph
  have hefun (t : ℝ) : e t = l (c (Circle.exp t)) := rfl
  have heS : e.source = Ioo a (a + T) := by
    ext t
    simp only [e, OpenPartialHomeomorph.trans_source, mem_inter_iff, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_source, mem_univ, and_true]
    constructor
    · exact fun ht ↦ hbS ▸ ht.1
    · intro ht
      have htb : t ∈ b.source := hbS.symm ▸ ht
      exact ⟨htb, hbT ▸ b.map_source htb⟩
  have heT : e.target = univ := by
    ext z
    simp only [e, OpenPartialHomeomorph.trans_target, mem_inter_iff, mem_preimage,
      Homeomorph.toOpenPartialHomeomorph_target, mem_univ, true_and]
    change l.symm z ∈ c.target ∧ c.symm (l.symm z) ∈ b.target ↔ True
    simp only [c, stereographic'_target, mem_univ, true_and, iff_true]
    rw [hbT]
    exact c.map_target (by simp [c])
  -- Smoothness uses this native chart and its inverse. The complex exponential
  -- has nonzero velocity, so no coordinate derivative of the covering can vanish.
  have hesmooth (t : ℝ) (ht : t ∈ e.source) : ContDiffAt ℝ ∞ e t := by
    have htb : t ∈ b.source := hbS.symm ▸ (heS ▸ ht)
    have htc : Circle.exp t ∈ c.source := by
      rw [← hbfun, ← hbT]
      exact b.map_source htb
    have hc := contMDiffOn_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω))
      (IsManifold.subset_maximalAtlas (show c ∈ atlas V Circle from ⟨v, rfl⟩))
    have hcc := (hc _ htc).contMDiffAt (c.open_source.mem_nhds htc)
    exact contMDiffAt_iff_contDiffAt.mp
      (l.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff.contMDiffAt.comp t
        (hcc.comp t contMDiff_circleExp.contMDiffAt))
  let p (z : ℝ) : ℂ := (c.symm (l.symm z) : ℂ)
  have hpsmooth : ContDiff ℝ ∞ p := by
    have hc := contMDiffOn_symm_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω))
      (IsManifold.subset_maximalAtlas (show c ∈ atlas V Circle from ⟨v, rfl⟩))
    have hcu : ContMDiff I I ∞ c.symm := by
      apply contMDiffOn_univ.mp
      simpa [c] using hc
    exact contMDiff_iff_contDiff.mp
      (contMDiff_coe_sphere.comp
        (hcu.comp l.symm.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.contMDiff))
  have hnonzero (t : ℝ) (ht : t ∈ e.source) : deriv e t ≠ 0 := by
    have heder := (hesmooth t ht).differentiableAt (by simp)
    have hchain := (hpsmooth.differentiable (by simp) (e t)).hasDerivAt.scomp t
      heder.hasDerivAt
    have hsame : (p ∘ e) =ᶠ[𝓝 t] fun s : ℝ ↦
        Complex.exp ((s : ℂ) * Complex.I) := by
      filter_upwards [e.open_source.mem_nhds ht] with s hs
      have hsc : Circle.exp s ∈ c.source := by
        rw [← hbfun, ← hbT]
        exact b.map_source (hbS.symm ▸ (heS ▸ hs))
      simp only [comp_apply, p, hefun, l.symm_apply_apply, c.left_inv hsc, Circle.coe_exp]
    have hexp : HasDerivAt (fun s : ℝ ↦ Complex.exp ((s : ℂ) * Complex.I))
        (Complex.exp ((t : ℂ) * Complex.I) * Complex.I) t := by
      have hcos := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_cos t)
      have hsin := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (Real.hasDerivAt_sin t)
      convert hcos.add (hsin.mul_const Complex.I) using 1
      · ext s
        simp [Complex.exp_mul_I]
      · simp only [Complex.exp_mul_I, Complex.ofRealCLM_apply, Complex.ofReal_neg]
        ring_nf
        simp
        ring
    have heq := (hchain.congr_of_eventuallyEq hsame.symm).unique hexp
    intro hz
    simp only [hz, zero_smul] at heq
    exact (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero) heq.symm
  have hgsmooth : ContDiff ℝ ∞ e.symm := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hzt : z ∈ e.target := heT.symm ▸ mem_univ z
    have hzs := e.map_target hzt
    exact e.contDiffAt_symm_deriv (hnonzero _ hzs) hzt
      ((hesmooth _ hzs).differentiableAt (by simp)).hasDerivAt (hesmooth _ hzs)
  have hgderiv (z : ℝ) : deriv e.symm z ≠ 0 := by
    have hzt : z ∈ e.target := heT.symm ▸ mem_univ z
    have hzs := e.map_target hzt
    rw [(e.hasDerivAt_symm hzt (hnonzero _ hzs)
      ((hesmooth _ hzs).differentiableAt (by simp)).hasDerivAt).deriv]
    exact inv_ne_zero (hnonzero _ hzs)
  -- The density is the absolute inverse-coordinate Jacobian divided by the
  -- original period. Its sign and smoothness follow from the same nonzero derivative.
  let k : ℝ := T⁻¹
  have hk : 0 < k := inv_pos.mpr (show 0 < T from Fact.out)
  let q (z : ℝ) : ℝ := k * |deriv e.symm z|
  let w (z : V) : ℝ := q (l z)
  have hqsmooth : ContDiff ℝ ∞ q := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    exact contDiffAt_const.mul
      ((contDiff_infty_iff_deriv.mp hgsmooth).2.contDiffAt.abs (hgderiv z))
  have hwsmooth : ContDiff ℝ ∞ w :=
    hqsmooth.comp l.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hwpos (z : V) : 0 < w z := mul_pos hk (abs_pos.mpr (hgderiv (l z)))
  -- Normalize the actual additive Haar measure. Removing an endpoint of its
  -- fundamental interval changes no Lebesgue measure and introduces no new measure.
  have hhaar : (@AddCircle.haarAddCircle T inferInstance) =
      ENNReal.ofReal k • (volume : Measure (AddCircle T)) := by
    rw [AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
      ← ENNReal.ofReal_mul hk.le]
    have hT : T ≠ 0 := ne_of_gt (show 0 < T from Fact.out)
    simp [k, hT]
  have hmk : Measure.map ((↑) : ℝ → AddCircle T)
      (volume.restrict (Ioo a (a + T))) = volume := by
    rw [restrict_Ioo_eq_restrict_Ioc]
    exact (AddCircle.measurePreserving_mk T a).map_eq
  have hbmeas : Measurable b := by
    change Measurable Circle.exp
    exact Circle.exp.continuous.measurable
  have hμ : fourierCircleMeasure =
      ENNReal.ofReal k • Measure.map b (volume.restrict b.source) := by
    change Measure.map AddCircle.homeomorphCircle'
      (@AddCircle.haarAddCircle T inferInstance) = _
    rw [hhaar, Measure.map_smul _ AddCircle.homeomorphCircle'.continuous.measurable.aemeasurable,
      hbS, ← hmk]
    have hquot : Measurable ((↑) : ℝ → AddCircle T) := by
      convert (AddCircle.continuous_mk' T).measurable using 1
      rfl
    rw [Measure.map_map AddCircle.homeomorphCircle'.continuous.measurable
      hquot]
    rfl
  have hescont : ContinuousOn e e.source :=
    fun t ht ↦ (hesmooth t ht).continuousAt.continuousWithinAt
  have hemeas : AEMeasurable e (volume.restrict e.source) :=
    hescont.aemeasurable e.open_source.measurableSet
  -- Push the original measure restricted to the chart source through the same
  -- chart. Every covering-interval point lies in that source; keeping the
  -- restriction explicit prevents assigning any mass to the deleted pole.
  have hscalar : Measure.map l (Measure.map c (fourierCircleMeasure.restrict c.source)) =
      ENNReal.ofReal k • Measure.map e (volume.restrict e.source) := by
    ext A hA
    have hlA : MeasurableSet (l ⁻¹' A) := l.continuous.measurable hA
    have hpre : MeasurableSet (c ⁻¹' (l ⁻¹' A) ∩ c.source) := by
      simpa only [Set.domRestrict_eq, Set.preimage_comp,
        Set.image_preimage_eq_inter_range, Subtype.range_coe] using
        c.open_source.measurableSet.subtype_image
          (hlA.preimage c.continuousOn.domRestrict.measurable)
    rw [Measure.map_apply l.continuous.measurable hA,
      Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hlA,
      Measure.restrict_apply' c.open_source.measurableSet, hμ, Measure.smul_apply,
      Measure.map_apply hbmeas hpre, Measure.restrict_apply' b.open_source.measurableSet,
      Measure.smul_apply, Measure.map_apply_of_aemeasurable hemeas hA,
      Measure.restrict_apply' e.open_source.measurableSet]
    congr 2
    ext t
    change (l (c (b t)) ∈ A ∧ b t ∈ c.source) ∧ t ∈ b.source ↔
      e t ∈ A ∧ t ∈ e.source
    constructor
    · rintro ⟨⟨htA, _⟩, hts⟩
      exact ⟨htA, heS.symm ▸ (hbS ▸ hts)⟩
    · rintro ⟨htA, hts⟩
      have htb : t ∈ b.source := hbS.symm ▸ (heS ▸ hts)
      exact ⟨⟨htA, hbT ▸ b.map_source htb⟩, htb⟩
  have hginj : Injective e.symm := by
    intro x y hxy
    exact e.symm.injOn (show x ∈ e.target from heT.symm ▸ mem_univ x)
      (show y ∈ e.target from heT.symm ▸ mem_univ y) hxy
  -- Apply the one-variable Jacobian theorem to the actual inverse on each
  -- measurable set, then return through the fixed isometry to the native model.
  have hJ : Measure.map e (volume.restrict e.source) =
      (volume : Measure ℝ).withDensity (fun z ↦ ENNReal.ofReal |deriv e.symm z|) := by
    ext A hA
    rw [Measure.map_apply_of_aemeasurable hemeas hA,
      Measure.restrict_apply' e.open_source.measurableSet, withDensity_apply _ hA]
    have hset : e ⁻¹' A ∩ e.source = e.symm '' A := by
      ext t
      constructor
      · rintro ⟨htA, hts⟩
        exact ⟨e t, htA, e.left_inv hts⟩
      · rintro ⟨z, hzA, rfl⟩
        have hzt : z ∈ e.target := heT.symm ▸ mem_univ z
        exact ⟨by simpa only [mem_preimage, e.right_inv hzt] using hzA,
          e.map_target hzt⟩
    rw [hset]
    have hder (z : ℝ) (_hz : z ∈ A) :
        HasDerivWithinAt e.symm (deriv e.symm z) A z :=
      (hgsmooth.differentiable (by simp) z).hasDerivAt.hasDerivWithinAt
    simpa only [lintegral_one, mul_one, Measure.restrict_apply_univ] using
      lintegral_image_eq_lintegral_abs_deriv_mul hA hder hginj.injOn (fun _ ↦ 1)
  have hJk : ENNReal.ofReal k • Measure.map e (volume.restrict e.source) =
      (volume : Measure ℝ).withDensity (fun z ↦ ENNReal.ofReal (q z)) := by
    rw [hJ]
    ext A hA
    rw [Measure.smul_apply, withDensity_apply _ hA, withDensity_apply _ hA]
    simp only [q, ENNReal.ofReal_mul hk.le, smul_eq_mul]
    rw [lintegral_const_mul]
    exact ((contDiff_infty_iff_deriv.mp hgsmooth).2.continuous.abs.measurable).ennreal_ofReal
  have hlw : Measure.map l ((volume : Measure V).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) =
      (volume : Measure ℝ).withDensity (fun z ↦ ENNReal.ofReal (q z)) := by
    ext A hA
    rw [Measure.map_apply l.continuous.measurable hA,
      withDensity_apply _ (l.continuous.measurable hA), withDensity_apply _ hA]
    exact l.measurePreserving.setLIntegral_comp_preimage hA
      hqsmooth.continuous.measurable.ennreal_ofReal
  have htarget : Measure.map c (fourierCircleMeasure.restrict c.source) =
      (volume : Measure V).withDensity (fun z ↦ ENNReal.ofReal (w z)) := by
    apply l.toHomeomorph.measurableEmbedding.map_injective
    change Measure.map l (Measure.map c (fourierCircleMeasure.restrict c.source)) =
      Measure.map l ((volume : Measure V).withDensity (fun z ↦ ENNReal.ofReal (w z)))
    rw [hscalar, hJk, hlw]
  refine ⟨w, hwsmooth.contDiffOn, fun z _hz ↦ hwpos z, ?_⟩
  change Measure.map c (fourierCircleMeasure.restrict c.source) =
    (volume.restrict c.target).withDensity (fun z ↦ ENNReal.ofReal (w z))
  simpa only [c, stereographic'_target, Measure.restrict_univ] using htarget

/-- A smooth section of this trivial line has a smooth scalar coordinate. -/
theorem contMDiff_fourierCircleSectionCoordinate
    (u : smoothSections (n := 1) (r := 1) FourierCircleLine) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) ∞
      (fun z : Circle ↦ u.val z 0) := by
  /- Evaluate IsSmoothSection in the specified global trivialization. Its
  base set is all of Circle, and its fiber coordinate is exactly u(z).
  Compose with evaluation at the unique Fin 1 coordinate, a continuous
  complex-linear and therefore real-smooth map. -/
  -- The native frame at one is the global trivialization on the entire circle.
  have hcoord : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 1))
      𝓘(ℝ, EuclideanSpace ℂ (Fin 1)) ∞ u.val := by
    have h := u.property (trivializationAt (EuclideanSpace ℂ (Fin 1)) FourierCircleLine
      (1 : Circle)) inferInstance
    exact contMDiffOn_univ.mp h
  -- Restrict the complex coordinate evaluation to the real scalar field for smoothness.
  exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 ↦ ℂ) 0).restrictScalars ℝ).contMDiff.comp
    hcoord

/-- Evaluate the same smooth section as an element of the original Fourier L² space. -/
def circleSmoothToFourierL2 :
    smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ] CircleFourierL2 :=
  let coordinate : smoothSections (n := 1) (r := 1) FourierCircleLine →ₗ[ℂ]
      C(AddCircle (2 * Real.pi), ℂ) :=
    { toFun := fun u ↦
        ⟨fun x ↦ u.val (AddCircle.homeomorphCircle' x) 0,
          (contMDiff_fourierCircleSectionCoordinate u).continuous.comp
            AddCircle.homeomorphCircle'.continuous⟩
      map_add' := fun u v ↦ by ext x; rfl
      map_smul' := fun c u ↦ by ext x; rfl }
  (ContinuousMap.toLp 2
    (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) ℂ).toLinearMap.comp
      coordinate

/-- The Fourier L² embedding retains every smooth section of the specified line. -/
theorem circleSmoothToFourierL2_injective :
    Function.Injective circleSmoothToFourierL2 := by
  /- Stage 1: normalized Haar measure has full support, so mathlib's
  ContinuousMap.toLp is injective. Equality of the embedded sections
  therefore gives equality of their continuous scalar coordinates.
  Stage 2: the positive angular homeomorphism is surjective. The unique
  coordinate determines a vector in the one-dimensional trivial fiber,
  hence determines the section at every point of the original Circle. -/
  intro u v h
  -- Haar full support identifies the same continuous functions from their L² images.
  have hcoord := ContinuousMap.toLp_injective
    (@AddCircle.haarAddCircle (2 * Real.pi) circlePeriodPositive) h
  -- The original angular homeomorphism and the single fiber coordinate recover the section.
  apply Subtype.ext
  funext z
  apply PiLp.ext
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  obtain ⟨x, rfl⟩ := AddCircle.homeomorphCircle'.surjective z
  exact congrArg (fun f : C(AddCircle (2 * Real.pi), ℂ) ↦ f x) hcoord

end AtiyahSinger
