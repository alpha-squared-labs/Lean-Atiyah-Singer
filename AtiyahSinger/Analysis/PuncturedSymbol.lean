/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereHomotopy
public import AtiyahSinger.Geometry.CotangentSupport
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Continuous off-zero symbols and jointly continuous families

Public module ID: M0904.

These are actual sections of the original Hom bundle over nonzero cotangent
vectors. No growth, degree, or smoothness condition is built into continuity.
Radial families use positive scalars and remain pointwise invertible off the
same zero section.
Sources: SG III.1 (1.6), III.13 (13.1); continuity and radial comparison details are
project supplements.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20

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

/-- The actual Hom total-space section away from zero. -/
def puncturedSymbolTotal (a : GlobalSymbolFunction (n := n) E F) :
    PuncturedCotangentBundle (n := n) (M := M) → TotalSpace
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))
      (fun x ↦ E x →L[ℂ] F x) :=
  fun z ↦ ⟨z.val.proj, a z.val.proj z.val.snd⟩

/-- Continuity of the symbol as an actual off-zero Hom section. -/
def IsContinuousOffZeroGlobalSymbol (a : GlobalSymbolFunction (n := n) E F) : Prop :=
  Continuous (puncturedSymbolTotal (r := r) (q := q) a)

/-- Off-zero equality transfers continuity without constraining zero-section values. -/
theorem IsContinuousOffZeroGlobalSymbol.congr {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a)
    (hab : ∀ x ξ, ξ ≠ 0 → a x ξ = b x ξ) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) b := by
  /- The equality identifies the actual total Hom maps on the punctured domain. Substitute that
  equality into continuity; the unused values at zero never enter the argument. -/
  apply Continuous.congr ha
  intro z
  exact congrArg (TotalSpace.mk' _ z.val.proj) (hab _ _ z.property)

/-- The zero Hom section is continuous off zero. -/
theorem isContinuousOffZeroGlobalSymbol_zero :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) (0 : GlobalSymbolFunction (n := n) E F) := by
  /- Compose the zero section of the original Hom vector bundle with the continuous punctured
  cotangent projection. That composite is the displayed total map. -/
  exact (Bundle.Trivialization.continuous_zeroSection ℂ).comp
    ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val)

/-- Addition is continuous in the original off-zero Hom bundle. -/
theorem IsContinuousOffZeroGlobalSymbol.add {a b : GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) a)
    (hb : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) b) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) (a + b) := by
  /- Both total Hom maps lie over the same base projection. Continuous fiberwise addition of
  the Hom vector bundle therefore gives continuity of their sum. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousOffZeroGlobalSymbol at *
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (ha.continuousAt (x := p))
  have h₂ := (FiberBundle.continuousAt_totalSpace H _).mp (hb.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  -- In this chart, addition is the ordinary continuous addition of linear maps.
  apply (h₁.2.add h₂.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.val.proj))] with y hy
  exact (e.linear ℂ hy).1 (a y.val.proj y.val.snd) (b y.val.proj y.val.snd)

/-- Constant scalar multiplication preserves off-zero continuity. -/
theorem IsContinuousOffZeroGlobalSymbol.smul {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) a)
    (c : ℂ) : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q)
    (c • a) := by
  /- Compose the continuous total Hom map with scalar multiplication by c in that vector
  bundle. The base point is unchanged, including when c is zero. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousOffZeroGlobalSymbol at *
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (ha.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  -- The scalar and the fiber coordinate vary continuously in this same chart.
  apply ((continuousAt_const (y := c)).smul h₁.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.val.proj))] with y hy
  exact (e.linear ℂ hy).2 c (a y.val.proj y.val.snd)

/-- Inversion of an elliptic off-zero Hom section is continuous. -/
theorem IsContinuousOffZeroGlobalSymbol.inverse {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a) (hi : IsEllipticGlobalSymbol E F a) :
    IsContinuousOffZeroGlobalSymbol (r := q) (q := r) (globalSymbolInverse a) := by
  /- In a pair of local frames, invertibility forces equal fiber dimensions at the point.
  Shrink to those fixed frames and use continuity of matrix inversion on the invertible
  locus. The inverse formulas agree under frame changes. On an empty punctured domain the
  assertion is vacuous, with no global equality of ranks inferred. -/
  classical
  change Continuous (puncturedSymbolTotal (r := q) (q := r) (globalSymbolInverse a))
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.val.proj
  have hsource := (continuousAt_hom_bundle (RingHom.id ℂ)
    (puncturedSymbolTotal (r := r) (q := q) a) (x₀ := z₀)).mp ha.continuousAt
  have hbase := hsource.1
  let A (z : PuncturedCotangentBundle (n := n) (M := M)) :=
    (f.continuousLinearMapAt ℂ z.val.proj).comp
      ((a z.val.proj z.val.snd).comp (e.symmL ℂ z.val.proj))
  have hi : (A z₀).IsInvertible := by
    have ha : (a z₀.val.proj z₀.val.snd).IsInvertible :=
      hi.isInvertible (r := r) (q := q) _ _ z₀.property
    dsimp [A]
    rw [← f.coe_continuousLinearEquivAt_eq' (R := ℂ)
      (mem_baseSet_trivializationAt _ _ _),
      ← e.symm_continuousLinearEquivAt_eq' (R := ℂ)
        (mem_baseSet_trivializationAt _ _ _)]
    exact ContinuousLinearMap.isInvertible_equiv.comp
      (ha.comp ContinuousLinearMap.isInvertible_equiv)
  -- Invert the continuous coordinate map, then return to the original moving fibers.
  have hinverse := (hi.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hsource.2
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase, hinverse.congr_of_eventuallyEq ?_⟩
  filter_upwards [hbase.preimage_mem_nhds (e.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _)),
    hbase.preimage_mem_nhds (f.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt _ _ _))] with z hez hfz
  change (e.continuousLinearMapAt ℂ z.val.proj).comp
    ((a z.val.proj z.val.snd).inverse.comp (f.symmL ℂ z.val.proj)) = (A z).inverse
  change z.val.proj ∈ e.baseSet at hez
  change z.val.proj ∈ f.baseSet at hfz
  dsimp [A]
  rw [← e.coe_continuousLinearEquivAt_eq' (R := ℂ) hez,
    ← e.symm_continuousLinearEquivAt_eq' (R := ℂ) hez,
    ← f.coe_continuousLinearEquivAt_eq' (R := ℂ) hfz,
    ← f.symm_continuousLinearEquivAt_eq' (R := ℂ) hfz]
  simp only [ContinuousLinearMap.inverse_equiv_comp,
    ContinuousLinearMap.inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    ContinuousLinearMap.comp_assoc]

include hM in
/-- Chartwise smoothness gives actual total-space continuity off zero. -/
theorem IsSmoothOffZeroGlobalSymbol.continuous
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) a := by
  /- Around each nonzero covector choose valid manifold and bundle charts. The chartwise smooth
  function is continuous on the open punctured chart domain. The continuous cotangent
  coordinate equivalence and Hom trivialization convert this into total-space continuity
  locally. These neighborhoods cover the punctured total space; no smoothness at zero is
  needed. -/
  classical
  change Continuous (puncturedSymbolTotal (r := r) (q := q) a)
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let c := chartAt (EuclideanSpace ℝ (Fin n)) z₀.val.proj
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E z₀.val.proj
  let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F z₀.val.proj
  let t := trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I) z₀.val.proj
  have hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M := chart_mem_atlas _ _
  have hx₀ : z₀.val.proj ∈ c.source := mem_chart_source _ _
  have hsource := (continuousAt_hom_bundle (RingHom.id ℝ)
    (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦ z.val) (x₀ := z₀)).mp
      continuous_subtype_val.continuousAt
  have hbase := hsource.1
  have hchart : ContinuousAt
      (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦ c z.val.proj) z₀ :=
    (c.continuousAt hx₀).comp
      (f := fun z : PuncturedCotangentBundle (n := n) (M := M) ↦ z.val.proj) hbase
  have hξ : ContinuousAt (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
      z.val.snd.comp (t.symmL ℝ z.val.proj)) z₀ := by
    have h := hsource.2
    change ContinuousAt (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
      ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ z.val.proj).comp
        (z.val.snd.comp (t.symmL ℝ z.val.proj))) z₀ at h
    simpa only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp] using h
  -- The moving covector is evaluated on the inverse chart differential in native coordinates.
  have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
  have hd₀ := ((contMDiffAt_symm_of_mem_maximalAtlas hcm (c.map_source hx₀)).mfderiv_const
    (m := (∞ : WithTop ℕ∞)) (by simp)).continuousAt
  unfold inTangentCoordinates at hd₀
  simp only [c.left_inv hx₀] at hd₀
  have hd := hd₀.comp
    (f := fun z : PuncturedCotangentBundle (n := n) (M := M) ↦ c z.val.proj) hchart
  have hdual (v : EuclideanSpace ℝ (Fin n)) : ContinuousAt
      (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
        z.val.snd ((mfderiv I I c.symm (c z.val.proj)) v)) z₀ := by
    apply (hξ.clm_apply (hd.clm_apply (continuousAt_const (y := v)))).congr_of_eventuallyEq
    filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
    dsimp only [Function.comp_apply, ContinuousLinearMap.inCoordinates, Function.id_def]
    simp only [TangentBundle.symmL_model_space]
    erw [c.left_inv hz]
    change z.val.snd ((mfderiv I I c.symm (c z.val.proj)) v) =
      z.val.snd (t.symmL ℝ z.val.proj (t.continuousLinearMapAt ℝ z.val.proj
        ((mfderiv I I c.symm (c z.val.proj)) v)))
    exact congrArg z.val.snd
      (t.symmL_continuousLinearMapAt (R := ℝ) hz
        ((mfderiv I I c.symm (c z.val.proj)) v)).symm
  have hcoord : ContinuousAt (fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
      covectorInChart c z.val.proj z.val.snd) z₀ := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    exact hdual (EuclideanSpace.single j 1)
  -- The original chartwise smoothness is now composed with these actual cotangent coordinates.
  have hne (z : PuncturedCotangentBundle (n := n) (M := M)) (hz : z.val.proj ∈ c.source) :
      covectorInChart c z.val.proj z.val.snd ≠ 0 := by
    intro hzero
    have hi := covectorFromChart_covectorInChart c hc z.val.proj hz z.val.snd
    rw [hzero] at hi
    have hzero' : covectorFromChart c z.val.proj 0 = 0 := by
      ext v
      simp [covectorFromChart]
      rfl
    exact z.property (hi.symm.trans hzero')
  have hdomain : (c z₀.val.proj, covectorInChart c z₀.val.proj z₀.val.snd) ∈
      symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0} := by
    refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, hne z₀ hx₀⟩ <;>
      simpa only [Set.mem_preimage, c.left_inv hx₀] using mem_baseSet_trivializationAt _ _ _
  have hvalue := ((ha c hc e f).continuousOn.continuousAt
    (((isOpen_symbolChartDomain E F c e f).prod isOpen_ne).mem_nhds hdomain)).comp
      (f := fun z : PuncturedCotangentBundle (n := n) (M := M) ↦
        (c z.val.proj, covectorInChart c z.val.proj z.val.snd)) (hchart.prodMk hcoord)
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase, ?_⟩
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
  change (f.continuousLinearMapAt ℂ z.val.proj).comp
    ((a z.val.proj z.val.snd).comp (e.symmL ℂ z.val.proj)) =
    globalSymbolInChart E F a c e f (c z.val.proj)
      (covectorInChart c z.val.proj z.val.snd)
  rw [globalSymbolInChart_covectorInChart E F _ c hc e f z.val.proj hz]

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Continuous off-zero symbols restrict to continuous cosphere symbols. -/
theorem IsContinuousOffZeroGlobalSymbol.cosphereRestriction
    {a : GlobalSymbolFunction (n := n) E F} (ha : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) a) :
    IsContinuousCosphereSymbol (r := r) (q := q) g (cosphereRestriction g a) := by
  /- Compose the punctured total map with the continuous cosphere inclusion into nonzero
  covectors. Its base and fiber value coincide with the original restricted symbol. -/
  exact ha.comp g.continuous_cosphereInclusion

/-- Continuous cosphere symbols extend continuously off zero at every real degree. -/
theorem isContinuousOffZeroGlobalSymbol_cosphereExtension (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) (cosphereExtension g m a) := by
  /- Compose the continuous Hom section with radial normalization. Multiply it by the
  continuous positive function length raised to m on nonzero covectors. Continuity at zero
  is neither required nor asserted. -/
  -- Pull the given section back along radial normalization.
  have hpre := ha.comp g.continuous_radial
  have hweight : Continuous (fun p : PuncturedCotangentBundle (n := n) (M := M) ↦
      ((g.length p.val.proj p.val.snd ^ m : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply (g.continuous_length.comp continuous_subtype_val).rpow_const
    intro p
    exact Or.inl (g.length_pos _ _ p.property).ne'
  -- The scalar product is continuous in each native Hom trivialization.
  unfold IsContinuousOffZeroGlobalSymbol
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (hpre.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  apply (hweight.continuousAt.smul h₁.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.val.proj))] with y hy
  change (e ⟨y.val.proj, cosphereExtension g m a y.val.proj y.val.snd⟩).2 =
    ((g.length y.val.proj y.val.snd ^ m : ℝ) : ℂ) •
      (e ⟨y.val.proj, a (g.radial y)⟩).2
  rw [cosphereExtension_of_ne_zero g m a _ _ y.property]
  exact (e.linear ℂ hy).2 _ _

/-- Joint continuity of off-zero symbols, with an arbitrary parameter space. -/
def IsContinuousOffZeroSymbolFamily {Z : Type*} [TopologicalSpace Z]
    (a : Z → GlobalSymbolFunction (n := n) E F) : Prop :=
  Continuous (fun p : Z × PuncturedCotangentBundle (n := n) (M := M) ↦
    puncturedSymbolTotal (r := r) (q := q) (a p.1) p.2)

/-- Joint continuity gives continuity at each parameter. -/
theorem IsContinuousOffZeroSymbolFamily.slice {Z : Type*} [TopologicalSpace Z]
    {a : Z → GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroSymbolFamily (r := r) (q := q) a) (z : Z) :
    IsContinuousOffZeroGlobalSymbol (r := r) (q := q) (a z) := by
  /- Precompose the joint total-space map with insertion of the fixed parameter z. The second
  variable remains the original nonzero covector. -/
  exact ha.comp (continuous_const.prodMk continuous_id)

/-- A constant family of continuous symbols is jointly continuous. -/
theorem IsContinuousOffZeroGlobalSymbol.family_const {Z : Type*} [TopologicalSpace Z]
    {a : GlobalSymbolFunction (n := n) E F} (ha : IsContinuousOffZeroGlobalSymbol (r := r)
    (q := q) a) :
    IsContinuousOffZeroSymbolFamily (r := r) (q := q) (fun _ : Z ↦ a) := by
  /- Precompose the continuous punctured symbol map with the second projection from the
  product. The parameter is ignored, so the result is jointly continuous. -/
  exact ha.comp continuous_snd

/-- Continuous reparameterization preserves joint continuity. -/
theorem IsContinuousOffZeroSymbolFamily.comp {Z W : Type*}
    [TopologicalSpace Z] [TopologicalSpace W]
    {a : Z → GlobalSymbolFunction (n := n) E F}
    (ha : IsContinuousOffZeroSymbolFamily (r := r) (q := q) a)
    (f : W → Z) (hf : Continuous f) :
    IsContinuousOffZeroSymbolFamily (r := r) (q := q) (a ∘ f) := by
  /- Precompose the joint Hom map with the product of f and identity on the nonzero cotangent
  domain. This preserves the fiber base and makes no support change. -/
  exact Continuous.comp ha ((hf.comp continuous_fst).prodMk continuous_snd)

/-- Radial extension of a continuous cosphere family is jointly continuous off zero. -/
theorem IsContinuousCosphereFamily.extension {Z : Type*} [TopologicalSpace Z]
    {a : Z → CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a) (m : ℝ) :
    IsContinuousOffZeroSymbolFamily (r := r) (q := q)
      (fun z ↦ cosphereExtension g m (a z)) := by
  /- Precompose jointly with identity on the parameter and continuous radial normalization on
  nonzero covectors. Multiply by the continuous positive radial power, pulled back along the
  second projection. -/
  -- The parameter is unchanged while the covector is normalized radially.
  have hpre : Continuous (fun p : Z × PuncturedCotangentBundle (n := n) (M := M) ↦
      cosphereSymbolTotal (r := r) (q := q) g (a p.1) (g.radial p.2)) :=
    Continuous.comp ha (continuous_fst.prodMk (g.continuous_radial.comp continuous_snd))
  have hweight : Continuous (fun p : Z × PuncturedCotangentBundle (n := n) (M := M) ↦
      ((g.length p.2.val.proj p.2.val.snd ^ m : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply ((g.continuous_length.comp continuous_subtype_val).comp continuous_snd).rpow_const
    intro p
    exact Or.inl (g.length_pos _ _ p.2.property).ne'
  -- A single local Hom frame handles the jointly varying scalar and section.
  unfold IsContinuousOffZeroSymbolFamily
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.2.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (hpre.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  apply (hweight.continuousAt.smul h₁.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.2.val.proj))] with y hy
  change (e ⟨y.2.val.proj, cosphereExtension g m (a y.1) y.2.val.proj y.2.val.snd⟩).2 =
    ((g.length y.2.val.proj y.2.val.snd ^ m : ℝ) : ℂ) •
      (e ⟨y.2.val.proj, a y.1 (g.radial y.2)⟩).2
  rw [cosphereExtension_of_ne_zero g m (a y.1) _ _ y.2.property]
  exact (e.linear ℂ hy).2 _ _

/-- Vary the homogeneous degree by a positive radial scalar. -/
def cosphereDegreeFamily (m l : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) (t : unitInterval) :
    GlobalSymbolFunction (n := n) E F :=
  cosphereExtension g ((1 - (t : ℝ)) * m + (t : ℝ) * l) a

/-- The radial degree family begins at degree m. -/
theorem cosphereDegreeFamily_zero (m l : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereDegreeFamily g m l a 0 = cosphereExtension g m a := by
  /- Evaluate the affine degree at parameter zero. The resulting real exponent is m, and the
  radial extension formula including its fixed zero branch is unchanged. -/
  simp [cosphereDegreeFamily]

/-- The radial degree family ends at degree l. -/
theorem cosphereDegreeFamily_one (m l : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereDegreeFamily g m l a 1 = cosphereExtension g l a := by
  /- Evaluate the affine degree at parameter one. Its exponent equals l, giving equality of the
  actual global functions, not merely their restrictions. -/
  simp [cosphereDegreeFamily]

/-- The radial degree family is jointly continuous off zero. -/
theorem isContinuousOffZeroSymbolFamily_degree (m l : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a) :
    IsContinuousOffZeroSymbolFamily (r := r) (q := q) (cosphereDegreeFamily g m l a) := by
  /- The positive length and continuous affine exponent define a jointly continuous real power
  on the punctured domain. Multiplying the radially pulled-back original Hom section by this
  scalar gives the stated family. -/
  -- The parameter is unchanged while the covector is normalized radially.
  have hpre : Continuous (fun p : unitInterval × PuncturedCotangentBundle (n := n) (M := M) ↦
      cosphereSymbolTotal (r := r) (q := q) g a (g.radial p.2)) :=
    Continuous.comp ha (g.continuous_radial.comp continuous_snd)
  have hweight : Continuous (fun p : unitInterval × PuncturedCotangentBundle (n := n) (M := M) ↦
      ((g.length p.2.val.proj p.2.val.snd ^ ((1 - (p.1 : ℝ)) * m + (p.1 : ℝ) * l) : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply Continuous.rpow
      ((g.continuous_length.comp continuous_subtype_val).comp continuous_snd)
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        continuous_const).add
        ((continuous_subtype_val.comp continuous_fst).mul continuous_const))
    intro p
    exact Or.inl (g.length_pos _ _ p.2.property).ne'
  -- A single local Hom frame handles the jointly varying scalar and section.
  unfold IsContinuousOffZeroSymbolFamily
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.2.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (hpre.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  apply (hweight.continuousAt.smul h₁.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.2.val.proj))] with y hy
  change (e ⟨y.2.val.proj,
    cosphereExtension g ((1 - (y.1 : ℝ)) * m + (y.1 : ℝ) * l) a
      y.2.val.proj y.2.val.snd⟩).2 =
    ((g.length y.2.val.proj y.2.val.snd ^ ((1 - (y.1 : ℝ)) * m + (y.1 : ℝ) * l) : ℝ) : ℂ) •
      (e ⟨y.2.val.proj, a (g.radial y.2)⟩).2
  rw [cosphereExtension_of_ne_zero g _ a _ _ y.2.property]
  exact (e.linear ℂ hy).2 _ _

/-- Every time of the degree family remains elliptic. -/
theorem isEllipticGlobalSymbol_degree (m l : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (hi : IsEllipticCosphereSymbol g a) (t : unitInterval) :
    IsEllipticGlobalSymbol E F (cosphereDegreeFamily g m l a t) := by
  /- At every nonzero covector the radial scalar is strictly positive at every real exponent.
  Its product with the invertible unit-direction map is invertible. The zero section is the
  same possible failure set for all parameters. -/
  exact (isEllipticGlobalSymbol_cosphereExtension_iff g _ a).mpr hi

end AtiyahSinger
