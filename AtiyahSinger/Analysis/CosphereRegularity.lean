/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereSymbol
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology

import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Continuous and smooth cosphere sections

Public module ID: M0420.

Continuity is that of the pulled-back Hom bundle. Smoothness is expressed by
the standard degree-zero radial extension criterion, equivalent to smoothness
on the unit sphere bundle. This avoids installing redundant manifold structures.
The smooth section topology is the topology induced by this explicit extension
into the previously defined punctured C-infinity seminorm space. It is not the
C-zero topology. These are project bridges for the regular homotopy argument
in SG III.7.10--7.11. The intrinsic regularity and actual bundle continuity
are proved below. Arbitrary-degree extension and restriction are continuous for
the original compact mixed-derivative topologies by the fixed smooth multiplier theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20


set_option linter.unusedSectionVars false

section MetricCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
/-- Metric length is smooth in the original cotangent chart away from zero.
This supplies the smooth weights for degree changes and radial normalization. -/
theorem SmoothCotangentMetric.contDiffOn_length_covectorFromChart
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    ContDiffOn ℝ ∞
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) ↦
        g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2))
      (c.target ×ˢ {ξ | ξ ≠ 0}) := by
  -- The original inverse chart and its differential give a smooth cotangent map.
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
  intro p hp
  have hbase : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) I ∞
      (fun p ↦ c.symm p.1) p :=
    (contMDiffAt_symm_of_mem_maximalAtlas hcm hp.1).comp p contDiffAt_fst.contMDiffAt
  have hd := ((contMDiffAt_of_mem_maximalAtlas hcm (c.map_target hp.1)).mfderiv_const
    (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase
  have hinner : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, CotangentModel n) ∞ (fun p ↦ innerSL ℝ p.2) p :=
    (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
  have hmap : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (I.prod 𝓘(ℝ, CotangentModel n)) ∞
      (fun p ↦ (⟨c.symm p.1, covectorFromChart c (c.symm p.1) p.2⟩ :
        CotangentTotalSpace)) p := by
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨hbase, ?_⟩
    apply (hinner.clm_comp hd).congr_of_eventuallyEq
    filter_upwards with z
    ext v
    simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
      Function.id_def, ContinuousLinearMap.comp_apply, I]
    rfl
  -- Coordinate injectivity puts this map in the original punctured cotangent bundle.
  have hne (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (hz : z ∈ c.target ×ˢ {ξ | ξ ≠ 0}) : covectorFromChart c (c.symm z.1) z.2 ≠ 0 := by
    intro hzero
    have hi := covectorInChart_covectorFromChart c hc (c.symm z.1) (c.map_target hz.1) z.2
    rw [hzero] at hi
    have hzcoord : covectorInChart c (c.symm z.1) 0 = 0 := by ext j; rfl
    exact hz.2 (hi.symm.trans hzcoord)
  -- Compose with metric length using the already established native smooth metric theorem.
  have hlen := (g.contMDiffOn_length _ (hne p hp)).comp p
    (hmap.contMDiffWithinAt (s := c.target ×ˢ {ξ | ξ ≠ 0})) hne
  exact hlen.contDiffWithinAt

end MetricCoordinates

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
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Smoothness of a cosphere section via its degree-zero radial extension. -/
def IsSmoothCosphereSymbol (a : CosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g 0 a)

/-- Smooth cosphere data extend smoothly at every real homogeneous degree. -/
theorem isSmoothOffZeroGlobalSymbol_cosphereExtension_iff (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g m a) ↔
      IsSmoothCosphereSymbol (r := r) (q := q) g a := by
  /- Off zero, the degree-m extension is the degree-zero extension
  multiplied by the smooth positive function length^m. Multiplication by length^(-m)
  gives the converse. Smooth cotangent frame changes identify these intrinsic formulas. -/
  -- Multiplying by a positive smooth length weight changes the homogeneous degree.
  have hchange (k l : ℝ)
      (h : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g l a)) :
      IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g (k + l) a) := by
    intro c hc e f _ _
    let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0}
    let w (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)
    have hne (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
        (hp : p ∈ U) : covectorFromChart c (c.symm p.1) p.2 ≠ 0 := by
      intro hz
      have hi := covectorInChart_covectorFromChart c hc (c.symm p.1)
        (c.map_target hp.1.1.1) p.2
      rw [hz] at hi
      have hzcoord : covectorInChart c (c.symm p.1) 0 = 0 := by ext j; rfl
      exact hp.2 (hi.symm.trans hzcoord)
    have hw : ContDiffOn ℝ ∞ w U :=
      (g.contDiffOn_length_covectorFromChart c hc).mono (fun _ hp ↦ ⟨hp.1.1.1, hp.2⟩)
    have hpow : ContDiffOn ℝ ∞ (fun p ↦ ((w p ^ k : ℝ) : ℂ)) U :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hw.rpow_const_of_ne (fun p hp ↦ (g.length_pos _ _ (hne p hp)).ne'))
    apply (hpow.smul (h c hc e f)).congr
    intro p hp
    have hval : cosphereExtension g (k + l) a (c.symm p.1)
        (covectorFromChart c (c.symm p.1) p.2) =
        ((w p ^ k : ℝ) : ℂ) • cosphereExtension g l a (c.symm p.1)
          (covectorFromChart c (c.symm p.1) p.2) := by
      rw [cosphereExtension_of_ne_zero g (k + l) a _ _ (hne p hp),
        cosphereExtension_of_ne_zero g l a _ _ (hne p hp),
        Real.rpow_add (g.length_pos _ _ (hne p hp)), Complex.ofReal_mul, mul_smul]
      rfl
    change globalSymbolInChart E F (cosphereExtension g (k + l) a) c e f p.1 p.2 =
      ((w p ^ k : ℝ) : ℂ) • globalSymbolInChart E F (cosphereExtension g l a) c e f p.1 p.2
    simp only [globalSymbolInChart, hval, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.comp_smul]
  -- The inverse degree change uses the same metric and original section.
  constructor
  · intro h
    change IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g 0 a)
    simpa only [neg_add_cancel] using hchange (-m) m h
  · intro h
    simpa only [add_zero] using hchange m 0 h

/-- Restriction of smooth punctured data is smooth on the cosphere. -/
theorem isSmoothCosphereSymbol_restriction (a : GlobalSymbolFunction (n := n) E F)
    (ha : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F a) :
    IsSmoothCosphereSymbol (r := r) (q := q) g (cosphereRestriction g a) := by
  /- The degree-zero extension of the restriction is a evaluated at the
  normalized covector. The normalization is smooth off zero and respects the actual
  base point. Compose in each valid bundle chart; no homogeneity of a is required. -/
  -- In the same chart, radial normalization only rescales the frequency coordinate.
  intro c hc e f _ _
  let U : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0}
  let w (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    g.length (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2)
  have hne (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      (hp : p ∈ U) : covectorFromChart c (c.symm p.1) p.2 ≠ 0 := by
    intro hz
    have hi := covectorInChart_covectorFromChart c hc (c.symm p.1)
      (c.map_target hp.1.1.1) p.2
    rw [hz] at hi
    have hzcoord : covectorInChart c (c.symm p.1) 0 = 0 := by ext j; rfl
    exact hp.2 (hi.symm.trans hzcoord)
  have hw : ContDiffOn ℝ ∞ w U :=
    (g.contDiffOn_length_covectorFromChart c hc).mono (fun _ hp ↦ ⟨hp.1.1.1, hp.2⟩)
  have hwne (p) (hp : p ∈ U) : w p ≠ 0 := (g.length_pos _ _ (hne p hp)).ne'
  have hrad : ContDiffOn ℝ ∞ (fun p ↦ (p.1, (w p)⁻¹ • p.2)) U :=
    contDiffOn_fst.prodMk ((hw.inv hwne).smul contDiffOn_snd)
  have hmaps : Set.MapsTo (fun p ↦ (p.1, (w p)⁻¹ • p.2)) U U := by
    intro p hp
    exact ⟨hp.1, smul_ne_zero (inv_ne_zero (hwne p hp)) hp.2⟩
  -- Pull back the original punctured smooth function along this smooth normalization.
  apply ((ha c hc e f).comp hrad hmaps).congr
  intro p hp
  change globalSymbolInChart E F (cosphereExtension g 0 (cosphereRestriction g a))
    c e f p.1 p.2 = globalSymbolInChart E F a c e f p.1 ((w p)⁻¹ • p.2)
  have hscale : covectorFromChart c (c.symm p.1) ((w p)⁻¹ • p.2) =
      g.normalize (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2) := by
    ext v
    simp [covectorFromChart, SmoothCotangentMetric.normalize, w]
    rfl
  simp only [globalSymbolInChart, cosphereExtension_of_ne_zero g 0 _ _ _ (hne p hp),
    Real.rpow_zero, Complex.ofReal_one, cosphereRestriction,
    SmoothCotangentMetric.radial, hscale]
  erw [one_smul]

set_option linter.style.multiGoal false in

/-- Smooth cosphere sections are continuous in the actual bundle topology. -/
theorem IsSmoothCosphereSymbol.continuous
    {a : CosphereSymbolFunction (E := E) (F := F) g}
      (ha : IsSmoothCosphereSymbol (r := r) (q := q) g a) :
    IsContinuousCosphereSymbol (r := r) (q := q) g a := by
  /- Smooth radial extension is continuous off zero in all compatible
  frames. Restrict along the continuous unit-covector inclusion, where the extension
  equals a. This gives continuity into the Hom total space, not only each fiber. -/
  classical
  change Continuous (cosphereSymbolTotal (r := r) (q := q) g a)
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
    (fun z : CosphereBundle g ↦ z.val) (x₀ := z₀)).mp
      continuous_subtype_val.continuousAt
  have hbase := hsource.1
  have hchart : ContinuousAt (fun z : CosphereBundle g ↦ c z.val.proj) z₀ :=
    (c.continuousAt hx₀).comp (f := fun z : CosphereBundle g ↦ z.val.proj) hbase
  have hξ : ContinuousAt (fun z : CosphereBundle g ↦ z.val.snd.comp (t.symmL ℝ z.val.proj)) z₀ := by
    have h := hsource.2
    change ContinuousAt (fun z : CosphereBundle g ↦
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
  have hd := hd₀.comp (f := fun z : CosphereBundle g ↦ c z.val.proj) hchart
  have hdual (v : EuclideanSpace ℝ (Fin n)) : ContinuousAt (fun z : CosphereBundle g ↦
      z.val.snd ((mfderiv I I c.symm (c z.val.proj)) v)) z₀ := by
    apply (hξ.clm_apply (hd.clm_apply continuousAt_const)).congr_of_eventuallyEq
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
  have hcoord : ContinuousAt (fun z : CosphereBundle g ↦
      covectorInChart c z.val.proj z.val.snd) z₀ := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    exact hdual (EuclideanSpace.single j 1)
  -- The inverse chart identities keep the moving coordinate covector off the zero section.
  have hne (z : CosphereBundle g) (hz : z.val.proj ∈ c.source) :
      covectorInChart c z.val.proj z.val.snd ≠ 0 := by
    intro hzero
    have hi := covectorFromChart_covectorInChart c hc z.val.proj hz z.val.snd
    rw [hzero] at hi
    have hzero' : covectorFromChart c z.val.proj 0 = 0 := by
      ext v
      simp [covectorFromChart]
      rfl
    exact g.cosphere_ne_zero z (hi.symm.trans hzero')
  have hdomain : (c z₀.val.proj, covectorInChart c z₀.val.proj z₀.val.snd) ∈
      symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0} := by
    refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, hne z₀ hx₀⟩ <;>
      simpa only [Set.mem_preimage, c.left_inv hx₀] using mem_baseSet_trivializationAt _ _ _
  have hvalue := ((ha c hc e f).continuousOn.continuousAt
    (((isOpen_symbolChartDomain E F c e f).prod isOpen_ne).mem_nhds hdomain)).comp
      (f := fun z : CosphereBundle g ↦
        (c z.val.proj, covectorInChart c z.val.proj z.val.snd)) (hchart.prodMk hcoord)
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase, ?_⟩
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
  change (f.continuousLinearMapAt ℂ z.val.proj).comp ((a z).comp (e.symmL ℂ z.val.proj)) =
    globalSymbolInChart E F (cosphereExtension g 0 a) c e f (c z.val.proj)
      (covectorInChart c z.val.proj z.val.snd)
  rw [globalSymbolInChart_covectorInChart E F _ c hc e f z.val.proj hz]
  have hrestrict := congrFun (cosphereRestriction_extension g 0 a) z
  change cosphereExtension g 0 a z.val.proj z.val.snd = a z at hrestrict
  rw [hrestrict]

/-- The zero cosphere section is smooth. -/
theorem isSmoothCosphereSymbol_zero :
    IsSmoothCosphereSymbol (r := r) (q := q) g
      (0 : CosphereSymbolFunction (E := E) (F := F) g) := by
  /- The radial extension of zero is identically zero, including its
  chosen zero-section value. Its coordinate matrices are smooth on every punctured chart. -/
  change IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g 0 0)
  have hzero : cosphereExtension (E := E) (F := F) g 0 0 = 0 := by
    ext x ξ v
    by_cases hξ : ξ = 0
    · subst ξ
      simp [cosphereExtension_zero_covector]
    · simp [cosphereExtension_of_ne_zero g 0 0 x ξ hξ]
      rfl
  rw [hzero]
  exact isSmoothOffZeroGlobalSymbol_zero E F

/-- Smooth cosphere sections are closed under addition. -/
theorem IsSmoothCosphereSymbol.add
    {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsSmoothCosphereSymbol (r := r) (q := q) g a)
      (hb : IsSmoothCosphereSymbol (r := r) (q := q) g b) :
    IsSmoothCosphereSymbol (r := r) (q := q) g (a + b) := by
  /- Radial extension commutes with addition. In every valid chart its
  coordinate expression is the sum of two smooth functions on the same punctured domain. -/
  change IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g 0 (a + b))
  rw [cosphereExtension_add]
  exact IsSmoothOffZeroGlobalSymbol.add ha hb

/-- Smooth cosphere sections are closed under complex scalar multiplication. -/
theorem IsSmoothCosphereSymbol.smul (c : ℂ)
    {a : CosphereSymbolFunction (E := E) (F := F) g}
      (ha : IsSmoothCosphereSymbol (r := r) (q := q) g a) :
    IsSmoothCosphereSymbol (r := r) (q := q) g (c • a) := by
  /- Radial extension commutes with complex scalar multiplication.
  Constant complex multiplication is real smooth in the finite-dimensional Hom model. -/
  change IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F (cosphereExtension g 0 (c • a))
  rw [cosphereExtension_smul]
  exact IsSmoothOffZeroGlobalSymbol.smul c ha

/-- The standard vector space of smooth sections on the cosphere. -/
def smoothCosphereSymbolSpace : Submodule ℂ (CosphereSymbolFunction (E := E) (F := F) g) where
  carrier := {a | IsSmoothCosphereSymbol (r := r) (q := q) g a}
  zero_mem' := isSmoothCosphereSymbol_zero g
  add_mem' := fun ha hb ↦ IsSmoothCosphereSymbol.add g ha hb
  smul_mem' := fun c _ ha ↦ IsSmoothCosphereSymbol.smul g c ha

/-- The actual homogeneous smooth extension, carrying separately stated certificates. -/
def smoothCosphereExtension (m : ℝ) (a : smoothCosphereSymbolSpace (r := r) (q := q)
      (E := E) (F := F) g) :
    homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m :=
  ⟨cosphereExtension g m a.val,
    (isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g m a.val).2 a.property,
    isHomogeneousGlobalSymbol_cosphereExtension g m a.val⟩

/-- Restriction of a smooth homogeneous symbol to the actual smooth cosphere section. -/
def smoothCosphereRestriction (m : ℝ)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) :
    smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g :=
  ⟨cosphereRestriction g a.val, isSmoothCosphereSymbol_restriction g a.val a.property.1⟩

attribute [local instance] homogeneousSymbolTopology

/-- The usual smooth topology, transported by degree-zero radial extension. -/
@[instance_reducible]
def smoothCosphereSymbolTopology :
    TopologicalSpace (smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g) :=
  TopologicalSpace.induced (smoothCosphereExtension (r := r) (q := q) g 0) inferInstance

attribute [local instance] smoothCosphereSymbolTopology

set_option maxHeartbeats 1500000 in

set_option backward.isDefEq.respectTransparency false in
-- Local multilinear curry isometries retain the same real normed spaces through dependent degrees.
omit hE hF in
/-- A fixed punctured-smooth scalar multiplier is continuous in the original mixed-derivative
symbol topologies. The formula is required only off zero; arbitrary zero-section values are
unmeasured by both topologies. The target subtype retains its stated homogeneous degree. -/
theorem continuous_homogeneousSymbolMap_of_smooth_multiplier {m l : ℝ}
    (T : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m →
      homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F l)
    (w : ∀ x : M, (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) → ℂ)
    (hw : ∀ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))),
      c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ContDiffOn ℝ ∞ (fun p ↦ w (c.symm p.1) (covectorFromChart c (c.symm p.1) p.2))
        (c.target ×ˢ {ξ | ξ ≠ 0}))
    (hT : ∀ a x ξ, ξ ≠ 0 → (T a).val x ξ = w x ξ • a.val x ξ) : Continuous T := by
  classical
  let P := EuclideanSpace ℝ (Fin n)
  let mixed {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :=
    iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (f y) ξ) x
  -- Parameter differentiation retains smooth dependence on both original variables.
  have parametric {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (x ξ : P)
      (hf : ContDiffAt ℝ ∞ (Function.uncurry f) (x, ξ)) (j : ℕ) :
      ContDiffAt ℝ ∞ (fun p : P × P ↦ iteratedFDeriv ℝ j (f p.1) p.2) (x, ξ) := by
    induction j with
    | zero =>
      exact hf.continuousLinearMap_comp
        ((continuousMultilinearCurryFin0 ℝ P V).symm : _ →L[ℝ] P [×0]→L[ℝ] V)
    | succ j ih =>
      have h : ContDiffAt ℝ ∞
          (Function.uncurry (fun p : P × P ↦ fun z : P ↦ iteratedFDeriv ℝ j (f p.1) z))
          ((x, ξ), ξ) := ih.comp ((x, ξ), ξ) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
      have hd : ContDiffAt ℝ ∞
          (fun p : P × P ↦ fderiv ℝ (iteratedFDeriv ℝ j (f p.1)) p.2) (x, ξ) :=
        h.fderiv contDiffAt_snd (by simp)
      exact hd.continuousLinearMap_comp
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ P) V).symm :
          _ →L[ℝ] P [×(j + 1)]→L[ℝ] V)
  -- Currying preserves the norm and identifies each differentiated jet with the next frequency jet.
  have mixed_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i j : ℕ) (x ξ : P) :
      ‖mixed (fun y η ↦ fderiv ℝ (f y) η) i j x ξ‖ = ‖mixed f i (j + 1) x ξ‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ (j + 1) (f y) ξ) =
        (continuousMultilinearCurryRightEquiv' ℝ j P V).symm ∘
          (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) := by
      funext y
      exact iteratedFDeriv_succ_eq_comp_right
    rw [heq]
    exact ((continuousMultilinearCurryRightEquiv' ℝ j P V).symm.norm_iteratedFDeriv_comp_left
      (fun y ↦ iteratedFDeriv ℝ j (fderiv ℝ (f y)) ξ) x i).symm
  have mixed_zero {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (f : P → P → V) (i : ℕ) (x ξ : P) :
      ‖mixed f i 0 x ξ‖ = ‖iteratedFDeriv ℝ i (fun y ↦ f y ξ) x‖ := by
    unfold mixed
    have heq : (fun y ↦ iteratedFDeriv ℝ 0 (f y) ξ) =
        (continuousMultilinearCurryFin0 ℝ P V).symm ∘ (fun y ↦ f y ξ) := by
      rfl
    rw [heq, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  have smooth_frequency_derivative {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U Ω : Set P} (hU : IsOpen U) (hΩ : IsOpen Ω) (f : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω)) :
      ContDiffOn ℝ ∞ (fun p : P × P ↦ fderiv ℝ (f p.1) p.2) (U ×ˢ Ω) := by
    intro p hp
    have hf' := hf.contDiffAt ((hU.prod hΩ).mem_nhds hp)
    have h : ContDiffAt ℝ ∞
        (Function.uncurry (fun z : P × P ↦ fun η : P ↦ f z.1 η)) (p, p.2) :=
      hf'.comp (p, p.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
    exact (h.fderiv contDiffAt_snd (by simp)).contDiffWithinAt
  have mixed_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      {U Ω : Set P} (hU : IsOpen U) (hΩ : IsOpen Ω) (f g : P → P → V)
      (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω))
      (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Ω))
      (i j : ℕ) (x ξ : P) (hx : x ∈ U) (hξ : ξ ∈ Ω) :
      mixed (fun y η ↦ f y η + g y η) i j x ξ =
        mixed f i j x ξ + mixed g i j x ξ := by
    have hlocal (y η : P) (hy : y ∈ U) (hη : η ∈ Ω) :
        ContDiffAt ℝ ∞ (Function.uncurry f) (y, η) ∧
          ContDiffAt ℝ ∞ (Function.uncurry g) (y, η) :=
      ⟨hf.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩),
        hg.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)⟩
    have heq : (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ f y η + g y η) ξ) =ᶠ[𝓝 x]
        (fun y ↦ iteratedFDeriv ℝ j (f y) ξ + iteratedFDeriv ℝ j (g y) ξ) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact iteratedFDeriv_add_apply
        (((hlocal y ξ hy hξ).1.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
        (((hlocal y ξ hy hξ).2.comp ξ (contDiffAt_const.prodMk contDiffAt_id)).of_le (by simp))
    have hf' := (parametric f x ξ (hlocal x ξ hx hξ).1 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    have hg' := (parametric g x ξ (hlocal x ξ hx hξ).2 j).comp x
      (contDiffAt_id.prodMk contDiffAt_const)
    exact ((heq.iteratedFDeriv ℝ i).eq_of_nhds).trans
      (iteratedFDeriv_add_apply (hf'.of_le (by simp)) (hg'.of_le (by simp)))
  have estimate (j : ℕ) : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ {V W Z : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
        [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
        (B : V →L[ℝ] W →L[ℝ] Z) (f : P → P → V) (g : P → P → W)
        (U Ω : Set P) (hU : IsOpen U) (hΩ : IsOpen Ω)
        (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ Ω))
        (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (U ×ˢ Ω))
        (x ξ : P) (hx : x ∈ U) (hξ : ξ ∈ Ω)
        (A D : ℝ) (hA : 0 ≤ A) (hD : 0 ≤ D),
        (∀ a ≤ i, ∀ b ≤ j, ‖mixed f a b x ξ‖ ≤ A) →
        (∀ a ≤ i, ∀ b ≤ j, ‖mixed g a b x ξ‖ ≤ D) →
        ‖mixed (fun y η ↦ B (f y η) (g y η)) i j x ξ‖ ≤ C * ‖B‖ * A * D := by
    induction j with
    | zero =>
      intro i
      refine ⟨∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ),
        Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _), ?_⟩
      intro V W Z _ _ _ _ _ _ B f g U Ω hU hΩ hf hg x ξ hx hξ A D hA hD hfb hgb
      rw [mixed_zero]
      have hf' : ContDiffOn ℝ ∞ (fun y ↦ f y ξ) U :=
        hf.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hξ⟩)
      have hg' : ContDiffOn ℝ ∞ (fun y ↦ g y ξ) U :=
        hg.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hy ↦ ⟨hy, hξ⟩)
      have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf' hg' hU.uniqueDiffOn hx
        (n := i) (by simp)
      simp only [iteratedFDerivWithin_of_isOpen _ hU hx] at h
      apply h.trans
      calc
        ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) *
            ‖iteratedFDeriv ℝ k (fun y ↦ f y ξ) x‖ *
            ‖iteratedFDeriv ℝ (i - k) (fun y ↦ g y ξ) x‖ ≤
            ‖B‖ * ∑ k ∈ Finset.range (i + 1), (i.choose k : ℝ) * A * D := by
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          apply Finset.sum_le_sum
          intro k hk
          have hfk := hfb k (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)) 0 (by simp)
          have hgk := hgb (i - k) (Nat.sub_le _ _) 0 (by simp)
          rw [mixed_zero] at hfk hgk
          exact mul_le_mul (mul_le_mul_of_nonneg_left hfk (Nat.cast_nonneg _)) hgk
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
        _ = _ := by simp only [← Finset.sum_mul]; ring
    | succ j ih =>
      intro i
      obtain ⟨C, hC, hbound⟩ := ih i
      refine ⟨2 * C, mul_nonneg (by norm_num) hC, ?_⟩
      intro V W Z _ _ _ _ _ _ B f g U Ω hU hΩ hf hg x ξ hx hξ A D hA hD hfb hgb
      let df : P → P → P →L[ℝ] V := fun y η ↦ fderiv ℝ (f y) η
      let dg : P → P → P →L[ℝ] W := fun y η ↦ fderiv ℝ (g y) η
      have hdf := smooth_frequency_derivative hU hΩ f hf
      have hdg := smooth_frequency_derivative hU hΩ g hg
      have hdfb : ∀ a ≤ i, ∀ b ≤ j, ‖mixed df a b x ξ‖ ≤ A := by
        intro a ha b hb
        rw [mixed_shift]
        exact hfb a ha (b + 1) (Nat.add_le_add_right hb 1)
      have hdgb : ∀ a ≤ i, ∀ b ≤ j, ‖mixed dg a b x ξ‖ ≤ D := by
        intro a ha b hb
        rw [mixed_shift]
        exact hgb a ha (b + 1) (Nat.add_le_add_right hb 1)
      let p : P → P → P →L[ℝ] Z := fun y η ↦ B.precompR P (f y η) (dg y η)
      let q : P → P → P →L[ℝ] Z := fun y η ↦ B.precompL P (df y η) (g y η)
      have hp := hbound (B.precompR P) f dg U Ω hU hΩ hf hdg x ξ hx hξ A D hA hD
        (fun a ha b hb ↦ hfb a ha b (Nat.le_trans hb (Nat.le_succ j))) hdgb
      have hq := hbound (B.precompL P) df g U Ω hU hΩ hdf hg x ξ hx hξ A D hA hD
        hdfb (fun a ha b hb ↦ hgb a ha b (Nat.le_trans hb (Nat.le_succ j)))
      have hps : ContDiffOn ℝ ∞ (Function.uncurry p) (U ×ˢ Ω) :=
        (B.precompR P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hf hdg
      have hqs : ContDiffOn ℝ ∞ (Function.uncurry q) (U ×ˢ Ω) :=
        (B.precompL P).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hdf hg
      have heq : (fun y ↦ iteratedFDeriv ℝ j
          (fun η ↦ fderiv ℝ (fun η ↦ B (f y η) (g y η)) η) ξ) =ᶠ[𝓝 x]
          (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ p y η + q y η) ξ) := by
        filter_upwards [hU.mem_nhds hx] with y hy
        have hinner : (fun η ↦ fderiv ℝ (fun η ↦ B (f y η) (g y η)) η) =ᶠ[𝓝 ξ]
            (fun η ↦ p y η + q y η) := by
          filter_upwards [hΩ.mem_nhds hξ] with η hη
          have hf' := (hf.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)).comp η
            (contDiffAt_const.prodMk contDiffAt_id)
          have hg' := (hg.contDiffAt ((hU.prod hΩ).mem_nhds ⟨hy, hη⟩)).comp η
            (contDiffAt_const.prodMk contDiffAt_id)
          exact B.fderiv_of_bilinear (hf'.differentiableAt (by simp))
            (hg'.differentiableAt (by simp))
        exact (hinner.iteratedFDeriv ℝ j).eq_of_nhds
      rw [← mixed_shift]
      change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
      rw [(heq.iteratedFDeriv ℝ i).eq_of_nhds]
      change ‖mixed (fun y η ↦ p y η + q y η) i j x ξ‖ ≤ _
      rw [mixed_add hU hΩ p q hps hqs i j x ξ hx hξ]
      apply (norm_add_le _ _).trans
      apply (add_le_add hp hq).trans
      have hpr : C * ‖B.precompR P‖ * A * D ≤ C * ‖B‖ * A * D := by
        gcongr
        exact ContinuousLinearMap.norm_precompR_le P B
      have hpl : C * ‖B.precompL P‖ * A * D ≤ C * ‖B‖ * A * D := by
        gcongr
        exact ContinuousLinearMap.norm_precompL_le P B
      exact (add_le_add hpr hpl).trans_eq (by ring)
  -- On each compact product the fixed multiplier has finitely many bounded derivatives.
  have hbound (J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ a b,
        homogeneousSymbolSeminorm E F l J (T a - T b) ≤ C *
          ∑ i ∈ Finset.range (J.localIndex.spatialOrder + 1),
            ∑ j ∈ Finset.range (J.localIndex.frequencyOrder + 1),
              homogeneousSymbolSeminorm E F m
                { J with
                  localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } }
                (a - b) := by
    let : MemTrivializationAtlas J.inputFrame := J.input_mem_atlas
    let : MemTrivializationAtlas J.outputFrame := J.output_mem_atlas
    let U := symbolChartDomain E F J.chart J.inputFrame J.outputFrame
    have hU : IsOpen U := isOpen_symbolChartDomain E F J.chart J.inputFrame J.outputFrame
    let K := J.localIndex.compactSet
    let L := J.frequencySet
    let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
    let v : P → P → ℂ := fun x ξ ↦
      w (J.chart.symm x) (covectorFromChart J.chart (J.chart.symm x) ξ)
    have hv : ContDiffOn ℝ ∞ (Function.uncurry v) (U ×ˢ {ξ | ξ ≠ 0}) :=
      (hw J.chart J.mem_atlas).mono (fun _ hp ↦ ⟨hp.1.1.1, hp.2⟩)
    have hvb (i j : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ ∈ L,
        ‖mixed v i j x ξ‖ ≤ C := by
      have hcont : ContinuousOn (fun p : P × P ↦ mixed v i j p.1 p.2) (K ×ˢ L) := by
        intro p hp
        have hvp := hv.contDiffAt ((hU.prod isOpen_ne).mem_nhds
          ⟨J.localIndex.subset_domain hp.1, J.frequency_ne_zero p.2 hp.2⟩)
        have hξ := parametric v p.1 p.2 hvp j
        have hswap : ContDiffAt ℝ ∞
            (Function.uncurry (fun ξ x ↦ iteratedFDeriv ℝ j (v x) ξ)) (p.2, p.1) :=
          hξ.comp (p.2, p.1) (contDiffAt_snd.prodMk contDiffAt_fst)
        have hx := parametric _ p.2 p.1 hswap i
        exact ((hx.comp p (contDiffAt_snd.prodMk contDiffAt_fst)).continuousAt).continuousWithinAt
      have hcompact := J.localIndex.isCompact.prod J.isCompact_frequencySet
      obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hcont
      exact ⟨max C 0, le_max_right _ _, fun x hx ξ hξ ↦
        (hC (x, ξ) ⟨hx, hξ⟩).trans (le_max_left _ _)⟩
    choose D hD hvb using hvb
    let i := J.localIndex.spatialOrder
    let j := J.localIndex.frequencyOrder
    let A : ℝ := ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), D a b
    have hA : 0 ≤ A := Finset.sum_nonneg (fun a _ ↦ Finset.sum_nonneg (fun b _ ↦ hD a b))
    have hDA (a b : ℕ) (ha : a ≤ i) (hb : b ≤ j) : D a b ≤ A := by
      apply (Finset.single_le_sum (fun k _ ↦ hD a k)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hb))).trans
      exact Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg (fun t _ ↦ hD k t))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ha))
    obtain ⟨C, hC, hestimate⟩ := estimate j i
    let B : ℂ →L[ℝ] H →L[ℝ] H := ContinuousLinearMap.lsmul ℝ ℂ
    refine ⟨C * ‖B‖ * A, mul_nonneg (mul_nonneg hC (norm_nonneg _)) hA, ?_⟩
    intro a b
    let Q (s t : ℕ) : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F :=
      { J with localIndex := { J.localIndex with spatialOrder := s, frequencyOrder := t } }
    let R : ℝ := ∑ s ∈ Finset.range (i + 1),
      ∑ t ∈ Finset.range (j + 1), homogeneousSymbolSeminorm E F m (Q s t) (a - b)
    have hR : 0 ≤ R := Finset.sum_nonneg (fun s _ ↦ Finset.sum_nonneg
      (fun t _ ↦ apply_nonneg (homogeneousSymbolSeminorm E F m (Q s t)) _))
    have hQR (s t : ℕ) (hs : s ≤ i) (ht : t ≤ j) :
        homogeneousSymbolSeminorm E F m (Q s t) (a - b) ≤ R := by
      apply (Finset.single_le_sum (fun k _ ↦ apply_nonneg
        (homogeneousSymbolSeminorm E F m (Q s k)) _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))).trans
      exact Finset.single_le_sum (fun k _ ↦ Finset.sum_nonneg (fun u _ ↦ apply_nonneg
        (homogeneousSymbolSeminorm E F m (Q k u)) _))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hs))
    let f := globalSymbolInChart E F (a - b).val J.chart J.inputFrame J.outputFrame
    let out := globalSymbolInChart E F (T a - T b).val J.chart J.inputFrame J.outputFrame
    have hf : ContDiffOn ℝ ∞ (Function.uncurry f) (U ×ˢ {ξ | ξ ≠ 0}) :=
      (a - b).property.1 J.chart J.mem_atlas J.inputFrame J.outputFrame
    have heq (x ξ : P) (hx : x ∈ U) (hξ : ξ ≠ 0) : out x ξ = v x ξ • f x ξ := by
      have hne : covectorFromChart J.chart (J.chart.symm x) ξ ≠ 0 := by
        intro hz
        have h := covectorInChart_covectorFromChart J.chart J.mem_atlas
          (J.chart.symm x) (J.chart.map_target hx.1.1) ξ
        rw [hz] at h
        exact hξ (h.symm.trans (by ext k; rfl))
      change globalSymbolInChart E F ((T a).val - (T b).val) J.chart J.inputFrame
        J.outputFrame x ξ = v x ξ • globalSymbolInChart E F (a.val - b.val)
          J.chart J.inputFrame J.outputFrame x ξ
      simp only [globalSymbolInChart, Pi.sub_apply, hT a _ _ hne, hT b _ _ hne,
        ← smul_sub, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, v]
    have hpoint (x ξ : P) (hx : x ∈ K) (hξ : ξ ∈ L) :
        ‖mixed out i j x ξ‖ ≤ C * ‖B‖ * A * R := by
      have hder : mixed out i j x ξ = mixed (fun y η ↦ B (v y η) (f y η)) i j x ξ := by
        have houter : (fun y ↦ iteratedFDeriv ℝ j (out y) ξ) =ᶠ[𝓝 x]
            (fun y ↦ iteratedFDeriv ℝ j (fun η ↦ B (v y η) (f y η)) ξ) := by
          filter_upwards [hU.mem_nhds (J.localIndex.subset_domain hx)] with y hy
          have hinner : out y =ᶠ[𝓝 ξ] (fun η ↦ B (v y η) (f y η)) := by
            filter_upwards [isOpen_ne.mem_nhds (J.frequency_ne_zero ξ hξ)] with η hη
            exact heq y η hy hη
          exact (hinner.iteratedFDeriv ℝ j).eq_of_nhds
        exact (houter.iteratedFDeriv ℝ i).eq_of_nhds
      rw [hder]
      apply hestimate B v f U {ξ | ξ ≠ 0} hU isOpen_ne hv hf x ξ
        (J.localIndex.subset_domain hx) (J.frequency_ne_zero ξ hξ) A R hA hR
      · intro s hs t ht
        exact (hvb s t x hx ξ hξ).trans (hDA s t hs ht)
      · intro s hs t ht
        apply le_trans ?_ (hQR s t hs ht)
        exact le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F m (Q s t) (a - b))
          ⟨x, hx, ξ, hξ, rfl⟩
    change homogeneousSymbolSeminorm E F l J (T a - T b) ≤ C * ‖B‖ * A * R
    change homogeneousSymbolSeminormValue E F l J (T a - T b) ≤ _
    by_cases hK : K.Nonempty
    · by_cases hL : L.Nonempty
      · apply csSup_le
        · obtain ⟨x, hx⟩ := hK
          obtain ⟨ξ, hξ⟩ := hL
          exact ⟨_, ⟨x, hx, ξ, hξ, rfl⟩⟩
        · rintro t ⟨x, hx, ξ, hξ, rfl⟩
          exact hpoint x ξ hx hξ
      · have hL' : J.frequencySet = ∅ := Set.not_nonempty_iff_eq_empty.mp hL
        simp only [homogeneousSymbolSeminormValue, hL', Set.mem_empty_iff_false,
          false_and, exists_false, and_false, Set.ofPred_false, Real.sSup_empty]
        positivity
    · have hK' : J.localIndex.compactSet = ∅ := Set.not_nonempty_iff_eq_empty.mp hK
      simp only [homogeneousSymbolSeminormValue, hK', Set.mem_empty_iff_false,
        false_and, exists_false, Set.ofPred_false, Real.sSup_empty]
      positivity
  -- Difference seminorms tend to zero; finite lower-order tests control every output test.
  have : IsTopologicalAddGroup (homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q)
      E F m) := (withSeminorms_homogeneousSymbolTopology E F m).isTopologicalAddGroup
  rw [continuous_iff_continuousAt]
  intro a
  apply (tendsto_homogeneousSymbolTopology_iff E F l (𝓝 a) T (T a)).mpr
  intro J ε hε
  obtain ⟨C, hC, hb⟩ := hbound J
  let R (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m) : ℝ :=
    ∑ i ∈ Finset.range (J.localIndex.spatialOrder + 1),
      ∑ j ∈ Finset.range (J.localIndex.frequencyOrder + 1),
        homogeneousSymbolSeminorm E F m
          { J with
            localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } } (b - a)
  have hR : Tendsto R (𝓝 a) (𝓝 0) := by
    have hcont : Continuous R := by
      apply continuous_finsetSum
      intro i hi
      apply continuous_finsetSum
      intro j hj
      exact ((withSeminorms_homogeneousSymbolTopology E F m).continuous_seminorm
        { J with
          localIndex := { J.localIndex with spatialOrder := i, frequencyOrder := j } }).comp
            (continuous_id.sub continuous_const)
    have hz : R a = 0 := by simp [R]
    simpa only [hz] using (hcont.continuousAt (x := a)).tendsto
  have hCR : Tendsto (fun b ↦ C * R b) (𝓝 a) (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul hR
  have hsmall := hCR.eventually (Iio_mem_nhds hε)
  filter_upwards [hsmall] with b hbsmall
  exact lt_of_le_of_lt (hb b a) hbsmall


set_option backward.isDefEq.respectTransparency false in

/-- Smooth radial extension is continuous at every fixed real degree. -/
theorem continuous_smoothCosphereExtension (m : ℝ) :
    Continuous (smoothCosphereExtension (r := r) (q := q) (E := E) (F := F) g m) := by
  /- For degree zero this is the inducing map. For general degree,
  multiplication by the fixed smooth function length^m is continuous in punctured
  compact derivative seminorms by Leibniz estimates; zero-section data are unmeasured. -/
  let T (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0) :=
    smoothCosphereExtension g m (smoothCosphereRestriction g 0 a)
  have hT : Continuous T := by
    apply continuous_homogeneousSymbolMap_of_smooth_multiplier T
      (fun x ξ ↦ ((g.length x ξ ^ m : ℝ) : ℂ))
    · intro c hc
      apply Complex.ofRealCLM.contDiff.comp_contDiffOn
      apply (g.contDiffOn_length_covectorFromChart c hc).rpow_const_of_ne
      intro p hp
      apply (g.length_pos _ _ ?_).ne'
      intro hzero
      have hi := covectorInChart_covectorFromChart c hc (c.symm p.1) (c.map_target hp.1) p.2
      rw [hzero] at hi
      exact hp.2 (hi.symm.trans (by ext k; rfl))
    · intro a x ξ hξ
      change cosphereExtension g m (cosphereRestriction g a.val) x ξ = _
      have hzero := cosphereExtension_restriction g 0 a.val a.property.2 x ξ hξ
      rw [cosphereExtension_of_ne_zero g 0 _ x ξ hξ] at hzero
      simp only [Real.rpow_zero, Complex.ofReal_one, one_smul] at hzero
      rw [cosphereExtension_of_ne_zero g m _ x ξ hξ, hzero]
  have hzero : Continuous (smoothCosphereExtension (r := r) (q := q)
      (E := E) (F := F) g 0) := continuous_induced_dom
  apply (hT.comp hzero).congr
  intro a
  apply Subtype.ext
  change cosphereExtension g m (cosphereRestriction g (cosphereExtension g 0 a.val)) =
    cosphereExtension g m a.val
  rw [cosphereRestriction_extension]

set_option backward.isDefEq.respectTransparency false in

/-- Restriction is continuous for the punctured smooth and cosphere smooth topologies. -/
theorem continuous_smoothCosphereRestriction (m : ℝ) :
    Continuous (smoothCosphereRestriction (r := r) (q := q) (E := E) (F := F) g m) := by
  /- After degree-zero extension, this is multiplication of the original
  degree-m data by length^(-m) off zero. Leibniz bounds on compact punctured sets
  establish continuity for every defining seminorm. Zero values remain irrelevant. -/
  apply continuous_induced_rng.mpr
  apply continuous_homogeneousSymbolMap_of_smooth_multiplier
    (fun a ↦ smoothCosphereExtension g 0 (smoothCosphereRestriction g m a))
    (fun x ξ ↦ ((g.length x ξ ^ (-m) : ℝ) : ℂ))
  · intro c hc
    apply Complex.ofRealCLM.contDiff.comp_contDiffOn
    apply (g.contDiffOn_length_covectorFromChart c hc).rpow_const_of_ne
    intro p hp
    apply (g.length_pos _ _ ?_).ne'
    intro hzero
    have hi := covectorInChart_covectorFromChart c hc (c.symm p.1) (c.map_target hp.1) p.2
    rw [hzero] at hi
    exact hp.2 (hi.symm.trans (by ext k; rfl))
  · intro a x ξ hξ
    change cosphereExtension g 0 (cosphereRestriction g a.val) x ξ = _
    rw [cosphereExtension_of_ne_zero g 0 _ x ξ hξ]
    simp only [Real.rpow_zero, Complex.ofReal_one, one_smul, cosphereRestriction,
      SmoothCotangentMetric.radial, SmoothCotangentMetric.normalize]
    have h := a.property.2 x ξ hξ ((g.length x ξ)⁻¹) (inv_pos.mpr (g.length_pos x ξ hξ))
    have hpow : (g.length x ξ)⁻¹ ^ m = g.length x ξ ^ (-m) :=
      (Real.rpow_neg_eq_inv_rpow (g.length x ξ) m).symm
    simpa only [hpow] using h

/-- Restriction after smooth extension is exactly the original cosphere section. -/
theorem smoothCosphereRestriction_extension (m : ℝ)
    (a : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g) :
    smoothCosphereRestriction (r := r) (q := q) g m
      (smoothCosphereExtension (r := r) (q := q) g m a) = a := by
  /- Apply the previously established restriction-extension formula
  to the underlying functions. Subtype extensionality discards only regularity certificates. -/
  apply Subtype.ext
  exact cosphereRestriction_extension g m a.val

/-- Smoothness is independent of the chosen homogeneous degree. -/
theorem isSmoothCosphereSymbol_iff_restriction (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    IsSmoothCosphereSymbol (r := r) (q := q) g a ↔
      ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m,
        cosphereRestriction g b.val = a := by
  /- Extend a at degree m for the forward direction. In the reverse
  direction restrict the smooth punctured representative supplied by b. This supplies
  a standard intrinsic characterization without imposing anything at zero. -/
  constructor
  · intro ha
    exact ⟨smoothCosphereExtension g m ⟨a, ha⟩, cosphereRestriction_extension g m a⟩
  · rintro ⟨b, rfl⟩
    exact isSmoothCosphereSymbol_restriction g b.val b.property.1

end AtiyahSinger
