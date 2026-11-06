/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereRegularity

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Jointly continuous cosphere families

Public module ID: M0415.

The parameter and cosphere variables are tested jointly in the actual Hom
bundle. This is stronger than separate fiberwise pointwise continuity. Algebraic
operations, restriction of smooth-topology families, and interval interpolation
are exposed for the relative smoothing step in SG III.7.10--7.11.
Smooth-topology cosphere and homogeneous families also have jointly continuous
total-space values, as proved by the evaluation and restriction comparisons below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold MeasureTheory Set Function
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20


set_option linter.unusedSectionVars false

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

/-- A jointly continuous family of actual cosphere Hom sections. -/
def IsContinuousCosphereFamily {Z : Type*} [TopologicalSpace Z]
    (a : Z → CosphereSymbolFunction (E := E) (F := F) g) : Prop :=
  Continuous (fun p : Z × CosphereBundle g ↦ cosphereSymbolTotal (r := r) (q := q) g (a p.1) p.2)

/-- Each slice of a jointly continuous family is a continuous section. -/
theorem IsContinuousCosphereFamily.slice {Z : Type*} [TopologicalSpace Z]
    {a : Z → CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a) (z : Z) : 
      IsContinuousCosphereSymbol (r := r) (q := q)
      g (a z) := by
  /- Compose the joint total-space map with the continuous map taking
  a unit covector to the pair consisting of z and that covector. This is exactly a slice. -/
  exact ha.comp (continuous_const.prodMk continuous_id)

/-- Constant families of continuous sections are jointly continuous. -/
theorem IsContinuousCosphereSymbol.family_const {Z : Type*} [TopologicalSpace Z]
    {a : CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a) : 
      IsContinuousCosphereFamily (r := r) (q := q)
      g (fun _ : Z ↦ a) := by
  /- Compose the continuous total-space section with the second product
  projection. The resulting map ignores the parameter and remains over the same base. -/
  exact ha.comp continuous_snd

/-- Joint continuity is preserved by continuous reparameterization. -/
theorem IsContinuousCosphereFamily.comp {Z W : Type*} [TopologicalSpace Z] [TopologicalSpace W]
    {a : Z → CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a) (f : W → Z) (hf : Continuous f) :
    IsContinuousCosphereFamily (r := r) (q := q) g (a ∘ f) := by
  /- Precompose the joint map with the continuous product map f times
  the identity. The fiber base remains the cosphere projection, so no transport is required. -/
  exact Continuous.comp ha ((hf.comp continuous_fst).prodMk continuous_snd)

/-- The zero cosphere section is continuous. -/
theorem isContinuousCosphereSymbol_zero :
    IsContinuousCosphereSymbol (r := r) (q := q) g
      (0 : CosphereSymbolFunction (E := E) (F := F) g) := by
  /- This section is the zero section of the Hom bundle composed with
  the cosphere base projection. Both maps are continuous for the given bundle topology. -/
  exact (Bundle.Trivialization.continuous_zeroSection ℂ).comp
    ((FiberBundle.continuous_proj _ _).comp continuous_subtype_val)

/-- Addition of continuous cosphere sections is continuous. -/
theorem IsContinuousCosphereSymbol.add {a b : CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
      (hb : IsContinuousCosphereSymbol (r := r) (q := q) g b) :
    IsContinuousCosphereSymbol (r := r) (q := q) g (a + b) := by
  /- Use continuous fiberwise addition in the Hom vector bundle. Both
  sections have exactly the same base projection, so addition is defined continuously. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousCosphereSymbol at *
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
  exact (e.linear ℂ hy).1 (a y) (b y)

/-- Complex scalar multiplication preserves continuity. -/
theorem IsContinuousCosphereSymbol.smul (c : ℂ)
    {a : CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a) : 
      IsContinuousCosphereSymbol (r := r) (q := q)
      g (c • a) := by
  /- Continuous constant scalar multiplication in the Hom vector
  bundle, composed with the continuous section a, is the total-space section of c times a. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousCosphereSymbol at *
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
  exact (e.linear ℂ hy).2 c (a y)

/-- Addition of jointly continuous families is jointly continuous. -/
theorem IsContinuousCosphereFamily.add {Z : Type*} [TopologicalSpace Z]
    {a b : Z → CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a)
      (hb : IsContinuousCosphereFamily (r := r) (q := q) g b) :
    IsContinuousCosphereFamily (r := r) (q := q) g (fun z ↦ a z + b z) := by
  /- Apply the continuous fiberwise addition map to the two joint
  total-space maps. Their base projections agree at each pair of parameter and covector. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousCosphereFamily at *
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.2.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (ha.continuousAt (x := p))
  have h₂ := (FiberBundle.continuousAt_totalSpace H _).mp (hb.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  -- In this chart, addition is the ordinary continuous addition of linear maps.
  apply (h₁.2.add h₂.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.2.val.proj))] with y hy
  exact (e.linear ℂ hy).1 (a y.1 y.2) (b y.1 y.2)

/-- A continuous parameter scalar can multiply a jointly continuous family. -/
theorem IsContinuousCosphereFamily.smul {Z : Type*} [TopologicalSpace Z]
    {a : Z → CosphereSymbolFunction (E := E) (F := F) g}
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a) (c : Z → ℂ) (hc : Continuous c) :
    IsContinuousCosphereFamily (r := r) (q := q) g (fun z ↦ c z • a z) := by
  /- Pull the scalar back along the first projection and use continuous
  scalar multiplication on the Hom bundle. Parameter variation must be continuous as stated. -/
  -- Work in one native Hom-bundle chart around the common base point.
  unfold IsContinuousCosphereFamily at *
  apply continuous_iff_continuousAt.mpr
  intro p
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let V := fun x ↦ E x →L[ℂ] F x
  let e := trivializationAt H V p.2.val.proj
  have h₁ := (FiberBundle.continuousAt_totalSpace H _).mp (ha.continuousAt (x := p))
  apply (FiberBundle.continuousAt_totalSpace H _).mpr
  refine ⟨h₁.1, ?_⟩
  -- The scalar and the fiber coordinate vary continuously in this same chart.
  apply ((hc.comp continuous_fst).continuousAt.smul h₁.2).congr_of_eventuallyEq
  filter_upwards [h₁.1.eventually (e.open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt H V p.2.val.proj))] with y hy
  exact (e.linear ℂ hy).2 (c y.1) (a y.1 y.2)

/-- The ordinary affine interpolation of two sections in each fixed Hom fiber. -/
def cosphereInterpolation (a b : CosphereSymbolFunction (E := E) (F := F) g)
    (t : unitInterval) : CosphereSymbolFunction (E := E) (F := F) g :=
  ((1 - (t : ℝ) : ℝ) : ℂ) • a + (((t : ℝ) : ℂ) • b)

/-- Interpolation starts at its first section. -/
theorem cosphereInterpolation_zero (a b : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereInterpolation g a b 0 = a := by
  /- At parameter zero the scalar weights are one and zero. Evaluate
  pointwise and simplify scalar actions and addition in each actual Hom fiber. -/
  simp [cosphereInterpolation]

/-- Interpolation ends at its second section. -/
theorem cosphereInterpolation_one (a b : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereInterpolation g a b 1 = b := by
  /- At parameter one the scalar weights are zero and one. Evaluate
  pointwise and simplify the same fiberwise operations; no endpoint transport is present. -/
  simp [cosphereInterpolation]

/-- Interpolation of continuous sections is jointly continuous. -/
theorem isContinuousCosphereFamily_interpolation
    (a b : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereSymbol (r := r) (q := q) g a)
      (hb : IsContinuousCosphereSymbol (r := r) (q := q) g b) :
    IsContinuousCosphereFamily (r := r) (q := q) g (cosphereInterpolation g a b) := by
  /- Promote both endpoints to constant continuous families. Multiply
  by the continuous interval weights and add. This does not assert invertibility of
  the intermediate maps; arbitrary elliptic endpoints need not have elliptic interpolation. -/
  have hleft : Continuous (fun t : unitInterval ↦ ((1 - (t : ℝ) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_const.sub continuous_subtype_val)
  have hright : Continuous (fun t : unitInterval ↦ ((t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_subtype_val
  exact (ha.family_const g |>.smul g _ hleft).add g
    (hb.family_const g |>.smul g _ hright)

attribute [local instance] homogeneousSymbolTopology smoothCosphereSymbolTopology

set_option maxHeartbeats 700000 in

set_option backward.isDefEq.respectTransparency false in
-- The same dependent total-space maps are compared in original bundle frames.
/-- A family continuous in the smooth topology has jointly continuous cosphere values. -/
theorem isContinuousCosphereFamily_of_continuous {Z : Type*} [TopologicalSpace Z]
    (a : Z → smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g) (ha : Continuous a) :
    IsContinuousCosphereFamily (r := r) (q := q) g (fun z ↦ (a z).val) := by
  /- Local compactness of the finite-dimensional punctured bundle
  makes evaluation continuous for compact smooth convergence. Compose with the
  degree-zero extension and then restrict to the unit covectors. No converse is asserted. -/
  classical
  -- Zeroth compact seminorms control simultaneous variation of the section and evaluation point.
  have heval (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
      (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
      [MemTrivializationAtlas e] [MemTrivializationAtlas f]
      (b : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
      (x ξ : EuclideanSpace ℝ (Fin n))
      (hx : x ∈ symbolChartDomain E F c e f) (hξ : ξ ≠ 0) :
      ContinuousAt
        (fun p : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 ×
          (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ↦
            globalSymbolInChart E F p.1.val c e f p.2.1 p.2.2) (b, (x, ξ)) := by
    let U := symbolChartDomain E F c e f
    have hU := isOpen_symbolChartDomain E F c e f
    obtain ⟨K, hK, hxK, hKU⟩ := exists_compact_subset hU hx
    obtain ⟨L, hL, hξL, hLne⟩ := exists_compact_subset isOpen_ne hξ
    let J : HomogeneousSymbolSeminormIndex (n := n) (r := r) (q := q) E F :=
      { chart := c
        mem_atlas := hc
        inputFrame := e
        outputFrame := f
        input_mem_atlas := inferInstance
        output_mem_atlas := inferInstance
        localIndex :=
          { compactSet := K
            subset_domain := hKU
            isCompact := hK
            spatialOrder := 0
            frequencyOrder := 0 }
        frequencySet := L
        isCompact_frequencySet := hL
        frequency_ne_zero := fun η hη ↦ hLne hη }
    let Q := homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 ×
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    let f₀ := globalSymbolInChart E F b.val c e f
    let δ (p : Q) := globalSymbolInChart E F p.1.val c e f p.2.1 p.2.2 - f₀ p.2.1 p.2.2
    have : IsTopologicalAddGroup (homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q)
        E F 0) := (withSeminorms_homogeneousSymbolTopology E F 0).isTopologicalAddGroup
    have hs : Tendsto (fun p : Q ↦ homogeneousSymbolSeminorm E F 0 J (p.1 - b))
        (𝓝 (b, (x, ξ))) (𝓝 0) := by
      have h : Continuous (fun p : Q ↦ homogeneousSymbolSeminorm E F 0 J (p.1 - b)) :=
        ((withSeminorms_homogeneousSymbolTopology E F 0).continuous_seminorm J).comp
          (continuous_fst.sub continuous_const)
      simpa only [sub_self, map_zero] using (h.continuousAt (x := (b, (x, ξ)))).tendsto
    have hle : ∀ᶠ p : Q in 𝓝 (b, (x, ξ)),
        ‖δ p‖ ≤ homogeneousSymbolSeminorm E F 0 J (p.1 - b) := by
      have hxN : K ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxK
      have hξN : L ∈ 𝓝 ξ := mem_interior_iff_mem_nhds.mp hξL
      filter_upwards [(continuousAt_fst.comp continuousAt_snd).preimage_mem_nhds hxN,
        (continuousAt_snd.comp continuousAt_snd).preimage_mem_nhds hξN] with p hpK hpL
      have h := le_csSup (bddAbove_homogeneousSymbolSeminormValue_set E F 0 J (p.1 - b))
        ⟨p.2.1, hpK, p.2.2, hpL, rfl⟩
      change ‖symbolDerivative (globalSymbolInChart E F (p.1 - b).val c e f) 0 0
        p.2.1 p.2.2‖ ≤ homogeneousSymbolSeminorm E F 0 J (p.1 - b) at h
      have heq : globalSymbolInChart E F (p.1 - b).val c e f p.2.1 p.2.2 = δ p := by
        simp only [globalSymbolInChart, Submodule.coe_sub, Pi.sub_apply,
          ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, δ, f₀]
      simpa only [symbolDerivative, norm_iteratedFDeriv_zero, heq] using h
    have hδ : Tendsto δ (𝓝 (b, (x, ξ))) (𝓝 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      exact squeeze_zero' (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _)) hle hs
    have hb : ContinuousAt (Function.uncurry f₀) (x, ξ) :=
      (b.property.1 c hc e f).continuousOn.continuousAt
        ((hU.prod isOpen_ne).mem_nhds ⟨hx, hξ⟩)
    have hfixed : Tendsto (fun p : Q ↦ f₀ p.2.1 p.2.2)
        (𝓝 (b, (x, ξ))) (𝓝 (f₀ x ξ)) := hb.tendsto.comp continuousAt_snd
    have hadd := hδ.add hfixed
    change Tendsto (fun p : Q ↦ globalSymbolInChart E F p.1.val c e f p.2.1 p.2.2)
      (𝓝 (b, (x, ξ))) (𝓝 (f₀ x ξ))
    simpa only [δ, sub_add_cancel, zero_add] using hadd
  let a₀ (z : Z) := smoothCosphereExtension (r := r) (q := q) g 0 (a z)
  have ha₀ : Continuous a₀ := continuous_induced_dom.comp ha
  change Continuous (fun p : Z × CosphereBundle g ↦
    cosphereSymbolTotal (r := r) (q := q) g (a p.1).val p.2)
  apply continuous_iff_continuousAt.mpr
  rintro ⟨z, z₀⟩
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
    · filter_upwards [hbase.preimage_mem_nhds (c.open_source.mem_nhds hx₀)] with z hz
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
    exact g.cosphere_ne_zero z (hi.symm.trans hzero')
  have hdomain : (c z₀.val.proj, covectorInChart c z₀.val.proj z₀.val.snd) ∈
      symbolChartDomain E F c e f ×ˢ {ξ | ξ ≠ 0} := by
    refine ⟨⟨⟨c.map_source hx₀, ?_⟩, ?_⟩, hne z₀ hx₀⟩ <;>
      simpa only [Set.mem_preimage, c.left_inv hx₀] using mem_baseSet_trivializationAt _ _ _
  -- Compose joint coordinate evaluation with the same moving native cotangent coordinates.
  have hchart' : ContinuousAt (fun p : Z × CosphereBundle g ↦ c p.2.val.proj) (z, z₀) :=
    hchart.comp (x := (z, z₀)) (f := fun p : Z × CosphereBundle g ↦ p.2) continuousAt_snd
  have hcoord' : ContinuousAt (fun p : Z × CosphereBundle g ↦
      covectorInChart c p.2.val.proj p.2.val.snd) (z, z₀) :=
    hcoord.comp (x := (z, z₀)) (f := fun p : Z × CosphereBundle g ↦ p.2) continuousAt_snd
  have hmap : ContinuousAt (fun p : Z × CosphereBundle g ↦
      (a₀ p.1, (c p.2.val.proj, covectorInChart c p.2.val.proj p.2.val.snd))) (z, z₀) :=
    (ha₀.continuousAt.comp continuousAt_fst).prodMk (hchart'.prodMk hcoord')
  have hvalue := (heval c hc e f (a₀ z) (c z₀.val.proj)
    (covectorInChart c z₀.val.proj z₀.val.snd) hdomain.1 hdomain.2).comp
      (x := (z, z₀))
      (f := fun p : Z × CosphereBundle g ↦
        (a₀ p.1, (c p.2.val.proj, covectorInChart c p.2.val.proj p.2.val.snd))) hmap
  have hbase' : ContinuousAt (fun p : Z × CosphereBundle g ↦ p.2.val.proj) (z, z₀) :=
    hbase.comp (x := (z, z₀)) (f := fun p : Z × CosphereBundle g ↦ p.2) continuousAt_snd
  apply (continuousAt_hom_bundle (RingHom.id ℂ) _).mpr
  refine ⟨hbase', ?_⟩
  apply hvalue.congr_of_eventuallyEq
  filter_upwards [hbase'.preimage_mem_nhds
    (c.open_source.mem_nhds hx₀)] with p hp
  change (f.continuousLinearMapAt ℂ p.2.val.proj).comp
    (((a p.1).val p.2).comp (e.symmL ℂ p.2.val.proj)) =
      globalSymbolInChart E F (cosphereExtension g 0 (a p.1).val) c e f (c p.2.val.proj)
        (covectorInChart c p.2.val.proj p.2.val.snd)
  rw [globalSymbolInChart_covectorInChart E F _ c hc e f p.2.val.proj hp]
  have hrestrict := congrFun (cosphereRestriction_extension g 0 (a p.1).val) p.2
  change cosphereExtension g 0 (a p.1).val p.2.val.proj p.2.val.snd = (a p.1).val p.2
    at hrestrict
  rw [hrestrict]

/-- A smooth-topology homogeneous family restricts to a jointly continuous family. -/
theorem isContinuousCosphereFamily_restriction {Z : Type*} [TopologicalSpace Z]
    (m : ℝ) (a : Z → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (ha : Continuous a) :
    IsContinuousCosphereFamily (r := r) (q := q) g (fun z ↦ cosphereRestriction g (a z).val) := by
  /- Compose a with the continuous smooth restriction map, then use
  joint continuity of evaluation for smooth cosphere sections. The resulting total
  map is literally restriction of each homogeneous symbol at the original unit covector. -/
  -- Restrict through the original continuous smooth map, retaining each actual unit covector.
  have h : Continuous (fun z ↦ smoothCosphereRestriction (r := r) (q := q) g m (a z)) :=
    (continuous_smoothCosphereRestriction g m).comp ha
  exact isContinuousCosphereFamily_of_continuous g _ h

end AtiyahSinger
