/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereEllipticity

/-!
# Changing the auxiliary cotangent metric

Public module ID: M0419.

Radial normalization identifies the two cosphere bundles over the same base.
Transport of degree-m principal data includes the positive radial weight. At degree
zero that weight equals one, giving pure pullback. Re-extension retains the same
homogeneous principal data, with the canonical zero value at the zero section.
These identities are project deductions supporting SG III.7.10--7.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

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

variable (g k l : SmoothCotangentMetric (n := n) (M := M))

/-- Radially identify the source unit covector with a target unit covector. -/
def cosphereChange (z : CosphereBundle g) : CosphereBundle k :=
  k.radial (g.cosphereInclusion z)

/-- Changing the metric preserves the actual base point. -/
theorem cosphereChange_proj (z : CosphereBundle g) :
    (cosphereChange g k z).val.proj = z.val.proj := by
  /- The radial normalization multiplies only the covector within its
  original fiber. Its total-space constructor uses exactly the original base point. -/
  rfl

/-- Changing a metric to itself is the identity. -/
theorem cosphereChange_self (z : CosphereBundle g) : cosphereChange g g z = z := by
  /- A g-unit covector already has g-length one and is unchanged by
  g-normalization. Subtype extensionality identifies the resulting unit covectors. -/
  exact g.radial_cosphereInclusion z

/-- Successive radial metric changes compose without changing the ray. -/
theorem cosphereChange_comp (z : CosphereBundle g) :
    cosphereChange k l (cosphereChange g k z) = cosphereChange g l z := by
  /- The first change is positive scalar multiplication by reciprocal
  k-length. Positive scaling does not affect l-normalization. Identify the total-space
  covectors and then their unit-length subtype certificates. -/
  -- Fix the original base point; both successive normalizations remain in its fiber.
  apply Subtype.ext
  change (⟨z.val.proj, l.normalize z.val.proj
    (k.normalize z.val.proj z.val.snd)⟩ : CotangentTotalSpace) =
    ⟨z.val.proj, l.normalize z.val.proj z.val.snd⟩
  congr 1
  -- The first normalization scales by the reciprocal of a strictly positive length.
  exact l.normalize_pos_smul z.val.proj z.val.snd
    (k.length z.val.proj z.val.snd)⁻¹
    (inv_pos.mpr (k.length_pos _ _ (g.cosphere_ne_zero z)))

/-- Radial metric change is continuous. -/
theorem continuous_cosphereChange : Continuous (cosphereChange g k) := by
  /- Compose the continuous inclusion into nonzero covectors with the
  target metric radial retraction. Both maps use the fixed original bundle topology. -/
  exact k.continuous_radial.comp g.continuous_cosphereInclusion

/-- Radial changes in opposite directions are inverse. -/
theorem cosphereChange_leftInverse :
    Function.LeftInverse (cosphereChange k g) (cosphereChange g k) := by
  /- Use cosphereChange_comp with the third metric equal to the first,
  followed by cosphereChange_self. No compactness, rank positivity, or chosen coordinates occur. -/
  intro z
  rw [cosphereChange_comp, cosphereChange_self]

/-- The actual radial homeomorphism between the two cosphere models. -/
def cosphereHomeomorph : CosphereBundle g ≃ₜ CosphereBundle k :=
  { toFun := cosphereChange g k
    invFun := cosphereChange k g
    left_inv := cosphereChange_leftInverse g k
    right_inv := cosphereChange_leftInverse k g
    continuous_toFun := continuous_cosphereChange g k
    continuous_invFun := continuous_cosphereChange k g }

/-- Transport homogeneous degree-m data by extension and restriction. -/
def cosphereMetricTransport (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    CosphereSymbolFunction (E := E) (F := F) k :=
  cosphereRestriction k (cosphereExtension g m a)

/-- Metric transport includes the homogeneous radial weight. -/
theorem cosphereMetricTransport_apply (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) (z : CosphereBundle k) :
    cosphereMetricTransport g k m a z =
      ((g.length z.val.proj z.val.snd ^ m : ℝ) : ℂ) • a (cosphereChange k g z) := by
  /- The k-unit covector is nonzero. Unfold extension and normalize it with g;
  the factor is its positive g-length raised to degree m. Omitting this factor
  can change the represented principal data at nonzero degree. -/
  exact cosphereExtension_of_ne_zero g m a z.val.proj z.val.snd
    (k.cosphere_ne_zero z)

/-- Transport to the same cosphere model is the identity. -/
theorem cosphereMetricTransport_self (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereMetricTransport g g m a = a := by
  /- This is the exact restriction-extension identity for g. The unit
  length makes the degree weight equal to one, independently of the sign of m. -/
  exact cosphereRestriction_extension g m a

/-- Transport preserves the actual homogeneous extension everywhere. -/
theorem cosphereExtension_metricTransport (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereExtension k m (cosphereMetricTransport g k m a) = cosphereExtension g m a := by
  /- Off zero, restrict and re-extend the degree-m homogeneous extension
  and use homogeneous reconstruction. At zero both extensions use the canonical zero
  value, so here full equality is justified, unlike equality for arbitrary representatives. -/
  funext x ξ
  by_cases hξ : ξ = 0
  · subst ξ
    simp only [cosphereExtension_zero_covector]
  · -- Homogeneous reconstruction applies to the same original extension off zero.
    exact cosphereExtension_restriction k m (cosphereExtension g m a)
      (isHomogeneousGlobalSymbol_cosphereExtension g m a) x ξ hξ

/-- Successive metric transports compose in the same homogeneous degree. -/
theorem cosphereMetricTransport_comp (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    cosphereMetricTransport k l m (cosphereMetricTransport g k m a) =
      cosphereMetricTransport g l m a := by
  /- Extend the first transported section back to degree m using the
  preceding exact equality, then restrict to the third cosphere. This automatically
  retains and composes both radial weights in the correct order. -/
  change cosphereRestriction l
    (cosphereExtension k m (cosphereMetricTransport g k m a)) =
    cosphereRestriction l (cosphereExtension g m a)
  rw [cosphereExtension_metricTransport]

/-- Metric transport preserves smoothness of cosphere sections. -/
theorem isSmoothCosphereSymbol_metricTransport (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsSmoothCosphereSymbol (r := r) (q := q) g a) :
    IsSmoothCosphereSymbol (r := r) (q := q) k (cosphereMetricTransport g k m a) := by
  /- Extend a smoothly at degree m, then restrict this punctured smooth
  function to the k-unit covectors. The two operations have already been justified
  in actual coordinates and retain the original source and target bundle fibers. -/
  exact isSmoothCosphereSymbol_restriction k (cosphereExtension g m a)
    ((isSmoothOffZeroGlobalSymbol_cosphereExtension_iff g m a).mpr ha)

/-- Metric transport preserves ellipticity in both directions. -/
theorem isEllipticCosphereSymbol_metricTransport_iff (m : ℝ)
    (a : CosphereSymbolFunction (E := E) (F := F) g) :
    IsEllipticCosphereSymbol k (cosphereMetricTransport g k m a) ↔
      IsEllipticCosphereSymbol g a := by
  /- Each radial weight is positive, so forward transport preserves bijectivity.
  Applying that argument to the opposite transport proves the converse, because the
  two exact metric transports compose to the identity on the original section. -/
  -- A forward transport is composition with a nonzero scalar map in the same Hom fiber.
  have hforward (g' k' : SmoothCotangentMetric (n := n) (M := M))
      (b : CosphereSymbolFunction (E := E) (F := F) g')
      (hb : IsEllipticCosphereSymbol g' b) :
      IsEllipticCosphereSymbol k' (cosphereMetricTransport g' k' m b) := by
    intro z
    rw [cosphereMetricTransport_apply]
    have hweight : ((g'.length z.val.proj z.val.snd ^ m : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos
        (g'.length_pos _ _ (k'.cosphere_ne_zero z)) m).ne'
    exact (IsUnit.smul_bijective (isUnit_iff_ne_zero.mpr hweight)).comp
      (hb (cosphereChange k' g' z))
  constructor
  · intro ha
    -- Transport back through the same two metrics, then use the exact composition law.
    have hback := hforward k g (cosphereMetricTransport g k m a) ha
    simpa only [cosphereMetricTransport_comp, cosphereMetricTransport_self] using hback
  · exact hforward g k a

/-- Continuous families remain jointly continuous after changing the metric. -/
theorem IsContinuousCosphereFamily.metricTransport {Z : Type*} [TopologicalSpace Z]
    (m : ℝ) (a : Z → CosphereSymbolFunction (E := E) (F := F) g)
    (ha : IsContinuousCosphereFamily (r := r) (q := q) g a) :
    IsContinuousCosphereFamily (r := r) (q := q) k
      (fun z ↦ cosphereMetricTransport g k m (a z)) := by
  /- Precompose the joint family by the inverse radial homeomorphism
  in its cosphere variable. Multiply in each Hom fiber by the continuous positive
  g-length power on the k-cosphere; the scalar is independent of the parameter. -/
  -- First precompose the original joint total-space map with radial metric change.
  have hpre : Continuous (fun p : Z × CosphereBundle k ↦
      cosphereSymbolTotal (r := r) (q := q) g (a p.1) (cosphereChange k g p.2)) :=
    Continuous.comp ha
      (continuous_fst.prodMk ((continuous_cosphereChange k g).comp continuous_snd))
  have hweight : Continuous (fun p : Z × CosphereBundle k ↦
      ((g.length p.2.val.proj p.2.val.snd ^ m : ℝ) : ℂ)) := by
    apply Complex.continuous_ofReal.comp
    apply ((g.continuous_length.comp continuous_subtype_val).comp continuous_snd).rpow_const
    intro p
    exact Or.inl (g.length_pos _ _ (k.cosphere_ne_zero p.2)).ne'
  -- Multiply by the radial weight in a single native Hom chart around each base point.
  unfold IsContinuousCosphereFamily
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
  change (e ⟨y.2.val.proj, cosphereMetricTransport g k m (a y.1) y.2⟩).2 =
    ((g.length y.2.val.proj y.2.val.snd ^ m : ℝ) : ℂ) •
      (e ⟨y.2.val.proj, a y.1 (cosphereChange k g y.2)⟩).2
  rw [cosphereMetricTransport_apply]
  exact (e.linear ℂ hy).2 _ _

end AtiyahSinger
