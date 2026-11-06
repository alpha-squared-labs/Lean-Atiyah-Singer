/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Complex differential forms and the exterior derivative on a smooth manifold

Public module ID: M1166.

D09: a differential p-form assigns a continuous alternating real-multilinear
complex-valued map to each actual tangent fiber. Smoothness means ordinary
real smoothness of its coefficients in every manifold chart. The base model
is the full finite-dimensional Euclidean space, so there is no boundary.
No compactness, orientability, metric, or selected global frame is assumed.

The exterior derivative is fixed by mathlib's local `extDeriv`, with its
unnormalized alternating-sum convention. Existence and uniqueness assert
that this actual coordinate formula defines a smooth complex-linear operator;
they do not postulate an arbitrary differential with square zero.

Sources: Lawson--Michelsohn, Spin Geometry, II.5, printed pp.123--125,
introduces the de Rham complex in its Dirac-operator discussion. The explicit
coordinate globalization and pullback construction are project supplements
to that discussion. Mathlib provides the normed-space exterior derivative
and its square-zero theorem.
Formal adjoints and the metric Hodge Laplacian are not constructed here.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff Topology

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Complex-valued alternating covariant tensors of degree p on the real tangent fiber. -/
abbrev DifferentialFormFiber (p : ℕ) (x : M) : Type :=
  TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x [⋀^Fin p]→L[ℝ] ℂ

/-- The ordinary coordinate coefficients of a form, pulled back along the inverse chart. -/
def differentialFormInChart {p : ℕ} (form : ∀ x : M, DifferentialFormFiber (n := n) p x)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (y : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ :=
  (form (c.symm y)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y)

/-- A differential form is smooth when its coefficients are smooth in every atlas chart. -/
def IsSmoothDifferentialForm {p : ℕ} (form : ∀ x : M, DifferentialFormFiber (n := n) p x) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      ContDiffOn ℝ ∞ (differentialFormInChart (n := n) form c) c.target

/-- The standard complex submodule of smooth forms inside all alternating tensor fields. -/
def smoothDifferentialForms (p : ℕ) :
    Submodule ℂ (∀ x : M, DifferentialFormFiber (n := n) p x) where
  carrier := {form | IsSmoothDifferentialForm (n := n) form}
  zero_mem' := by
    intro c hc
    change ContDiffOn ℝ ∞ (differentialFormInChart (n := n)
      (0 : ∀ x : M, DifferentialFormFiber (n := n) p x) c) c.target
    convert (contDiffOn_const : ContDiffOn ℝ ∞
      (fun _ : EuclideanSpace ℝ (Fin n) ↦
        (0 : EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ)) c.target) using 1
    ext y v
    rfl
  add_mem' := by
    intro form form₂ hform hform₂ c hc
    change ContDiffOn ℝ ∞ (differentialFormInChart (n := n) (form + form₂) c) c.target
    convert (hform c hc).add (hform₂ c hc) using 1
    ext y v
    rfl
  smul_mem' := by
    intro a form hform c hc
    change ContDiffOn ℝ ∞ (differentialFormInChart (n := n) (a • form) c) c.target
    convert (hform c hc).const_smul a using 1
    ext y v
    rfl

/-- The complex vector space Ωᵖ(M; ℂ) of smooth differential forms. -/
abbrev SmoothDifferentialForm (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] (p : ℕ) : Type _ :=
  smoothDifferentialForms (n := n) (M := M) p

/-- The coordinate formula for d, evaluated in the selected chart at the base point. -/
def differentialFormExteriorDerivative {p : ℕ}
    (form : ∀ x : M, DifferentialFormFiber (n := n) p x) (x : M) :
    DifferentialFormFiber (n := n) (p + 1) x :=
  (extDeriv (differentialFormInChart (n := n) form (chartAt (EuclideanSpace ℝ (Fin n)) x))
      (chartAt (EuclideanSpace ℝ (Fin n)) x x)).compContinuousLinearMap
    (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (chartAt (EuclideanSpace ℝ (Fin n)) x) x)

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "I₀" => 𝓘(ℝ, V)

/-- The explicit exterior derivative has the same coordinate formula in every atlas chart. -/
theorem differentialFormExteriorDerivative_inChart {p : ℕ}
    (form : SmoothDifferentialForm (n := n) M p)
    (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
    (y : V) (hy : y ∈ c.target) :
    differentialFormInChart (n := n)
      (differentialFormExteriorDerivative (n := n) form.val) c y =
        extDeriv (differentialFormInChart (n := n) form.val c) y := by
  -- Compare the selected chart with c through their smooth coordinate transition.
  let x := c.symm y
  let a := chartAt V x
  have hx : x ∈ a.source := mem_chart_source V x
  have hc' := mdifferentiable_of_mem_atlas (I := I₀) hc
  have ha' := mdifferentiable_of_mem_atlas (I := I₀) (chart_mem_atlas V x)
  let f : V → V := a ∘ c.symm
  have hf (z : V) (hzc : z ∈ c.target) (hza : c.symm z ∈ a.source) :
      ContDiffAt ℝ ∞ f z := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas V x)) hza).comp z
      (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hzc)
  have hdf (z : V) (hzc : z ∈ c.target) (hza : c.symm z ∈ a.source) :
      fderiv ℝ f z = (mfderiv I₀ I₀ a (c.symm z)).comp (mfderiv I₀ I₀ c.symm z) := by
    have h := mfderiv_comp z (ha'.mdifferentiableAt hza) (hc'.mdifferentiableAt_symm hzc)
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℝ f z = _ at h
    exact h
  -- The original form is the transition pullback on a neighborhood of y.
  have hnear : differentialFormInChart (n := n) form.val c =ᶠ[𝓝 y]
      (fun z ↦ (differentialFormInChart (n := n) form.val a (f z)).compContinuousLinearMap
        (fderiv ℝ f z)) := by
    filter_upwards [c.open_target.mem_nhds hy,
      (c.continuousAt_symm hy).preimage_mem_nhds (a.open_source.mem_nhds hx)] with z hzc hza
    rw [hdf z hzc hza]
    ext v
    change form.val (c.symm z) (fun i ↦ mfderiv I₀ I₀ c.symm z (v i)) =
      form.val (a.symm (a (c.symm z)))
        (fun i ↦ mfderiv I₀ I₀ a.symm (a (c.symm z))
          (mfderiv I₀ I₀ a (c.symm z) (mfderiv I₀ I₀ c.symm z (v i))))
    rw [a.left_inv hza]
    apply congrArg (form.val (c.symm z))
    funext i
    have h := congrArg (fun L : TangentSpace I₀ (c.symm z) →L[ℝ] TangentSpace I₀ (c.symm z) ↦
      L (mfderiv I₀ I₀ c.symm z (v i))) (ha'.symm_comp_deriv hza)
    exact h.symm
  -- Naturality of the local exterior derivative cancels second transition derivatives.
  have hω : DifferentiableAt ℝ (differentialFormInChart (n := n) form.val a) (f y) :=
    ((form.property a (chart_mem_atlas V x)).contDiffAt
      (a.open_target.mem_nhds (a.map_source hx))).differentiableAt (by simp)
  have hext := extDeriv_pullback hω (hf y hy hx) (by simp)
  rw [← hnear.extDeriv_eq] at hext
  rw [hdf y hy hx] at hext
  convert hext.symm using 1
  ext v
  rfl

/-- The actual coordinate exterior derivative defines a unique smooth complex-linear operator. -/
theorem existsUnique_smoothFormExteriorDerivative (p : ℕ) :
    ∃! d : SmoothDifferentialForm (n := n) M p →ₗ[ℂ]
        SmoothDifferentialForm (n := n) M (p + 1),
      ∀ (form : SmoothDifferentialForm (n := n) M p) (x : M),
        (d form).val x = differentialFormExteriorDerivative (n := n) form.val x := by
  -- Chart covariance reduces global smoothness to differentiation and continuous alternation.
  have hsmooth (form : SmoothDifferentialForm (n := n) M p) :
      IsSmoothDifferentialForm (n := n)
        (differentialFormExteriorDerivative (n := n) form.val) := by
    intro c hc
    have h := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ V ℂ).contDiff
      |>.comp_contDiffOn ((form.property c hc).fderiv_of_isOpen (m := ∞)
        c.open_target (by simp))
    apply h.congr
    intro y hy
    exact differentialFormExteriorDerivative_inChart form c hc y hy
  -- Real differentiation is additive and commutes with complex scalars in the value space.
  let d : SmoothDifferentialForm (n := n) M p →ₗ[ℂ]
      SmoothDifferentialForm (n := n) M (p + 1) :=
    { toFun := fun form ↦ ⟨differentialFormExteriorDerivative form.val, hsmooth form⟩
      map_add' := by
        intro form form₂
        apply Subtype.ext
        funext x
        let c := chartAt V x
        have hx : c x ∈ c.target := mem_chart_target V x
        have h₁ := ((form.property c (chart_mem_atlas V x)).contDiffAt
          (c.open_target.mem_nhds hx)).differentiableAt (by simp)
        have h₂ := ((form₂.property c (chart_mem_atlas V x)).contDiffAt
          (c.open_target.mem_nhds hx)).differentiableAt (by simp)
        have hcoeff : differentialFormInChart (n := n) (form + form₂).val c =
            differentialFormInChart (n := n) form.val c +
              differentialFormInChart (n := n) form₂.val c := by
          ext y v
          rfl
        change (extDeriv (differentialFormInChart (n := n) (form + form₂).val c)
          (c x)).compContinuousLinearMap (mfderiv I₀ I₀ c x) = _
        rw [hcoeff, extDeriv_add h₁ h₂]
        rfl
      map_smul' := by
        intro a form
        apply Subtype.ext
        funext x
        let c := chartAt V x
        have hcoeff : differentialFormInChart (n := n) (a • form).val c =
            a • differentialFormInChart (n := n) form.val c := by
          ext y v
          rfl
        change (extDeriv (differentialFormInChart (n := n) (a • form).val c)
          (c x)).compContinuousLinearMap (mfderiv I₀ I₀ c x) = _
        rw [hcoeff, extDeriv, fderiv_const_smul_field]
        rw [Pi.smul_apply, ContinuousAlternatingMap.alternatizeUncurryFin_smul]
        rfl }
  -- The specified pointwise formula determines the linear operator uniquely.
  refine ⟨d, ?_, ?_⟩
  · intro form x
    rfl
  · intro d' hd'
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    funext x
    exact hd' form x

/-- The global exterior derivative selected by its explicit coordinate formula. -/
def smoothFormExteriorDerivative (p : ℕ) :
    SmoothDifferentialForm (n := n) M p →ₗ[ℂ]
      SmoothDifferentialForm (n := n) M (p + 1) :=
  (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) p).exists.choose

/-- In every valid chart, the global exterior derivative is the local exterior derivative. -/
theorem smoothFormExteriorDerivative_inChart {p : ℕ}
    (form : SmoothDifferentialForm (n := n) M p)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ c.target) :
    differentialFormInChart (n := n) (smoothFormExteriorDerivative (n := n) p form).val c y =
      extDeriv (differentialFormInChart (n := n) form.val c) y := by
  -- Recover the same selected operator's pointwise formula, then use chart covariance.
  have hspec :=
    (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) p).exists.choose_spec
  have hval : (smoothFormExteriorDerivative (n := n) p form).val =
      differentialFormExteriorDerivative (n := n) form.val := by
    funext x
    exact hspec form x
  rw [hval]
  exact differentialFormExteriorDerivative_inChart form c hc y hy

/-- The exterior derivative on smooth manifold forms has square zero. -/
theorem smoothFormExteriorDerivative_comp (p : ℕ) :
    (smoothFormExteriorDerivative (n := n) (M := M) (p + 1)).comp
      (smoothFormExteriorDerivative (n := n) (M := M) p) = 0 := by
  apply LinearMap.ext
  intro form
  apply Subtype.ext
  funext x
  -- Evaluate the outer selected derivative in the chart at x.
  let c := chartAt V x
  have hx : c x ∈ c.target := mem_chart_target V x
  have hspec :=
    (existsUnique_smoothFormExteriorDerivative (n := n) (M := M) (p + 1)).exists.choose_spec
  change (smoothFormExteriorDerivative (n := n) (p + 1)
    (smoothFormExteriorDerivative (n := n) p form)).val x = 0
  rw [show (smoothFormExteriorDerivative (n := n) (p + 1)
      (smoothFormExteriorDerivative (n := n) p form)).val x =
      differentialFormExteriorDerivative (n := n)
        (smoothFormExteriorDerivative (n := n) p form).val x from
    hspec (smoothFormExteriorDerivative (n := n) p form) x]
  -- On the open chart target the inner derivative has exactly the local coefficients.
  have hnear : differentialFormInChart (n := n)
      (smoothFormExteriorDerivative (n := n) p form).val c =ᶠ[𝓝 (c x)]
        extDeriv (differentialFormInChart (n := n) form.val c) := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    exact smoothFormExteriorDerivative_inChart form c (chart_mem_atlas V x) y hy
  have hω := (form.property c (chart_mem_atlas V x)).contDiffAt
    (c.open_target.mem_nhds hx)
  -- Local square zero follows from symmetry of second derivatives; pulling back zero is zero.
  change (extDeriv (differentialFormInChart (n := n)
    (smoothFormExteriorDerivative (n := n) p form).val c)
      (c x)).compContinuousLinearMap (mfderiv I₀ I₀ c x) = 0
  rw [hnear.extDeriv_eq, extDeriv_extDeriv_apply hω (by simp)]
  rfl

end AtiyahSinger
