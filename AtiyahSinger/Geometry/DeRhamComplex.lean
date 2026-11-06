/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DifferentialForms
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Quotient.Basic

import Mathlib.Analysis.Analytic.CPolynomial
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The de Rham complex, cohomology, and smooth pullback

Public module ID: M1160.

D09: the differentials are the actual global exterior derivatives defined
from mathlib's coordinate `extDeriv`. Closed and exact forms are their kernels
and images, with the image entering degree zero explicitly equal to zero.
The cohomology is the ordinary algebraic quotient of closed forms by exact
forms; no closure of the image and no Sobolev completion is substituted.

Smooth pullback uses the actual manifold derivative on tangent vectors and
induces the usual contravariant complex-linear map on this same quotient.
The construction includes all degrees and all smooth maps between possibly
different finite-dimensional boundaryless manifolds. Compactness, orientation,
properness and diffeomorphism hypotheses are unnecessary here.

Sources: Lawson--Michelsohn, Spin Geometry, II.5, printed p.125, for the complex
and quotient. The book's displayed coefficient field there is real; our
complex-valued version is its standard complexification, required by the
later equivariant representation-valued index. The scalar extension and
explicit pullback construction are project supplements to that passage.
No de Rham comparison theorem, Hodge theorem, or sphere computation is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory
open scoped Manifold ContDiff Topology

variable {n m k : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {P : Type*} [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin k)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ P]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "W" => EuclideanSpace ℝ (Fin m)
local notation "I₀" => 𝓘(ℝ, V)
local notation "J₀" => 𝓘(ℝ, W)

/-- Pulling back the actual tangent tensors gives the ordinary pullback in any two atlas charts. -/
theorem differentialFormPullback_inChart (f : M → N) (hf : ContMDiff I₀ J₀ ∞ f) {p : ℕ}
    (form : ∀ x : N, DifferentialFormFiber (n := m) p x)
    (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M)
    (a : OpenPartialHomeomorph N W) (ha : a ∈ atlas W N)
    (z : V) (hzc : z ∈ c.target) (hza : f (c.symm z) ∈ a.source) :
    differentialFormInChart (n := n)
        (fun x ↦ (form (f x)).compContinuousLinearMap (mfderiv I₀ J₀ f x)) c z =
      (differentialFormInChart (n := m) form a
        ((a ∘ f ∘ c.symm) z)).compContinuousLinearMap (fderiv ℝ (a ∘ f ∘ c.symm) z) := by
  -- The ordinary coordinate derivative is the composition of the actual tangent maps.
  have hc' := mdifferentiable_of_mem_atlas (I := I₀) hc
  have ha' := mdifferentiable_of_mem_atlas (I := J₀) ha
  have hfd := (hf.mdifferentiable (by simp)) (c.symm z)
  have hfc := hfd.comp z (hc'.mdifferentiableAt_symm hzc)
  have hdf : fderiv ℝ (a ∘ f ∘ c.symm) z =
      (mfderiv J₀ J₀ a (f (c.symm z))).comp
        ((mfderiv I₀ J₀ f (c.symm z)).comp (mfderiv I₀ I₀ c.symm z)) := by
    have h := mfderiv_comp z (ha'.mdifferentiableAt hza) hfc
    rw [mfderiv_eq_fderiv, mfderiv_comp z hfd (hc'.mdifferentiableAt_symm hzc)] at h
    exact h
  -- Cancel the inverse target-chart derivative on the same tangent fiber.
  rw [hdf]
  ext v
  change form (f (c.symm z))
      (fun i ↦ mfderiv I₀ J₀ f (c.symm z) (mfderiv I₀ I₀ c.symm z (v i))) =
    form (a.symm (a (f (c.symm z))))
      (fun i ↦ mfderiv J₀ J₀ a.symm (a (f (c.symm z)))
        (mfderiv J₀ J₀ a (f (c.symm z))
          (mfderiv I₀ J₀ f (c.symm z) (mfderiv I₀ I₀ c.symm z (v i)))))
  rw [a.left_inv hza]
  apply congrArg (form (f (c.symm z)))
  funext i
  have h := congrArg (fun L : TangentSpace J₀ (f (c.symm z)) →L[ℝ]
      TangentSpace J₀ (f (c.symm z)) ↦
    L (mfderiv I₀ J₀ f (c.symm z) (mfderiv I₀ I₀ c.symm z (v i))))
      (ha'.symm_comp_deriv hza)
  exact h.symm

/-- Pullback along a smooth map is the unique linear operator with the tangent-vector formula. -/
theorem existsUnique_smoothFormPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ) :
    ∃! pullback : SmoothDifferentialForm (n := m) N p →ₗ[ℂ]
        SmoothDifferentialForm (n := n) M p,
      ∀ (form : SmoothDifferentialForm (n := m) N p) (x : M),
        (pullback form).val x = (form.val (f x)).compContinuousLinearMap
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f x) := by
  -- Work near each source-chart point in a target chart containing its image.
  have hsmooth (form : SmoothDifferentialForm (n := m) N p) :
      IsSmoothDifferentialForm (n := n)
        (fun x ↦ (form.val (f x)).compContinuousLinearMap (mfderiv I₀ J₀ f x)) := by
    intro c hc y hy
    let a := chartAt W (f (c.symm y))
    have ha : f (c.symm y) ∈ a.source := mem_chart_source W _
    let g : V → W := a ∘ f ∘ c.symm
    have hg : ContDiffAt ℝ ∞ g y := by
      apply contMDiffAt_iff_contDiffAt.mp
      exact (contMDiffAt_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (chart_mem_atlas W _)) ha).comp y
        (hf.contMDiffAt.comp y
          (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy))
    have hnear : differentialFormInChart (n := n)
        (fun x ↦ (form.val (f x)).compContinuousLinearMap (mfderiv I₀ J₀ f x)) c =ᶠ[𝓝 y]
        (fun z ↦ (differentialFormInChart (n := m) form.val a
          (g z)).compContinuousLinearMap (fderiv ℝ g z)) := by
      filter_upwards [c.open_target.mem_nhds hy,
        (hf.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
          (a.open_source.mem_nhds ha)] with z hzc hza
      exact differentialFormPullback_inChart f hf form.val c hc a
        (chart_mem_atlas W _) z hzc hza
    -- Precomposition of alternating maps is polynomial in the tangent map, hence smooth.
    have hcoef := (form.property a (chart_mem_atlas W _)).contDiffAt
      (a.open_target.mem_nhds (a.map_source ha))
    have hop : ContDiffAt ℝ ∞
        (ContinuousAlternatingMap.compContinuousLinearMapCLM :
          (V →L[ℝ] W) → (W [⋀^Fin p]→L[ℝ] ℂ) →L[ℝ] V [⋀^Fin p]→L[ℝ] ℂ)
          (fderiv ℝ g y) :=
      (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM _).contDiffAt
    have hlocal := (hop.comp y (hg.fderiv_right (m := ∞) (by simp))).clm_apply
      (hcoef.comp y hg)
    exact (hlocal.congr_of_eventuallyEq hnear).contDiffWithinAt
  -- The actual tangent formula is complex-linear in the form; it determines the map uniquely.
  let pullback : SmoothDifferentialForm (n := m) N p →ₗ[ℂ]
      SmoothDifferentialForm (n := n) M p :=
    { toFun := fun form ↦ ⟨fun x ↦ (form.val (f x)).compContinuousLinearMap
        (mfderiv I₀ J₀ f x), hsmooth form⟩
      map_add' := by
        intro form form₂
        apply Subtype.ext
        funext x
        ext v
        rfl
      map_smul' := by
        intro a form
        apply Subtype.ext
        funext x
        ext v
        rfl }
  refine ⟨pullback, ?_, ?_⟩
  · intro form x
    rfl
  · intro pullback' hpullback'
    apply LinearMap.ext
    intro form
    apply Subtype.ext
    funext x
    exact hpullback' form x

/-- Smooth pullback of differential forms, with the actual tangent-vector formula. -/
def smoothFormPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ) :
    SmoothDifferentialForm (n := m) N p →ₗ[ℂ] SmoothDifferentialForm (n := n) M p :=
  (existsUnique_smoothFormPullback f hf p).exists.choose

/-- Evaluation of pullback uses the same map and its actual manifold derivative. -/
theorem smoothFormPullback_apply (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ)
    (form : SmoothDifferentialForm (n := m) N p) (x : M) :
    (smoothFormPullback f hf p form).val x =
      (form.val (f x)).compContinuousLinearMap
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin m)) f x) := by
  -- Use the specification of the very witness selected in the original definition.
  exact (existsUnique_smoothFormPullback f hf p).exists.choose_spec form x

/-- Exterior differentiation commutes with smooth pullback. -/
theorem smoothFormExteriorDerivative_pullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ) :
    (smoothFormExteriorDerivative (n := n) (M := M) p).comp
        (smoothFormPullback f hf p) =
      (smoothFormPullback f hf (p + 1)).comp
        (smoothFormExteriorDerivative (n := m) (M := N) p) := by
  apply LinearMap.ext
  intro form
  apply Subtype.ext
  funext x
  -- Choose source and target charts only for this local computation at x.
  let c := chartAt V x
  let a := chartAt W (f x)
  let g : V → W := a ∘ f ∘ c.symm
  have hc : x ∈ c.source := mem_chart_source V x
  have hy : c x ∈ c.target := mem_chart_target V x
  have ha : f x ∈ a.source := mem_chart_source W (f x)
  have hxa : f (c.symm (c x)) ∈ a.source := by rwa [c.left_inv hc]
  have hg : ContDiffAt ℝ ∞ g (c x) := by
    apply contMDiffAt_iff_contDiffAt.mp
    exact (contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (chart_mem_atlas W _)) hxa).comp (c x)
      (hf.contMDiffAt.comp (c x)
        (contMDiffAt_symm_of_mem_maximalAtlas
          (IsManifold.subset_maximalAtlas (chart_mem_atlas V _)) hy))
  have hraw (q : ℕ) (form' : SmoothDifferentialForm (n := m) N q) :
      (smoothFormPullback f hf q form').val = fun x ↦
        (form'.val (f x)).compContinuousLinearMap (mfderiv I₀ J₀ f x) := by
    funext x
    exact smoothFormPullback_apply f hf q form' x
  -- The actual pullback coefficients coincide with the normed-space formula near c(x).
  have hnear : differentialFormInChart (n := n) (smoothFormPullback f hf p form).val c
      =ᶠ[𝓝 (c x)] (fun z ↦ (differentialFormInChart (n := m) form.val a
        (g z)).compContinuousLinearMap (fderiv ℝ g z)) := by
    rw [hraw]
    filter_upwards [c.open_target.mem_nhds hy,
      (hf.continuous.continuousAt.comp (c.continuousAt_symm hy)).preimage_mem_nhds
        (a.open_source.mem_nhds hxa)] with z hzc hza
    exact differentialFormPullback_inChart f hf form.val c (chart_mem_atlas V _) a
      (chart_mem_atlas W _) z hzc hza
  have hcoef : DifferentiableAt ℝ (differentialFormInChart (n := m) form.val a) (g (c x)) :=
    ((form.property a (chart_mem_atlas W _)).contDiffAt
      (a.open_target.mem_nhds (a.map_source hxa))).differentiableAt (by simp)
  -- Naturality in normed spaces identifies both coordinate forms with the same expression.
  have hcoords : differentialFormInChart (n := n)
      (smoothFormExteriorDerivative (n := n) p (smoothFormPullback f hf p form)).val c (c x) =
      differentialFormInChart (n := n)
        (smoothFormPullback f hf (p + 1) (smoothFormExteriorDerivative (n := m) p form)).val
          c (c x) := by
    rw [smoothFormExteriorDerivative_inChart _ c (chart_mem_atlas V _) (c x) hy,
      hnear.extDeriv_eq, extDeriv_pullback hcoef hg (by simp), hraw]
    rw [differentialFormPullback_inChart f hf _ c (chart_mem_atlas V _) a
      (chart_mem_atlas W _) (c x) hy hxa,
      smoothFormExteriorDerivative_inChart form a (chart_mem_atlas W _)
        (g (c x)) (a.map_source hxa)]
  -- The source chart's inverse tangent map is invertible, so the original fiber forms agree.
  dsimp only [differentialFormInChart] at hcoords
  rw [c.left_inv hc] at hcoords
  have hinverse (v : TangentSpace I₀ x) :
      mfderiv I₀ I₀ c.symm (c x) (mfderiv I₀ I₀ c x v) = v :=
    congrArg (fun L : TangentSpace I₀ x →L[ℝ] TangentSpace I₀ x ↦ L v)
      ((mdifferentiable_of_mem_atlas (I := I₀) (chart_mem_atlas V x)).symm_comp_deriv hc)
  ext v
  have h := congrArg (fun coef : V [⋀^Fin (p + 1)]→L[ℝ] ℂ ↦
    coef (fun i ↦ mfderiv I₀ I₀ c x (v i))) hcoords
  change (smoothFormExteriorDerivative (n := n) p (smoothFormPullback f hf p form)).val x
      (fun i ↦ mfderiv I₀ I₀ c.symm (c x) (mfderiv I₀ I₀ c x (v i))) =
    (smoothFormPullback f hf (p + 1) (smoothFormExteriorDerivative (n := m) p form)).val x
      (fun i ↦ mfderiv I₀ I₀ c.symm (c x) (mfderiv I₀ I₀ c x (v i))) at h
  simpa only [hinverse, LinearMap.comp_apply] using h

/-- The de Rham cochain complex of smooth complex-valued forms in all nonnegative degrees. -/
def deRhamComplex : CochainComplex (ModuleCat ℂ) ℕ :=
  CochainComplex.of
    (fun p ↦ ModuleCat.of ℂ (SmoothDifferentialForm (n := n) M p))
    (fun p ↦ ModuleCat.ofHom (smoothFormExteriorDerivative (n := n) (M := M) p))
    (fun p ↦ ModuleCat.hom_ext (smoothFormExteriorDerivative_comp (n := n) (M := M) p))

/-- Closed p-forms are the kernel of the actual exterior derivative. -/
def deRhamClosedForms (p : ℕ) : Submodule ℂ (SmoothDifferentialForm (n := n) M p) :=
  LinearMap.ker (smoothFormExteriorDerivative (n := n) (M := M) p)

/-- Exact p-forms are the previous differential's image; no differential enters degree zero. -/
def deRhamExactForms : (p : ℕ) → Submodule ℂ (SmoothDifferentialForm (n := n) M p)
  | 0 => ⊥
  | p + 1 => LinearMap.range (smoothFormExteriorDerivative (n := n) (M := M) p)

/-- Every exact differential form is closed. -/
theorem deRhamExactForms_le_closedForms (p : ℕ) :
    deRhamExactForms (n := n) (M := M) p ≤ deRhamClosedForms (n := n) (M := M) p := by
  -- The incoming image is zero in degree zero and the actual derivative's range otherwise.
  cases p with
  | zero => exact bot_le
  | succ p =>
    rintro form ⟨primitive, rfl⟩
    change smoothFormExteriorDerivative (n := n) (p + 1)
      (smoothFormExteriorDerivative (n := n) p primitive) = 0
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_comp (n := n) (M := M) p)
      primitive
    exact h

/-- The complex de Rham cohomology Hᵖ_dR(M; ℂ), as closed forms modulo exact forms. -/
abbrev DeRhamCohomology (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] (p : ℕ) : Type _ :=
  deRhamClosedForms (n := n) (M := M) p ⧸
    (deRhamExactForms (n := n) (M := M) p).comap
      (deRhamClosedForms (n := n) (M := M) p).subtype

/-- The cohomology class of a closed differential form. -/
def deRhamClass (p : ℕ) :
    deRhamClosedForms (n := n) (M := M) p →ₗ[ℂ] DeRhamCohomology (n := n) M p :=
  ((deRhamExactForms (n := n) (M := M) p).comap
    (deRhamClosedForms (n := n) (M := M) p).subtype).mkQ

/-- The actual pullback on forms preserves closed forms and descends through exact forms. -/
def deRhamPullback (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ) :
    DeRhamCohomology (n := m) N p →ₗ[ℂ] DeRhamCohomology (n := n) M p := by
  -- Restrict the same smooth pullback to closed forms, using its commutation with d.
  let closedPullback : deRhamClosedForms (n := m) (M := N) p →ₗ[ℂ]
      deRhamClosedForms (n := n) (M := M) p :=
    (smoothFormPullback f hf p).restrict (by
      intro form hform
      change smoothFormExteriorDerivative (n := m) (M := N) p form = 0 at hform
      change smoothFormExteriorDerivative (n := n) (M := M) p
        (smoothFormPullback f hf p form) = 0
      have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf p) form
      simpa [hform] using h)
  -- Descend through the exact subspaces; their degree-zero value is explicitly zero.
  refine Submodule.mapQ
    ((deRhamExactForms (n := m) (M := N) p).comap
      (deRhamClosedForms (n := m) (M := N) p).subtype)
    ((deRhamExactForms (n := n) (M := M) p).comap
      (deRhamClosedForms (n := n) (M := M) p).subtype) closedPullback ?_
  intro form hform
  change smoothFormPullback f hf p form.val ∈ deRhamExactForms (n := n) (M := M) p
  change form.val ∈ deRhamExactForms (n := m) (M := N) p at hform
  cases p with
  | zero =>
    have hzero : form.val = 0 := hform
    simp [hzero, deRhamExactForms]
  | succ p =>
    rcases hform with ⟨primitive, hprimitive⟩
    refine ⟨smoothFormPullback f hf p primitive, ?_⟩
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf p) primitive
    simpa [hprimitive] using h

/-- Pullback acts on a class by pulling back its closed representative. -/
theorem deRhamPullback_class (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (p : ℕ)
    (form : deRhamClosedForms (n := m) (M := N) p)
    (hpullback : smoothFormPullback f hf p form.val ∈
      deRhamClosedForms (n := n) (M := M) p) :
    deRhamPullback f hf p (deRhamClass p form) =
      deRhamClass p ⟨smoothFormPullback f hf p form.val, hpullback⟩ := by
  -- The original mapQ is defined on exactly this closed representative.
  rfl

/-- The identity smooth map induces the identity on de Rham cohomology. -/
theorem deRhamPullback_id (p : ℕ) :
    deRhamPullback (n := n) (m := n) (M := M) (N := M) id contMDiff_id p =
      LinearMap.id := by
  -- The identity tangent map fixes each original smooth form.
  have hform (form : SmoothDifferentialForm (n := n) M p) :
      smoothFormPullback id contMDiff_id p form = form := by
    apply Subtype.ext
    funext x
    rw [smoothFormPullback_apply, mfderiv_id]
    rfl
  -- Every quotient class has a closed representative; the same quotient map preserves it.
  apply LinearMap.ext
  intro a
  obtain ⟨form, rfl⟩ := (Submodule.Quotient.mk_surjective
    ((deRhamExactForms (n := n) (M := M) p).comap
      (deRhamClosedForms (n := n) (M := M) p).subtype)) a
  change deRhamPullback id contMDiff_id p (deRhamClass p form) = deRhamClass p form
  rw [deRhamPullback_class id contMDiff_id p form (by rw [hform]; exact form.property)]
  congr 1
  apply Subtype.ext
  exact hform form.val

/-- De Rham pullback reverses the order of smooth-map composition. -/
theorem deRhamPullback_comp (f : M → N) (g : N → P)
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ g) (p : ℕ) :
    deRhamPullback (g ∘ f) (hg.comp hf) p =
      (deRhamPullback f hf p).comp (deRhamPullback g hg p) := by
  -- The original tangent chain rule gives contravariant composition on smooth forms.
  have hform (form : SmoothDifferentialForm (n := k) P p) :
      smoothFormPullback (g ∘ f) (hg.comp hf) p form =
        smoothFormPullback f hf p (smoothFormPullback g hg p form) := by
    apply Subtype.ext
    funext x
    rw [smoothFormPullback_apply, smoothFormPullback_apply, smoothFormPullback_apply]
    rw [mfderiv_comp x ((hg.mdifferentiable (by simp)) (f x))
      ((hf.mdifferentiable (by simp)) x)]
    rfl
  -- Closed representatives suffice for equality on the original algebraic quotient.
  apply LinearMap.ext
  intro a
  obtain ⟨form, rfl⟩ := (Submodule.Quotient.mk_surjective
    ((deRhamExactForms (n := k) (M := P) p).comap
      (deRhamClosedForms (n := k) (M := P) p).subtype)) a
  have hclosed : smoothFormPullback g hg p form.val ∈
      deRhamClosedForms (n := m) (M := N) p := by
    change smoothFormExteriorDerivative (n := m) p (smoothFormPullback g hg p form.val) = 0
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback g hg p) form.val
    have hz : smoothFormExteriorDerivative (n := k) p form.val = 0 := form.property
    simpa [hz] using h
  have hclosed' : smoothFormPullback f hf p (smoothFormPullback g hg p form.val) ∈
      deRhamClosedForms (n := n) (M := M) p := by
    change smoothFormExteriorDerivative (n := n) p
      (smoothFormPullback f hf p (smoothFormPullback g hg p form.val)) = 0
    have h := LinearMap.congr_fun (smoothFormExteriorDerivative_pullback f hf p)
      (smoothFormPullback g hg p form.val)
    have hz : smoothFormExteriorDerivative (n := m) p
        (smoothFormPullback g hg p form.val) = 0 := hclosed
    simpa [hz] using h
  change deRhamPullback (g ∘ f) (hg.comp hf) p (deRhamClass p form) =
    deRhamPullback f hf p (deRhamPullback g hg p (deRhamClass p form))
  rw [deRhamPullback_class (g ∘ f) (hg.comp hf) p form (by
      rw [hform]
      exact hclosed'),
    deRhamPullback_class g hg p form hclosed,
    deRhamPullback_class f hf p ⟨smoothFormPullback g hg p form.val, hclosed⟩ hclosed']
  congr 1
  apply Subtype.ext
  exact hform form.val

end AtiyahSinger
