/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HodgeEllipticRealization
public import AtiyahSinger.Geometry.DeRhamComplex
public import AtiyahSinger.Geometry.HodgeLaplacian
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

import AtiyahSinger.Analysis.SmoothAdjointCokernel

/-!
# Hodge decomposition on the actual smooth differential forms

Public module ID: M0738.

P06: on a compact boundaryless Riemannian manifold, the original smooth forms
split into harmonic, exact and coexact forms, orthogonally for the metric
volume density. The harmonic class map is the actual inclusion into closed
forms followed by the existing de Rham quotient; its bijectivity is the Hodge
theorem, rather than an assumption on an abstract cohomology model.

The total form space is the usual algebraic direct sum of the actual forms
in all nonnegative degrees. Its exterior derivative and codifferential use
the original operators on every summand. This avoids silently discarding a
top-degree derivative or introducing unrelated finite-dimensional spaces.
The total Hodge--de Rham operator is their sum, and its kernel agrees with
the kernel of the degreewise Hodge Laplacian on compact manifolds.

Sources: Lawson--Michelsohn, Spin Geometry, II.5.12 and II.5.14--5.15,
printed pp.123--125, its orientability note on pp.125--126, and III.5.5--5.6,
printed p.195. The latter derives the
orthogonal decomposition from self-adjoint elliptic theory. Our coefficients
are complex and the measure is the metric density, so no orientation is
required. Wikipedia's Hodge theory article states the same canonical map,
unique harmonic representative and three-summand decomposition in real
coefficients. Complexification is the explicit standard supplement
HODGE-COMPLEXIFICATION-SOURCE. SG's orientability note already supports the
nonorientable conclusion; the explicit coordinate density construction is
recorded separately.

All degrees, empty manifolds, disconnected manifolds and dimension zero are
retained. The degree-zero exact space is the existing zero subspace. The
Hodge decomposition theorem keeps its three pairwise orthogonality clauses
together with uniqueness of the three components: they are the single
textbook orthogonal-decomposition result, not four separate proof steps.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory Set
open scoped ComplexConjugate DirectSum Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

variable (g : SmoothTangentMetric (n := n) (M := M))

/-- Harmonic p-forms are the kernel of the actual metric Hodge Laplacian. -/
def harmonicForms (p : ℕ) : Submodule ℂ (SmoothDifferentialForm (n := n) M p) :=
  LinearMap.ker (smoothFormHodgeLaplacian g p)

/-- Coexact p-forms are the image of the original metric codifferential from degree p+1. -/
def deRhamCoexactForms (p : ℕ) : Submodule ℂ (SmoothDifferentialForm (n := n) M p) :=
  LinearMap.range (smoothFormCodifferential g p)

/-- On a compact manifold every harmonic form is closed for the original differential. -/
theorem harmonicForms_le_closedForms [CompactSpace M] (p : ℕ) :
    harmonicForms g p ≤ deRhamClosedForms (n := n) (M := M) p := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  let P := smoothFormPairing g
  let d := smoothFormExteriorDerivative (n := n) (M := M)
  let δ := smoothFormCodifferential g
  have hcompact (q : ℕ) (u : F q) : IsCompact (closure {x : M | u.val x ≠ 0}) :=
    isClosed_closure.isCompact
  have hint (q : ℕ) (u v : F q) :
      Integrable (fun x ↦ differentialFormInner g q x (u.val x) (v.val x))
        g.riemannianVolume := integrable_differentialFormInner g q u v (hcompact q u)
  -- The original fiber pairing is Hermitian and positive, with its prescribed normalization.
  have hsym (q : ℕ) (u v : F q) : conj (P q v u) = P q u v := by
    rw [show P q v u = ∫ x, differentialFormInner g q x (v.val x) (u.val x)
      ∂g.riemannianVolume from rfl, ← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦ (differentialFormInnerCore g q x).conj_inner_symm _ _
  have hnonneg (q : ℕ) (u : F q) : 0 ≤ (P q u u).re := by
    change 0 ≤ RCLike.re (∫ x, differentialFormInner g q x (u.val x) (u.val x)
      ∂g.riemannianVolume)
    rw [← integral_re (hint q u u)]
    apply integral_nonneg
    intro x
    exact (differentialFormInnerCore g q x).re_inner_nonneg _
  have hself_zero (q : ℕ) (u : F q) (h : (P q u u).re = 0) : u = 0 := by
    apply (smoothFormPairing_self_eq_zero_iff g q u (hcompact q u)).mp
    apply Complex.ext h
    have hconj := congrArg Complex.im (hsym q u u)
    simp only [Complex.conj_im] at hconj
    change (P q u u).im = 0
    linarith
  have hadd (q : ℕ) (u v w : F q) : P q u (v + w) = P q u v + P q u w := by
    change (∫ x, differentialFormInner g q x (u.val x) ((v + w).val x)
      ∂g.riemannianVolume) = _
    have heq (x : M) : differentialFormInner g q x (u.val x) ((v + w).val x) =
        differentialFormInner g q x (u.val x) (v.val x) +
          differentialFormInner g q x (u.val x) (w.val x) := by
      let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) q x) :=
        differentialFormInnerCore g q x
      exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) (u.val x) (v.val x) (w.val x)
    simp_rw [heq]
    exact integral_add (hint q u v) (hint q u w)
  have hzero (q : ℕ) (u : F q) : P q u 0 = 0 := by
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x ↦ by
      let : InnerProductSpace.Core ℂ (DifferentialFormFiber (n := n) q x) :=
        differentialFormInnerCore g q x
      exact InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) (u.val x)
  intro u hu
  change smoothFormHodgeLaplacian g p u = 0 at hu
  change d p u = 0
  -- Pair the harmonic equation with u; formal adjunction identifies the two energy terms.
  cases p with
  | zero =>
      have hadj := smoothFormCodifferential_formalAdjoint g 0 u (d 0 u) (hcompact 0 u)
      change P 1 (d 0 u) (d 0 u) = P 0 u (δ 0 (d 0 u)) at hadj
      change δ 0 (d 0 u) = 0 at hu
      rw [hu, hzero] at hadj
      exact (smoothFormPairing_self_eq_zero_iff g 1 _ (hcompact 1 _)).mp hadj
  | succ p =>
      have heq : P (p + 1) u (d p (δ p u)) +
          P (p + 1) u (δ (p + 1) (d (p + 1) u)) = 0 := by
        rw [← hadd]
        change P (p + 1) u (smoothFormHodgeLaplacian g (p + 1) u) = 0
        rw [hu, hzero]
      have hd := smoothFormCodifferential_formalAdjoint g (p + 1) u
        (d (p + 1) u) (hcompact (p + 1) u)
      have hδ := smoothFormCodifferential_formalAdjoint g p (δ p u) u (hcompact p _)
      change P (p + 1) (d p (δ p u)) u = P p (δ p u) (δ p u) at hδ
      change P (p + 2) (d (p + 1) u) (d (p + 1) u) =
        P (p + 1) u (δ (p + 1) (d (p + 1) u)) at hd
      rw [← hd, ← hsym (p + 1) u (d p (δ p u)), hδ] at heq
      -- Both real self-pairings are nonnegative, so the exterior derivative has zero norm.
      have hre := congrArg Complex.re heq
      simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
      apply hself_zero (p + 2) (d (p + 1) u)
      linarith [hnonneg p (δ p u), hnonneg (p + 2) (d (p + 1) u)]

/-- Total smooth forms are finite sums of the original homogeneous smooth forms. -/
abbrev TotalSmoothDifferentialForm (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] : Type _ :=
  ⨁ p : ℕ, SmoothDifferentialForm (n := n) M p

/-- The total exterior derivative raises each original homogeneous degree by one. -/
def totalFormExteriorDerivative :
    TotalSmoothDifferentialForm (n := n) M →ₗ[ℂ] TotalSmoothDifferentialForm (n := n) M :=
  DirectSum.toModule ℂ ℕ (TotalSmoothDifferentialForm (n := n) M)
    (fun p ↦ (DirectSum.lof ℂ ℕ (fun q ↦ SmoothDifferentialForm (n := n) M q) (p + 1)).comp
      (smoothFormExteriorDerivative (n := n) (M := M) p))

/-- The total codifferential lowers positive degrees and is zero on zero-forms. -/
def totalFormCodifferential :
    TotalSmoothDifferentialForm (n := n) M →ₗ[ℂ] TotalSmoothDifferentialForm (n := n) M :=
  DirectSum.toModule ℂ ℕ (TotalSmoothDifferentialForm (n := n) M)
    (fun p ↦ match p with
      | 0 => 0
      | q + 1 => (DirectSum.lof ℂ ℕ (fun k ↦ SmoothDifferentialForm (n := n) M k) q).comp
          (smoothFormCodifferential g q))

/-- The Hodge--de Rham operator on actual total forms is d plus its metric codifferential. -/
def totalFormHodgeDirac :
    TotalSmoothDifferentialForm (n := n) M →ₗ[ℂ] TotalSmoothDifferentialForm (n := n) M :=
  totalFormExteriorDerivative (n := n) (M := M) + totalFormCodifferential g

/-- The total Hodge Laplacian acts by the original degreewise Laplacian on every summand. -/
def totalFormHodgeLaplacian :
    TotalSmoothDifferentialForm (n := n) M →ₗ[ℂ] TotalSmoothDifferentialForm (n := n) M :=
  DirectSum.toModule ℂ ℕ (TotalSmoothDifferentialForm (n := n) M)
    (fun p ↦ (DirectSum.lof ℂ ℕ (fun q ↦ SmoothDifferentialForm (n := n) M q) p).comp
      (smoothFormHodgeLaplacian g p))

/-- The square of the actual Hodge--de Rham operator is the actual total Hodge Laplacian. -/
theorem totalFormHodgeDirac_comp :
    (totalFormHodgeDirac g).comp (totalFormHodgeDirac g) = totalFormHodgeLaplacian g := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  let L (p : ℕ) := DirectSum.lof ℂ ℕ F p
  let d := smoothFormExteriorDerivative (n := n) (M := M)
  let δ := smoothFormCodifferential g
  let D := totalFormHodgeDirac g
  -- The total operator has precisely its two original adjacent-degree components.
  have hzero (u : F 0) : D (L 0 u) = L 1 (d 0 u) := by
    simp [D, L, F, totalFormHodgeDirac, totalFormExteriorDerivative, totalFormCodifferential, d]
  have hsucc (p : ℕ) (u : F (p + 1)) :
      D (L (p + 1) u) = L (p + 2) (d (p + 1) u) + L p (δ p u) := by
    simp [D, L, F, totalFormHodgeDirac, totalFormExteriorDerivative, totalFormCodifferential,
      d, δ]
  have hdd (p : ℕ) (u : F p) : d (p + 1) (d p u) = 0 :=
    LinearMap.congr_fun (smoothFormExteriorDerivative_comp (n := n) (M := M) p) u
  have hδδ (p : ℕ) (u : F (p + 1 + 1)) : δ p (δ (p + 1) u) = 0 :=
    LinearMap.congr_fun (smoothFormCodifferential_comp g p) u
  -- Check the actual direct-sum generators, retaining the missing incoming term at degree zero.
  apply DirectSum.linearMap_ext
  intro p
  apply LinearMap.ext
  intro u
  simp only [LinearMap.comp_apply, totalFormHodgeLaplacian, DirectSum.toModule_lof]
  change D (D (L p u)) = L p (smoothFormHodgeLaplacian g p u)
  cases p with
  | zero =>
      rw [hzero, hsucc]
      rw [hdd, map_zero, zero_add]
      rfl
  | succ p =>
      rw [hsucc, map_add, hsucc]
      cases p with
      | zero =>
          rw [hzero, hdd, map_zero, zero_add, ← map_add]
          congr 1
          simp only [smoothFormHodgeLaplacian, LinearMap.add_apply, LinearMap.comp_apply, d, δ]
          exact add_comm _ _
      | succ p =>
          rw [hsucc, hdd, hδδ, map_zero, map_zero, zero_add, add_zero, ← map_add]
          congr 1
          simp only [smoothFormHodgeLaplacian, LinearMap.add_apply, LinearMap.comp_apply, d, δ]
          exact add_comm _ _

/-- On a compact manifold, d plus its metric adjoint has the same kernel as the Laplacian. -/
theorem totalFormHodgeDirac_ker_eq [CompactSpace M] :
    LinearMap.ker (totalFormHodgeDirac g) = LinearMap.ker (totalFormHodgeLaplacian g) := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  let L (p : ℕ) := DirectSum.lof ℂ ℕ F p
  let d := smoothFormExteriorDerivative (n := n) (M := M)
  let δ := smoothFormCodifferential g
  let D := totalFormHodgeDirac g
  -- The square identity gives the forward inclusion on the unchanged total form space.
  apply Submodule.ext
  intro u
  constructor
  · intro hu
    change D u = 0 at hu
    change totalFormHodgeLaplacian g u = 0
    rw [← totalFormHodgeDirac_comp, LinearMap.comp_apply, hu, map_zero]
  · intro hu
    change totalFormHodgeLaplacian g u = 0 at hu
    -- Each homogeneous component is harmonic, so its actual exterior derivative vanishes.
    have hcomponent (p : ℕ) :
        smoothFormHodgeLaplacian g p (u p) = 0 := by
      let proj := DirectSum.component ℂ ℕ F p
      have hmap : proj.comp (totalFormHodgeLaplacian g) =
          (smoothFormHodgeLaplacian g p).comp proj := by
        apply DirectSum.linearMap_ext
        intro q
        apply LinearMap.ext
        intro v
        by_cases hqp : q = p
        · subst q
          simp [proj, F, totalFormHodgeLaplacian]
        · simp [proj, F, totalFormHodgeLaplacian,
            DirectSum.component.of, hqp]
      have h := LinearMap.congr_fun hmap u
      rw [LinearMap.comp_apply, hu, map_zero] at h
      exact h.symm
    have hclosed (p : ℕ) : d p (u p) = 0 :=
      harmonicForms_le_closedForms g p (hcomponent p)
    -- For a positive-degree component, the remaining Laplacian term is d(delta u).
    have hcoclosed (p : ℕ) : δ p (u (p + 1)) = 0 := by
      have hdelta : d p (δ p (u (p + 1))) = 0 := by
        have h := hcomponent (p + 1)
        change d p (δ p (u (p + 1))) + δ (p + 1) (d (p + 1) (u (p + 1))) = 0 at h
        simpa only [hclosed, map_zero, add_zero] using h
      have hcompact : IsCompact (closure {x : M | (δ p (u (p + 1))).val x ≠ 0}) :=
        isClosed_closure.isCompact
      apply (smoothFormPairing_self_eq_zero_iff g p _ hcompact).mp
      rw [← smoothFormCodifferential_formalAdjoint g p _ _ hcompact]
      change smoothFormPairing g (p + 1) (d p (δ p (u (p + 1)))) (u (p + 1)) = 0
      rw [hdelta]
      unfold smoothFormPairing
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards with x
      unfold differentialFormInner
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro I _
      apply Finset.sum_eq_zero
      intro J _
      change ((starRingEnd ℂ) (0 : ℂ) * _) * _ = 0
      simp
    -- Both adjacent-degree contributions vanish, and the finite sum reconstructs u exactly.
    change D u = 0
    rw [← DirectSum.sum_support_of u, map_sum]
    apply Finset.sum_eq_zero
    intro p _
    change D (L p (u p)) = 0
    cases p with
    | zero =>
        simp [D, L, F, totalFormHodgeDirac, totalFormExteriorDerivative,
          totalFormCodifferential, show smoothFormExteriorDerivative 0 (u 0) = 0 from hclosed 0]
    | succ p =>
        simp [D, L, F, totalFormHodgeDirac, totalFormExteriorDerivative,
          totalFormCodifferential,
          show smoothFormExteriorDerivative (p + 1) (u (p + 1)) = 0 from hclosed (p + 1),
          show smoothFormCodifferential g p (u (p + 1)) = 0 from hcoclosed p]


/-- The L2 inner-product core on the original smooth forms for the specified metric density.
Only the pairing is packaged; no new norm or topology on smooth forms is installed. -/
@[instance_reducible]
def smoothFormL2Core [CompactSpace M] (p : ℕ) :
    InnerProductSpace.Core ℂ (SmoothDifferentialForm (n := n) M p) where
  inner := smoothFormPairing g p
  conj_inner_symm u v := by
    change conj (∫ x, differentialFormInner g p x (v.val x) (u.val x)
      ∂g.riemannianVolume) = _
    rw [← integral_conj]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x ↦
      (differentialFormInnerCore g p x).conj_inner_symm _ _
  re_inner_nonneg u := by
    change 0 ≤ RCLike.re (∫ x, differentialFormInner g p x (u.val x) (u.val x)
      ∂g.riemannianVolume)
    rw [← integral_re (integrable_differentialFormInner g p u u isClosed_closure.isCompact)]
    apply integral_nonneg
    intro x
    exact (differentialFormInnerCore g p x).re_inner_nonneg _
  add_left u v w := by
    have heq (x : M) : differentialFormInner g p x ((u + v).val x) (w.val x) =
        differentialFormInner g p x (u.val x) (w.val x) +
          differentialFormInner g p x (v.val x) (w.val x) :=
      (differentialFormInnerCore g p x).add_left _ _ _
    change (∫ x, differentialFormInner g p x ((u + v).val x) (w.val x)
      ∂g.riemannianVolume) = _
    simp_rw [heq]
    exact integral_add (integrable_differentialFormInner g p u w isClosed_closure.isCompact)
      (integrable_differentialFormInner g p v w isClosed_closure.isCompact)
  smul_left u v c := by
    have heq (x : M) : differentialFormInner g p x ((c • u).val x) (v.val x) =
        conj c * differentialFormInner g p x (u.val x) (v.val x) :=
      (differentialFormInnerCore g p x).smul_left _ _ _
    change (∫ x, differentialFormInner g p x ((c • u).val x) (v.val x)
      ∂g.riemannianVolume) = _
    simp_rw [heq]
    exact integral_const_mul _ _
  definite u hu :=
    (smoothFormPairing_self_eq_zero_iff g p u isClosed_closure.isCompact).mp hu

/-- The space of harmonic forms on a compact manifold is finite dimensional. -/
theorem finiteDimensional_harmonicForms [CompactSpace M] (p : ℕ) :
    FiniteDimensional ℂ (harmonicForms g p) := by
  -- The realization retains the original forms, metric density and Laplacian section map.
  obtain ⟨B, Φ, h, L, _hpair, hL, _hadj, R, hR⟩ :=
    exists_smoothFormHodgeLaplacian_parametrix g p
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := B.rank) B.Fiber
  let : FiniteDimensional ℂ L.toLinearMap.ker :=
    L.finiteDimensional_ker_of_isParametrix A A R hR
  -- The same section equivalence embeds the actual harmonic kernel into that smooth kernel.
  let inclusion : harmonicForms g p →ₗ[ℂ] L.toLinearMap.ker :=
    { toFun := fun u ↦ ⟨Φ u.val, by
        change L.toLinearMap (Φ u.val) = 0
        rw [hL, show smoothFormHodgeLaplacian g p u.val = 0 from u.property, map_zero]⟩
      map_add' := by intro u v; apply Subtype.ext; exact Φ.map_add u.val v.val
      map_smul' := by intro c u; apply Subtype.ext; exact Φ.map_smul c u.val }
  apply FiniteDimensional.of_injective inclusion
  intro u v huv
  apply Subtype.ext
  apply Φ.injective
  exact congrArg Subtype.val huv

/-- Every original smooth form is a harmonic form plus an actual Laplacian image.
This Laplacian splitting is also used by the finite total graded Hodge operator. -/
theorem exists_harmonic_add_hodgeLaplacian [CompactSpace M] (p : ℕ)
    (form : SmoothDifferentialForm (n := n) M p) :
    ∃ h : harmonicForms g p, ∃ u : SmoothDifferentialForm (n := n) M p,
      form = h.val + smoothFormHodgeLaplacian g p u := by
  -- The self-adjoint parametrix identifies its original smooth kernel with its cokernel.
  obtain ⟨B, Φ, h, L, _hpair, hL, hadj, R, hR⟩ :=
    exists_smoothFormHodgeLaplacian_parametrix g p
  let : IsSmoothPositiveMeasure (n := n) g.riemannianVolume :=
    g.isSmoothPositiveMeasure_riemannianVolume
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := B.rank) B.Fiber
  have hbij := L.bijective_adjointKer_to_coker_of_isParametrix h h A A R hR
    L.toLinearMap hadj
  obtain ⟨v, hv⟩ := hbij.2 (L.toLinearMap.range.mkQ (Φ form))
  have hdiff : Φ form - v.val ∈ L.toLinearMap.range := (Submodule.Quotient.eq _).mp hv.symm
  obtain ⟨w, hw⟩ := hdiff
  -- Transport these same representatives back; no completion or closed range is substituted.
  have hharmonic : Φ.symm v.val ∈ harmonicForms g p := by
    change smoothFormHodgeLaplacian g p (Φ.symm v.val) = 0
    apply Φ.injective
    rw [← hL, Φ.apply_symm_apply, show L.toLinearMap v.val = 0 from v.property, map_zero]
  refine ⟨⟨Φ.symm v.val, hharmonic⟩, Φ.symm w, ?_⟩
  apply Φ.injective
  rw [map_add, Φ.apply_symm_apply, ← hL, Φ.apply_symm_apply, hw]
  abel

/-- The Hodge decomposition is the unique L2-orthogonal harmonic/exact/coexact splitting. -/
theorem smoothForm_hodge_decomposition [CompactSpace M] (p : ℕ) :
    (∀ (harmonic : harmonicForms g p)
        (exactForm : deRhamExactForms (n := n) (M := M) p),
      smoothFormPairing g p harmonic.val exactForm.val = 0) ∧
    (∀ (harmonic : harmonicForms g p) (coexact : deRhamCoexactForms g p),
      smoothFormPairing g p harmonic.val coexact.val = 0) ∧
    (∀ (exactForm : deRhamExactForms (n := n) (M := M) p)
        (coexact : deRhamCoexactForms g p),
      smoothFormPairing g p exactForm.val coexact.val = 0) ∧
    (∀ form : SmoothDifferentialForm (n := n) M p,
      ∃! components : harmonicForms g p ×
          deRhamExactForms (n := n) (M := M) p × deRhamCoexactForms g p,
        form = components.1.val + components.2.1.val + components.2.2.val) := by
  classical
  let F := SmoothDifferentialForm (n := n) M
  let P := smoothFormPairing g
  let d := smoothFormExteriorDerivative (n := n) (M := M)
  let δ := smoothFormCodifferential g
  let core (q : ℕ) := smoothFormL2Core g q
  have hzero_left (q : ℕ) (u : F q) : P q 0 u = 0 := by
    let : InnerProductSpace.Core ℂ (F q) := core q
    exact InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) u
  have hzero_right (q : ℕ) (u : F q) : P q u 0 = 0 := by
    let : InnerProductSpace.Core ℂ (F q) := core q
    exact InnerProductSpace.Core.inner_zero_right (𝕜 := ℂ) u
  have hsym (q : ℕ) (u v : F q) : conj (P q v u) = P q u v :=
    (core q).conj_inner_symm _ _
  have hadd (q : ℕ) (u v w : F q) : P q u (v + w) = P q u v + P q u w := by
    let : InnerProductSpace.Core ℂ (F q) := core q
    exact InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) u v w
  have hadj (q : ℕ) (u : F q) (v : F (q + 1)) : P (q + 1) (d q u) v = P q u (δ q v) :=
    smoothFormCodifferential_formalAdjoint g q u v isClosed_closure.isCompact
  -- Harmonic forms are closed; the remaining energy term also makes them coclosed.
  have hcoclosed (q : ℕ) (h : harmonicForms g (q + 1)) : δ q h.val = 0 := by
    have hd : d (q + 1) h.val = 0 := harmonicForms_le_closedForms g (q + 1) h.property
    have hΔ : d q (δ q h.val) + δ (q + 1) (d (q + 1) h.val) = 0 := h.property
    rw [hd, map_zero, add_zero] at hΔ
    have henergy := hadj q (δ q h.val) h.val
    rw [hΔ, hzero_left] at henergy
    exact (core q).definite _ henergy.symm
  have hHE (h : harmonicForms g p) (e : deRhamExactForms (n := n) (M := M) p) :
      P p h.val e.val = 0 := by
    cases p with
    | zero =>
        have he : e.val = 0 := e.property
        rw [he, hzero_right]
    | succ p =>
        obtain ⟨u, hu⟩ := e.property
        change d p u = e.val at hu
        rw [← hu, ← hsym, hadj, hcoclosed, hzero_right, map_zero]
  have hHC (h : harmonicForms g p) (c : deRhamCoexactForms g p) :
      P p h.val c.val = 0 := by
    obtain ⟨u, hu⟩ := c.property
    change δ p u = c.val at hu
    have hd : d p h.val = 0 := harmonicForms_le_closedForms g p h.property
    rw [← hu, ← hadj, hd, hzero_left]
  have hEC (e : deRhamExactForms (n := n) (M := M) p) (c : deRhamCoexactForms g p) :
      P p e.val c.val = 0 := by
    obtain ⟨u, hu⟩ := c.property
    change δ p u = c.val at hu
    have hd : d p e.val = 0 := deRhamExactForms_le_closedForms p e.property
    rw [← hu, ← hadj, hd, hzero_left]
  refine ⟨hHE, hHC, hEC, ?_⟩
  -- Positivity makes a zero sum of the three orthogonal components trivial.
  have hzeroTriple (h : harmonicForms g p)
      (e : deRhamExactForms (n := n) (M := M) p) (c : deRhamCoexactForms g p)
      (heq : h.val + e.val + c.val = 0) : h = 0 ∧ e = 0 ∧ c = 0 := by
    have hh : h.val = 0 := by
      apply (core p).definite
      have hsum := congrArg (P p h.val) heq
      rw [hadd, hadd, hHE, hHC, hzero_right, add_zero, add_zero] at hsum
      exact hsum
    have hec : e.val + c.val = 0 := by simpa only [hh, zero_add] using heq
    have he : e.val = 0 := by
      apply (core p).definite
      have hsum := congrArg (P p e.val) hec
      rw [hadd, hEC, hzero_right, add_zero] at hsum
      exact hsum
    have hc : c.val = 0 := by simpa only [he, zero_add] using hec
    exact ⟨Subtype.ext hh, Subtype.ext he, Subtype.ext hc⟩
  intro form
  -- Expand the actual Laplacian image supplied by the harmonic-plus-Laplacian splitting.
  obtain ⟨h, u, hu⟩ := exists_harmonic_add_hodgeLaplacian g p form
  have hexists : ∃ components : harmonicForms g p ×
      deRhamExactForms (n := n) (M := M) p × deRhamCoexactForms g p,
      form = components.1.val + components.2.1.val + components.2.2.val := by
    cases p with
    | zero =>
        refine ⟨⟨h, 0, ⟨δ 0 (d 0 u), ⟨d 0 u, rfl⟩⟩⟩, ?_⟩
        change form = h.val + 0 + δ 0 (d 0 u)
        rw [add_zero]
        exact hu
    | succ p =>
        refine ⟨⟨h, ⟨d p (δ p u), ⟨δ p u, rfl⟩⟩,
          ⟨δ (p + 1) (d (p + 1) u), ⟨d (p + 1) u, rfl⟩⟩⟩, ?_⟩
        change form = h.val + d p (δ p u) + δ (p + 1) (d (p + 1) u)
        change form = h.val + (d p (δ p u) + δ (p + 1) (d (p + 1) u)) at hu
        exact hu.trans (add_assoc _ _ _).symm
  obtain ⟨components, hcomponents⟩ := hexists
  refine ⟨components, hcomponents, ?_⟩
  intro other hother
  have hdiff : (other.1 - components.1).val + (other.2.1 - components.2.1).val +
      (other.2.2 - components.2.2).val = 0 := by
    change (other.1.val - components.1.val) + (other.2.1.val - components.2.1.val) +
      (other.2.2.val - components.2.2.val) = 0
    calc
      _ = (other.1.val + other.2.1.val + other.2.2.val) -
          (components.1.val + components.2.1.val + components.2.2.val) := by abel
      _ = 0 := by rw [← hother, ← hcomponents, sub_self]
  obtain ⟨hh, he, hc⟩ := hzeroTriple _ _ _ hdiff
  exact Prod.ext (sub_eq_zero.mp hh) (Prod.ext (sub_eq_zero.mp he) (sub_eq_zero.mp hc))

/-- The harmonic class map is inclusion into closed forms followed by the actual quotient. -/
def harmonicDeRhamClass [CompactSpace M] (p : ℕ) :
    harmonicForms g p →ₗ[ℂ] DeRhamCohomology (n := n) M p :=
  (deRhamClass (n := n) (M := M) p).comp
    (Submodule.inclusion (harmonicForms_le_closedForms g p))

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates the de Rham quotient and unique original harmonic
-- representatives.
/-- Every actual de Rham class has one and only one harmonic representative. -/
theorem harmonicDeRhamClass_bijective [CompactSpace M] (p : ℕ) :
    Function.Bijective (harmonicDeRhamClass g p) := by
  classical
  let C := deRhamClosedForms (n := n) (M := M) p
  let E := deRhamExactForms (n := n) (M := M) p
  let Q := E.comap C.subtype
  let d := smoothFormExteriorDerivative (n := n) (M := M) p
  let : InnerProductSpace.Core ℂ (SmoothDifferentialForm (n := n) M p) := smoothFormL2Core g p
  obtain ⟨hHE, _hHC, _hEC, hdecomp⟩ := smoothForm_hodge_decomposition g p
  constructor
  · -- A harmonic representative of the zero class is exact, hence orthogonal to itself.
    have hzero (h : harmonicForms g p) (hh : harmonicDeRhamClass g p h = 0) : h = 0 := by
      have hexact : h.val ∈ E := (Submodule.Quotient.mk_eq_zero Q).mp hh
      apply Subtype.ext
      exact (smoothFormL2Core g p).definite h.val (hHE h ⟨h.val, hexact⟩)
    intro u v huv
    apply sub_eq_zero.mp
    apply hzero
    rw [map_sub, huv, sub_self]
  · -- Decompose an actual closed representative of the original algebraic quotient.
    intro a
    obtain ⟨u, hu⟩ := Q.mkQ_surjective a
    obtain ⟨components, hcomponents, _hunique⟩ := hdecomp u.val
    have hdh : d components.1.val = 0 := harmonicForms_le_closedForms g p components.1.property
    have hde : d components.2.1.val = 0 := deRhamExactForms_le_closedForms p components.2.1.property
    have hdc : d components.2.2.val = 0 := by
      have heq := congrArg d hcomponents
      rw [map_add, map_add, hdh, hde, zero_add, zero_add] at heq
      exact heq.symm.trans u.property
    -- A closed coexact form has zero squared norm by the same formal-adjoint identity.
    have hc : components.2.2.val = 0 := by
      obtain ⟨v, hv⟩ := components.2.2.property
      change smoothFormCodifferential g p v = components.2.2.val at hv
      have hadj := smoothFormCodifferential_formalAdjoint g p components.2.2.val v
        isClosed_closure.isCompact
      change smoothFormPairing g (p + 1) (d components.2.2.val) v = _ at hadj
      rw [hdc, hv] at hadj
      have hz : smoothFormPairing g (p + 1) 0 v = 0 := by
        let : InnerProductSpace.Core ℂ (SmoothDifferentialForm (n := n) M (p + 1)) :=
          smoothFormL2Core g (p + 1)
        exact InnerProductSpace.Core.inner_zero_left (𝕜 := ℂ) v
      exact (smoothFormL2Core g p).definite _ (hadj.symm.trans hz)
    refine ⟨components.1, ?_⟩
    have hclass : harmonicDeRhamClass g p components.1 = Q.mkQ u := by
      apply (Submodule.Quotient.eq Q).mpr
      change components.1.val - u.val ∈ E
      have hdiff : components.1.val - u.val = -components.2.1.val := by
        rw [hcomponents, hc, add_zero]
        abel
      rw [hdiff]
      exact E.neg_mem components.2.1.property
    exact hclass.trans hu

/-- The canonical Hodge isomorphism from harmonic forms to the original de Rham quotient. -/
def harmonicDeRhamEquiv [CompactSpace M] (p : ℕ) :
    harmonicForms g p ≃ₗ[ℂ] DeRhamCohomology (n := n) M p :=
  LinearEquiv.ofBijective (harmonicDeRhamClass g p) (harmonicDeRhamClass_bijective g p)


end AtiyahSinger
