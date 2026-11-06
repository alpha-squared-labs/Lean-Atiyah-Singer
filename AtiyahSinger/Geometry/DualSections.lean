/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.VectorBundle.Constructions
public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import Mathlib.Topology.VectorBundle.Hom

/-!
# The complex dual bundle and its smooth sections

Public module ID: M1169.

D01/D02 and the geometric input for SG III.2.15(2). The fiber is the actual
continuous complex-linear dual, with the canonical mathlib Hom-bundle topology.
Its model fiber is the dual of C^r. For the existing Euclidean Bessel coordinates
we write a covector as its values on the standard basis in a primal frame.
The resulting coefficients transform by the inverse transpose, not the adjoint.

Smoothness and the evaluation pairing do not use a Hermitian metric. A smooth
Hermitian metric subsequently gives a conjugate-linear equivalence of smooth
sections. This is a separate theorem; it is not built into the definition of E*.
The full conversion to the project's Euclidean-model FiberBundle API is not asserted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]

/-- The actual complex-linear dual in each fiber, carrying its operator norm. -/
abbrev DualBundle (x : M) : Type _ := StrongDual ℂ (E x)

variable [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Coefficients of a dual section are its evaluations on the local primal basis. -/
def dualSectionInFrame
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (α : ∀ x, DualBundle E x) (x : M) :
    EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun i ↦ α x (e.symmL ℂ x (EuclideanSpace.single i 1)))

/-- Dual coordinates transform by the inverse of the primal coordinate change. -/
theorem dualSectionInFrame_coordChange
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    (α : ∀ x, DualBundle E x) (x : M) (hx : x ∈ e.baseSet ∩ e'.baseSet) (i : Fin r) :
    dualSectionInFrame E e' α x i =
      ∑ j, (e'.coordChangeL ℂ e x (EuclideanSpace.single i 1)) j *
        dualSectionInFrame E e α x j := by
  /- Express the i-th e'-basis vector in the e-frame using the reverse transition
  e' -> e. Expand in the standard basis and apply the complex-linear covector.
  This is the inverse transpose rule for column covector coefficients; no complex
  conjugation occurs. Both frame inverses are used only on their common base set. -/
  classical
  -- Expand the very same inverse-frame vector in the old primal frame.
  let v := e'.symmL ℂ x (EuclideanSpace.single i 1)
  have hcoord : (e ⟨x, v⟩).2 =
      e'.coordChangeL ℂ e x (EuclideanSpace.single i 1) := by
    rw [e'.coordChangeL_apply e hx.symm]
    simp only [v, e'.symmL_apply hx.2]
  have hexpand : ∑ j : Fin r, (e ⟨x, v⟩).2 j •
      e.symmL ℂ x (EuclideanSpace.single j 1) = v := by
    have heq := congrArg (e.symmL ℂ x)
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨x, v⟩).2))
    calc
      _ = e.symmL ℂ x ((e ⟨x, v⟩).2) := by
        simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
      _ = v := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx.1 v]
        exact e.symmL_continuousLinearMapAt hx.1 v
  -- Evaluation is complex linear: this transition has no conjugation.
  change α x v = _
  rw [← hexpand, map_sum]
  simp only [map_smul, smul_eq_mul, hcoord, dualSectionInFrame]

/-- A dual section is smooth precisely when its coefficients in every dual frame are smooth. -/
def IsSmoothDualSection (α : ∀ x, DualBundle E x) : Prop :=
  ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) (_he : MemTrivializationAtlas e),
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
      (dualSectionInFrame E e α) e.baseSet

/-- The zero covector section is smooth. -/
theorem isSmoothDualSection_zero :
    IsSmoothDualSection (n := n) (r := r) E (fun _ ↦ 0) := by
  /- All evaluations of the zero functional are zero. In every dual frame the
  coefficient function is therefore constant, hence real-smooth on the base set. -/
  intro e he
  apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr
  intro x _
  ext i
  rfl

/-- Addition preserves smoothness of actual dual sections. -/
theorem isSmoothDualSection_add (α β : ∀ x, DualBundle E x)
    (hα : IsSmoothDualSection (n := n) (r := r) E α)
    (hβ : IsSmoothDualSection (n := n) (r := r) E β) :
    IsSmoothDualSection (n := n) (r := r) E (α + β) := by
  /- Evaluation on each local basis vector is additive in the covector. Thus the
  coordinate vector of α+β is the sum of two smooth coordinate vectors. -/
  intro e he
  -- The coordinates retain addition of the original complex-linear functionals.
  apply ((hα e he).add (hβ e he)).congr
  intro x _
  ext i
  rfl

/-- Complex scalar multiplication preserves smoothness of dual sections. -/
theorem isSmoothDualSection_smul (c : ℂ) (α : ∀ x, DualBundle E x)
    (hα : IsSmoothDualSection (n := n) (r := r) E α) :
    IsSmoothDualSection (n := n) (r := r) E (c • α) := by
  /- The coordinate vector of cα is c times the coordinate vector of α. Fixed
  complex scalar multiplication is real-smooth, so the chart condition is preserved. -/
  intro e he
  -- Fixed complex scalar multiplication is a real-smooth linear operation.
  have hscale := ((c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))).restrictScalars
    ℝ).contMDiff (n := ∞)
  apply (hscale.comp_contMDiffOn (hα e he)).congr
  intro x _
  ext i
  rfl

/-- The standard space of smooth sections of the complex dual bundle. -/
def smoothDualSections : Submodule ℂ (∀ x, DualBundle E x) where
  carrier := {α | IsSmoothDualSection (n := n) (r := r) E α}
  zero_mem' := isSmoothDualSection_zero E
  add_mem' := fun hα hβ ↦ isSmoothDualSection_add E _ _ hα hβ
  smul_mem' := fun c _ hα ↦ isSmoothDualSection_smul E c _ hα

/-- Evaluating a smooth covector section on a smooth vector section is a smooth scalar function. -/
theorem contMDiff_dualSection_eval
    (α : smoothDualSections (n := n) (r := r) E)
    (u : smoothSections (n := n) (r := r) E) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ α.val x (u.val x)) := by
  /- On each frame base set, expand u in its basis. Evaluation is the finite sum
  of products of primal and dual coefficients. Both are smooth by their definitions.
  The frame base sets cover M, so locality gives global real smoothness. -/
  classical
  intro x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  -- In this same frame, both primal and dual coefficient functions are smooth.
  have hprimal (i : Fin r) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ (e ⟨y, u.val y⟩).2 i) e.baseSet :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contDiff.contMDiff
      |>.comp_contMDiffOn (u.property e inferInstance)
  have hdual (i : Fin r) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ dualSectionInFrame E e α.val y i) e.baseSet :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contDiff.contMDiff
      |>.comp_contMDiffOn (α.property e inferInstance)
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ ∑ i, (e ⟨y, u.val y⟩).2 i * dualSectionInFrame E e α.val y i)
      e.baseSet := by
    apply contMDiffOn_finsetSum
    intro i _
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      ((hprimal i).prodMk_space (hdual i))
  -- Expand the actual vector; evaluation gives the local finite sum.
  have heval (y : M) (hy : y ∈ e.baseSet) :
      α.val y (u.val y) =
        ∑ i, (e ⟨y, u.val y⟩).2 i * dualSectionInFrame E e α.val y i := by
    have hexpand : ∑ i : Fin r, (e ⟨y, u.val y⟩).2 i •
        e.symmL ℂ y (EuclideanSpace.single i 1) = u.val y := by
      have heq := congrArg (e.symmL ℂ y)
        ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨y, u.val y⟩).2))
      calc
        _ = e.symmL ℂ y ((e ⟨y, u.val y⟩).2) := by
          simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
        _ = u.val y := by
          rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy]
          exact e.symmL_continuousLinearMapAt hy _
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, smul_eq_mul, dualSectionInFrame]
  exact (hsum.congr heval).contMDiffAt (e.open_baseSet.mem_nhds hx)

variable [MeasurableSpace M] (μ : Measure M)

/-- The geometric bilinear pairing uses covector evaluation at the same base point. -/
def smoothDualSectionPairing (α : smoothDualSections (n := n) (r := r) E)
    (u : smoothSections (n := n) (r := r) E) : ℂ :=
  ∫ x, α.val x (u.val x) ∂μ

variable [BorelSpace M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothPositiveMeasure (n := n) μ]

/-- Smooth dual evaluation is integrable for a positive smooth density on a compact base. -/
theorem integrable_dualSection_eval
    (α : smoothDualSections (n := n) (r := r) E)
    (u : smoothSections (n := n) (r := r) E) :
    Integrable (fun x ↦ α.val x (u.val x)) μ := by
  /- The evaluation is smooth, hence continuous and bounded on compact M. The
  positive smooth density has finite total mass, so this complex function is integrable. -/
  -- The original density has finite mass; the evaluation map is already globally smooth.
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  exact (contMDiff_dualSection_eval E α u).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

end AtiyahSinger

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]

/- The explicit smooth-bundle premise and the inherited Hermitian premise concern the same
original atlas. Both are proof-irrelevant. Retain the original public parameters; the six
overlapping-instance lint exceptions below each apply to only one declaration. -/

set_option linter.overlappingInstances false in
set_option linter.unusedSectionVars false in
/-- A smooth Hermitian metric sends a smooth section to a smooth complex covector section. -/
theorem isSmoothDualSection_inner
    (u : smoothSections (n := n) (r := r) E) :
    IsSmoothDualSection (n := n) (r := r) E
      (fun x ↦ InnerProductSpace.toDualMap ℂ (E x) (u.val x)) := by
  /- In each frame the dual coefficients are the conjugates of u's coefficients
  multiplied by the smooth Gram matrix. Conjugation is real-smooth, and finite sums
  and products of these coefficients are smooth. No compactness is required. -/
  classical
  intro e he
  let := he
  -- Each coefficient is a finite sum of conjugate coordinates times the native Gram entries.
  have hcoord (i : Fin r) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (e ⟨x, u.val x⟩).2 i) e.baseSet :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contDiff.contMDiff
      |>.comp_contMDiffOn (u.property e he)
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Fin r → ℂ) ∞
      (fun x j ↦ ∑ i, conj ((e ⟨x, u.val x⟩).2 i) *
        inner ℂ (e.symmL ℂ x (EuclideanSpace.single i 1))
          (e.symmL ℂ x (EuclideanSpace.single j 1))) e.baseSet := by
    apply contMDiffOn_pi_space.mpr
    intro j
    apply contMDiffOn_finsetSum
    intro i _
    have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i)
    exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp_contMDiffOn
      (hconj.prodMk_space (IsSmoothHermitianBundle.contMDiffOn_inner (n := n) e i j))
  have hP := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff (n := ∞)
  have hsmooth := hP.contMDiff.comp_contMDiffOn hsum
  -- Expand the actual vector in this same frame; the first inner-product slot conjugates scalars.
  apply hsmooth.congr
  intro x hx
  apply PiLp.ext
  intro j
  change inner ℂ (u.val x) (e.symmL ℂ x (EuclideanSpace.single j 1)) = _
  have hexpand : ∑ i : Fin r, (e ⟨x, u.val x⟩).2 i •
      e.symmL ℂ x (EuclideanSpace.single i 1) = u.val x := by
    have heq := congrArg (e.symmL ℂ x)
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨x, u.val x⟩).2))
    calc
      _ = e.symmL ℂ x ((e ⟨x, u.val x⟩).2) := by
        simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
      _ = u.val x := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
        exact e.symmL_continuousLinearMapAt hx _
  conv_lhs => rw [← hexpand]
  simp only [sum_inner, inner_smul_left]
  rfl

set_option linter.overlappingInstances false in
/-- Fiberwise Hermitian duality, as a conjugate-linear map of actual smooth sections. -/
def smoothHermitianDual :
    smoothSections (n := n) (r := r) E →ₗ⋆[ℂ] smoothDualSections (n := n) (r := r) E where
  toFun u := ⟨fun x ↦ InnerProductSpace.toDualMap ℂ (E x) (u.val x),
    isSmoothDualSection_inner E u⟩
  map_add' u v := Subtype.ext (funext fun x ↦
    (InnerProductSpace.toDualMap ℂ (E x)).map_add (u.val x) (v.val x))
  map_smul' c u := Subtype.ext (funext fun x ↦
    (InnerProductSpace.toDualMap ℂ (E x)).map_smulₛₗ c (u.val x))

set_option linter.overlappingInstances false in
/-- Smooth Hermitian duality is bijective, including on noncompact bases. -/
theorem bijective_smoothHermitianDual :
    Function.Bijective (smoothHermitianDual (n := n) (r := r) E) := by
  /- Each fiber is finite-dimensional by local triviality, so its Riesz map is
  bijective. The inverse field is smooth: locally invert the positive definite Gram
  matrix and conjugate the covector coefficients. These unique inverse vectors agree
  on overlaps and give a global smooth section. Pointwise uniqueness gives injectivity. -/
  classical
  open scoped Matrix.Norms.Elementwise in
    -- Finite-dimensional local triviality supplies the native fiberwise Riesz equivalences.
    let : ∀ x : M, FiniteDimensional ℂ (E x) := fun x ↦
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    let : ∀ x : M, CompleteSpace (E x) := fun x ↦ FiniteDimensional.complete ℂ (E x)
    constructor
    · intro u v huv
      apply Subtype.ext
      funext x
      apply (InnerProductSpace.toDualMap ℂ (E x)).injective
      exact congrArg (fun α : smoothDualSections (n := n) (r := r) E ↦ α.val x) huv
    · intro α
      let s (x : M) : E x := (InnerProductSpace.toDual ℂ (E x)).symm (α.val x)
      have hs : IsSmoothSection (n := n) (r := r) E s := by
        intro e he
        let := he
        let V := EuclideanSpace ℂ (Fin r)
        let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
        let G (x : M) : Matrix (Fin r) (Fin r) ℂ :=
          Matrix.gram ℂ (fun i ↦ e.symmL ℂ x (EuclideanSpace.single i 1))
        let toOp : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ] (V →L[ℂ] V) :=
          LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
        let toOpC : Matrix (Fin r) (Fin r) ℂ →L[ℝ] (V →L[ℂ] V) :=
          LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
        let A (x : M) : V →L[ℂ] V := toOpC (G x)
        -- The native metric's smooth Gram entries give a smooth operator-valued map.
        have hA : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
            A e.baseSet := by
          apply toOpC.contDiff.contMDiff.comp_contMDiffOn
          apply contMDiffOn_pi_space.mpr
          intro i
          apply contMDiffOn_pi_space.mpr
          intro j
          exact IsSmoothHermitianBundle.contMDiffOn_inner (n := n) e i j
        have hequiv (x : M) (hx : x ∈ e.baseSet) :
            ∃ H : V ≃L[ℂ] V, H.toContinuousLinearMap = A x := by
          -- The same frame transports a basis, so its actual Gram matrix is nonsingular.
          have hli : LinearIndependent ℂ
              (fun i : Fin r ↦ e.symmL ℂ x (EuclideanSpace.single i 1)) := by
            have hb := (EuclideanSpace.basisFun (Fin r) ℂ).toBasis.linearIndependent.map'
              (e.continuousLinearEquivAt ℂ x hx).symm.toLinearMap
              (LinearMap.ker_eq_bot.mpr (e.continuousLinearEquivAt ℂ x hx).symm.injective)
            simpa only [Function.comp_def, LinearEquiv.coe_coe,
              ContinuousLinearEquiv.coe_toLinearEquiv, OrthonormalBasis.coe_toBasis,
              EuclideanSpace.basisFun_apply,
              Trivialization.symm_continuousLinearEquivAt_eq] using hb
          have hunit : IsUnit (G x) :=
            (Matrix.isUnit_iff_isUnit_det _).mpr
              (isUnit_iff_ne_zero.mpr (Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hli))
          let L := (LinearEquiv.ofBijective (G x).mulVecLin
            ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
              Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
          refine ⟨P.trans (L.trans P.symm), ?_⟩
          ext v i
          rfl
        -- Inversion is smooth locally on the invertible operators, without any compactness bound.
        have hinverse : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞
            (fun x ↦ (A x).inverse) e.baseSet := by
          intro x hx
          obtain ⟨H, hH⟩ := hequiv x hx
          have hi : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A x) := by
            rw [← hH]
            exact (contDiffAt_map_inverse H).restrict_scalars ℝ
          exact hi.contMDiffAt.comp_contMDiffWithinAt x (hA x hx)
        let b (x : M) : V := WithLp.toLp 2
          (fun i ↦ conj (dualSectionInFrame E e α.val x i))
        have hb : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ b e.baseSet := by
          have hP := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin r ↦ ℂ)).symm.contDiff (n := ∞)
          apply hP.contMDiff.comp_contMDiffOn
          apply contMDiffOn_pi_space.mpr
          intro i
          let hp := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ)
          have hc := hp.contDiff.contMDiff.comp_contMDiffOn (α.property e he)
          exact Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn hc
        have heval : ContDiff ℝ ∞ (fun z : (V →L[ℂ] V) × V ↦ z.1 z.2) :=
          (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
        have hcoordSmooth := heval.contMDiff.comp_contMDiffOn (hinverse.prodMk_space hb)
        -- Test the native inverse Riesz equation on the same basis to identify its coordinates.
        have hcoord (x : M) (hx : x ∈ e.baseSet) : A x (e ⟨x, s x⟩).2 = b x := by
          apply PiLp.ext
          intro i
          have htest := congrArg (starRingEnd ℂ)
            (InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := E x)
              (x := e.symmL ℂ x (EuclideanSpace.single i 1)) (y := α.val x))
          rw [inner_conj_symm] at htest
          change inner ℂ (e.symmL ℂ x (EuclideanSpace.single i 1)) (s x) = _ at htest
          have hexpand : ∑ j : Fin r, (e ⟨x, s x⟩).2 j •
              e.symmL ℂ x (EuclideanSpace.single j 1) = s x := by
            have heq := congrArg (e.symmL ℂ x)
              ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨x, s x⟩).2))
            calc
              _ = e.symmL ℂ x ((e ⟨x, s x⟩).2) := by
                simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
              _ = s x := by
                rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
                exact e.symmL_continuousLinearMapAt hx _
          conv_lhs at htest => rw [← hexpand]
          change (∑ j, inner ℂ (e.symmL ℂ x (EuclideanSpace.single i 1))
              (e.symmL ℂ x (EuclideanSpace.single j 1)) * (e ⟨x, s x⟩).2 j) =
            conj (α.val x (e.symmL ℂ x (EuclideanSpace.single i 1)))
          simpa only [inner_sum, inner_smul_right, mul_comm] using htest
        apply hcoordSmooth.congr
        intro x hx
        obtain ⟨H, hH⟩ := hequiv x hx
        change (e ⟨x, s x⟩).2 = (A x).inverse (b x)
        rw [← hH, ContinuousLinearMap.inverse_equiv]
        apply H.injective
        simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply,
          ← hH] using hcoord x hx
      -- The original fiber inverse recovers the specified covector at each base point.
      refine ⟨⟨s, hs⟩, ?_⟩
      apply Subtype.ext
      funext x
      exact (InnerProductSpace.toDual ℂ (E x)).apply_symm_apply (α.val x)

set_option linter.overlappingInstances false in
/-- The usual metric identification of E and E*, conjugate-linear over the complex numbers. -/
def smoothHermitianDualEquiv :
    smoothSections (n := n) (r := r) E ≃ₗ⋆[ℂ] smoothDualSections (n := n) (r := r) E :=
  LinearEquiv.ofBijective (smoothHermitianDual E) (bijective_smoothHermitianDual E)

set_option linter.overlappingInstances false in
/-- The metric identification retains the pointwise Hermitian evaluation formula. -/
theorem smoothHermitianDualEquiv_apply
    (u : smoothSections (n := n) (r := r) E) (x : M) (v : E x) :
    (smoothHermitianDualEquiv E u).val x v = inner ℂ (u.val x) v := by
  /- The equivalence keeps the forward map of smoothHermitianDual. That map is
  the actual fiberwise toDualMap, whose evaluation is precisely the Hermitian inner product. -/
  rfl

set_option linter.overlappingInstances false in
/-- The bilinear E*–E integral becomes the Hermitian integral under the metric identification. -/
theorem smoothDualSectionPairing_hermitian [MeasurableSpace M] (μ : Measure M)
    (v u : smoothSections (n := n) (r := r) E) :
    smoothDualSectionPairing E μ (smoothHermitianDualEquiv E v) u =
      smoothSectionPairing μ E v u := by
  /- The preceding pointwise formula identifies the two integrands at every point.
  Thus their Bochner integrals agree by congruence. This identity itself does not
  require compactness or integrability; the nondegeneracy theorems impose those separately. -/
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x ↦ smoothHermitianDualEquiv_apply E v x (u.val x))

end AtiyahSinger
