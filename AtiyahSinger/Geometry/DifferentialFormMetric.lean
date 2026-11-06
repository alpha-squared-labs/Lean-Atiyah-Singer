/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DifferentialForms
public import AtiyahSinger.Geometry.HermitianPairing
public import AtiyahSinger.Geometry.TangentMusical
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Support

import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# The metric pairing and Riemannian density of differential forms

Public module ID: M1165.

D09: the supplied native smooth tangent metric induces the standard Hermitian
pairing on the same complex-valued real alternating tangent tensors used by
`SmoothDifferentialForm`. An explicit inverse-Gram contraction fixes its
normalization: the ordered-tuple sum is divided by p!, so increasing exterior
products of an orthonormal coframe have norm one. Its coordinate basis is an
implementation choice in each original tangent fiber, not a smooth global frame.
The orthonormal-frame identity below makes the basis-independent meaning explicit.

The Riemannian measure is specified in every original chart by the square root
of the determinant of the pulled-back tangent metric. This is a density, not a
volume form. Its construction uses a Hausdorff, second-countable base.
No orientation, compactness, positive dimension, connectedness or nonempty
hypothesis is imposed. The zero-dimensional determinant is one.
The integral pairing uses precisely this measure and this induced fiber pairing.
Its compact-test integrability supports the formal adjoint on noncompact bases.

Sources: Lawson--Michelsohn, Spin Geometry, II.5, printed pp.123--125, uses the
induced form metric, formal adjoint and Hodge Laplacian. Its orientability note
continues on p.126. The explicit inverse-Gram formula and chart-density measure
construction are project supplements to those passages. Complex coefficients
use conjugation in the first variable, consistently with mathlib's convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Module
open scoped BigOperators Manifold ContDiff ComplexConjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- The Hermitian metric on alternating forms induced by the supplied real tangent metric.
The factor 1/p! compensates for summation over ordered tuples, including repeated indices. -/
def differentialFormInner (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (α β : DifferentialFormFiber (n := n) p x) : ℂ :=
  let e : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x :=
    fun i ↦ EuclideanSpace.single i 1
  let gram : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ g.inner x (e i) (e j)
  (p.factorial : ℂ)⁻¹ * ∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
    conj (α (fun k ↦ e (I k))) * β (fun k ↦ e (J k)) *
      ∏ k : Fin p, ((gram⁻¹) (I k) (J k) : ℂ)

set_option maxHeartbeats 1000000 in

/-- The induced Hermitian pairing is the same inverse-Gram contraction in every basis.
This basis-independence formula is used by both the orthonormal-frame identity and the
coordinate proof of smoothness; it preserves the normalization on ordered tuples. -/
theorem differentialFormInner_eq_sum_basis
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (b : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (α β : DifferentialFormFiber (n := n) p x) :
    let gram : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ g.inner x (b i) (b j)
    differentialFormInner g p x α β =
      (p.factorial : ℂ)⁻¹ * ∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
        conj (α (fun k ↦ b (I k))) * β (fun k ↦ b (J k)) *
          ∏ k : Fin p, (gram⁻¹ (I k) (J k) : ℂ) := by
  classical
  -- Compare the original implementation basis with the supplied basis.
  let a : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ g.inner x (a i) (a j)
  let H : Matrix (Fin n) (Fin n) ℝ := fun i j ↦ g.inner x (b i) (b j)
  let C : Matrix (Fin n) (Fin n) ℝ := a.toMatrix b
  let D : Matrix (Fin n) (Fin n) ℝ := b.toMatrix a
  have hCD : C * D = 1 := a.toMatrix_mul_toMatrix_flip b
  have hchange : C.transpose * G * C = H := by
    have hG : LinearMap.BilinForm.toMatrix a (g.inner x).toBilinForm = G := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl
    have hH : LinearMap.BilinForm.toMatrix b (g.inner x).toBilinForm = H := by
      ext i j
      rw [LinearMap.BilinForm.toMatrix_apply]
      rfl
    simpa only [hG, hH] using
      LinearMap.BilinForm.toMatrix_mul_basis_toMatrix a b (g.inner x).toBilinForm
  -- Positivity makes the supplied Gram matrix invertible, also in dimension zero.
  have hpos : H.PosDef := by
    change Matrix.PosDef (fun i j : Fin n ↦ g.inner x (b i) (b j))
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      change (g.inner x) (b j) (b i) = (g.inner x) (b i) (b j)
      exact (g.symm x) _ _
    · intro v hv
      have hne : b.equivFun.symm v ≠ 0 := by
        intro h
        apply hv
        exact b.equivFun.symm.injective (h.trans (map_zero _).symm)
      convert (g.pos x) (b.equivFun.symm v) hne using 1
      rw [b.equivFun_symm_apply]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, dotProduct,
        Matrix.mulVec, Pi.star_apply, star_trivial]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [(g.symm x) (b j) (b i)]
      ring
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  -- The inverse Gram matrix transforms contravariantly under this same change of basis.
  have hCG : C.transpose * G = H * D := by
    rw [← hchange, Matrix.mul_assoc, hCD, Matrix.mul_one]
  have hinv : C * H⁻¹ * C.transpose = G⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    calc
      C * H⁻¹ * C.transpose * G = C * H⁻¹ * (C.transpose * G) :=
        Matrix.mul_assoc _ _ _
      _ = C * H⁻¹ * (H * D) := by rw [hCG]
      _ = C * D := by rw [Matrix.mul_assoc, H.nonsing_inv_mul_cancel_left D hunit]
      _ = 1 := hCD
  -- Expand each covariant tensor in the implementation basis by multilinearity.
  have hexpand (η : DifferentialFormFiber (n := n) p x) (I : Fin p → Fin n) :
      η (fun k ↦ b (I k)) = ∑ K : Fin p → Fin n,
        η (fun k ↦ a (K k)) * ∏ k, (C (K k) (I k) : ℂ) := by
    have hvec : (fun k ↦ b (I k)) =
        (fun k ↦ ∑ i, a.repr (b (I k)) i • a i) := by
      funext k
      exact (a.sum_repr _).symm
    rw [hvec]
    change η.toContinuousMultilinearMap _ = _
    rw [ContinuousMultilinearMap.map_sum]
    simp_rw [ContinuousMultilinearMap.map_smul_univ, Complex.real_smul, Complex.ofReal_prod]
    apply Finset.sum_congr rfl
    intro K hK
    change (∏ k, (C (K k) (I k) : ℂ)) * η (fun k ↦ a (K k)) = _
    ring
  -- Finite distributivity contracts each tensor slot independently; no degree bound is needed.
  have hcontract (A B : (Fin p → Fin n) → ℂ) (C W : Matrix (Fin n) (Fin n) ℂ) :
      (∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
        (∑ K : Fin p → Fin n, A K * ∏ k, C (K k) (I k)) *
        (∑ L : Fin p → Fin n, B L * ∏ k, C (L k) (J k)) *
        ∏ k, W (I k) (J k)) =
      ∑ K : Fin p → Fin n, ∑ L : Fin p → Fin n,
        A K * B L * ∏ k, (C * W * C.transpose) (K k) (L k) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext I
      arg 2
      ext J
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext I
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext K
      arg 2
      ext I
      rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext K
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro K hK
    apply Finset.sum_congr rfl
    intro L hL
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    have hprod : (∏ k, ∑ j, ∑ i, C (K k) i * W i j * C (L k) j) =
        ∑ J : Fin p → Fin n, ∑ I : Fin p → Fin n,
          ∏ k, C (K k) (I k) * W (I k) (J k) * C (L k) (J k) := by
      rw [Fintype.prod_sum]
      apply Finset.sum_congr rfl
      intro J hJ
      exact Fintype.prod_sum _
    rw [hprod, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro I hI
    simp only [Finset.prod_mul_distrib]
    ring
  -- Extend real matrix coefficients to complex scalars and retain conjugation in the first slot.
  let Cc : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ (C i j : ℂ)
  let Wc : Matrix (Fin n) (Fin n) ℂ := fun i j ↦ (H⁻¹ i j : ℂ)
  have hmatrix : Cc * Wc * Cc.transpose = (fun i j ↦ (G⁻¹ i j : ℂ)) := by
    ext i j
    have h := congrArg (fun T : Matrix (Fin n) (Fin n) ℝ ↦ (T i j : ℂ)) hinv
    simpa only [Matrix.mul_apply, Matrix.transpose_apply,
      Complex.ofReal_sum, Complex.ofReal_mul] using h
  have ha : (a : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) =
      (fun i ↦ EuclideanSpace.single i 1) := by
    funext i
    exact EuclideanSpace.basisFun_apply (Fin n) ℝ i
  suffices h : (p.factorial : ℂ)⁻¹ *
      (∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
        conj (α (fun k ↦ a (I k))) * β (fun k ↦ a (J k)) *
          ∏ k, (G⁻¹ (I k) (J k) : ℂ)) =
    (p.factorial : ℂ)⁻¹ *
      (∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
        conj (α (fun k ↦ b (I k))) * β (fun k ↦ b (J k)) *
          ∏ k, (H⁻¹ (I k) (J k) : ℂ)) by
    simpa only [differentialFormInner, G, H, ha] using h
  congr 1
  symm
  simp_rw [hexpand, map_sum, map_mul, map_prod, Complex.conj_ofReal]
  have h := hcontract (fun K ↦ conj (α (fun k ↦ a (K k))))
    (fun L ↦ β (fun k ↦ a (L k))) Cc Wc
  rw [hmatrix] at h
  exact h

/-- In any metric-orthonormal frame the induced metric is the usual exterior-power pairing. -/
theorem differentialFormInner_eq_sum_orthonormal
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (e : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x)
    (he : ∀ i j : Fin n, g.inner x (e i) (e j) = if i = j then 1 else 0)
    (α β : DifferentialFormFiber (n := n) p x) :
    differentialFormInner g p x α β =
      (p.factorial : ℂ)⁻¹ * ∑ I : Fin p → Fin n,
        conj (α (fun k ↦ e (I k))) * β (fun k ↦ e (I k)) := by
  classical
  -- Orthonormality gives linear independence; the original tangent dimension gives spanning.
  have hli : LinearIndependent ℝ e := by
    apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have h := congrArg (g.inner x (e i)) hc
    simpa [map_sum, map_smul, he] using h
  let a : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let : FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    Module.Finite.of_basis a
  let b : Basis (Fin n) ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    Basis.mk hli (hli.span_eq_top_of_card_eq_finrank'
      (Module.finrank_eq_card_basis a).symm).ge
  have hb : (b : Fin n → TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) = e :=
    Basis.coe_mk _ _
  -- In this basis the Gram matrix is the identity, so only equal tuples survive contraction.
  have hgram : (fun i j ↦ g.inner x (b i) (b j)) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simpa only [hb, Matrix.one_apply] using he i j
  rw [differentialFormInner_eq_sum_basis g p x b α β]
  rw [hgram]
  simp only [inv_one, hb]
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  simp only [Matrix.one_apply, apply_ite Complex.ofReal, Complex.ofReal_one,
    Complex.ofReal_zero, Fintype.prod_boole, ← funext_iff]
  simp

/-- The induced pairing of two smooth forms is a smooth complex-valued function. -/
theorem contMDiff_differentialFormInner
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ)
    (α β : SmoothDifferentialForm (n := n) M p) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ differentialFormInner g p x (α.val x) (β.val x)) := by
  classical
  -- Work in a genuine manifold chart; the implementation basis is not a global smooth frame.
  let V := EuclideanSpace ℝ (Fin n)
  let I₀ := 𝓘(ℝ, V)
  intro x
  let c := chartAt V x
  have hc := chart_mem_atlas V x
  let E (y : V) (i : Fin n) : TangentSpace I₀ (c.symm y) :=
    mfderiv I₀ I₀ c.symm y (EuclideanSpace.single i 1)
  let H (y : V) : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ g.inner (c.symm y) (E y i) (E y j)
  -- The bundled derivative of the inverse chart sends constant model vectors to smooth fields.
  have hframe (y : V) (hy : y ∈ c.target) (i : Fin n) :
      ContMDiffAt I₀ I₀.tangent ∞ (fun z ↦ (⟨c.symm z, E z i⟩ : TangentBundle I₀ M)) y := by
    have hcsm : ContMDiffAt I₀ I₀ ∞ c.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
    have hconst : ContMDiffAt I₀ I₀.tangent ∞
        (fun z : V ↦ (⟨z, EuclideanSpace.single i 1⟩ : TangentBundle I₀ V)) y := by
      apply contMDiffAt_totalSpace.mpr
      constructor
      · exact contMDiffAt_id
      · simpa only [trivializationAt_model_space_apply] using
          (contMDiffAt_const : ContMDiffAt I₀ 𝓘(ℝ, V) ∞
            (fun _ : V ↦ (EuclideanSpace.single i 1 : V)) y)
    exact (hcsm.contMDiffAt_tangentMap (X := ⟨y, EuclideanSpace.single i 1⟩)
      (m := ∞) (by simp)).comp y hconst
  have hmetric (y : V) (hy : y ∈ c.target) (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun z ↦ H z i j) y := by
    have hcsm : ContMDiffAt I₀ I₀ ∞ c.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
    have h : ContMDiffAt I₀ (I₀.prod 𝓘(ℝ, ℝ)) ∞
        (fun z ↦ (⟨c.symm z, H z i j⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ))) y := by
      apply ContMDiffAt.clm_bundle_apply₂ (F₁ := V) (F₂ := V)
      · exact g.contMDiff.contMDiffAt.comp y hcsm
      · exact hframe y hy i
      · exact hframe y hy j
    have hscalar := (contMDiffAt_totalSpace.mp h).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using hscalar)
  -- The same inverse derivative transports the standard basis and preserves positivity.
  let b (y : V) (hy : y ∈ c.target) : Basis (Fin n) ℝ (TangentSpace I₀ (c.symm y)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      ((mdifferentiable_of_mem_atlas (I := I₀) hc).symm.mfderiv hy).toLinearEquiv
  have hb (y : V) (hy : y ∈ c.target) (i : Fin n) : b y hy i = E y i := by
    change mfderiv I₀ I₀ c.symm y ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) = _
    rw [show (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i =
      EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply _ _ _]
  have hpos (y : V) (hy : y ∈ c.target) : (H y).PosDef := by
    have heq : H y = (fun i j ↦ g.inner (c.symm y) (b y hy i) (b y hy j)) := by
      ext i j
      simp only [hb, H]
    rw [heq]
    change Matrix.PosDef (fun i j : Fin n ↦ g.inner (c.symm y) ((b y hy) i) ((b y hy) j))
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      change g.inner (c.symm y) (b y hy j) (b y hy i) =
        g.inner (c.symm y) (b y hy i) (b y hy j)
      exact (g.symm (c.symm y)) _ _
    · intro v hv
      have hne : (b y hy).equivFun.symm v ≠ 0 := by
        intro h
        apply hv
        exact (b y hy).equivFun.symm.injective (h.trans (map_zero _).symm)
      convert (g.pos (c.symm y)) ((b y hy).equivFun.symm v) hne using 1
      rw [(b y hy).equivFun_symm_apply]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, dotProduct,
        Matrix.mulVec, Pi.star_apply, star_trivial]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [(g.symm (c.symm y)) ((b y hy) j) ((b y hy) i)]
      ring
  have hdet (y : V) (hy : y ∈ c.target) : (H y).det ≠ 0 :=
    ne_of_gt (hpos y hy).det_pos
  -- Determinants and adjugates are polynomial in the coefficients; positivity permits inversion.
  have hdet_smooth (F : V → Matrix (Fin n) (Fin n) ℝ) (y : V)
      (hF : ∀ i j, ContDiffAt ℝ ∞ (fun z ↦ F z i j) y) :
      ContDiffAt ℝ ∞ (fun z ↦ (F z).det) y := by
    simp only [Matrix.det_apply']
    apply ContDiffAt.sum
    intro σ hσ
    apply ContDiffAt.mul contDiffAt_const
    exact contDiffAt_prod (fun i hi ↦ hF (σ i) i)
  have hinv_smooth (y : V) (hy : y ∈ c.target) (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun z ↦ (H z)⁻¹ i j) y := by
    have hadj : ContDiffAt ℝ ∞ (fun z ↦ (H z).adjugate i j) y := by
      simp only [Matrix.adjugate_apply]
      apply hdet_smooth
      intro k l
      by_cases hk : k = j
      · subst k
        simpa only [Matrix.updateRow_self] using
          (contDiffAt_const : ContDiffAt ℝ ∞
            (fun _ : V ↦ (Pi.single i (1 : ℝ) : Fin n → ℝ) l) y)
      · simpa [Matrix.updateRow_apply, hk] using hmetric y hy k l
    simpa only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply,
      smul_eq_mul, Pi.inv_apply] using
      ((hdet_smooth H y (hmetric y hy)).inv (hdet y hy)).mul hadj
  -- Evaluate the original chart coefficients and contract them with the smooth inverse metric.
  let coeff (η : SmoothDifferentialForm (n := n) M p) (y : V) (I : Fin p → Fin n) : ℂ :=
    differentialFormInChart η.val c y (fun k ↦ EuclideanSpace.single (I k) 1)
  have hcoeff (η : SmoothDifferentialForm (n := n) M p) (y : V)
      (hy : y ∈ c.target) (I : Fin p → Fin n) :
      ContDiffAt ℝ ∞ (fun z ↦ coeff η z I) y := by
    exact (ContinuousAlternatingMap.apply ℝ V ℂ
      (fun k ↦ EuclideanSpace.single (I k) 1)).contDiff.contDiffAt.comp y
      ((η.property c hc).contDiffAt (c.open_target.mem_nhds hy))
  let f (y : V) : ℂ := (p.factorial : ℂ)⁻¹ *
    ∑ I : Fin p → Fin n, ∑ J : Fin p → Fin n,
      conj (coeff α y I) * coeff β y J * ∏ k, ((H y)⁻¹ (I k) (J k) : ℂ)
  have hf (y : V) (hy : y ∈ c.target) : ContDiffAt ℝ ∞ f y := by
    apply ContDiffAt.mul contDiffAt_const
    apply ContDiffAt.sum
    intro I hI
    apply ContDiffAt.sum
    intro J hJ
    apply ContDiffAt.mul
    · exact (Complex.conjCLE.contDiff.contDiffAt.comp y (hcoeff α y hy I)).mul
        (hcoeff β y hy J)
    · apply contDiffAt_prod
      intro k hk
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp y (hinv_smooth y hy (I k) (J k))
  -- Basis independence identifies this chart expression with the fixed global pairing.
  have heq (y : V) (hy : y ∈ c.target) :
      differentialFormInner g p (c.symm y) (α.val (c.symm y)) (β.val (c.symm y)) = f y := by
    rw [differentialFormInner_eq_sum_basis g p (c.symm y) (b y hy)]
    simp only [hb]
    rfl
  have hcx : c x ∈ c.target := c.map_source (mem_chart_source V x)
  have hs : ContDiffAt ℝ ∞ (fun y ↦
      differentialFormInner g p (c.symm y) (α.val (c.symm y)) (β.val (c.symm y))) (c x) := by
    apply (hf (c x) hcx).congr_of_eventuallyEq
    filter_upwards [c.open_target.mem_nhds hcx] with y hy
    exact heq y hy
  rw [contMDiffAt_iff_source]
  simpa only [mfld_simps, contMDiffWithinAt_univ, c, V, Function.comp_def] using
    (contMDiffAt_iff_contDiffAt.mpr hs)

/-- In every original chart, the metric Gram determinant gives a smooth positive density.
This fact is shared by measure gluing and the smooth-positive measure certificate. -/
private theorem smooth_positive_metric_chart_density
    (g : SmoothTangentMetric (n := n) (M := M))
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    let w := fun y ↦ Real.sqrt (Matrix.det (fun i j : Fin n ↦
      g.inner (c.symm y)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y (EuclideanSpace.single i 1))
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y (EuclideanSpace.single j 1))))
    ContDiffOn ℝ ∞ w c.target ∧ ∀ y ∈ c.target, 0 < w y := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I₀ := 𝓘(ℝ, V)
  let E (y : V) (i : Fin n) : TangentSpace I₀ (c.symm y) :=
    mfderiv I₀ I₀ c.symm y (EuclideanSpace.single i 1)
  let H (y : V) : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ g.inner (c.symm y) (E y i) (E y j)
  -- The bundled derivative of the inverse chart sends constant model vectors to smooth fields.
  have hframe (y : V) (hy : y ∈ c.target) (i : Fin n) :
      ContMDiffAt I₀ I₀.tangent ∞ (fun z ↦ (⟨c.symm z, E z i⟩ : TangentBundle I₀ M)) y := by
    have hcsm : ContMDiffAt I₀ I₀ ∞ c.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
    have hconst : ContMDiffAt I₀ I₀.tangent ∞
        (fun z : V ↦ (⟨z, EuclideanSpace.single i 1⟩ : TangentBundle I₀ V)) y := by
      apply contMDiffAt_totalSpace.mpr
      constructor
      · exact contMDiffAt_id
      · simpa only [trivializationAt_model_space_apply] using
          (contMDiffAt_const : ContMDiffAt I₀ 𝓘(ℝ, V) ∞
            (fun _ : V ↦ (EuclideanSpace.single i 1 : V)) y)
    exact (hcsm.contMDiffAt_tangentMap (X := ⟨y, EuclideanSpace.single i 1⟩)
      (m := ∞) (by simp)).comp y hconst
  have hmetric (y : V) (hy : y ∈ c.target) (i j : Fin n) :
      ContDiffAt ℝ ∞ (fun z ↦ H z i j) y := by
    have hcsm : ContMDiffAt I₀ I₀ ∞ c.symm y :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy
    have h : ContMDiffAt I₀ (I₀.prod 𝓘(ℝ, ℝ)) ∞
        (fun z ↦ (⟨c.symm z, H z i j⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ))) y := by
      apply ContMDiffAt.clm_bundle_apply₂ (F₁ := V) (F₂ := V)
      · exact g.contMDiff.contMDiffAt.comp y hcsm
      · exact hframe y hy i
      · exact hframe y hy j
    have hscalar := (contMDiffAt_totalSpace.mp h).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using hscalar)
  -- The same inverse derivative transports the standard basis and preserves positivity.
  let b (y : V) (hy : y ∈ c.target) : Basis (Fin n) ℝ (TangentSpace I₀ (c.symm y)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.map
      ((mdifferentiable_of_mem_atlas (I := I₀) hc).symm.mfderiv hy).toLinearEquiv
  have hb (y : V) (hy : y ∈ c.target) (i : Fin n) : b y hy i = E y i := by
    change mfderiv I₀ I₀ c.symm y ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis i) = _
    rw [show (EuclideanSpace.basisFun (Fin n) ℝ).toBasis i =
      EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply _ _ _]
  have hpos (y : V) (hy : y ∈ c.target) : (H y).PosDef := by
    have heq : H y = (fun i j ↦ g.inner (c.symm y) (b y hy i) (b y hy j)) := by
      ext i j
      simp only [hb, H]
    rw [heq]
    change Matrix.PosDef (fun i j : Fin n ↦ g.inner (c.symm y) ((b y hy) i) ((b y hy) j))
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    constructor
    · ext i j
      change g.inner (c.symm y) (b y hy j) (b y hy i) =
        g.inner (c.symm y) (b y hy i) (b y hy j)
      exact (g.symm (c.symm y)) _ _
    · intro v hv
      have hne : (b y hy).equivFun.symm v ≠ 0 := by
        intro h
        apply hv
        exact (b y hy).equivFun.symm.injective (h.trans (map_zero _).symm)
      convert (g.pos (c.symm y)) ((b y hy).equivFun.symm v) hne using 1
      rw [(b y hy).equivFun_symm_apply]
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, dotProduct,
        Matrix.mulVec, Pi.star_apply, star_trivial]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [(g.symm (c.symm y)) ((b y hy) j) ((b y hy) i)]
      ring
  constructor
  · intro y hy
    have hdet : ContDiffAt ℝ ∞ (fun z ↦ (H z).det) y := by
      simp only [Matrix.det_apply']
      apply ContDiffAt.sum
      intro σ hσ
      apply ContDiffAt.mul contDiffAt_const
      exact contDiffAt_prod (fun i hi ↦ hmetric y hy (σ i) i)
    exact (hdet.sqrt (hpos y hy).det_pos.ne').contDiffWithinAt
  · intro y hy
    exact Real.sqrt_pos.mpr (hpos y hy).det_pos

namespace SmoothTangentMetric

variable (g : SmoothTangentMetric (n := n) (M := M))
  [MeasurableSpace M] [BorelSpace M]

/-- A measure is the Riemannian volume exactly when each chart has density sqrt(det g).
The chart metric is evaluated on actual derivatives of that chart's inverse. -/
def IsRiemannianVolume (μ : Measure M) : Prop :=
  ∀ c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)),
    c ∈ atlas (EuclideanSpace ℝ (Fin n)) M →
      Measure.map c (μ.restrict c.source) =
        (volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal
          (Real.sqrt (Matrix.det (fun i j : Fin n ↦
            g.inner (c.symm y)
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y (EuclideanSpace.single i 1))
              (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y
                (EuclideanSpace.single j 1))))))

variable [T2Space M] [SecondCountableTopology M]

set_option maxHeartbeats 1200000 in

open Set Function in
open scoped Topology in
/-- On a Hausdorff, second-countable base, the chartwise metric density defines one
unique Borel measure on the original manifold. -/
theorem existsUnique_riemannianVolume :
    ∃! μ : Measure M, g.IsRiemannianVolume μ := by
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, V)
  let H (c : OpenPartialHomeomorph M V) (y : V) : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ g.inner (c.symm y)
      (mfderiv I I c.symm y (EuclideanSpace.single i 1))
      (mfderiv I I c.symm y (EuclideanSpace.single j 1))
  let w (c : OpenPartialHomeomorph M V) (y : V) := Real.sqrt (H c y).det
  have hw (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) :
      ContDiffOn ℝ ∞ (w c) c.target ∧ ∀ y ∈ c.target, 0 < w c y :=
    smooth_positive_metric_chart_density g c hc
  -- The derivative chain rule transforms the Gram matrix by transpose conjugation.
  have hchange (c d : OpenPartialHomeomorph M V)
      (hc : c ∈ atlas V M) (hd : d ∈ atlas V M)
      (y : V) (hy : y ∈ (c.symm.trans d).source) :
      w c y = |(fderiv ℝ (c.symm.trans d) y).det| * w d (c.symm.trans d y) := by
    let t := c.symm.trans d
    have ht : ContMDiffAt I I ∞ t y := by
      exact (contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd) hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hc) hy.1)
    have hds : ContMDiffAt I I ∞ d.symm (t y) :=
      contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hd)
        (t.map_source hy).1
    have hbase : d.symm (t y) = c.symm y := d.left_inv hy.2
    have hevent : d.symm ∘ t =ᶠ[nhds y] c.symm := by
      filter_upwards [t.open_source.mem_nhds hy] with z hz
      exact d.left_inv hz.2
    have hder : mfderiv I I c.symm y =
        (mfderiv I I d.symm (t y)).comp (fderiv ℝ t y) := by
      have h := hevent.mfderiv_eq (I := I) (I' := I)
      rw [mfderiv_comp y (hds.mdifferentiableAt (by simp))
        (ht.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at h
      ext v
      exact congrArg (fun f ↦ f v) h.symm
    let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let B : LinearMap.BilinForm ℝ V := (g.inner (d.symm (t y))).toBilinForm.comp
      (mfderiv I I d.symm (t y)).toLinearMap
      (mfderiv I I d.symm (t y)).toLinearMap
    let L := (fderiv ℝ t y).toLinearMap
    let C := LinearMap.toMatrix b b L
    have hgram : H c y = C.transpose * H d (t y) * C := by
      have hb (i : Fin n) : b i = EuclideanSpace.single i 1 :=
        EuclideanSpace.basisFun_apply _ _ _
      have hleft : LinearMap.BilinForm.toMatrix b (B.comp L L) = H c y := by
        ext i j
        rw [LinearMap.BilinForm.toMatrix_apply]
        change g.inner (d.symm (t y))
          (mfderiv I I d.symm (t y) (fderiv ℝ t y (b i)))
          (mfderiv I I d.symm (t y) (fderiv ℝ t y (b j))) = _
        rw [hbase]
        change g.inner (c.symm y)
          ((mfderiv I I d.symm (t y)).comp (fderiv ℝ t y) (b i))
          ((mfderiv I I d.symm (t y)).comp (fderiv ℝ t y) (b j)) = _
        rw [← hder, hb, hb]
        rfl
      have hright : LinearMap.BilinForm.toMatrix b B = H d (t y) := by
        ext i j
        rw [LinearMap.BilinForm.toMatrix_apply]
        change g.inner (d.symm (t y)) (mfderiv I I d.symm (t y) (b i))
          (mfderiv I I d.symm (t y) (b j)) = _
        rw [hb, hb]
      rw [← hleft, ← hright]
      exact LinearMap.BilinForm.toMatrix_comp b b B L L
    have hdet : (H c y).det = (fderiv ℝ t y).det ^ 2 * (H d (t y)).det := by
      rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      have hC : C.det = (fderiv ℝ t y).det := LinearMap.det_toMatrix b L
      rw [hC]
      ring
    dsimp only [w]
    rw [hdet, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  -- Glue the prescribed chart measures using one countable smooth partition of unity.
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace V M
  obtain ⟨ι, φ, hφ⟩ := SmoothBumpCovering.exists_isSubordinate I isClosed_univ
    (U := fun x : M ↦ (chartAt V x).source)
    (fun x _ ↦ (chartAt V x).open_source.mem_nhds (mem_chart_source V x))
  let : Encodable ι := φ.locallyFinite.encodable
    (fun i ↦ ⟨φ.c i, (φ i).c_mem_support⟩)
  let ρ := φ.toSmoothPartitionOfUnity
  have hρ := hφ.toSmoothPartitionOfUnity
  let d (i : ι) := chartAt V (φ.c i)
  let a (i : ι) (z : V) := ENNReal.ofReal (ρ i ((d i).symm z) * w (d i) z)
  let ν (i : ι) : Measure V := (volume.restrict (d i).target).withDensity (a i)
  let μi (i : ι) : Measure M := Measure.map (d i).symm (ν i)
  have hvolume : g.IsRiemannianVolume (Measure.sum μi) := by
    intro c hc
    change Measure.map c ((Measure.sum μi).restrict c.source) =
      (volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (w c y))
    have hcM := contMDiffOn_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
    have hcS := contMDiffOn_symm_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
    let t (i : ι) : OpenPartialHomeomorph V V := c.symm.trans (d i)
    have ht (i : ι) : ContDiffOn ℝ ∞ (t i) (t i).source := by
      apply contMDiffOn_iff_contDiffOn.mp
      intro y hy
      have hcs := (hcS y hy.1).contMDiffAt (c.open_target.mem_nhds hy.1)
      have hd := (contMDiffOn_chart (I := I) (n := (∞ : ℕ∞ω)) (x := φ.c i)
        _ hy.2).contMDiffAt ((d i).open_source.mem_nhds hy.2)
      exact (hd.comp y hcs).contMDiffWithinAt
    let q (i : ι) (y : V) := w c y * ρ i (c.symm y)
    have hqnonneg (i : ι) (y : V) : 0 ≤ q i y :=
      mul_nonneg (Real.sqrt_nonneg _) (ρ.nonneg i _)
    have hqsmooth (i : ι) : ContDiffOn ℝ ∞ (q i) c.target := by
      apply (hw c hc).1.mul
      intro y hy
      apply ContDiffAt.contDiffWithinAt
      apply contMDiffAt_iff_contDiffAt.mp
      exact (ρ i).contMDiff.contMDiffAt.comp y
        ((hcS y hy).contMDiffAt (c.open_target.mem_nhds hy))
    -- A single supported coordinate measure has the expected Jacobian density in c.
    have hqmeasure (i : ι) : Measure.map c ((μi i).restrict c.source) =
        (volume.restrict c.target).withDensity (fun y ↦ ENNReal.ofReal (q i y)) := by
      ext A hA
      have hpre : MeasurableSet (c ⁻¹' A ∩ c.source) := by
        simpa only [Set.domRestrict_eq, Set.preimage_comp,
          Set.image_preimage_eq_inter_range, Subtype.range_coe] using
          c.open_source.measurableSet.subtype_image
            (hA.preimage c.continuousOn.domRestrict.measurable)
      let A₀ := A ∩ (t i).source
      have hA₀ : MeasurableSet A₀ := hA.inter (t i).open_source.measurableSet
      let B := t i '' A₀
      have hder (y : V) (hy : y ∈ A₀) :
          HasFDerivWithinAt (t i) (fderiv ℝ (t i) y) A₀ y :=
        (((ht i) y hy.2).contDiffAt ((t i).open_source.mem_nhds hy.2)
          |>.differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt
      have hB : MeasurableSet B := measurable_image_of_fderivWithin hA₀ hder
        ((t i).injOn.mono Set.inter_subset_right)
      have hset : (d i).symm ⁻¹' (c ⁻¹' A ∩ c.source) ∩ (d i).target = B := by
        ext z
        constructor
        · rintro ⟨⟨hzA, hzc⟩, hzd⟩
          refine ⟨c ((d i).symm z), ⟨hzA, ?_⟩, ?_⟩
          · refine ⟨c.map_source hzc, ?_⟩
            change c.symm (c ((d i).symm z)) ∈ (d i).source
            rw [c.left_inv hzc]
            exact (d i).map_target hzd
          · change d i (c.symm (c ((d i).symm z))) = z
            rw [c.left_inv hzc, (d i).right_inv hzd]
        · rintro ⟨y, hy, rfl⟩
          have hdy : (d i).symm (t i y) = c.symm y := (d i).left_inv hy.2.2
          refine ⟨⟨?_, ?_⟩, ((t i).map_source hy.2).1⟩
          · change c ((d i).symm (t i y)) ∈ A
            rw [hdy, c.right_inv hy.2.1]
            exact hy.1
          · rw [hdy]
            exact c.map_target hy.2.1
      have hdmeas : AEMeasurable (d i).symm (ν i) :=
        ((d i).continuousOn_symm.aemeasurable (d i).open_target.measurableSet).mono_ac
          (withDensity_absolutelyContinuous _ _)
      rw [Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hA,
        Measure.restrict_apply' c.open_source.measurableSet]
      change (Measure.map (d i).symm (ν i)) (c ⁻¹' A ∩ c.source) = _
      rw [Measure.map_apply_of_aemeasurable hdmeas hpre]
      have hleft : (ν i) ((d i).symm ⁻¹' (c ⁻¹' A ∩ c.source)) =
          ∫⁻ y in B, a i y ∂volume := by
        change ((volume.restrict (d i).target).withDensity (a i)) _ = _
        rw [withDensity_apply', Measure.restrict_restrict'
          (d i).open_target.measurableSet, hset]
      rw [hleft, withDensity_apply _ hA, Measure.restrict_restrict hA]
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA₀ hder
        ((t i).injOn.mono Set.inter_subset_right)]
      calc
        (∫⁻ y in A₀, ENNReal.ofReal |(fderiv ℝ (t i) y).det| * a i (t i y) ∂volume) =
            ∫⁻ y in A₀, ENNReal.ofReal (q i y) ∂volume := by
          apply setLIntegral_congr_fun hA₀
          intro y hy
          dsimp only [a, q]
          rw [show (d i).symm (t i y) = c.symm y from (d i).left_inv hy.2.2,
            ← ENNReal.ofReal_mul (abs_nonneg _),
            hchange c (d i) hc (chart_mem_atlas V (φ.c i)) y hy.2]
          congr 1
          ring
        _ = ∫⁻ y in A ∩ c.target, ENNReal.ofReal (q i y) ∂volume := by
          rw [← lintegral_indicator hA₀,
            ← lintegral_indicator (hA.inter c.open_target.measurableSet)]
          apply lintegral_congr
          intro y
          by_cases hy : y ∈ A₀
          · rw [Set.indicator_of_mem hy,
              Set.indicator_of_mem (show y ∈ A ∩ c.target from ⟨hy.1, hy.2.1⟩)]
          · rw [Set.indicator_of_notMem hy]
            by_cases hyc : y ∈ A ∩ c.target
            · rw [Set.indicator_of_mem hyc]
              have hz : ρ i (c.symm y) = 0 := by
                by_contra hn
                exact hy ⟨hyc.1, hyc.2, hρ i (subset_closure hn)⟩
              simp [q, hz]
            · rw [Set.indicator_of_notMem hyc]
    -- The same partition sums to one, so the resulting density is exactly sqrt(det g).
    have hsum (y : V) : ENNReal.ofReal (w c y) = ∑' i, ENNReal.ofReal (q i y) := by
      have hfin : (support (fun i ↦ q i y)).Finite :=
        (ρ.locallyFinite.point_finite (c.symm y)).subset
          (fun i hi ↦ right_ne_zero_of_mul hi)
      have hwq : w c y = ∑ᶠ i, q i y := by
        dsimp only [q]
        rw [← mul_finsum, ρ.sum_eq_one (mem_univ _), mul_one]
      rw [hwq, finsum_eq_sum_of_support_subset (fun i ↦ q i y)
        (s := hfin.toFinset) (fun i hi ↦ hfin.mem_toFinset.mpr hi),
        ENNReal.ofReal_sum_of_nonneg (fun i hi ↦ hqnonneg i y)]
      symm
      apply tsum_eq_sum
      intro i hi
      have hz : q i y = 0 := by
        by_contra hn
        exact hi (hfin.mem_toFinset.mpr hn)
      simp [hz]
    have hcm := c.continuousOn.aemeasurable (μ := Measure.sum μi)
      c.open_source.measurableSet
    rw [Measure.restrict_sum _ c.open_source.measurableSet] at hcm ⊢
    rw [Measure.map_sum hcm]
    simp_rw [hqmeasure]
    ext A hA
    rw [Measure.sum_apply _ hA, withDensity_apply _ hA]
    simp_rw [withDensity_apply _ hA]
    rw [show (fun y ↦ ENNReal.ofReal (w c y)) =
      (fun y ↦ ∑' i, ENNReal.ofReal (q i y)) from funext hsum]
    symm
    apply lintegral_tsum
    intro i
    exact ((hqsmooth i).continuousOn.aemeasurable
      c.open_target.measurableSet).ennreal_ofReal.restrict
  refine ⟨Measure.sum μi, hvolume, ?_⟩
  intro θ hθ
  -- A countable chart cover determines the original Borel measure uniquely.
  let U (x : M) := (chartAt V x).source
  obtain ⟨S, hS, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable U
    (fun x ↦ (chartAt V x).open_source)
  have hcover' : ⋃ x ∈ S, U x = Set.univ := by
    rw [hcover]
    exact Set.eq_univ_of_forall (fun x ↦ Set.mem_iUnion.mpr ⟨x, mem_chart_source V x⟩)
  apply Measure.ext_of_biUnion_eq_univ hS hcover'
  intro x hx
  let c := chartAt V x
  have hpull (η : Measure M) (hη : g.IsRiemannianVolume η) :
      Measure.map c.symm (Measure.map c (η.restrict c.source)) = η.restrict c.source := by
    have hsymm : AEMeasurable c.symm (Measure.map c (η.restrict c.source)) := by
      rw [hη c (chart_mem_atlas V x)]
      exact (c.symm.continuousOn.aemeasurable c.open_target.measurableSet).mono_ac
        (withDensity_absolutelyContinuous _ _)
    rw [hsymm.map_map_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet)]
    calc
      _ = Measure.map id (η.restrict c.source) := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem c.open_source.measurableSet] with y hy
        exact c.left_inv hy
      _ = _ := Measure.map_id
  change θ.restrict c.source = (Measure.sum μi).restrict c.source
  rw [← hpull θ hθ, ← hpull (Measure.sum μi) hvolume,
    hθ c (chart_mem_atlas V x), hvolume c (chart_mem_atlas V x)]

/-- The canonical Riemannian measure selected by the exact original chart-density formula. -/
def riemannianVolume : Measure M :=
  g.existsUnique_riemannianVolume.exists.choose

/-- The selected Riemannian measure has the specified metric density in every chart. -/
theorem isRiemannianVolume_riemannianVolume :
    g.IsRiemannianVolume g.riemannianVolume := by
  /- Recover the chartwise measure identity from the same existence witness
  used in riemannianVolume. No arbitrary positive density is substituted. -/
  exact g.existsUnique_riemannianVolume.exists.choose_spec

/-- The actual Riemannian volume is a smooth positive measure in the existing density API. -/
theorem isSmoothPositiveMeasure_riemannianVolume :
    IsSmoothPositiveMeasure (n := n) g.riemannianVolume := by
  /- Use the exact square-root Gram-determinant density in each chart.
  Smoothness of g and the inverse chart derivative gives smooth Gram entries.
  On the chart target positive definiteness makes the determinant positive,
  so its square root is smooth and positive. The preceding chart identity
  is exactly the measure equation required by IsSmoothPositiveMeasure. -/
  constructor
  intro c hc
  refine ⟨fun y ↦ Real.sqrt (Matrix.det (fun i j : Fin n ↦
    g.inner (c.symm y)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y (EuclideanSpace.single i 1))
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℝ (Fin n)) c.symm y (EuclideanSpace.single j 1)))),
    (smooth_positive_metric_chart_density g c hc).1,
    (smooth_positive_metric_chart_density g c hc).2,
    g.isRiemannianVolume_riemannianVolume c hc⟩

end SmoothTangentMetric

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M]
  (g : SmoothTangentMetric (n := n) (M := M))

/-- The integral Hermitian pairing of forms for the actual metric and its Riemannian measure.
It is conjugate-linear in the first variable whenever the integrands are integrable. -/
def smoothFormPairing (p : ℕ) (α β : SmoothDifferentialForm (n := n) M p) : ℂ :=
  ∫ x, differentialFormInner g p x (α.val x) (β.val x) ∂g.riemannianVolume

open Set Function in
open scoped Topology in
/-- A compactly supported smooth form pairs integrably with every smooth form. -/
theorem integrable_differentialFormInner (p : ℕ)
    (α β : SmoothDifferentialForm (n := n) M p)
    (hα : IsCompact (closure {x : M | α.val x ≠ 0})) :
    Integrable (fun x ↦ differentialFormInner g p x (α.val x) (β.val x))
      g.riemannianVolume := by
  /- Positive smooth chart densities are locally bounded. On a sufficiently
  small coordinate ball this gives finite measure and hence a locally
  finite measure on M. The smooth pairing vanishes wherever α vanishes,
  so its closed support lies in the given compact closed support of α.
  Apply integrability of a continuous compactly supported function for
  this same locally finite Riemannian measure. Compactness of M is unnecessary. -/
  classical
  let μ := g.riemannianVolume
  let hμ : IsSmoothPositiveMeasure (n := n) μ :=
    g.isSmoothPositiveMeasure_riemannianVolume
  -- Positive smooth chart densities are locally bounded and therefore give local finiteness.
  let : IsLocallyFiniteMeasure μ := by
    constructor
    intro x
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    have hcx : c x ∈ c.target := c.map_source hx
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    have hwcont : ContinuousAt w (c x) :=
      hw.continuousOn.continuousAt (c.open_target.mem_nhds hcx)
    have hneigh : c.target ∩ {z | w z < w (c x) + 1} ∈ nhds (c x) :=
      Filter.inter_mem (c.open_target.mem_nhds hcx)
        (hwcont.eventually (gt_mem_nhds (lt_add_one _)))
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hneigh
    let U := c ⁻¹' Metric.ball (c x) ε ∩ c.source
    have hUnhds : U ∈ nhds x :=
      Filter.inter_mem ((c.continuousAt hx).preimage_mem_nhds (Metric.ball_mem_nhds _ hε))
        (c.open_source.mem_nhds hx)
    refine ⟨U, hUnhds, ?_⟩
    -- The chart pushforward measures the same restricted neighborhood.
    have heq : μ U = ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) (Metric.ball (c x) ε) := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) measurableSet_ball,
        Measure.restrict_apply' c.open_source.measurableSet]
    rw [heq, withDensity_apply _ measurableSet_ball]
    have hbound : (∫⁻ z in Metric.ball (c x) ε, ENNReal.ofReal (w z)
        ∂(volume.restrict c.target)) ≤ ENNReal.ofReal (w (c x) + 1) *
          volume (Metric.ball (c x) ε) := by
      calc
        _ ≤ ∫⁻ _z in Metric.ball (c x) ε, ENNReal.ofReal (w (c x) + 1)
            ∂(volume.restrict c.target) := by
          apply lintegral_mono_ae
          filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
          exact ENNReal.ofReal_le_ofReal (hball hz).2.le
        _ ≤ _ := by
          rw [lintegral_const, Measure.restrict_apply_univ]
          exact mul_le_mul_right (Measure.restrict_apply_le _ _) _
    exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top)
  -- The smooth integrand vanishes off the original compact support of its first factor.
  have hsupp : HasCompactSupport
      (fun x ↦ differentialFormInner g p x (α.val x) (β.val x)) := by
    apply hα.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change differentialFormInner g p x (α.val x) (β.val x) ≠ 0 at hx
    by_contra hzero
    apply hx
    have hz : α.val x = 0 := not_ne_iff.mp hzero
    rw [hz]
    unfold differentialFormInner
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro I _
    apply Finset.sum_eq_zero
    intro J _
    change (conj (0 : ℂ) * _) * _ = 0
    simp
  exact (contMDiff_differentialFormInner g p α β).continuous.integrable_of_hasCompactSupport hsupp

open Set Function in
open scoped Topology in
/-- The integral pairing is positive definite on compactly supported smooth forms. -/
theorem smoothFormPairing_self_eq_zero_iff (p : ℕ)
    (α : SmoothDifferentialForm (n := n) M p)
    (hα : IsCompact (closure {x : M | α.val x ≠ 0})) :
    smoothFormPairing g p α α = 0 ↔ α = 0 := by
  /- Stage 1: compute the self-pairing in a metric-orthonormal frame. It is
  a sum of squared absolute values with positive normalization, vanishing
  exactly for the zero alternating tensor. Thus its imaginary part is zero
  and its real part is nonnegative. Compact support gives integrability.
  Stage 2: a zero integral of this nonnegative real part makes it vanish
  almost everywhere. Strictly positive chart densities give full support;
  continuity then gives pointwise vanishing and hence the zero form.
  Conversely the zero form has zero integrand.
  Empty bases, degree zero and degrees above the dimension are included. -/
  classical
  have hpoint (x : M) (η : DifferentialFormFiber (n := n) p x) :
      0 ≤ (differentialFormInner g p x η η).re ∧
        ((differentialFormInner g p x η η).re = 0 ↔ η = 0) := by
    classical
    -- Install the metric on a temporary copy only, to choose an orthonormal basis.
    let V := TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x
    let a : Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let : FiniteDimensional ℝ V := Module.Finite.of_basis a
    let W := ULift.{0} V
    let core : InnerProductSpace.Core ℝ W :=
      { inner u v := g.inner x u.down v.down
        conj_inner_symm u v := g.symm x v.down u.down
        re_inner_nonneg v := by
          by_cases hv : v.down = 0
          · simp [hv]
          · exact (g.pos x v.down hv).le
        add_left u v w := by
          change g.inner x (u.down + v.down) w.down = _
          simp
        smul_left u v c := by
          change g.inner x (c • u.down) v.down = c * g.inner x u.down v.down
          simp
        definite v h := by
          have hv : v.down = 0 := by
            by_contra hv
            exact (ne_of_gt (g.pos x v.down hv)) h
          exact ULift.ext hv }
    let : InnerProductSpace.Core ℝ W := core
    let : NormedAddCommGroup W := core.toNormedAddCommGroup
    let : NormedSpace ℝ W := InnerProductSpace.Core.toNormedSpace
    let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
    let : FiniteDimensional ℝ W :=
      (ULift.moduleEquiv (R := ℝ) (M := V)).symm.finiteDimensional
    have hdim : Module.finrank ℝ W = n := by
      rw [(ULift.moduleEquiv (R := ℝ) (M := V)).finrank_eq]
      simpa using Module.finrank_eq_card_basis a
    let b : OrthonormalBasis (Fin n) ℝ W :=
      (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
    let e : Fin n → V := fun i ↦ (b i).down
    have he (i j : Fin n) : g.inner x (e i) (e j) = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    let d : Basis (Fin n) ℝ V := b.toBasis.map (ULift.moduleEquiv (R := ℝ) (M := V))
    -- The original normalization becomes a positive multiple of squared coefficients.
    have hformula : (differentialFormInner g p x η η).re =
        (p.factorial : ℝ)⁻¹ * ∑ I : Fin p → Fin n, Complex.normSq (η (fun k ↦ e (I k))) := by
      rw [differentialFormInner_eq_sum_orthonormal g p x e he]
      simp only [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_sum,
        ← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        Complex.ofReal_re]
    have hfactor : 0 < (p.factorial : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast p.factorial_pos)
    rw [hformula]
    constructor
    · exact mul_nonneg hfactor.le (Finset.sum_nonneg (fun I _ ↦ Complex.normSq_nonneg _))
    · constructor
      · intro hz
        have hsum : (∑ I : Fin p → Fin n, Complex.normSq (η (fun k ↦ e (I k)))) = 0 :=
          (mul_eq_zero.mp hz).resolve_left hfactor.ne'
        have hcoeff (I : Fin p → Fin n) : η (fun k ↦ e (I k)) = 0 := by
          apply Complex.normSq_eq_zero.mp
          exact (Finset.sum_eq_zero_iff_of_nonneg
            (fun J _ ↦ Complex.normSq_nonneg (η (fun k ↦ e (J k))))).mp hsum I (Finset.mem_univ _)
        have hη : η.toAlternatingMap = 0 := by
          apply d.ext_alternating
          intro I hI
          exact hcoeff I
        ext v
        exact congrArg (fun f : V [⋀^Fin p]→ₗ[ℝ] ℂ ↦ f v) hη
      · rintro rfl
        simp
  -- Positive coordinate densities give full support to the same canonical measure.
  let μ := g.riemannianVolume
  let hμ : IsSmoothPositiveMeasure (n := n) μ :=
    g.isSmoothPositiveMeasure_riemannianVolume
  let : μ.IsOpenPosMeasure := by
    constructor
    intro U hU hUne hzero
    obtain ⟨x, hxU⟩ := hUne
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    have hx : x ∈ c.source := mem_chart_source _ x
    obtain ⟨w, hw, hwpos, hmap⟩ := hμ.exists_smooth_density c (chart_mem_atlas _ x)
    let A := c '' (c.source ∩ U)
    have hAopen : IsOpen A := c.isOpen_image_source_inter hU
    have hAnon : A.Nonempty := ⟨c x, ⟨x, ⟨hx, hxU⟩, rfl⟩⟩
    have hAsub : A ⊆ c.target := by
      rintro _ ⟨y, hy, rfl⟩
      exact c.map_source hy.1
    have hpre : c ⁻¹' A ∩ c.source ⊆ U := by
      rintro y ⟨⟨z, hz, hzy⟩, hy⟩
      have heq : z = y := c.injOn hz.1 hy hzy
      simpa only [← heq] using hz.2
    have hAnull : ((volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z))) A = 0 := by
      rw [← hmap, Measure.map_apply_of_aemeasurable
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hAopen.measurableSet,
        Measure.restrict_apply' c.open_source.measurableSet]
      exact measure_mono_null hpre hzero
    -- Positivity makes coordinate Lebesgue measure absolutely continuous in the density.
    have hac : volume.restrict c.target ≪ (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w z)) := by
      apply withDensity_absolutelyContinuous'
        (hw.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_pos.mpr (hwpos z hz)).ne'
    have hvol := hac hAnull
    rw [Measure.restrict_apply hAopen.measurableSet,
      Set.inter_eq_left.mpr hAsub] at hvol
    exact hAopen.measure_ne_zero volume hAnon hvol
  constructor
  · intro hzero
    -- Pass through the real part, whose integrand is nonnegative and integrable.
    have hint := integrable_differentialFormInner g p α α hα
    have hrealint : Integrable
        (fun x ↦ (differentialFormInner g p x (α.val x) (α.val x)).re) μ :=
      Complex.reCLM.integrable_comp hint
    have hrealzero :
        (∫ x, (differentialFormInner g p x (α.val x) (α.val x)).re ∂μ) = 0 := by
      calc
        _ = (∫ x, differentialFormInner g p x (α.val x) (α.val x) ∂μ).re := by
          simpa only [RCLike.re_eq_complex_re] using integral_re hint
        _ = 0 := congrArg Complex.re hzero
    have hae : (fun x ↦ (differentialFormInner g p x (α.val x) (α.val x)).re) =ᵐ[μ]
        (fun _ ↦ (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg (fun x ↦ (hpoint x (α.val x)).1) hrealint).mp hrealzero
    -- Continuity and full support upgrade almost-everywhere vanishing to pointwise vanishing.
    have hcont := Complex.continuous_re.comp (contMDiff_differentialFormInner g p α α).continuous
    have hfun := Measure.eq_of_ae_eq hae hcont continuous_const
    apply Subtype.ext
    funext x
    exact (hpoint x (α.val x)).2.mp (congrFun hfun x)
  · rintro rfl
    change (∫ x, differentialFormInner g p x 0 0 ∂g.riemannianVolume) = 0
    have hz (x : M) : differentialFormInner g p x 0 0 = 0 := by
      unfold differentialFormInner
      apply mul_eq_zero_of_right
      apply Finset.sum_eq_zero
      intro I _
      apply Finset.sum_eq_zero
      intro J _
      change (conj (0 : ℂ) * 0) * _ = 0
      simp
    simp only [hz, integral_zero]

end AtiyahSinger
