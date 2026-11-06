/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetric
public import Mathlib.Analysis.Matrix.Normed

/-!
# Comparing two smooth Hermitian metrics

Public module ID: M1272.

D02/A07: the unique positive change operator B is specified by k(u,v)=h(u,Bv).
Its local expression is H⁻¹K, not K⁻¹H. We retain the original fiber topology,
specify the induced map on actual smooth sections, and state uniform comparison
only on compact sets. These are project deductions from the standard metric
definition in Husemoller III.9 and the metric pairing used in Spin Geometry III.5.
The data do not include any Fredholm or index conclusion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle
open scoped Manifold ContDiff ComplexConjugate Matrix.Norms.Elementwise

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h k : SmoothHermitianMetric (n := n) (r := r) E)

/-- The change operator is uniquely determined by the two actual fiber forms. -/
theorem existsUnique_change (x : M) :
    ∃! B : E x ≃L[ℂ] E x, ∀ u v : E x,
      h.pairing x u (B v) = k.pairing x u v := by
  /- Choose a frame at x and form H⁻¹K from the two positive definite Gram
  matrices. Transport this invertible linear map to the fiber. Finite dimension
  makes it and its inverse continuous for the original topology. The displayed
  identity determines B by nondegeneracy of h, independently of the chosen frame. -/
  classical
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  let frame : E x ≃L[ℂ] (Fin r → ℂ) := (e.continuousLinearEquivAt ℂ x hx).trans
    (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ))
  -- Each positive Gram matrix acts invertibly in the same original frame.
  have hunit : IsUnit (h.gramMatrix e x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (h.isUnit_det_gramMatrix e x hx)
  have kunit : IsUnit (k.gramMatrix e x) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (k.isUnit_det_gramMatrix e x hx)
  let H : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) :=
    (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
  let K : (Fin r → ℂ) ≃L[ℂ] (Fin r → ℂ) :=
    (LinearEquiv.ofBijective (k.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr kunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr kunit⟩).toContinuousLinearEquiv
  let B : E x ≃L[ℂ] E x := frame.trans (K.trans (H.symm.trans frame.symm))
  have hmatrix (v : E x) :
      Matrix.mulVec (h.gramMatrix e x) ((e ⟨x, B v⟩).2) =
        Matrix.mulVec (k.gramMatrix e x) ((e ⟨x, v⟩).2) := by
    change H (frame (B v)) = K (frame v)
    simp [B]
  have hB (u v : E x) : h.pairing x u (B v) = k.pairing x u v := by
    rw [h.pairing_eq_gramMatrix e x hx, k.pairing_eq_gramMatrix e x hx]
    simp only [mul_assoc, ← Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z ↦ conj ((e ⟨x, u⟩).2 i) * z) (congrFun (hmatrix v) i)
  refine ⟨B, hB, ?_⟩
  intro C hC
  apply ContinuousLinearEquiv.ext
  funext v
  -- The form separates its second slot by positive definiteness.
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  have hz : h.pairing x (C v - B v) (C v - B v) = 0 := by
    change (h.toCore x).inner (C v - B v) (C v - B v) = 0
    rw [InnerProductSpace.Core.inner_sub_right]
    change h.pairing x (C v - B v) (C v) - h.pairing x (C v - B v) (B v) = 0
    rw [hC, hB, sub_self]
  exact sub_eq_zero.mp ((h.toCore x).definite _ hz)

/-- The canonical change operator, specified pointwise by h(u,Bv)=k(u,v). -/
def change (x : M) : E x ≃L[ℂ] E x :=
  Classical.choose (h.existsUnique_change k x).exists

/-- The chosen operator satisfies its defining metric identity. -/
theorem pairing_change (x : M) (u v : E x) :
    h.pairing x u (h.change k x v) = k.pairing x u v := by
  /- Use the defining property of the chosen unique equivalence. -/
  exact (Classical.choose_spec (h.existsUnique_change k x).exists) u v

/-- Nondegeneracy identifies any candidate change map by its pairing identity. -/
theorem change_eq (x : M) (B : E x ≃L[ℂ] E x)
    (hB : ∀ u v : E x, h.pairing x u (B v) = k.pairing x u v) :
    h.change k x = B := by
  /- Apply uniqueness to B and the chosen equivalence. -/
  exact (h.existsUnique_change k x).unique
    (fun u v ↦ h.pairing_change k x u v) hB

/-- Equal metrics give the identity equivalence, including on zero-dimensional fibers. -/
theorem change_self (x : M) : h.change h x = ContinuousLinearEquiv.refl ℂ (E x) := by
  /- The identity map satisfies the defining pairing equation, hence is unique. -/
  apply h.change_eq h x
  intro u v
  rfl

/-- Reversing the metric comparison gives its genuine inverse. -/
theorem change_symm (x : M) : (h.change k x).symm = k.change h x := by
  /- Substitute B⁻¹v into h(u,Bv)=k(u,v). The resulting equation characterizes
  the comparison in the reverse direction. -/
  symm
  apply k.change_eq h x
  intro u v
  simpa using (h.pairing_change k x u ((h.change k x).symm v)).symm

/-- The reverse change cancels the forward change on the actual fiber. -/
theorem change_swap_apply (x : M) (u : E x) :
    k.change h x (h.change k x u) = u := by
  /- Identify the reverse change with the inverse and apply its left inverse law. -/
  rw [← h.change_symm k x]
  exact (h.change k x).symm_apply_apply u

/-- Metric changes compose in the order forced by their pairing convention. -/
theorem change_trans (l : SmoothHermitianMetric (n := n) (r := r) E) (x : M) :
    h.change l x = (k.change l x).trans (h.change k x) := by
  /- Pair the composite with u using h. The first metric identity turns it into
  k(u,B_kl v), and the second into l(u,v). Uniqueness identifies B_hl. No
  commutativity of the two change operators is asserted. -/
  apply h.change_eq l x
  intro u v
  change h.pairing x u (h.change k x (k.change l x v)) = l.pairing x u v
  rw [h.pairing_change k, k.pairing_change l]

/-- The change operator is self-adjoint for the starting metric. -/
theorem pairing_change_left (x : M) (u v : E x) :
    h.pairing x (h.change k x u) v = k.pairing x u v := by
  /- Conjugate the defining equation with u and v interchanged, using Hermitian
  symmetry for both metrics. -/
  have heq := congrArg (starRingEnd ℂ) (h.pairing_change k x v u)
  simpa only [pairing, (h.toCore x).conj_inner_symm,
    (k.toCore x).conj_inner_symm] using heq

/-- The change operator is strictly positive for its starting metric. -/
theorem re_pairing_change_pos (x : M) (u : E x) (hu : u ≠ 0) :
    0 < (h.pairing x u (h.change k x u)).re := by
  /- The defining equation identifies this real number with k(u,u), which is
  strictly positive. Positivity is relative to h, not to an unrelated fiber norm. -/
  rw [h.pairing_change k]
  exact k.pairing_self_pos x u hu

/-- In a valid frame the change matrix solves H B = K. -/
theorem gramMatrix_mul_change
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) (v : E x) (i : Fin r) :
    ∑ j, h.gramMatrix e x i j * (e ⟨x, h.change k x v⟩).2 j =
      ∑ j, k.gramMatrix e x i j * (e ⟨x, v⟩).2 j := by
  /- Test the pairing equation against the inverse frame of the ith basis vector.
  Expand only the second argument. This specifies H B=K without assuming that
  the frame is orthonormal for either metric. -/
  classical
  have htest := h.pairing_change k x (e.symmL ℂ x (EuclideanSpace.single i 1)) v
  rw [h.pairing_eq_gramMatrix e x hx, k.pairing_eq_gramMatrix e x hx] at htest
  have hcoord : (e ⟨x, e.symmL ℂ x (EuclideanSpace.single i 1)⟩).2 =
      EuclideanSpace.single i 1 := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
    exact e.continuousLinearMapAt_symmL hx _
  simpa [hcoord] using htest

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

set_option linter.unusedSectionVars false in
-- Retain the original manifold parameter in the public change-operator interface.
/-- The change operator has smooth coordinate matrices on every frame domain. -/
theorem contMDiffOn_change
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      (fun x ↦ (e.continuousLinearMapAt ℂ x).comp
        ((h.change k x).toContinuousLinearMap.comp (e.symmL ℂ x))) e.baseSet := by
  /- The coordinate matrix is H⁻¹K on e.baseSet. Both Gram matrices are smooth
  there and H is invertible. Smooth matrix inversion on GL and multiplication
  prove the assertion; behavior of totalized frame maps outside the domain is irrelevant. -/
  classical
  let toOp : Matrix (Fin r) (Fin r) ℂ →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp Matrix.toEuclideanLin.toLinearMap
  let toOpC : Matrix (Fin r) (Fin r) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
    LinearMap.toContinuousLinearMap (toOp.restrictScalars ℝ)
  let A (g : SmoothHermitianMetric (n := n) (r := r) E) (x : M) :=
    toOpC (g.gramMatrix e x)
  have hA (g : SmoothHermitianMetric (n := n) (r := r) E) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
        (A g) e.baseSet := by
    apply toOpC.contDiff.contMDiff.comp_contMDiffOn
    apply contMDiffOn_pi_space.mpr
    intro i
    apply contMDiffOn_pi_space.mpr
    intro j
    exact g.contMDiffOn_gram e i j
  -- Realize each invertible Gram operator as an equivalence in the fixed coordinate space.
  have hequiv (x : M) (hx : x ∈ e.baseSet) :
      ∃ H : EuclideanSpace ℂ (Fin r) ≃L[ℂ] EuclideanSpace ℂ (Fin r),
        H.toContinuousLinearMap = A h x := by
    have hunit := (Matrix.isUnit_iff_isUnit_det _).mpr (h.isUnit_det_gramMatrix e x hx)
    let L := (LinearEquiv.ofBijective (h.gramMatrix e x).mulVecLin
      ⟨Matrix.mulVec_injective_iff_isUnit.mpr hunit,
        Matrix.mulVec_surjective_iff_isUnit.mpr hunit⟩).toContinuousLinearEquiv
    let P := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin r ↦ ℂ)
    refine ⟨P.trans (L.trans P.symm), ?_⟩
    ext v i
    rfl
  have hinverse : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
      (fun x ↦ (A h x).inverse) e.baseSet := by
    intro x hx
    obtain ⟨H, hH⟩ := hequiv x hx
    have hinv : ContDiffAt ℝ ∞ ContinuousLinearMap.inverse (A h x) := by
      rw [← hH]
      exact (contDiffAt_map_inverse H).restrict_scalars ℝ
    exact hinv.contMDiffAt.comp_contMDiffWithinAt x (hA h x hx)
  have hcomp : ContDiff ℝ ∞
      (fun p : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ↦ p.1.comp p.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
  have hsmooth := hcomp.contMDiff.comp_contMDiffOn (hinverse.prodMk_space (hA k))
  -- The defining pairing identity gives exactly H⁻¹K in this same frame.
  apply hsmooth.congr
  intro x hx
  obtain ⟨H, hH⟩ := hequiv x hx
  apply ContinuousLinearMap.ext
  intro v
  apply H.injective
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  rw [← hH, ContinuousLinearMap.inverse_equiv]
  simp only [ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]
  change H.toContinuousLinearMap
    (e.continuousLinearMapAt ℂ x (h.change k x (e.symmL ℂ x v))) = (A k x) v
  rw [hH]
  apply PiLp.ext
  intro i
  have hv : (e ⟨x, e.symmL ℂ x v⟩).2 = v := by
    rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
    exact e.continuousLinearMapAt_symmL hx v
  have hid := h.gramMatrix_mul_change k e x hx (e.symmL ℂ x v) i
  rw [hv] at hid
  change ∑ j, h.gramMatrix e x i j *
      (e.continuousLinearMapAt ℂ x (h.change k x (e.symmL ℂ x v))) j =
    ∑ j, k.gramMatrix e x i j * v j
  simpa only [e.continuousLinearMapAt_apply_of_mem ℂ hx] using hid

/-- Applying the metric change to a smooth section preserves smoothness. -/
theorem isSmoothSection_change (u : smoothSections (n := n) (r := r) E) :
    IsSmoothSection (n := n) (r := r) E (fun x ↦ h.change k x (u.val x)) := by
  /- In any frame multiply the smooth coordinate matrix of the change by the
  smooth coordinate vector of u. This checks exactly the existing section predicate. -/
  intro e he
  let := he
  have heval : ContDiff ℝ ∞
      (fun p : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ×
        EuclideanSpace ℂ (Fin r) ↦ p.1 p.2) :=
    (show ContDiff ℂ ∞ _ from contDiff_fst.clm_apply contDiff_snd).restrict_scalars ℝ
  have hsmooth := heval.contMDiff.comp_contMDiffOn
    ((h.contMDiffOn_change k e).prodMk_space (u.property e he))
  apply hsmooth.congr
  intro x hx
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx (u.val x),
    e.symmL_continuousLinearMapAt hx, e.continuousLinearMapAt_apply_of_mem ℂ hx]

/-- The induced equivalence sends a section u to the section x ↦ B(x)u(x). -/
def changeSections :
    smoothSections (n := n) (r := r) E ≃ₗ[ℂ] smoothSections (n := n) (r := r) E where
  toFun := fun u ↦ ⟨fun x ↦ h.change k x (u.val x), h.isSmoothSection_change k u⟩
  invFun := fun u ↦ ⟨fun x ↦ k.change h x (u.val x), k.isSmoothSection_change h u⟩
  left_inv := fun u ↦ Subtype.ext (funext (fun x ↦ h.change_swap_apply k x (u.val x)))
  right_inv := fun u ↦ Subtype.ext (funext (fun x ↦ k.change_swap_apply h x (u.val x)))
  map_add' := fun u v ↦
    Subtype.ext (funext (fun x ↦ (h.change k x).map_add (u.val x) (v.val x)))
  map_smul' := fun c u ↦
    Subtype.ext (funext (fun x ↦ (h.change k x).map_smul c (u.val x)))

/-- The section equivalence uses the specified pointwise change map. -/
theorem changeSections_apply (u : smoothSections (n := n) (r := r) E) (x : M) :
    (h.changeSections k u).val x = h.change k x (u.val x) := by
  /- Unfold the explicit section equivalence and its subtype value. -/
  rfl

/-- Swapping the metrics inverts the entire section equivalence. -/
theorem changeSections_symm : (h.changeSections k).symm = k.changeSections h := by
  /- Both equivalences apply the reverse fiber change at each point. -/
  apply LinearEquiv.ext
  intro u
  rfl

set_option linter.unusedSectionVars false in
-- Retain the original manifold parameter in the public compact comparison interface.
/-- Metric comparison is uniform on a compact subset of the base. -/
theorem exists_bounds_on_compact (K : Set M) (hK : IsCompact K) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ K, ∀ u : E x,
      c * (h.pairing x u u).re ≤ (k.pairing x u u).re ∧
        (k.pairing x u u).re ≤ C * (h.pairing x u u).re := by
  /- In a frame at each point, positive definite Gram matrices and continuity
  give upper and positive lower comparison constants on a neighborhood. Extract
  a finite cover of K and take the maximum and minimum constants. Treat the
  empty compact set with c=C=1; the empty coordinate sphere covers rank zero
  vacuously. No global compactness is assumed. -/
  classical
  -- First obtain comparison constants on an actual neighborhood of each base point.
  have hlocal (x : M) : ∃ c C : ℝ, ∃ U : Set M,
      0 < c ∧ 0 < C ∧ U ∈ nhds x ∧ ∀ y ∈ U, ∀ u : E y,
        c * (h.pairing y u u).re ≤ (k.pairing y u u).re ∧
          (k.pairing y u u).re ≤ C * (h.pairing y u u).re := by
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    let Q (g : SmoothHermitianMetric (n := n) (r := r) E) (y : M)
        (z : EuclideanSpace ℂ (Fin r)) : ℝ :=
      (∑ i, ∑ j, conj (z i) * g.gramMatrix e y i j * z j).re
    have hQeq (g : SmoothHermitianMetric (n := n) (r := r) E) (y : M)
        (hy : y ∈ e.baseSet) (z : EuclideanSpace ℂ (Fin r)) :
        Q g y z = (g.pairing y (e.symmL ℂ y z) (e.symmL ℂ y z)).re := by
      have hz : (e ⟨y, e.symmL ℂ y z⟩).2 = z := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hy]
        exact e.continuousLinearMapAt_symmL hy z
      rw [g.pairing_eq_gramMatrix e y hy, hz]
    have hQpos (g : SmoothHermitianMetric (n := n) (r := r) E) (y : M)
        (hy : y ∈ e.baseSet) (z : EuclideanSpace ℂ (Fin r)) (hz : z ≠ 0) :
        0 < Q g y z := by
      rw [hQeq g y hy z]
      apply g.pairing_self_pos
      intro hzero
      apply hz
      have hinv := e.continuousLinearMapAt_symmL (R := ℂ) hy z
      simpa [hzero] using hinv.symm
    have hQcont (g : SmoothHermitianMetric (n := n) (r := r) E) :
        ContinuousOn (fun p : M × EuclideanSpace ℂ (Fin r) ↦ Q g p.1 p.2)
          (e.baseSet ×ˢ Set.univ) := by
      apply Complex.continuous_re.comp_continuousOn
      apply continuousOn_finsetSum
      intro i _
      apply continuousOn_finsetSum
      intro j _
      have hcoeff : ContinuousOn
          (fun p : M × EuclideanSpace ℂ (Fin r) ↦ g.gramMatrix e p.1 i j)
          (e.baseSet ×ˢ Set.univ) :=
        (g.contMDiffOn_gram e i j).continuousOn.comp
          continuous_fst.continuousOn (fun p hp ↦ hp.1)
      have hi : Continuous (fun p : M × EuclideanSpace ℂ (Fin r) ↦ p.2 i) :=
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) i).comp continuous_snd
      have hj : Continuous (fun p : M × EuclideanSpace ℂ (Fin r) ↦ p.2 j) :=
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℂ) j).comp continuous_snd
      exact (((Complex.continuous_conj.comp hi).continuousOn).mul hcoeff).mul hj.continuousOn
    let R (y : M) (z : EuclideanSpace ℂ (Fin r)) : ℝ := Q k y z / Q h y z
    have hRcont (z : EuclideanSpace ℂ (Fin r)) (hz : z ≠ 0) :
        ContinuousAt (fun p : M × EuclideanSpace ℂ (Fin r) ↦ R p.1 p.2) (x, z) :=
      ((hQcont k).continuousAt
        ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ z⟩)).div
        ((hQcont h).continuousAt
          ((e.open_baseSet.prod isOpen_univ).mem_nhds ⟨hx, Set.mem_univ z⟩))
        (ne_of_gt (hQpos h x hx z hz))
    let S := Metric.sphere (0 : EuclideanSpace ℂ (Fin r)) 1
    have hS : IsCompact S := isCompact_sphere _ _
    have hSne (z : EuclideanSpace ℂ (Fin r)) (hz : z ∈ S) : z ≠ 0 := by
      intro hz0
      simp [S, hz0] at hz
    have hRcontinuous : ContinuousOn (R x) S := by
      intro z hz
      exact ((hRcont z (hSne z hz)).comp
        (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
    obtain ⟨a, ha, halower⟩ := hS.exists_forall_le' hRcontinuous (a := 0) (by
      intro z hz
      exact div_pos (hQpos k x hx z (hSne z hz)) (hQpos h x hx z (hSne z hz)))
    obtain ⟨b, hb⟩ := (hS.image_of_continuousOn hRcontinuous).bddAbove
    -- Compactness of the coordinate sphere makes both strict bounds uniform nearby.
    have hnear : ∀ᶠ y in nhds x, ∀ z ∈ S,
        a / 2 < R y z ∧ R y z < max b 1 + 1 := by
      apply hS.eventually_forall_of_forall_eventually
      intro z hz
      have hlow : a / 2 < R x z := lt_of_lt_of_le (by linarith) (halower z hz)
      have hupp : R x z < max b 1 + 1 :=
        lt_of_le_of_lt ((hb ⟨z, hz, rfl⟩).trans (le_max_left _ _)) (by linarith)
      exact ((hRcont z (hSne z hz)).eventually_const_lt hlow).and
        ((hRcont z (hSne z hz)).eventually_lt_const hupp)
    let U := e.baseSet ∩ {y | ∀ z ∈ S, a / 2 < R y z ∧ R y z < max b 1 + 1}
    refine ⟨a / 2, max b 1 + 1, U, by positivity, by positivity,
      Filter.inter_mem (e.open_baseSet.mem_nhds hx) hnear, ?_⟩
    intro y hy u
    by_cases hu : u = 0
    · subst u
      have hh0 : h.pairing y 0 0 = 0 := by
        let : InnerProductSpace.Core ℂ (E y) := h.toCore y
        exact InnerProductSpace.Core.inner_zero_left _
      have hk0 : k.pairing y 0 0 = 0 := by
        let : InnerProductSpace.Core ℂ (E y) := k.toCore y
        exact InnerProductSpace.Core.inner_zero_left _
      simp [hh0, hk0]
    let z : EuclideanSpace ℂ (Fin r) := (e ⟨y, u⟩).2
    have hz : z ≠ 0 := by
      intro hz0
      apply hu
      apply (e.continuousLinearEquivAt ℂ y hy.1).injective
      rw [map_zero]
      rw [e.coe_continuousLinearEquivAt_eq hy.1,
        e.continuousLinearMapAt_apply_of_mem ℂ hy.1]
      exact hz0
    let w : EuclideanSpace ℂ (Fin r) := (‖z‖⁻¹ : ℂ) • z
    have hw : w ∈ S := by
      simpa [S, w, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℂ) hz
    have hscale : (‖z‖ : ℂ) • e.symmL ℂ y w = u := by
      rw [← map_smul]
      have hz0 : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      simp only [w, smul_smul]
      rw [mul_inv_cancel₀ (by exact_mod_cast hz0), one_smul]
      rw [show z = e.continuousLinearMapAt ℂ y u from
        (e.continuousLinearMapAt_apply_of_mem ℂ hy.1 u).symm]
      exact e.symmL_continuousLinearMapAt hy.1 u
    have hquadratic (g : SmoothHermitianMetric (n := n) (r := r) E) :
        (g.pairing y u u).re = Q g y w * ‖z‖ ^ 2 := by
      let : InnerProductSpace.Core ℂ (E y) := g.toCore y
      rw [hQeq g y hy.1 w]
      conv_lhs => rw [← hscale]
      change ((g.toCore y).inner ((‖z‖ : ℂ) • e.symmL ℂ y w)
        ((‖z‖ : ℂ) • e.symmL ℂ y w)).re =
          ((g.toCore y).inner (e.symmL ℂ y w) (e.symmL ℂ y w)).re * ‖z‖ ^ 2
      rw [(g.toCore y).smul_left, InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
      simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      ring
    obtain ⟨hlow, hupp⟩ := hy.2 w hw
    have hden : 0 < Q h y w := hQpos h y hy.1 w (hSne w hw)
    have hlo : a / 2 * Q h y w ≤ Q k y w := (le_div_iff₀ hden).mp hlow.le
    have hup : Q k y w ≤ (max b 1 + 1) * Q h y w := (div_le_iff₀ hden).mp hupp.le
    rw [hquadratic h, hquadratic k]
    constructor
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hlo (sq_nonneg ‖z‖)
    · simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hup (sq_nonneg ‖z‖)
  -- A finite neighborhood cover of K gives one positive minimum and finite maximum.
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · subst K
    exact ⟨1, 1, zero_lt_one, zero_lt_one, by simp⟩
  choose c C U hc hC hU hbounds using hlocal
  obtain ⟨t, _, htcover⟩ := hK.elim_nhds_subcover U (fun x _ ↦ hU x)
  have ht : t.Nonempty := by
    obtain ⟨x, hx⟩ := hNonempty
    obtain ⟨y, hy, _⟩ := Set.mem_iUnion₂.mp (htcover hx)
    exact ⟨y, hy⟩
  refine ⟨t.inf' ht c, t.sup' ht C, ?_, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff ht).mpr (fun x _ ↦ hc x)
  · obtain ⟨x, hx⟩ := ht
    exact (hC x).trans_le (Finset.le_sup' C hx)
  · intro x hx u
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (htcover hx)
    have hpos : 0 ≤ (h.pairing x u u).re := (h.toCore x).re_inner_nonneg u
    obtain ⟨hlow, hupp⟩ := hbounds y x hxy u
    constructor
    · exact (mul_le_mul_of_nonneg_right (Finset.inf'_le c hy) hpos).trans hlow
    · exact hupp.trans (mul_le_mul_of_nonneg_right (Finset.le_sup' C hy) hpos)

/-- On a compact base the two metric quadratic forms are uniformly equivalent. -/
theorem exists_uniform_bounds [CompactSpace M] :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (x : M) (u : E x),
      c * (h.pairing x u u).re ≤ (k.pairing x u u).re ∧
        (k.pairing x u u).re ≤ C * (h.pairing x u u).re := by
  /- Apply compact-set comparison to the whole base and remove its membership
  condition. These constants compare the two smooth metrics, not arbitrary
  original fiber norms whose dependence on x need not be smooth. -/
  obtain ⟨c, C, hc, hC, hbounds⟩ := h.exists_bounds_on_compact k Set.univ isCompact_univ
  exact ⟨c, C, hc, hC, fun x u ↦ hbounds x (Set.mem_univ x) u⟩

end AtiyahSinger.SmoothHermitianMetric
