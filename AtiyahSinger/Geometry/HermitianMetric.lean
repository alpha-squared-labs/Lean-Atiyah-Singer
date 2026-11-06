/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianPairing
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Explicit smooth Hermitian metrics

Public module ID: M1270.

D02/E01: a smooth Hermitian metric consists of positive definite Hermitian forms
with smooth Gram entries on the original smooth complex vector bundle. The
structure requires real-smooth transitions in that same supplied atlas. The
standard mathlib `InnerProductSpace.Core` supplies the algebraic forms, kept as
explicit data without installing a second norm on a fiber.

The metric carrier is defined over a charted base. Standard smooth-manifold clients
supply `IsManifold` separately; the bundle condition certifies the original bundle
transitions and does not certify smooth compatibility of the base charts.

Sources: Husemoller, Fibre Bundles, III.9.1–9.5, pp.37–38; Spin Geometry III.5,
pp.194–195. Husemoller's first slot is linear; here it is conjugate-linear, as in
mathlib. On a Hausdorff second-countable smooth base, smooth existence is
the partition-of-unity refinement of continuous existence, recorded as a
project deduction rather than a new numbered book lemma.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff ComplexConjugate

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Positive definite Hermitian forms with smooth Gram entries and smooth transitions
in the original complex bundle atlas. -/
structure SmoothHermitianMetric where
  /-- The actual positive definite form on each fiber, without replacing its norm. -/
  toCore : ∀ x, InnerProductSpace.Core ℂ (E x)
  /-- Real smoothness of the Gram entries in every specified smooth frame. -/
  contMDiffOn_gram :
    ∀ (e : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas e],
      ∀ i j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ (toCore x).inner (e.symmL ℂ x (EuclideanSpace.single i 1))
            (e.symmL ℂ x (EuclideanSpace.single j 1))) e.baseSet
  /-- The original complex-linear bundle atlas has real-smooth transition maps. -/
  isSmoothBundle : IsSmoothComplexBundle (n := n) (r := r) E

namespace SmoothHermitianMetric

variable {E} (h : SmoothHermitianMetric (n := n) (r := r) E)

/-- The specified Hermitian form, conjugate-linear in the first variable. -/
def pairing (x : M) (u v : E x) : ℂ := (h.toCore x).inner u v

/-- The local Gram matrix, with the first index in the conjugate-linear slot. -/
def gramMatrix
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j ↦ h.pairing x (e.symmL ℂ x (EuclideanSpace.single i 1))
    (e.symmL ℂ x (EuclideanSpace.single j 1))

/-- The form is continuous for the pre-existing fiber topology. -/
theorem continuous_pairing (x : M) :
    Continuous (fun p : E x × E x ↦ h.pairing x p.1 p.2) := by
  /- A bundle trivialization makes the original fiber finite-dimensional.
  Restrict scalars to regard the specified form as real bilinear, then apply
  finite-dimensional continuity in both variables. The original norm is unchanged. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : NormedSpace ℝ (E x) := NormedSpace.restrictScalars ℝ ℂ (E x)
  let : IsScalarTower ℝ ℂ (E x) := IsScalarTower.restrictScalars ℝ ℂ (E x)
  let : FiniteDimensional ℝ (E x) := Module.Finite.trans ℂ (E x)
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  -- Regard the explicit form as real bilinear data, preserving the original norm.
  let B : E x →ₗ[ℝ] E x →ₗ[ℝ] ℂ :=
    LinearMap.mk₂ ℝ (h.pairing x)
      (fun u v w ↦ (h.toCore x).add_left u v w)
      (by
        intro c u v
        change (h.toCore x).inner (c • u) v = c • (h.toCore x).inner u v
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
          InnerProductSpace.Core.inner_smul_ofReal_left]
        simp [Algebra.smul_def, mul_comm])
      (fun u v w ↦ InnerProductSpace.Core.inner_add_right u v w)
      (by
        intro c u v
        change (h.toCore x).inner u (c • v) = c • (h.toCore x).inner u v
        rw [RCLike.real_smul_eq_coe_smul (K := ℂ),
          InnerProductSpace.Core.inner_smul_ofReal_right]
        simp [Algebra.smul_def, mul_comm])
  -- Finite-dimensional linear continuity and evaluation give joint continuity.
  let Bc : E x →ₗ[ℝ] E x →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp B
  exact (Bc.continuous_of_finiteDimensional.comp continuous_fst).clm_apply continuous_snd

/-- Each metric norm is equivalent to the given norm on the individual fiber. -/
theorem exists_fiber_bounds (x : M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ u : E x,
      c * ‖u‖ ^ 2 ≤ (h.pairing x u u).re ∧
        (h.pairing x u u).re ≤ C * ‖u‖ ^ 2 := by
  /- Compactness of the unit sphere in the given finite-dimensional norm
  supplies a positive lower bound and a finite upper bound for the quadratic
  form. The same compactness lemmas cover an empty unit sphere. Rescale
  nonzero vectors; zero is immediate. These constants are fiberwise, with
  no regular variation of the original norms assumed. -/
  let : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let : NormedSpace ℝ (E x) := NormedSpace.restrictScalars ℝ ℂ (E x)
  let : IsScalarTower ℝ ℂ (E x) := IsScalarTower.restrictScalars ℝ ℂ (E x)
  let : FiniteDimensional ℝ (E x) := Module.Finite.trans ℂ (E x)
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let q : E x → ℝ := fun u ↦ (h.pairing x u u).re
  have hq : Continuous q := Complex.continuous_re.comp
    ((h.continuous_pairing x).comp (continuous_id.prodMk continuous_id))
  -- Compactness gives uniform bounds on the original unit sphere, even if it is empty.
  have hs := isCompact_sphere (0 : E x) 1
  obtain ⟨c, hc, hclower⟩ := hs.exists_forall_le' hq.continuousOn (a := 0) (by
    intro u hu
    have hu0 : u ≠ 0 := by
      intro hz
      simp [hz] at hu
    apply lt_of_le_of_ne ((h.toCore x).re_inner_nonneg u)
    intro hz
    exact hu0 ((InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hz.symm))
  obtain ⟨C, hC⟩ := (hs.image hq).bddAbove
  refine ⟨c, max C 1, hc, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    simp [pairing, InnerProductSpace.Core.inner_zero_left]
  -- Recover a nonzero vector by scaling its normalized direction with its original norm.
  let y : E x := (‖u‖⁻¹ : ℂ) • u
  have hy : y ∈ Metric.sphere (0 : E x) 1 := by
    simpa [y, mem_sphere_zero_iff_norm] using (norm_smul_inv_norm (𝕜 := ℂ) hu)
  have hu_norm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hscale : (‖u‖ : ℂ) • y = u := by
    simp [y, smul_smul, hu_norm]
  have hqscale : q u = q y * ‖u‖ * ‖u‖ := by
    conv_lhs => rw [← hscale]
    exact InnerProductSpace.Core.re_inner_smul_ofReal_smul_self (𝕜 := ℂ) y
  have hlower := hclower y hy
  have hupper : q y ≤ max C 1 := (hC ⟨y, hy, rfl⟩).trans (le_max_left _ _)
  change c * ‖u‖ ^ 2 ≤ q u ∧ q u ≤ max C 1 * ‖u‖ ^ 2
  rw [hqscale]
  constructor <;> nlinarith [sq_nonneg ‖u‖, mul_le_mul_of_nonneg_right hlower (sq_nonneg ‖u‖),
    mul_le_mul_of_nonneg_right hupper (sq_nonneg ‖u‖)]

/-- Positivity on nonzero vectors is strict, including the rank-zero convention. -/
theorem pairing_self_pos (x : M) (u : E x) (hu : u ≠ 0) :
    0 < (h.pairing x u u).re := by
  /- Conjugate symmetry makes the diagonal real. Nonnegativity and definiteness
  exclude zero on a nonzero vector; no positive-rank assumption is needed. -/
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  -- A zero real diagonal would be a zero vector by the original positive form.
  apply lt_of_le_of_ne ((h.toCore x).re_inner_nonneg u)
  intro hz
  apply hu
  exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hz.symm

/-- In a valid frame the pairing is the sesquilinear sum with its Gram matrix. -/
theorem pairing_eq_gramMatrix
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) (u v : E x) :
    h.pairing x u v = ∑ i, ∑ j,
      conj ((e ⟨x, u⟩).2 i) * h.gramMatrix e x i j * (e ⟨x, v⟩).2 j := by
  /- Expand both coordinate vectors in the standard basis, then apply the
  inverse frame. Sesquilinearity puts conjugation on the first coordinate.
  Membership in the base set is necessary to recover the original fiber vectors. -/
  classical
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let B : E x →ₗ⋆[ℂ] E x →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ _ _ (h.pairing x)
      (fun a b c ↦ (h.toCore x).add_left a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
      (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
  -- The inverse frame transports the standard basis expansion into the actual fiber.
  have hexpand (w : E x) :
      ∑ i : Fin r, (e ⟨x, w⟩).2 i • e.symmL ℂ x (EuclideanSpace.single i 1) = w := by
    have heq := congrArg (e.symmL ℂ x)
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr ((e ⟨x, w⟩).2))
    calc
      _ = e.symmL ℂ x ((e ⟨x, w⟩).2) := by
        simpa [map_sum, map_smul, EuclideanSpace.basisFun_apply] using heq
      _ = w := by
        rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx w]
        exact e.symmL_continuousLinearMapAt hx w
  -- Expand each slot with its own scalar convention; the first slot conjugates coefficients.
  change B u v = _
  conv_lhs => rw [← hexpand u, map_sum]
  simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [← hexpand v, map_sum]
  simp only [map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  change conj ((e ⟨x, u⟩).2 i) *
      ((e ⟨x, v⟩).2 j * h.gramMatrix e x i j) = _
  ring

/-- Positive definiteness gives an invertible Gram matrix on the frame base set. -/
theorem isUnit_det_gramMatrix
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (x : M) (hx : x ∈ e.baseSet) :
    IsUnit (h.gramMatrix e x).det := by
  /- A vector in the Gram kernel has zero squared metric norm after applying
  the inverse frame, so it vanishes. Finite dimension turns injectivity into
  invertibility. The empty matrix has determinant one when r=0. -/
  classical
  -- A kernel vector gives an actual fiber vector through the inverse of this same frame.
  have hker : ∀ z : Fin r → ℂ, Matrix.mulVec (h.gramMatrix e x) z = 0 → z = 0 := by
    intro z hz
    let w : E x := (e.continuousLinearEquivAt ℂ x hx).symm (WithLp.toLp 2 z)
    have hwcoord : (e ⟨x, w⟩).2 = WithLp.toLp 2 z :=
      (e.continuousLinearEquivAt ℂ x hx).apply_symm_apply _
    have hwzero : h.pairing x w w = 0 := by
      rw [h.pairing_eq_gramMatrix e x hx, hwcoord]
      simp only [mul_assoc, ← Finset.mul_sum]
      apply Finset.sum_eq_zero
      intro i _
      have hzi := congrFun hz i
      change ∑ j, h.gramMatrix e x i j * z j = 0 at hzi
      simp [hzi]
    have hw : w = 0 := by
      by_contra hw
      have hpos := h.pairing_self_pos x w hw
      simp [hwzero] at hpos
    have hzLp : WithLp.toLp 2 z = (0 : EuclideanSpace ℂ (Fin r)) := by
      rw [← hwcoord, hw]
      rw [← e.continuousLinearMapAt_apply_of_mem ℂ hx]
      exact (e.continuousLinearMapAt ℂ x).map_zero
    exact congrArg WithLp.ofLp hzLp
  -- In finite dimension, a square matrix with zero kernel has a unit determinant.
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.mulVec_injective_iff_isUnit.mp
  exact LinearMap.ker_eq_bot.mp (Matrix.ker_mulVecLin_eq_bot_iff.mpr hker)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option linter.unusedSectionVars false in
-- Preserve the original manifold parameter of this public pairing theorem.
include hM in
/-- The metric pairs smooth sections to a smooth scalar function. -/
theorem contMDiff_pairing (u v : smoothSections (n := n) (r := r) E) :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ h.pairing x (u.val x) (v.val x)) := by
  /- In each valid frame use the finite Gram expansion. The Gram coefficients
  and both section coordinate functions are smooth. Complex conjugation is
  real-smooth, so local smoothness glues over the bundle chart cover. -/
  classical
  intro x
  let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
  -- Each coordinate projection and complex conjugation is real-smooth.
  have hcoord (w : smoothSections (n := n) (r := r) E) (i : Fin r) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ (e ⟨y, w.val y⟩).2 i) e.baseSet := by
    exact ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin r ↦ ℂ) i).restrictScalars ℝ).contDiff.contMDiff
      |>.comp_contMDiffOn (w.property e inferInstance)
  have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ ∑ i, ∑ j, conj ((e ⟨y, u.val y⟩).2 i) *
        h.gramMatrix e y i j * (e ⟨y, v.val y⟩).2 j) e.baseSet := by
    apply contMDiffOn_finsetSum
    intro i _
    apply contMDiffOn_finsetSum
    intro j _
    have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord u i)
    have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
    exact hmul.contMDiff.comp_contMDiffOn
      ((hmul.contMDiff.comp_contMDiffOn
        (hconj.prodMk_space (h.contMDiffOn_gram e i j))).prodMk_space (hcoord v j))
  -- The same valid frame expansion identifies the local formula with the original pairing.
  have hlocal := hsum.congr (f₁ := fun y ↦ h.pairing y (u.val y) (v.val y))
    (fun y hy ↦ h.pairing_eq_gramMatrix e y hy (u.val y) (v.val y))
  exact hlocal.contMDiffAt (e.open_baseSet.mem_nhds hx)

end SmoothHermitianMetric

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hT2 hSC hE in
/-- On a Hausdorff second-countable smooth base, a finite-rank smooth complex bundle
admits a smooth Hermitian metric. -/
theorem nonempty_smoothHermitianMetric :
    Nonempty (SmoothHermitianMetric (n := n) (r := r) E) := by
  /- Choose a locally finite smooth partition of unity subordinate to smooth
  bundle charts. Pull back the standard Hermitian form in each chart and sum
  with the partition weights. Local finiteness gives smooth Gram entries.
  Nonnegative weights with sum one give strict positivity on every nonzero
  vector. This works on noncompact bases and requires no orientation or density. -/
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let e (i : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E i
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) isClosed_univ
    (fun i : M ↦ (e i).baseSet) (fun i ↦ (e i).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, mem_baseSet_trivializationAt _ E x⟩)
  let ρc := ρ.toPartitionOfUnity
  let coord (i x : M) (v : E x) : EuclideanSpace ℂ (Fin r) := (e i ⟨x, v⟩).2
  let q (i x : M) (u v : E x) : ℂ := inner ℂ (coord i x u) (coord i x v)
  let H (x : M) (u v : E x) : ℂ :=
    ∑ i ∈ ρc.finsupport x, ((ρ i x : ℝ) : ℂ) * q i x u v
  have hactive {i x : M} (hi : i ∈ ρc.finsupport x) : x ∈ (e i).baseSet :=
    hρ i (subset_closure ((ρc.mem_finsupport x).mp hi))
  have hnonneg (i x : M) (v : E x) : 0 ≤ (q i x v v).re :=
    inner_self_nonneg (𝕜 := ℂ) (x := coord i x v)
  have hre (x : M) (v : E x) :
      (H x v v).re = ∑ i ∈ ρc.finsupport x, ρ i x * (q i x v v).re := by
    simp [H, Complex.mul_re]
  -- The weighted positive forms live on the original fibers with their original scalars.
  let core (x : M) : InnerProductSpace.Core ℂ (E x) := {
    inner := H x
    conj_inner_symm := by
      intro u v
      simp only [H, map_sum, map_mul, Complex.conj_ofReal]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [q]
      rw [inner_conj_symm]
    re_inner_nonneg := by
      intro v
      change 0 ≤ (H x v v).re
      rw [hre]
      exact Finset.sum_nonneg (fun i _ ↦ mul_nonneg (ρ.nonneg i x) (hnonneg i x v))
    add_left := by
      intro u v w
      simp only [H, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      let hlin := (e i).linearEquivAt ℂ x (hactive hi)
      have hadd : coord i x (u + v) = coord i x u + coord i x v := by
        simpa only [hlin, Trivialization.linearEquivAt_apply, coord] using hlin.map_add u v
      simp only [q, hadd, inner_add_left, mul_add]
    smul_left := by
      intro u v c
      simp only [H, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      let hlin := (e i).linearEquivAt ℂ x (hactive hi)
      have hsmul : coord i x (c • u) = c • coord i x u := by
        simpa only [hlin, Trivialization.linearEquivAt_apply, coord] using hlin.map_smul c u
      simp only [q, hsmul, inner_smul_left]
      ring
    definite := by
      intro v hv
      -- One positive weight selects an actual invertible frame at this base point.
      obtain ⟨i, hi⟩ := ρ.exists_pos_of_mem (Set.mem_univ x)
      have himem : i ∈ ρc.finsupport x := (ρc.mem_finsupport x).mpr (ne_of_gt hi)
      have hsumzero : ∑ j ∈ ρc.finsupport x, ρ j x * (q j x v v).re = 0 := by
        rw [← hre, hv, Complex.zero_re]
      have hterm : ρ i x * (q i x v v).re ≤ 0 := by
        rw [← hsumzero]
        exact Finset.single_le_sum
          (fun j _ ↦ mul_nonneg (ρ.nonneg j x) (hnonneg j x v)) himem
      have hqzero : (q i x v v).re = 0 := by
        nlinarith [hnonneg i x v]
      have hcoordzero : coord i x v = 0 := by
        by_contra hvcoord
        exact (ne_of_gt ((re_inner_self_pos (𝕜 := ℂ)).mpr hvcoord)) hqzero
      apply ((e i).linearEquivAt ℂ x (hactive himem)).injective
      exact hcoordzero.trans (((e i).linearEquivAt ℂ x (hactive himem)).map_zero.symm) }
  refine ⟨{ toCore := core, contMDiffOn_gram := ?_, isSmoothBundle := hE }⟩
  intro f hf a b x hx
  -- In any original frame, each supported chart form is a smooth transition-column pairing.
  let g (i : M) (y : M) : ℂ := q i y
    (f.symmL ℂ y (EuclideanSpace.single a 1))
    (f.symmL ℂ y (EuclideanSpace.single b 1))
  have hsmooth : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun y ↦ ∑ᶠ i, ρ i y • g i y) x := by
    apply ρ.contMDiffAt_finsum
    intro i hi
    have hxi : x ∈ (e i).baseSet := hρ i hi
    have htransition := IsSmoothComplexBundle.contMDiffOn_coordChange
      (n := n) (E := E) f (e i)
    have hvec (v : EuclideanSpace ℂ (Fin r)) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
          (fun y ↦ coord i y (f.symmL ℂ y v)) (f.baseSet ∩ (e i).baseSet) := by
      have heval : ContDiff ℝ ∞
          (fun T : EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r) ↦ T v) :=
        (show ContDiff ℂ ∞ _ from contDiff_id.clm_apply contDiff_const).restrict_scalars ℝ
      apply (heval.contMDiff.comp_contMDiffOn htransition).congr
      intro y hy
      dsimp only [coord]
      rw [f.symmL_apply hy.1]
      exact (f.coordChangeL_apply (e i) hy v).symm
    have hpair := (contDiff_inner (𝕜 := ℂ)).contMDiff.comp_contMDiffOn
      ((hvec (EuclideanSpace.single a 1)).prodMk_space
        (hvec (EuclideanSpace.single b 1)))
    exact hpair.contMDiffAt ((f.open_baseSet.inter (e i).open_baseSet).mem_nhds ⟨hx, hxi⟩)
  -- Local finiteness identifies the same finite metric sum with the smooth weighted sum.
  have heq (y : M) :
      H y (f.symmL ℂ y (EuclideanSpace.single a 1))
        (f.symmL ℂ y (EuclideanSpace.single b 1)) = ∑ᶠ i, ρ i y • g i y := by
    simpa [H, g, ρc, Algebra.smul_def] using
      ρc.sum_finsupport_smul_eq_finsum (x₀ := y) (fun i _ ↦ g i y)
  change ContMDiffWithinAt _ _ _
    (fun y ↦ H y (f.symmL ℂ y (EuclideanSpace.single a 1))
      (f.symmL ℂ y (EuclideanSpace.single b 1))) f.baseSet x
  simp_rw [heq]
  exact hsmooth.contMDiffWithinAt

end AtiyahSinger

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothHermitianBundle (n := n) (r := r) E]

/-- The existing fiber inner products, regarded as explicit metric data. -/
def ofInnerProduct : SmoothHermitianMetric (n := n) (r := r) E where
  toCore := fun _x ↦ InnerProductSpace.toCore
  contMDiffOn_gram := IsSmoothHermitianBundle.contMDiffOn_inner
  isSmoothBundle := IsSmoothHermitianBundle.toIsSmoothComplexBundle

/-- The explicit metric obtained from the installed inner products has their exact values. -/
theorem pairing_ofInnerProduct (x : M) (u v : E x) :
    (ofInnerProduct (n := n) (r := r) E).pairing x u v = inner ℂ u v := by
  /- Both sides are the same inner-product field of the original fiber instance. -/
  rfl

end AtiyahSinger.SmoothHermitianMetric
