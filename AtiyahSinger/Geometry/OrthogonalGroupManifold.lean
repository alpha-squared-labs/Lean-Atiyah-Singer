/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphere
public import Mathlib.Algebra.Star.Module
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The original real orthogonal group as a compact Lie group

Public module ID: M1332.

The model is mathlib's real submodule of skew-adjoint matrices. Its norm is
the existing Euclidean operator norm; its topology is the original matrix
subspace topology. Cayley coordinates and their left translates give an
atlas on the existing `Matrix.orthogonalGroup`, without changing its points,
group operations or topology. The Cayley chart is pinned to both rational
matrix formulas, its exact source, and its entire skew-adjoint target.

This standard matrix-group construction supplies the Lie-group input used
in SG III.9 and III.13. It is a supplementary construction, not a separately
numbered lemma from those passages. It includes `O(0)` and does not identify
the orthogonal group with an open subset of the full matrix space.

Smooth maps into the group are detected by their original real entries.
Consumers can assemble these entries in the ordinary iterated Pi space,
without silently identifying different matrix norms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Matrix
open scoped Manifold ContDiff Matrix.Norms.L2Operator

/-- The standard real skew-adjoint matrix model for the orthogonal group. -/
abbrev OrthogonalGroupModel (r : ℕ) : Type :=
  ↥(skewAdjoint.submodule ℝ (Matrix (Fin r) (Fin r) ℝ))

/-- The Cayley chart with its exact original domain and both matrix formulas. -/
theorem exists_orthogonalGroupCayleyChart (r : ℕ) :
    ∃ e : OpenPartialHomeomorph (Matrix.orthogonalGroup (Fin r) ℝ)
        (OrthogonalGroupModel r),
      e.source = {Q | (1 + Q.val).det ≠ 0} ∧ e.target = Set.univ ∧
      (1 : Matrix.orthogonalGroup (Fin r) ℝ) ∈ e.source ∧
      (∀ Q ∈ e.source, (e Q).val = (1 - Q.val) * (1 + Q.val)⁻¹) ∧
      ∀ A : OrthogonalGroupModel r,
        (e.symm A).val = (1 - A.val) * (1 + A.val)⁻¹ := by
  classical
  let M := Matrix (Fin r) (Fin r) ℝ
  let C : M → M := fun A ↦ (1 - A) * (1 + A)⁻¹
  -- A real skew-adjoint matrix has no eigenvalue -1, including in dimension zero.
  have hskew_unit (A : OrthogonalGroupModel r) : IsUnit (1 + A.val) := by
    have hstar : A.val.transpose = -A.val := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using (skewAdjoint.mem_iff.mp A.property)
    apply Matrix.mulVec_injective_iff_isUnit.mp
    change Function.Injective (1 + A.val).mulVecLin
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro v hv
    change v = 0
    change (1 + A.val) *ᵥ v = 0 at hv
    have hav : A.val *ᵥ v = -v := by
      have hz : v + A.val *ᵥ v = 0 := by simpa only [Matrix.add_mulVec,
        Matrix.one_mulVec] using hv
      exact eq_neg_of_add_eq_zero_right hz
    have hdot : v ⬝ᵥ (A.val *ᵥ v) = 0 := by
      have ht := Matrix.dotProduct_transpose_mulVec A.val v v
      rw [hstar, Matrix.neg_mulVec, dotProduct_neg] at ht
      linarith
    rw [hav, dotProduct_neg] at hdot
    exact dotProduct_self_eq_zero.mp (by linarith)
  -- Clearing the genuine invertible denominator gives the rational involution identities.
  have hright (A : M) (hA : IsUnit (1 + A)) : C A * (1 + A) = 1 - A := by
    dsimp [C]
    rw [mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hA),
      mul_one]
  have hinvolution (A : M) (hA : IsUnit (1 + A)) :
      IsUnit (1 + C A) ∧ C (C A) = A := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hA
    have hcomm : (1 + A) * (1 - A) = (1 - A) * (1 + A) := by
      simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one]
      abel
    have hleft : (1 + A) * C A = 1 - A := by
      dsimp [C]
      rw [← mul_assoc, hcomm, mul_assoc, Matrix.mul_nonsing_inv _ hdet, mul_one]
    have hsum : 1 + C A = (2 : ℝ) • (1 + A)⁻¹ := by
      apply hA.mul_left_inj.mp
      rw [add_mul, one_mul, hright A hA, smul_mul_assoc,
        Matrix.nonsing_inv_mul _ hdet]
      simp [two_smul]
    have htwo : IsUnit ((2 : ℝ) • (1 : M)) := by
      refine isUnit_iff_exists_inv.mpr ⟨(1 / 2 : ℝ) • 1, ?_⟩
      simp
    have hunit : IsUnit (1 + C A) := by
      rw [hsum, ← one_mul ((1 + A)⁻¹), ← smul_mul_assoc]
      exact htwo.mul (Matrix.isUnit_nonsing_inv_iff.mpr hA)
    refine ⟨hunit, hunit.mul_left_inj.mp ?_⟩
    rw [hright (C A) hunit]
    calc
      1 - C A = (1 - A) - C A + A := by abel
      _ = (1 + A) * C A - C A + A := by rw [hleft]
      _ = A * (1 + C A) := by
        simp only [mul_add, add_mul, one_mul, mul_one]
        abel
  have horth (A : OrthogonalGroupModel r) : C A.val ∈ Matrix.orthogonalGroup (Fin r) ℝ := by
    have hA := hskew_unit A
    have hstar : A.val.transpose = -A.val := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
        using (skewAdjoint.mem_iff.mp A.property)
    apply (Matrix.mem_orthogonalGroup_iff' _ ℝ).mpr
    apply hA.mul_left_inj.mp
    apply ((Matrix.isUnit_transpose _).mpr hA).mul_right_inj.mp
    calc
      (1 + A.val)ᵀ * ((C A.val)ᵀ * C A.val * (1 + A.val)) =
          (C A.val * (1 + A.val))ᵀ * (C A.val * (1 + A.val)) := by
        rw [Matrix.transpose_mul (C A.val) (1 + A.val)]
        simp only [mul_assoc]
      _ = (1 - A.val)ᵀ * (1 - A.val) := by rw [hright A.val hA]
      _ = (1 + A.val)ᵀ * (1 * (1 + A.val)) := by
        simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, hstar]
        simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one]
        abel
  have hskew (Q : Matrix.orthogonalGroup (Fin r) ℝ) (hQ : IsUnit (1 + Q.val)) :
      C Q.val ∈ skewAdjoint M := by
    apply skewAdjoint.mem_iff.mpr
    change (C Q.val)ᴴ = -C Q.val
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    apply hQ.mul_left_inj.mp
    apply ((Matrix.isUnit_transpose _).mpr hQ).mul_right_inj.mp
    have htrans : (1 + Q.val)ᵀ * (C Q.val)ᵀ = (1 - Q.val)ᵀ := by
      exact (Matrix.transpose_mul (C Q.val) (1 + Q.val)).symm.trans
        (congrArg Matrix.transpose (hright Q.val hQ))
    have hsum : (1 - Q.val)ᵀ * (1 + Q.val) +
        (1 + Q.val)ᵀ * (1 - Q.val) = 0 := by
      calc
        _ = (2 : ℝ) • (1 - Q.valᵀ * Q.val) := by
          simp only [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one, two_smul]
          simp only [mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one]
          abel
        _ = 0 := by rw [(Matrix.mem_orthogonalGroup_iff' _ ℝ).mp Q.property]; simp
    calc
      (1 + Q.val)ᵀ * ((C Q.val)ᵀ * (1 + Q.val)) =
          (1 - Q.val)ᵀ * (1 + Q.val) := by rw [← mul_assoc, htrans]
      _ = -((1 + Q.val)ᵀ * (1 - Q.val)) := eq_neg_of_add_eq_zero_left hsum
      _ = (1 + Q.val)ᵀ * (-C Q.val * (1 + Q.val)) := by
        rw [neg_mul, mul_neg, hright Q.val hQ]
  -- The skew projection merely supplies irrelevant values outside the prescribed chart source.
  let P : M →L[ℝ] OrthogonalGroupModel r :=
    (show M →ₗ[ℝ] OrthogonalGroupModel r from skewAdjointPart ℝ).toContinuousLinearMap
  have hP (A : OrthogonalGroupModel r) : P A.val = A := by
    change (skewAdjointPart ℝ) A.val = A
    exact congrArg (fun L : OrthogonalGroupModel r →ₗ[ℝ] OrthogonalGroupModel r ↦ L A)
      (skewAdjointPart_comp_subtype_skewAdjoint (R := ℝ) (A := M))
  have hPQ (Q : Matrix.orthogonalGroup (Fin r) ℝ) (hQ : IsUnit (1 + Q.val)) :
      (P (C Q.val)).val = C Q.val :=
    congrArg Subtype.val (hP ⟨C Q.val, hskew Q hQ⟩)
  have hC (X : M) (hX : IsUnit (1 + X)) : ContinuousAt C X := by
    have hinv := NormedRing.inverse_continuousAt hX.unit
    simp only [IsUnit.unit_spec] at hinv
    have hplus : Continuous (fun Y : M ↦ 1 + Y) := continuous_const.add continuous_id
    have hinvc : ContinuousAt (fun Y : M ↦ Ring.inverse (1 + Y)) X :=
      hinv.comp hplus.continuousAt
    have hformula : C = fun Y : M ↦ (1 - Y) * Ring.inverse (1 + Y) := by
      funext Y
      exact congrArg (fun Z : M ↦ (1 - Y) * Z)
        (Matrix.nonsing_inv_eq_ringInverse (1 + Y))
    rw [hformula]
    exact (continuous_const.sub continuous_id).continuousAt.mul hinvc
  let e : OpenPartialHomeomorph (Matrix.orthogonalGroup (Fin r) ℝ)
      (OrthogonalGroupModel r) :=
    { toFun := fun Q ↦ P (C Q.val)
      invFun := fun A ↦ ⟨C A.val, horth A⟩
      source := {Q | (1 + Q.val).det ≠ 0}
      target := Set.univ
      map_source' := fun _ _ ↦ Set.mem_univ _
      map_target' := by
        intro A _
        exact ((Matrix.isUnit_iff_isUnit_det _).mp (hinvolution A.val (hskew_unit A)).1).ne_zero
      left_inv' := by
        intro Q hQ
        apply Subtype.ext
        change C (P (C Q.val)).val = Q.val
        have hunit : IsUnit (1 + Q.val) :=
          (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hQ)
        rw [hPQ Q hunit, (hinvolution Q.val hunit).2]
      right_inv' := by
        intro A _
        change P (C (C A.val)) = A
        rw [(hinvolution A.val (hskew_unit A)).2, hP A]
      open_source := by
        exact isOpen_ne.preimage (by fun_prop :
          Continuous (fun Q : Matrix.orthogonalGroup (Fin r) ℝ ↦ (1 + Q.val).det))
      open_target := isOpen_univ
      continuousOn_toFun := by
        intro Q hQ
        apply P.continuous.continuousAt.comp_continuousWithinAt
        have hunit : IsUnit (1 + Q.val) :=
          (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hQ)
        exact ((hC Q.val hunit).comp continuous_subtype_val.continuousAt).continuousWithinAt
      continuousOn_invFun := by
        apply Continuous.continuousOn
        apply Continuous.subtype_mk
        apply continuous_iff_continuousAt.mpr
        intro A
        exact (hC A.val (hskew_unit A)).comp continuous_subtype_val.continuousAt }
  refine ⟨e, rfl, rfl, ?_, ?_, fun _ ↦ rfl⟩
  · change (1 + (1 : M)).det ≠ 0
    have htwo : IsUnit ((2 : ℝ) • (1 : M)) := by
      refine isUnit_iff_exists_inv.mpr ⟨(1 / 2 : ℝ) • 1, ?_⟩
      simp
    exact ((Matrix.isUnit_iff_isUnit_det _).mp (by simpa [two_smul] using htwo)).ne_zero
  · intro Q hQ
    exact hPQ Q ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hQ))

/-- The specified Cayley chart, selected with its exact matrix-coordinate certificate. -/
def orthogonalGroupCayleyChart (r : ℕ) :
    OpenPartialHomeomorph (Matrix.orthogonalGroup (Fin r) ℝ) (OrthogonalGroupModel r) :=
  (exists_orthogonalGroupCayleyChart r).choose

/-- Left translates of the original Cayley chart, with the chart centered at each group element. -/
instance orthogonalGroupChartedSpace (r : ℕ) :
    ChartedSpace (OrthogonalGroupModel r) (Matrix.orthogonalGroup (Fin r) ℝ) where
  atlas := Set.range fun Q : Matrix.orthogonalGroup (Fin r) ℝ ↦
    (Homeomorph.mulLeft Q⁻¹).toOpenPartialHomeomorph.trans (orthogonalGroupCayleyChart r)
  chartAt Q :=
    (Homeomorph.mulLeft Q⁻¹).toOpenPartialHomeomorph.trans (orthogonalGroupCayleyChart r)
  mem_chart_source Q := by
    change Q ∈ Set.univ ∧ Q⁻¹ * Q ∈ (orthogonalGroupCayleyChart r).source
    refine ⟨Set.mem_univ Q, ?_⟩
    simpa only [orthogonalGroupCayleyChart, inv_mul_cancel] using
      (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.1
  chart_mem_atlas Q := ⟨Q, rfl⟩

/-- Smoothness into the original orthogonal group is exactly smoothness of all its entries. -/
theorem contMDiff_orthogonalGroup_iff {V H M : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [TopologicalSpace H]
    (I : ModelWithCorners ℝ V H) [TopologicalSpace M] [ChartedSpace H M]
    (r : ℕ) (k : ℕ∞ω) (f : M → Matrix.orthogonalGroup (Fin r) ℝ) :
    ContMDiff I 𝓘(ℝ, OrthogonalGroupModel r) k f ↔
      ∀ i j : Fin r, ContMDiff I 𝓘(ℝ) k (fun x ↦ (f x).val i j) := by
  classical
  let Mat := Matrix (Fin r) (Fin r) ℝ
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let C : Mat → Mat := fun A ↦ (1 - A) * (1 + A)⁻¹
  let P : Mat →L[ℝ] (OrthogonalGroupModel r) := LinearMap.toContinuousLinearMap
    (show Mat →ₗ[ℝ] (OrthogonalGroupModel r) from skewAdjointPart ℝ)
  have hP (A : OrthogonalGroupModel r) : P A.val = A := by
    exact congrArg (fun L : (OrthogonalGroupModel r) →ₗ[ℝ] (OrthogonalGroupModel r) ↦ L A)
      (skewAdjointPart_comp_subtype_skewAdjoint (R := ℝ) (A := Mat))
  -- Both formulas refer to the originally selected Cayley chart and its left translates.
  have hinv (g : G) (A : OrthogonalGroupModel r) :
      ((chartAt (OrthogonalGroupModel r) g).symm A).val = g.val * C A.val := by
    change ((g⁻¹)⁻¹ * (orthogonalGroupCayleyChart r).symm A).val = _
    rw [inv_inv]
    change g.val * ((orthogonalGroupCayleyChart r).symm A).val = _
    congr 1
    exact (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.2 A
  have hcenter (g : G) : chartAt (OrthogonalGroupModel r) g g = 0 := by
    change orthogonalGroupCayleyChart r (g⁻¹ * g) = _
    rw [inv_mul_cancel]
    apply Subtype.ext
    have h := (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.1 1
      (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.1
    exact h.trans (by simp)
  have hchart (g q : G) (hq : q ∈ (chartAt (OrthogonalGroupModel r) g).source) :
      chartAt (OrthogonalGroupModel r) g q = P (C (g⁻¹ * q).val) := by
    have hmem : g⁻¹ * q ∈ (orthogonalGroupCayleyChart r).source := hq.2
    have hformula : (orthogonalGroupCayleyChart r (g⁻¹ * q)).val = C (g⁻¹ * q).val :=
      (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.1 _ hmem
    change orthogonalGroupCayleyChart r (g⁻¹ * q) = _
    rw [← hformula, hP]
  -- Matrix inversion is analytic at a genuine unit. The coordinate proof therefore covers ω.
  have hC (A : Mat) (hA : IsUnit (1 + A)) : ContDiffAt ℝ k C A := by
    have hi := contDiffAt_ringInverse ℝ (n := k) hA.unit
    simp only [IsUnit.unit_spec] at hi
    have hs : ContDiffAt ℝ k (fun B : Mat ↦ 1 - B) A :=
      contDiffAt_const.sub contDiffAt_id
    have ha : ContDiffAt ℝ k (fun B : Mat ↦ 1 + B) A :=
      contDiffAt_const.add contDiffAt_id
    change ContDiffAt ℝ k (fun B : Mat ↦ (1 - B) * (1 + B)⁻¹) A
    convert hs.mul (hi.comp A ha) using 1
    funext B
    exact congrArg (fun D : Mat ↦ (1 - B) * D)
      (Matrix.nonsing_inv_eq_ringInverse (1 + B))
  have htwo : IsUnit (1 + (1 : Mat)) := by
    have h : IsUnit ((2 : ℝ) • (1 : Mat)) := by
      refine isUnit_iff_exists_inv.mpr ⟨(1 / 2 : ℝ) • 1, ?_⟩
      simp
    simpa only [two_smul] using h
  let entry (i j : Fin r) : Mat →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  let matrix : (Fin r → Fin r → ℝ) →L[ℝ] Mat :=
    LinearMap.toContinuousLinearMap (LinearMap.id : (Fin r → Fin r → ℝ) →ₗ[ℝ] Mat)
  constructor
  · intro hf i j x
    have hlocal := (contMDiffAt_iff_target.mp (hf x)).2
    have hcoords : ContMDiffAt I 𝓘(ℝ, OrthogonalGroupModel r) k
        (fun y ↦ chartAt (OrthogonalGroupModel r) (f x) (f y)) x := by
      simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] at hlocal
      convert! hlocal using 1
    have hCzero : ContDiffAt ℝ k C (0 : Mat) := hC 0 (by simp)
    have hvalue : ContMDiffAt I 𝓘(ℝ, Mat) k
        (fun y ↦ (f x).val * C (chartAt (OrthogonalGroupModel r) (f x) (f y)).val) x := by
      have hsub := ((skewAdjoint.submodule ℝ Mat).subtypeL.contDiff (n := k)).contMDiff
      have hCat : ContDiffAt ℝ k C
          (chartAt (OrthogonalGroupModel r) (f x) (f x)).val := by
        simpa only [hcenter, ZeroMemClass.coe_zero] using hCzero
      have hc := hCat.contMDiffAt.comp x (hsub.contMDiffAt.comp x hcoords)
      convert! ((ContinuousLinearMap.mul ℝ Mat (f x).val).contDiff.contMDiff.contMDiffAt.comp
        x hc) using 1
    have hentry := (entry i j).contDiff.contMDiff.contMDiffAt.comp x hvalue
    apply hentry.congr_of_eventuallyEq
    filter_upwards [(hf x).continuousAt.eventually
      ((chartAt (OrthogonalGroupModel r) (f x)).open_source.mem_nhds
        (mem_chart_source (OrthogonalGroupModel r) (f x)))] with y hy
    change (f y).val i j = ((f x).val * C (chartAt (OrthogonalGroupModel r) (f x) (f y)).val) i j
    rw [← hinv, (chartAt (OrthogonalGroupModel r) (f x)).left_inv hy]
  · intro hf
    have hentries : ContMDiff I 𝓘(ℝ, Fin r → Fin r → ℝ) k (fun x i j ↦ (f x).val i j) :=
      contMDiff_pi_space.mpr (fun i ↦ contMDiff_pi_space.mpr (hf i))
    have hmat : ContMDiff I 𝓘(ℝ, Mat) k (fun x ↦ (f x).val) :=
      matrix.contDiff.contMDiff.comp hentries
    intro x
    have hcontinuous : ContinuousAt f x :=
      (hmat x).continuousAt.codRestrict (fun y ↦ (f y).property)
    apply contMDiffAt_iff_target.mpr
    refine ⟨hcontinuous, ?_⟩
    have hprod : ContMDiffAt I 𝓘(ℝ, Mat) k
        (fun y ↦ ((f x)⁻¹).val * (f y).val) x :=
      (ContinuousLinearMap.mul ℝ Mat ((f x)⁻¹).val).contDiff.contMDiff.contMDiffAt.comp x (hmat x)
    have hone : ((f x)⁻¹).val * (f x).val = (1 : Mat) := by
      change ((f x)⁻¹ * f x).val = _
      rw [inv_mul_cancel]
      rfl
    have hc : ContMDiffAt I 𝓘(ℝ, Mat) k
        (fun y ↦ C (((f x)⁻¹).val * (f y).val)) x := by
      apply (hC _ ?_).contMDiffAt.comp x hprod
      rw [hone]
      exact htwo
    have hp := P.contDiff.contMDiff.contMDiffAt.comp x hc
    apply hp.congr_of_eventuallyEq
    filter_upwards [hcontinuous.eventually
      ((chartAt (OrthogonalGroupModel r) (f x)).open_source.mem_nhds
        (mem_chart_source (OrthogonalGroupModel r) (f x)))] with y hy
    change chartAt (OrthogonalGroupModel r) (f x) (f y) =
      P (C (((f x)⁻¹ * f y).val))
    exact hchart (f x) (f y) hy

/-- The Cayley atlas makes the original orthogonal matrix group a smooth Lie group. -/
theorem lieGroup_orthogonalGroup (r : ℕ) :
    LieGroup 𝓘(ℝ, OrthogonalGroupModel r) ∞ (Matrix.orthogonalGroup (Fin r) ℝ) := by
  classical
  let Mat := Matrix (Fin r) (Fin r) ℝ
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let C : Mat → Mat := fun A ↦ (1 - A) * (1 + A)⁻¹
  let P : Mat →L[ℝ] OrthogonalGroupModel r := LinearMap.toContinuousLinearMap
    (show Mat →ₗ[ℝ] OrthogonalGroupModel r from skewAdjointPart ℝ)
  have hP (A : OrthogonalGroupModel r) : P A.val = A := by
    exact congrArg (fun L : OrthogonalGroupModel r →ₗ[ℝ] OrthogonalGroupModel r ↦ L A)
      (skewAdjointPart_comp_subtype_skewAdjoint (R := ℝ) (A := Mat))
  have hC (A : Mat) (hA : IsUnit (1 + A)) : ContDiffAt ℝ ∞ C A := by
    have hi := contDiffAt_ringInverse ℝ (n := ∞) hA.unit
    simp only [IsUnit.unit_spec] at hi
    have hs : ContDiffAt ℝ ∞ (fun B : Mat ↦ 1 - B) A :=
      contDiffAt_const.sub contDiffAt_id
    have ha : ContDiffAt ℝ ∞ (fun B : Mat ↦ 1 + B) A :=
      contDiffAt_const.add contDiffAt_id
    change ContDiffAt ℝ ∞ (fun B : Mat ↦ (1 - B) * (1 + B)⁻¹) A
    convert hs.mul (hi.comp A ha) using 1
    funext B
    exact congrArg (fun D : Mat ↦ (1 - B) * D)
      (Matrix.nonsing_inv_eq_ringInverse (1 + B))
  have hchart (g q : G) (hq : q ∈ (chartAt (OrthogonalGroupModel r) g).source) :
      chartAt (OrthogonalGroupModel r) g q = P (C (g⁻¹ * q).val) := by
    have hmem : g⁻¹ * q ∈ (orthogonalGroupCayleyChart r).source := hq.2
    have hformula : (orthogonalGroupCayleyChart r (g⁻¹ * q)).val = C (g⁻¹ * q).val :=
      (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.1 _ hmem
    change orthogonalGroupCayleyChart r (g⁻¹ * q) = _
    rw [← hformula, hP]
  have hinv (g : G) (A : OrthogonalGroupModel r) :
      ((chartAt (OrthogonalGroupModel r) g).symm A).val = g.val * C A.val := by
    change ((g⁻¹)⁻¹ * (orthogonalGroupCayleyChart r).symm A).val = _
    rw [inv_inv]
    change g.val * ((orthogonalGroupCayleyChart r).symm A).val = _
    congr 1
    exact (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.2 A
  -- The exact global Cayley target guarantees invertibility of every skew denominator.
  have hskewUnit (A : OrthogonalGroupModel r) : IsUnit (1 + A.val) := by
    let e := orthogonalGroupCayleyChart r
    let Q := e.symm A
    have htarget : A ∈ e.target := by
      have ht : e.target = Set.univ :=
        (exists_orthogonalGroupCayleyChart r).choose_spec.2.1
      rw [ht]
      trivial
    have hsource : Q ∈ e.source := e.map_target htarget
    have hdet : (1 + Q.val).det ≠ 0 := by
      have hs : e.source = {Q | (1 + Q.val).det ≠ 0} :=
        (exists_orthogonalGroupCayleyChart r).choose_spec.1
      rw [hs] at hsource
      exact hsource
    have hformula : A.val = C Q.val := by
      have h := (exists_orthogonalGroupCayleyChart r).choose_spec.2.2.2.1 Q hsource
      change (e Q).val = C Q.val at h
      rw [e.right_inv htarget] at h
      exact h
    have hsum : (1 + A.val) * (1 + Q.val) = (2 : ℝ) • (1 : Mat) := by
      rw [hformula, add_mul, one_mul]
      change 1 + Q.val + ((1 - Q.val) * (1 + Q.val)⁻¹) * (1 + Q.val) = _
      rw [mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet), mul_one]
      simp [two_smul]
    refine isUnit_iff_exists_inv.mpr ⟨(1 / 2 : ℝ) • (1 + Q.val), ?_⟩
    rw [mul_smul_comm, hsum, smul_smul]
    norm_num
  let entry (i j : Fin r) : Mat →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  let matrix : (Fin r → Fin r → ℝ) →L[ℝ] Mat :=
    LinearMap.toContinuousLinearMap (LinearMap.id : (Fin r → Fin r → ℝ) →ₗ[ℝ] Mat)
  have hentries (i j : Fin r) : ContMDiff 𝓘(ℝ, OrthogonalGroupModel r) 𝓘(ℝ) ∞
      (fun g : G ↦ g.val i j) :=
    (contMDiff_orthogonalGroup_iff 𝓘(ℝ, OrthogonalGroupModel r) r ∞ id).mp contMDiff_id i j
  have hmatrix : ContMDiff 𝓘(ℝ, OrthogonalGroupModel r) 𝓘(ℝ, Mat) ∞
      (fun g : G ↦ g.val) :=
    matrix.contDiff.contMDiff.comp
      (contMDiff_pi_space.mpr (fun i ↦ contMDiff_pi_space.mpr (hentries i)))
  -- Inverse charts and forward charts have their certified rational formulas on their domains.
  have hinvSmooth (g : G) : ContMDiff 𝓘(ℝ, OrthogonalGroupModel r)
      𝓘(ℝ, OrthogonalGroupModel r) ∞ (chartAt (OrthogonalGroupModel r) g).symm := by
    apply (contMDiff_orthogonalGroup_iff 𝓘(ℝ, OrthogonalGroupModel r) r ∞ _).mpr
    intro i j A
    have hs := ((skewAdjoint.submodule ℝ Mat).subtypeL.contDiff (n := ∞)).contMDiff A
    have hc := (hC A.val (hskewUnit A)).contMDiffAt.comp A hs
    have hm := (ContinuousLinearMap.mul ℝ Mat g.val).contDiff.contMDiff.contMDiffAt.comp A hc
    have he := (entry i j).contDiff.contMDiff.contMDiffAt.comp A hm
    apply he.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun A ↦ congrArg (fun B : Mat ↦ B i j) (hinv g A))
  have hchartSmooth (g : G) : ContMDiffOn 𝓘(ℝ, OrthogonalGroupModel r)
      𝓘(ℝ, OrthogonalGroupModel r) ∞ (chartAt (OrthogonalGroupModel r) g)
      (chartAt (OrthogonalGroupModel r) g).source := by
    intro q hq
    have hdet : (1 + (g⁻¹ * q).val).det ≠ 0 := by
      have hmem : g⁻¹ * q ∈ (orthogonalGroupCayleyChart r).source := hq.2
      have hs : (orthogonalGroupCayleyChart r).source = {Q | (1 + Q.val).det ≠ 0} :=
        (exists_orthogonalGroupCayleyChart r).choose_spec.1
      rw [hs] at hmem
      exact hmem
    have hu : IsUnit (1 + (g⁻¹ * q).val) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    have hm := (ContinuousLinearMap.mul ℝ Mat (g⁻¹).val).contDiff.contMDiff.contMDiffAt.comp q
      (hmatrix q)
    have hc := (hC (g⁻¹ * q).val hu).contMDiffAt.comp q hm
    have hp := P.contDiff.contMDiff.contMDiffAt.comp q hc
    apply (hp.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [(chartAt (OrthogonalGroupModel r) g).open_source.mem_nhds hq] with y hy
    exact hchart g y hy
  have hmanifold : IsManifold 𝓘(ℝ, OrthogonalGroupModel r) ∞ G := by
    apply isManifold_of_contDiffOn
    intro e e' he he'
    obtain ⟨g, rfl⟩ := he
    obtain ⟨g', rfl⟩ := he'
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, Set.preimage_id, Set.range_id, Set.inter_univ]
    change ContDiffOn ℝ ∞
      (fun A ↦ chartAt (OrthogonalGroupModel r) g'
        ((chartAt (OrthogonalGroupModel r) g).symm A))
      ((chartAt (OrthogonalGroupModel r) g).symm ≫ₕ
        chartAt (OrthogonalGroupModel r) g').source
    intro A hA
    have hc := (hchartSmooth g').contMDiffAt
      ((chartAt (OrthogonalGroupModel r) g').open_source.mem_nhds hA.2)
    exact (hc.comp A (hinvSmooth g A)).contDiffAt.contDiffWithinAt
  let := hmanifold
  -- Matrix multiplication is a finite sum of products of original smooth entries.
  refine { contMDiff_mul := ?_, contMDiff_inv := ?_ }
  · apply (contMDiff_orthogonalGroup_iff
      (𝓘(ℝ, OrthogonalGroupModel r).prod 𝓘(ℝ, OrthogonalGroupModel r)) r ∞ _).mpr
    intro i j
    change ContMDiff _ 𝓘(ℝ) ∞
      (fun p : G × G ↦ ∑ a : Fin r, p.1.val i a * p.2.val a j)
    exact contMDiff_finsetSum (fun a _ ↦ ((hentries i a).comp contMDiff_fst).mul
      ((hentries a j).comp contMDiff_snd))
  · apply (contMDiff_orthogonalGroup_iff 𝓘(ℝ, OrthogonalGroupModel r) r ∞ _).mpr
    intro i j
    exact hentries j i

/-- The original real orthogonal matrix group is compact, including dimension zero. -/
theorem compactSpace_orthogonalGroup (r : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin r) ℝ) := by
  classical
  let M := Matrix (Fin r) (Fin r) ℝ
  rcases subsingleton_or_nontrivial M with htrivial | hnontrivial
  · let := htrivial
    infer_instance
  · let := hnontrivial
    have hclosed : IsClosed (unitary M : Set M) := isClosed_unitary
    have hbound : (unitary M : Set M) ⊆ Metric.closedBall 0 1 := by
      intro Q hQ
      simpa only [Metric.mem_closedBall, dist_zero_right,
        CStarRing.norm_coe_unitary (⟨Q, hQ⟩ : unitary M)] using (le_refl (1 : ℝ))
    exact (isCompact_iff_compactSpace.mp
      ((isCompact_closedBall (0 : M) 1).of_isClosed_subset hclosed hbound))


end AtiyahSinger
