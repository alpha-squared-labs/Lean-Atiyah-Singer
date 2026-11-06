/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Geometry.Manifold.Algebra.LieGroup

/-!
# Smooth orthonormal frames for a family of Hermitian forms

Public module ID: M1402.

Finite Gram--Schmidt applied to a fixed basis is smooth wherever the given
positive Hermitian forms have smooth Gram entries. Linear independence makes
each normalization denominator strictly positive. The inverse coordinates
are the same Hermitian pairings, so both frame matrices are smooth.

This is the smooth version of the local orthonormalization used in the
original Hermitian flag topology, with the original underlying topology fixed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators Manifold ContDiff ComplexConjugate

/-- Smooth positive Gram entries give smooth frames and inverse frames for those same forms. -/
theorem exists_smoothHermitianFrames {n r : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (b : Module.Basis (Fin r) ℂ V) (H : M → InnerProductSpace.Core ℂ V) (U : Set M)
    (hH : ∀ i j : Fin r, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
      (fun x ↦ (H x).inner (b i) (b j)) U) :
    ∃ e : M → EuclideanSpace ℂ (Fin r) ≃ₗ[ℂ] V,
      (∀ x u v, (H x).inner (e x u) (e x v) = inner ℂ u v) ∧
        (∀ i : Fin r, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, V) ∞
          (fun x ↦ e x (EuclideanSpace.basisFun (Fin r) ℂ i)) U) ∧
        ∀ i : Fin r, ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
          (fun x ↦ (e x).symm (b i)) U := by
  classical
  let : ContMDiffMul 𝓘(ℝ, ℂ) ∞ ℂ :=
    ⟨(contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
      (contMDiff_fst.prodMk_space contMDiff_snd)⟩
  let : ContMDiffSMul 𝓘(ℝ, ℂ) 𝓘(ℝ, V) ∞ ℂ V :=
    ⟨(contDiff_smul (𝕜 := ℝ) (𝕜' := ℂ) (F := V)).contMDiff.comp
      (contMDiff_fst.prodMk_space contMDiff_snd)⟩
  let : ContMDiffSMul 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
      ℂ (EuclideanSpace ℂ (Fin r)) :=
    ⟨(contDiff_smul (𝕜 := ℝ) (𝕜' := ℂ) (F := EuclideanSpace ℂ (Fin r))).contMDiff.comp
      (contMDiff_fst.prodMk_space contMDiff_snd)⟩
  let : ContMDiffInv₀ 𝓘(ℝ, ℂ) ∞ ℂ :=
    ⟨fun x hx ↦ (contDiffAt_inv ℝ hx (n := ∞)).contMDiffAt⟩
  let b₀ : OrthonormalBasis (Fin r) ℂ (EuclideanSpace ℂ (Fin r)) :=
    EuclideanSpace.basisFun (Fin r) ℂ
  let β := b
  let originalModule : Module ℂ V := inferInstance
  let normed (x : M) : PLift (NormedAddCommGroup V) := ⟨(H x).toNormedAddCommGroup⟩
  let metric (x : M) : letI := (normed x).down; letI := originalModule
      PLift (InnerProductSpace ℂ V) :=
    letI := (normed x).down
    letI := originalModule
    ⟨InnerProductSpace.ofCore (H x).toCore⟩
  -- Smoothness of arbitrary pairings follows from the original finite Gram matrix.
  have hpair (v w : M → V)
      (hv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ v U)
      (hw : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ w U) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ (H x).inner (v x) (w x)) U := by
    have hcoord (i : Fin r) (v : M → V)
        (hv : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ v U) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ b.repr (v x) i) U :=
      ((b.coord i).toContinuousLinearMap.restrictScalars ℝ).contDiff.contMDiff.comp_contMDiffOn hv
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ ∑ i : Fin r, ∑ j : Fin r,
          conj (b.repr (v x) i) * b.repr (w x) j * (H x).inner (b i) (b j)) U := by
      apply contMDiffOn_finsetSum
      intro i _
      apply contMDiffOn_finsetSum
      intro j _
      exact ((Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcoord i v hv)).mul
        (hcoord j w hw)).mul (hH i j)
    apply hs.congr
    intro x _
    let := (normed x).down
    let := originalModule
    let := (metric x).down
    change inner ℂ (v x) (w x) = _
    conv_lhs => rw [← β.sum_repr (v x), ← β.sum_repr (w x)]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      β, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  let g (i : Fin r) (x : M) : V :=
    letI := (normed x).down
    letI := originalModule
    letI := (metric x).down
    InnerProductSpace.gramSchmidt ℂ β i
  let length (i : Fin r) (x : M) : ℝ :=
    letI := (normed x).down
    letI := originalModule
    ‖g i x‖
  have hg_ne (i : Fin r) (x : M) : g i x ≠ 0 := by
    let := (normed x).down
    let := originalModule
    let := (metric x).down
    exact InnerProductSpace.gramSchmidt_ne_zero i β.linearIndependent
  have hlength_ne (i : Fin r) (x : M) : length i x ≠ 0 := by
    let := (normed x).down
    let := originalModule
    exact norm_ne_zero_iff.mpr (hg_ne i x)
  have hlength_eq (i : Fin r) (x : M) :
      length i x = Real.sqrt ((H x).inner (g i x) (g i x)).re := rfl
  have hlength (i : Fin r)
      (hi : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ (g i) U) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞ (length i) U := by
    have hp := Complex.reCLM.contMDiff.comp_contMDiffOn (hpair (g i) (g i) hi hi)
    have hn (x : M) : ((H x).inner (g i x) (g i x)).re ≠ 0 := by
      let := (normed x).down
      let := originalModule
      let := (metric x).down
      exact ne_of_gt ((re_inner_self_pos (𝕜 := ℂ)).mpr (hg_ne i x))
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) ∞
        (fun x ↦ Real.sqrt ((H x).inner (g i x) (g i x)).re) U := by
      intro x hx
      exact (Real.contDiffAt_sqrt (hn x)).contMDiffAt.comp_contMDiffWithinAt x (hp x hx)
    exact hs.congr (fun x _ ↦ hlength_eq i x)
  -- Each Gram--Schmidt step uses only earlier smooth vectors and nonzero denominators.
  have hg (i : Fin r) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ (g i) U := by
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hc (j : Fin r) (hj : j ∈ Finset.Iio i) :
          ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
            (fun x ↦ (H x).inner (g j x) (β i) / (length j x : ℂ) ^ 2) U := by
        have hj' := ih j (Finset.mem_Iio.mp hj)
        exact (hpair (g j) (fun _ ↦ β i) hj' contMDiffOn_const).div₀
          ((Complex.ofRealCLM.contMDiff.comp_contMDiffOn (hlength j hj')).pow 2)
          (fun x _ ↦ pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (hlength_ne j x)))
      have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
          (fun x ↦ ∑ j ∈ Finset.Iio i,
            ((H x).inner (g j x) (β i) / (length j x : ℂ) ^ 2) • g j x) U := by
        apply contMDiffOn_finsetSum
        intro j hj
        exact (hc j hj).smul (ih j (Finset.mem_Iio.mp hj))
      apply ((contMDiffOn_const (c := β i)).sub hsum).congr
      intro x _
      let := (normed x).down
      let := originalModule
      let := (metric x).down
      change InnerProductSpace.gramSchmidt ℂ β i = _
      rw [eq_sub_iff_add_eq]
      exact (InnerProductSpace.gramSchmidt_def'' ℂ β i).symm
  let o (x : M) : letI := (normed x).down; letI := originalModule
      letI := (metric x).down; OrthonormalBasis (Fin r) ℂ V :=
    letI := (normed x).down
    letI := originalModule
    letI := (metric x).down
    OrthonormalBasis.mk (InnerProductSpace.gramSchmidtNormed_orthonormal β.linearIndependent)
      (by rw [InnerProductSpace.span_gramSchmidtNormed_range,
        InnerProductSpace.span_gramSchmidt, β.span_eq])
  have ho (i : Fin r) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞ (fun x ↦ o x i) U := by
    have hc := (Complex.ofRealCLM.contMDiff.comp_contMDiffOn (hlength i (hg i))).inv₀
      (fun x _ ↦ Complex.ofReal_ne_zero.mpr (hlength_ne i x))
    apply (hc.smul (hg i)).congr
    intro x _
    let := (normed x).down
    let := originalModule
    let := (metric x).down
    simp only [o, OrthonormalBasis.coe_mk, InnerProductSpace.gramSchmidtNormed, g, length]
    rfl
  let e (x : M) : EuclideanSpace ℂ (Fin r) ≃ₗ[ℂ] V :=
    letI := (normed x).down
    letI := originalModule
    letI := (metric x).down
    (o x).repr.symm.toLinearEquiv
  have he (x : M) (i : Fin r) : e x (b₀ i) = o x i := by
    let := (normed x).down
    let := originalModule
    let := (metric x).down
    simpa only [e, b₀, EuclideanSpace.basisFun_apply,
      LinearIsometryEquiv.coe_toLinearEquiv] using (o x).repr_symm_single i
  have hiso (x : M) (u v : EuclideanSpace ℂ (Fin r)) :
      (H x).inner (e x u) (e x v) = inner ℂ u v := by
    let := (normed x).down
    let := originalModule
    let := (metric x).down
    exact (o x).repr.symm.inner_map_map u v
  refine ⟨e, hiso, ?_, ?_⟩
  · intro i
    change ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V) ∞
      (fun x ↦ e x (b₀ i)) U
    simpa only [he] using ho i
  · intro j
    have hcoords (i : Fin r) : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun x ↦ ((e x).symm (b j)) i) U := by
      apply (hpair (fun x ↦ o x i) (fun _ ↦ b j) (ho i) contMDiffOn_const).congr
      intro x _
      have h := hiso x (b₀ i) ((e x).symm (b j))
      rw [(e x).apply_symm_apply, he] at h
      exact (b₀.repr_apply_apply _ i).trans h.symm
    have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun x ↦ ∑ i : Fin r, ((e x).symm (b j)) i • b₀ i) U :=
      contMDiffOn_finsetSum (fun i (_ : i ∈ Finset.univ) ↦
        (hcoords i).smul (contMDiffOn_const (c := b₀ i)))
    apply hs.congr
    intro x _
    exact (b₀.sum_repr ((e x).symm (b j))).symm

end AtiyahSinger
