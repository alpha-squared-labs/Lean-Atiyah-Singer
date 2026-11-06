/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedOperatorKernels
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.UniformConvergence

/-!
# Bounded approximation in the graph of a closed operator

Public module ID: M0333.

Orthogonal projection onto the graph of `ε T` gives contractions on the source
and target of a closed operator. Their off-diagonal block is bounded, takes
values in the original graph, and intertwines those two contractions with `T`.
The errors on the domains of `T` and its adjoint are bounded by `ε` times the
corresponding graph seminorms. Density then gives strong convergence.

This standard graph-projection construction supplies simultaneous graph
approximation in Hilbert tensor products without a spectral decomposition.
-/

@[expose] public noncomputable section

namespace LinearPMap

open Filter
open scoped Topology

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Projection onto the scaled original graph gives compatible bounded contractions. -/
theorem exists_selfAdjoint_graph_contractions (T : E →ₗ.[ℂ] F)
    (hT : T.IsClosed) (hTdense : Dense (T.domain : Set E))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R : E →L[ℂ] E) (A : E →L[ℂ] F) (S : F →L[ℂ] F),
      ‖R‖ ≤ 1 ∧ ‖S‖ ≤ 1 ∧
      (∀ x : E, (R x, A x) ∈ T.graph) ∧
      (∀ x : T.domain, A x = S (T x)) ∧
      (∀ x : T.domain, ‖R x - x‖ ≤ ε * ‖T x‖) ∧
      (∀ y : T.adjoint.domain, ‖S y - y‖ ≤ ε * ‖T.adjoint y‖) ∧
      IsSelfAdjoint R ∧ IsSelfAdjoint S := by
  -- Work in the Hilbert direct sum, so both coordinate maps have norm at most one.
  let Z := WithLp 2 (E × F)
  let fst : Z →L[ℂ] E := WithLp.fstL 2 ℂ E F
  let snd : Z →L[ℂ] F := WithLp.sndL 2 ℂ E F
  let inl : E →L[ℂ] Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ E F)
  let inr : F →L[ℂ] Z :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℂ E F)
  have hinl (x : E) : ‖inl x‖ = ‖x‖ := WithLp.norm_toLp_fst 2 E F x
  have hinr (y : F) : ‖inr y‖ = ‖y‖ := WithLp.norm_toLp_snd 2 E F y
  have hfst (z : Z) : ‖fst z‖ ≤ ‖z‖ := WithLp.norm_fst_le E z
  have hsnd (z : Z) : ‖snd z‖ ≤ ‖z‖ := WithLp.norm_snd_le E z
  have hpair (x : E) (y : F) : inl x + inr y = WithLp.toLp 2 (x, y) := by
    apply WithLp.ofLp_injective
    change (x, 0) + (0, y) = (x, y)
    simp
  have hsi (x : E) : snd (inl x) = 0 := rfl
  have hsr (y : F) : snd (inr y) = y := rfl
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε.ne'
  let scale : Z →L[ℂ] E × F := fst.prod ((ε : ℂ)⁻¹ • snd)
  let G : Submodule ℂ Z := T.graph.comap scale.toLinearMap
  have hG : _root_.IsClosed (G : Set Z) := hT.preimage scale.continuous
  let : CompleteSpace G := hG.completeSpace_coe
  let proj := G.starProjection
  let projCompl := G.orthogonal.starProjection
  let R := fst.comp (proj.comp inl)
  let A := (ε : ℂ)⁻¹ • snd.comp (proj.comp inl)
  let S := snd.comp (projCompl.comp inr)
  have hcomplement (z : Z) : projCompl z = z - proj z := G.starProjection_orthogonal_val z
  have hgraph (x : T.domain) : inl x + inr ((ε : ℂ) • T x) ∈ G := by
    rw [hpair]
    change ((x : E), (ε : ℂ)⁻¹ • ((ε : ℂ) • T x)) ∈ T.graph
    simpa only [inv_smul_smul₀ hεc] using T.mem_graph x
  have hR (x : E) : ‖R x‖ ≤ ‖x‖ :=
    (hfst _).trans ((G.norm_starProjection_apply_le _).trans_eq (hinl x))
  have hS (y : F) : ‖S y‖ ≤ ‖y‖ :=
    (hsnd _).trans ((G.orthogonal.norm_starProjection_apply_le _).trans_eq (hinr y))
  refine ⟨R, A, S, ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_,
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simpa only [one_mul] using hR x
  · intro y
    simpa only [one_mul] using hS y
  · intro x
    -- The two blocks are read from a point of the very same scaled graph.
    exact G.starProjection_apply_mem (inl x)
  · intro x
    -- The projection fixes graph vectors. Its lower row gives A x = S (T x).
    have hfix : proj (inl x + inr ((ε : ℂ) • T x)) =
        inl x + inr ((ε : ℂ) • T x) :=
      G.starProjection_eq_self_iff.mpr (hgraph x)
    have hrow := congrArg snd hfix
    simp only [_root_.map_add, _root_.map_smul, hsi, hsr, zero_add] at hrow
    have hrow' : snd (proj (inl x)) = (ε : ℂ) • (T x - snd (proj (inr (T x)))) := by
      simpa only [_root_.map_add, _root_.map_smul, _root_.map_zero, zero_add, smul_sub] using
        (eq_sub_iff_add_eq.mpr hrow)
    change (ε : ℂ)⁻¹ • snd (proj (inl x)) = snd (projCompl (inr (T x)))
    rw [hrow', inv_smul_smul₀ hεc, hcomplement, _root_.map_sub]
    rfl
  · intro x
    -- The complementary projection kills (x, ε T x), hence its error is O(ε).
    have hzero : projCompl (inl x + inr ((ε : ℂ) • T x)) = 0 := by
      rw [hcomplement, G.starProjection_eq_self_iff.mpr (hgraph x), sub_self]
    have heq : projCompl (inl x) = -projCompl (inr ((ε : ℂ) • T x)) := by
      exact eq_neg_iff_add_eq_zero.mpr (by simpa only [_root_.map_add] using hzero)
    have herr : fst (projCompl (inl x)) = (x : E) - R x := by
      rw [hcomplement, _root_.map_sub]
      rfl
    calc
      ‖R x - x‖ = ‖fst (projCompl (inl x))‖ := by rw [herr, norm_sub_rev]
      _ ≤ ‖projCompl (inl x)‖ := hfst _
      _ = ‖projCompl (inr ((ε : ℂ) • T x))‖ := by rw [heq, norm_neg]
      _ ≤ ‖inr ((ε : ℂ) • T x)‖ := G.orthogonal.norm_starProjection_apply_le _
      _ = ε * ‖T x‖ := by rw [hinr, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hε]
  · intro y
    -- The actual adjunction puts (-ε T† y, y) in the graph orthogonal.
    have horth : inl (-(ε : ℂ) • T.adjoint y) + inr y ∈ G.orthogonal := by
      intro z hz
      obtain ⟨x, hx, hTx⟩ := T.mem_graph_iff.mp hz
      change (x : E) = (WithLp.ofLp z).1 at hx
      change T x = (ε : ℂ)⁻¹ • (WithLp.ofLp z).2 at hTx
      rw [hpair, WithLp.prod_inner_apply, WithLp.ofLp_toLp]
      change inner ℂ (WithLp.ofLp z).1 (-(ε : ℂ) • T.adjoint y) +
        inner ℂ (WithLp.ofLp z).2 (y : F) = 0
      have hz₂ : (WithLp.ofLp z).2 = (ε : ℂ) • T x := by
        rw [hTx, smul_inv_smul₀ hεc]
      rw [hz₂, ← hx, inner_smul_right, inner_smul_left,
        (T.adjoint_isFormalAdjoint hTdense).symm x y]
      simp only [Complex.conj_ofReal]
      ring
    have hzero : proj (inl (-(ε : ℂ) • T.adjoint y) + inr y) = 0 := by
      change _ ∈ G.starProjection.ker
      rwa [Submodule.ker_starProjection]
    have heq : proj (inr y) = -proj (inl (-(ε : ℂ) • T.adjoint y)) := by
      exact eq_neg_iff_add_eq_zero.mpr (by simpa only [_root_.map_add, add_comm] using hzero)
    have herr : S y - y = -snd (proj (inr y)) := by
      change snd (projCompl (inr y)) - y = _
      rw [hcomplement, _root_.map_sub]
      change (y : F) - snd (proj (inr y)) - y = _
      abel
    calc
      ‖S y - y‖ = ‖snd (proj (inr y))‖ := by rw [herr, norm_neg]
      _ ≤ ‖proj (inr y)‖ := hsnd _
      _ = ‖proj (inl (-(ε : ℂ) • T.adjoint y))‖ := by rw [heq, norm_neg]
      _ ≤ ‖inl (-(ε : ℂ) • T.adjoint y)‖ := G.norm_starProjection_apply_le _
      _ = ε * ‖T.adjoint y‖ := by
        rw [hinl, norm_smul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
  · -- Compressing the same orthogonal projection preserves self-adjointness.
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ (R x) y = inner ℂ x (R y)
    have h := G.starProjection_isSymmetric (inl x) (inl y)
    change inner ℂ (R x) y + inner ℂ (snd (proj (inl x))) 0 =
      inner ℂ x (R y) + inner ℂ (0 : F) (snd (proj (inl y))) at h
    simpa only [inner_zero_right, inner_zero_left, add_zero] using h
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ (S x) y = inner ℂ x (S y)
    have h := G.orthogonal.starProjection_isSymmetric (inr x) (inr y)
    change inner ℂ (fst (projCompl (inr x))) 0 + inner ℂ (S x) y =
      inner ℂ (0 : E) (fst (projCompl (inr y))) + inner ℂ x (S y) at h
    simpa only [inner_zero_right, inner_zero_left, zero_add] using h

/-- Projection onto the scaled original graph gives compatible bounded contractions. -/
theorem exists_graph_contractions (T : E →ₗ.[ℂ] F)
    (hT : T.IsClosed) (hTdense : Dense (T.domain : Set E))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (R : E →L[ℂ] E) (A : E →L[ℂ] F) (S : F →L[ℂ] F),
      ‖R‖ ≤ 1 ∧ ‖S‖ ≤ 1 ∧
      (∀ x : E, (R x, A x) ∈ T.graph) ∧
      (∀ x : T.domain, A x = S (T x)) ∧
      (∀ x : T.domain, ‖R x - x‖ ≤ ε * ‖T x‖) ∧
      (∀ y : T.adjoint.domain, ‖S y - y‖ ≤ ε * ‖T.adjoint y‖) := by
  obtain ⟨R, A, S, hR, hS, hgraph, hmap, herrR, herrS, _, _⟩ :=
    T.exists_selfAdjoint_graph_contractions hT hTdense ε hε
  exact ⟨R, A, S, hR, hS, hgraph, hmap, herrR, herrS⟩

/-- A closed operator with dense source and adjoint domains admits bounded graph approximation.
The target contractions converge strongly as well, so the intertwining identity controls
convergence of actual operator images in tensor products. -/
theorem exists_selfAdjoint_graph_approximation (T : E →ₗ.[ℂ] F)
    (hT : T.IsClosed) (hTdense : Dense (T.domain : Set E))
    (hTadjoint : Dense (T.adjoint.domain : Set F)) :
    ∃ (R : ℕ → E →L[ℂ] E) (A : ℕ → E →L[ℂ] F) (S : ℕ → F →L[ℂ] F),
      (∀ n, ‖R n‖ ≤ 1 ∧ ‖S n‖ ≤ 1) ∧
      (∀ n (x : E), (R n x, A n x) ∈ T.graph) ∧
      (∀ n (x : T.domain), A n x = S n (T x)) ∧
      (∀ x : E, Tendsto (fun n ↦ R n x) atTop (𝓝 x)) ∧
      (∀ y : F, Tendsto (fun n ↦ S n y) atTop (𝓝 y)) ∧
      (∀ n, IsSelfAdjoint (R n) ∧ IsSelfAdjoint (S n)) := by
  -- Choose the scaled-graph projections with a positive parameter decreasing to zero.
  choose R A S h using fun n : ℕ ↦
    exists_selfAdjoint_graph_contractions T hT hTdense (1 / ((n : ℝ) + 1)) (by positivity)
  refine ⟨R, A, S, fun n ↦ ⟨(h n).1, (h n).2.1⟩,
    fun n ↦ (h n).2.2.1, fun n ↦ (h n).2.2.2.1, ?_, ?_,
    fun n ↦ (h n).2.2.2.2.2.2⟩
  · intro x
    -- Uniform contraction makes the strong-convergence set closed; the source domain is dense.
    refine hTdense.induction (P := fun x ↦ Tendsto (fun n ↦ R n x) atTop (𝓝 x)) ?_ ?_ x
    · intro x hx
      rw [tendsto_iff_dist_tendsto_zero]
      simp only [dist_eq_norm]
      apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (h n).2.2.2.2.1 ⟨x, hx⟩)
      simpa only [zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖T ⟨x, hx⟩‖
    · exact (LipschitzWith.uniformEquicontinuous (fun n x ↦ R n x) 1
        (fun n ↦ (R n).lipschitzWith_of_opNorm_le (h n).1)).equicontinuous
          |>.isClosed_setOfPred_tendsto continuous_id
  · intro y
    -- The adjoint-domain estimate gives the same dense-set argument on the target space.
    refine hTadjoint.induction (P := fun y ↦ Tendsto (fun n ↦ S n y) atTop (𝓝 y)) ?_ ?_ y
    · intro y hy
      rw [tendsto_iff_dist_tendsto_zero]
      simp only [dist_eq_norm]
      apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ (h n).2.2.2.2.2.1 ⟨y, hy⟩)
      simpa only [zero_mul] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖T.adjoint ⟨y, hy⟩‖
    · exact (LipschitzWith.uniformEquicontinuous (fun n y ↦ S n y) 1
        (fun n ↦ (S n).lipschitzWith_of_opNorm_le (h n).2.1)).equicontinuous
          |>.isClosed_setOfPred_tendsto continuous_id

/-- A closed operator with dense source and adjoint domains admits bounded graph approximation.
The target contractions converge strongly as well, so the intertwining identity controls
convergence of actual operator images in tensor products. -/
theorem exists_graph_approximation (T : E →ₗ.[ℂ] F)
    (hT : T.IsClosed) (hTdense : Dense (T.domain : Set E))
    (hTadjoint : Dense (T.adjoint.domain : Set F)) :
    ∃ (R : ℕ → E →L[ℂ] E) (A : ℕ → E →L[ℂ] F) (S : ℕ → F →L[ℂ] F),
      (∀ n, ‖R n‖ ≤ 1 ∧ ‖S n‖ ≤ 1) ∧
      (∀ n (x : E), (R n x, A n x) ∈ T.graph) ∧
      (∀ n (x : T.domain), A n x = S n (T x)) ∧
      (∀ x : E, Tendsto (fun n ↦ R n x) atTop (𝓝 x)) ∧
      (∀ y : F, Tendsto (fun n ↦ S n y) atTop (𝓝 y)) := by
  obtain ⟨R, A, S, hnorm, hgraph, hmap, hR, hS, _⟩ :=
    T.exists_selfAdjoint_graph_approximation hT hTdense hTadjoint
  exact ⟨R, A, S, hnorm, hgraph, hmap, hR, hS⟩

end LinearPMap
