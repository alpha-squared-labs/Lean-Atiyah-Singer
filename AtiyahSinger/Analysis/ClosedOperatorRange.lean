/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedOperatorKernels
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# The closed range theorem for unbounded Hilbert space operators

Public module ID: M0343.

The original closed graph, restricted to the orthogonal complement of its kernel,
projects bijectively to the original closed range. The Banach inverse theorem gives
a bounded inverse on that range. Adjunction then identifies the actual adjoint range
with the kernel orthogonal complement. No closure is substituted for either range.

These are the standard closed range arguments used for the graded tensor estimate.
-/

@[expose] public noncomputable section

namespace LinearPMap

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- The double actual adjoint recovers the original closed densely defined operator. -/
theorem adjoint_adjoint_eq_of_isClosed (T : E →ₗ.[ℂ] F)
    (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (hTadjoint : Dense (T.adjoint.domain : Set F)) : T.adjoint.adjoint = T := by
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro z hz
    obtain ⟨u, hu, hTu⟩ := T.adjoint.adjoint.mem_graph_iff.mp hz
    let G := T.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
    have hG : _root_.IsClosed (G : Set (WithLp 2 (E × F))) :=
      hTclosed.preimage (WithLp.prod_continuous_ofLp 2 E F)
    have hdouble : WithLp.toLp 2 z ∈ G.orthogonal.orthogonal := by
      intro w hw
      have hrepresent (v : T.domain) : inner ℂ (-(WithLp.ofLp w).1) (v : E) =
          inner ℂ (WithLp.ofLp w).2 (T v) := by
        have hv : WithLp.toLp 2 ((v : E), T v) ∈ G := T.mem_graph v
        have h := hw _ hv
        simp only [WithLp.prod_inner_apply] at h
        have hc := congrArg (starRingEnd ℂ) h
        simp only [_root_.map_add, inner_conj_symm, _root_.map_zero] at hc
        rw [inner_neg_left]
        exact neg_eq_iff_add_eq_zero.mpr hc
      have hd : (WithLp.ofLp w).2 ∈ T.adjoint.domain :=
        T.mem_adjoint_domain_of_exists _ ⟨-(WithLp.ofLp w).1, hrepresent⟩
      have hv : T.adjoint ⟨(WithLp.ofLp w).2, hd⟩ = -(WithLp.ofLp w).1 :=
        T.adjoint_apply_eq hTdense _ hrepresent
      have h := (T.adjoint.adjoint_isFormalAdjoint hTadjoint).symm
        ⟨(WithLp.ofLp w).2, hd⟩ u
      rw [hv, hu, hTu, inner_neg_left] at h
      rw [WithLp.prod_inner_apply, WithLp.ofLp_toLp]
      exact add_eq_zero_iff_eq_neg.mpr (neg_eq_iff_eq_neg.mp h)
    rw [Submodule.orthogonal_orthogonal_eq_closure,
      hG.submodule_topologicalClosure_eq] at hdouble
    exact hdouble
  · exact (T.adjoint_isFormalAdjoint hTdense).le_adjoint hTadjoint

/-- A closed operator with closed range has a bounded inverse on its kernel complement.
The inverse is extended to the whole target by orthogonal projection onto the range. -/
theorem exists_bounded_generalizedInverse (T : E →ₗ.[ℂ] F)
    (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (hrange : _root_.IsClosed (T.toFun.range : Set F)) :
    ∃ S : F →L[ℂ] E,
      (∀ y : F, S y ∈ T.ker.orthogonal) ∧
      (∀ y ∈ T.toFun.range, (S y, y) ∈ T.graph) := by
  -- Both coordinates live in the original closed graph; only the kernel is removed.
  have hker : _root_.IsClosed (T.ker : Set E) := by
    rw [T.ker_eq_orthogonal_adjoint_range hTdense hTclosed]
    exact Submodule.isClosed_orthogonal _
  let : CompleteSpace T.ker := hker.completeSpace_coe
  let R := T.toFun.range
  let : CompleteSpace R := hrange.completeSpace_coe
  let C := T.graph ⊓ T.ker.orthogonal.comap (LinearMap.fst ℂ E F)
  have hC : _root_.IsClosed (C : Set (E × F)) :=
    hTclosed.inter (T.ker.isClosed_orthogonal.preimage continuous_fst)
  let : CompleteSpace C := hC.completeSpace_coe
  let f : C →L[ℂ] R :=
    ((ContinuousLinearMap.snd ℂ E F).comp C.subtypeL).codRestrict R (by
      intro z
      obtain ⟨x, _, hx⟩ := T.mem_graph_iff.mp z.property.1
      exact ⟨x, hx⟩)
  have hbij : Function.Bijective f := by
    constructor
    · intro z w hzw
      have hzero : (z - w).val.2 = 0 := congrArg Subtype.val (sub_eq_zero.mpr hzw)
      have hk : (z - w).val.1 ∈ T.ker := by
        obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp (z - w).property.1
        exact T.mem_ker_iff.mpr ⟨u, hu.symm, hTu.trans hzero⟩
      have hx : (z - w).val.1 = 0 :=
        (inner_self_eq_zero.mp ((z - w).property.2 _ hk))
      apply sub_eq_zero.mp
      exact Subtype.ext (Prod.ext hx hzero)
    · intro y
      obtain ⟨u, hu⟩ := y.property
      obtain ⟨k, hk, hTk⟩ := T.mem_ker_iff.mp (T.ker.starProjection_apply_mem (u : E))
      let v := u - k
      have hv : (v : E) = (u : E) - T.ker.starProjection u := by
        change (u : E) - k = _
        rw [hk]
      have hTv : T v = (y : F) := by
        change T (u - k) = _
        rw [T.map_sub, hTk, sub_zero]
        exact hu
      refine ⟨⟨((v : E), T v), ⟨T.mem_graph v, ?_⟩⟩, Subtype.ext hTv⟩
      change (v : E) ∈ T.ker.orthogonal
      rw [hv]
      exact T.ker.sub_starProjection_mem_orthogonal _
  -- The inverse is continuous because these are Banach spaces, including the zero case.
  let e : C ≃L[ℂ] R :=
    (LinearEquiv.ofBijective f.toLinearMap hbij).toContinuousLinearEquivOfContinuous f.continuous
  let S : F →L[ℂ] E := (ContinuousLinearMap.fst ℂ E F).comp
    (C.subtypeL.comp (e.symm.toContinuousLinearMap.comp R.orthogonalProjectionOnto))
  refine ⟨S, ?_, ?_⟩
  · intro y
    exact (e.symm (R.orthogonalProjectionOnto y)).property.2
  · intro y hy
    have hp : R.orthogonalProjectionOnto y = ⟨y, hy⟩ := by
      exact R.orthogonalProjectionOnto_mem_subspace_eq_self ⟨y, hy⟩
    have he : (e.symm ⟨y, hy⟩).val.2 = y :=
      congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
    have hg := (e.symm ⟨y, hy⟩).property.1
    change (S y, y) ∈ T.graph
    change ((e.symm (R.orthogonalProjectionOnto y)).val.1, y) ∈ T.graph
    rw [hp]
    have hz : ((e.symm ⟨y, hy⟩).val.1, y) = (e.symm ⟨y, hy⟩).val :=
      Prod.ext rfl he.symm
    rw [hz]
    exact hg

/-- Closedness of the original range identifies the actual adjoint range with the kernel
orthogonal complement, and in particular proves that the adjoint range is closed. -/
theorem range_adjoint_eq_orthogonal_ker (T : E →ₗ.[ℂ] F)
    (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (hrange : _root_.IsClosed (T.toFun.range : Set F)) :
    T.adjoint.toFun.range = T.ker.orthogonal := by
  obtain ⟨S, _, hSgraph⟩ := T.exists_bounded_generalizedInverse hTdense hTclosed hrange
  apply le_antisymm
  · intro y hy
    rw [T.ker_eq_orthogonal_adjoint_range hTdense hTclosed]
    exact T.adjoint.toFun.range.le_orthogonal_orthogonal hy
  · intro x hx
    -- The bounded inverse represents the adjoint functional on the entire original domain.
    have hrepresent (u : T.domain) : inner ℂ x (u : E) = inner ℂ (S.adjoint x) (T u) := by
      obtain ⟨v, hv, hTv⟩ := T.mem_graph_iff.mp (hSgraph (T u) ⟨u, rfl⟩)
      have hdiff : (u : E) - S (T u) ∈ T.ker := by
        apply T.mem_ker_iff.mpr
        refine ⟨u - v, ?_, ?_⟩
        · change (u : E) - S (T u) = (u : E) - v
          rw [hv]
        · rw [T.map_sub, hTv, sub_self]
      have hinner := hx _ hdiff
      rw [inner_sub_left] at hinner
      rw [ContinuousLinearMap.adjoint_inner_left]
      simpa only [inner_conj_symm] using
        congrArg (starRingEnd ℂ) (sub_eq_zero.mp hinner)
    have hdomain : S.adjoint x ∈ T.adjoint.domain :=
      T.mem_adjoint_domain_of_exists _ ⟨x, hrepresent⟩
    exact ⟨⟨S.adjoint x, hdomain⟩, T.adjoint_apply_eq hTdense _ hrepresent⟩

/-- A lower bound on the orthogonal complement of the kernel forces the actual range
of a closed operator to be closed. The ambient norm on its original domain is retained. -/
theorem isClosed_range_of_bound (T : E →ₗ.[ℂ] F)
    (hTdense : Dense (T.domain : Set E)) (hTclosed : T.IsClosed)
    (C : ℝ)
    (hbound : ∀ u : T.domain, (u : E) ∈ T.ker.orthogonal → ‖(u : E)‖ ≤ C * ‖T u‖) :
    _root_.IsClosed (T.toFun.range : Set F) := by
  have hker : _root_.IsClosed (T.ker : Set E) := by
    rw [T.ker_eq_orthogonal_adjoint_range hTdense hTclosed]
    exact Submodule.isClosed_orthogonal _
  let : CompleteSpace T.ker := hker.completeSpace_coe
  let G := T.graph ⊓ T.ker.orthogonal.comap (LinearMap.fst ℂ E F)
  have hG : _root_.IsClosed (G : Set (E × F)) :=
    hTclosed.inter (T.ker.isClosed_orthogonal.preimage continuous_fst)
  let : CompleteSpace G := hG.completeSpace_coe
  let f : G →L[ℂ] F := (ContinuousLinearMap.snd ℂ E F).comp G.subtypeL
  -- The graph norm is bounded by the output norm after removing the original kernel.
  have hanti : AntilipschitzWith (Real.toNNReal (max C 1)) f := by
    apply f.antilipschitz_of_bound
    intro z
    obtain ⟨u, hu, hTu⟩ := T.mem_graph_iff.mp z.property.1
    have huorth : (u : E) ∈ T.ker.orthogonal := hu ▸ z.property.2
    have hn := hbound u huorth
    rw [hu, hTu] at hn
    change max ‖z.val.1‖ ‖z.val.2‖ ≤ ↑(Real.toNNReal (max C 1)) * ‖z.val.2‖
    rw [Real.coe_toNNReal _ (le_max_of_le_right zero_le_one)]
    exact max_le (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_right C 1) (norm_nonneg z.val.2))
  have hclosed : _root_.IsClosed (f.range : Set F) := hanti.isClosed_range f.uniformContinuous
  have hrange : f.range = T.toFun.range := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      obtain ⟨u, _, hTu⟩ := T.mem_graph_iff.mp z.property.1
      exact ⟨u, hTu⟩
    · rintro y ⟨u, rfl⟩
      obtain ⟨k, hk, hTk⟩ := T.mem_ker_iff.mp (T.ker.starProjection_apply_mem (u : E))
      have hvorth : ((u - k : T.domain) : E) ∈ T.ker.orthogonal := by
        change (u : E) - k ∈ T.ker.orthogonal
        rw [← hk]
        exact T.ker.sub_starProjection_mem_orthogonal _
      refine ⟨⟨((↑(u - k) : E), T (u - k)), ⟨T.mem_graph _, hvorth⟩⟩, ?_⟩
      change T (u - k) = T u
      rw [T.map_sub, hTk, sub_zero]
  exact hrange ▸ hclosed

end LinearPMap
