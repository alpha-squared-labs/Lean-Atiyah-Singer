/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedMetricL2KernelCokernel
public import AtiyahSinger.Analysis.ClosedOperatorRange
public import AtiyahSinger.Analysis.SmoothFiniteRankProjection

/-!
# The bounded smooth Green operator of the original elliptic map

Public module ID: M0969.

The Fredholm alternative gives a unique smooth solution orthogonal to the
original kernel after removing the actual metric-adjoint kernel projection.
The closed integral realization then proves its genuine L² bound. Both exact
Green identities use the original operator and its two metric projections.
No pseudodifferential or parameter-family regularity of the Green map is claimed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hBorel hE hF hμ

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)

namespace PseudodifferentialOperator

variable (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)

/-- The original elliptic map has a bounded smooth Green operator with both exact projections. -/
theorem exists_smoothGreenOperator
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F) (hP : P.IsElliptic) :
    let W : Submodule ℂ (h.SmoothL2Section μ) := P.toLinearMap.ker
    let W' : Submodule ℂ (k.SmoothL2Section μ) := (P.metricFormalAdjoint h k).toLinearMap.ker
    letI : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
    letI : FiniteDimensional ℂ W' :=
      (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
        ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
    ∃ G : k.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ,
      (∀ u : h.SmoothL2Section μ, G (P.toLinearMap u) = u - W.starProjection u) ∧
      (∀ v : k.SmoothL2Section μ, P.toLinearMap (G v) = v - W'.starProjection v) ∧
      (∀ v : k.SmoothL2Section μ, G v ∈ W.orthogonal) ∧
      ∀ (v : k.SmoothL2Section μ) (u : h.SmoothL2Section μ),
        P.toLinearMap u = v - W'.starProjection v → u ∈ W.orthogonal → u = G v := by
  classical
  intro W W'
  let : FiniteDimensional ℂ W := P.finiteDimensional_ker_of_isElliptic A B hP
  let : FiniteDimensional ℂ W' :=
    (P.metricFormalAdjoint h k).finiteDimensional_ker_of_isElliptic B A
      ((P.isElliptic_metricFormalAdjoint_iff h k).mpr hP)
  let p : h.SmoothL2Section μ →ₗ[ℂ] k.SmoothL2Section μ := P.toLinearMap
  let i : h.SmoothL2Section μ →ₗ[ℂ] h.L2SectionSpace μ := h.smoothToL2 μ
  let j : k.SmoothL2Section μ →ₗ[ℂ] k.L2SectionSpace μ := k.smoothToL2 μ
  have hi_inner (u v : h.SmoothL2Section μ) : inner ℂ (i u) (i v) = inner ℂ u v :=
    h.inner_smoothToL2 μ u v
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  -- The smooth Fredholm alternative solves precisely the projected right-hand side.
  have hsolve (v : k.SmoothL2Section μ) :
      ∃ u : h.SmoothL2Section μ,
        p u = v - W'.starProjection v ∧ u ∈ W.orthogonal := by
    have hrange : v - W'.starProjection v ∈ p.range := by
      apply (P.mem_range_iff_pairing_metricFormalAdjoint_eq_zero h k A B Q hQ _).mpr
      intro w
      exact W'.sub_starProjection_mem_orthogonal v w.val w.property
    obtain ⟨u, hu⟩ := hrange
    refine ⟨u - W.starProjection u, ?_, W.sub_starProjection_mem_orthogonal u⟩
    rw [map_sub, show p (W.starProjection u) = 0 from
      W.starProjection_apply_mem u, sub_zero]
    exact hu
  have hunique (u v : h.SmoothL2Section μ) (hu : u ∈ W.orthogonal)
      (hv : v ∈ W.orthogonal) (heq : p u = p v) : u = v := by
    have hker : u - v ∈ W := by
      change p (u - v) = 0
      rw [map_sub, heq, sub_self]
    have horth : u - v ∈ W.orthogonal := W.orthogonal.sub_mem hu hv
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (horth _ hker))
  let g (v : k.SmoothL2Section μ) : h.SmoothL2Section μ := (hsolve v).choose
  have hg (v : k.SmoothL2Section μ) :
      p (g v) = v - W'.starProjection v ∧ g v ∈ W.orthogonal :=
    (hsolve v).choose_spec
  let G₀ : k.SmoothL2Section μ →ₗ[ℂ] h.SmoothL2Section μ := {
    toFun := g
    map_add' v w := by
      apply hunique _ _ (hg _).2 (W.orthogonal.add_mem (hg v).2 (hg w).2)
      rw [(hg _).1, p.map_add, (hg v).1, (hg w).1, W'.starProjection.map_add]
      abel
    map_smul' c v := by
      apply hunique _ _ (hg _).2 (W.orthogonal.smul_mem c (hg v).2)
      rw [(hg _).1, p.map_smul, (hg v).1, W'.starProjection.map_smul, smul_sub] }
  -- Compare with the bounded inverse of the same closed graph, retaining the actual kernel map.
  let L := P.metricL2ClosedRealization h k
  have hL := P.metricL2ClosedRealization_realization h k
  have hFred := P.closed_range_finite_metricL2ClosedRealization h k hP
  obtain ⟨S, hSorth, hSgraph⟩ := L.exists_bounded_generalizedInverse hL.2.2 hL.2.1 hFred.1
  obtain ⟨e, _, he, _⟩ := P.exists_metricL2ClosedRealization_kernel_cokernel_equiv h k hP
  have hsmoothGraph (u : h.SmoothL2Section μ) :
      (i u, j (p u)) ∈ L.graph := by
    rw [hL.1]
    apply (P.metricL2SmoothCore h k).graph.le_topologicalClosure
    let f := LinearEquiv.ofInjective (i) (h.smoothToL2_injective μ)
    exact (P.metricL2SmoothCore h k).mem_graph_iff.mpr
      ⟨f u, rfl, congrArg (fun w ↦ j (p w)) (f.symm_apply_apply u)⟩
  have horth (u : h.SmoothL2Section μ) (hu : u ∈ W.orthogonal) :
      i u ∈ L.ker.orthogonal := by
    intro x hx
    obtain ⟨w, hw⟩ := e.surjective ⟨x, hx⟩
    let w₀ : h.SmoothL2Section μ := w.val
    have hxw : i w₀ = x := (he w).symm.trans (congrArg Subtype.val hw)
    rw [← hxw, hi_inner]
    exact hu w.val w.property
  have hcompare (v : k.SmoothL2Section μ) :
      i (G₀ v) = S (j (v - W'.starProjection v)) := by
    have hinput := hsmoothGraph (G₀ v)
    change (i (G₀ v), j (p (g v))) ∈
      L.graph at hinput
    rw [(hg v).1] at hinput
    have hrange : j (v - W'.starProjection v) ∈ L.toFun.range :=
      LinearPMap.mem_range_iff.mpr ⟨i (G₀ v), hinput⟩
    have houtput := hSgraph _ hrange
    have hdiff : i (G₀ v) -
        S (j (v - W'.starProjection v)) ∈ L.ker := by
      have hh := L.graph.sub_mem hinput houtput
      have hz : j (v - W'.starProjection v) -
          j (v - W'.starProjection v) = 0 := sub_self _
      obtain ⟨w, hw, hLw⟩ := L.mem_graph_iff.mp hh
      exact L.mem_ker_iff.mpr ⟨w, hw.symm, hLw.trans hz⟩
    have hdifforth : i (G₀ v) - S (j (v - W'.starProjection v)) ∈ L.ker.orthogonal :=
      L.ker.orthogonal.sub_mem (horth (G₀ v) (hg v).2) (hSorth _)
    exact sub_eq_zero.mp (inner_self_eq_zero.mp (hdifforth _ hdiff))
  have hnorm (u : h.SmoothL2Section μ) : ‖i u‖ = ‖u‖ :=
    UniformSpace.Completion.norm_coe u
  have knorm (v : k.SmoothL2Section μ) : ‖j v‖ = ‖v‖ :=
    UniformSpace.Completion.norm_coe v
  have hbound (v : k.SmoothL2Section μ) : ‖G₀ v‖ ≤ (2 * ‖S‖) * ‖v‖ := by
    rw [← hnorm, hcompare]
    calc
      ‖S (j (v - W'.starProjection v))‖ ≤
          ‖S‖ * ‖j (v - W'.starProjection v)‖ := S.le_opNorm _
      _ = ‖S‖ * ‖v - W'.starProjection v‖ := by rw [knorm]
      _ ≤ ‖S‖ * (‖v‖ + ‖W'.starProjection v‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖S‖ * (‖v‖ + ‖v‖) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl (W'.norm_starProjection_apply_le v))
          (norm_nonneg _)
      _ = (2 * ‖S‖) * ‖v‖ := by ring
  let G : k.SmoothL2Section μ →L[ℂ] h.SmoothL2Section μ := G₀.mkContinuous (2 * ‖S‖) hbound
  -- The two exact Green identities follow from the same orthogonal smooth solution.
  have hright (u : h.SmoothL2Section μ) : G (p u) = u - W.starProjection u := by
    apply hunique _ _ (hg _).2 (W.sub_starProjection_mem_orthogonal u)
    have hPi : W'.starProjection (p u) = 0 := by
      apply W'.starProjection_apply_eq_zero_iff.mpr
      intro w hw
      exact (P.mem_range_iff_pairing_metricFormalAdjoint_eq_zero h k A B Q hQ _).mp
        ⟨u, rfl⟩ ⟨w, hw⟩
    change p (g (p u)) = _
    rw [(hg _).1, hPi, sub_zero, map_sub,
      show p (W.starProjection u) = 0 from W.starProjection_apply_mem u, sub_zero]
  refine ⟨G, hright, fun v ↦ (hg v).1, fun v ↦ (hg v).2, ?_⟩
  intro v u hu huorth
  exact hunique u (G v) huorth (hg v).2 (hu.trans (hg v).1.symm)

end PseudodifferentialOperator

end AtiyahSinger
