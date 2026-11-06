/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ContinuousBundleSmoothing
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.ModelBundleTopology

import AtiyahSinger.Geometry.AtlasFrameTransition
import AtiyahSinger.Topology.HermitianFixedRankModel

/-!
# Native smooth models of fixed-rank continuous complex bundles

Public module ID: M1239.

Choose a compatible smooth atlas on the original bundle, then express its
actual charts in one fixed Euclidean model. Only the phantom total-space model
changes. A continuous Hermitian metric supplies fiber norms, and the selected
smooth charts supply the native vector-bundle atlas. The identity on vectors
gives an isomorphism back to the original continuous bundle topology.

This is the fixed-rank form of the ordinary smooth realization in Spin Geometry
Appendix A, Remark A.1. It does not treat all continuous linear charts as smooth.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hC : CompactSpace M] [hT : T2Space M]
  {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

include hM hC hT hE in
/-- An original continuous bundle of fixed rank has a native smooth model of that same rank. -/
theorem exists_smooth_model_of_rank (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      Nonempty (Iso E F.Fiber) := by
  classical
  obtain ⟨A⟩ := nonempty_smoothComplexBundleAtlas (n := n) (E := E)
  obtain ⟨h⟩ := nonempty_continuousHermitianMetric (E := E)
  let t₀ := (inferInstance : TopologicalSpace (TotalSpace Unit E))
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let V := EuclideanSpace ℂ (Fin r)
  let := nativeModelTopology E V
  choose idx hidx using A.covers
  have hdim (x : M) : A.rank (idx x) = r := by
    have hc := (A.frameLinearEquiv (idx x) x (hidx x)).finrank_eq
    simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hr x] using hc.symm
  let D (x : M) : EuclideanSpace ℂ (Fin (A.rank (idx x))) ≃L[ℂ] V :=
    (LinearEquiv.ofFinrankEq _ _ (by simp [V, hdim x])).toContinuousLinearEquiv
  let c (x : M) : (Fin (A.rank (idx x)) → ℂ) ≃L[ℂ] V :=
    (EuclideanSpace.equiv (Fin (A.rank (idx x))) ℂ).symm.trans (D x)
  -- These are selected original smooth charts, retyped without changing any fiber vector.
  let chart (x : M) : Trivialization V (π V E) :=
    ((A.chart (idx x)).transFiberHomeomorph (c x).toHomeomorph).compHomeomorph
      (nativeModelTotalHomeomorph E V)
  have hchart (x : M) : x ∈ (chart x).baseSet := hidx x
  have hlinear (i : M) : (chart i).IsLinear ℂ := by
    constructor
    intro x hx
    constructor
    · intro v w
      change c i (A.chart (idx i) ⟨x, v + w⟩).2 =
        c i (A.chart (idx i) ⟨x, v⟩).2 + c i (A.chart (idx i) ⟨x, w⟩).2
      rw [(A.linear (idx i) x hx).map_add, map_add]
    · intro a v
      change c i (A.chart (idx i) ⟨x, a • v⟩).2 = a • c i (A.chart (idx i) ⟨x, v⟩).2
      rw [(A.linear (idx i) x hx).map_smul, map_smul]
  let b₀ := h.nativeFiberBundle r hr
  let b : FiberBundle V E :=
    { totalSpaceMk_isInducing' := b₀.totalSpaceMk_isInducing'
      trivializationAtlas' := Set.range chart
      trivializationAt' := chart
      mem_baseSet_trivializationAt' := hchart
      trivialization_mem_atlas' := fun x ↦ ⟨x, rfl⟩ }
  let := b
  let vb : VectorBundle ℂ V E :=
    { trivialization_linear' := by
        rintro _ ⟨i, rfl⟩
        exact hlinear i
      continuousOn_coordChange' := by
        rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
        let := hlinear i
        let := hlinear j
        apply continuousOn_clm_apply.mpr
        intro v
        have hin : ContinuousOn (fun x : M ↦ (x, v))
            ((chart i).baseSet ∩ (chart j).baseSet) :=
          continuousOn_id.prodMk continuousOn_const
        have hback := (chart i).continuousOn_symm.comp hin
          (fun x hx ↦ ⟨hx.1, Set.mem_univ v⟩)
        have hout := (chart j).continuousOn.comp hback
          (fun x hx ↦ (chart j).mem_source.mpr hx.2)
        exact hout.snd.congr (fun x hx ↦ (chart i).coordChangeL_apply (chart j) hx v) }
  let := vb
  -- Assemble the original smooth transition columns before changing the fixed coordinates.
  have hAsmooth (i j : A.Index) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
          EuclideanSpace ℂ (Fin (A.rank j))) ∞ (A.coordChangeL i j)
        ((A.chart i).baseSet ∩ (A.chart j).baseSet) := by
    unfold SmoothComplexBundleAtlas.coordChangeL
    apply contMDiffOn_finsetSum
    intro a _
    let e := EuclideanSpace.equiv (Fin (A.rank j)) ℂ
    have hcol := (e.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn (A.contMDiffOn_coordChange i j a)
    exact ((ContinuousLinearMap.smulRightL ℂ
      (EuclideanSpace ℂ (Fin (A.rank i))) (EuclideanSpace ℂ (Fin (A.rank j)))
      ((ContinuousLinearMap.proj a).comp
        (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).toContinuousLinearMap)).restrictScalars ℝ)
      |>.contMDiff.comp_contMDiffOn hcol
  let B (i j : M) (x : M) : V →L[ℂ] V :=
    (D j).toContinuousLinearMap.comp
      ((A.coordChangeL (idx i) (idx j) x).comp (D i).symm.toContinuousLinearMap)
  have hBsmooth (i j : M) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] V) ∞ (B i j)
        ((chart i).baseSet ∩ (chart j).baseSet) := by
    let pre := ((ContinuousLinearMap.compL ℂ V
      (EuclideanSpace ℂ (Fin (A.rank (idx i))))
      (EuclideanSpace ℂ (Fin (A.rank (idx j))))).flip
      (D i).symm.toContinuousLinearMap).restrictScalars ℝ
    let post := ((ContinuousLinearMap.compL ℂ V
      (EuclideanSpace ℂ (Fin (A.rank (idx j)))) V)
      (D j).toContinuousLinearMap).restrictScalars ℝ
    exact post.contMDiff.comp_contMDiffOn
      (pre.contMDiff.comp_contMDiffOn (hAsmooth (idx i) (idx j)))
  have hB (i j : M) (x : M) (hx : x ∈ (chart i).baseSet ∩ (chart j).baseSet)
      (v : V) : (chart i).coordChangeL ℂ (chart j) x v = B i j x v := by
    let := hlinear i
    let := hlinear j
    let w : E x := (chart i).symm x v
    have hi : D i ((EuclideanSpace.equiv (Fin (A.rank (idx i))) ℂ).symm
        ((A.chart (idx i) ⟨x, w⟩).2)) = v :=
      congrArg Prod.snd ((chart i).apply_mk_symm hx.1 v)
    have hc := A.coordChangeL_apply (idx i) (idx j) x hx w
    rw [(chart i).coordChangeL_apply (chart j) hx v]
    change D j ((EuclideanSpace.equiv (Fin (A.rank (idx j))) ℂ).symm
      ((A.chart (idx j) ⟨x, w⟩).2)) = _
    rw [hc]
    change D j (A.coordChangeL (idx i) (idx j) x
      ((EuclideanSpace.equiv (Fin (A.rank (idx i))) ℂ).symm
        ((A.chart (idx i) ⟨x, w⟩).2))) =
      D j (A.coordChangeL (idx i) (idx j) x ((D i).symm v))
    rw [← hi, ContinuousLinearEquiv.symm_apply_apply]
  let : IsSmoothComplexBundle (n := n) (r := r) E := by
    constructor
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    apply (hBsmooth i j).congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    exact hB i j x hx v
  let F : SmoothFiniteComplexBundle (n := n) M := { rank := r, Fiber := E }
  refine ⟨F, rfl, ?_⟩
  have ht : modelTopology V E = t₀ :=
    ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := E) r
  change Nonempty (@Iso M E E _ _ _ _ t₀ (modelTopology V E))
  rw [ht]
  exact ⟨Iso.refl E⟩

end AtiyahSinger.ComplexBundle
