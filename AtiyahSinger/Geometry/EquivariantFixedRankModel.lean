/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.AtlasFrame
public import AtiyahSinger.Geometry.NativeSmoothAtlas
public import AtiyahSinger.Geometry.SmoothComplexBundleAtlas
public import AtiyahSinger.Geometry.SmoothEquivariantBundle
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.ModelBundleTopology

import AtiyahSinger.Geometry.AtlasFrameTransition
import AtiyahSinger.Topology.HermitianFixedRankModel

/-!
# Fixed-rank native models retaining a specified smooth equivariant atlas

Public module ID: M1191.

The original atlas and its jointly smooth moving action columns determine a
native fixed-rank smooth bundle. A continuous Hermitian metric supplies the
fiber norms. The action on every vector is unchanged, and the identity on
vectors is an equivariant isomorphism for the original continuous topology.
Only the phantom model and the selected native trivialization atlas change.

This is the fixed-rank model step in the standard equivariant smoothing
construction, expanding SG Appendix A, Remark A.1 and the actions of SG III.9.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped BigOperators Manifold ContDiff

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hC : CompactSpace M] [hT : T2Space M]
  [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]

include hC hT hAction in
open Classical in
/-- A fixed-rank native model retains smooth forward and inverse maps for the specified atlas. -/
theorem exists_equivariant_smooth_model_of_rank_with_atlasMaps
    (A : SmoothComplexBundleAtlas (n := n) E) (σ : EquivariantStructure G E) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r)
    (hσ : ∀ (i j : A.Index) (k : Fin (A.rank i)),
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun p : G × M ↦ if hx : p.2 ∈ (A.chart i).baseSet then
          (A.chart j ⟨p.1 • p.2,
            σ.linearMap p.1 p.2 ((A.frameLinearEquiv i p.2 hx).symm (Pi.single k 1))⟩).2
          else 0)
        {p : G × M | p.2 ∈ (A.chart i).baseSet ∧ p.1 • p.2 ∈ (A.chart j).baseSet}) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ τ : EquivariantStructure G F.Fiber,
        τ.IsSmooth (n := n) (r := F.rank) IG ∧
          ∃ e : Iso E F.Fiber, e.IsEquivariant σ τ ∧
            IsSmoothAtlasBundleMap A
              (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) e.toHom.linearMap ∧
            IsSmoothAtlasBundleMap
              (nativeSmoothComplexBundleAtlas (n := n) (r := F.rank) F.Fiber) A
              e.symm.toHom.linearMap := by
  classical
  let : IsFiniteRank E := A.isFiniteRank
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
  have ht : modelTopology V E = t₀ :=
    ContinuousHermitianMetric.modelTopology_nativeModelTopology (E := E) r
  -- Rebuild only the continuity certificate; the moving-fiber linear maps are identical.
  let act := σ.linearMap
  have hone := σ.one_map
  have hmul := σ.mul_map
  have hcont := σ.continuous_action
  let τ : letI := modelTopology V E; EquivariantStructure G E := by
    let := modelTopology V E
    refine { linearMap := act
             one_map := hone
             mul_map := hmul
             continuous_action := ?_ }
    rw [ht]
    exact hcont
  let F : SmoothFiniteComplexBundle (n := n) M := { rank := r, Fiber := E }
  refine ⟨F, rfl, τ, ?_, ?_⟩
  · -- A fixed native column is a constant linear combination of the supplied atlas columns.
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩ a
    let v := (c i).symm (EuclideanSpace.single a 1)
    let col (k : Fin (A.rank (idx i))) (p : G × M) : Fin (A.rank (idx j)) → ℂ :=
      if hx : p.2 ∈ (A.chart (idx i)).baseSet then
        (A.chart (idx j) ⟨p.1 • p.2,
          σ.linearMap p.1 p.2
            ((A.frameLinearEquiv (idx i) p.2 hx).symm (Pi.single k 1))⟩).2
      else 0
    have hs : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) 𝓘(ℝ, V) ∞
        (fun p : G × M ↦ c j (∑ k, v k • col k p))
        {p : G × M | p.2 ∈ (chart i).baseSet ∧ p.1 • p.2 ∈ (chart j).baseSet} := by
      apply (c j).toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
      apply contMDiffOn_finsetSum
      intro k _
      exact ((v k • ContinuousLinearMap.id ℂ (Fin (A.rank (idx j)) → ℂ)).restrictScalars
        ℝ).contMDiff.comp_contMDiffOn (hσ (idx i) (idx j) k)
    apply hs.congr
    intro p hp
    have hinner : (chart i).symmL ℂ p.2 (EuclideanSpace.single a 1) =
        (A.frameLinearEquiv (idx i) p.2 hp.1).symm v := by
      apply (A.frameLinearEquiv (idx i) p.2 hp.1).injective
      rw [LinearEquiv.apply_symm_apply]
      apply (c i).injective
      rw [(chart i).symmL_apply hp.1]
      change (chart i ⟨p.2, (chart i).symm p.2 (EuclideanSpace.single a 1)⟩).2 = c i v
      rw [(chart i).apply_mk_symm hp.1]
      exact ((c i).apply_symm_apply _).symm
    change c j ((A.chart (idx j) ⟨p.1 • p.2,
      σ.linearMap p.1 p.2 ((chart i).symmL ℂ p.2 (EuclideanSpace.single a 1))⟩).2) = _
    rw [hinner]
    apply congrArg (c j)
    let L := (A.frameLinearEquiv (idx j) (p.1 • p.2) hp.2).toLinearMap.comp
      ((σ.linearMap p.1 p.2).comp (A.frameLinearEquiv (idx i) p.2 hp.1).symm.toLinearMap)
    have he := congrArg L ((Pi.basisFun ℂ (Fin (A.rank (idx i)))).sum_repr v)
    have hpi : p.2 ∈ (A.chart (idx i)).baseSet := hp.1
    simp only [col, dite_eq_left hpi]
    change L v = ∑ k, v k • L (Pi.single k 1)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using he.symm
  · -- The identity on every vector intertwines the two literally identical moving maps.
    let e : @Iso M E E _ _ _ _ t₀ (modelTopology V E) :=
      @Iso.mk M E E _ _ _ _ t₀ (modelTopology V E)
        (fun x ↦ LinearEquiv.refl ℂ (E x))
        (by
          rw [ht]
          exact continuous_id)
        (by
          rw [ht]
          exact continuous_id)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_, ?_⟩
    · -- Forward coordinates are original transition matrices followed by one fixed model map.
      refine ⟨contMDiff_id, ?_⟩
      rintro i ⟨_, ⟨j, rfl⟩⟩ k
      let output := (EuclideanSpace.equiv (Fin r) ℂ).toContinuousLinearMap.comp
        (c j).toContinuousLinearMap
      have hs := (output.restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (A.contMDiffOn_coordChange i (idx j) k)
      apply hs.congr
      intro x hx
      simp only [dite_eq_left hx.1]
      change output ((A.chart (idx j)
        ⟨x, (A.frameLinearEquiv i x hx.1).symm (Pi.single k 1)⟩).2) = _
      apply congrArg output
      have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart i).proj_symm_apply' (x := Pi.single k 1) hx.1)
        ((A.chart i).toOpenPartialHomeomorph.symm (x, Pi.single k 1)).2
      exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart (idx j) z).2) hpoint
    · -- Inverse coordinates expand the same constant model vector in the original chart basis.
      refine ⟨contMDiff_id, ?_⟩
      rintro ⟨_, ⟨i, rfl⟩⟩ j k
      let v := (c i).symm ((EuclideanSpace.equiv (Fin r) ℂ).symm (Pi.single k 1))
      have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
          (fun x : M ↦ ∑ a, v a •
            (A.chart j ((A.chart (idx i)).toPartialEquiv.symm (x, Pi.single a 1))).2)
          ((A.chart (idx i)).baseSet ∩ (A.chart j).baseSet) := by
        apply contMDiffOn_finsetSum
        intro a _
        exact ((v a • ContinuousLinearMap.id ℂ (Fin (A.rank j) → ℂ)).restrictScalars ℝ)
          |>.contMDiff.comp_contMDiffOn (A.contMDiffOn_coordChange (idx i) j a)
      apply hs.congr
      intro x hx
      let N := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
      have hnx : letI := modelTopology V E
          x ∈ (N.chart ⟨chart i, ⟨i, rfl⟩⟩).baseSet := hx.1
      rw [dite_eq_left hnx]
      let frame : E x ≃ₗ[ℂ] (Fin r → ℂ) :=
        @frameLinearEquiv n M _ _ E _ _ (modelTopology V E) N ⟨chart i, ⟨i, rfl⟩⟩ x hnx
      have hinverse : frame.symm
          (Pi.single k 1) = (A.frameLinearEquiv (idx i) x hx.1).symm v := by
        apply frame.injective
        rw [LinearEquiv.apply_symm_apply]
        change Pi.single k 1 = (EuclideanSpace.equiv (Fin r) ℂ)
          (c i ((A.frameLinearEquiv (idx i) x hx.1)
            ((A.frameLinearEquiv (idx i) x hx.1).symm v)))
        rw [LinearEquiv.apply_symm_apply]
        exact ((EuclideanSpace.equiv (Fin r) ℂ).apply_symm_apply _).symm.trans
          (congrArg (EuclideanSpace.equiv (Fin r) ℂ) ((c i).apply_symm_apply _).symm)
      change (A.chart j ⟨x, frame.symm
        (Pi.single k 1)⟩).2 = _
      rw [hinverse]
      let L := (A.frameLinearEquiv j x hx.2).toLinearMap.comp
        (A.frameLinearEquiv (idx i) x hx.1).symm.toLinearMap
      have he := congrArg L ((Pi.basisFun ℂ (Fin (A.rank (idx i)))).sum_repr v)
      have hcolumn (a : Fin (A.rank (idx i))) :
          L (Pi.single a 1) =
            (A.chart j ((A.chart (idx i)).toPartialEquiv.symm (x, Pi.single a 1))).2 := by
        have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
          ((A.chart (idx i)).proj_symm_apply' (x := Pi.single a 1) hx.1)
          ((A.chart (idx i)).toOpenPartialHomeomorph.symm (x, Pi.single a 1)).2
        exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2) hpoint
      change L v = _
      simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, hcolumn] using he.symm


include hC hT hAction in
open Classical in
/-- A specified jointly smooth equivariant atlas of fixed rank has the same native smooth model. -/
theorem exists_equivariant_smooth_model_of_rank
    (A : SmoothComplexBundleAtlas (n := n) E) (σ : EquivariantStructure G E) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r)
    (hσ : ∀ (i j : A.Index) (k : Fin (A.rank i)),
      ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun p : G × M ↦ if hx : p.2 ∈ (A.chart i).baseSet then
          (A.chart j ⟨p.1 • p.2,
            σ.linearMap p.1 p.2 ((A.frameLinearEquiv i p.2 hx).symm (Pi.single k 1))⟩).2
          else 0)
        {p : G × M | p.2 ∈ (A.chart i).baseSet ∧ p.1 • p.2 ∈ (A.chart j).baseSet}) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∃ τ : EquivariantStructure G F.Fiber,
        τ.IsSmooth (n := n) (r := F.rank) IG ∧
          ∃ e : Iso E F.Fiber, e.IsEquivariant σ τ := by
  -- Forget only the two additional smooth-atlas compatibility certificates.
  obtain ⟨F, hrF, τ, hτ, e, he, _, _⟩ :=
    exists_equivariant_smooth_model_of_rank_with_atlasMaps IG A σ r hr hσ
  exact ⟨F, hrF, τ, hτ, e, he⟩

end AtiyahSinger.SmoothComplexBundleAtlas
