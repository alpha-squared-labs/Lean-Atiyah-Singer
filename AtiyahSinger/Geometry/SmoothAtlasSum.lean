/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasBundleMaps
public import AtiyahSinger.Geometry.AtlasFrameTransition
public import AtiyahSinger.Geometry.EquivariantAtlasSmoothing
public import AtiyahSinger.Topology.BundleSum

/-!
# Direct sums of the specified smooth bundle atlases

Public module ID: M1368.

The direct sum uses the original product fibers and their existing induced
total topology. Each new chart is the product of two specified original
charts, with the standard concatenation of finite coordinate vectors.
No global rank is imposed. This is the atlas form of the usual smooth
bundle direct sum (SG III.1), needed to retain a prescribed atlas when
adjoining an independently smoothed equivariant complement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)

attribute [local instance] sumTopology

/-- The product chart uses the original two fiber coordinates and the standard concatenation. -/
def sumChart (i : A.Index) (j : B.Index) :
    Trivialization (Fin (A.rank i + B.rank j) → ℂ) (π Unit (E ×ᵇ F)) := by
  classical
  let := A.isFiniteRank
  let := B.isFiniteRank
  let r := A.rank i
  let s := B.rank j
  let e := A.chart i
  let d := B.chart j
  -- Use the two original chart inverses on their common open base set.
  let invE (y : M) (v : Fin r → ℂ) : E y :=
    if hy : y ∈ e.baseSet then
      cast (congrArg E (e.proj_symm_apply' hy)) (e.toPartialEquiv.symm (y, v)).snd
    else 0
  let invF (y : M) (v : Fin s → ℂ) : F y :=
    if hy : y ∈ d.baseSet then
      cast (congrArg F (d.proj_symm_apply' hy)) (d.toPartialEquiv.symm (y, v)).snd
    else 0
  have hpointE (y : M) (v : Fin r → ℂ) (hy : y ∈ e.baseSet) :
      (⟨y, invE y v⟩ : TotalSpace Unit E) = e.toPartialEquiv.symm (y, v) := by
    dsimp only [invE]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := E) (e.proj_symm_apply' hy) _
  have hpointF (y : M) (v : Fin s → ℂ) (hy : y ∈ d.baseSet) :
      (⟨y, invF y v⟩ : TotalSpace Unit F) = d.toPartialEquiv.symm (y, v) := by
    dsimp only [invF]
    rw [dite_eq_left hy]
    exact TotalSpace.mk_cast (F := Unit) (E := F) (d.proj_symm_apply' hy) _
  have hinverseE (y : M) (hy : y ∈ e.baseSet) (v : E y) :
      invE y (e ⟨y, v⟩).2 = v := by
    have hp := (hpointE y (e ⟨y, v⟩).2 hy).trans
      (e.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace Unit E)) (e.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) hp)
  have hinverseF (y : M) (hy : y ∈ d.baseSet) (v : F y) :
      invF y (d ⟨y, v⟩).2 = v := by
    have hp := (hpointF y (d ⟨y, v⟩).2 hy).trans
      (d.symm_apply_mk_proj (x := (⟨y, v⟩ : TotalSpace Unit F)) (d.mem_source.mpr hy))
    exact eq_of_heq (congr_arg_heq (fun z : TotalSpace Unit F ↦ z.snd) hp)
  -- Continuity is proved in the original direct-sum topology, not transported from a chart.
  let pairMap : TotalSpace Unit (E ×ᵇ F) → TotalSpace Unit E × TotalSpace Unit F :=
    fun z ↦ (⟨z.proj, z.snd.1⟩, ⟨z.proj, z.snd.2⟩)
  have hinducing : Topology.IsInducing pairMap := ⟨rfl⟩
  have hprojE : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.1⟩ : TotalSpace Unit E)) := continuous_fst.comp hinducing.continuous
  have hprojF : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z.proj, z.snd.2⟩ : TotalSpace Unit F)) := continuous_snd.comp hinducing.continuous
  have hbase : Continuous (π Unit (E ×ᵇ F)) := (continuous_proj (E := E)).comp hprojE
  let t : Trivialization ((Fin r → ℂ) × (Fin s → ℂ)) (π Unit (E ×ᵇ F)) :=
    { toFun := fun z ↦ (z.proj, (e ⟨z.proj, z.snd.1⟩).2, (d ⟨z.proj, z.snd.2⟩).2)
      invFun := fun y ↦ ⟨y.1, invE y.1 y.2.1, invF y.1 y.2.2⟩
      source := π Unit (E ×ᵇ F) ⁻¹' (e.baseSet ∩ d.baseSet)
      baseSet := e.baseSet ∩ d.baseSet
      target := (e.baseSet ∩ d.baseSet) ×ˢ Set.univ
      map_source' := fun _ h ↦ ⟨h, Set.mem_univ _⟩
      map_target' := fun _ h ↦ h.1
      left_inv' := by
        intro z hz
        exact TotalSpace.ext rfl (heq_of_eq (Prod.ext
          (hinverseE z.proj hz.1 z.snd.1) (hinverseF z.proj hz.2 z.snd.2)))
      right_inv' := by
        intro y hy
        apply Prod.ext
        · rfl
        · apply Prod.ext
          · change (e ⟨y.1, invE y.1 y.2.1⟩).2 = y.2.1
            rw [hpointE y.1 y.2.1 hy.1.1]
            exact congrArg Prod.snd (e.apply_symm_apply' hy.1.1)
          · change (d ⟨y.1, invF y.1 y.2.2⟩).2 = y.2.2
            rw [hpointF y.1 y.2.2 hy.1.2]
            exact congrArg Prod.snd (d.apply_symm_apply' hy.1.2)
      open_source := (e.open_baseSet.inter d.open_baseSet).preimage hbase
      open_target := (e.open_baseSet.inter d.open_baseSet).prod isOpen_univ
      open_baseSet := e.open_baseSet.inter d.open_baseSet
      continuousOn_toFun := hbase.continuousOn.prodMk
        ((continuous_snd.comp_continuousOn
          (e.toOpenPartialHomeomorph.continuousOn.comp hprojE.continuousOn
            (fun _ h ↦ e.mem_source.mpr h.1))).prodMk
          (continuous_snd.comp_continuousOn
            (d.toOpenPartialHomeomorph.continuousOn.comp hprojF.continuousOn
              (fun _ h ↦ d.mem_source.mpr h.2))))
      continuousOn_invFun := by
        rw [hinducing.continuousOn_iff]
        have hE : ContinuousOn (fun y : M × (Fin r → ℂ) × (Fin s → ℂ) ↦
            e.toPartialEquiv.symm (y.1, y.2.1)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          e.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd)).continuousOn
          (fun y hy ↦ e.mem_target.mpr hy.1.1)
        have hF : ContinuousOn (fun y : M × (Fin r → ℂ) × (Fin s → ℂ) ↦
            d.toPartialEquiv.symm (y.1, y.2.2)) ((e.baseSet ∩ d.baseSet) ×ˢ Set.univ) :=
          d.toOpenPartialHomeomorph.continuousOn_symm.comp
          (continuous_fst.prodMk (continuous_snd.comp continuous_snd)).continuousOn
          (fun y hy ↦ d.mem_target.mpr hy.1.2)
        refine (hE.prodMk hF).congr ?_
        intro y hy
        exact Prod.ext (hpointE y.1 y.2.1 hy.1.1) (hpointF y.1 y.2.2 hy.1.2)
      source_eq := rfl
      target_eq := rfl
      proj_toFun := fun _ _ ↦ rfl }
  -- Concatenate the two finite coordinate families by the standard Fin-sum equivalence.
  let c : ((Fin r → ℂ) × (Fin s → ℂ)) ≃L[ℂ] (Fin (r + s) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin r) (Fin s) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (r + s) ↦ ℂ) finSumFinEquiv)).toContinuousLinearEquiv
  exact t.transFiberHomeomorph c.toHomeomorph

/-- The direct-sum smooth atlas retains the original two atlases and original product fibers. -/
def sum : SmoothComplexBundleAtlas (n := n) (E ×ᵇ F) := by
  classical
  let c (i : A.Index) (j : B.Index) :
      ((Fin (A.rank i) → ℂ) × (Fin (B.rank j) → ℂ)) ≃L[ℂ]
        (Fin (A.rank i + B.rank j) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank i)) (Fin (B.rank j)) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank i + B.rank j) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  refine { Index := A.Index × B.Index
           rank := fun i ↦ A.rank i.1 + B.rank i.2
           chart := fun i ↦ A.sumChart B i.1 i.2
           covers := ?_
           linear := ?_
           contMDiffOn_coordChange := ?_ }
  · intro x
    obtain ⟨i, hi⟩ := A.covers x
    obtain ⟨j, hj⟩ := B.covers x
    exact ⟨⟨i, j⟩, hi, hj⟩
  · rintro ⟨i, j⟩ x hx
    constructor
    · intro v w
      change c i j ((A.chart i ⟨x, v.1 + w.1⟩).2, (B.chart j ⟨x, v.2 + w.2⟩).2) =
        c i j ((A.chart i ⟨x, v.1⟩).2, (B.chart j ⟨x, v.2⟩).2) +
          c i j ((A.chart i ⟨x, w.1⟩).2, (B.chart j ⟨x, w.2⟩).2)
      rw [(A.linear i x hx.1).map_add, (B.linear j x hx.2).map_add]
      exact (c i j).map_add
        ((A.chart i ⟨x, v.1⟩).2, (B.chart j ⟨x, v.2⟩).2)
        ((A.chart i ⟨x, w.1⟩).2, (B.chart j ⟨x, w.2⟩).2)
    · intro t v
      change c i j ((A.chart i ⟨x, t • v.1⟩).2, (B.chart j ⟨x, t • v.2⟩).2) =
        t • c i j ((A.chart i ⟨x, v.1⟩).2, (B.chart j ⟨x, v.2⟩).2)
      rw [(A.linear i x hx.1).map_smul, (B.linear j x hx.2).map_smul]
      exact (c i j).map_smul t ((A.chart i ⟨x, v.1⟩).2, (B.chart j ⟨x, v.2⟩).2)
  · rintro ⟨i, j⟩ ⟨k, l⟩ a
    let v := (c i j).symm (Pi.single a 1)
    let U := ((A.chart i).baseSet ∩ (B.chart j).baseSet) ∩
      ((A.chart k).baseSet ∩ (B.chart l).baseSet)
    let pE (x : M) := ∑ b, v.1 b •
      (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2
    let pF (x : M) := ∑ b, v.2 b •
      (B.chart l ((B.chart j).toPartialEquiv.symm (x, Pi.single b 1))).2
    have hE : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Fin (A.rank k) → ℂ) ∞ pE U := by
      apply contMDiffOn_finsetSum
      intro b _
      apply ((v.1 b • ContinuousLinearMap.id ℂ (Fin (A.rank k) → ℂ)).restrictScalars ℝ)
        |>.contMDiff.comp_contMDiffOn
      exact (A.contMDiffOn_coordChange i k b).mono (fun _ hx ↦ ⟨hx.1.1, hx.2.1⟩)
    have hF : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Fin (B.rank l) → ℂ) ∞ pF U := by
      apply contMDiffOn_finsetSum
      intro b _
      apply ((v.2 b • ContinuousLinearMap.id ℂ (Fin (B.rank l) → ℂ)).restrictScalars ℝ)
        |>.contMDiff.comp_contMDiffOn
      exact (B.contMDiffOn_coordChange j l b).mono (fun _ hx ↦ ⟨hx.1.2, hx.2.2⟩)
    have hs := (c k l).toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
      (hE.prodMk_space hF)
    apply hs.congr
    intro x hx
    have hvalueE :
        (A.chart k ⟨x, (A.frameLinearEquiv i x hx.1.1).symm v.1⟩).2 = pE x := by
      let L := (A.frameLinearEquiv k x hx.2.1).toLinearMap.comp
        (A.frameLinearEquiv i x hx.1.1).symm.toLinearMap
      have hb := congrArg L ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr v.1)
      have hcol (b : Fin (A.rank i)) : L (Pi.single b 1) =
          (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2 := by
        exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart k z).2)
          (TotalSpace.mk_cast (F := Unit) (E := E)
            ((A.chart i).proj_symm_apply' (x := Pi.single b 1) hx.1.1) _)
      change L v.1 = ∑ b, v.1 b •
        (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2
      simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, hcol] using hb.symm
    have hvalueF :
        (B.chart l ⟨x, (B.frameLinearEquiv j x hx.1.2).symm v.2⟩).2 = pF x := by
      let L := (B.frameLinearEquiv l x hx.2.2).toLinearMap.comp
        (B.frameLinearEquiv j x hx.1.2).symm.toLinearMap
      have hb := congrArg L ((Pi.basisFun ℂ (Fin (B.rank j))).sum_repr v.2)
      have hcol (b : Fin (B.rank j)) : L (Pi.single b 1) =
          (B.chart l ((B.chart j).toPartialEquiv.symm (x, Pi.single b 1))).2 := by
        exact congrArg (fun z : TotalSpace Unit F ↦ (B.chart l z).2)
          (TotalSpace.mk_cast (F := Unit) (E := F)
            ((B.chart j).proj_symm_apply' (x := Pi.single b 1) hx.1.2) _)
      change L v.2 = ∑ b, v.2 b •
        (B.chart l ((B.chart j).toPartialEquiv.symm (x, Pi.single b 1))).2
      simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, hcol] using hb.symm
    change c k l
      ((A.chart k ⟨x, if hx : x ∈ (A.chart i).baseSet then
          (A.frameLinearEquiv i x hx).symm v.1 else 0⟩).2,
        (B.chart l ⟨x, if hx : x ∈ (B.chart j).baseSet then
          (B.frameLinearEquiv j x hx).symm v.2 else 0⟩).2) = c k l (pE x, pF x)
    rw [dite_eq_left hx.1.1, dite_eq_left hx.1.2, hvalueE, hvalueF]

/-- Inclusion of the first original smooth summand is smooth in the specified sum atlas. -/
theorem isSmoothAtlasBundleMap_inl :
    IsSmoothAtlasBundleMap A (A.sum B) (fun x ↦ LinearMap.inl ℂ (E x) (F x)) := by
  classical
  refine ⟨contMDiff_id, ?_⟩
  rintro i ⟨j, k⟩ a
  let c : ((Fin (A.rank j) → ℂ) × (Fin (B.rank k) → ℂ)) ≃L[ℂ]
      (Fin (A.rank j + B.rank k) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank j)) (Fin (B.rank k)) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank j + B.rank k) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  have hs := c.toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
    (((A.contMDiffOn_coordChange i j a).mono
      (fun (x : M) (hx : x ∈ (A.chart i).baseSet ∩
          ((A.chart j).baseSet ∩ (B.chart k).baseSet)) ↦ ⟨hx.1, hx.2.1⟩)).prodMk_space
        (contMDiffOn_const (c := (0 : Fin (B.rank k) → ℂ))))
  apply hs.congr
  intro x hx
  rw [dite_eq_left hx.1]
  change c ((A.chart j ⟨x, (A.frameLinearEquiv i x hx.1).symm (Pi.single a 1)⟩).2,
    (B.chart k ⟨x, 0⟩).2) =
      c ((A.chart j ((A.chart i).toPartialEquiv.symm (x, Pi.single a 1))).2, 0)
  have hpoint := TotalSpace.mk_cast (F := Unit) (E := E)
    ((A.chart i).proj_symm_apply' (x := Pi.single a 1) hx.1)
    ((A.chart i).toPartialEquiv.symm (x, Pi.single a 1)).2
  have hzero : (B.chart k ⟨x, (0 : F x)⟩).2 = 0 :=
    (B.frameLinearEquiv k x hx.2.2).map_zero
  exact congrArg c (Prod.ext
    (congrArg (fun z : TotalSpace Unit E ↦ (A.chart j z).2) hpoint) hzero)

/-- Projection onto the first original smooth summand is smooth in the specified sum atlas. -/
theorem isSmoothAtlasBundleMap_fst :
    IsSmoothAtlasBundleMap (A.sum B) A (fun x ↦ LinearMap.fst ℂ (E x) (F x)) := by
  classical
  refine ⟨contMDiff_id, ?_⟩
  rintro ⟨i, j⟩ k a
  let c : ((Fin (A.rank i) → ℂ) × (Fin (B.rank j) → ℂ)) ≃L[ℂ]
      (Fin (A.rank i + B.rank j) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank i)) (Fin (B.rank j)) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank i + B.rank j) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  let v := (c.symm (Pi.single a 1)).1
  have hs : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, Fin (A.rank k) → ℂ) ∞
      (fun x : M ↦ ∑ b, v b •
        (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2)
      (((A.chart i).baseSet ∩ (B.chart j).baseSet) ∩ (A.chart k).baseSet) := by
    apply contMDiffOn_finsetSum
    intro b _
    apply ((v b • ContinuousLinearMap.id ℂ (Fin (A.rank k) → ℂ)).restrictScalars ℝ)
      |>.contMDiff.comp_contMDiffOn
    exact (A.contMDiffOn_coordChange i k b).mono (fun _ hx ↦ ⟨hx.1.1, hx.2⟩)
  apply hs.congr
  intro x hx
  have hbase : x ∈ ((A.sum B).chart ⟨i, j⟩).baseSet := hx.1
  rw [dite_eq_left hbase]
  have hinverse : ((A.sum B).frameLinearEquiv ⟨i, j⟩ x hbase).symm (Pi.single a 1) =
      ((A.frameLinearEquiv i x hx.1.1).symm (c.symm (Pi.single a 1)).1,
        (B.frameLinearEquiv j x hx.1.2).symm (c.symm (Pi.single a 1)).2) := by
    apply ((A.sum B).frameLinearEquiv ⟨i, j⟩ x hbase).injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single a 1 = c
      ((A.frameLinearEquiv i x hx.1.1)
        ((A.frameLinearEquiv i x hx.1.1).symm (c.symm (Pi.single a 1)).1),
      (B.frameLinearEquiv j x hx.1.2)
        ((B.frameLinearEquiv j x hx.1.2).symm (c.symm (Pi.single a 1)).2))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact (c.apply_symm_apply _).symm
  change (A.chart k ⟨x, (((A.sum B).frameLinearEquiv ⟨i, j⟩ x hbase).symm
    (Pi.single a 1)).1⟩).2 = _
  rw [hinverse]
  let L := (A.frameLinearEquiv k x hx.2).toLinearMap.comp
    (A.frameLinearEquiv i x hx.1.1).symm.toLinearMap
  have hb := congrArg L ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr v)
  have hcol (b : Fin (A.rank i)) : L (Pi.single b 1) =
      (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2 := by
    exact congrArg (fun z : TotalSpace Unit E ↦ (A.chart k z).2)
      (TotalSpace.mk_cast (F := Unit) (E := E)
        ((A.chart i).proj_symm_apply' (x := Pi.single b 1) hx.1.1) _)
  change L v = ∑ b, v b •
    (A.chart k ((A.chart i).toPartialEquiv.symm (x, Pi.single b 1))).2
  simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, hcol] using hb.symm

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

/-- The direct sum of the specified smooth actions is smooth in the same direct-sum atlas. -/
theorem isSmoothAtlas_sum (σ : EquivariantStructure G E) (τ : EquivariantStructure G F)
    (hσ : σ.IsSmoothAtlas IG A) (hτ : τ.IsSmoothAtlas IG B) :
    (σ.sum τ).IsSmoothAtlas IG (A.sum B) := by
  classical
  let c (i : A.Index) (j : B.Index) :
      ((Fin (A.rank i) → ℂ) × (Fin (B.rank j) → ℂ)) ≃L[ℂ]
        (Fin (A.rank i + B.rank j) → ℂ) :=
    ((LinearEquiv.sumArrowLequivProdArrow (Fin (A.rank i)) (Fin (B.rank j)) ℂ ℂ).symm.trans
      (LinearEquiv.piCongrLeft ℂ (fun _ : Fin (A.rank i + B.rank j) ↦ ℂ)
        finSumFinEquiv)).toContinuousLinearEquiv
  rintro ⟨i, j⟩ ⟨k, l⟩ a
  let v := (c i j).symm (Pi.single a 1)
  let U := {p : G × M | p.2 ∈ ((A.chart i).baseSet ∩ (B.chart j).baseSet) ∧
    p.1 • p.2 ∈ ((A.chart k).baseSet ∩ (B.chart l).baseSet)}
  let pE (p : G × M) := ∑ b, v.1 b •
    (if hx : p.2 ∈ (A.chart i).baseSet then
      (A.chart k ⟨p.1 • p.2, σ.linearMap p.1 p.2
        ((A.frameLinearEquiv i p.2 hx).symm (Pi.single b 1))⟩).2 else 0)
  let pF (p : G × M) := ∑ b, v.2 b •
    (if hx : p.2 ∈ (B.chart j).baseSet then
      (B.chart l ⟨p.1 • p.2, τ.linearMap p.1 p.2
        ((B.frameLinearEquiv j p.2 hx).symm (Pi.single b 1))⟩).2 else 0)
  have hE : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, Fin (A.rank k) → ℂ) ∞ pE U := by
    apply contMDiffOn_finsetSum
    intro b _
    apply ((v.1 b • ContinuousLinearMap.id ℂ (Fin (A.rank k) → ℂ)).restrictScalars ℝ)
      |>.contMDiff.comp_contMDiffOn
    exact (hσ i k b).mono (fun _ hx ↦ ⟨hx.1.1, hx.2.1⟩)
  have hF : ContMDiffOn (IG.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      𝓘(ℝ, Fin (B.rank l) → ℂ) ∞ pF U := by
    apply contMDiffOn_finsetSum
    intro b _
    apply ((v.2 b • ContinuousLinearMap.id ℂ (Fin (B.rank l) → ℂ)).restrictScalars ℝ)
      |>.contMDiff.comp_contMDiffOn
    exact (hτ j l b).mono (fun _ hx ↦ ⟨hx.1.2, hx.2.2⟩)
  have hs := (c k l).toContinuousLinearMap.restrictScalars ℝ |>.contMDiff.comp_contMDiffOn
    (hE.prodMk_space hF)
  apply hs.congr
  intro p hp
  have hbase : p.2 ∈ ((A.sum B).chart ⟨i, j⟩).baseSet := hp.1
  rw [dite_eq_left hbase]
  have hinverse : ((A.sum B).frameLinearEquiv ⟨i, j⟩ p.2 hbase).symm (Pi.single a 1) =
      ((A.frameLinearEquiv i p.2 hp.1.1).symm v.1,
        (B.frameLinearEquiv j p.2 hp.1.2).symm v.2) := by
    apply ((A.sum B).frameLinearEquiv ⟨i, j⟩ p.2 hbase).injective
    rw [LinearEquiv.apply_symm_apply]
    change Pi.single a 1 = c i j
      ((A.frameLinearEquiv i p.2 hp.1.1) ((A.frameLinearEquiv i p.2 hp.1.1).symm v.1),
        (B.frameLinearEquiv j p.2 hp.1.2) ((B.frameLinearEquiv j p.2 hp.1.2).symm v.2))
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact ((c i j).apply_symm_apply _).symm
  change c k l
    ((A.chart k ⟨p.1 • p.2, σ.linearMap p.1 p.2
      (((A.sum B).frameLinearEquiv ⟨i, j⟩ p.2 hbase).symm (Pi.single a 1)).1⟩).2,
    (B.chart l ⟨p.1 • p.2, τ.linearMap p.1 p.2
      (((A.sum B).frameLinearEquiv ⟨i, j⟩ p.2 hbase).symm (Pi.single a 1)).2⟩).2) =
      c k l (pE p, pF p)
  rw [hinverse]
  apply congrArg (c k l)
  apply Prod.ext
  · let L := (A.frameLinearEquiv k (p.1 • p.2) hp.2.1).toLinearMap.comp
      ((σ.linearMap p.1 p.2).comp (A.frameLinearEquiv i p.2 hp.1.1).symm.toLinearMap)
    have hb := congrArg L ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr v.1)
    change L v.1 = pE p
    simp only [pE, dite_eq_left hp.1.1]
    change L v.1 = ∑ b, v.1 b • L (Pi.single b 1)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using hb.symm
  · let L := (B.frameLinearEquiv l (p.1 • p.2) hp.2.2).toLinearMap.comp
      ((τ.linearMap p.1 p.2).comp (B.frameLinearEquiv j p.2 hp.1.2).symm.toLinearMap)
    have hb := congrArg L ((Pi.basisFun ℂ (Fin (B.rank j))).sum_repr v.2)
    change L v.2 = pF p
    simp only [pF, dite_eq_left hp.1.2]
    change L v.2 = ∑ b, v.2 b • L (Pi.single b 1)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply] using hb.symm

end AtiyahSinger.SmoothComplexBundleAtlas
