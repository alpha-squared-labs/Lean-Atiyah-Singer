/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSupportedSobolevReconstruction
public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AssociatedTensorLocalFiberSobolev
public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization
public import AtiyahSinger.Analysis.NativeAtlasSobolev
public import AtiyahSinger.Analysis.SmoothSectionFamilyL2Coordinates
public import AtiyahSinger.Geometry.AtlasPresentationChartCutoff
public import AtiyahSinger.Analysis.EquivariantAtlasOperator
public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.SmoothSectionSobolevFamily

import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Return bounds for the actual supported associated tensor section

Public module ID: M0193.

The original base cutoff equals one on the support of the section. The original
sphere partition then reconstructs that same section through compatible product
charts. Finite row reassembly, exact Fubini coordinates, and the inverse of the
specified sphere metric equivalence give a uniform local-to-global H⁰ bound.

The section itself, its whole-fiber coordinate family, and its original support
are retained. The result is a bounded return estimate and makes no compactness
claim for an identity operator tensored with a fiber smoothing operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [T2Space B]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D" => AssociatedEquivariantFiber (E := F.Fiber) S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3600000 in
-- Normalize the same supported global section and its original whole-fiber norms.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Original whole-fiber norms control the same global section supported in a base plateau. -/
theorem exists_associatedSphereTensorLocalizedFiber_return_bound
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1)
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν] :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    ∀ G₀ : AtlasBundlePresentation AT,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
        (∀ z, w.val z ≠ 0 → πS z ∈ c.symm '' {x | input.cutoff x = 1}) →
        ∃ u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber,
          (∀ (z : Xp) (i : Fin a), u z i = nativeSmoothSectionLinearEquiv F.Fiber
            ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
              associatedSphereTensorLocalFiberCoordinates S E A b input.frame
                input.frame_mem_atlas i
                (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
          (∀ (s : ℝ) (i : Fin a),
            MemLp (fun z ↦ L.smoothToSobolev s (u z i)) 2 (volume : Measure Xp)) ∧
          ∃ hu : ∀ i : Fin a,
              MemLp (fun z ↦ k.smoothToL2 ν (u z i)) 2 (volume : Measure Xp),
            ‖G₀.smoothToSobolev 0 w‖ ≤
              C * ∑ i : Fin a, ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ := by
  classical
  -- Use the same localized whole-fiber family and its Sobolev membership.
  have hfamilies := exists_associatedSphereTensorLocalizedFiber_sobolev (a := a)
    S E F σ hσ b input hc hinput χ hχ hχsupport hχone L k ν
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let Yc := EuclideanSpace ℝ (Fin r)
  let XY := EuclideanSpace ℝ (Fin (n + r))
  let V := EuclideanSpace ℂ (Fin (a * F.rank))
  let W := EuclideanSpace ℂ (Fin F.rank)
  let K (j : Fin L.size) := L.toAtlasBundlePresentation.chartCutoff j
  let Bcut (j : Fin L.size) :=
    associatedSphereTensorChartCutoff S E A σ hA b c input hinput (L.chart j) (K j)
  dsimp only
  intro G₀
  change AtlasBundlePresentation AT at G₀
  -- Keep the original sphere partition and all its compatible associated product charts.
  let CP (j : Fin L.size) := associatedSphereProductChart S b c (L.chart j)
  have hCP (j : Fin L.size) : CP j ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc (L.chart j) (L.chart_mem_atlas j)
  have hlocal (j : Fin L.size) : ∃ I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, V),
      ∀ w z, I w z = (Bcut j).localizedFunction w z := by
    have hd := AtlasChartCutoff.exists_localize_sobolev_of_mem_maximalAtlas
      (Bcut j) (hCP j) G₀ 0
    exact ⟨hd.choose, hd.choose_spec.1⟩
  choose I hI using hlocal
  have hreverseData := exists_sobolev_bound_of_supported_partition CP hCP Bcut G₀ 0
  let Creverse : ℝ := hreverseData.choose
  have hCreverse := hreverseData.choose_spec.1
  have hreverse := hreverseData.choose_spec.2
  let row (i : Fin a) : V →L[ℂ] W := LinearMap.toContinuousLinearMap {
    toFun v := WithLp.toLp 2 (fun j ↦ v (finProdFinEquiv (i, j)))
    map_add' v w := by ext j; rfl
    map_smul' z v := by ext j; rfl }
  let q :=
    ((EuclideanSpace.equiv (Fin n) ℝ).symm.prodCongr (ContinuousLinearEquiv.refl ℝ Yc)).trans
      e.symm
  have he : MeasurePreserving e := by
    exact (WithLp.volume_preserving_ofLp X Yc).comp
      ((LinearIsometryEquiv.measurePreserving
        (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin n ⊕ Fin r ↦ ℝ))).comp
        (LinearIsometryEquiv.measurePreserving
          (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ finSumFinEquiv.symm)))
  have he' : MeasurePreserving e.toHomeomorph.toMeasurableEquiv
      (volume : Measure XY) ((volume : Measure X).prod (volume : Measure Yc)) := he
  have hq : MeasurePreserving q ((volume : Measure Xp).prod volume) volume :=
    he'.symm.comp
      ((PiLp.volume_preserving_toLp (Fin n)).prod (MeasurePreserving.id volume))
  let : Measure.IsAddHaarMeasure ((volume : Measure Xp).prod (volume : Measure Yc)) :=
    Measure.prod.instIsAddHaarMeasure _ _
  let f (w : AT.smoothSections) (i : Fin a) (j : Fin L.size) : 𝓢(Xp × Yc, W) :=
    SchwartzMap.postcompCLM (row i) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ q (I j w))
  let col (i : Fin a) : W →L[ℂ] V := LinearMap.toContinuousLinearMap {
    toFun v := WithLp.toLp 2 (fun l ↦
      if (finProdFinEquiv.symm l).1 = i then v (finProdFinEquiv.symm l).2 else 0)
    map_add' v w := by
      ext l
      simp only [V, W, WithLp.ofLp_add, Pi.add_apply]
      split_ifs <;> simp
    map_smul' z v := by
      ext l
      simp only [V, W, WithLp.ofLp_smul, Pi.smul_apply]
      split_ifs <;> simp }
  have hnormMap (v : 𝓢(XY, V)) :
      ‖v.toLp 2‖ ≤ ∑ i : Fin a,
        ‖col i‖ * ‖(SchwartzMap.postcompCLM (row i)
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ q v)).toLp 2
            ((volume : Measure Xp).prod volume)‖ := by
    let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ q v
    let vrow (i : Fin a) := SchwartzMap.postcompCLM (row i) g
    have hg : g.toLp 2 ((volume : Measure Xp).prod volume) =
        Lp.compMeasurePreserving q hq (v.toLp 2) := by
      apply Lp.ext
      have hiq := hq.quasiMeasurePreserving.ae (v.coeFn_toLp 2 volume)
      filter_upwards [g.coeFn_toLp 2 ((volume : Measure Xp).prod volume),
        Lp.coeFn_compMeasurePreserving (v.toLp 2) hq, hiq] with p hp ht hi
      exact hp.trans (hi.symm.trans ht.symm)
    have hreassemble : g = ∑ i : Fin a, SchwartzMap.postcompCLM (col i) (vrow i) := by
      apply SchwartzMap.ext
      intro p
      apply PiLp.ext
      intro l
      simp only [sum_apply, V, W, WithLp.ofLp_sum, Finset.sum_apply]
      change v (q p) l = ∑ i : Fin a,
        if (finProdFinEquiv.symm l).1 = i then
          v (q p) (finProdFinEquiv (i, (finProdFinEquiv.symm l).2)) else 0
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      rw [finProdFinEquiv.apply_symm_apply]
    have hpost (i : Fin a) :
        (SchwartzMap.postcompCLM (col i) (vrow i)).toLp 2
            ((volume : Measure Xp).prod volume) =
          (col i).compLp ((vrow i).toLp 2 ((volume : Measure Xp).prod volume)) := by
      apply Lp.ext
      filter_upwards [(SchwartzMap.postcompCLM (col i) (vrow i)).coeFn_toLp 2
          ((volume : Measure Xp).prod volume),
        (col i).coeFn_compLp ((vrow i).toLp 2 ((volume : Measure Xp).prod volume)),
        (vrow i).coeFn_toLp 2 ((volume : Measure Xp).prod volume)] with p hp hc hf
      exact hp.trans ((congrArg (col i) hf.symm).trans hc.symm)
    let toLp : 𝓢(Xp × Yc, V) →L[ℂ] Lp V 2 ((volume : Measure Xp).prod volume) :=
      SchwartzMap.toLpCLM ℂ V 2 ((volume : Measure Xp).prod volume)
    have hsum : g.toLp 2 ((volume : Measure Xp).prod volume) =
        ∑ i : Fin a, (col i).compLp ((vrow i).toLp 2 ((volume : Measure Xp).prod volume)) := by
      have hmap := congrArg toLp hreassemble
      exact hmap.trans ((map_sum toLp
        (fun i ↦ SchwartzMap.postcompCLM (col i) (vrow i)) Finset.univ).trans
          (Finset.sum_congr rfl (fun i _ ↦ hpost i)))
    have hnorm : ‖v.toLp 2‖ = ‖g.toLp 2 ((volume : Measure Xp).prod volume)‖ := by
      have hn := congrArg norm hg
      rw [Lp.norm_compMeasurePreserving] at hn
      exact hn.symm
    have htriangle := norm_sum_le Finset.univ
      (fun i : Fin a ↦ (col i).compLp
        ((vrow i).toLp 2 ((volume : Measure Xp).prod volume)))
    have hterms := Finset.sum_le_sum (s := Finset.univ) fun (i : Fin a) _ ↦
      (col i).norm_compLp_le ((vrow i).toLp 2 ((volume : Measure Xp).prod volume))
    exact hnorm.trans_le ((congrArg norm hsum).trans_le (htriangle.trans hterms))
  have hzero (v : 𝓢(XY, V)) : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
    simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
  have hNative (j : Fin L.size) (v : A.smoothSections) (y : Yc) :
      (K j).localize (L.chart_mem_atlas j) v y =
        L.localize j (nativeSmoothSectionLinearEquiv F.Fiber v) y := by
    change (if y ∈ (L.chart j).target then
      (((if y ∈ (L.chart j).target then L.cutoff j ((L.chart j).symm y) else 0) : ℝ) : ℂ) •
        (EuclideanSpace.equiv (Fin F.rank) ℂ).symm
          ((EuclideanSpace.equiv (Fin F.rank) ℂ)
            (L.frame j ⟨(L.chart j).symm y, v.val ((L.chart j).symm y)⟩).2) else 0) =
      (if y ∈ (L.chart j).target then
        (L.cutoff j ((L.chart j).symm y) : ℂ) •
          (L.frame j ⟨(L.chart j).symm y, v.val ((L.chart j).symm y)⟩).2 else 0)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    by_cases hy : y ∈ (L.chart j).target
    · simp only [ite_eq_left hy]
    · simp only [ite_eq_right hy]
  let eMetric : L.SobolevSpace 0 ≃L[ℂ] k.L2SectionSpace ν :=
    k.sobolevZeroEquivL2 (μ := ν) L
  let Ccol : ℝ := ∑ i : Fin a, ‖col i‖
  have hCcol : 0 ≤ Ccol := Finset.sum_nonneg fun i _ ↦ norm_nonneg (col i)
  let Cmetric := ‖eMetric.symm.toContinuousLinearMap‖
  refine ⟨Creverse * (L.size * Ccol * Cmetric),
    mul_nonneg hCreverse (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCcol)
      (norm_nonneg _)), ?_⟩
  intro w hw
  change AT.smoothSections at w
  let u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
    (hfamilies w).choose
  have hu := (hfamilies w).choose_spec.1
  have hs := (hfamilies w).choose_spec.2.2.1
  have hm := (hfamilies w).choose_spec.2.2.2
  have hcoords (i : Fin a) (j : Fin L.size) (x : Xp) (y : Yc) :
      f w i j (x, y) = L.localize j (u x i) y := by
    apply PiLp.ext
    intro l
    change I j w (e.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x, y))
      (finProdFinEquiv (i, l)) = _
    rw [hI]
    have h := associatedSphereTensorChartCutoff_localizedFunction (a := a)
      S E A σ hA b c input hinput (L.chart j) (L.chart_mem_atlas j) (K j)
      w ((EuclideanSpace.equiv (Fin n) ℝ).symm x) y i l
    refine h.trans ?_
    have hn := hNative j
      ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
        associatedSphereTensorLocalFiberCoordinates S E A b input.frame
          input.frame_mem_atlas i
          (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
          (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))) y
    exact (congrArg (fun v : W ↦ v l) hn).trans
      (congrArg (fun v ↦ L.localize j v y l) (hu x i).symm)
  -- On the original section support the base plateau is one, so the sphere partition suffices.
  have hpartition (z : Z) (hz : w.val z ≠ 0) :
      (∑ j, if z ∈ (CP j).source then (Bcut j).cutoff (CP j z) else 0) = 1 := by
    obtain ⟨x, hx, hxz⟩ := hw z hz
    change input.cutoff x = 1 at hx
    have hxt : x ∈ tsupport input.cutoff := by
      apply subset_tsupport
      change input.cutoff x ≠ 0
      rw [hx]
      exact one_ne_zero
    have hxc : x ∈ c.target := (input.support_subset hxt).1
    have hbase : πS z ∈ (S.trivialization b).baseSet := hinput ⟨x, hxt, hxz⟩
    let t := associatedSphereTrivialization S b
    have htbase : t.baseSet = (S.trivialization b).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.1
    have hzt : z ∈ t.source := t.mem_source.mpr (htbase.symm ▸ hbase)
    have htproj : (t z).1 = c.symm x := (t.proj_toFun z hzt).trans hxz.symm
    have hweight (j : Fin L.size) :
        (if z ∈ (CP j).source then (Bcut j).cutoff (CP j z) else 0) =
          L.cutoff j (t z).2 := by
      have hsource : z ∈ (CP j).source ↔ (t z).2 ∈ (L.chart j).source := by
        constructor
        · intro h
          exact h.1.2.2
        · intro hy
          refine ⟨⟨hzt, ?_, hy⟩, Set.mem_univ _⟩
          change (t z).1 ∈ c.source
          rw [htproj]
          exact c.map_target hxc
      rw [hsource]
      have hcoord : e (CP j z) = (c (t z).1, L.chart j (t z).2) :=
        e.apply_symm_apply _
      change (if (t z).2 ∈ (L.chart j).source then
        input.cutoff (e (CP j z)).1 * (K j).cutoff (e (CP j z)).2 else 0) = _
      rw [hcoord, htproj, c.right_inv hxc, hx, one_mul]
      exact L.toAtlasBundlePresentation.chartCutoff_pullback j (t z).2
    rw [Finset.sum_congr rfl (fun j _ ↦ hweight j)]
    exact L.sum_cutoff (t z).2
  have hglobal : ‖G₀.smoothToSobolev 0 w‖ ≤
      Creverse * ∑ j : Fin L.size, ‖(I j w).toLp 2‖ := by
    have hb : ‖G₀.smoothToSobolev 0 w‖ ≤
        Creverse * ∑ j : Fin L.size, ‖schwartzSobolevCoordinate 0 (I j w)‖ :=
      hreverse w (fun j ↦ I j w) (hI · w) hpartition
    have heq : (∑ j : Fin L.size, ‖schwartzSobolevCoordinate 0 (I j w)‖) =
        ∑ j : Fin L.size, ‖(I j w).toLp 2‖ :=
      Finset.sum_congr rfl (fun j _ ↦ congrArg norm (hzero (I j w)))
    exact hb.trans_eq (congrArg (Creverse * ·) heq)
  let g (i : Fin a) := (hs 0 i).2.toLp (fun z ↦ L.smoothToSobolev 0 (u z i))
  have hrow (i : Fin a) (j : Fin L.size) :
      ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖ ≤ ‖g i‖ := by
    have hsq := L.norm_sobolevZero_family_sq (fun x ↦ u x i) (hs 0 i).2
      (f w i) (hcoords i)
    have hone := Finset.single_le_sum
      (f := fun j : Fin L.size ↦ ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖ ^ 2)
      (fun j _ ↦ sq_nonneg _) (Finset.mem_univ j)
    change ‖g i‖ ^ 2 = _ at hsq
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hone.trans_eq hsq.symm)
  have hmetric (i : Fin a) : g i =
      eMetric.symm.toContinuousLinearMap.compLp
        ((hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))) := by
    apply Lp.ext
    filter_upwards [(hs 0 i).2.coeFn_toLp,
      eMetric.symm.toContinuousLinearMap.coeFn_compLp
        ((hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))),
      (hm i).coeFn_toLp] with z hgz hez hmz
    have hsmooth := k.sobolevZeroEquivL2_smooth (μ := ν) L (u z i)
    have hi : eMetric.symm (k.smoothToL2 ν (u z i)) = L.smoothToSobolev 0 (u z i) :=
      (congrArg eMetric.symm hsmooth.symm).trans (eMetric.symm_apply_apply _)
    exact hgz.trans (hi.symm.trans
      ((congrArg eMetric.symm hmz.symm).trans hez.symm))
  have hbmetric (i : Fin a) : ‖g i‖ ≤
      Cmetric * ‖(hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ := by
    rw [hmetric]
    exact eMetric.symm.toContinuousLinearMap.norm_compLp_le _
  let total : ℝ := ∑ i : Fin a, ‖(hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖
  have hterm (j : Fin L.size) : ‖(I j w).toLp 2‖ ≤ Ccol * Cmetric * total := by
    apply (hnormMap (I j w)).trans
    calc
      (∑ i : Fin a, ‖col i‖ * ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖) ≤
          ∑ i : Fin a, ‖col i‖ * (Cmetric * total) := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg (col i))
        apply (hrow i j).trans ((hbmetric i).trans _)
        have hsingle : ‖(hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ ≤ total :=
          Finset.single_le_sum
            (f := fun l : Fin a ↦ ‖(hm l).toLp (fun z ↦ k.smoothToL2 ν (u z l))‖)
            (fun l _ ↦ norm_nonneg ((hm l).toLp (fun z ↦ k.smoothToL2 ν (u z l))))
            (Finset.mem_univ i)
        exact mul_le_mul_of_nonneg_left hsingle (norm_nonneg _)
      _ = Ccol * Cmetric * total := by rw [← Finset.sum_mul, mul_assoc]
  -- A finite scalar estimate combines the uniform chart bounds.
  have hfinite (m : ℕ) (f : Fin m → ℝ) (c₁ c₂ c₃ c₄ : ℝ)
      (hc₄ : 0 ≤ c₄) (hf : ∀ j : Fin m, f j ≤ c₁ * c₂ * c₃) :
      c₄ * (∑ j : Fin m, f j) ≤ c₄ * (m * c₁ * c₂) * c₃ := by
    have hsum : (∑ j : Fin m, f j) ≤ ∑ _j : Fin m, c₁ * c₂ * c₃ :=
      Finset.sum_le_sum (fun j _ ↦ hf j)
    have hbound := mul_le_mul_of_nonneg_left hsum hc₄
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_assoc] using hbound
  refine ⟨u, hu, fun s i ↦ (hs s i).2, hm, ?_⟩
  exact hglobal.trans (hfinite L.size
    (fun j ↦ ‖(I j w).toLp 2 (volume : Measure XY)‖)
    Ccol Cmetric total Creverse hCreverse hterm)

end AtiyahSinger
