/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

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
# Global norm control of the original compact whole-fiber families

Public module ID: M0184.

The specified base cutoff and original whole-sphere coordinates give native
fiber families bounded by the original associated finite-atlas Sobolev-zero
norm. The proof uses the original sphere partition, exact product chart values,
volume-preserving coordinate concatenation and Fubini. The sphere metric is
retained through its actual Sobolev-zero equivalence. No separated expansion or
replacement global norm is used.
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
set_option maxHeartbeats 900000 in
-- Normalize the compact fiber families in the original global H⁰ norm.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual compact fiber families have a uniform bound in the original global H⁰ norm. -/
theorem exists_associatedSphereTensorLocalizedFiber_l2_bound
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
            ∀ i : Fin a, ‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ ≤
              C * ‖G₀.smoothToSobolev 0 w‖ := by
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
  -- The original sphere partition supplies fixed compatible associated chart maps.
  have hlocal (j : Fin L.size) : ∃ I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, V),
      (∀ w z, I w z = (Bcut j).localizedFunction w z) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
          ‖schwartzSobolevCoordinate 0 (I w)‖ ≤ C * ‖G₀.smoothToSobolev 0 w‖ :=
    AtlasChartCutoff.exists_localize_sobolev_of_mem_maximalAtlas (Bcut j)
      (associatedSphereProductChart_mem_maximalAtlas S b c hc (L.chart j)
        (L.chart_mem_atlas j)) G₀ 0
  choose I hI cI hcI hbI using hlocal
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
  have hnormMap (v : 𝓢(XY, V)) (R : V →L[ℂ] W) :
      ‖(SchwartzMap.postcompCLM R
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ q v)).toLp 2
          ((volume : Measure Xp).prod volume)‖ ≤ ‖R‖ * ‖v.toLp 2‖ := by
    let t := Lp.compMeasurePreserving q hq (v.toLp 2)
    let v' := SchwartzMap.postcompCLM R (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ q v)
    have hrep : v'.toLp 2 ((volume : Measure Xp).prod volume) = R.compLp t := by
      apply Lp.ext
      have hv : ∀ᵐ z ∂(volume : Measure XY), (v.toLp 2 volume) z = v z :=
        v.coeFn_toLp 2 volume
      have hvq : ∀ᵐ p ∂((volume : Measure Xp).prod volume),
          (v.toLp 2 volume) (q p) = v (q p) := hq.quasiMeasurePreserving.ae hv
      filter_upwards [v'.coeFn_toLp 2 ((volume : Measure Xp).prod volume),
        R.coeFn_compLp t, Lp.coeFn_compMeasurePreserving (v.toLp 2) hq,
        hvq] with p hp hr ht hi
      rw [hp, hr, ht]
      change R (v (q p)) = R ((v.toLp 2 volume) (q p))
      exact congrArg R hi.symm
    change ‖v'.toLp 2 ((volume : Measure Xp).prod volume)‖ ≤ _
    rw [hrep]
    have hb : ‖R.compLp t‖ ≤ ‖R‖ * ‖t‖ := R.norm_compLp_le t
    simpa only [t, Lp.norm_compMeasurePreserving] using hb
  have hzero (v : 𝓢(XY, V)) : schwartzSobolevCoordinate 0 v = v.toLp 2 := by
    simp only [schwartzSobolevCoordinate, zero_div, Real.rpow_zero,
      SchwartzMap.fourierMultiplierCLM_const, one_smul, ContinuousLinearMap.id_apply]
  have hnorm (w : AT.smoothSections) (i : Fin a) (j : Fin L.size) :
      ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖ ≤
        ‖row i‖ * cI j * ‖G₀.smoothToSobolev 0 w‖ := by
    have heq : ‖(I j w).toLp 2‖ = ‖schwartzSobolevCoordinate 0 (I j w)‖ :=
      congrArg norm (hzero (I j w)).symm
    have hi : ‖(I j w).toLp 2‖ ≤ cI j * ‖G₀.smoothToSobolev 0 w‖ :=
      heq.trans_le (hbI j w)
    apply (hnormMap (I j w) (row i)).trans
    exact (mul_le_mul_of_nonneg_left hi (norm_nonneg (row i))).trans_eq
      (mul_assoc _ _ _).symm
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
  let C₀ : ℝ := ∑ i : Fin a, ∑ j : Fin L.size, ‖row i‖ * cI j
  have hC₀ : 0 ≤ C₀ :=
    Finset.sum_nonneg fun i _ ↦
      Finset.sum_nonneg fun j _ ↦ mul_nonneg (norm_nonneg (row i)) (hcI j)
  have hC : 0 ≤ ‖eMetric.toContinuousLinearMap‖ * C₀ :=
    mul_nonneg (norm_nonneg eMetric.toContinuousLinearMap) hC₀
  refine ⟨‖eMetric.toContinuousLinearMap‖ * C₀, hC, ?_⟩
  intro w
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
  refine ⟨u, hu, fun s i ↦ (hs s i).2, hm, ?_⟩
  intro i
  let g := (hs 0 i).2.toLp (fun z ↦ L.smoothToSobolev 0 (u z i))
  have hsq := L.norm_sobolevZero_family_sq (fun x ↦ u x i) (hs 0 i).2
    (f w i) (hcoords i)
  have hsum : ‖g‖ ≤ ∑ j, ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖ := by
    have hnonneg := Finset.sum_nonneg (s := Finset.univ)
      (fun j _ ↦ norm_nonneg ((f w i j).toLp 2 ((volume : Measure Xp).prod volume)))
    have hsumSq := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
      (fun j _ ↦ norm_nonneg ((f w i j).toLp 2 ((volume : Measure Xp).prod volume)))
    change ‖g‖ ^ 2 = _ at hsq
    exact (sq_le_sq₀ (norm_nonneg g) hnonneg).mp (hsq.trans_le hsumSq)
  have hg : ‖g‖ ≤ C₀ * ‖G₀.smoothToSobolev 0 w‖ := by
    apply hsum.trans
    calc
      (∑ j, ‖(f w i j).toLp 2 ((volume : Measure Xp).prod volume)‖) ≤
          ∑ j, ‖row i‖ * cI j * ‖G₀.smoothToSobolev 0 w‖ :=
        Finset.sum_le_sum (fun j _ ↦ hnorm w i j)
      _ = (∑ j, ‖row i‖ * cI j) * ‖G₀.smoothToSobolev 0 w‖ :=
        (Finset.sum_mul _ _ _).symm
      _ ≤ C₀ * ‖G₀.smoothToSobolev 0 w‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.single_le_sum
          (f := fun l : Fin a ↦ ∑ j : Fin L.size, ‖row l‖ * cI j)
          (fun l _ ↦ Finset.sum_nonneg fun j _ ↦
            mul_nonneg (norm_nonneg (row l)) (hcI j))
          (Finset.mem_univ i)
  -- The same metric equivalence acts on the actual family representatives.
  have hmetric : (hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i)) =
      eMetric.toContinuousLinearMap.compLp g := by
    apply Lp.ext
    filter_upwards [(hm i).coeFn_toLp, eMetric.toContinuousLinearMap.coeFn_compLp g,
      (hs 0 i).2.coeFn_toLp] with z hmz hez hgz
    have hsmooth := k.sobolevZeroEquivL2_smooth (μ := ν) L (u z i)
    exact hmz.trans (hsmooth.symm.trans
      ((congrArg eMetric.toContinuousLinearMap hgz.symm).trans hez.symm))
  calc
    ‖(hm i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ =
        ‖eMetric.toContinuousLinearMap.compLp g‖ := congrArg norm hmetric
    _ ≤ ‖eMetric.toContinuousLinearMap‖ * ‖g‖ :=
      eMetric.toContinuousLinearMap.norm_compLp_le g
    _ ≤ ‖eMetric.toContinuousLinearMap‖ * C₀ * ‖G₀.smoothToSobolev 0 w‖ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hg (norm_nonneg eMetric.toContinuousLinearMap)

end AtiyahSinger
