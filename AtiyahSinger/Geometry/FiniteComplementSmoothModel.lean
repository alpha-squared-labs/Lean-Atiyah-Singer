/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.FixedRankSmoothModel
public import AtiyahSinger.Topology.BundleHomotopyType

import AtiyahSinger.Analysis.SmoothIdempotentCorrection
import AtiyahSinger.Geometry.AtlasFrameTransition
import AtiyahSinger.Topology.HermitianFixedRankModel
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Smooth models on bases of finite CW homotopy type

Public module ID: M1234.

For a bundle of specified constant rank on a Hausdorff second-countable
smooth base, a finite CW homotopy model gives a finite idempotent presentation
on the original, possibly noncompact, base. Fine approximation and the
analytic idempotent correction smooth this presentation. The original bundle
is retained by an explicit continuous fiber isomorphism; no compactness of
its base or uniform bound on its original idempotents is assumed.

This is the finite-presentation case of smooth bundle classification from
SG Appendix A, Remark A.1, needed for SG III.13's relative representatives.
The approximation argument uses distance to the closed bad set as its variable
positive tolerance. The fixed-rank model changes the phantom total-space
model but keeps the actual vectors and topology.
-/

@[expose] public noncomputable section

universe u v

namespace AtiyahSinger.ComplexBundle

open Bundle Topology
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
  IdempotentMatrix.isFiniteRank_fiber isFiniteRank_pullback

-- Keep the finite matrix correction and its explicit inverse image maps in one proof.
private theorem nonempty_smoothAtlas_of_idempotent_presentation
    {E : M → Type v} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (p : IdempotentMatrix C(M, ℂ)) (e : Iso E (fun x ↦ p.fiber x)) :
    Nonempty (SmoothComplexBundleAtlas.{u} (n := n) E) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  let Mat := Matrix (Fin p.size) (Fin p.size) ℂ
  let P (x : M) : Mat := (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).matrix
  have hP : Continuous P := continuous_pi fun i ↦
    continuous_pi fun j ↦ (p.matrix i j).continuous
  have hPP (x : M) : P x * P x = P x :=
    (p.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom).mul_self
  let entry (i j : Fin p.size) : Mat →L[ℝ] ℂ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun A ↦ A i j
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
  -- One open neighborhood controls both the correction domain and the actual bundle comparison.
  let Ω : Set (Mat × Mat) := {z |
    ‖(4 : ℝ) • (z.2 * z.2 - z.2)‖ < 1 ∧
      ‖idempotentIntertwiner (idempotentCorrection z.2) z.1 - 1‖ < 1}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hdefect : Continuous (fun w : Mat × Mat ↦
        ‖(4 : ℝ) • (w.2 * w.2 - w.2)‖) := by
      fun_prop
    have hQ : ContinuousAt (fun w : Mat × Mat ↦ idempotentCorrection w.2) z :=
      (contDiffAt_idempotentCorrection z.2 hz.1).continuousAt.comp
        continuous_snd.continuousAt
    have hT : ContinuousAt (fun w : Mat × Mat ↦
        ‖idempotentIntertwiner (idempotentCorrection w.2) w.1 - 1‖) z := by
      dsimp only [idempotentIntertwiner]
      exact (((continuousAt_const.sub hQ).sub continuousAt_fst).add
        ((continuousAt_const.mul hQ).mul continuousAt_fst) |>.sub continuousAt_const).norm
    exact (hdefect.continuousAt.eventually_lt continuousAt_const hz.1).and
      (hT.eventually_lt continuousAt_const hz.2)
  have hdiagΩ (x : M) : (P x, P x) ∈ Ω := by
    constructor
    · simp only [hPP, sub_self, smul_zero, norm_zero, zero_lt_one]
    · rw [idempotentCorrection_eq (P x) (hPP x)]
      have hid : idempotentIntertwiner (P x) (P x) = 1 := by
        dsimp only [idempotentIntertwiner]
        noncomm_ring [hPP x]
      rw [hid, sub_self, norm_zero]
      exact zero_lt_one
  -- Distance to the closed bad set supplies a positive pointwise tolerance.
  -- This uses no compact range or uniform bound on the original idempotents.
  obtain ⟨ε, hεc, hεpos, hεΩ⟩ : ∃ ε : M → ℝ, Continuous ε ∧
      (∀ x, 0 < ε x) ∧ ∀ x (A : Mat), dist A (P x) < ε x → (P x, A) ∈ Ω := by
    by_cases hbad : Ωᶜ.Nonempty
    · refine ⟨fun x ↦ Metric.infDist (P x, P x) Ωᶜ,
        (Metric.continuous_infDist_pt _).comp (hP.prodMk hP), ?_, ?_⟩
      · intro x
        exact (hΩ.isClosed_compl.notMem_iff_infDist_pos hbad).mp
          (by simpa only [Set.notMem_compl_iff] using hdiagΩ x)
      · intro x A hA
        apply Set.notMem_compl_iff.mp
        apply Metric.notMem_of_dist_lt_infDist (x := (P x, P x))
        simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg), dist_comm]
          using hA
    · refine ⟨fun _ ↦ 1, continuous_const, fun _ ↦ zero_lt_one, ?_⟩
      intro x A _
      exact Set.notMem_compl_iff.mp (fun h ↦ hbad ⟨(P x, A), h⟩)
  obtain ⟨a, ha, _⟩ := hP.exists_contMDiff_approx
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) hεc hεpos
  have haΩ (x : M) : (P x, a x) ∈ Ω := hεΩ x (a x) (ha x)
  let Q (x : M) : Mat := idempotentCorrection (a x)
  have hQ : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Mat) ∞ Q := by
    intro x
    exact (contDiffAt_idempotentCorrection (a x) (haΩ x).1).contMDiffAt.comp x
      (a.contMDiff x)
  have hQQ (x : M) : Q x * Q x = Q x :=
    isIdempotentElem_idempotentCorrection (a x) (haΩ x).1
  have hentry (i j : Fin p.size) :
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞ (fun x ↦ Q x i j) :=
    (entry i j).contMDiff.comp hQ
  let q : IdempotentMatrix C(M, ℂ) :=
    { size := p.size
      matrix := fun i j ↦ ⟨fun x ↦ Q x i j, (hentry i j).continuous⟩
      mul_self := by
        ext i j x
        change (∑ k : Fin p.size,
          (⟨fun y ↦ Q y i k, (hentry i k).continuous⟩ : C(M, ℂ)) *
            (⟨fun y ↦ Q y k j, (hentry k j).continuous⟩ : C(M, ℂ))) x = Q x i j
        simpa [Matrix.mul_apply, Mat] using congrFun (congrFun (hQQ x) i) j }
  let T (x : M) : Mat := idempotentIntertwiner (Q x) (P x)
  have hT : Continuous T := by
    dsimp only [T, idempotentIntertwiner]
    exact ((continuous_const.sub hQ.continuous).sub hP).add
      ((continuous_const.mul hQ.continuous).mul hP)
  have hunit (x : M) : IsUnit (T x) :=
    isUnit_idempotentIntertwiner_of_norm_lt (Q x) (P x) (haΩ x).2
  have hcomm (x : M) : T x * P x = Q x * T x :=
    idempotentIntertwiner_mul (Q x) (P x) (hQQ x) (hPP x)
  let L (x : M) : Mat := Ring.inverse (T x)
  have hLT (x : M) : L x * T x = 1 := Ring.inverse_mul_cancel (T x) (hunit x)
  have hTL (x : M) : T x * L x = 1 := Ring.mul_inverse_cancel (T x) (hunit x)
  -- Restrict this same invertible intertwiner to the original and corrected image fibers.
  let front (x : M) : p.fiber x →ₗ[ℂ] q.fiber x :=
    (Q x).mulVecLin.rangeRestrict.comp ((T x).mulVecLin.comp (p.fiber x).subtype)
  let back (x : M) : q.fiber x →ₗ[ℂ] p.fiber x :=
    (P x).mulVecLin.rangeRestrict.comp ((L x).mulVecLin.comp (q.fiber x).subtype)
  have hPfix (x : M) (v : p.fiber x) : P x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ : ∃ w : Fin p.size → ℂ, P x *ᵥ w = v.val := v.property
    rw [← hw, Matrix.mulVec_mulVec, hPP]
  have hQfix (x : M) (v : q.fiber x) : Q x *ᵥ v.val = v.val := by
    obtain ⟨w, hw⟩ : ∃ w : Fin p.size → ℂ, Q x *ᵥ w = v.val := v.property
    rw [← hw, Matrix.mulVec_mulVec, hQQ]
  have hfrontback (x : M) (v : q.fiber x) : front x (back x v) = v := by
    apply Subtype.ext
    change Q x *ᵥ (T x *ᵥ (P x *ᵥ (L x *ᵥ v.val))) = v.val
    have hid : Q x * T x * P x * L x = Q x := by
      calc
        _ = Q x * (T x * P x) * L x := by noncomm_ring
        _ = Q x * (Q x * T x) * L x := by rw [hcomm]
        _ = (Q x * Q x) * (T x * L x) := by noncomm_ring
        _ = Q x := by rw [hQQ, hTL, mul_one]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hQfix x v
  have hbackfront (x : M) (v : p.fiber x) : back x (front x v) = v := by
    apply Subtype.ext
    change P x *ᵥ (L x *ᵥ (Q x *ᵥ (T x *ᵥ v.val))) = v.val
    have hid : P x * L x * Q x * T x = P x := by
      calc
        _ = (P x * L x) * (Q x * T x) := by noncomm_ring
        _ = (P x * L x) * (T x * P x) := by rw [← hcomm]
        _ = P x * (L x * T x) * P x := by noncomm_ring
        _ = P x := by rw [hLT, mul_one, hPP]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hid]
    exact hPfix x v
  have hpair : Continuous (fun z : TotalSpace Unit (fun x ↦ p.fiber x) ↦
      (z.proj, z.snd.val)) := continuous_induced_dom
  have hbase := continuous_fst.comp hpair
  have hvec := continuous_snd.comp hpair
  let f : Hom (fun x ↦ p.fiber x) (fun x ↦ q.fiber x) :=
    { linearMap := front
      continuous_total := by
        apply continuous_induced_rng.mpr
        exact hbase.prodMk ((hQ.continuous.comp hbase).matrix_mulVec
          ((hT.comp hbase).matrix_mulVec hvec)) }
  have hf (x : M) : Function.Bijective (f.linearMap x) :=
    ⟨Function.LeftInverse.injective (hbackfront x),
      Function.RightInverse.surjective (hfrontback x)⟩
  -- The resulting atlas is transported through the one specified actual bundle isomorphism.
  let eq : Iso E (fun x ↦ q.fiber x) := e.trans (f.toIso hf)
  obtain ⟨B⟩ := q.nonempty_smoothComplexBundleAtlas hentry
  exact ⟨eq.smoothAtlas B⟩


omit [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] in
-- Check all transported chart transitions and original total-space topology together.
private theorem exists_smooth_model_of_atlas
    {E : M → Type} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (A : SmoothComplexBundleAtlas.{u} (n := n) E) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E x) = r) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      Nonempty (Iso E F.Fiber) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
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


-- Retain the dependent pullback and native-atlas witnesses through the full construction.
/-- A bundle of fixed rank on a smooth base of finite CW homotopy type has a smooth model.
The specified finite CW model is used only for an actual finite image presentation;
the base itself may be noncompact. -/
theorem FiniteBundle.exists_smooth_model_of_homotopyEquiv_finiteCW
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (e : ContinuousMap.HomotopyEquiv M C) (E : FiniteBundle M) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E.Fiber x) = r) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      Nonempty (Iso E.Fiber F.Fiber) := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- The finite model is compact; the original manifold is never made compact.
  let : Finite (Σ j, Topology.RelCWComplex.cell C j) :=
    Topology.RelCWComplex.finite_cells_of_finite
  have hC : IsCompact C := by
    have hc := isCompact_iUnion (fun ji : (Σ j, Topology.RelCWComplex.cell C j) ↦
      Topology.RelCWComplex.isCompact_closedCell (C := C) (n := ji.1) (i := ji.2))
    simpa only [Set.iUnion_sigma, Topology.CWComplex.union] using hc
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let c : C(M, C) := e.toFun
  let d : C(C, M) := e.invFun
  let E₀ := E.pullback d
  obtain ⟨p₀, ⟨j₀⟩⟩ := exists_idempotent_presentation (E := E₀.Fiber)
  obtain ⟨h⟩ := nonempty_pullback_iso_of_homotopic E (d.comp c) (ContinuousMap.id M)
    e.left_inv
  let k : Iso ((c : M → C) *ᵖ E₀.Fiber) E.Fiber :=
    (pullbackCompIso (E := E.Fiber) d c).trans (h.trans (pullbackIdIso (E := E.Fiber)))
  -- Pull the finite matrix presentation back through the same original c.
  let p : IdempotentMatrix C(M, ℂ) :=
    p₀.map (ContinuousMap.compRightAlgHom ℂ ℂ c).toRingHom
  let bridge : Hom ((c : M → C) *ᵖ (fun y ↦ p₀.fiber y)) (fun x ↦ p.fiber x) :=
    { linearMap _ := LinearMap.id
      continuous_total := by
        have hvec : Continuous (fun z : TotalSpace Unit (fun y ↦ p₀.fiber y) ↦
            z.snd.val) := by
          have hpair : Continuous (fun z : TotalSpace Unit (fun y ↦ p₀.fiber y) ↦
              (z.proj, z.snd.val)) := continuous_induced_dom
          exact hpair.snd
        apply continuous_induced_rng.mpr
        exact continuous_proj.prodMk
          (hvec.comp (Pullback.continuous_lift Unit (fun y ↦ p₀.fiber y) c)) }
  let j : Iso E.Fiber (fun x ↦ p.fiber x) :=
    k.symm.trans ((j₀.pullback c).trans (bridge.toIso (fun _ ↦ Function.bijective_id)))
  -- Fine approximation smooths this actual presentation on the original noncompact base.
  obtain ⟨A⟩ := nonempty_smoothAtlas_of_idempotent_presentation (n := n) p j
  exact exists_smooth_model_of_atlas (n := n) A r hr

end AtiyahSinger.ComplexBundle
