/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.SmoothKernelDensity
public import AtiyahSinger.Geometry.DensityDiffeomorph
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-!
# Smooth kernels under the geometric section action

Public module ID: M0581.

Fixed group elements transport the two variables of a smooth bundle kernel.
The actual integral operator is first expressed using the pushed-forward
positive smooth measure, and then reweighted back to the original measure.
This is the smoothing remainder in geometric covariance of PDOs; no invariant
measure or compactness of the group is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (P : smoothSections (n := n) (r := r) E →ₗ[ℂ]
    smoothSections (n := n) (r := q) F)

/-- The original geometric conjugation preserves actual smooth-kernel operators. -/
theorem IsSmoothingOperator.conjugate (hP : IsSmoothingOperator μ P) (g : G) :
    IsSmoothingOperator μ
      ((σF.smoothSectionRepresentation IG hσF g).comp
        (P.comp (σE.smoothSectionRepresentation IG hσE g⁻¹))) := by
  /- Write the transported kernel using the inverse of the same output fiber
  action. Its matrix is an inverse smooth action matrix times the original
  kernel matrix times the input action matrix. Change variables in the actual
  integral using the pushed-forward measure, then return to the original density. -/
  classical
  obtain ⟨K, rfl⟩ := hP
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let : MulAction G (TotalSpace Unit E) := σE.toMulAction
  let : MulAction G (TotalSpace Unit F) := σF.toMulAction
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let C (x : M) : F x ≃ₗ[ℂ] F (g⁻¹ • x) :=
    LinearEquiv.ofBijective (σF.linearMap g⁻¹ x) (σF.linearMap_bijective g⁻¹ x)
  let L (x y : M) : E y →L[ℂ] F x :=
    (C x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((K.toFun (g⁻¹ • x) (g⁻¹ • y)).comp
        (σE.linearMap g⁻¹ y).toContinuousLinearMap)
  have hmove : ContMDiff I I ∞ (fun x : M ↦ g⁻¹ • x) :=
    ContMDiffSMul.contMDiff_const_smul (I := IG) g⁻¹
  -- Joint smoothness is checked in the original source and target frames.
  have hL : IsSmoothKernel (n := n) (r := r) (q := q) E F L := by
    intro e f _ _ p hp
    let d := trivializationAt (EuclideanSpace ℂ (Fin r)) E (g⁻¹ • p.2)
    let k := trivializationAt (EuclideanSpace ℂ (Fin q)) F (g⁻¹ • p.1)
    let U : Set (M × M) := {z | z.1 ∈ f.baseSet ∧ z.2 ∈ e.baseSet ∧
      g⁻¹ • z.1 ∈ k.baseSet ∧ g⁻¹ • z.2 ∈ d.baseSet}
    have hU : IsOpen U := (f.open_baseSet.preimage continuous_fst).inter
      ((e.open_baseSet.preimage continuous_snd).inter
        ((k.open_baseSet.preimage (hmove.continuous.comp continuous_fst)).inter
          (d.open_baseSet.preimage (hmove.continuous.comp continuous_snd))))
    have hpU : p ∈ U := ⟨hp.1, hp.2, mem_baseSet_trivializationAt _ _ _,
      mem_baseSet_trivializationAt _ _ _⟩
    let A (z : M × M) : EuclideanSpace ℂ (Fin q) →L[ℂ]
        EuclideanSpace ℂ (Fin q) :=
      ((k.linearMapAt ℂ (g⁻¹ • z.1)).comp ((σF.linearMap g⁻¹ z.1).comp
        (f.symmL ℂ z.1).toLinearMap)).toContinuousLinearMap
    let B (z : M × M) : EuclideanSpace ℂ (Fin r) →L[ℂ]
        EuclideanSpace ℂ (Fin r) :=
      ((d.linearMapAt ℂ (g⁻¹ • z.2)).comp ((σE.linearMap g⁻¹ z.2).comp
        (e.symmL ℂ z.2).toLinearMap)).toContinuousLinearMap
    have hA : ContMDiffOn (I.prod I)
        𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞ A U := by
      have hsum : ContMDiffOn (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ∞
          (fun z : M × M ↦ ∑ i : Fin q,
            ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin q))
              (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin q ↦ ℂ) i)
              ((k ⟨g⁻¹ • z.1, σF.linearMap g⁻¹ z.1
                (f.symmL ℂ z.1 (EuclideanSpace.single i 1))⟩).2)) U := by
        apply contMDiffOn_finsetSum
        intro i _
        have hc := (hσF f k i).comp
          (show ContMDiffOn (I.prod I) (IG.prod I) ∞
            (fun z : M × M ↦ (g⁻¹, z.1)) U from
              contMDiffOn_const.prodMk contMDiffOn_fst)
          (s := U) (fun z hz ↦ ⟨hz.1, hz.2.2.1⟩)
        exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin q))
          (EuclideanSpace ℂ (Fin q)) (PiLp.proj 2 (fun _ : Fin q ↦ ℂ) i)).restrictScalars
            ℝ).contMDiff.comp_contMDiffOn hc
      apply hsum.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro w
      have hh := congrArg (A z) ((EuclideanSpace.basisFun (Fin q) ℂ).sum_repr w)
      simpa [A, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, k.coe_linearMapAt_of_mem hz.2.2.1] using hh.symm
    have hB : ContMDiffOn (I.prod I)
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞ B U := by
      have hsum : ContMDiffOn (I.prod I)
          𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
          (fun z : M × M ↦ ∑ i : Fin r,
            ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
              (EuclideanSpace ℂ (Fin r)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) i)
              ((d ⟨g⁻¹ • z.2, σE.linearMap g⁻¹ z.2
                (e.symmL ℂ z.2 (EuclideanSpace.single i 1))⟩).2)) U := by
        apply contMDiffOn_finsetSum
        intro i _
        have hc := (hσE e d i).comp
          (show ContMDiffOn (I.prod I) (IG.prod I) ∞
            (fun z : M × M ↦ (g⁻¹, z.2)) U from
              contMDiffOn_const.prodMk contMDiffOn_snd)
          (s := U) (fun z hz ↦ ⟨hz.2.1, hz.2.2.2⟩)
        exact ((ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin r))
          (EuclideanSpace ℂ (Fin r)) (PiLp.proj 2 (fun _ : Fin r ↦ ℂ) i)).restrictScalars
            ℝ).contMDiff.comp_contMDiffOn hc
      apply hsum.congr
      intro z hz
      apply ContinuousLinearMap.ext
      intro w
      have hh := congrArg (B z) ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr w)
      simpa [B, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, d.coe_linearMapAt_of_mem hz.2.2.2] using hh.symm
    let T (z : M × M) (hz : z ∈ U) :
        EuclideanSpace ℂ (Fin q) ≃L[ℂ] EuclideanSpace ℂ (Fin q) :=
      (((f.linearEquivAt ℂ z.1 hz.1).symm.trans (C z.1)).trans
        (k.linearEquivAt ℂ (g⁻¹ • z.1) hz.2.2.1)).toContinuousLinearEquiv
    have hT (z : M × M) (hz : z ∈ U) : (T z hz).toContinuousLinearMap = A z := by
      apply ContinuousLinearMap.ext
      intro w
      simp [T, A, C, k.coe_linearMapAt_of_mem hz.2.2.1, f.symmL_apply hz.1,
        Bundle.Trivialization.linearEquivAt_symm_apply,
        Bundle.Trivialization.linearEquivAt_apply]
    have hinversion := (contDiffAt_map_inverse (n := ∞) (T p hpU)).restrict_scalars ℝ
    rw [hT p hpU] at hinversion
    have hinv := hinversion.comp_contMDiffAt (hA.contMDiffAt (hU.mem_nhds hpU))
    have hK := (K.isSmooth d k).comp
      (show ContMDiffOn (I.prod I) (I.prod I) ∞
        (fun z : M × M ↦ (g⁻¹ • z.1, g⁻¹ • z.2)) U from
          ((hmove.comp contMDiff_fst).prodMk (hmove.comp contMDiff_snd)).contMDiffOn)
      (s := U) (fun z hz ↦ ⟨hz.2.2.1, hz.2.2.2⟩)
    have hcomp : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1.comp z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    have hcomp' : ContDiff ℝ ∞ (fun z :
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ×
          (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ↦ z.1.comp z.2) :=
      (show ContDiff ℂ ∞ _ from contDiff_fst.clm_comp contDiff_snd).restrict_scalars ℝ
    have hright := hcomp'.comp_contMDiffAt
      ((hK.contMDiffAt (hU.mem_nhds hpU)).prodMk_space
        (hB.contMDiffAt (hU.mem_nhds hpU)))
    have hlocal := hcomp.comp_contMDiffAt (hinv.prodMk_space hright)
    apply (hlocal.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hU.mem_nhds hpU] with z hz
    change kernelInFrames E F L e f z =
      (A z).inverse.comp ((kernelInFrames E F K.toFun d k
        (g⁻¹ • z.1, g⁻¹ • z.2)).comp (B z))
    rw [← hT z hz, ContinuousLinearMap.inverse_equiv]
    apply ContinuousLinearMap.ext
    intro w
    simp [kernelInFrames, L, T, B, ContinuousLinearMap.comp_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_apply, d.symmL_apply hz.2.2.2,
      f.continuousLinearMapAt_apply_of_mem ℂ hz.1,
      d.coe_linearMapAt_of_mem hz.2.2.2,
      k.continuousLinearMapAt_apply_of_mem ℂ hz.2.2.1,
      d.symm_apply_apply_mk hz.2.2.2, k.symm_apply_apply_mk hz.2.2.1]
  let K' : SmoothKernel (n := n) (r := r) (q := q) E F := ⟨L, hL⟩
  let e := Diffeomorph.smul (M := M) IG I ∞ g
  let ν : Measure M := Measure.map e μ
  let : IsSmoothPositiveMeasure (n := n) ν := IsSmoothPositiveMeasure.map_diffeomorph μ e
  -- The pushforward measure handles exactly the base change in the input variable.
  apply (isSmoothingOperator_measure_iff ν μ _).mp
  refine ⟨K', ?_⟩
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  let v := σE.smoothSectionRepresentation IG hσE g⁻¹ u
  have hinput (y : M) :
      K.toFun (g⁻¹ • x) (g⁻¹ • (g • y)) (σE.linearMap g⁻¹ (g • y) (u.val (g • y))) =
        K.toFun (g⁻¹ • x) y (v.val y) := by
    have ht := σE.mk_sectionLinearMap g⁻¹ u.val y
    change (⟨y, v.val y⟩ : TotalSpace Unit E) =
      ⟨g⁻¹ • ((g⁻¹)⁻¹ • y), σE.linearMap g⁻¹ ((g⁻¹)⁻¹ • y)
        (u.val ((g⁻¹)⁻¹ • y))⟩ at ht
    rw [inv_inv] at ht
    have hsource :
        (⟨g⁻¹ • (g • y), σE.linearMap g⁻¹ (g • y) (u.val (g • y))⟩ :
          TotalSpace Unit E) = ⟨y, v.val y⟩ := by
      exact ht.symm
    exact congrArg (fun z : TotalSpace Unit E ↦ K.toFun (g⁻¹ • x) z.proj z.snd) hsource
  have houtput (s : ∀ y, F y) :
      (C x).symm (s (g⁻¹ • x)) = σF.sectionLinearMap g s x := by
    apply TotalSpace.mk_injective (F := Unit) x
    apply (MulAction.injective g⁻¹)
    change (⟨g⁻¹ • x, C x ((C x).symm (s (g⁻¹ • x)))⟩ : TotalSpace Unit F) = _
    rw [LinearEquiv.apply_symm_apply]
    have ht := σF.mk_sectionLinearMap g s x
    change (⟨x, σF.sectionLinearMap g s x⟩ : TotalSpace Unit F) =
      g • (⟨g⁻¹ • x, s (g⁻¹ • x)⟩ : TotalSpace Unit F) at ht
    rw [ht]
    exact (inv_smul_smul g _).symm
  let D := (C x).symm.toContinuousLinearEquiv
  change (∫ y, L x y (u.val y) ∂ν) = σF.sectionLinearMap g (K.toLinearMap μ v).val x
  calc
    _ = ∫ y, L x (g • y) (u.val (g • y)) ∂μ :=
      integral_map_equiv (Homeomorph.smul g).toMeasurableEquiv _
    _ = ∫ y, D (K.toFun (g⁻¹ • x) y (v.val y)) ∂μ := by
      apply integral_congr_ae
      filter_upwards with y
      exact congrArg D (hinput y)
    _ = D (K.apply μ v (g⁻¹ • x)) := D.integral_comp_comm _
    _ = _ := houtput (K.toLinearMap μ v).val

end AtiyahSinger

