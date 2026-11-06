/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SphereHodge
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# Continuous tensor coefficients of the original orthogonal sphere action

Public module ID: M1432.

The inverse pullback of a fixed smooth differential form has continuous pointwise
coefficients in the orthogonal matrix. Free matrix parameters and radial normalization
supply a local smooth extension of the original sphere action. Differentiating this
extension in native charts proves continuity of the actual tangent pullbacks.

These separating coefficients construct finite continuous representations on the
original harmonic spaces. The argument installs neither a topology on all smooth
forms nor a Lie atlas on the orthogonal group. It is a standard parameter-dependent
pullback argument supplementing the isometry action used in SG III.9, pp.211--212.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter IsManifold Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 1000000 in
-- Full matrix parameters supply an honest smooth extension before differentiating.
set_option backward.isDefEq.respectTransparency false in
/-- Pointwise tensor coefficients of the specified inverse sphere pullback are continuous. -/
theorem continuous_orthogonalSphere_smoothFormPullback_eval (r p : ℕ)
    (u : SmoothDifferentialForm (n := r) (OrthogonalSphere r) p)
    (x : OrthogonalSphere r) (v : Fin p → EuclideanSpace ℝ (Fin r)) :
    Continuous (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦
      (smoothFormPullback (fun z : OrthogonalSphere r ↦ A⁻¹ • z)
        (contMDiff_orthogonalSphere_smul r A⁻¹) p u).val x v) := by
  classical
  have hRadial :
      ∃ F : (Fin r → Fin r → ℝ) → OrthogonalSphere r → OrthogonalSphere r,
        (∀ A : Matrix.orthogonalGroup (Fin r) ℝ, F A.val = fun z ↦ A • z) ∧
        ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r),
          ContMDiffAt ((𝓘(ℝ, Fin r → Fin r → ℝ)).prod (𝓡 r)) (𝓡 r) ∞
            (Function.uncurry F) (A.val, z) := by
    classical
    let Mat := Fin r → Fin r → ℝ
    let V := EuclideanSpace ℝ (Fin r)
    let W := OrthogonalSphereAmbient r
    let I := (𝓘(ℝ, Mat)).prod (𝓡 r)
    -- Native target charts transfer pointwise ambient regularity to sphere regularity.
    have hSphereAt (g : Mat × OrthogonalSphere r → OrthogonalSphere r)
        (p : Mat × OrthogonalSphere r)
        (hg : ContMDiffAt I 𝓘(ℝ, W) ∞ (fun q ↦ (g q).val) p) :
        ContMDiffAt I (𝓡 r) ∞ g p := by
      rw [contMDiffAt_iff_target]
      refine ⟨tendsto_subtype_rng.mpr hg.continuousAt, ?_⟩
      let v : OrthogonalSphere r := g p
      let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
        r (ne_zero_of_mem_unit_sphere (-v))).repr
      have hPole : inner (𝕜 := ℝ) (-(v : W)) (v : W) ≠ 1 := by
        rw [inner_neg_left, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere v]
        norm_num
      have hStereo : ContDiffAt ℝ ∞ (stereoToFun (-(v : W))) (v : W) :=
        contDiffOn_stereoToFun.contDiffAt
          ((isOpen_ne.preimage (innerSL ℝ (-(v : W))).continuous).mem_nhds hPole)
      change ContMDiffAt I (𝓡 r) ∞
        (fun q ↦ U (stereoToFun (-(v : W)) (g q).val)) p
      have hCoordinate : ContDiffAt ℝ ∞
          (fun w : W ↦ U (stereoToFun (-(v : W)) w)) (v : W) :=
        U.contDiff.contDiffAt.comp (v : W) hStereo
      exact ContMDiffAt.comp (f := fun q ↦ (g q).val)
        (g := fun w : W ↦ U (stereoToFun (-(v : W)) w)) p
        hCoordinate.contMDiffAt hg
    let matrixMap : Mat ≃L[ℝ] (V →L[ℝ] V) :=
      LinearEquiv.toContinuousLinearEquiv
        (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv
    let split := WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ
    let ambient (p : Mat × OrthogonalSphere r) : W :=
      split.symm (matrixMap p.1 p.2.val.fst, p.2.val.snd)
    -- All matrix entries are free parameters in this ambient smooth family.
    have hMatrix : ContMDiff I 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun p : Mat × OrthogonalSphere r ↦ matrixMap p.1) :=
      matrixMap.contDiff.contMDiff.comp contMDiff_fst
    have hSphere : ContMDiff I 𝓘(ℝ, W) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val) :=
      contMDiff_coe_sphere.comp contMDiff_snd
    have hHorizontal : ContMDiff I 𝓘(ℝ, V) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val.fst) :=
      (ContinuousLinearMap.fst ℝ V ℝ).contDiff.contMDiff.comp
        (split.contDiff.contMDiff.comp hSphere)
    have hVertical : ContMDiff I 𝓘(ℝ, ℝ) ∞
        (fun p : Mat × OrthogonalSphere r ↦ p.2.val.snd) :=
      (ContinuousLinearMap.snd ℝ V ℝ).contDiff.contMDiff.comp
        (split.contDiff.contMDiff.comp hSphere)
    have hAmbient : ContMDiff I 𝓘(ℝ, W) ∞ ambient :=
      split.symm.contDiff.contMDiff.comp
        ((hMatrix.clm_apply hHorizontal).prodMk_space hVertical)
    let F (P : Mat) (z : OrthogonalSphere r) : OrthogonalSphere r :=
      if h : ambient (P, z) = 0 then orthogonalSphereNorth r
      else ⟨NormedSpace.normalize (ambient (P, z)), by
        simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize h⟩
    have hOpen : IsOpen {p : Mat × OrthogonalSphere r | ambient p ≠ 0} :=
      isOpen_ne.preimage hAmbient.continuous
    -- On this open locus the fallback disappears and radial normalization is smooth.
    have hSmooth (p : Mat × OrthogonalSphere r) (hp : ambient p ≠ 0) :
        ContMDiffAt I (𝓡 r) ∞ (Function.uncurry F) p := by
      have hNormalize : ContDiffAt ℝ ∞ (NormedSpace.normalize : W → W) (ambient p) :=
        ((contDiffAt_norm ℝ hp).inv (norm_ne_zero_iff.mpr hp)).smul contDiffAt_id
      have hValue : ContMDiffAt I 𝓘(ℝ, W) ∞
          (fun q : Mat × OrthogonalSphere r ↦ (F q.1 q.2).val) p := by
        apply (hNormalize.contMDiffAt.comp p hAmbient.contMDiffAt).congr_of_eventuallyEq
        filter_upwards [hOpen.mem_nhds hp] with q hq
        simp only [F, dite_eq_right hq]
        rfl
      exact hSphereAt (Function.uncurry F) p hValue
    have hOriginal (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r) :
        ambient (A.val, z) = (A • z).val := rfl
    have hNonzero (A : Matrix.orthogonalGroup (Fin r) ℝ) (z : OrthogonalSphere r) :
        ambient (A.val, z) ≠ 0 := by
      rw [hOriginal]
      exact ne_zero_of_mem_unit_sphere (A • z)
    refine ⟨F, ?_, ?_⟩
    · -- Unit norm makes the extension exactly the already specified orthogonal action.
      intro A
      funext z
      apply Subtype.ext
      simp only [F, dite_eq_right (hNonzero A z)]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (norm_eq_of_mem_sphere (A • z))
    · intro A z
      exact hSmooth (A.val, z) (hNonzero A z)
  -- Differentiate the local smooth extension in fixed native tangent coordinates.
  obtain ⟨F, hFeq, hFsmooth⟩ := hRadial
  let V := EuclideanSpace ℝ (Fin r)
  let S := OrthogonalSphere r
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let Mat := Fin r → Fin r → ℝ
  let I := 𝓘(ℝ, Mat)
  let J := 𝓡 r
  let : ContinuousSMul G S := continuousSMul_orthogonalSphere r
  apply continuous_iff_continuousAt.mpr
  intro A₀
  let c := chartAt V (A₀⁻¹ • x)
  have hc : c ∈ atlas V S := chart_mem_atlas V (A₀⁻¹ • x)
  have hx : x ∈ (chartAt V x).source := mem_chart_source V x
  have hy₀ : A₀⁻¹ • x ∈ c.source := mem_chart_source V (A₀⁻¹ • x)
  let C := inTangentCoordinates J J (fun _ : Mat ↦ x) (fun B ↦ F B x)
    (fun B ↦ mfderiv J J (F B) x) A₀⁻¹.val
  have hd := ContMDiffAt.mfderiv (fun B : Mat ↦ F B) (fun _ : Mat ↦ x)
    (hFsmooth A₀⁻¹ x) contMDiffAt_const (m := (∞ : WithTop ℕ∞)) (by simp)
  have hparam : Continuous (fun A : G ↦ A⁻¹.val) := continuous_subtype_val.comp continuous_inv
  have hder : ContinuousAt (fun A : G ↦ C A⁻¹.val) A₀ :=
    ContinuousAt.comp (f := fun A : G ↦ A⁻¹.val) (g := C)
      hd.continuousAt hparam.continuousAt
  have hy : Continuous (fun A : G ↦ A⁻¹ • x) := continuous_inv.smul continuous_const
  have hcy : ContinuousAt (fun A : G ↦ c (A⁻¹ • x)) A₀ :=
    ContinuousAt.comp (f := fun A : G ↦ A⁻¹ • x) (g := c)
      (c.continuousAt hy₀) hy.continuousAt
  let a (A : G) := differentialFormInChart u.val c (c (A⁻¹ • x))
  have ha : ContinuousAt a A₀ :=
    ContinuousAt.comp (f := fun A : G ↦ c (A⁻¹ • x))
      (g := differentialFormInChart u.val c)
      ((u.property c hc).continuousOn.continuousAt
        (c.open_target.mem_nhds (c.map_source hy₀))) hcy
  have hv : ContinuousAt (fun A : G ↦ fun i : Fin p ↦ C A⁻¹.val (v i)) A₀ := by
    apply continuousAt_pi.mpr
    intro i
    exact hder.clm_apply continuousAt_const
  have heval : ContinuousAt (fun A : G ↦ a A (fun i ↦ C A⁻¹.val (v i))) A₀ :=
    continuous_eval.continuousAt.comp (ha.prodMk hv)
  -- The inverse chart chain rule recovers exactly the original form evaluation.
  apply heval.congr_of_eventuallyEq
  filter_upwards [hy.continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hy₀)] with A hA
  have hcoords : C A⁻¹.val =
      (mfderiv J J c (A⁻¹ • x)).comp
        (mfderiv J J (fun z : S ↦ A⁻¹ • z) x) := by
    have ht := inTangentCoordinates_eq_mfderiv_comp_abuse (I := J) (I' := J)
      (f := fun _ : Mat ↦ x) (g := fun B ↦ F B x)
      (ϕ := fun B ↦ mfderiv J J (F B) x) (x₀ := A₀⁻¹.val) (x := A⁻¹.val) hx
      (show F A⁻¹.val x ∈ (chartAt V (F A₀⁻¹.val x)).source by
        rw [hFeq A₀⁻¹, hFeq A⁻¹]
        exact hA)
    rw [mfderivWithin_range_extChartAt_symm, ContinuousLinearMap.comp_id] at ht
    change C A⁻¹.val = _ at ht
    rw [hFeq A₀⁻¹, hFeq A⁻¹] at ht
    exact ht
  have hinv := (mdifferentiable_of_mem_atlas (I := J) hc).symm_comp_deriv hA
  symm
  rw [smoothFormPullback_apply]
  change u.val (c.symm (c (A⁻¹ • x)))
      (fun i ↦ (mfderiv J J c.symm (c (A⁻¹ • x))) (C A⁻¹.val (v i))) =
    u.val (A⁻¹ • x) (fun i ↦ (mfderiv J J (fun z : S ↦ A⁻¹ • z) x) (v i))
  erw [c.left_inv hA, hcoords]
  congr 1
  funext i
  exact congrArg (fun T : V →L[ℝ] V ↦
    T ((mfderiv J J (fun z : S ↦ A⁻¹ • z) x) (v i))) hinv

end AtiyahSinger
