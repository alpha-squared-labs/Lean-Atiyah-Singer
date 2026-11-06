/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothAtlasTransport
public import AtiyahSinger.Geometry.SmoothIdempotentBundle
public import AtiyahSinger.Topology.SerreSwanMaps

import AtiyahSinger.Analysis.SmoothIdempotentCorrection
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Compatible smooth atlases on the original continuous bundles

Public module ID: M1144.

A finite-rank continuous complex bundle on a compact smooth manifold admits a
smooth atlas on its original fibers and total-space topology. Serre--Swan first
realizes the bundle as the image of a continuous idempotent. Smooth approximation
followed by the analytic idempotent retraction gives a nearby smooth idempotent.
The explicit invertible intertwiner identifies their actual image bundles.

This proves the ordinary bundle-smoothing assertion of Spin Geometry Appendix A,
Remark A.1. Ranks may vary between components; neither self-adjointness of the
initial idempotent nor a global trivialization is assumed. The final finite
subatlas has a small index type, without resizing the original fibers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology
open scoped Manifold ContDiff Matrix Matrix.Norms.L2Operator

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hC : CompactSpace M] [hT : T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [hE : IsFiniteRank E]

attribute [local instance] IdempotentMatrix.fiberTotalSpaceTopology
attribute [local instance] IdempotentMatrix.isFiniteRank_fiber

include hM hC hT hE in
/-- A continuous finite-rank complex bundle has a compatible smooth atlas on the same fibers. -/
theorem nonempty_smoothComplexBundleAtlas :
    Nonempty (SmoothComplexBundleAtlas.{0} (n := n) E) := by
  classical
  let p := idempotentPresentation (E := E)
  let e : Iso E (fun x ↦ p.fiber x) := presentationIso
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
  have hdiag : IsCompact (Set.range (fun x : M ↦ (P x, P x))) :=
    isCompact_range (hP.prodMk hP)
  have hdiagΩ : Set.range (fun x : M ↦ (P x, P x)) ⊆ Ω := by
    rintro _ ⟨x, rfl⟩
    constructor
    · simp only [hPP, sub_self, smul_zero, norm_zero, zero_lt_one]
    · rw [idempotentCorrection_eq (P x) (hPP x)]
      have hid : idempotentIntertwiner (P x) (P x) = 1 := by
        dsimp only [idempotentIntertwiner]
        noncomm_ring [hPP x]
      rw [hid, sub_self, norm_zero]
      exact zero_lt_one
  obtain ⟨ε, hε, hεΩ⟩ := hdiag.exists_thickening_subset_open hΩ hdiagΩ
  -- Approximate in the fixed matrix space, then retract to genuine smooth idempotents.
  obtain ⟨a, ha, _⟩ := hP.exists_contMDiff_approx
    𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (⊤ : ℕ∞) continuous_const (fun _ ↦ hε)
  have haΩ (x : M) : (P x, a x) ∈ Ω := by
    apply hεΩ
    apply Metric.mem_thickening_iff.mpr
    refine ⟨(P x, P x), ⟨x, rfl⟩, ?_⟩
    simpa only [Prod.dist_eq, dist_self, max_eq_right (dist_nonneg)] using ha x
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
  exact ⟨(eq.smoothAtlas B).finiteSubatlas⟩

end AtiyahSinger.ComplexBundle
