/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalSphere

/-!
# Smooth families of orthogonal sphere transformations

Public module ID: M1336.

For a matrix family smooth on a set with orthogonal values, the original block
action on the native sphere is jointly smooth on that set times the sphere.
This supplies the transition maps for the sphere-bundle construction in
SG III.13, page 251, without assuming a Lie-group atlas on `O(r)`.

The parameter is any smooth real manifold in the stated model. No compactness,
orientation, spin structure, or positive-rank assumption is needed. The matrix
entries are the actual smooth data, and the sphere action is the already fixed
`diag(A, 1)` action on the Euclidean `L²` direct sum.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
  (I : ModelWithCorners ℝ E H) [hB : IsManifold I ∞ B]

include hB in
/-- Orthogonal matrix families smooth on a parameter set act smoothly on its sphere product. -/
theorem contMDiffOn_orthogonalSphere_parametric_smul (r : ℕ)
    (A : B → Matrix (Fin r) (Fin r) ℝ) (s : Set B)
    (hA : ContMDiffOn I 𝓘(ℝ, Fin r → Fin r → ℝ) ∞ (fun b i j ↦ A b i j) s)
    (horth : ∀ b : B, A b ∈ Matrix.orthogonalGroup (Fin r) ℝ) :
    ContMDiffOn (I.prod (𝓡 r)) (𝓡 r) ∞
      (fun p : B × OrthogonalSphere r ↦
        (⟨A p.1, horth p.1⟩ : Matrix.orthogonalGroup (Fin r) ℝ) • p.2)
      (s ×ˢ Set.univ) := by
  /- Stage 1: in the actual ambient L² direct sum, the map is
  (b,(x,t)) |-> (A(b)x,t). Each horizontal coordinate is a finite sum of
  products of the matrix entries, smooth on s, with the smooth sphere inclusion
  coordinates. The unchanged last coordinate is smooth as well.
  Stage 2: orthogonality preserves the horizontal Euclidean norm, so the
  block map takes the original unit sphere into itself. In each native target
  sphere chart, its stereographic coordinate formula is smooth on the stated
  product set: denominators are nonzero near the point under consideration.
  The resulting map is definitionally the previously specified action.
  No differentiability assertion for the subtype O(r) is used in this argument. -/
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let f (p : B × OrthogonalSphere r) : W :=
    orthogonalSphereBlockIsometry r ⟨A p.1, horth p.1⟩ p.2.val
  -- The matrix representation is a continuous linear map between finite-dimensional spaces.
  let matrixMap : Matrix (Fin r) (Fin r) ℝ ≃L[ℝ] (V →L[ℝ] V) :=
    LinearEquiv.toContinuousLinearEquiv
      (Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv
  have hMatrix : ContMDiffOn (I.prod (𝓡 r)) 𝓘(ℝ, V →L[ℝ] V) ∞
      (fun p : B × OrthogonalSphere r ↦ matrixMap (A p.1)) (s ×ˢ Set.univ) :=
    matrixMap.contDiff.contMDiff.comp_contMDiffOn
      (hA.comp contMDiffOn_fst (fun _ hp ↦ hp.1))
  have hSphere : ContMDiff (I.prod (𝓡 r)) 𝓘(ℝ, W) ∞
      (fun p : B × OrthogonalSphere r ↦ p.2.val) :=
    contMDiff_coe_sphere.comp contMDiff_snd
  let split := WithLp.prodContinuousLinearEquiv 2 ℝ V ℝ
  have hHorizontal : ContMDiff (I.prod (𝓡 r)) 𝓘(ℝ, V) ∞
      (fun p : B × OrthogonalSphere r ↦ p.2.val.fst) :=
    (ContinuousLinearMap.fst ℝ V ℝ).contDiff.contMDiff.comp
      (split.contDiff.contMDiff.comp hSphere)
  have hVertical : ContMDiff (I.prod (𝓡 r)) 𝓘(ℝ, ℝ) ∞
      (fun p : B × OrthogonalSphere r ↦ p.2.val.snd) :=
    (ContinuousLinearMap.snd ℝ V ℝ).contDiff.contMDiff.comp
      (split.contDiff.contMDiff.comp hSphere)
  have hAmbient : ContMDiffOn (I.prod (𝓡 r)) 𝓘(ℝ, W) ∞ f (s ×ˢ Set.univ) :=
    split.symm.contDiff.contMDiff.comp_contMDiffOn
      ((hMatrix.clm_apply hHorizontal.contMDiffOn).prodMk_space hVertical.contMDiffOn)
  have hf (p : B × OrthogonalSphere r) : f p ∈ Metric.sphere (0 : W) 1 :=
    ((⟨A p.1, horth p.1⟩ : Matrix.orthogonalGroup (Fin r) ℝ) • p.2).property
  -- Restrict the smooth ambient family using the original sphere's stereographic charts.
  change ContMDiffOn (I.prod (𝓡 r)) (𝓡 r) ∞
    (fun p ↦ (⟨f p, hf p⟩ : OrthogonalSphere r)) (s ×ˢ Set.univ)
  rw [contMDiffOn_iff_target]
  refine ⟨?_, ?_⟩
  · intro p hp
    exact tendsto_subtype_rng.mpr (hAmbient.continuousOn p hp)
  intro v
  let U := (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    r (ne_zero_of_mem_unit_sphere (-v))).repr
  have hU : ContDiffOn ℝ ω U Set.univ := U.contDiff.contDiffOn
  have hChart := (hU.comp_inter contDiffOn_stereoToFun).contMDiffOn
  convert! (hChart.of_le le_top).comp' hAmbient using 1
  ext p
  have hfv : f p = -(v : W) ↔ inner (𝕜 := ℝ) (f p) (-(v : W)) = 1 := by
    have hnorm : ‖f p‖ = 1 := by simpa using hf p
    rw [inner_eq_one_iff_of_norm_eq_one hnorm]
    exact norm_eq_of_mem_sphere (-v)
  simp only [extChartAt_source, chartAt, ChartedSpace.chartAt, stereographic'_source,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
    Subtype.ext_iff, Set.mem_univ, and_true, Set.mem_ofPred_eq]
  change (p ∈ s ×ˢ Set.univ ∧ f p ≠ -(v : W)) ↔
    (p ∈ s ×ˢ Set.univ ∧ inner (𝕜 := ℝ) (-(v : W)) (f p) ≠ 1)
  apply and_congr Iff.rfl
  exact not_congr (hfv.trans (by rw [real_inner_comm]))

end AtiyahSinger
