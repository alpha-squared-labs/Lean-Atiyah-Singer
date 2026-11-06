/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OrthogonalFixedPoint
public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.PointChartPushforward
public import AtiyahSinger.Topology.SphereTangentKTheory
public import AtiyahSinger.Topology.TangentEmbeddingPushforward

/-!
# The pushforward of any specified orthogonal fixed-point inclusion

Public module ID: M1976.

SG III.12 and III.13, printed pp.241 and 253. The map is the actual
positive exterior Thom operator followed by open extension through the tangent
chart constructed from the specified inclusion. It is not defined by the
desired index, by a selected pole index, or by a preassigned normalization.

The first comparison identifies this actual map with an existing canonical
pole pushforward. The second compares its underlying positive unit with the
existing ordinary tangentEmbeddingPushforward of the very same inclusion.
The latter retains the actual normal quotient and the ordered complexification
used by the general embedding construction. Thus the fixed-point interface is
connected to the original embedding geometry, as well as to the canonical
classes with their specified normalization. All ranks, both
fixed points and arbitrary representation coefficients are retained.
The comparisons retain these actual maps and their original support classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Manifold Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere
  continuousSMul_orthogonalSphereTangent tangentBundleFullChartedSpace

set_option maxSynthPendingDepth 35

variable {r : ℕ}

/-- Positive Thom multiplication and actual open extension for the specified fixed-point map. -/
def orthogonalSphereFixedPointPushforward
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ) →ₗ[
      RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)]
      EquivariantSupportTripleKZero (Matrix.orthogonalGroup (Fin r) ℝ)
        (TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
  letI := compactSpace_orthogonalGroup r
  letI := (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
  letI := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r))
    (TangentBundle (𝓡 r) (OrthogonalSphere r))
  -- Use the actual chart of j and the original positive exterior class.
  exact (equivariantSupportTripleKZeroOpenLinearMap
    (orthogonalSphereFixedPointTangentTube j hj)
    (orthogonalSphereFixedPointTangentMap_properties j hj).1
    (orthogonalSphereFixedPointTangentMap_properties j hj).2.2).comp
      (equivariantBottLinearMap (orthogonalComplexification_unitary r))

/-- Any specified fixed-point inclusion and its full pushforward agree with one actual pole map. -/
theorem orthogonalSphereFixedPointPushforward_eq_pole
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    ∃ b : Bool, (∀ x : EuclideanSpace ℝ (Fin 0), j x = orthogonalSpherePole r b) ∧
      orthogonalSphereFixedPointPushforward j hj = orthogonalSpherePolePushforward r b := by
  classical
  let V := EuclideanSpace ℝ (Fin r)
  let W := OrthogonalSphereAmbient r
  let f := orthogonalSphereFixedPointChart j hj
  have hf := (exists_orthogonalSphereFixedPointChart j hj).choose_spec
  have hzero : f 0 = j 0 := hf.2.1
  have hformula (u : V) : (f u : W) =
      WithLp.toLp 2 (((2 : ℝ) / (1 + ‖u‖ ^ 2)) • u,
        (j 0).val.snd * (1 - ‖u‖ ^ 2) / (1 + ‖u‖ ^ 2)) := hf.1 u
  -- The selected chart's exact formula identifies the same fixed pole.
  have hhorizontal : (j 0).val.fst = 0 := by
    have h := congrArg (fun w : W ↦ w.fst) (hformula 0)
    simpa [hzero] using h
  have hheight : (j 0).val.snd = 1 ∨ (j 0).val.snd = -1 := by
    have hn : ‖(j 0).val‖ = 1 := norm_eq_of_mem_sphere (j 0)
    have hs := WithLp.prod_norm_sq_eq_of_L2 (j 0).val
    rw [hn, hhorizontal, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add] at hs
    have hsq : (j 0).val.snd ^ 2 = 1 := by
      simpa only [Real.norm_eq_abs, sq_abs, one_pow] using hs.symm
    exact sq_eq_one_iff.mp hsq
  obtain ⟨b, hb⟩ : ∃ b : Bool, j 0 = orthogonalSpherePole r b := by
    rcases hheight with hp | hp
    · refine ⟨true, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
    · refine ⟨false, ?_⟩
      apply Subtype.ext
      apply WithLp.ofLp_injective 2
      apply Prod.ext
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hhorizontal
      · simpa [orthogonalSpherePole, orthogonalSphereNorth] using hp
  have hchart : (orthogonalSphereFixedPointChart j hj : V → OrthogonalSphere r) =
      (orthogonalSphereNormalizedChart r b).symm := by
    funext u
    apply Subtype.ext
    change (f u : W) = _
    rw [hformula, orthogonalSphereNormalizedChart_inverse_formula, hb]
    cases b <;> simp [orthogonalSpherePole, orthogonalSphereNorth]
  -- Equality of the whole charts identifies the same actual derivative tube.
  have htangent : orthogonalSphereFixedPointTangentMap j hj =
      (orthogonalSphereTangentChart r b : EuclideanSpace ℂ (Fin r) →
        TangentBundle (𝓡 r) (OrthogonalSphere r)) := by
    funext z
    exact congrArg (fun g : V → OrthogonalSphere r ↦ tangentMap (𝓡 r) (𝓡 r) g
      (⟨WithLp.toLp 2 (fun i ↦ (z i).re), WithLp.toLp 2 (fun i ↦ (z i).im)⟩ :
        TangentBundle (𝓡 r) V)) hchart
  have htube : orthogonalSphereFixedPointTangentTube j hj =
      orthogonalSphereTangentChart r b := by
    apply ContinuousMap.ext
    exact congrFun htangent
  refine ⟨b, ?_, ?_⟩
  · intro x
    exact (congrArg j (Subsingleton.elim x 0)).trans hb
  · -- The full representation-linear maps use the same Bott class and open extension.
    unfold orthogonalSphereFixedPointPushforward orthogonalSpherePolePushforward
    congr 2

set_option maxHeartbeats 1200000 in
-- Compare the native point homeomorphism, actual sphere chart and both support models.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Forgetting the action gives the original tangent embedding pushforward of the positive unit. -/
theorem orthogonalSphereFixedPointPushforward_forget
    (j : ContMDiffMap (𝓡 0) (𝓡 r)
      (EuclideanSpace ℝ (Fin 0)) (OrthogonalSphere r) ∞)
    (hj : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
      (x : EuclideanSpace ℝ (Fin 0)), A • j x = j x) :
    letI : T2Space (TangentBundle (𝓡 0) (EuclideanSpace ℝ (Fin 0))) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin 0))
        (EuclideanSpace ℝ (Fin 0))).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 0) (EuclideanSpace ℝ (Fin 0))) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) _
    letI : T2Space (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 r) (OrthogonalSphere r)) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
    letI : Unique
        (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0))) :=
      { default := (0, 0)
        uniq := fun x ↦ by
          apply Prod.ext
          · ext i
            exact Fin.elim0 i
          · ext i
            exact Fin.elim0 i }
    let pointHomeomorph :=
      (tangentBundleModelSpaceHomeomorph (𝓡 0)).trans
        (Homeomorph.homeomorphOfUnique
          (ModelProd (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0))) PUnit.{1})
    supportTripleKZeroToCompactSupport
        (equivariantSupportTripleKZeroForget (orthogonalSphereFixedPointPushforward j hj 1)) =
      tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
        (orthogonalSpherePointEmbedding_properties j).2
        (compactSupportKZeroHomeomorph pointHomeomorph.symm compactSupportKZeroPointOne) := by
  classical
  let E := EuclideanSpace ℝ (Fin 0)
  let F := EuclideanSpace ℝ (Fin r)
  let W := EuclideanSpace ℂ (Fin r)
  let S := OrthogonalSphere r
  let T0 := TangentBundle (𝓡 0) E
  let TS := TangentBundle (𝓡 r) S
  let := compactSpace_orthogonalGroup r
  let : T2Space T0 := (tangentBundle_topology E E).1
  let : LocallyCompactSpace T0 := ChartedSpace.locallyCompactSpace (E × E) T0
  let : T2Space TS := (tangentBundle_topology F S).1
  let : LocallyCompactSpace TS := ChartedSpace.locallyCompactSpace (F × F) TS
  let : Unique (ModelProd E E) :=
    { default := (0, 0)
      uniq := fun x ↦ by
        apply Prod.ext
        · ext i
          exact Fin.elim0 i
        · ext i
          exact Fin.elim0 i }
  let p : T0 ≃ₜ PUnit.{1} := (tangentBundleModelSpaceHomeomorph (𝓡 0)).trans
    (Homeomorph.homeomorphOfUnique (ModelProd E E) PUnit.{1})
  change supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (orthogonalSphereFixedPointPushforward j hj 1)) =
    tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
      (orthogonalSpherePointEmbedding_properties j).2
      (compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne)
  -- The already identified pole uses exactly the chart of this specified fixed inclusion.
  obtain ⟨b, hjb, hpush⟩ := orthogonalSphereFixedPointPushforward_eq_pole j hj
  let e := orthogonalSphereNormalizedChart r b
  have he := orthogonalSphereNormalizedChart_properties r b
  have hes := orthogonalSphereNormalizedChart_smooth r b
  let c : ContMDiffMap (𝓡 r) (𝓡 r) F S ∞ := ⟨e.symm, hes.2⟩
  let d : PartialDiffeomorph (𝓡 r) (𝓡 r) F S ∞ :=
    { toPartialEquiv := e.symm.toPartialEquiv
      open_source := e.open_target
      open_target := e.open_source
      contMDiffOn_toFun := hes.2.contMDiffOn
      contMDiffOn_invFun := hes.1 }
  have hc : IsLocalDiffeomorph (𝓡 r) (𝓡 r) ∞ c := by
    intro x
    apply d.isLocalDiffeomorphAt _ _ _
    change x ∈ e.target
    rw [he.2.1]
    trivial
  have hinj : Function.Injective c := by
    intro x y hxy
    have hx : x ∈ e.target := he.2.1 ▸ Set.mem_univ x
    have hy : y ∈ e.target := he.2.1 ▸ Set.mem_univ y
    exact (e.symm.injOn hx hy) hxy
  have hzero : c 0 = j 0 := he.2.2.1.trans (hjb 0).symm
  obtain ⟨htube, hpoint⟩ := tangentEmbeddingPushforward_pointChart r j
    (orthogonalSpherePointEmbedding_properties j).1
    (orthogonalSpherePointEmbedding_properties j).2 c hc hinj hzero p
  have hpoint' : tangentEmbeddingPushforward j (orthogonalSpherePointEmbedding_properties j).1
      (orthogonalSpherePointEmbedding_properties j).2
      (compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne) =
        compactSupportKZeroOpenPushforward (orthogonalSphereTangentChart r b)
          (orthogonalSphereTangentChart_isOpenEmbedding r b) (exteriorBottClass W) := hpoint
  rw [hpoint', hpush]
  -- Forgetting preserves the original exterior triple and the same open chart.
  change supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget
    (equivariantSupportTripleKZeroOpenPushforward (orthogonalSphereTangentChart r b)
      (orthogonalSphereTangentChart_isOpenEmbedding r b)
      (orthogonalSphereTangentChart_equivariant r b)
      ((1 : RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ)) •
        equivariantExteriorBottClass (orthogonalComplexification_unitary r)))) = _
  rw [one_smul, equivariantSupportTripleKZeroOpenPushforward_forget,
    equivariantExteriorBottClass_forget]

end AtiyahSinger
