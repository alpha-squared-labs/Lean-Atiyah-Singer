/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportProductLaws
public import AtiyahSinger.Topology.LinearEmbeddingPushforward
public import AtiyahSinger.Topology.TangentEmbeddingOpenRestriction

/-!
# Point pushforward in an actual smooth chart

Public module ID: M1989.

The original tangent pushforward of the positive point unit is the positive
exterior Bott class extended through the derivative of the given chart. Open
naturality reduces this to the already proved linear coordinate inclusion;
the external-product unit law removes the zero-dimensional tangent factor.
The real coordinate precedes the imaginary vertical coordinate throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

set_option maxHeartbeats 1200000 in
-- Retain the original zero-dimensional point and both actual tangent-coordinate maps.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A point inclusion in an open smooth chart has the positive exterior tangent Thom class. -/
theorem tangentEmbeddingPushforward_pointChart (r : ℕ)
    {N : Type*} [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin r)) N]
    [IsManifold (𝓡 r) ∞ N] [T2Space N] [SecondCountableTopology N]
    (j : ContMDiffMap (𝓡 0) (𝓡 r) (EuclideanSpace ℝ (Fin 0)) N ∞)
    (hj : IsSmoothEmbedding (𝓡 0) (𝓡 r) ∞ j) (hp : IsProperMap j)
    (c : ContMDiffMap (𝓡 r) (𝓡 r) (EuclideanSpace ℝ (Fin r)) N ∞)
    (hc : IsLocalDiffeomorph (𝓡 r) (𝓡 r) ∞ c) (hinj : Function.Injective c)
    (hzero : c 0 = j 0)
    (p : TangentBundle (𝓡 0) (EuclideanSpace ℝ (Fin 0)) ≃ₜ PUnit.{1}) :
    letI : T2Space (TangentBundle (𝓡 0) (EuclideanSpace ℝ (Fin 0))) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin 0)) (EuclideanSpace ℝ (Fin 0))).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 0) (EuclideanSpace ℝ (Fin 0))) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 0)) _
    letI : T2Space (TangentBundle (𝓡 r) N) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin r)) N).1
    letI : LocallyCompactSpace (TangentBundle (𝓡 r) N) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r)) _
    ∃ htube : IsOpenEmbedding (fun z : EuclideanSpace ℂ (Fin r) ↦
        (⟨c (WithLp.toLp 2 (fun i ↦ (z i).re)),
          mfderiv (𝓡 r) (𝓡 r) c (WithLp.toLp 2 (fun i ↦ (z i).re))
            (WithLp.toLp 2 (fun i ↦ (z i).im))⟩ : TangentBundle (𝓡 r) N)),
      tangentEmbeddingPushforward j hj hp
          (compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne) =
        compactSupportKZeroOpenPushforward _ htube
          (exteriorBottClass (EuclideanSpace ℂ (Fin r))) := by
  classical
  let E := EuclideanSpace ℝ (Fin 0)
  let F := EuclideanSpace ℝ (Fin r)
  let W := EuclideanSpace ℂ (Fin r)
  let T0 := TangentBundle (𝓡 0) E
  let TR := TangentBundle (𝓡 r) F
  let TN := TangentBundle (𝓡 r) N
  let : T2Space T0 := (tangentBundle_topology E E).1
  let : T2Space TR := (tangentBundle_topology F F).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : LocallyCompactSpace T0 := ChartedSpace.locallyCompactSpace (E × E) T0
  let : LocallyCompactSpace TR := ChartedSpace.locallyCompactSpace (F × F) TR
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let f : ContMDiffMap (𝓡 0) (𝓡 r) E F ∞ := ⟨fun _ ↦ 0, contMDiff_const⟩
  have hf : IsSmoothEmbedding (𝓡 0) (𝓡 r) ∞ f := by
    refine ⟨isImmersion_of_injective_mfderiv f ?_, IsEmbedding.of_subsingleton f⟩
    intro x
    change Function.Injective (show E →L[ℝ] F from mfderiv (𝓡 0) (𝓡 r) f x)
    exact Function.injective_of_subsingleton _
  have hfp : IsProperMap f := f.contMDiff.continuous.isProperMap
  let a : F ≃L[ℝ] E × F := (ContinuousLinearEquiv.uniqueProd ℝ F E).symm
  have hlinear := tangentEmbeddingPushforward_linear r f hf hfp a (fun _ ↦ rfl)
  let Q : W ≃ₜ TR := (PiLp.homeomorph 2 (fun _ : Fin r ↦ ℂ)).trans
    (euclideanTangentComplexHomeomorph r).symm
  let Tc : C(TR, TN) := ⟨smoothTangentMap c, (smoothTangentMap c).contMDiff.continuous⟩
  have hTc : IsOpenEmbedding Tc := isOpenEmbedding_smoothTangentMap c hc hinj
  let tube : W → TN := Tc ∘ Q
  have htube : IsOpenEmbedding tube := hTc.comp Q.isOpenEmbedding
  refine ⟨htube, ?_⟩
  let b := exteriorBottClass W
  let b0 := compactSupportKZeroHomeomorph p.symm compactSupportKZeroPointOne
  -- The original open square compares j with the literal zero-to-Euclidean inclusion.
  let id0 := ContMDiffMap.id (I := 𝓡 0) (M := E) (n := ∞)
  have hsquare := tangentEmbeddingPushforward_open_naturality j hj hp f hf hfp id0
    (Diffeomorph.refl (𝓡 0) E ∞).isLocalDiffeomorph Function.injective_id c hc hinj
    (fun x ↦ by
      change j x = c 0
      exact (congrArg j (Subsingleton.elim x 0)).trans hzero.symm)
  have hid : (smoothTangentMap id0 : T0 → T0) = id := by
    funext z
    change tangentMap (𝓡 0) (𝓡 0) id z = z
    rw [tangentMap_id]
    rfl
  have hidK : compactSupportKZeroOpenPushforward (smoothTangentMap id0)
      (isOpenEmbedding_smoothTangentMap id0
        (Diffeomorph.refl (𝓡 0) E ∞).isLocalDiffeomorph Function.injective_id) =
        AddMonoidHom.id (CompactSupportKZero T0) := by
    simpa only [hid] using compactSupportKZeroOpenPushforward_id (X := T0)
  have hsq := DFunLike.congr_fun hsquare b0
  change compactSupportKZeroOpenPushforward Tc hTc (tangentEmbeddingPushforward f hf hfp b0) =
    tangentEmbeddingPushforward j hj hp
      (compactSupportKZeroOpenPushforward (smoothTangentMap id0) _ b0) at hsq
  rw [hidK, AddMonoidHom.id_apply] at hsq
  -- Remove the actual singleton factor by the external-product unit, preserving both coordinates.
  let H := linearEmbeddingTangentProductHomeomorph r a
  let R := p.symm.prodCongr (Homeomorph.refl W)
  let L := Homeomorph.uniqueProd PUnit.{1} W
  have hprod := compactSupportKZeroExternalProduct_homeomorph p.symm (Homeomorph.refl W)
    compactSupportKZeroPointOne b
  have hidW : compactSupportKZeroHomeomorph (Homeomorph.refl W) b = b := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph]
    exact DFunLike.congr_fun (compactSupportKZeroOpenPushforward_id (X := W)) b
  rw [hidW] at hprod
  have hcoord : (H : T0 × W → TR) ∘ R = (Q : W → TR) ∘ L := by
    funext z
    rfl
  have hnormal : tangentEmbeddingPushforward f hf hfp b0 =
      compactSupportKZeroHomeomorph Q b := by
    rw [hlinear]
    change compactSupportKZeroHomeomorph H (compactSupportKZeroExternalProduct b0 b) = _
    rw [← hprod]
    rw [← compactSupportKZeroOpenPushforward_homeomorph H,
      ← compactSupportKZeroOpenPushforward_homeomorph R,
      ← AddMonoidHom.comp_apply,
      ← compactSupportKZeroOpenPushforward_comp R R.isOpenEmbedding H H.isOpenEmbedding]
    simp only [hcoord]
    rw [compactSupportKZeroOpenPushforward_comp L L.isOpenEmbedding Q Q.isOpenEmbedding,
      AddMonoidHom.comp_apply, compactSupportKZeroOpenPushforward_homeomorph L,
      compactSupportKZeroOpenPushforward_homeomorph Q,
      compactSupportKZeroExternalProduct_one_left]
  change tangentEmbeddingPushforward j hj hp b0 = compactSupportKZeroOpenPushforward tube htube b
  rw [← hsq, hnormal, ← compactSupportKZeroOpenPushforward_homeomorph Q,
    ← AddMonoidHom.comp_apply, ← compactSupportKZeroOpenPushforward_comp Q Q.isOpenEmbedding Tc hTc]

end AtiyahSinger
