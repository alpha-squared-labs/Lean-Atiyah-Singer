/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DiffeomorphTangentMetric
public import AtiyahSinger.Topology.TangentEmbeddingPushforward
public import AtiyahSinger.Topology.ThomDirectSum

/-!
# Pushforward by the actual tangent diffeomorphism

Public module ID: M2229.

The original normal quotient of a diffeomorphism has zero fibers. Every selected
normalized tube is consequently determined by its zero-section equation. The
positive zero-rank Thom unit cancels that zero-section transport and leaves the
actual tangent homeomorphism. No embedding composition or moving isotopy is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff TensorProduct

attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold
attribute [local instance] normalBundleTopology complexifiedNormalPullbackTopology

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [T2Space M] [T2Space N] [SecondCountableTopology M] [SecondCountableTopology N]

set_option backward.isDefEq.respectTransparency.types false in
/-- The original tangent embedding pushforward of a diffeomorphism is its native transport. -/
theorem tangentEmbeddingPushforward_diffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ e) (hp : IsProperMap e) :
    letI : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin n)) M).1
    letI : T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) N) :=
      (tangentBundle_topology (EuclideanSpace ℝ (Fin m)) N).1
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) _
    letI : LocallyCompactSpace (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) N) :=
      ChartedSpace.locallyCompactSpace
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) _
    tangentEmbeddingPushforward e.toContMDiffMap he hp =
      compactSupportKZeroHomeomorph (tangentDiffeomorph e) := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let TM := TangentBundle I M
  let TN := TangentBundle J N
  let f := e.toContMDiffMap
  let Te := tangentDiffeomorph e
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  -- The inverse differential proves full range on the original tangent fiber.
  have hright (x : M) : (mfderiv I J e x).comp (mfderiv J I e.symm (e x)) =
      ContinuousLinearMap.id ℝ (TangentSpace J (e x)) := by
    have h (y : N) : (mfderiv I J e (e.symm y)).comp (mfderiv J I e.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace J y) := by
      rw [← mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) _)
        (e.symm.contMDiff.mdifferentiable (by simp) _)]
      rw [show (e : M → N) ∘ e.symm = id from funext e.apply_symm_apply, mfderiv_id]
    have hd : mfderiv I J e (e.symm (e x)) = mfderiv I J e x := by
      congr 1
      exact e.symm_apply_apply x
    exact hd ▸ h (e x)
  have hnormal (x : M) : Subsingleton (NormalBundle I J f x) := by
    change Subsingleton (TangentSpace J (e x) ⧸
      LinearMap.range (mfderiv I J e x).toLinearMap)
    have hr : LinearMap.range (mfderiv I J e x).toLinearMap = ⊤ := by
      apply LinearMap.range_eq_top.mpr
      intro v
      exact ⟨mfderiv J I e.symm (e x) v, DFunLike.congr_fun (hright x) v⟩
    rw [hr]
    infer_instance
  let (x : M) : Subsingleton (NormalBundle I J f x) := hnormal x
  let : ∀ z : TM, Subsingleton (ComplexifiedNormalPullback f z) := fun z ↦ by
    let := hnormal z.proj
    change Subsingleton (ℂ ⊗[ℝ] NormalBundle I J f z.proj)
    infer_instance
  let : ComplexBundle.IsFiniteRank (ComplexifiedNormalPullback f) :=
    isFiniteRank_complexifiedNormalPullback f he.isImmersion
  -- Zero fibers determine every selected tube from its original zero-section equation.
  have hWith (S : TangentNormalSplitting f he)
      (T : TubularNeighborhood (smoothTangentMap f) (isImmersion_smoothTangentMap f he))
      (h : ComplexBundle.ContinuousHermitianMetric (ComplexifiedNormalPullback f)) :
      tangentEmbeddingPushforwardWith f he S T h = compactSupportKZeroHomeomorph Te := by
    let X := TotalSpace Unit (ComplexifiedNormalPullback f)
    let νT := NormalBundle 𝓘(ℝ, E × E) 𝓘(ℝ, F × F) (smoothTangentMap f)
    let VT := NormalModel (E × E) (F × F)
    let (z : TM) : Subsingleton (νT z) :=
      ⟨fun v w ↦ (S.equiv z).injective (Subsingleton.elim _ _)⟩
    let τ := tangentEmbeddingTubularMap f he S T
    let hτ := isOpenEmbedding_tangentEmbeddingTubularMap f he S T
    let : T2Space X := hτ.isEmbedding.t2Space
    let : LocallyCompactSpace X := hτ.locallyCompactSpace
    let Z := ComplexBundle.zeroSectionHomeomorph (E := ComplexifiedNormalPullback f)
    have hzero (z : TM) : τ ⟨z, 0⟩ = Te z := by
      have hC : complexifiedNormalTotalHomeomorph f he S ⟨z, 0⟩ =
          (⟨z, 0⟩ : TotalSpace VT νT) := by
        apply TotalSpace.ext
        · rfl
        · exact heq_of_eq (Subsingleton.elim _ _)
      change T.totalMap (smoothTangentMap f) (isImmersion_smoothTangentMap f he)
        (complexifiedNormalTotalHomeomorph f he S ⟨z, 0⟩) = Te z
      rw [hC]
      exact T.map_zero z
    have hmap : (τ : X → TN) = Te ∘ Z.symm := by
      funext z
      have hz : z = (⟨z.proj, 0⟩ : X) :=
        TotalSpace.ext rfl (heq_of_eq (Subsingleton.elim _ _))
      exact (congrArg τ hz).trans (hzero z.proj)
    -- The positive zero-rank Thom unit cancels precisely the inverse zero-section transport.
    have hpush : compactSupportKZeroOpenPushforward τ hτ =
        (compactSupportKZeroHomeomorph Te).comp (compactSupportKZeroHomeomorph Z.symm) := by
      rw [← compactSupportKZeroOpenPushforward_homeomorph Te,
        ← compactSupportKZeroOpenPushforward_homeomorph Z.symm,
        ← compactSupportKZeroOpenPushforward_comp]
      congr 1
    change (compactSupportKZeroOpenPushforward τ hτ).comp h.supportedThomHom = _
    rw [ComplexBundle.ContinuousHermitianMetric.supportedThomHom_zeroRank, hpush,
      AddMonoidHom.comp_assoc, compactSupportKZeroHomeomorph_symm]
    rfl
  unfold tangentEmbeddingPushforward
  exact hWith _ _ _

end AtiyahSinger
