/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantIndexExcision
public import AtiyahSinger.Geometry.FiniteDimensionalLocalDiffeomorph
public import AtiyahSinger.Geometry.LocalDiffeomorphTangentMetric
public import AtiyahSinger.Geometry.OpenManifoldDerivative
public import AtiyahSinger.Topology.OpenCotangentKZero
public import AtiyahSinger.Topology.TangentCotangentKZero

/-!
# Musical naturality for the actual open tangent and cotangent maps

Public module ID: M2228.

The derivative of a specified open embedding and its inverse-dual cotangent
lift give the same compact-support K map after musical identification.
Pull back the target metric by that very differential; the resulting square
commutes on actual vectors. Proper metric independence removes the auxiliary
source metric. This is the square needed to apply analytic excision to the
original tangent Thom-to-tube pushforward.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

variable {n : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [IsManifold (𝓡 n) ∞ O] [T2Space O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in

/-- Musical K transport commutes with the actual differential of an open embedding. -/
theorem tangentCotangentKZeroEquiv_openEmbedding
    (U : Opens M) (f : O ≃ₘ⟮𝓡 n, 𝓡 n⟯ U)
    (g : SmoothTangentMetric (n := n) (M := O))
    (h : SmoothTangentMetric (n := n) (M := M)) :
    letI := g.flatHomeomorph.symm.t2Space
    letI := g.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
    letI := h.flatHomeomorph.symm.t2Space
    letI := h.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
    ∃ hT : IsOpenEmbedding (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (f x : M))),
      (cotangentKZeroOpenEmbedding U f).comp (tangentCotangentKZeroEquiv g).toAddMonoidHom =
        (tangentCotangentKZeroEquiv h).toAddMonoidHom.comp
          (compactSupportKZeroOpenPushforward
            (tangentMap (𝓡 n) (𝓡 n) (fun x : O ↦ (f x : M))) hT) := by
  classical
  let := g.flatHomeomorph.symm.t2Space
  let := g.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
  let := h.flatHomeomorph.symm.t2Space
  let := h.flatHomeomorph.isOpenEmbedding.locallyCompactSpace
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let j : ContMDiffMap I I O M ∞ :=
    ⟨fun x ↦ (f x : M), contMDiff_subtype_val.comp f.contMDiff⟩
  have hDj (x : O) : mfderiv I I j x = mfderiv I I f x := by
    change mfderiv I I ((Subtype.val : U → M) ∘ f) x = _
    rw [mfderiv_comp x ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) (f x))
      (f.contMDiff.mdifferentiable (by simp) x), mfderiv_openSubtype_val]
    exact ContinuousLinearMap.id_comp _
  have hj : IsLocalDiffeomorph I I ∞ j :=
    isLocalDiffeomorph_of_isInvertible_mfderiv j (fun x ↦ by
      rw [hDj]
      exact f.isInvertible_mfderiv (by simp))
  let q := h.comapLocalDiffeomorph j hj
  let T := tangentMap I I j
  let C := cotangentOpenEmbeddingMap U f
  have hC : IsOpenEmbedding C := isOpenEmbedding_cotangentOpenEmbeddingMap U f
  -- The inverse differential of f cancels exactly the differential used in the pulled metric.
  have hright (x : O) : (mfderiv I I f x).comp (mfderiv I I f.symm (f x)) =
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
    have h₀ (y : U) : (mfderiv I I f (f.symm y)).comp (mfderiv I I f.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace I y) := by
      rw [← mfderiv_comp y (f.contMDiff.mdifferentiable (by simp) _)
        (f.symm.contMDiff.mdifferentiable (by simp) _)]
      rw [show (f : O → U) ∘ f.symm = id from funext f.apply_symm_apply, mfderiv_id]
    have hd : mfderiv I I f (f.symm (f x)) = mfderiv I I f x := by
      congr 1
      exact f.symm_apply_apply x
    exact hd ▸ h₀ (f x)
  have hsquare : (C : CotangentTotalSpace (n := n) (M := O) →
      CotangentTotalSpace (n := n) (M := M)) ∘ q.flatHomeomorph = h.flatHomeomorph ∘ T := by
    funext z
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      ext w
      change h.inner (j z.proj) (mfderiv I I j z.proj z.snd)
        (mfderiv I I j z.proj (mfderiv I I f.symm (f z.proj) w)) =
          h.inner (j z.proj) (mfderiv I I j z.proj z.snd) w
      rw [hDj]
      exact congrArg (h.inner (j z.proj) (mfderiv I I f z.proj z.snd))
        (DFunLike.congr_fun (hright z.proj) w)
  -- The square also proves openness of this same derivative map on the whole tangent bundle.
  have hTmap : T = h.flatHomeomorph.symm ∘ C ∘ q.flatHomeomorph := by
    funext z
    apply h.flatHomeomorph.injective
    exact (congrFun hsquare z).symm.trans (h.flatHomeomorph.apply_symm_apply _).symm
  have hT : IsOpenEmbedding T := by
    rw [hTmap]
    exact h.flatHomeomorph.symm.isOpenEmbedding.comp (hC.comp q.flatHomeomorph.isOpenEmbedding)
  refine ⟨hT, ?_⟩
  have hmap : compactSupportKZeroOpenPushforward C hC = cotangentKZeroOpenEmbedding U f := by
    change compactSupportKZeroOpenPushforward (cotangentOpenInclusion U ∘ cotangentDiffeomorph f)
      _ = _
    rw [compactSupportKZeroOpenPushforward_comp (cotangentDiffeomorph f)
      (cotangentDiffeomorph f).isOpenEmbedding (cotangentOpenInclusion U)
      (isOpenEmbedding_cotangentOpenInclusion U),
      compactSupportKZeroOpenPushforward_homeomorph]
    rfl
  have hK : (compactSupportKZeroOpenPushforward C hC).comp
      (compactSupportKZeroHomeomorph q.flatHomeomorph) =
        (compactSupportKZeroHomeomorph h.flatHomeomorph).comp
          (compactSupportKZeroOpenPushforward T hT) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph q.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph h.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_comp, ← compactSupportKZeroOpenPushforward_comp]
    congr 1
  -- The source metric changes by the existing proper musical homotopy, on the same base.
  rw [tangentCotangentKZeroEquiv_independent_metric g q]
  rw [hmap] at hK
  exact hK

end AtiyahSinger
