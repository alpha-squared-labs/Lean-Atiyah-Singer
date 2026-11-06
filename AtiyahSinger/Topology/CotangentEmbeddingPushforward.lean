/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.OpenCotangentKZero
public import AtiyahSinger.Topology.TangentCotangentKZero
public import AtiyahSinger.Topology.TangentDiffeomorphPushforward
public import AtiyahSinger.Topology.TangentEmbeddingComposition

/-!
# The actual cotangent embedding pushforward

Public module ID: M1746.

Transport the existing tangent embedding pushforward through the musical
compact-support equivalences at its source and target. The result acts on the
original cotangent K groups and is independent of the supplied smooth metrics.
Successive pushforwards compose using the same middle metric and its exact
inverse, so the intermediate transport cancels on the original middle group.

This is the cotangent realization of SG's tangent embedding construction in
III.12 (12.7), p.241, and III.13, pp.243 and 247, using the metric identification
in II.5, p.113. The proper smooth embedding, normal Thom construction and
positive complex convention are those already used by the tangent pushforward.
No direct differential map from arbitrary source covectors to target covectors
is asserted. The tangent construction uses the established tubular-neighborhood
existence theorem for the same proper smooth embedding and quotient normal.
The diffeomorphism comparison uses zero-rank Thom transport and a pulled-back
smooth metric; it does not require the embedding composition theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold Topology
open scoped ContDiff

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent
attribute [local instance] tangentBundleFullChartedSpace tangentBundle_full_isManifold

variable {n m k : ℕ} {M N P : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace P] [ChartedSpace (EuclideanSpace ℝ (Fin k)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ P]
  [T2Space M] [T2Space N] [T2Space P]
  [SecondCountableTopology M] [SecondCountableTopology N] [SecondCountableTopology P]

/-- The original tangent pushforward transported to the actual cotangent K groups. -/
def cotangentEmbeddingPushforward
    (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (hp : IsProperMap f)
    (g : SmoothTangentMetric (n := n) (M := M))
    (h : SmoothTangentMetric (n := m) (M := N)) :
    CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+
      CompactSupportKZero (CotangentTotalSpace (n := m) (M := N)) :=
  (tangentCotangentKZeroEquiv h).toAddMonoidHom.comp
    ((tangentEmbeddingPushforward f hf hp).comp
      (tangentCotangentKZeroEquiv g).symm.toAddMonoidHom)

/-- Both supplied metrics can change without changing the actual cotangent pushforward. -/
theorem cotangentEmbeddingPushforward_independent_metric
    (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      M N ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f) (hp : IsProperMap f)
    (g₀ g₁ : SmoothTangentMetric (n := n) (M := M))
    (h₀ h₁ : SmoothTangentMetric (n := m) (M := N)) :
    cotangentEmbeddingPushforward f hf hp g₀ h₀ =
      cotangentEmbeddingPushforward f hf hp g₁ h₁ := by
  -- The specified musical equivalences agree at both ends, including their exact inverses.
  have hsource := tangentCotangentKZeroEquiv_independent_metric g₀ g₁
  have htarget := tangentCotangentKZeroEquiv_independent_metric h₀ h₁
  -- Substitute in the original conjugation while retaining the same tangent pushforward.
  unfold cotangentEmbeddingPushforward
  rw [hsource, htarget]

/-- Cotangent embedding pushforwards compose with the same middle musical identification. -/
theorem cotangentEmbeddingPushforward_comp
    (f : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      M N ∞)
    (g : ContMDiffMap 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, EuclideanSpace ℝ (Fin k))
      N P ∞)
    (hf : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ f)
    (hg : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin k)) ∞ g)
    (hpf : IsProperMap f) (hpg : IsProperMap g)
    (gM : SmoothTangentMetric (n := n) (M := M))
    (gN : SmoothTangentMetric (n := m) (M := N))
    (gP : SmoothTangentMetric (n := k) (M := P)) :
    cotangentEmbeddingPushforward (g.comp f) (isSmoothEmbedding_comp f g hf hg)
        (hpg.comp hpf) gM gP =
      (cotangentEmbeddingPushforward g hg hpg gN gP).comp
        (cotangentEmbeddingPushforward f hf hpf gM gN) := by
  -- Use the same middle musical equivalence; its inverse cancels before composition.
  unfold cotangentEmbeddingPushforward
  rw [tangentEmbeddingPushforward_comp f g hf hg hpf hpg]
  ext a
  simp only [AddMonoidHom.comp_apply, AddEquiv.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, AddEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 600000 in
-- Compare the same native tangent, dual and pulled-metric instances in the musical square.
/-- For a diffeomorphism, the cotangent pushforward is its original inverse-dual transport. -/
theorem cotangentEmbeddingPushforward_diffeomorph
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin m))⟯ N)
    (he : IsSmoothEmbedding 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ e) (hp : IsProperMap e)
    (g : SmoothTangentMetric (n := n) (M := M))
    (h : SmoothTangentMetric (n := m) (M := N)) :
    cotangentEmbeddingPushforward e.toContMDiffMap he hp g h =
      (cotangentKZeroDiffeomorph e).toAddMonoidHom := by
  /- The actual tangent pushforward is transport by the tangent diffeomorphism,
  because its original normal quotient has zero fibers. Pull back the target
  metric by that same differential, identify the resulting musical square on
  actual covectors, then remove this metric choice by the proved proper metric
  homotopy. No compactness or embedding composition is needed. -/
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let F := EuclideanSpace ℝ (Fin m)
  let I := 𝓘(ℝ, E)
  let J := 𝓘(ℝ, F)
  let TM := TangentBundle I M
  let TN := TangentBundle J N
  let : T2Space TM := (tangentBundle_topology E M).1
  let : T2Space TN := (tangentBundle_topology F N).1
  let : LocallyCompactSpace TM := ChartedSpace.locallyCompactSpace (E × E) TM
  let : LocallyCompactSpace TN := ChartedSpace.locallyCompactSpace (F × F) TN
  let Te := tangentDiffeomorph e
  let q := h.comapDiffeomorph e
  -- The original derivative and inverse derivative cancel on each target fiber.
  have hright (x : M) : (mfderiv I J e x).comp (mfderiv J I e.symm (e x)) =
      ContinuousLinearMap.id ℝ (TangentSpace J (e x)) := by
    have h₀ (y : N) : (mfderiv I J e (e.symm y)).comp (mfderiv J I e.symm y) =
        ContinuousLinearMap.id ℝ (TangentSpace J y) := by
      rw [← mfderiv_comp y (e.contMDiff.mdifferentiable (by simp) _)
        (e.symm.contMDiff.mdifferentiable (by simp) _)]
      rw [show (e : M → N) ∘ e.symm = id from funext e.apply_symm_apply, mfderiv_id]
    have hd : mfderiv I J e (e.symm (e x)) = mfderiv I J e x := by
      congr 1
      exact e.symm_apply_apply x
    exact hd ▸ h₀ (e x)
  -- The pulled-back metric gives precisely the original inverse-dual covector lift.
  have hsquare : q.flatHomeomorph.trans (cotangentDiffeomorph e) =
      Te.trans h.flatHomeomorph := by
    apply Homeomorph.ext
    intro z
    apply TotalSpace.ext
    · rfl
    · apply heq_of_eq
      ext w
      change h.inner (e z.proj) (mfderiv I J e z.proj z.snd)
          (mfderiv I J e z.proj (mfderiv J I e.symm (e z.proj) w)) =
        h.inner (e z.proj) (mfderiv I J e z.proj z.snd) w
      exact congrArg (h.inner (e z.proj) (mfderiv I J e z.proj z.snd))
        (DFunLike.congr_fun (hright z.proj) w)
  have hpush : (compactSupportKZeroHomeomorph (cotangentDiffeomorph e)).comp
        (compactSupportKZeroHomeomorph q.flatHomeomorph) =
      (compactSupportKZeroHomeomorph h.flatHomeomorph).comp
        (compactSupportKZeroHomeomorph Te) := by
    rw [← compactSupportKZeroOpenPushforward_homeomorph (cotangentDiffeomorph e),
      ← compactSupportKZeroOpenPushforward_homeomorph q.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph h.flatHomeomorph,
      ← compactSupportKZeroOpenPushforward_homeomorph Te,
      ← compactSupportKZeroOpenPushforward_comp, ← compactSupportKZeroOpenPushforward_comp]
    have hfun := congrArg (fun d : TM ≃ₜ CotangentTotalSpace (n := m) (M := N) ↦
      (d : TM → CotangentTotalSpace (n := m) (M := N))) hsquare
    congr 1
  -- Metric independence replaces only the source metric; the same target metric remains fixed.
  rw [cotangentEmbeddingPushforward_independent_metric e.toContMDiffMap he hp g q h h]
  apply AddMonoidHom.ext
  intro a
  obtain ⟨b, rfl⟩ := (tangentCotangentKZeroEquiv q).surjective a
  change compactSupportKZeroHomeomorph h.flatHomeomorph
      (tangentEmbeddingPushforward e.toContMDiffMap he hp
        ((tangentCotangentKZeroEquiv q).symm (tangentCotangentKZeroEquiv q b))) =
    compactSupportKZeroHomeomorph (cotangentDiffeomorph e)
      (compactSupportKZeroHomeomorph q.flatHomeomorph b)
  rw [AddEquiv.symm_apply_apply, tangentEmbeddingPushforward_diffeomorph]
  exact (DFunLike.congr_fun hpush b).symm

end AtiyahSinger
