/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentExternalTensorIso
public import AtiyahSinger.Geometry.SmoothSumBundleIso
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.EquivariantOpenBundleGluing

/-!
# The prescribed native graded bundle on the product cotangent space

Public module ID: M1149.

The same two tensor factors and the same smooth sum equivalence determine an
actual isomorphism from the cotangent pullback of the original external sum.
The equality of total vectors records the exact given fiber map even before
unfolding the chosen inverse in the original cotangent homeomorphism.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 50
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  isFiniteRank_pullback

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)

set_option maxHeartbeats 2400000 in
-- The comparison composes the actual tensor, pullback and sum topologies with the given e.
set_option maxRecDepth 4096 in
/-- The actual cotangent external sum maps by the same prescribed native sum equivalence. -/
theorem exists_cotangentGradedSumIso :
    letI := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
      E₀.Fiber F₀.Fiber
    letI := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
      E₁.Fiber F₁.Fiber
    ∀ (S : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (e : ∀ x : M × N, (externalTensorFiber E₀.Fiber F₀.Fiber x ×
        externalTensorFiber E₁.Fiber F₁.Fiber x) ≃ₗ[ℂ] S.Fiber x)
      (_he₀ : IsSmoothBundleMap (n := n + m) (r := E₀.rank * F₀.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x))))
      (_he₁ : IsSmoothBundleMap (n := n + m) (r := E₁.rank * F₁.rank) (q := S.rank)
        (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ
          (externalTensorFiber E₀.Fiber F₀.Fiber x)
          (externalTensorFiber E₁.Fiber F₁.Fiber x)))),
    letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    let pM := cotangentProjection (n := n) (M := M)
    let pN := cotangentProjection (n := m) (M := N)
    let p := cotangentProjection (n := n + m) (M := M × N)
    let c := cotangentProductHomeomorph (n := n) (m := m) M N
    let A₀ : FiniteBundle
        (CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
      ((FiniteBundle.ofFamily (pM *ᵖ E₀.Fiber)).pullback ContinuousMap.fst).tensor
      ((FiniteBundle.ofFamily (pN *ᵖ F₀.Fiber)).pullback ContinuousMap.snd)
    let A₁ : FiniteBundle
        (CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
      ((FiniteBundle.ofFamily (pM *ᵖ E₁.Fiber)).pullback ContinuousMap.fst).tensor
      ((FiniteBundle.ofFamily (pN *ᵖ F₁.Fiber)).pullback ContinuousMap.snd)
    letI := A₀.totalTopology
    letI := A₁.totalTopology
    letI := (A₀.sum A₁).totalTopology
    ∃ U : Iso ((c : _ → _) *ᵖ (A₀.sum A₁).Fiber) (p *ᵖ S.Fiber),
      ∀ z w, (⟨z.proj, U.linearEquiv z w⟩ : TotalSpace Unit S.Fiber) =
        ⟨((c z).1.proj, (c z).2.proj), e ((c z).1.proj, (c z).2.proj) w⟩ := by
  let := modelTopology (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₀.rank)) E₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin E₁.rank)) E₁.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₀.rank)) F₀.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F₁.rank)) F₁.Fiber
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedSpace (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorTopology (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₀.rank) (s := F₀.rank)
    E₀.Fiber F₀.Fiber
  let := externalTensorFiberNormedAddCommGroup (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberNormedSpace (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorTopology (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorFiberBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorVectorBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := E₁.rank) (s := F₁.rank)
    E₁.Fiber F₁.Fiber
  dsimp only
  intro S e he₀ he₁
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin (E₀.rank * F₀.rank)))
    (externalTensorFiber E₀.Fiber F₀.Fiber)
  let := modelTopology (EuclideanSpace ℂ (Fin (E₁.rank * F₁.rank)))
    (externalTensorFiber E₁.Fiber F₁.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin (E₀.rank * F₀.rank)))
    (externalTensorFiber E₀.Fiber F₀.Fiber)
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin (E₁.rank * F₁.rank)))
    (externalTensorFiber E₁.Fiber F₁.Fiber)
  let pM := cotangentProjection (n := n) (M := M)
  let pN := cotangentProjection (n := m) (M := N)
  let p := cotangentProjection (n := n + m) (M := M × N)
  let c₀ := cotangentProductHomeomorph (n := n) (m := m) M N
  let c : C(CotangentTotalSpace (n := n + m) (M := M × N),
      CotangentTotalSpace (n := n) (M := M) × CotangentTotalSpace (n := m) (M := N)) :=
    { toFun := fun z ↦
        (⟨z.proj.1, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩,
        ⟨z.proj.2, (z.snd.comp EuclideanSpace.finAddEquivProd.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n))
            (EuclideanSpace ℝ (Fin m)))⟩)
      continuous_toFun := c₀.continuous.congr cotangentProductHomeomorph_apply }
  have hc : (c₀ : _ → _) = c := funext cotangentProductHomeomorph_apply
  let A₀ := ((FiniteBundle.ofFamily (pM *ᵖ E₀.Fiber)).pullback
    (ContinuousMap.fst : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), _))).tensor
    ((FiniteBundle.ofFamily (pN *ᵖ F₀.Fiber)).pullback ContinuousMap.snd)
  let A₁ := ((FiniteBundle.ofFamily (pM *ᵖ E₁.Fiber)).pullback
    (ContinuousMap.fst : C(CotangentTotalSpace (n := n) (M := M) ×
      CotangentTotalSpace (n := m) (M := N), _))).tensor
    ((FiniteBundle.ofFamily (pN *ᵖ F₁.Fiber)).pullback ContinuousMap.snd)
  let := A₀.totalTopology
  let := A₁.totalTopology
  let := (A₀.sum A₁).totalTopology
  let B₀ := FiniteBundle.ofFamily (externalTensorFiber E₀.Fiber F₀.Fiber)
  let B₁ := FiniteBundle.ofFamily (externalTensorFiber E₁.Fiber F₁.Fiber)
  have h₀ := exists_cotangentExternalTensorIso (n := n) (m := m)
    (r := E₀.rank) (s := F₀.rank) E₀.Fiber F₀.Fiber
  have h₁ := exists_cotangentExternalTensorIso (n := n) (m := m)
    (r := E₁.rank) (s := F₁.rank) E₁.Fiber F₁.Fiber
  change ∃ a : Iso ((c₀ : _ → _) *ᵖ A₀.Fiber) (p *ᵖ B₀.Fiber),
    ∀ z w, HEq (a.linearEquiv z w) w at h₀
  change ∃ a : Iso ((c₀ : _ → _) *ᵖ A₁.Fiber) (p *ᵖ B₁.Fiber),
    ∀ z w, HEq (a.linearEquiv z w) w at h₁
  rw [hc] at h₀ h₁
  obtain ⟨u₀, hu₀⟩ := h₀
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨v, hv⟩ := exists_sumBundleIso_of_smooth e he₀ he₁
  change ∃ U : Iso ((c₀ : _ → _) *ᵖ (A₀.sum A₁).Fiber) (p *ᵖ S.Fiber),
    ∀ z w, (⟨z.proj, U.linearEquiv z w⟩ : TotalSpace Unit S.Fiber) =
      ⟨((c₀ z).1.proj, (c₀ z).2.proj), e ((c₀ z).1.proj, (c₀ z).2.proj) w⟩
  rw [hc]
  -- Sum the same two vector-preserving tensor maps and then apply the original smooth e.
  let U := (sumPullbackIso c A₀ A₁).trans
    ((u₀.sum u₁).trans ((sumPullbackIso p B₀ B₁).symm.trans (v.pullback p)))
  refine ⟨U, ?_⟩
  intro z w
  change (⟨z.proj, v.linearEquiv z.proj
    (u₀.linearEquiv z w.1, u₁.linearEquiv z w.2)⟩ : TotalSpace Unit S.Fiber) =
      ⟨z.proj, e z.proj w⟩
  apply congrArg (TotalSpace.mk z.proj)
  rw [hv, eq_of_heq (hu₀ z w.1), eq_of_heq (hu₁ z w.2)]
  rfl

end AtiyahSinger
