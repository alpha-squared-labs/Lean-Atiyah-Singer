/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Topology.BundleSum
public import AtiyahSinger.Topology.SerreSwan

/-!
# The actual sum isomorphism supplied by two smooth inclusions

Public module ID: M1416.

Smoothness of the two prescribed summand maps gives continuity of their sum
on the original direct-sum topology. Finite local rank supplies continuity of
the inverse of that same fiber equivalence. This is used to transport graded
symbols to the specified native source and target bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

attribute [local instance] sumTopology isFiniteRank_sum isFiniteRank_pullback

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

variable {s : ℕ} {H : M → Type*}
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s)) H]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The specified fiber sum equivalence is an actual bundle isomorphism. -/
theorem exists_sumBundleIso_of_smooth
    (e : ∀ x, (E x × F x) ≃ₗ[ℂ] H x)
    (he₀ : IsSmoothBundleMap (n := n) (r := r) (q := s)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ (E x) (F x))))
    (he₁ : IsSmoothBundleMap (n := n) (r := q) (q := s)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ (E x) (F x)))) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin s)) H
    ∃ a : Iso (E ×ᵇ F) H, ∀ x v, a.linearEquiv x v = e x v := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := modelTopology (EuclideanSpace ℂ (Fin s)) H
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin r)) E
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin q)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin s)) H
  let A : Hom E H := ⟨fun x ↦ (e x).toLinearMap.comp
    (LinearMap.inl ℂ (E x) (F x)), he₀.continuous_total⟩
  let B : Hom F H := ⟨fun x ↦ (e x).toLinearMap.comp
    (LinearMap.inr ℂ (E x) (F x)), he₁.continuous_total⟩
  let U := A.comp (sumFst (E := E) (F := F))
  let W := B.comp (sumSnd (E := E) (F := F))
  let p : C(TotalSpace Unit (E ×ᵇ F), M) := ⟨π Unit (E ×ᵇ F), continuous_proj⟩
  -- The two moving-fiber maps give sections of one common pullback before addition.
  have hU : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z, U.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ H))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit H p).continuous_iff]
    exact continuous_id.prodMk U.continuous_total
  have hW : Continuous (fun z : TotalSpace Unit (E ×ᵇ F) ↦
      (⟨z, W.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ H))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit H p).continuous_iff]
    exact continuous_id.prodMk W.continuous_total
  let L : Hom (E ×ᵇ F) H :=
    { linearMap := fun x ↦ (e x).toLinearMap
      continuous_total := by
        have h := (Pullback.continuous_lift Unit H p).comp
          (continuous_add_section (p *ᵖ H) _ _ hU hW)
        apply h.congr
        intro z
        apply congrArg (TotalSpace.mk z.proj)
        change (e z.proj) (z.snd.1, 0) + (e z.proj) (0, z.snd.2) =
          (e z.proj) z.snd
        rw [← map_add]
        congr 1
        exact Prod.ext (add_zero _) (zero_add _) }
  -- Inverting this same bijective Hom retains the displayed forward map exactly.
  exact ⟨L.toIso (fun x ↦ (e x).bijective), fun _ _ ↦ rfl⟩

end AtiyahSinger
