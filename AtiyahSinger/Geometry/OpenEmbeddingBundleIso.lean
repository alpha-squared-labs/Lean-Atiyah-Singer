/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMapContinuity
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle
public import AtiyahSinger.Topology.BundlePullback

/-!
# The actual bundle isomorphism along a base map into an open subset

Public module ID: M1318.

A continuous base map into an open subset and a smooth fiberwise linear
equivalence give a continuous isomorphism to the single pullback along
the composed base map. Native model retyping and pullback associativity
preserve every fiber vector. This supplies the bundle comparison used
in relative compact-support symbol excision.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

variable {n m : ℕ} {O M : Type*}
  [TopologicalSpace O] [ChartedSpace (EuclideanSpace ℝ (Fin n)) O]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A native smooth fiber comparison induces the same isomorphism over the actual base map. -/
theorem IsSmoothBundleMap.exists_iso_openEmbedding
    (E : SmoothFiniteComplexBundle (n := n) O)
    (G : SmoothFiniteComplexBundle (n := m) M) (U : Opens M)
    (e : C(O, U)) (a : ∀ x : O, E.Fiber x ≃ₗ[ℂ] G.Fiber (e x).val)
    (ha : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank)
      (E := E.Fiber)
      (F := (e : O → U) *ᵖ ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
      (fun x ↦ (a x).toLinearMap)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
    ∃ b : Iso E.Fiber
        (((ContinuousMap.subtypeVal (U : Set M)).comp e : O → M) *ᵖ G.Fiber),
      ∀ (x : O) (v : E.Fiber x), b.linearEquiv x v = a x v := by
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber
  let i : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let GU := (i : U → M) *ᵖ G.Fiber
  let GO := (e : O → U) *ᵖ GU
  let tU : TopologicalSpace (TotalSpace Unit GU) :=
    @Pullback.TotalSpace.topologicalSpace M Unit G.Fiber U (i : U → M) _
      (modelTopology (EuclideanSpace ℂ (Fin G.rank)) G.Fiber)
  let t : TopologicalSpace (TotalSpace Unit GO) :=
    @Pullback.TotalSpace.topologicalSpace U Unit GU O (e : O → U) _ tU
  have ht : modelTopology (EuclideanSpace ℂ (Fin G.rank)) GO = t := by
    simp only [modelTopology, Pullback.TotalSpace.topologicalSpace, pullbackTopology_def,
      induced_inf, induced_compose, t, tU, modelTopology]
    rfl
  -- Only the topology presentation changes; the original fiber equivalences are retained.
  have h := IsSmoothBundleMap.exists_iso (E := E.Fiber)
    (F := (e : O → U) *ᵖ ((i : U → M) *ᵖ G.Fiber)) a ha
  change letI := modelTopology (EuclideanSpace ℂ (Fin G.rank)) GO;
    ∃ b : Iso E.Fiber GO, ∀ x v, b.linearEquiv x v = a x v at h
  rw [ht] at h
  obtain ⟨b, hb⟩ := h
  refine ⟨b.trans (pullbackCompIso (E := G.Fiber) i e), ?_⟩
  intro x v
  change (pullbackCompIso (E := G.Fiber) i e).linearEquiv x (b.linearEquiv x v) = a x v
  rw [pullbackCompIso_apply, hb]

end AtiyahSinger
