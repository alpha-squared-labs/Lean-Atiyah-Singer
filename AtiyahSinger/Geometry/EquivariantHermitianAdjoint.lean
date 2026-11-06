/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetricAdjoint
public import AtiyahSinger.Topology.EquivariantVectorBundle
public import AtiyahSinger.Topology.ModelBundleTopology

/-!
# Metric adjoints under the original moving-fiber actions

Public module ID: M1192.

The original adjoint between two specified Hermitian metrics intertwines the
same fiber actions whenever the metrics are invariant and the original maps
intertwine. Positivity separates vectors in the actual target fiber, without
replacing any native fiber norm or choosing alternative bundle coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G M] [ContinuousSMul G M]

/-- The actual metric adjoint preserves the original moving-fiber intertwining square. -/
theorem SmoothHermitianMetric.adjoint_intertwines
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F)
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (g : G) (x : M)
    (hInv : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ u v, h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) =
      h.pairing x u v)
    (kInv : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ u v, k.pairing (g • x) (τ.linearMap g x u) (τ.linearMap g x v) =
      k.pairing x u v)
    (P : E x →L[ℂ] F x) (Q : E (g • x) →L[ℂ] F (g • x))
    (hPQ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ u, Q (σ.linearMap g x u) = τ.linearMap g x (P u)) (v : F x) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    h.adjoint k (g • x) Q (τ.linearMap g x v) = σ.linearMap g x (h.adjoint k x P v) := by
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let u₀ := h.adjoint k (g • x) Q (τ.linearMap g x v)
  let u₁ := σ.linearMap g x (h.adjoint k x P v)
  have heq (w : E (g • x)) : h.pairing (g • x) w u₀ = h.pairing (g • x) w u₁ := by
    obtain ⟨u, rfl⟩ := (σ.linearMap_bijective g x).surjective w
    change h.pairing (g • x) (σ.linearMap g x u)
      (h.adjoint k (g • x) Q (τ.linearMap g x v)) =
        h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x (h.adjoint k x P v))
    rw [h.pairing_adjoint, hPQ, kInv, hInv, h.pairing_adjoint]
  -- The same positive form separates these two vectors in the original fiber.
  let : InnerProductSpace.Core ℂ (E (g • x)) := h.toCore (g • x)
  have hz : (h.toCore (g • x)).inner (u₀ - u₁) (u₀ - u₁) = 0 := by
    rw [InnerProductSpace.Core.inner_sub_right]
    exact sub_eq_zero.mpr (heq (u₀ - u₁))
  exact sub_eq_zero.mp ((h.toCore (g • x)).definite _ hz)

end AtiyahSinger
