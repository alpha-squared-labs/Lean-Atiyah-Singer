/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorOperator

/-!
# The actual graph domain carries its original unitary action

Public module ID: M0337.

Invariant input and output integral actions restrict to the same graph with
the Hilbert graph norm. This provides the fixed unitary source representation
for norm perturbations of an order-one operator. A later Sobolev comparison
uses a continuous linear equivalence to this graph and keeps its actual norm.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {G E F : Type*}
  [Group G] [TopologicalSpace G]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The original two unitary actions induce a jointly continuous action on the actual graph. -/
theorem LinearPMap.exists_graphIsometryRepresentation
    (D : E →ₗ.[ℂ] F)
    (ρ : G →* (E ≃ₗᵢ[ℂ] E)) (τ : G →* (F ≃ₗᵢ[ℂ] F))
    (hρ : Continuous (fun p : G × E ↦ ρ p.1 p.2))
    (hτ : Continuous (fun p : G × F ↦ τ p.1 p.2))
    (hgraph : ∀ g z, (ρ g z.1, τ g z.2) ∈ D.graph ↔ z ∈ D.graph) :
    let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
    ∃ γ : G →* (S ≃ₗᵢ[ℂ] S),
      Continuous (fun p : G × S ↦ γ p.1 p.2) ∧
      ∀ g v, (γ g v).val = WithLp.toLp 2
        (ρ g (WithLp.ofLp v.val).1, τ g (WithLp.ofLp v.val).2) := by
  let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  let W (g : G) := (ρ g).withLpProdCongr 2 (τ g)
  -- Restrict the same product isometry; graph invariance identifies its exact image subspace.
  have hS (g : G) : S.map (W g).toLinearMap = S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (ρ g (WithLp.ofLp w).1, τ g (WithLp.ofLp w).2) ∈ D.graph
      exact (hgraph g (WithLp.ofLp w)).mpr hw
    · intro hz
      refine ⟨(W g).symm z, ?_, (W g).apply_symm_apply z⟩
      apply (hgraph g (WithLp.ofLp ((W g).symm z))).mp
      change WithLp.ofLp (W g ((W g).symm z)) ∈ D.graph
      rw [(W g).apply_symm_apply]
      exact hz
  let a (g : G) : S ≃ₗᵢ[ℂ] S :=
    ((W g).submoduleMap S).trans (LinearIsometryEquiv.ofEq _ _ (hS g))
  have ha (g : G) (v : S) : (a g v).val = W g v.val := rfl
  let γ : G →* (S ≃ₗᵢ[ℂ] S) := {
    toFun := a
    map_one' := by
      ext v
      apply WithLp.ofLp_injective
      change (ρ 1 (WithLp.ofLp v.val).1, τ 1 (WithLp.ofLp v.val).2) = WithLp.ofLp v.val
      rw [map_one, map_one]
      rfl
    map_mul' := by
      intro g h
      ext v
      apply WithLp.ofLp_injective
      change (ρ (g * h) (WithLp.ofLp v.val).1, τ (g * h) (WithLp.ofLp v.val).2) =
        (ρ g (ρ h (WithLp.ofLp v.val).1), τ g (τ h (WithLp.ofLp v.val).2))
      rw [map_mul, map_mul]
      rfl }
  refine ⟨γ, ?_, fun _ _ ↦ rfl⟩
  -- The induced graph topology uses the same two continuous ambient coordinates.
  apply continuous_induced_rng.mpr
  have hcoord : Continuous (fun p : G × S ↦ WithLp.ofLp p.2.val) :=
    (WithLp.prod_continuous_ofLp 2 E F).comp (continuous_subtype_val.comp continuous_snd)
  exact (WithLp.prod_continuous_toLp 2 E F).comp
    ((hρ.comp (continuous_fst.prodMk hcoord.fst)).prodMk
      (hτ.comp (continuous_fst.prodMk hcoord.snd)))

omit [Group G] [TopologicalSpace G] in
/-- A complete realization with the exact closed graph identifies its original domain norm. -/
theorem LinearPMap.exists_graphDomainEquiv
    [CompleteSpace E] [CompleteSpace F]
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (D : E →ₗ.[ℂ] F) (hD : D.IsClosed)
    (J : X →L[ℂ] E) (T : X →L[ℂ] F) (hJ : Function.Injective J)
    (hgraph : D.graph = (J.prod T).toLinearMap.range) :
    let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
    ∃ Φ : X ≃L[ℂ] S, ∀ x, (Φ x).val = WithLp.toLp 2 (J x, T x) := by
  let S := D.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  have hS : IsClosed (S : Set (WithLp 2 (E × F))) :=
    hD.preimage (WithLp.prod_continuous_ofLp 2 E F)
  let : CompleteSpace S := hS.completeSpace_coe
  let A := (WithLp.prodContinuousLinearEquiv 2 ℂ E F).symm.toContinuousLinearMap.comp
    (J.prod T)
  have hA (x : X) : A x ∈ S := by
    change (J x, T x) ∈ D.graph
    rw [hgraph]
    exact ⟨x, rfl⟩
  let φ := A.codRestrict S hA
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y hxy
      apply hJ
      exact congrArg (fun z : S ↦ (WithLp.ofLp z.val).1) hxy
    · intro z
      have hz : WithLp.ofLp z.val ∈ (J.prod T).toLinearMap.range := by
        rw [← hgraph]
        exact z.property
      obtain ⟨x, hx⟩ := hz
      refine ⟨x, Subtype.ext ?_⟩
      apply WithLp.ofLp_injective
      exact hx
  exact ⟨ContinuousLinearEquiv.ofBijective φ (LinearMap.ker_eq_bot.mpr hφ.1)
    (LinearMap.range_eq_top.mpr hφ.2), fun _ ↦ rfl⟩

end AtiyahSinger
