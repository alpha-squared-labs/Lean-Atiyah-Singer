/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSubdivisionMesh
public import AtiyahSinger.Topology.RelativeSingularExcision
public import AtiyahSinger.Topology.SingularSubdivisionSupport
public import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex

/-!
# The small-chain homotopy equivalence for an open cover

Public module ID: M2154.

Lebesgue's lemma applies on the compact image of the original standard simplex
under its weight embedding. Iterated barycentric subdivision has arbitrarily
small affine images in that same metric space. Realizing those expressions in
the original singular chain complex gives eventual smallness of each chain.
The original subdivision homotopy descends to the small-chain cokernel, where
subdivision is locally nilpotent. The resulting contraction, together with the
degreewise splitting on actual generators, proves the small-chain equivalence.

This is the standard singular excision argument in Hatcher, section 2.1. It works
for arbitrary commutative coefficients and arbitrary topological spaces.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Convexity Opposite Topology
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- Iterating the actual vertex subdivision eventually refines a supplied open cover. -/
theorem vertexChainSubdivision_eventually_small (𝒰 : Set (Set X))
    (hOpen : ∀ U ∈ 𝒰, IsOpen U) (hCover : ⋃₀ 𝒰 = Set.univ) (n : ℕ)
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (a : R) :
    ∃ N : ℕ, ∀ m ≥ N,
      ∀ w ∈ ((vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (n + 1))^[m]
        (Finsupp.single StdSimplex.single a)).support,
        ∃ U ∈ 𝒰, Set.range (σ.comp (stdSimplexAffineMap w)) ⊆ U := by
  classical
  let f : ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (Fin (n + 1) → ℝ) :=
    ⟨fun s ↦ s.weights, (IsAffineMap.linearMap (Finsupp.lcoeFun :
      (Fin (n + 1) →₀ ℝ) →ₗ[ℝ] Fin (n + 1) → ℝ)).comp
        (StdSimplex.isAffineMap_weights ℝ (Fin (n + 1)))⟩
  let e : StdSimplex ℝ (Fin (n + 1)) ≃ₜ Set.range f :=
    (StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).toHomeomorph
  let : CompactSpace (Set.range f) := e.compactSpace
  let c (U : 𝒰) : Set (Set.range f) := (σ ∘ e.symm) ⁻¹' U.val
  have hc (U : 𝒰) : IsOpen (c U) :=
    (hOpen U.val U.property).preimage (σ.continuous.comp e.symm.continuous)
  have hcover : (Set.univ : Set (Set.range f)) ⊆ ⋃ U : 𝒰, c U := by
    intro s _
    have hs : σ (e.symm s) ∈ ⋃₀ 𝒰 := hCover.symm ▸ Set.mem_univ _
    obtain ⟨U, hU, hsU⟩ := Set.mem_sUnion.mp hs
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hsU⟩
  -- Keep the native topology through its embedding; no topology on the simplex is replaced.
  obtain ⟨ε, hε, hLeb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hc hcover
  obtain ⟨N, hN⟩ := vertexChainSubdivision_eventually_affine_ball R f n
    StdSimplex.single a ε hε
  refine ⟨N, ?_⟩
  intro m hm w hw
  obtain ⟨U, hU⟩ := hLeb (e (w 0)) (Set.mem_univ _)
  refine ⟨U.val, U.property, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hball : e (stdSimplexAffineMap w t) ∈ Metric.ball (e (w 0)) ε := hN m hm w hw t
  have hmem := hU hball
  change σ (e.symm (e (stdSimplexAffineMap w t))) ∈ U.val at hmem
  rw [e.symm_apply_apply] at hmem
  exact hmem

/-- Every original singular chain eventually becomes small for the given open cover. -/
theorem singularSubdivision_eventually_small (𝒰 : Set (Set X))
    (hOpen : ∀ U ∈ 𝒰, IsOpen U) (hCover : ⋃₀ 𝒰 = Set.univ) (n : ℕ)
    (x : (singularChains R X).X n) :
    ∃ k : ℕ, (((singularSubdivision R X).f n).hom ^ k) x ∈
      ((smallSingularChainsInclusion R 𝒰).f n).hom.range := by
  classical
  apply singularSubdivision_eventually_small_of_generators R 𝒰 n ?_ x
  intro τ a
  let σ := (TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ
  let V := vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
  let S := ((singularSubdivision R X).f n).hom
  have hiter (k : ℕ) (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (n + 1)) :
      (S ^ k) (singularAffineChain R σ n c) =
        singularAffineChain R σ n (V^[k] c) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, Function.iterate_succ_apply']
      exact singularSubdivisionComponent_affineChain R X σ n _
  obtain ⟨N, hN⟩ := vertexChainSubdivision_eventually_small R 𝒰 hOpen hCover n σ a.down
  refine ⟨N, ?_⟩
  have hgen : (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) τ a =
      singularAffineChain R σ n (Finsupp.single StdSimplex.single a.down) :=
    (singularAffineChain_vertices R σ a.down).symm
  change (S ^ N) _ ∈ _
  rw [hgen, hiter]
  -- The finite expression uses only small generators, with their original coefficients.
  let c := V^[N] (Finsupp.single StdSimplex.single a.down)
  change singularAffineChain R σ n c ∈ _
  simp only [singularAffineChain]
  apply Submodule.sum_mem
  intro w hw
  apply Submodule.smul_mem
  apply singularGenerator_mem_small_range
  obtain ⟨U, hU, hσ⟩ := hN N le_rfl w hw
  exact ⟨U, hU, hσ⟩

/-- The actual cokernel of the small-chain inclusion is contracted by geometric subdivision. -/
theorem contractible_cokernel_smallSingularChains (𝒰 : Set (Set X))
    (hOpen : ∀ U ∈ 𝒰, IsOpen U) (hCover : ⋃₀ 𝒰 = Set.univ) :
    Nonempty (Homotopy (𝟙 (cokernel (smallSingularChainsInclusion R 𝒰))) 0) := by
  exact contractible_cokernel_of_homotopy_of_eventually_range
    (smallSingularChainsInclusion R 𝒰) (singularSubdivision R X)
    (singularSubdivisionHomotopy R X) (singularSubdivision_preserves_small R 𝒰)
    (singularSubdivisionHomotopy_preserves_small R 𝒰)
    (singularSubdivision_eventually_small R 𝒰 hOpen hCover)

end AtiyahSinger
