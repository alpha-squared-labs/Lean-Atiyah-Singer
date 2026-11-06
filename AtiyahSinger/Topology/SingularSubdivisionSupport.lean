/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularSubdivision

/-!
# Subdivision preserves the original small singular chains

Public module ID: M2156.

Both subdivision and its cone homotopy interpret affine chains inside the very
same singular simplex. They therefore preserve every family of small simplices,
without requiring openness. Openness is needed only for eventual smallness.
The coproduct argument below supplies induction on the actual chain generators;
no alternative free-chain model or replacement coefficient module is introduced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

/-- The original simplicial generators generate their whole module of chains.
This implementation interface is used for range preservation and eventual smallness. -/
theorem simplicialChain_mem_submodule (S : SSet.{u}) (n : ℕ)
    (P : Submodule R ((S.chainComplex (singularCoefficient R)).X n))
    (hP : ∀ τ a, S.ιChainComplex (R := singularCoefficient R) τ a ∈ P)
    (x : (S.chainComplex (singularCoefficient R)).X n) : x ∈ P := by
  have hzero : ModuleCat.ofHom P.mkQ =
      (0 : (S.chainComplex (singularCoefficient R)).X n ⟶
        ModuleCat.of R (((S.chainComplex (singularCoefficient R)).X n) ⧸ P)) := by
    apply SSet.chainComplex_hom_ext
    intro τ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero P).mpr (hP τ a)
  apply (Submodule.Quotient.mk_eq_zero P).mp
  exact congrArg (fun f ↦ f x) hzero

variable {X : Type u} [TopologicalSpace X]

/-- Every small generator belongs to the range of the original small-chain inclusion. -/
theorem singularGenerator_mem_small_range (𝒰 : Set (Set X)) (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌))
    (hτ : τ ∈ (smallSingularSet 𝒰).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a ∈
      ((smallSingularChainsInclusion R 𝒰).f n).hom.range := by
  refine ⟨(smallSingularSet 𝒰).toSSet.ιChainComplex
    (R := singularCoefficient R) ⟨τ, hτ⟩ a, ?_⟩
  change ((smallSingularSet 𝒰).toSSet.ιChainComplex ⟨τ, hτ⟩ ≫
    (SSet.chainComplexMap (smallSingularSet 𝒰).ι (singularCoefficient R)).f n) a = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Any affine chain within a supplied small singular simplex is small for the same family. -/
theorem singularAffineChain_mem_small_range (𝒰 : Set (Set X)) {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (U : Set X) (hU : U ∈ 𝒰)
    (hσ : Set.range σ ⊆ U) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    singularAffineChain R σ k c ∈ ((smallSingularChainsInclusion R 𝒰).f k).hom.range := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    rw [map_add]
    exact Submodule.add_mem _ hc hd
  | single v a =>
    rw [singularAffineChain_single]
    apply Submodule.smul_mem
    apply singularGenerator_mem_small_range
    refine ⟨U, hU, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hσ ⟨stdSimplexAffineMap v t, rfl⟩

/-- Subdivision preserves the range of the same small-chain inclusion in each degree. -/
theorem singularSubdivision_preserves_small (𝒰 : Set (Set X)) (n : ℕ)
    (x : (smallSingularChains R 𝒰).X n) :
    (singularSubdivision R X).f n ((smallSingularChainsInclusion R 𝒰).f n x) ∈
      ((smallSingularChainsInclusion R 𝒰).f n).hom.range := by
  let P := ((smallSingularChainsInclusion R 𝒰).f n).hom.range
  apply simplicialChain_mem_submodule R (smallSingularSet 𝒰).toSSet n
    (P.comap (((singularSubdivision R X).f n).hom.comp
      ((smallSingularChainsInclusion R 𝒰).f n).hom)) ?_ x
  intro τ a
  change singularSubdivisionComponent R X n
    ((smallSingularChainsInclusion R 𝒰).f n
      ((smallSingularSet 𝒰).toSSet.ιChainComplex (R := singularCoefficient R) τ a)) ∈ P
  have hι : (smallSingularChainsInclusion R 𝒰).f n
      ((smallSingularSet 𝒰).toSSet.ιChainComplex (R := singularCoefficient R) τ a) =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) τ.val a := by
    change ((smallSingularSet 𝒰).toSSet.ιChainComplex τ ≫
      (SSet.chainComplexMap (smallSingularSet 𝒰).ι (singularCoefficient R)).f n) a = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  rw [hι, singularSubdivisionComponent_generator]
  apply P.smul_mem
  obtain ⟨U, hU, hτ⟩ := τ.property
  exact singularAffineChain_mem_small_range R 𝒰 _ U hU hτ n _

/-- The chosen geometric homotopy also preserves the range of small chains. -/
theorem singularSubdivisionHomotopyComponent_preserves_small (𝒰 : Set (Set X)) (n : ℕ)
    (x : (smallSingularChains R 𝒰).X n) :
    singularSubdivisionHomotopyComponent R X n
        ((smallSingularChainsInclusion R 𝒰).f n x) ∈
      ((smallSingularChainsInclusion R 𝒰).f (n + 1)).hom.range := by
  let P := ((smallSingularChainsInclusion R 𝒰).f (n + 1)).hom.range
  apply simplicialChain_mem_submodule R (smallSingularSet 𝒰).toSSet n
    (P.comap ((singularSubdivisionHomotopyComponent R X n).hom.comp
      ((smallSingularChainsInclusion R 𝒰).f n).hom)) ?_ x
  intro τ a
  change singularSubdivisionHomotopyComponent R X n
    ((smallSingularChainsInclusion R 𝒰).f n
      ((smallSingularSet 𝒰).toSSet.ιChainComplex (R := singularCoefficient R) τ a)) ∈ P
  have hι : (smallSingularChainsInclusion R 𝒰).f n
      ((smallSingularSet 𝒰).toSSet.ιChainComplex (R := singularCoefficient R) τ a) =
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) τ.val a := by
    change ((smallSingularSet 𝒰).toSSet.ιChainComplex τ ≫
      (SSet.chainComplexMap (smallSingularSet 𝒰).ι (singularCoefficient R)).f n) a = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  rw [hι, singularSubdivisionHomotopyComponent_generator]
  apply P.smul_mem
  obtain ⟨U, hU, hτ⟩ := τ.property
  exact singularAffineChain_mem_small_range R 𝒰 _ U hU hτ (n + 1) _

/-- Every component of the original homotopy preserves small chains in its target degree. -/
theorem singularSubdivisionHomotopy_preserves_small (𝒰 : Set (Set X)) (n m : ℕ)
    (x : (smallSingularChains R 𝒰).X n) :
    (singularSubdivisionHomotopy R X).hom n m
        ((smallSingularChainsInclusion R 𝒰).f n x) ∈
      ((smallSingularChainsInclusion R 𝒰).f m).hom.range := by
  by_cases h : n + 1 = m
  · subst m
    simpa only [singularSubdivisionHomotopy, ↓reduceDIte, eqToHom_refl, Category.comp_id] using
      singularSubdivisionHomotopyComponent_preserves_small R 𝒰 n x
  · simp [singularSubdivisionHomotopy, h]

/-- Eventual smallness on generators extends to actual finite chains, using the same subdivision.
The finite common stage is justified by preservation of the original small range. -/
theorem singularSubdivision_eventually_small_of_generators (𝒰 : Set (Set X)) (n : ℕ)
    (hgen : ∀ (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R),
      ∃ k : ℕ, (((singularSubdivision R X).f n).hom ^ k)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) ∈
          ((smallSingularChainsInclusion R 𝒰).f n).hom.range)
    (x : (singularChains R X).X n) :
    ∃ k : ℕ, (((singularSubdivision R X).f n).hom ^ k) x ∈
      ((smallSingularChainsInclusion R 𝒰).f n).hom.range := by
  let S := ((singularSubdivision R X).f n).hom
  let Q := ((smallSingularChainsInclusion R 𝒰).f n).hom.range
  have hstable (y : (singularChains R X).X n) (hy : y ∈ Q) : S y ∈ Q := by
    obtain ⟨z, rfl⟩ := hy
    exact singularSubdivision_preserves_small R 𝒰 n z
  have hpow (k : ℕ) (y : (singularChains R X).X n) (hy : y ∈ Q) : (S ^ k) y ∈ Q := by
    induction k with
    | zero => exact hy
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hstable _ ih
  -- Eventual membership is a submodule: larger stages retain membership, so finite sums
  -- use a common stage. This does not posit a uniform stage for all singular simplices.
  let P : Submodule R ((singularChains R X).X n) :=
    { carrier := {y | ∃ k : ℕ, (S ^ k) y ∈ Q}
      zero_mem' := ⟨0, Q.zero_mem⟩
      add_mem' := by
        rintro y z ⟨k, hk⟩ ⟨l, hl⟩
        refine ⟨l + k, ?_⟩
        rw [map_add]
        apply Q.add_mem
        · rw [pow_add, Module.End.mul_apply]
          exact hpow l _ hk
        · rw [Nat.add_comm l k, pow_add, Module.End.mul_apply]
          exact hpow k _ hl
      smul_mem' := by
        rintro a y ⟨k, hk⟩
        refine ⟨k, ?_⟩
        rw [map_smul]
        exact Q.smul_mem a hk }
  exact simplicialChain_mem_submodule R (TopCat.toSSet.obj (TopCat.of X)) n P hgen x

end AtiyahSinger
