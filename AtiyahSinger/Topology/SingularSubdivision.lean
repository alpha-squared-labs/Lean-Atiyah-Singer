/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularAffineRealization
public import AtiyahSinger.Topology.SingularSmallChains
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Tactic.Abel

/-!
# Barycentric subdivision on the original singular chains

Public module ID: M2155.

Every original singular simplex is subdivided by the universal finite vertex
expression inside its own standard simplex. The original coproduct extends this
operation linearly. Compatibility of affine realization with boundary and affine
substitution supplies the chain map and its standard cone homotopy.

The coefficient module, singular generators, and differential remain the original
ones. This is the subdivision construction for singular excision in Hatcher,
section 2.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The degreewise subdivision of the actual free singular generators. -/
def singularSubdivisionComponent (n : ℕ) :
    (singularChains R X).X n ⟶ (singularChains R X).X n :=
  Sigma.desc (fun τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) ↦
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight
      (singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) n
        (vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)))))

/-- Each supplied singular generator has precisely its finite barycentric subdivision. -/
theorem singularSubdivisionComponent_generator (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    singularSubdivisionComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      a.down • singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) n
        (vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)) := by
  change ((Sigma.ι (fun _ ↦ singularCoefficient R) τ) ≫ Sigma.desc _) a = _
  erw [Sigma.ι_comp_desc]
  rfl

/-- Subdividing a realized affine expression is realization of that same vertex subdivision. -/
theorem singularSubdivisionComponent_affineChain {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    singularSubdivisionComponent R X k (singularAffineChain R σ k c) =
      singularAffineChain R σ k
        (vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (k + 1) c) := by
  classical
  suffices h : (singularSubdivisionComponent R X k).hom.comp (singularAffineChain R σ k) =
      (singularAffineChain R σ k).comp
        (vertexChainSubdivision R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single]
  erw [(singularSubdivisionComponent R X k).hom.map_smul,
    singularSubdivisionComponent_generator]
  simp only [one_smul]
  change a • singularAffineChain R (σ.comp (stdSimplexAffineMap v)) k
    (vertexChainSubdivision R (StdSimplex ℝ (Fin (k + 1))) (k + 1)
      (Finsupp.single StdSimplex.single 1)) = _
  -- Affine naturality transports the universal subdivision through this very affine simplex.
  rw [singularAffineChain_comp, vertexChainMap_subdivision]
  have hvertices : (StdSimplex.affineMapMk (R := ℝ) v) ∘ StdSimplex.single = v := by
    funext j
    simp
  simp only [vertexChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hvertices]
  rw [← Finsupp.smul_single_one v a]
  simp only [map_smul]

/-- The subdivision operator commutes with the original singular boundary. -/
theorem singularSubdivisionComponent_boundary (n : ℕ) :
    singularSubdivisionComponent R X (n + 1) ≫ (singularChains R X).d (n + 1) n =
      (singularChains R X).d (n + 1) n ≫ singularSubdivisionComponent R X n := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let σ := (TopCat.of X).toSSetObjEquiv (op ⦋n + 1⦌) τ
  have hgen : (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) τ a =
      singularAffineChain R σ (n + 1) (Finsupp.single StdSimplex.single a.down) := by
    exact (singularAffineChain_vertices R σ a.down).symm
  change (singularChains R X).d (n + 1) n
      (singularSubdivisionComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    singularSubdivisionComponent R X n
      ((singularChains R X).d (n + 1) n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  -- Both sides interpret the same subdivided alternating boundary in the original simplex.
  rw [hgen, singularSubdivisionComponent_affineChain, singularAffineChain_boundary,
    vertexChainSubdivision_boundary, singularAffineChain_boundary,
    singularSubdivisionComponent_affineChain]

/-- Barycentric subdivision as an endomorphism of the original singular chain complex. -/
def singularSubdivision : singularChains R X ⟶ singularChains R X where
  f := singularSubdivisionComponent R X
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact singularSubdivisionComponent_boundary R X j

/-- The original simplex cone homotopy interpreted in singular degree n. -/
def singularSubdivisionHomotopyComponent (n : ℕ) :
    (singularChains R X).X n ⟶ (singularChains R X).X (n + 1) :=
  Sigma.desc (fun τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) ↦
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight
      (singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) (n + 1)
        (vertexChainSubdivisionHomotopy R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)))))

/-- The homotopy of a singular generator stays within that generator's original simplex. -/
theorem singularSubdivisionHomotopyComponent_generator (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    singularSubdivisionHomotopyComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      a.down • singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) (n + 1)
        (vertexChainSubdivisionHomotopy R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)) := by
  change ((Sigma.ι (fun _ ↦ singularCoefficient R) τ) ≫ Sigma.desc _) a = _
  erw [Sigma.ι_comp_desc]
  rfl

/-- The same affine substitution commutes with the chosen cone homotopy. -/
theorem singularSubdivisionHomotopyComponent_affineChain {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    singularSubdivisionHomotopyComponent R X k (singularAffineChain R σ k c) =
      singularAffineChain R σ (k + 1)
        (vertexChainSubdivisionHomotopy R (StdSimplex ℝ (Fin (n + 1))) (k + 1) c) := by
  classical
  suffices h : (singularSubdivisionHomotopyComponent R X k).hom.comp
      (singularAffineChain R σ k) =
      (singularAffineChain R σ (k + 1)).comp
        (vertexChainSubdivisionHomotopy R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single]
  erw [(singularSubdivisionHomotopyComponent R X k).hom.map_smul,
    singularSubdivisionHomotopyComponent_generator]
  simp only [one_smul]
  change a • singularAffineChain R (σ.comp (stdSimplexAffineMap v)) (k + 1)
    (vertexChainSubdivisionHomotopy R (StdSimplex ℝ (Fin (k + 1))) (k + 1)
      (Finsupp.single StdSimplex.single 1)) = _
  -- The affine map transports the original first vertex and every term of its cone together.
  rw [singularAffineChain_comp, vertexChainMap_subdivisionHomotopy]
  have hvertices : (StdSimplex.affineMapMk (R := ℝ) v) ∘ StdSimplex.single = v := by
    funext j
    simp
  simp only [vertexChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hvertices]
  rw [← Finsupp.smul_single_one v a]
  simp only [map_smul]

/-- In degree zero the cone homotopy has no lower boundary term. -/
theorem singularSubdivisionHomotopyComponent_boundary_zero :
    singularSubdivisionHomotopyComponent R X 0 ≫ (singularChains R X).d 1 0 =
      𝟙 _ - singularSubdivisionComponent R X 0 := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let σ := (TopCat.of X).toSSetObjEquiv (op ⦋0⦌) τ
  have hgen : (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) τ a =
      singularAffineChain R σ 0 (Finsupp.single StdSimplex.single a.down) := by
    exact (singularAffineChain_vertices R σ a.down).symm
  change (singularChains R X).d 1 0
      (singularSubdivisionHomotopyComponent R X 0
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    (show (singularChains R X).X 0 from
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularSubdivisionComponent R X 0
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)
  rw [hgen, singularSubdivisionHomotopyComponent_affineChain, singularAffineChain_boundary,
    vertexChainSubdivisionHomotopy_boundary, singularSubdivisionComponent_affineChain]
  simp [vertexChainSubdivisionHomotopy]

/-- The geometric cone equation holds in every positive singular degree. -/
theorem singularSubdivisionHomotopyComponent_boundary (n : ℕ) :
    singularSubdivisionHomotopyComponent R X (n + 1) ≫
        (singularChains R X).d (n + 2) (n + 1) =
      𝟙 _ - singularSubdivisionComponent R X (n + 1) -
        (singularChains R X).d (n + 1) n ≫ singularSubdivisionHomotopyComponent R X n := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let σ := (TopCat.of X).toSSetObjEquiv (op ⦋n + 1⦌) τ
  have hgen : (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) τ a =
      singularAffineChain R σ (n + 1) (Finsupp.single StdSimplex.single a.down) := by
    exact (singularAffineChain_vertices R σ a.down).symm
  change (singularChains R X).d (n + 2) (n + 1)
      (singularSubdivisionHomotopyComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    (show (singularChains R X).X (n + 1) from
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularSubdivisionComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularSubdivisionHomotopyComponent R X n
        ((singularChains R X).d (n + 1) n
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  -- Realize the augmented vertex identity; its lower term is exactly this singular boundary.
  rw [hgen, singularSubdivisionHomotopyComponent_affineChain, singularAffineChain_boundary,
    vertexChainSubdivisionHomotopy_boundary, singularSubdivisionComponent_affineChain,
    singularAffineChain_boundary, singularSubdivisionHomotopyComponent_affineChain]
  simp only [map_sub]

/-- The original cone homotopy has only components from degree n to degree n+1. -/
def singularSubdivisionHomotopy : Homotopy (𝟙 (singularChains R X)) (singularSubdivision R X) where
  hom n m := if h : n + 1 = m then
      singularSubdivisionHomotopyComponent R X n ≫
        eqToHom (congrArg (fun j ↦ (singularChains R X).X j) h)
    else 0
  zero n m h := by
    have hne : n + 1 ≠ m := h
    simp only [hne, ↓reduceDIte]
  comm n := by
    cases n with
    | zero =>
      rw [dNext_nat, prevD_eq _ (by rfl :
        (ComplexShape.down ℕ).Rel 1 0)]
      simp only [Nat.zero_sub, Nat.one_ne_zero, comp_zero, zero_add,
        ↓reduceDIte, eqToHom_refl, Category.comp_id]
      change 𝟙 _ = singularSubdivisionHomotopyComponent R X 0 ≫
        (singularChains R X).d 1 0 + singularSubdivisionComponent R X 0
      rw [singularSubdivisionHomotopyComponent_boundary_zero]
      abel
    | succ n =>
      rw [dNext_eq _ (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
        prevD_eq _ (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))]
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id]
      change 𝟙 _ = (singularChains R X).d (n + 1) n ≫
        singularSubdivisionHomotopyComponent R X n +
        singularSubdivisionHomotopyComponent R X (n + 1) ≫
          (singularChains R X).d (n + 2) (n + 1) + singularSubdivisionComponent R X (n + 1)
      rw [singularSubdivisionHomotopyComponent_boundary]
      abel

end AtiyahSinger
