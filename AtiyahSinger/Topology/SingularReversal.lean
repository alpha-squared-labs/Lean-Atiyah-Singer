/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSimplexReversal
public import AtiyahSinger.Topology.SingularAffineRealization
public import Mathlib.Algebra.Homology.Homotopy

import Mathlib.Tactic.Abel

/-!
# Signed reversal and its homotopy on original singular chains

Public module ID: M2152.

The signed reversal of an ordered simplex is realized inside the original
singular simplex. Compatibility with boundary and affine substitution gives a
chain map and a cone homotopy to the identity. Every homotopy term stays in that
same simplex, which is essential for the relative cup-product argument.

The original singular generators, coefficient module, and differential are
retained. The construction is the standard reversal proof of graded
commutativity of singular cohomology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory CategoryTheory.Limits Convexity Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Reverse the vertices of the supplied singular simplex in its native standard simplex. -/
def singularSimplexReversal {X : Type u} [TopologicalSpace X] {n : ℕ}
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
    (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) :=
  singularAffineSimplex ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) n
    (StdSimplex.single ∘ Fin.rev)

/-- Degreewise signed reversal of the actual free singular generators. -/
def singularReversalComponent (n : ℕ) :
    (singularChains R X).X n ⟶ (singularChains R X).X n :=
  Sigma.desc (fun τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) ↦
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight
      (singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) n
        (vertexChainReversal R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)))))

/-- Each supplied singular generator has precisely its signed vertex reversal. -/
theorem singularReversalComponent_generator (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    singularReversalComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      a.down • singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) n
        (vertexChainReversal R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)) := by
  change ((Sigma.ι (fun _ ↦ singularCoefficient R) τ) ≫ Sigma.desc _) a = _
  erw [Sigma.ι_comp_desc]
  rfl

/-- On a generator, reversal is the usual orientation sign times the reversed simplex. -/
theorem singularReversalComponent_generator_signed (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    singularReversalComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      vertexReversalSign R (n + 1) •
        (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) (singularSimplexReversal τ) a := by
  rw [singularReversalComponent_generator, vertexChainReversal_single, map_smul,
    singularAffineChain_single, one_smul]
  let g : singularCoefficient R ⟶ (singularChains R X).X n :=
    (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (singularSimplexReversal τ)
  change a.down • vertexReversalSign R (n + 1) • g (ULift.up 1) =
    vertexReversalSign R (n + 1) • g a
  rw [smul_comm]
  congr 1
  rw [← g.hom.map_smul]
  congr 1
  apply ULift.down_injective
  simp

/-- Reversing a realized affine expression is realization of that same signed vertex reversal. -/
theorem singularReversalComponent_affineChain {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    singularReversalComponent R X k (singularAffineChain R σ k c) =
      singularAffineChain R σ k
        (vertexChainReversal R (StdSimplex ℝ (Fin (n + 1))) (k + 1) c) := by
  classical
  suffices h : (singularReversalComponent R X k).hom.comp (singularAffineChain R σ k) =
      (singularAffineChain R σ k).comp
        (vertexChainReversal R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single]
  erw [(singularReversalComponent R X k).hom.map_smul,
    singularReversalComponent_generator]
  simp only [one_smul]
  change a • singularAffineChain R (σ.comp (stdSimplexAffineMap v)) k
    (vertexChainReversal R (StdSimplex ℝ (Fin (k + 1))) (k + 1)
      (Finsupp.single StdSimplex.single 1)) = _
  -- Naturality transports the universal signed reversal through this very affine simplex.
  rw [singularAffineChain_comp, vertexChainMap_reversal]
  have hvertices : (StdSimplex.affineMapMk (R := ℝ) v) ∘ StdSimplex.single = v := by
    funext j
    simp
  simp only [vertexChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hvertices]
  rw [← Finsupp.smul_single_one v a]
  simp only [map_smul]

/-- The signed reversal operator commutes with the original singular boundary. -/
theorem singularReversalComponent_boundary (n : ℕ) :
    singularReversalComponent R X (n + 1) ≫ (singularChains R X).d (n + 1) n =
      (singularChains R X).d (n + 1) n ≫ singularReversalComponent R X n := by
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
      (singularReversalComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    singularReversalComponent R X n
      ((singularChains R X).d (n + 1) n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  -- Both sides interpret the same signed reversed alternating boundary in the original simplex.
  rw [hgen, singularReversalComponent_affineChain, singularAffineChain_boundary,
    vertexChainReversal_boundary, singularAffineChain_boundary,
    singularReversalComponent_affineChain]

/-- Signed reversal as an endomorphism of the original singular chain complex. -/
def singularReversal : singularChains R X ⟶ singularChains R X where
  f := singularReversalComponent R X
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    exact singularReversalComponent_boundary R X j

/-- The original simplex cone homotopy interpreted in singular degree n. -/
def singularReversalHomotopyComponent (n : ℕ) :
    (singularChains R X).X n ⟶ (singularChains R X).X (n + 1) :=
  Sigma.desc (fun τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) ↦
    ModuleCat.ofHom ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight
      (singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) (n + 1)
        (vertexChainReversalHomotopy R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)))))

/-- The homotopy of a singular generator stays within that generator's original simplex. -/
theorem singularReversalHomotopyComponent_generator (n : ℕ)
    (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) (a : ULift.{u} R) :
    singularReversalHomotopyComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      a.down • singularAffineChain R ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τ) (n + 1)
        (vertexChainReversalHomotopy R (StdSimplex ℝ (Fin (n + 1))) (n + 1)
          (Finsupp.single StdSimplex.single 1)) := by
  change ((Sigma.ι (fun _ ↦ singularCoefficient R) τ) ≫ Sigma.desc _) a = _
  erw [Sigma.ι_comp_desc]
  rfl

/-- The same affine substitution commutes with the chosen cone homotopy. -/
theorem singularReversalHomotopyComponent_affineChain {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    singularReversalHomotopyComponent R X k (singularAffineChain R σ k c) =
      singularAffineChain R σ (k + 1)
        (vertexChainReversalHomotopy R (StdSimplex ℝ (Fin (n + 1))) (k + 1) c) := by
  classical
  suffices h : (singularReversalHomotopyComponent R X k).hom.comp
      (singularAffineChain R σ k) =
      (singularAffineChain R σ (k + 1)).comp
        (vertexChainReversalHomotopy R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single]
  erw [(singularReversalHomotopyComponent R X k).hom.map_smul,
    singularReversalHomotopyComponent_generator]
  simp only [one_smul]
  change a • singularAffineChain R (σ.comp (stdSimplexAffineMap v)) (k + 1)
    (vertexChainReversalHomotopy R (StdSimplex ℝ (Fin (k + 1))) (k + 1)
      (Finsupp.single StdSimplex.single 1)) = _
  -- The affine map transports the original first vertex and every term of its cone together.
  rw [singularAffineChain_comp, vertexChainMap_reversalHomotopy]
  have hvertices : (StdSimplex.affineMapMk (R := ℝ) v) ∘ StdSimplex.single = v := by
    funext j
    simp
  simp only [vertexChainMap, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, hvertices]
  rw [← Finsupp.smul_single_one v a]
  simp only [map_smul]

/-- In degree zero the cone homotopy has no lower boundary term. -/
theorem singularReversalHomotopyComponent_boundary_zero :
    singularReversalHomotopyComponent R X 0 ≫ (singularChains R X).d 1 0 =
      𝟙 _ - singularReversalComponent R X 0 := by
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
      (singularReversalHomotopyComponent R X 0
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    (show (singularChains R X).X 0 from
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularReversalComponent R X 0
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)
  rw [hgen, singularReversalHomotopyComponent_affineChain, singularAffineChain_boundary,
    vertexChainReversalHomotopy_boundary, singularReversalComponent_affineChain]
  simp [vertexChainReversalHomotopy]

/-- The geometric cone equation holds in every positive singular degree. -/
theorem singularReversalHomotopyComponent_boundary (n : ℕ) :
    singularReversalHomotopyComponent R X (n + 1) ≫
        (singularChains R X).d (n + 2) (n + 1) =
      𝟙 _ - singularReversalComponent R X (n + 1) -
        (singularChains R X).d (n + 1) n ≫ singularReversalHomotopyComponent R X n := by
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
      (singularReversalHomotopyComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    (show (singularChains R X).X (n + 1) from
      (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularReversalComponent R X (n + 1)
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) -
      singularReversalHomotopyComponent R X n
        ((singularChains R X).d (n + 1) n
          ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  -- Realize the augmented vertex identity; its lower term is exactly this singular boundary.
  rw [hgen, singularReversalHomotopyComponent_affineChain, singularAffineChain_boundary,
    vertexChainReversalHomotopy_boundary, singularReversalComponent_affineChain,
    singularAffineChain_boundary, singularReversalHomotopyComponent_affineChain]
  simp only [map_sub]

/-- The original cone homotopy has only components from degree n to degree n+1. -/
def singularReversalHomotopy : Homotopy (𝟙 (singularChains R X)) (singularReversal R X) where
  hom n m := if h : n + 1 = m then
      singularReversalHomotopyComponent R X n ≫
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
      change 𝟙 _ = singularReversalHomotopyComponent R X 0 ≫
        (singularChains R X).d 1 0 + singularReversalComponent R X 0
      rw [singularReversalHomotopyComponent_boundary_zero]
      abel
    | succ n =>
      rw [dNext_eq _ (by rfl : (ComplexShape.down ℕ).Rel (n + 1) n),
        prevD_eq _ (by rfl : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))]
      simp only [↓reduceDIte, eqToHom_refl, Category.comp_id]
      change 𝟙 _ = (singularChains R X).d (n + 1) n ≫
        singularReversalHomotopyComponent R X n +
        singularReversalHomotopyComponent R X (n + 1) ≫
          (singularChains R X).d (n + 2) (n + 1) + singularReversalComponent R X (n + 1)
      rw [singularReversalHomotopyComponent_boundary]
      abel

variable {X} {Y : Type u} [TopologicalSpace Y]

/-- Realizing the same affine expression commutes with postcomposition of its singular simplex. -/
theorem singularAffineChain_naturality (f : C(X, Y)) {n : ℕ}
    (σ : C(StdSimplex ℝ (Fin (n + 1)), X)) (k : ℕ)
    (c : SimplexVertexChain R (StdSimplex ℝ (Fin (n + 1))) (k + 1)) :
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f k (singularAffineChain R σ k c) =
      singularAffineChain R (f.comp σ) k c := by
  classical
  suffices h : (((singularChainsFunctor R).map (TopCat.ofHom f)).f k).hom.comp
      (singularAffineChain R σ k) = singularAffineChain R (f.comp σ) k from
    congrArg (fun g ↦ g c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, singularAffineChain_single]
  erw [(((singularChainsFunctor R).map (TopCat.ofHom f)).f k).hom.map_smul]
  congr 1
  change ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
    (singularAffineSimplex σ k v) ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom f))
        (singularCoefficient R)).f k) (ULift.up 1) = _
  rw [SSet.ι_chainComplexMap_f]
  rfl

/-- Signed reversal is natural for the actual chain map of any continuous map. -/
theorem singularReversal_naturality (f : C(X, Y)) :
    (singularChainsFunctor R).map (TopCat.ofHom f) ≫ singularReversal R Y =
      singularReversal R X ≫ (singularChainsFunctor R).map (TopCat.ofHom f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  have hgen : ((singularChainsFunctor R).map (TopCat.ofHom f)).f n
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
        (R := singularCoefficient R) (g.app (op ⦋n⦌) τ) a := by
    change ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex τ ≫
      (SSet.chainComplexMap g (singularCoefficient R)).f n) a = _
    rw [SSet.ι_chainComplexMap_f]
  change singularReversalComponent R Y n
      (((singularChainsFunctor R).map (TopCat.ofHom f)).f n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f n
      (singularReversalComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  rw [hgen, singularReversalComponent_generator, singularReversalComponent_generator]
  erw [(((singularChainsFunctor R).map (TopCat.ofHom f)).f n).hom.map_smul,
    singularAffineChain_naturality]
  rfl

/-- The specified cone homotopy is natural for continuous maps, keeping each simplex together. -/
theorem singularReversalHomotopyComponent_naturality (f : C(X, Y)) (n : ℕ) :
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f n ≫
        singularReversalHomotopyComponent R Y n =
      singularReversalHomotopyComponent R X n ≫
        ((singularChainsFunctor R).map (TopCat.ofHom f)).f (n + 1) := by
  apply SSet.chainComplex_hom_ext
  intro τ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let g := TopCat.toSSet.map (TopCat.ofHom f)
  have hgen : ((singularChainsFunctor R).map (TopCat.ofHom f)).f n
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a) =
      (TopCat.toSSet.obj (TopCat.of Y)).ιChainComplex
        (R := singularCoefficient R) (g.app (op ⦋n⦌) τ) a := by
    change ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex τ ≫
      (SSet.chainComplexMap g (singularCoefficient R)).f n) a = _
    rw [SSet.ι_chainComplexMap_f]
  change singularReversalHomotopyComponent R Y n
      (((singularChainsFunctor R).map (TopCat.ofHom f)).f n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a)) =
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f (n + 1)
      (singularReversalHomotopyComponent R X n
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex (R := singularCoefficient R) τ a))
  rw [hgen, singularReversalHomotopyComponent_generator,
    singularReversalHomotopyComponent_generator]
  erw [(((singularChainsFunctor R).map (TopCat.ofHom f)).f (n + 1)).hom.map_smul,
    singularAffineChain_naturality]
  rfl

/-- Every component of the original reversal homotopy commutes with continuous maps. -/
theorem singularReversalHomotopy_naturality (f : C(X, Y)) (n m : ℕ) :
    ((singularChainsFunctor R).map (TopCat.ofHom f)).f n ≫
        (singularReversalHomotopy R Y).hom n m =
      (singularReversalHomotopy R X).hom n m ≫
        ((singularChainsFunctor R).map (TopCat.ofHom f)).f m := by
  by_cases h : n + 1 = m
  · subst m
    simpa only [singularReversalHomotopy, ↓reduceDIte, eqToHom_refl, Category.comp_id] using
      singularReversalHomotopyComponent_naturality R f n
  · simp [singularReversalHomotopy, h]

end AtiyahSinger
