/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Finite vertex chains for affine subdivision

Public module ID: M1522.

An augmented vertex chain with k vertices is a finite linear combination of
ordered k-tuples. The alternating boundary deletes a vertex; coning prepends
one vertex. These are the finite combinatorial expressions used to construct
barycentric subdivision on the original singular chains, not a replacement
homology or cohomology theory. Geometric realization is supplied separately.

The cone identity gives the boundary-square identity by induction on the number
of vertices. This is the standard affine-chain calculation in the proof of
singular excision (Hatcher, section 2.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

universe u v

variable (R : Type u) [CommRing R] (E : Type v)

/-- Finite augmented vertex chains; k is the number of vertices, not the dimension. -/
abbrev SimplexVertexChain (k : ℕ) : Type (max u v) := (Fin k → E) →₀ R

/-- The alternating deletion of vertices on finite chains. -/
def vertexChainBoundary (k : ℕ) :
    SimplexVertexChain R E (k + 1) →ₗ[R] SimplexVertexChain R E k :=
  Finsupp.linearCombination R (fun v : Fin (k + 1) → E ↦
    ∑ i : Fin (k + 1), (-1 : R) ^ i.val • Finsupp.single (v ∘ i.succAbove) 1)

/-- Coning a vertex chain prepends the specified vertex, including for the empty tuple. -/
def vertexChainCone (x : E) (k : ℕ) :
    SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R E (k + 1) :=
  Finsupp.lmapDomain R R (fun v : Fin k → E ↦ Fin.cons x v)

/-- A map of vertices acts on the same ordered tuples and coefficients. -/
def vertexChainMap {F : Type*} (f : E → F) (k : ℕ) :
    SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R F k :=
  Finsupp.lmapDomain R R (fun v ↦ f ∘ v)

variable {E}

/-- Boundary of a generator is its actual alternating sum of faces. -/
theorem vertexChainBoundary_single (k : ℕ) (v : Fin (k + 1) → E) (a : R) :
    vertexChainBoundary R E k (Finsupp.single v a) =
      a • ∑ i : Fin (k + 1), (-1 : R) ^ i.val • Finsupp.single (v ∘ i.succAbove) 1 := by
  exact Finsupp.linearCombination_single _ _ _

/-- A coned generator has exactly the original coefficient and prepended ordered vertex. -/
@[simp]
theorem vertexChainCone_single (x : E) (k : ℕ) (v : Fin k → E) (a : R) :
    vertexChainCone R E x k (Finsupp.single v a) = Finsupp.single (Fin.cons x v) a := by
  simp [vertexChainCone]

/-- The cone boundary in positive tuple length is the base minus the cone of its boundary. -/
theorem vertexChainBoundary_cone (x : E) (k : ℕ)
    (c : SimplexVertexChain R E (k + 1)) :
    vertexChainBoundary R E (k + 1) (vertexChainCone R E x (k + 1) c) =
      c - vertexChainCone R E x k (vertexChainBoundary R E k c) := by
  classical
  -- Both sides are linear; on one simplex the first face is the original base.
  suffices h : (vertexChainBoundary R E (k + 1)).comp (vertexChainCone R E x (k + 1)) =
      LinearMap.id - (vertexChainCone R E x k).comp (vertexChainBoundary R E k) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, vertexChainCone_single, vertexChainBoundary_single,
    LinearMap.sub_apply, LinearMap.id_apply, map_smul, map_sum]
  have hsucc (i : Fin (k + 1)) :
      (Fin.cons x v) ∘ i.succ.succAbove = Fin.cons x (v ∘ i.succAbove) := by
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · simp
    · simp
  -- Every remaining face has the opposite sign of the corresponding coned face.
  rw [Fin.sum_univ_succ]
  simp [hsucc, pow_succ, Finset.smul_sum, sub_eq_add_neg,
    smul_add, Finsupp.smul_single]

/-- In augmented degree minus one, the boundary of a cone is its empty base. -/
theorem vertexChainBoundary_cone_zero (x : E) (c : SimplexVertexChain R E 0) :
    vertexChainBoundary R E 0 (vertexChainCone R E x 0 c) = c := by
  classical
  suffices h : (vertexChainBoundary R E 0).comp (vertexChainCone R E x 0) =
      LinearMap.id from congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp [vertexChainBoundary_single, Finsupp.smul_single]

/-- The alternating boundary squares to zero, including at the augmentation. -/
theorem vertexChainBoundary_boundary (k : ℕ) (c : SimplexVertexChain R E (k + 2)) :
    vertexChainBoundary R E k (vertexChainBoundary R E (k + 1) c) = 0 := by
  classical
  induction k with
  | zero =>
    suffices h : (vertexChainBoundary R E 0).comp (vertexChainBoundary R E 1) = 0 from
      congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    -- A two-vertex simplex is a cone on its last vertex, with the same coefficient.
    have hv : Fin.cons (v 0) (fun j : Fin 1 ↦ v j.succ) = v := by
      funext j
      exact Fin.cases rfl (fun _ ↦ rfl) j
    change vertexChainBoundary R E 0
      (vertexChainBoundary R E 1 (Finsupp.single v a)) = 0
    rw [← hv, ← vertexChainCone_single, vertexChainBoundary_cone, map_sub,
      vertexChainBoundary_cone_zero, sub_self]
  | succ k hk =>
    suffices h : (vertexChainBoundary R E (k + 1)).comp
        (vertexChainBoundary R E (k + 2)) = 0 from congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    have hv : Fin.cons (v 0) (fun j : Fin (k + 2) ↦ v j.succ) = v := by
      funext j
      exact Fin.cases rfl (fun _ ↦ rfl) j
    change vertexChainBoundary R E (k + 1)
      (vertexChainBoundary R E (k + 2) (Finsupp.single v a)) = 0
    -- Apply the cone identity twice; the lower-dimensional boundary square vanishes.
    rw [← hv, ← vertexChainCone_single, vertexChainBoundary_cone, map_sub,
      vertexChainBoundary_cone, hk, map_zero, sub_zero, sub_self]

/-- Mapping the vertices commutes with the alternating boundary of the same tuples. -/
theorem vertexChainMap_boundary {F : Type*} (f : E → F) (k : ℕ)
    (c : SimplexVertexChain R E (k + 1)) :
    vertexChainMap R E f k (vertexChainBoundary R E k c) =
      vertexChainBoundary R F k (vertexChainMap R E f (k + 1) c) := by
  classical
  suffices h : (vertexChainMap R E f k).comp (vertexChainBoundary R E k) =
      (vertexChainBoundary R F k).comp (vertexChainMap R E f (k + 1)) from
    congrArg (fun g ↦ g c) h
  apply Finsupp.lhom_ext
  intro v a
  simp [vertexChainMap, vertexChainBoundary_single, Function.comp_assoc]

/-- Mapping a coned chain retains the image of the same cone vertex. -/
theorem vertexChainMap_cone {F : Type*} (f : E → F) (x : E) (k : ℕ)
    (c : SimplexVertexChain R E k) :
    vertexChainMap R E f (k + 1) (vertexChainCone R E x k c) =
      vertexChainCone R F (f x) k (vertexChainMap R E f k c) := by
  classical
  suffices h : (vertexChainMap R E f (k + 1)).comp (vertexChainCone R E x k) =
      (vertexChainCone R F (f x) k).comp (vertexChainMap R E f k) from
    congrArg (fun g ↦ g c) h
  apply Finsupp.lhom_ext
  intro v a
  have htuple : f ∘ Fin.cons x v = Fin.cons (f x) (f ∘ v) := by
    funext j
    exact Fin.cases rfl (fun _ ↦ rfl) j
  simp [vertexChainMap, htuple]

end AtiyahSinger
