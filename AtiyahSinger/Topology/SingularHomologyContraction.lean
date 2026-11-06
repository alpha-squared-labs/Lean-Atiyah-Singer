/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.AlgebraicTopology.SimplicialSet.Homology.Nondegenerate
public import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Homotopy and contractible-space calculations for the original singular homology

Public module ID: M2144.

Positive-degree homology of a point is computed using the normalized complex of
its actual singular simplicial set. Homotopy retractions then transfer vanishing,
with no replacement of the project's coefficient module or singular chains.
These standard calculations are the base cases for Euclidean local homology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R]

/-- The empty space has zero singular homology in every degree. -/
theorem subsingleton_singularHomology_of_isEmpty
    (X : Type u) [TopologicalSpace X] [IsEmpty X] (k : ℕ) :
    Subsingleton (singularHomology R X k) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  let : S.HasDimensionLT 0 :=
    { degenerate_eq_top := fun n _ ↦ Set.eq_univ_of_forall fun σ ↦
        isEmptyElim (((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) σ)
          (Convexity.StdSimplex.single 0)) }
  exact ModuleCat.isZero_iff_subsingleton.mp
    (S.isZero_homology_of_hasDimensionLT (singularCoefficient R) k 0)

/-- Homotopic continuous maps induce the same map on the original homology. -/
theorem singularHomologyMap_eq_of_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : f.Homotopic g) (k : ℕ) :
    singularHomologyMap R f k = singularHomologyMap R g k := by
  obtain ⟨H⟩ := h
  exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor
    (f := TopCat.ofHom f) (g := TopCat.ofHom g) H (singularCoefficient R) k

/-- A space with at most one point has no positive-degree singular homology. -/
theorem subsingleton_singularHomology_of_subsingleton
    (X : Type u) [TopologicalSpace X] [Subsingleton X] (k : ℕ) (hk : 0 < k) :
    Subsingleton (singularHomology R X k) := by
  let S := TopCat.toSSet.obj (TopCat.of X)
  have hsimplex (n : ℕ) : Subsingleton (S.obj (op ⦋n⦌)) :=
    ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌)).injective.subsingleton
  -- Every positive-dimensional singular simplex is a degeneracy of one of its faces.
  let : S.HasDimensionLT 1 :=
    { degenerate_eq_top := by
        intro n hn
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        apply Set.eq_univ_of_forall
        intro σ
        have : S.σ 0 (S.δ 0 σ) = σ := (hsimplex (m + 1)).elim _ _
        rw [← this]
        exact S.σ_mem_degenerate 0 (S.δ 0 σ) }
  -- Normalization is a genuine chain homotopy equivalence over the original ring.
  exact ModuleCat.isZero_iff_subsingleton.mp
    (S.isZero_homology_of_hasDimensionLT (singularCoefficient R) k 1 hk)

/-- Homology vanishing passes to a space that is a homotopy retract of the given space. -/
theorem subsingleton_singularHomology_of_homotopy_retract
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (g : C(Y, X)) (h : (g.comp f).Homotopic (ContinuousMap.id X))
    (k : ℕ) [Subsingleton (singularHomology R Y k)] :
    Subsingleton (singularHomology R X k) := by
  have hmaps : singularHomologyMap R f k ≫ singularHomologyMap R g k =
      𝟙 (singularHomology R X k) := by
    change HomologicalComplex.homologyMap
      ((singularChainsFunctor R).map (TopCat.ofHom f)) k ≫
        HomologicalComplex.homologyMap ((singularChainsFunctor R).map (TopCat.ofHom g)) k = _
    rw [← HomologicalComplex.homologyMap_comp]
    rw [← Functor.map_comp]
    have heq := singularHomologyMap_eq_of_homotopic R h k
    change HomologicalComplex.homologyMap
      ((singularChainsFunctor R).map (TopCat.ofHom (g.comp f))) k = _ at heq
    exact heq.trans (by simp [singularHomologyMap])
  refine ⟨fun x y ↦ ?_⟩
  have h := congrArg (fun z ↦ singularHomologyMap R g k z)
    (Subsingleton.elim (singularHomologyMap R f k x) (singularHomologyMap R f k y))
  simpa only [← ModuleCat.comp_apply, hmaps, ModuleCat.id_apply] using h

/-- The original singular homology of a contractible space vanishes in positive degrees. -/
theorem subsingleton_singularHomology_of_contractible
    (X : Type u) [TopologicalSpace X] [ContractibleSpace X] (k : ℕ) (hk : 0 < k) :
    Subsingleton (singularHomology R X k) := by
  obtain ⟨x, hx⟩ := id_nullhomotopic X
  let f : C(X, PUnit.{u + 1}) := ContinuousMap.const _ PUnit.unit
  let g : C(PUnit.{u + 1}, X) := ContinuousMap.const _ x
  let := subsingleton_singularHomology_of_subsingleton R PUnit.{u + 1} k hk
  exact subsingleton_singularHomology_of_homotopy_retract R f g hx.symm k

end AtiyahSinger
