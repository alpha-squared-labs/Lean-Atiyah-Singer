/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol

/-!
# The principal class of an actual finite sum of bundle operators

Public module ID: M0294.

Concatenating the original finite local representations, including their actual
all-order remainders, proves additivity of the representation-independent
principal quotient. The supplied total operator has exactly the sum action;
no alternate operator or homogeneous symbol representative is chosen.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]

namespace AtlasPseudodifferentialOperator

/-- The original principal quotient preserves a specified finite sum of actual section maps. -/
theorem principalSymbol_eq_sum {ι : Type*} [Fintype ι] {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m) (Q : ι → AtlasPseudodifferentialOperator A B m)
    (hP : P.toLinearMap = ∑ i, (Q i).toLinearMap) :
    P.principalSymbol = ∑ i, (Q i).principalSymbol := by
  classical
  -- Reindex the actual local pieces, retaining each original smoothing difference.
  choose N L hL using fun i ↦ (Q i).isPseudodifferentialOperator
  let Ntotal := Fintype.card (Σ i, Fin (N i))
  let e : Fin Ntotal ≃ Σ i, Fin (N i) := (Fintype.equivFin _).symm
  let K (j : Fin Ntotal) := L (e j).1 (e j).2
  have hsumMaps : (∑ j, (K j).toLinearMap) = ∑ i, ∑ j, (L i j).toLinearMap := by
    simpa only [K, Fintype.sum_sigma] using
      (Fintype.sum_equiv e (fun j ↦ (K j).toLinearMap)
        (fun ij ↦ (L ij.1 ij.2).toLinearMap) (fun _ ↦ rfl))
  have hrem : IsAtlasSmoothingOperator A B (P.toLinearMap - ∑ j, (K j).toLinearMap) := by
    intro Li Lo s t
    choose R hR using fun i ↦ hL i Li Lo s t
    refine ⟨∑ i, R i, ?_⟩
    intro u
    calc
      (∑ i, R i) (Li.smoothToSobolev s u) =
          ∑ i, Lo.smoothToSobolev t (((Q i).toLinearMap - ∑ j, (L i j).toLinearMap) u) := by
        simp only [sum_apply, hR]
      _ = Lo.smoothToSobolev t ((P.toLinearMap - ∑ j, (K j).toLinearMap) u) := by
        rw [hP, hsumMaps]
        simp only [LinearMap.sub_apply, LinearMap.sum_apply, map_sub, map_sum,
          Finset.sum_sub_distrib]
  have hsumSymbols : (∑ j, (K j).globalSymbol) = ∑ i, ∑ j, (L i j).globalSymbol := by
    simpa only [K, Fintype.sum_sigma] using
      (Fintype.sum_equiv e (fun j ↦ (K j).globalSymbol)
        (fun ij ↦ (L ij.1 ij.2).globalSymbol) (fun _ ↦ rfl))
  -- The canonical quotient map is linear, after the actual representations have been identified.
  calc
    P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m (∑ j, (K j).globalSymbol) :=
      P.principalSymbol_eq_of_representation Ntotal K hrem
    _ = ∑ i, atlasGlobalPrincipalSymbolClass A B m (∑ j, (L i j).globalSymbol) := by
      rw [hsumSymbols, map_sum]
    _ = ∑ i, (Q i).principalSymbol :=
      Finset.sum_congr rfl (fun i _ ↦ ((Q i).principalSymbol_eq_of_representation
        (N i) (L i) (hL i)).symm)

end AtlasPseudodifferentialOperator

end AtiyahSinger
