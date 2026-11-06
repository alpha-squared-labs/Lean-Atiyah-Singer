/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClopenLocalization

/-!
# Diagonalization over a finite clopen cover

Public module ID: M0329.

Sum the actual localized PDOs for a finite disjoint clopen cover. Their
homogeneous principal symbols add to the supplied original symbol, and each
restriction of the new operator is the corresponding original diagonal block.
This implements the finite-component index argument without assuming that
the original PDO preserves components or discarding its off-diagonal action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)

/-- Clopen diagonalization preserves the principal symbol and the exact diagonal section blocks. -/
theorem PseudodifferentialOperator.exists_clopen_diagonal {ι : Type*} [Finite ι]
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0)
    (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2))
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0,
      Q.principalSymbol = P.principalSymbol ∧
      ∀ (i : ι) (u : smoothSections (n := n) (r := E.rank) E.Fiber) (x : U i),
        (Q.toLinearMap u).val x.val =
          (P.toLinearMap
            (smoothSectionZeroExtension E.Fiber (U i) (U i : Set M) (hclosed i)
              (Set.Subset.refl _)
              ⟨smoothSectionRestriction E.Fiber (U i) u,
                fun y hy ↦ False.elim (hy y.property)⟩)).val x.val := by
  classical
  let := Fintype.ofFinite ι
  -- Localize each piece using its actual supported operator and homogeneous representative.
  choose D c hD hc hpoint using fun i ↦
    P.exists_clopen_localization μ E F R s hp (U i) (hclosed i)
  let Q := pseudodifferentialOperatorOfSpace (∑ i, (D i).toSpace)
  refine ⟨Q, ?_, ?_⟩
  · -- One partition term acts as the identity at each point, so the principal sum is unchanged.
    let reg : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber 0 →ₗ[ℂ] globalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber 0 := {
      toFun a := R.regularizedSymbol 0 a.val a.property.1 a.property.2
      map_add' a b := Subtype.ext (R.regularizedSymbolFunction_add a.val b.val)
      map_smul' z a := Subtype.ext (R.regularizedSymbolFunction_smul z a.val) }
    have hsum (x : M) (ξ : CotangentFiber (n := n) x) (_hξ : ξ ≠ 0) :
        (∑ i, c i).val x ξ = s.val x ξ := by
      apply ContinuousLinearMap.ext
      intro v
      have hx : x ∈ ⋃ i, (U i : Set M) := hcover.symm ▸ Set.mem_univ x
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply, hc]
      rw [Finset.sum_eq_single i]
      · exact ite_eq_left hi
      · intro j _ hji
        apply ite_eq_right
        intro hj
        exact Set.disjoint_left.mp (hdisjoint hji) hj hi
      · intro hi'
        exact False.elim (hi' (Finset.mem_univ i))
    change principalSymbolLinearMap E.Fiber F.Fiber μ 0 (∑ i, (D i).toSpace) = _
    rw [map_sum]
    change (∑ i, (D i).principalSymbol) = P.principalSymbol
    simp_rw [hD]
    change (∑ i, globalPrincipalSymbolClass E.Fiber F.Fiber 0 (reg (c i))) = _
    rw [← map_sum, ← map_sum, hp]
    exact (R.regularizedSymbol_class_eq_iff R 0 (∑ i, c i).val s.val
      (∑ i, c i).property.1 (∑ i, c i).property.2 s.property.1 s.property.2).mpr hsum
  · intro i u x
    -- Restriction to this piece removes every other output projection.
    have hQ : (Q.toLinearMap u).val x.val = ∑ j, ((D j).toLinearMap u).val x.val := by
      simp only [Q, pseudodifferentialOperatorOfSpace, Submodule.coe_sum,
        PseudodifferentialOperator.toSpace, LinearMap.sum_apply, Finset.sum_apply]
    rw [hQ]
    simp_rw [hpoint]
    rw [Finset.sum_eq_single i]
    · exact ite_eq_left x.property
    · intro j _ hji
      apply ite_eq_right
      intro hj
      exact Set.disjoint_left.mp (hdisjoint hji) hj x.property
    · intro hi'
      exact False.elim (hi' (Finset.mem_univ i))

end AtiyahSinger
