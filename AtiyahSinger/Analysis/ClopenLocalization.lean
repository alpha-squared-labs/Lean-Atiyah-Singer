/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HomogeneousSymbolOperatorComposition
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol
public import AtiyahSinger.Geometry.ClopenBundleProjection
public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Geometry.OpenSections
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Exact localization to a clopen base subset

Public module ID: M0331.

Multiplying an actual degree-zero PDO by the two original characteristic bundle
projections gives a supported operator. Its homogeneous principal representative
is the original symbol on the clopen subset and zero outside. Its exact action
is restriction followed by genuine zero extension on the input, and the same
characteristic projection on the output. Both assertions use one operator.

This is the elementary localization used in the finite-component extension of
SG III.13 (13.7)--(13.8). The localized operator is not asserted to be elliptic
on the whole base: its complement has zero symbol.
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

open scoped Classical in
/-- The actual clopen localization has both the localized symbol and the exact section action. -/
theorem PseudodifferentialOperator.exists_clopen_localization
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0)
    (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (s : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2))
    (U : Opens M) (hclosed : IsClosed (U : Set M)) :
    ∃ Q : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0,
      ∃ c : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0,
      Q.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
        (R.regularizedSymbol 0 c.val c.property.1 c.property.2) ∧
      (∀ (x : M) (ξ : CotangentFiber (n := n) x) (v : E.Fiber x),
        c.val x ξ v = if x ∈ U then s.val x ξ v else 0) ∧
      ∀ (u : smoothSections (n := n) (r := E.rank) E.Fiber) (x : M),
        (Q.toLinearMap u).val x = if x ∈ U then
          (P.toLinearMap
            (smoothSectionZeroExtension E.Fiber U (U : Set M) hclosed (Set.Subset.refl _)
              ⟨smoothSectionRestriction E.Fiber U u,
                fun y hy ↦ False.elim (hy y.property)⟩)).val x else 0 := by
  classical
  let cut (B : SmoothFiniteComplexBundle (n := n) M) (x : M) :
      B.Fiber x →ₗ[ℂ] B.Fiber x := if x ∈ U then LinearMap.id else 0
  have hcut (B : SmoothFiniteComplexBundle (n := n) M) :
      IsSmoothBundleMap (n := n) (r := B.rank) (q := B.rank) (cut B) :=
    isSmoothBundleMap_clopenIndicator B.Fiber U hclosed
  -- The same two smooth characteristic projections define the actual operator and symbol.
  let A := smoothBundleMapOperator (μ := μ) (cut E) (hcut E)
  let B := smoothBundleMapOperator (μ := μ) (cut F) (hcut F)
  obtain ⟨α, hα, hA⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ) (cut E) (hcut E)
  obtain ⟨β, hβ, hB⟩ := exists_homogeneousSymbol_smoothBundleMap (μ := μ) (cut F) (hcut F)
  obtain ⟨RA⟩ := nonempty_quantizationPresentation (n := n) (r := E.rank) (q := E.rank)
    (E := E.Fiber) (F := E.Fiber)
  obtain ⟨RB⟩ := nonempty_quantizationPresentation (n := n) (r := F.rank) (q := F.rank)
    (E := F.Fiber) (F := F.Fiber)
  let t : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0 :=
    ⟨globalSymbolComp s.val α.val, s.property.1.globalSymbolComp α.property.1,
      by simpa only [zero_add] using s.property.2.globalSymbolComp α.property.2⟩
  let c : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber 0 :=
    ⟨globalSymbolComp β.val t.val, β.property.1.globalSymbolComp t.property.1,
      by simpa only [zero_add] using β.property.2.globalSymbolComp t.property.2⟩
  let T : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨P.toLinearMap.comp A.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (P.comp A).isPseudodifferentialOperator⟩
  let Q : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
      E.Fiber F.Fiber μ 0 :=
    ⟨B.toLinearMap.comp T.toLinearMap, by
      simpa only [PseudodifferentialOperator.comp, zero_add] using
        (B.comp T).isPseudodifferentialOperator⟩
  have hT := principalSymbol_eq_regularizedSymbol_of_comp RA R R
    α s t A P T (hA RA) hp rfl (fun _ _ _ ↦ rfl)
  have hQ := principalSymbol_eq_regularizedSymbol_of_comp R RB R
    t β c T B Q hT (hB RB) rfl (fun _ _ _ ↦ rfl)
  refine ⟨Q, c, hQ, ?_, ?_⟩
  · intro x ξ v
    change β.val x ξ (s.val x ξ (α.val x ξ v)) = _
    rw [hα, hβ]
    by_cases hx : x ∈ U <;> simp [cut, hx]
  · intro u x
    -- The input projection is exactly the original restriction followed by zero extension.
    have hAz : A.toLinearMap u =
        smoothSectionZeroExtension E.Fiber U (U : Set M) hclosed (Set.Subset.refl _)
          ⟨smoothSectionRestriction E.Fiber U u,
            fun y hy ↦ False.elim (hy y.property)⟩ := by
      apply Subtype.ext
      funext y
      change cut E y (u.val y) = if hy : y ∈ U then u.val y else 0
      by_cases hy : y ∈ U <;> simp [cut, hy]
    change cut F x ((P.toLinearMap (A.toLinearMap u)).val x) = _
    rw [hAz]
    by_cases hx : x ∈ U <;> simp [cut, hx]

end AtiyahSinger
