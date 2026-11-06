/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.DifferentialParametrix
public import AtiyahSinger.Analysis.HomogeneousSymbolTopology
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Geometry.SmoothSectionEvaluation

/-!
# Principal homogeneous symbol of multiplication by a smooth bundle map

Public module ID: M0963.

The actual order-zero multiplication PDO has the specified fiber map as its
homogeneous principal symbol at every covector. Its principal quotient class
is computed using any supplied regularization presentation. This comparison
connects geometric bundle maps with the original homogeneous symbol index,
without introducing a different symbol carrier or a choice of Hermitian metric.

Source: the degree-zero case of the principal polynomial in SG III.3; the
explicit equality with arbitrary global regularizations is a project supplement.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

/-- The specified smooth map is the homogeneous symbol of its actual multiplication PDO,
and every regularization gives that same principal quotient class. -/
theorem exists_homogeneousSymbol_smoothBundleMap
    (a : ∀ x, E x →ₗ[ℂ] F x) (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    ∃ s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0,
      (∀ x ξ u, s.val x ξ u = a x u) ∧
      ∀ R : QuantizationPresentation (n := n) (r := r) (q := q) E F,
        (smoothBundleMapOperator (μ := μ) a ha).principalSymbol =
          globalPrincipalSymbolClass E F 0
            (R.regularizedSymbol 0 s.val s.property.1 s.property.2) := by
  set_option backward.isDefEq.respectTransparency false in
  exact by
    classical
    let D : DifferentialOperator (n := n) (r := r) (q := q) E F 0 :=
      ⟨smoothSectionMap a ha,
        isDifferentialOperator_smoothSectionMap a ha⟩
    let P := smoothBundleMapOperator (μ := μ) a ha
    let : ∀ x, FiniteDimensional ℂ (E x) :=
      fun x ↦ VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
    have hsymbol (x : M)
        (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ) :
        D.principalSymbolFunction x ξ = (a x).toContinuousLinearMap := by
      ext v
      let c := chartAt (EuclideanSpace ℝ (Fin n)) x
      let e' := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      let f' := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
      have hxc : x ∈ c.source := mem_chart_source _ x
      have hxe : x ∈ e'.baseSet := mem_baseSet_trivializationAt _ E x
      have hxf : x ∈ f'.baseSet := mem_baseSet_trivializationAt _ F x
      obtain ⟨U, hU, hxU, Q, hQ⟩ := D.isDifferentialOperator c (chart_mem_atlas _ x)
        e' f' x ⟨⟨hxc, hxe⟩, hxf⟩
      obtain ⟨u, hu⟩ := exists_smoothSection_apply_eq (n := n) (r := r) x v
      -- At order zero both the operator and its principal polynomial use the same coefficient.
      have hvalue := hQ.2 u x hxU
      have hsection : sectionInChart E c e' u.val (c x) = (e' ⟨x, v⟩).2 := by
        unfold sectionInChart
        rw [c.left_inv hxc, hu]
      let : Inhabited (Fin (0 : Fin (0 + 1)).val → Fin n) := ⟨Fin.elim0⟩
      have hcoeff : (f' ⟨x, a x v⟩).2 =
          Q.coefficient 0 default (c x) (e'.linearMapAt ℂ x v) := by
        simpa [CoordinateDifferentialOperator.apply, hsection, D, smoothSectionMap, hu,
          e'.coe_linearMapAt_of_mem hxe] using hvalue
      have hprincipal := LinearMap.congr_fun
        (D.hasPrincipalSymbol c (chart_mem_atlas _ x) e' f' U hU Q hQ x hxU ξ) v
      have hsame : f'.linearMapAt ℂ x (D.principalSymbol x ξ v) =
          f'.linearMapAt ℂ x (a x v) := by
        simpa [CoordinateDifferentialOperator.principalSymbol,
          f'.coe_linearMapAt_of_mem hxf, hcoeff] using hprincipal
      have hcancel := congrArg (f'.symmL ℂ x) hsame
      change D.principalSymbol x ξ v = a x v
      simpa only [f'.coe_linearMapAt_of_mem hxf, f'.symmL_apply hxf,
        f'.symm_apply_apply_mk hxf] using hcancel
    have hhD : IsHomogeneousGlobalSymbol E F 0 D.principalSymbolFunction := by
      simpa only [Nat.cast_zero] using D.isHomogeneousGlobalSymbol_principalSymbolFunction
    let s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0 :=
      ⟨D.principalSymbolFunction, D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction, hhD⟩
    refine ⟨s, fun x ξ u ↦ DFunLike.congr_fun (hsymbol x ξ) u, ?_⟩
    intro R
    -- The natural differential order is transported to the exact real order of multiplication.
    have htransfer (l : ℝ) (hl : l = 0)
        (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ l)
        (hh : IsHomogeneousGlobalSymbol E F l D.principalSymbolFunction)
        (hQ : Q.toLinearMap = P.toLinearMap)
        (hQclass : Q.principalSymbol = globalPrincipalSymbolClass E F l
          (R.regularizedSymbol l D.principalSymbolFunction
            D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction hh)) :
        P.principalSymbol = globalPrincipalSymbolClass E F 0
          (R.regularizedSymbol 0 D.principalSymbolFunction
            D.isSmoothOffZeroGlobalSymbol_principalSymbolFunction hhD) := by
      subst l
      exact (P.principalSymbol_eq_of_toLinearMap_eq μ Q hQ.symm).trans hQclass
    exact htransfer _ Nat.cast_zero (D.toPseudodifferentialOperator μ)
      D.isHomogeneousGlobalSymbol_principalSymbolFunction rfl
      (D.principalSymbol_eq_regularizedSymbol μ R)

end AtiyahSinger
