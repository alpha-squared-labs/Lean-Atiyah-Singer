/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticRepresentative
public import AtiyahSinger.Analysis.PseudodifferentialDensity
public import AtiyahSinger.Analysis.SmoothEllipticSum
public import AtiyahSinger.Analysis.SymbolIndexInvariance

/-!
# The analytic-index homomorphism on cotangent K theory

Public module ID: M0078.

A10: SG III.13 (13.7)--(13.8), pp.246--247, on a compact preconnected base.
The homomorphism is selected only after a theorem specifies its value on every
actual elliptic representative in the existing small smooth bundle model.
Its evaluation theorem also covers arbitrary-universe original bundle families.
Additivity follows from smooth direct sums, and independence of representatives
from symbol-class index invariance. The auxiliary density is explicit; a separate
theorem identifies the resulting homomorphisms for different densities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hP : PreconnectedSpace M] [MeasurableSpace M] [hB : BorelSpace M]
  (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

include hM hT hSC hC hP hB hμ in
/-- There is exactly one additive index map with the stated value on every representative. -/
theorem existsUnique_analyticIndex :
    ∃! I : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+ ℤ,
      ∀ (E F : SmoothFiniteComplexBundle (n := n) M) (m : ℝ)
        (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber μ m)
        (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
        (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
          E.Fiber F.Fiber m)
        (hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m
          (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic),
        I (P.symbolKClassOfHomogeneous R a hp hi) = P.toLinearMap.index := by
  classical
  -- Choose actual order-zero representatives; all later comparisons use their displayed classes.
  choose E F R a P hp hi hclass using fun u ↦
    exists_elliptic_pseudodifferential_representative_of_preconnected (n := n) μ u 0
  let f (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) : ℤ :=
    (P u).toLinearMap.index
  have heval (A B : SmoothFiniteComplexBundle (n := n) M) (m : ℝ)
      (Q : PseudodifferentialOperator (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber μ m)
      (S : QuantizationPresentation (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber)
      (b : homogeneousGlobalSymbolSpace (n := n) (r := A.rank) (q := B.rank) A.Fiber B.Fiber m)
      (hQ : Q.principalSymbol = globalPrincipalSymbolClass A.Fiber B.Fiber m
        (S.regularizedSymbol m b.val b.property.1 b.property.2)) (hj : Q.IsElliptic) :
      f (Q.symbolKClassOfHomogeneous S b hQ hj) = Q.toLinearMap.index := by
    exact (P _).index_eq_of_symbolKClass_eq (R _) (a _) (hp _) (hi _)
      Q S b hQ hj (hclass _)
  -- A genuine smooth direct-sum representative supplies additivity of the chosen values.
  have hadd (u v : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
      f (u + v) = f u + f v := by
    obtain ⟨A, B, S, b, Q, hQ, hj, hsum, hindex⟩ :=
      exists_elliptic_pseudodifferential_sum μ (E u) (F u) (E v) (F v)
        (R u) (a u) (P u) (hp u) (hi u) (R v) (a v) (P v) (hp v) (hi v)
    rw [hclass u, hclass v] at hsum
    exact (congrArg f hsum).symm.trans ((heval A B 0 Q S b hQ hj).trans hindex)
  let I : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+ ℤ :=
    AddMonoidHom.mk' f hadd
  refine ⟨I, heval, ?_⟩
  -- Every class has the selected representative, so the formula also forces uniqueness.
  intro J hJ
  apply AddMonoidHom.ext
  intro u
  have h := hJ (E u) (F u) 0 (P u) (R u) (a u) (hp u) (hi u)
  rw [hclass u] at h
  exact h

/-- The analytic index characterized by the indices of actual elliptic representatives. -/
def analyticIndex : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M)) →+ ℤ :=
  (existsUnique_analyticIndex μ).exists.choose

variable {r q : ℕ} {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hC hP hB hμ hE hF in
/-- The analytic index evaluates to the index of the original, possibly large-fiber PDO. -/
theorem PseudodifferentialOperator.analyticIndex_symbolKClassOfHomogeneous {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic) :
    analyticIndex μ (P.symbolKClassOfHomogeneous R a hp hi) = P.toLinearMap.index := by
  -- Evaluate the defining witness on one small representative of the original K class.
  obtain ⟨E₀, F₀, S, b, Q, hQ, hj, hclass⟩ :=
    exists_elliptic_pseudodifferential_representative_of_preconnected μ
      (P.symbolKClassOfHomogeneous R a hp hi) 0
  have hspec := (existsUnique_analyticIndex μ).exists.choose_spec
    E₀ F₀ 0 Q S b hQ hj
  -- Cross-bundle index invariance compares that same representative with the original PDO.
  rw [hclass] at hspec
  exact hspec.trans (Q.index_eq_of_symbolKClass_eq S b hQ hj P R a hp hi hclass)

include hM hT hSC hC hP hB hμ in
/-- Changing the smooth positive density leaves the analytic-index homomorphism unchanged. -/
theorem analyticIndex_independent_measure
    (ν : Measure M) [hν : IsSmoothPositiveMeasure (n := n) ν] :
    analyticIndex (n := n) μ = analyticIndex (n := n) ν := by
  apply AddMonoidHom.ext
  intro u
  -- Keep an actual representative and change only its density certificate.
  obtain ⟨E₀, F₀, R, a, P, hp, hi, hclass⟩ :=
    exists_elliptic_pseudodifferential_representative_of_preconnected μ u 0
  let Q := P.changeMeasure ν
  have hQ : Q.principalSymbol = globalPrincipalSymbolClass E₀.Fiber F₀.Fiber 0
      (R.regularizedSymbol 0 a.val a.property.1 a.property.2) :=
    (P.principalSymbol_changeMeasure ν).trans hp
  have hj : Q.IsElliptic := (P.isElliptic_changeMeasure_iff ν).mpr hi
  have hQclass : Q.symbolKClassOfHomogeneous R a hQ hj = u := hclass
  -- Both maps now evaluate on exactly the same smooth section operator and symbol.
  rw [← hclass, P.analyticIndex_symbolKClassOfHomogeneous μ R a hp hi]
  rw [hclass, ← hQclass, Q.analyticIndex_symbolKClassOfHomogeneous ν R a hQ hj]
  exact (P.index_changeMeasure ν).symm

end AtiyahSinger
