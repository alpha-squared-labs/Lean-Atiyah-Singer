/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.IndexDirectSum
public import AtiyahSinger.Analysis.OperatorOrderShift
public import AtiyahSinger.Analysis.TrivialSymbolKIndex

/-!
# The index depends only on the actual compact-support symbol class

Public module ID: M1023.

A10: the well-definedness argument in SG III.13, pp.246--247. The operators
may have different source and target bundles and different real orders.
Equality is in the existing Kc group, not a hypothesized unstabilized homotopy.
The equivariant stable-germ comparison is applied to the one-element
group after actual smooth small-model comparisons. The general order shift
preserves the two original indices and compact-support symbol classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r q r' q' : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  {G : M → Type*}
  [∀ x, NormedAddCommGroup (G x)] [∀ x, NormedSpace ℂ (G x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r')) G)]
  [FiberBundle (EuclideanSpace ℂ (Fin r')) G]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r')) G]
  {H : M → Type*}
  [∀ x, NormedAddCommGroup (H x)] [∀ x, NormedSpace ℂ (H x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q')) H)]
  [FiberBundle (EuclideanSpace ℂ (Fin q')) H]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q')) H]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  [hG : IsSmoothComplexBundle (n := n) (r := r') G]
  [hH : IsSmoothComplexBundle (n := n) (r := q') H]
  [MeasurableSpace M] [hB : BorelSpace M]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

include hM hT hSC hC hE hF hG hH hB hμ in
/-- Equal compact-support classes of displayed elliptic symbols give equal smooth indices. -/
theorem index_eq_of_symbolKClass_eq {m l : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (hP : P.principalSymbol = globalPrincipalSymbolClass E F m
      (R.regularizedSymbol m a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (Q : PseudodifferentialOperator (n := n) (r := r') (q := q') G H μ l)
    (S : QuantizationPresentation (n := n) (r := r') (q := q') G H)
    (b : homogeneousGlobalSymbolSpace (n := n) (r := r') (q := q') G H l)
    (hQ : Q.principalSymbol = globalPrincipalSymbolClass G H l
      (S.regularizedSymbol l b.val b.property.1 b.property.2)) (hj : Q.IsElliptic)
    (hab : P.symbolKClassOfHomogeneous R a hP hi =
      Q.symbolKClassOfHomogeneous S b hQ hj) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  classical
  -- The general Fredholm-corrected order shift preserves each original index and K class.
  obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  have hia := (P.isElliptic_iff_homogeneous R a hP).mp hi
  have hib := (Q.isElliptic_iff_homogeneous S b hQ).mp hj
  obtain ⟨P₀, a₀, ha₀, _, _, hP₀, _, hi₀, hindexP, hKP⟩ :=
    P.exists_orderShift g R a hP hia 0
  obtain ⟨Q₀, b₀, hb₀, _, _, hQ₀, _, hj₀, hindexQ, hKQ⟩ :=
    Q.exists_orderShift g S b hQ hib 0
  have hK : homogeneousSymbolKClass 0 a₀ ha₀ = homogeneousSymbolKClass 0 b₀ hb₀ :=
    hKP.trans (hab.trans hKQ.symm)
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r')) G
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q')) H
  let : ContinuousSMul PUnit.{1} M := ⟨continuous_snd⟩
  let := punitContMDiffSMul (n := n) (M := M)
  -- Apply the one-element-group specialization to the same degree-zero symbols.
  let σE := ComplexBundle.EquivariantStructure.ofSubsingleton (G := PUnit.{1}) E
  have hσE := σE.isSmooth_of_subsingleton (n := n) (r := r) 𝓘(ℝ, PUnit.{1})
  let σF := ComplexBundle.EquivariantStructure.ofSubsingleton (G := PUnit.{1}) F
  have hσF := σF.isSmooth_of_subsingleton (n := n) (r := q) 𝓘(ℝ, PUnit.{1})
  let σG := ComplexBundle.EquivariantStructure.ofSubsingleton (G := PUnit.{1}) G
  have hσG := σG.isSmooth_of_subsingleton (n := n) (r := r') 𝓘(ℝ, PUnit.{1})
  let σH := ComplexBundle.EquivariantStructure.ofSubsingleton (G := PUnit.{1}) H
  have hσH := σH.isSmooth_of_subsingleton (n := n) (r := q') 𝓘(ℝ, PUnit.{1})
  have haG (g : PUnit.{1}) (x : M) (ξ : CotangentFiber (n := n) x) (_ : ξ ≠ 0) :
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, PUnit.{1}) σE σF g a₀.val x ξ = a₀.val x ξ :=
    congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
      𝓘(ℝ, PUnit.{1}) σE σF hσE hσF a₀.val g) x) ξ
  have hbG (g : PUnit.{1}) (x : M) (ξ : CotangentFiber (n := n) x) (_ : ξ ≠ 0) :
      equivariantGlobalSymbolLinearMap 𝓘(ℝ, PUnit.{1}) σG σH g b₀.val x ξ = b₀.val x ξ :=
    congrFun (congrFun (equivariantGlobalSymbolLinearMap_eq_of_subsingleton
      𝓘(ℝ, PUnit.{1}) σG σH hσG hσH b₀.val g) x) ξ
  have hindex := congrArg (representationDimension PUnit.{1})
    (equivariantHomogeneousAnalyticIndex_eq_of_homogeneousSymbolKClass_eq
      σE σF σG σH hσE hσF hσG hσH a₀ b₀ ha₀ hb₀ haG hbG hK)
  have hleft := representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
    𝓘(ℝ, PUnit.{1}) σE σF hσE hσF a₀ ha₀ haG μ R P₀ hi₀ hP₀
  have hright := representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
    𝓘(ℝ, PUnit.{1}) σG σH hσG hσH b₀ hb₀ hbG μ S Q₀ hj₀ hQ₀
  -- Return through the original smooth isomorphisms used in order reduction.
  exact hindexP.symm.trans ((hleft.symm.trans (hindex.trans hright)).trans hindexQ)

end PseudodifferentialOperator

end AtiyahSinger
