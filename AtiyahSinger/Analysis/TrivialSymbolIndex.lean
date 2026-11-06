/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantHomogeneousAnalyticIndex
public import AtiyahSinger.Analysis.EquivariantSymbolCovariance
public import AtiyahSinger.Geometry.TrivialSmoothEquivariance
public import AtiyahSinger.Topology.TrivialEquivariantKTheory

/-!
# Ordinary indices as dimensions for the one-element group

Public module ID: M1037.

Every actual operator and symbol is equivariant for a subsingleton group.
Evaluating the already constructed homogeneous equivariant index at the
original order-zero PDO, then taking dimension, recovers its smooth index.
The original density and bundle universes are retained. This comparison is
used for ordinary index descent through the equivariant stable-germ theorem.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [Subsingleton G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hLie : LieGroup IG ∞ G]
  [hGC : CompactSpace G] [hGT : T2Space G]
  [hGM : MeasurableSpace G] [hGB : BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)


omit hT2 hSC hC [MeasurableSpace M] hBorel hGC hGT hGM hGB in
include hσE hσF in
/-- The only group element fixes every original symbol, including its zero-section values. -/
theorem equivariantGlobalSymbolLinearMap_eq_of_subsingleton
    (a : GlobalSymbolFunction (n := n) E F) (g : G) :
    equivariantGlobalSymbolLinearMap IG σE σF g a = a := by
  rw [Subsingleton.elim g 1]
  exact congrArg (fun T ↦ T a)
    (equivariantGlobalSymbolAction_properties IG σE σF hσE hσF).2.1

/-- Taking dimension of the trivial-action symbol index gives the original smooth PDO index. -/
theorem representationDimension_equivariantHomogeneousAnalyticIndex_of_subsingleton
    (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (hi : IsEllipticGlobalSymbol E F s.val)
    (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
      equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)
    (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hP : P.IsElliptic)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E F 0
      (R.regularizedSymbol 0 s.val s.property.1 s.property.2)) :
    representationDimension G
        (equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs) =
      P.toLinearMap.index := by
  classical
  -- The supplied density is already invariant; no change of realization is made.
  have hμ : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ := by
    intro g
    simp only [Subsingleton.elim g 1, one_smul]
    exact Measure.map_id
  have hPg : P.IsEquivariant IG σE σF hσE hσF := by
    intro g
    simp only [Subsingleton.elim g 1, map_one, Module.End.one_eq_id,
      LinearMap.comp_id, LinearMap.id_comp]
  obtain ⟨h, hInv⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInv⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  -- Evaluate the same canonical witness, then forget its kernel and cokernel actions.
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF s hi hs
    μ inferInstance h k hInv kInv hμ R P hPg hP hp]
  exact P.representationDimension_equivariantAnalyticIndex IG σE σF hσE hσF
    h k hInv kInv hμ hPg hP

end AtiyahSinger
