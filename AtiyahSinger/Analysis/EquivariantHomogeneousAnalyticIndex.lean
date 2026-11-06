/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantDensityIndex
public import AtiyahSinger.Analysis.EquivariantHomogeneousIndexHomotopy
public import AtiyahSinger.Analysis.EquivariantQuantization
public import AtiyahSinger.Analysis.OperatorSymbolKClass
public import AtiyahSinger.Geometry.EquivariantSmoothDensity
public import AtiyahSinger.Geometry.SmoothInvariantMetric

/-!
# The full equivariant analytic index of a fixed homogeneous elliptic symbol

Public module ID: M0519.

The original smooth bundles, their original actions and the actual homogeneous
symbol determine one virtual representation index. Its universal value
characterization compares every actual equivariant elliptic realization,
allowing independent regularizations, invariant smooth metrics and positive
invariant smooth densities. Existence of one such realization is proved before
uniqueness; the characterization is not an assumed index service.

Sources: SG III.9, Definition 9.3, Proposition 9.4, Corollary 9.6 and
Theorem 9.7, pp.212--214. The original homogeneous PDO formulation and explicit
auxiliary-choice comparison are supplements. SG III.13, pp.245--247, treats
the further descent through K-theory relations as a separate problem.

Only degree zero is considered here. The Lie-group hypothesis is inherited
from the existing invariant smooth-density existence statement; there is no
additional finite-dimensional group-model hypothesis. Empty bases, dimension
zero and independent source/target ranks remain admitted. The existence,
choice independence and homogeneous homotopy invariance below are proved.
Descent to the original equivariant compact-support K group remains separate.
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
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
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


include hM hT2 hSC hC hBorel hE hF hLie hGC hGT hGM hGB hAction hσE hσF

variable (s : homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
  (hi : IsEllipticGlobalSymbol E F s.val)
  (hs : ∀ (g : G) (x : M) (ξ : CotangentFiber (n := n) x), ξ ≠ 0 →
    equivariantGlobalSymbolLinearMap IG σE σF g s.val x ξ = s.val x ξ)

include hi hs


set_option linter.unusedVariables false in
/-- All actual realizations of the original symbol have one full equivariant index value. -/
theorem existsUnique_equivariantHomogeneousAnalyticIndex :
    ∃! z : RepresentationGrothendieckGroup G,
      ∀ (μ : Measure M) (hμ : IsSmoothPositiveMeasure (n := n) μ),
      letI := hμ
      ∀ (h : SmoothHermitianMetric (n := n) (r := r) E)
        (k : SmoothHermitianMetric (n := n) (r := q) F)
        (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
          ∀ (g : G) (x : M) (u v : E x),
            h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
        (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
          ∀ (g : G) (x : M) (u v : F x),
            k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
        (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
        (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
        (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
        (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
        (hprincipal : P.principalSymbol = globalPrincipalSymbolClass E F 0
          (R.regularizedSymbol 0 s.val s.property.1 s.property.2)),
        z = P.equivariantAnalyticIndex IG σE σF hσE hσF
          h k hInvariant kInvariant hμInvariant hPg hP := by
  classical
  -- First construct one actual realization, so the universal property is nonvacuous.
  obtain ⟨μ₀, hμ₀, hμ₀Invariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ₀
  obtain ⟨h₀, hh₀⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k₀, hk₀⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨R₀⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  let p₀ := R₀.regularizedSymbol 0 s.val s.property.1 s.property.2
  have hfixed (g : G) :
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g
        (globalPrincipalSymbolClass E F 0 p₀) = globalPrincipalSymbolClass E F 0 p₀ :=
    (R₀.equivariant_regularizedSymbol_class_eq_iff IG σE σF hσE hσF R₀ 0 s s g).mpr
      (hs g)
  obtain ⟨P₀, hP₀g, hP₀class⟩ :=
    PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := μ₀)
      IG σE σF hσE hσF 0 (globalPrincipalSymbolClass E F 0 p₀) hfixed
  have hP₀ : P₀.IsElliptic := ⟨p₀, hP₀class,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R₀ 0 s.val
      s.property.1 s.property.2).mpr hi⟩
  refine ⟨P₀.equivariantAnalyticIndex IG σE σF hσE hσF
    h₀ k₀ hh₀ hk₀ hμ₀Invariant hP₀g hP₀, ?_, ?_⟩
  · intro μ hμ
    let := hμ
    intro h k hInvariant kInvariant hμInvariant R P hPg hP hprincipal
    -- Transport the very same smooth operator to the specified invariant measure.
    have htransport := P₀.equivariantAnalyticIndex_changeMeasure
      (ν := μ) (IG := IG) (σE := σE) (σF := σF) (hσE := hσE) (hσF := hσF)
      (h := h₀) (k := k₀) (hInvariant := hh₀) (kInvariant := hk₀)
      (hμInvariant := hμ₀Invariant) (hνInvariant := hμInvariant) hP₀g hP₀
    have hnewEll := (P₀.isElliptic_changeMeasure_iff μ).mpr hP₀
    have hmetric := (P₀.changeMeasure μ).equivariantAnalyticIndex_metric_independent
      IG σE σF hσE hσF h₀ k₀ hh₀ hk₀ hμInvariant hP₀g hnewEll
      h k hInvariant kInvariant
    -- Independent regularizations represent the identical off-zero homogeneous symbol.
    have hregularization : globalPrincipalSymbolClass E F 0 p₀ =
        globalPrincipalSymbolClass E F 0
          (R.regularizedSymbol 0 s.val s.property.1 s.property.2) :=
      (R₀.regularizedSymbol_class_eq_iff R 0 s.val s.val
        s.property.1 s.property.2 s.property.1 s.property.2).mpr (fun _ _ _ ↦ rfl)
    have hclasses : (P₀.changeMeasure μ).principalSymbol = P.principalSymbol :=
      (P₀.principalSymbol_changeMeasure μ).trans
        (hP₀class.trans (hregularization.trans hprincipal.symm))
    have hoperator := (P₀.changeMeasure μ).equivariantAnalyticIndex_eq_of_principalSymbol_eq
      IG σE σF hσE hσF h k hInvariant kInvariant hμInvariant hP₀g hnewEll
      P hPg hP hclasses
    exact htransport.symm.trans (hmetric.trans hoperator)
  · intro z hz
    -- Any value with the universal property agrees at the concrete initial realization.
    exact hz μ₀ hμ₀ h₀ k₀ hh₀ hk₀ hμ₀Invariant R₀ P₀ hP₀g hP₀ hP₀class

/-- The full equivariant analytic index characterized by all realizations of this symbol. -/
def equivariantHomogeneousAnalyticIndex : RepresentationGrothendieckGroup G :=
  (existsUnique_equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs).exists.choose


set_option linter.unusedVariables false in
/-- The canonical symbol index equals the full index of any specified actual realization. -/
theorem equivariantHomogeneousAnalyticIndex_eq :
    ∀ (μ : Measure M) (hμ : IsSmoothPositiveMeasure (n := n) μ),
      letI := hμ
      ∀ (h : SmoothHermitianMetric (n := n) (r := r) E)
        (k : SmoothHermitianMetric (n := n) (r := q) F)
        (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
          ∀ (g : G) (x : M) (u v : E x),
            h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
        (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
          ∀ (g : G) (x : M) (u v : F x),
            k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
        (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
        (R : QuantizationPresentation (n := n) (r := r) (q := q) E F)
        (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
        (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic)
        (hprincipal : P.principalSymbol = globalPrincipalSymbolClass E F 0
          (R.regularizedSymbol 0 s.val s.property.1 s.property.2)),
        equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF s hi hs =
          P.equivariantAnalyticIndex IG σE σF hσE hσF
          h k hInvariant kInvariant hμInvariant hPg hP := by
  -- The defining witness is evaluated with every supplied choice left unchanged.
  intro μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hprincipal
  exact (existsUnique_equivariantHomogeneousAnalyticIndex
    IG σE σF hσE hσF s hi hs).exists.choose_spec
      μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hprincipal

omit hi hs

attribute [local instance] homogeneousSymbolTopology

/-- A continuous path in the original smooth homogeneous topology preserves the full index. -/
theorem equivariantHomogeneousAnalyticIndex_eq_of_homotopy
    (a : unitInterval → homogeneousGlobalSymbolSpace (n := n) (r := r) (q := q) E F 0)
    (ha : Continuous a) (he : ∀ t, IsEllipticGlobalSymbol E F (a t).val)
    (hag : ∀ (t : unitInterval) (g : G) (x : M) (ξ : CotangentFiber (n := n) x),
      ξ ≠ 0 → equivariantGlobalSymbolLinearMap IG σE σF g (a t).val x ξ = (a t).val x ξ) :
    equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF (a 0) (he 0) (hag 0) =
      equivariantHomogeneousAnalyticIndex IG σE σF hσE hσF (a 1) (he 1) (hag 1) := by
  classical
  -- Use one invariant geometry and one regularization for both actual endpoints.
  obtain ⟨μ, hμ, hμInvariant⟩ :=
    exists_invariant_smoothPositiveMeasure G IG (n := n) (M := M)
  let := hμ
  obtain ⟨h, hInvariant⟩ := exists_invariant_smoothHermitianMetric IG σE hσE
  obtain ⟨k, kInvariant⟩ := exists_invariant_smoothHermitianMetric IG σF hσF
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := r) (q := q) (E := E) (F := F)
  let p (t : unitInterval) :=
    R.regularizedSymbol 0 (a t).val (a t).property.1 (a t).property.2
  have hfixed (t : unitInterval) (g : G) :
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF 0 g
        (globalPrincipalSymbolClass E F 0 (p t)) =
          globalPrincipalSymbolClass E F 0 (p t) :=
    (R.equivariant_regularizedSymbol_class_eq_iff IG σE σF hσE hσF R 0
      (a t) (a t) g).mpr (hag t g)
  obtain ⟨P, hPg, hPclass⟩ :=
    PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := μ)
      IG σE σF hσE hσF 0 (globalPrincipalSymbolClass E F 0 (p 0)) (hfixed 0)
  obtain ⟨Q, hQg, hQclass⟩ :=
    PseudodifferentialOperator.exists_equivariant_principalSymbol (μ := μ)
      IG σE σF hσE hσF 0 (globalPrincipalSymbolClass E F 0 (p 1)) (hfixed 1)
  have hP : P.IsElliptic := ⟨p 0, hPclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 (a 0).val
      (a 0).property.1 (a 0).property.2).mpr (he 0)⟩
  have hQ : Q.IsElliptic := ⟨p 1, hQclass,
    (isEllipticFullGlobalSymbol_regularizedSymbol_iff R 0 (a 1).val
      (a 1).property.1 (a 1).property.2).mpr (he 1)⟩
  -- Evaluate the canonical values at these same endpoints before using the supplied path.
  rw [equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF
    (a 0) (he 0) (hag 0) μ hμ h k hInvariant kInvariant hμInvariant R P hPg hP hPclass,
    equivariantHomogeneousAnalyticIndex_eq IG σE σF hσE hσF
    (a 1) (he 1) (hag 1) μ hμ h k hInvariant kInvariant hμInvariant R Q hQg hQ hQclass]
  apply P.equivariantAnalyticIndex_eq_of_continuous_homogeneous_principalSymbol
    IG σE σF hσE hσF h k hInvariant kInvariant hμInvariant
    Q hPg hP hQg hQ R a ha he hag hPclass hQclass

end AtiyahSinger
