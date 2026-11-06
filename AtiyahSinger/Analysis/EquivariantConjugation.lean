/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol
public import AtiyahSinger.Analysis.EquivariantSectionSupport
public import AtiyahSinger.Analysis.SectionOperatorSupport

/-!
# Geometric conjugation of the original pseudodifferential operators

Public module ID: M0490.

The operator is exactly `ρF(g) ∘ P ∘ ρE(g⁻¹)` on the original smooth sections,
using the same two supplied equivariant bundle structures. SG III.3.13--3.14,
printed p.186, and III.3.19, p.188, supply coordinate covariance and the principal
class. The group-action formulation is the standard supplement used with SG
III.9, pp.211--214. It retains the original real order and the same density.

The transformed smoothing kernel includes the smooth density ratio and the
absolute inverse Jacobian; the measure is not assumed invariant. The principal
symbol is transported by the existing inverse-cotangent action on the original
quotient. Two-sided operator support is transported by the same base action,
in the sense of SG III.3, p.183, including its input germ condition.
No compactness of the group, invariant metric, quantization, or new action is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)

/-- Geometric conjugation preserves the original PDO order and the same smooth density. -/
theorem isPseudodifferentialOperator_conjugate (g : G) :
    IsPseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m
      ((σF.smoothSectionRepresentation IG hσF g).comp
        (P.toLinearMap.comp (σE.smoothSectionRepresentation IG hσE g⁻¹))) := by
  /- Stage 1: start with the finite local pieces and smooth-kernel remainder
  supplied by P. Conjugate each actual piece by the same two section actions.
  The base map x ↦ g*x is a diffeomorphism in the original atlas; transform
  its input and output cutoffs and frames together. Refine into finitely many
  original valid chart/frame regions, using compactness of the original cutoff
  supports. The local coordinate covariance theorem and smooth frame changes
  retain the same S^m order and give admissible original PDO pieces.
  Stage 2: the off-diagonal errors of the refinement are smooth kernels.
  The original smoothing remainder transforms to a smooth kernel on the same
  original bundle fibers. At its input variable the change of variables gives
  the ratio of the pushed-forward positive smooth density to μ, including
  the absolute inverse Jacobian. Multiplication by this smooth factor retains
  smoothness. Therefore every remainder is represented relative to the same μ.
  Stage 3: sum the finitely many transformed local terms and their smooth
  remainders. Their section map is exactly the displayed composition; no
  equality modulo smoothing is substituted for the actual operator action.
  Nothing in this fixed-element argument requires compact G or invariant μ. -/
  obtain ⟨N, Q, hQ, _⟩ := P.exists_representation_conjugate IG σE σF hσE hσF g
  exact ⟨N, Q, hQ⟩

/-- The original PDO conjugated by the two specified geometric smooth-section actions. -/
def conjugate (g : G) : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m where
  toLinearMap := (σF.smoothSectionRepresentation IG hσF g).comp
    (P.toLinearMap.comp (σE.smoothSectionRepresentation IG hσE g⁻¹))
  isPseudodifferentialOperator :=
    P.isPseudodifferentialOperator_conjugate IG σE σF hσE hσF g

/-- Conjugation transports the principal class by the original inverse-cotangent action. -/
theorem principalSymbol_conjugate (g : G) :
    (P.conjugate IG σE σF hσE hσF g).principalSymbol =
      equivariantPrincipalSymbolRepresentation IG σE σF hσE hσF m g P.principalSymbol := by
  /- Stage 1: use the finite representation from the conjugation construction.
  Coordinate covariance gives its leading symbol at (x,ξ) as the original
  symbol at (g⁻¹*x, ξ∘d(g)_(g⁻¹*x)), with σE(g⁻¹,x) on the input and
  σF(g,g⁻¹*x) on the output. The only output-index transport is the actual
  equality g*(g⁻¹*x)=x. This is equivariantGlobalSymbolLinearMap, whose
  finite-dimensional fiber continuity has already been established.
  Stage 2: derivatives of coordinates and frame matrices beyond the leading
  term contribute order m-1. The transformed smooth kernel, including its
  density ratio relative to the same μ, has zero principal class. Thus the
  finite symbol sum has the class obtained by the existing quotient action.
  Stage 3: apply principalSymbol_eq_of_representation on each side and the
  canonical quotient-action compatibility. The result concerns the original
  S^m/S^(m-1) class, not pointwise equality of full symbol representatives.
  Neither P nor its original principal symbol is assumed equivariant. -/
  obtain ⟨N, Q, hQ, hclass⟩ := P.exists_representation_conjugate IG σE σF hσE hσF g
  exact ((P.conjugate IG σE σF hσE hσF g).principalSymbol_eq_of_representation N Q hQ).trans
    hclass

/-- Geometric conjugation transports both sides of the original operator support. -/
theorem hasSectionOperatorSupport_conjugate (g : G) (K : Set M)
    (hP : HasSectionOperatorSupport K P.toLinearMap) :
    HasSectionOperatorSupport ((fun x : M ↦ g • x) '' K)
      (P.conjugate IG σE σF hσE hσF g).toLinearMap := by
  /- Stage 1: the original fiber actions are linear bijections, so a transformed
  section is nonzero exactly at the g-image of its original nonzero set.
  The original base action is a homeomorphism and therefore carries its closure
  to that same image of the closure. Apply the output-support half of hP to
  the input section acted on by g inverse, obtaining output support in g*K.
  Stage 2: if the closed support of u is disjoint from g*K, the same exact
  support transformation shows that the closed support of g inverse*u is
  disjoint from K. The input half of hP makes P(g inverse*u)=0; linearity
  then makes g*P(g inverse*u)=0. This retains the original closed-support
  input condition and does not replace it by pointwise vanishing on K.
  No closedness or compactness of K, or invariance of K, is required. -/
  constructor
  · intro u
    change closure {x | σF.sectionLinearMap g
      (P.toLinearMap (σE.smoothSectionRepresentation IG hσE g⁻¹ u)).val x ≠ 0} ⊆ _
    rw [σF.closure_support_sectionLinearMap]
    exact Set.image_mono (hP.1 _)
  · intro u hu
    have hpre : Disjoint (closure {x |
        (σE.smoothSectionRepresentation IG hσE g⁻¹ u).val x ≠ 0}) K := by
      change Disjoint (closure {x | σE.sectionLinearMap g⁻¹ u.val x ≠ 0}) K
      rw [σE.closure_support_sectionLinearMap]
      apply Set.disjoint_left.mpr
      intro x hx hxK
      obtain ⟨y, hy, hxy⟩ := hx
      have hyK : y ∈ (fun z : M ↦ g • z) '' K := by
        refine ⟨x, hxK, ?_⟩
        rw [← hxy]
        exact smul_inv_smul g y
      exact Set.disjoint_left.mp hu hy hyK
    change σF.smoothSectionRepresentation IG hσF g
      (P.toLinearMap (σE.smoothSectionRepresentation IG hσE g⁻¹ u)) = 0
    rw [hP.2 _ hpre, map_zero]

end AtiyahSinger.PseudodifferentialOperator
