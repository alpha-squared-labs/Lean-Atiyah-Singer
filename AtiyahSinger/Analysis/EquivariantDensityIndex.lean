/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricEquivariantIndex
public import AtiyahSinger.Analysis.PseudodifferentialDensity

/-!
# Equivariant integral completions and index under a change of density

Public module ID: M0499.

Two supplied invariant positive smooth densities give different integral norms
on the same original smooth sections. Their identity map extends uniquely to
an equivariant continuous linear equivalence of the explicit-metric completions.
This is the same-section comparison, with no square-root density multiplier and
no claim that the comparison is unitary. The actual `changeMeasure` PDO retains
its smooth-section map and therefore its full virtual representation index.

Sources: SG III.2 (2.17), III.5.2--5.3 and III.9, printed pp.211--214. The book's
geometric-to-Hilbert discussion identifies the smooth kernel and cokernel before
using invariant Hilbert completions. The exact comparison between two positive
densities is a project deduction from that construction, not a separately named
book theorem. It uses the existing H⁰ comparisons and equivariant coordinate
invariance. Group compactness is unnecessary once both invariant densities and
the invariant metrics are supplied. Both same-section comparison and full index
invariance are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [hBorel : BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (μ ν : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ]
  [hν : IsSmoothPositiveMeasure (n := n) ν]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
  (hνInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) ν = ν)

include hM hT2 hSC hC hBorel hE hμ hν hG hAction
  hInvariant hμInvariant hνInvariant

namespace SmoothHermitianMetric

/-- Identity on smooth sections has a unique equivariant extension across invariant densities. -/
theorem existsUnique_l2MeasureEquiv_intertwines :
    ∃! T : h.L2SectionSpace μ ≃L[ℂ] h.L2SectionSpace ν,
      (∀ u : smoothSections (n := n) (r := r) E,
        T (h.smoothToL2 μ u) = h.smoothToL2 ν u) ∧
      ∀ g : G, T.toContinuousLinearMap.comp
          (h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g) =
        (h.l2ContRepresentation ν IG σE hσE hInvariant hνInvariant g).comp
          T.toContinuousLinearMap := by
  /- Stage 1: choose one finite smooth presentation A. Compose the inverse
  of h.sobolevZeroEquivL2 at μ with that same comparison at ν. Both factors
  use the identical density-free H⁰ completion, so their composite sends
  each original μ-smooth vector to the ν-image of the same section. It is
  a continuous linear equivalence, not generally an isometry.
  Stage 2: for each g the two displayed composites agree on every original
  smooth vector, by the dense-domain formula for the two original completed
  representations. Their continuity and the dense μ-smooth range make them
  equal everywhere. The supplied μ and ν invariance are precisely the
  conditions used to define those original unitary actions.
  Stage 3: any other continuous linear equivalence with the same smooth
  action agrees on that dense range, hence on the entire μ-completion.
  Extensionality proves uniqueness. Thus the comparison does not retain
  an auxiliary presentation choice or insert a density multiplier. -/
  classical
  obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := r) E
  let eμ := h.sobolevZeroEquivL2 (μ := μ) A
  let eν := h.sobolevZeroEquivL2 (μ := ν) A
  let T : h.L2SectionSpace μ ≃L[ℂ] h.L2SectionSpace ν := eμ.symm.trans eν
  -- Both comparisons use the identical density-free H⁰ completion and the same section.
  have hT (u : smoothSections (n := n) (r := r) E) :
      T (h.smoothToL2 μ u) = h.smoothToL2 ν u := by
    change eν (eμ.symm (h.smoothToL2 μ u)) = _
    rw [← h.sobolevZeroEquivL2_smooth (μ := μ) A u]
    rw [show eμ.symm (eμ (A.smoothToSobolev 0 u)) = A.smoothToSobolev 0 u from
      eμ.symm_apply_apply _]
    exact h.sobolevZeroEquivL2_smooth (μ := ν) A u
  refine ⟨T, ⟨hT, ?_⟩, ?_⟩
  · intro g
    -- The completed actions agree on the dense original smooth image.
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      (T.continuous.comp
        (h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g).continuous)
      ((h.l2ContRepresentation ν IG σE hσE hInvariant hνInvariant g).continuous.comp
        T.continuous)
    funext u
    change T (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g
        (h.smoothToL2 μ u)) =
      h.l2IsometryRepresentation ν IG σE hσE hInvariant hνInvariant g
        (T (h.smoothToL2 μ u))
    rw [h.l2IsometryRepresentation_smoothToL2, hT, hT,
      h.l2IsometryRepresentation_smoothToL2]
  · intro S hS
    -- The smooth specification alone fixes the whole continuous equivalence.
    apply ContinuousLinearEquiv.ext
    apply (h.denseRange_smoothToL2 μ).equalizer S.continuous T.continuous
    funext u
    exact (hS.1 u).trans (hT u).symm

end SmoothHermitianMetric

variable {q : ℕ} {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)

include hF kInvariant

namespace PseudodifferentialOperator

variable {μ}

/-- Changing the auxiliary invariant density preserves the full original equivariant index. -/
theorem equivariantAnalyticIndex_changeMeasure
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0)
    (hPg : P.IsEquivariant IG σE σF hσE hσF) (hP : P.IsElliptic) :
    (P.changeMeasure ν).equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hνInvariant hPg
        ((P.isElliptic_changeMeasure_iff ν).mpr hP) =
      P.equivariantAnalyticIndex IG σE σF hσE hσF
        h k hInvariant kInvariant hμInvariant hPg hP := by
  /- Stage 1: changeMeasure retains exactly P.toLinearMap. Equivariance is
  therefore the same proposition with the same smooth-action witnesses;
  hPg supplies it without a new hypothesis. The established density
  transport theorem supplies ellipticity of that precise new-density PDO.
  Stage 2: apply existsUnique_l2MeasureEquiv_intertwines separately to the
  original E and F actions. Their same-section equivalences intertwine
  the two original L² representations. On a dense smooth input, both sides
  of the operator comparison square are the ν-image of P applied to that
  very section, by metricL2Extension_smooth and toLinearMap_changeMeasure.
  Extend this equality by continuity; no square-root conjugate is substituted.
  Stage 3: equivariantFredholmIndex_eq_of_equiv applied to this square
  identifies the actual finite kernel and quotient-cokernel representation
  classes. Unfold the two geometric indices and reverse that equality.
  The result is in R(G); equality of dimensions alone would not suffice.
  All metrics, bundle actions and lower-order terms stay fixed, and the
  only altered geometric input is the supplied invariant density. -/
  -- Use the exact same-section equivalences already specified for both invariant measures.
  obtain ⟨e, he, _⟩ := h.existsUnique_l2MeasureEquiv_intertwines μ ν IG σE hσE
    hInvariant hμInvariant hνInvariant
  obtain ⟨f, hf, _⟩ := k.existsUnique_l2MeasureEquiv_intertwines μ ν IG σF hσF
    kInvariant hμInvariant hνInvariant
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let ρ' := h.l2ContRepresentation ν IG σE hσE hInvariant hνInvariant
  let τ' := k.l2ContRepresentation ν IG σF hσF kInvariant hνInvariant
  let e' : ContRepresentation.Equiv ρ ρ' := ContRepresentation.Equiv.mk e he.2
  let f' : ContRepresentation.Equiv τ τ' := ContRepresentation.Equiv.mk f hf.2
  -- Density extends the square for the original smooth action to both integral completions.
  have hsquare : ((P.changeMeasure ν).metricL2Extension h k).comp e.toContinuousLinearMap =
      f.toContinuousLinearMap.comp (P.metricL2Extension h k) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      (((P.changeMeasure ν).metricL2Extension h k).comp e.toContinuousLinearMap).continuous
      (f.toContinuousLinearMap.comp (P.metricL2Extension h k)).continuous
    funext u
    change (P.changeMeasure ν).metricL2Extension h k (e (h.smoothToL2 μ u)) =
      f (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [he.1, (P.changeMeasure ν).metricL2Extension_smooth,
      P.metricL2Extension_smooth, hf.1, P.toLinearMap_changeMeasure ν]
  -- Intertwining equivalences preserve the full kernel and quotient-cokernel classes.
  unfold equivariantAnalyticIndex
  exact (equivariantFredholmIndex_eq_of_equiv ρ τ ρ' τ' _ _ _ _ e' f' _ _ _ _
    hsquare _ _).symm

end PseudodifferentialOperator

end AtiyahSinger
