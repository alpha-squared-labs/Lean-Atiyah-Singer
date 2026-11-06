/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantL2
public import AtiyahSinger.Analysis.HermitianMetricL2Realization

/-!
# Equivariant PDOs on the original smooth sections and integral completions

Public module ID: M0557.

SG III.9.1 defines equivariance for differential operators by
`P(g * u) = g * P(u)` on actual smooth sections. Here the identical standard
condition is extended to the existing PDOs, using the original geometric
representations on the two supplied bundles. It does not choose a new action or assume an
equivariant symbol, ellipticity, a metric, or boundedness of the operator.
The compact-base and positive-density assumptions already belong to the
existing global PDO type and are retained here.

For order zero, equivariance is equivalent to intertwining by the existing
`metricL2Extension` on the same two explicit-metric completions. Both metrics
and the one measure must be invariant. Density proves extension, and the
injective smooth inclusion proves the converse. This precise equivalence is
a supplementary dense-domain argument for the Hilbert-space discussion on
SG III.9, pp.211--212, not a separately numbered theorem there.

The actual metric formal adjoint is equivariant at every real PDO order.
Its proof uses the integral adjunction identity on smooth sections, without
claiming that a positive-order operator is bounded on L². No group compactness
or Lie-group hypothesis is added once invariant metrics and density are given.
The smooth formal-adjoint equivariance and the order-zero L² intertwining
equivalence are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.PseudodifferentialOperator

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

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
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

/-- SG Definition 9.1's equivariance condition, extended to the original PDO section map. -/
def IsEquivariant {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) : Prop :=
  ∀ g : G, P.toLinearMap.comp (σE.smoothSectionRepresentation IG hσE g) =
    (σF.smoothSectionRepresentation IG hσF g).comp P.toLinearMap

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction hInvariant kInvariant hμInvariant

/-- Smooth equivariance is exactly intertwining by the existing order-zero integral realization. -/
theorem isEquivariant_iff_metricL2Extension_intertwines
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0) :
    P.IsEquivariant IG σE σF hσE hσF ↔
      ∀ g : G, (P.metricL2Extension h k).comp
          (h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g) =
        (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant g).comp
          (P.metricL2Extension h k) := by
  /- Stage 1: fix g and a smooth input u. The original dense-domain action
  formulas for l2IsometryRepresentation and metricL2Extension identify the
  two completed compositions with the smoothToL2 images of P(g*u) and g*(Pu).
  The hypothesis IsEquivariant equates these actual sections. Since both
  compositions are continuous and h.smoothToL2 μ has dense range, they agree
  on the entire existing completion. Only the order-zero PDO realization is
  used; no new norm or arbitrary Sobolev isometry is supplied.
  Stage 2: conversely apply completed intertwining to h.smoothToL2 μ u.
  The same two action formulas give equality after k.smoothToL2 μ. Its
  injectivity identifies the original smooth outputs. Extensionality in u
  yields the required equality of complex-linear smooth-section maps for g.
  Both directions retain exactly h, k, μ, σE and σF; ellipticity is unused. -/
  let RE := σE.smoothSectionRepresentation IG hσE
  let RF := σF.smoothSectionRepresentation IG hσF
  let TE := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let TF := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  have hE (g : G) (u : smoothSections (n := n) (r := r) E) :
      TE g (h.smoothToL2 μ u) = h.smoothToL2 μ (RE g u) :=
    h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant g u
  have hF (g : G) (u : smoothSections (n := n) (r := q) F) :
      TF g (k.smoothToL2 μ u) = k.smoothToL2 μ (RF g u) :=
    k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant g u
  constructor
  · intro hP g
    -- Extend the given equality from the same dense smooth image.
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer
      ((P.metricL2Extension h k).comp (TE g)).continuous
      ((TF g).comp (P.metricL2Extension h k)).continuous
    funext u
    change P.metricL2Extension h k (TE g (h.smoothToL2 μ u)) =
      TF g (P.metricL2Extension h k (h.smoothToL2 μ u))
    rw [hE, P.metricL2Extension_smooth, P.metricL2Extension_smooth, hF]
    exact congrArg (k.smoothToL2 μ) (congrArg (fun T ↦ T u) (hP g))
  · intro hP g
    apply LinearMap.ext
    intro u
    -- Injectivity of the original target inclusion recovers smooth equivariance.
    apply k.smoothToL2_injective μ
    have heq := congrArg (fun T ↦ T (h.smoothToL2 μ u)) (hP g)
    change P.metricL2Extension h k (TE g (h.smoothToL2 μ u)) =
      TF g (P.metricL2Extension h k (h.smoothToL2 μ u)) at heq
    rwa [hE, P.metricL2Extension_smooth, P.metricL2Extension_smooth, hF] at heq

/-- With the same invariant metrics and density, the actual formal adjoint is equivariant. -/
theorem isEquivariant_metricFormalAdjoint {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (hP : P.IsEquivariant IG σE σF hσE hσF) :
    (P.metricFormalAdjoint h k).IsEquivariant IG σF σE hσF hσE := by
  /- Stage 1: invariant metrics and density give the completed isometry actions.
  Their dense-domain action identities preserve each original smooth-section
  integral pairing, using the same μ.
  Stage 2: test P†(g*v) against an arbitrary smooth u. Apply the original
  formal-adjoint identity, move g across the output pairing as g inverse,
  use P(g inverse*u)=g inverse*(Pu), and apply the adjunction identity again.
  Move g back across the input pairing to obtain the pairing with g*(P†v).
  Stage 3: nondegeneracy of the same positive smooth integral pairing makes
  P†(g*v)=g*(P†v); extensionality gives the displayed equivariance. This
  argument concerns smooth sections at every real order m. It requires no
  bounded L² realization of P and no ellipticity or Fredholm hypothesis. -/
  let RE := σE.smoothSectionRepresentation IG hσE
  let RF := σF.smoothSectionRepresentation IG hσF
  let Q := (P.metricFormalAdjoint h k).toLinearMap
  -- The original completed isometries preserve the same smooth integral pairings.
  have hpairE (g : G) (u v : smoothSections (n := n) (r := r) E) :
      h.sectionPairing μ (RE g u) (RE g v) = h.sectionPairing μ u v := by
    rw [← h.inner_smoothToL2, ← h.inner_smoothToL2,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant,
      ← h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant]
    exact (h.l2IsometryRepresentation μ IG σE hσE hInvariant hμInvariant g).inner_map_map _ _
  have hpairF (g : G) (u v : smoothSections (n := n) (r := q) F) :
      k.sectionPairing μ (RF g u) (RF g v) = k.sectionPairing μ u v := by
    rw [← k.inner_smoothToL2, ← k.inner_smoothToL2,
      ← k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant,
      ← k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant]
    exact (k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant g).inner_map_map _ _
  intro g
  have hcancel (u : smoothSections (n := n) (r := r) E) : RE g (RE g⁻¹ u) = u := by
    change (RE g * RE g⁻¹) u = u
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hcomm (u : smoothSections (n := n) (r := r) E) :
      P.toLinearMap (RE g u) = RF g (P.toLinearMap u) :=
    congrArg (fun T ↦ T u) (hP g)
  apply LinearMap.ext
  intro v
  -- Move the same group element across adjunction, retaining both specified actions.
  have htest (u : smoothSections (n := n) (r := r) E) :
      h.sectionPairing μ u (Q (RF g v)) = h.sectionPairing μ u (RE g (Q v)) := by
    calc
      h.sectionPairing μ u (Q (RF g v)) =
          k.sectionPairing μ (P.toLinearMap u) (RF g v) :=
        (P.isMetricFormalAdjoint_metricFormalAdjoint h k u (RF g v)).symm
      _ = k.sectionPairing μ (RF g (P.toLinearMap (RE g⁻¹ u))) (RF g v) := by
        rw [← hcomm, hcancel]
      _ = k.sectionPairing μ (P.toLinearMap (RE g⁻¹ u)) v := hpairF g _ _
      _ = h.sectionPairing μ (RE g⁻¹ u) (Q v) :=
        P.isMetricFormalAdjoint_metricFormalAdjoint h k (RE g⁻¹ u) v
      _ = h.sectionPairing μ (RE g (RE g⁻¹ u)) (RE g (Q v)) :=
        (hpairE g _ _).symm
      _ = h.sectionPairing μ u (RE g (Q v)) := by rw [hcancel]
  -- Positive definiteness on smooth sections separates the two actual outputs.
  let core : InnerProductSpace.Core ℂ (smoothSections (n := n) (r := r) E) :=
    h.smoothL2SectionCore μ
  have hzero : h.sectionPairing μ (Q (RF g v) - RE g (Q v))
      (Q (RF g v) - RE g (Q v)) = 0 := by
    change core.inner (Q (RF g v) - RE g (Q v)) (Q (RF g v) - RE g (Q v)) = 0
    rw [InnerProductSpace.Core.inner_sub_right]
    exact sub_eq_zero.mpr (htest _)
  exact sub_eq_zero.mp ((h.sectionPairing_self_eq_zero_iff μ _).mp hzero)


end AtiyahSinger.PseudodifferentialOperator
