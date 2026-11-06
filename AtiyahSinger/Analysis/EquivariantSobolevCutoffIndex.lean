/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantAverageStability
public import AtiyahSinger.Analysis.EquivariantDomainAverage
public import AtiyahSinger.Analysis.EquivariantDomainIndex
public import AtiyahSinger.Analysis.SobolevInclusionTransport

/-!
# The original smooth index of a sufficiently close averaged cutoff

Public module ID: M0582.

A fixed invariant Hilbert realization equivalent to the original native H1
domain supplies the norm for cutoff comparison. The actual averaged PDO then
has the same full smooth index as the fixed equivariant Fredholm operator,
provided its original H1 realization is sufficiently close and its average
is elliptic. No invariance of the atlas Sobolev norm is assumed.
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
  [hG : LieGroup IG ∞ G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    EquivariantStructure G F)
  (hσE : σE.IsSmooth (n := n) (r := r) IG)
  (hσF : σF.IsSmooth (n := n) (r := q) IG)

include hM hT2 hSC hC hBorel hE hF hμ hG hAction

variable (h : SmoothHermitianMetric (n := n) (r := r) E)
  (k : SmoothHermitianMetric (n := n) (r := q) F)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∀ (g : G) (x : M) (u v : F x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hInvariant

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Normalize the same H1 realization, graph and integral average before comparing full indices.
/-- A close elliptic averaged cutoff has the full index of the fixed invariant H1 realization. -/
theorem exists_radius_smoothEquivariantAnalyticIndex_average_eq
    (A : SmoothBundlePresentation (n := n) (r := r) E)
    (B : SmoothBundlePresentation (n := n) (r := q) F)
    {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    (γ : ContRepresentation ℂ G X)
    (hγ : Continuous (fun p : G × X ↦ γ p.1 p.2))
    (R : G →* (X ≃ₗᵢ[ℂ] X)) (hR : ∀ g x, R g x = γ g x)
    (Φ : X ≃L[ℂ] A.SobolevSpace 1)
    (hjg : ∀ g u, γ g (Φ.symm (A.smoothToSobolev 1 u)) =
      Φ.symm (A.smoothToSobolev 1 (σE.smoothSectionRepresentation IG hσE g u)))
    (J : X →L[ℂ] h.L2SectionSpace μ) (hJ : Function.Injective J)
    (hJsmooth : ∀ u, J (Φ.symm (A.smoothToSobolev 1 u)) = h.smoothToL2 μ u)
    (T₀ : X →L[ℂ] k.L2SectionSpace μ)
    (hT₀g : ∀ g, T₀.comp (γ g) =
      (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant g).comp T₀)
    (hT₀ : T₀.IsFredholm) :
    let T (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1) :=
      ((k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
        (P.sobolevRealization A B 1 0 (by norm_num))).comp Φ.toContinuousLinearMap
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
        (hP : (P.average IG σE σF hσE hσF).IsElliptic), ‖T P - T₀‖ < ε →
        (P.average IG σE σF hσE hσF).smoothEquivariantAnalyticIndex
          IG σE σF hσE hσF (P.isEquivariant_average IG σE σF hσE hσF) hP =
            equivariantFredholmIndex γ
              (k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant) hγ
              (k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant)
              T₀ hT₀g hT₀ := by
  classical
  let ν := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure ν := ⟨Measure.haarMeasure_self⟩
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let S := k.l2IsometryRepresentation μ IG σF hσF kInvariant hμInvariant
  let hτ := k.continuous_l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let hRc := hγ.congr (fun p ↦ (hR p.1 p.2).symm)
  let W := unitaryOperatorAverage ν R S hRc hτ
  let T (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1) :=
    ((k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
      (P.sobolevRealization A B 1 0 (by norm_num))).comp Φ.toContinuousLinearMap
  let j := Φ.symm.toLinearEquiv.toLinearMap.comp (A.smoothToSobolev 1)
  have hj : DenseRange j :=
    Φ.symm.surjective.denseRange.comp (A.denseRange_smoothToSobolev 1) Φ.symm.continuous
  have hTsmooth (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 1)
      (u : smoothSections (n := n) (r := r) E) :
      T P (j u) = k.smoothToL2 μ (P.toLinearMap u) := by
    change k.sobolevZeroEquivL2 B
      (P.sobolevRealization A B 1 0 (by norm_num)
        (Φ (Φ.symm (A.smoothToSobolev 1 u)))) = _
    rw [Φ.apply_symm_apply, P.sobolevRealization_smoothToSobolev,
      k.sobolevZeroEquivL2_smooth]
  have hJg (g : G) (x : X) : J (γ g x) =
      h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g (J x) := by
    apply congrFun (hj.equalizer (J.continuous.comp (γ g).continuous)
      ((h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g).continuous.comp
        J.continuous) ?_) x
    funext u
    change J (γ g (Φ.symm (A.smoothToSobolev 1 u))) = _
    rw [hjg, hJsmooth]
    change _ = h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant g
      (J (Φ.symm (A.smoothToSobolev 1 u)))
    rw [hJsmooth]
    exact (h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE
      hInvariant hμInvariant g u).symm
  -- The fixed graph norm gives one stability radius before choosing the actual cutoff PDO.
  obtain ⟨ε, hε, hstable⟩ := exists_radius_equivariantFredholmIndex_average_eq
    ν γ τ hγ hτ R S hR (fun _ _ ↦ rfl) T₀ hT₀g hT₀
  refine ⟨ε, hε, ?_⟩
  intro P hP hclose
  let Pavg := P.average IG σE σF hσE hσF
  have havg : T Pavg = W (T P) := by
    apply P.boundedRealization_average IG σE σF hσE hσF k kInvariant hμInvariant
      R hRc j hj
    · intro g u
      change R g (Φ.symm (A.smoothToSobolev 1 u)) = _
      rw [hR, hjg]
      rfl
    · exact hTsmooth P
    · exact hTsmooth Pavg
  obtain ⟨hWg, hW, hWindex⟩ := hstable (T P) hclose
  have hTg : ∀ g, (T Pavg).comp (γ g) = (τ g).comp (T Pavg) := by
    simpa only [havg] using hWg
  have hT : (T Pavg).IsFredholm := havg ▸ hW
  have hindex : equivariantFredholmIndex γ τ hγ hτ (T Pavg) hTg hT =
      equivariantFredholmIndex γ τ hγ hτ T₀ hT₀g hT₀ := by
    simpa only [havg] using hWindex
  -- Ellipticity identifies the same native H1 realization with the full original closed graph.
  let J₀ := (h.sobolevZeroEquivL2 (μ := μ) A).toContinuousLinearMap.comp
    (A.sobolevInclusion 1 0 (by norm_num))
  let R₀ := (k.sobolevZeroEquivL2 (μ := μ) B).toContinuousLinearMap.comp
    (Pavg.sobolevRealization A B 1 0 (by norm_num))
  have hJtransport : J = J₀.comp Φ.toContinuousLinearMap := by
    apply DFunLike.coe_injective
    apply hj.equalizer J.continuous (J₀.comp Φ.toContinuousLinearMap).continuous
    funext u
    change J (Φ.symm (A.smoothToSobolev 1 u)) =
      J₀ (Φ (Φ.symm (A.smoothToSobolev 1 u)))
    rw [hJsmooth, Φ.apply_symm_apply]
    change h.smoothToL2 μ u =
      h.sobolevZeroEquivL2 A (A.sobolevInclusion 1 0 (by norm_num) (A.smoothToSobolev 1 u))
    rw [A.sobolevInclusion_smoothToSobolev, h.sobolevZeroEquivL2_smooth]
  have hgraph : (Pavg.metricL2ClosedRealization h k).graph =
      (J.prod (T Pavg)).toLinearMap.range := by
    have hg := Pavg.metricL2ClosedRealization_graph_sobolev h k hP A B
    have hcast : Pavg.sobolevRealization A B 1 0 (by norm_num) =
        Eq.mp (congrArg (fun s : ℝ ↦ A.SobolevSpace 1 →L[ℂ] B.SobolevSpace s)
          (sub_self (1 : ℝ))) (Pavg.sobolevExtension A B 1) :=
      B.sobolevInclusion_comp_eq_cast (1 - 1) 0 (sub_self 1) (Pavg.sobolevExtension A B 1)
    dsimp only at hg
    rw [← hcast] at hg
    change (Pavg.metricL2ClosedRealization h k).graph = (J₀.prod R₀).toLinearMap.range at hg
    rw [hg, hJtransport]
    ext z
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨Φ.symm v, ?_⟩
      change (J₀ (Φ (Φ.symm v)), R₀ (Φ (Φ.symm v))) = z
      rw [Φ.apply_symm_apply]
      exact hv
    · rintro ⟨v, hv⟩
      exact ⟨Φ v, hv⟩
  -- The original smooth kernel and quotient now compute this same bounded index.
  exact (Pavg.smoothEquivariantAnalyticIndex_eq_of_graph_realization
    IG σE σF hσE hσF h k hInvariant kInvariant hμInvariant
    (P.isEquivariant_average IG σE σF hσE hσF) hP γ hγ J hJ hJg
    (T Pavg) hgraph hTg hT).trans hindex

end AtiyahSinger.PseudodifferentialOperator
