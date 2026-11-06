/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantClosedMetricL2Index

/-!
# The original closed kernel and adjoint kernel as finite representations

Public module ID: M0486.

The actual smooth inclusions give finite coordinates on both original closed
kernels. The adjoint kernel includes into the original smooth quotient, so
its representation is the cokernel representation of the same operator.
This is the factor input for the full equivariant graded tensor index.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [LieGroup IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (σE : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    EquivariantStructure G E.Fiber)
  (σF : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure G F.Fiber)
  (hσE : σE.IsSmooth (n := n) (r := E.rank) IG)
  (hσF : σF.IsSmooth (n := n) (r := F.rank) IG)
  (h : SmoothHermitianMetric (n := n) (r := E.rank) E.Fiber)
  (k : SmoothHermitianMetric (n := n) (r := F.rank) F.Fiber)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    ∀ (g : G) (x : M) (u v : E.Fiber x),
      h.pairing (g • x) (σE.linearMap g x u) (σE.linearMap g x v) = h.pairing x u v)
  (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∀ (g : G) (x : M) (u v : F.Fiber x),
      k.pairing (g • x) (σF.linearMap g x u) (σF.linearMap g x v) = k.pairing x u v)
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)
  (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank)
    E.Fiber F.Fiber μ 1)
  (hPg : P.IsEquivariant IG σE σF hσE hσF)


include hPg

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Elaborate both original metric closures and their smooth finite-coordinate comparisons.
/-- Both actual closed kernels carry finite coordinates computing the full original index. -/
theorem PseudodifferentialOperator.exists_metricL2ClosedKernelRepresentations
    (hP : P.IsElliptic) :
    let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
    let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
    let L := P.metricL2ClosedRealization h k
    ∃ κ χ : FiniteContinuousRepresentation G,
      ∃ e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] L.ker,
        ∃ f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] L.adjoint.ker,
          (∀ g v, (e (κ.representation g v)).val = ρ g (e v).val) ∧
          (∀ g v, (f (χ.representation g v)).val = τ g (f v).val) ∧
          P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
            finiteRepresentationClass κ - finiteRepresentationClass χ := by
  classical
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let L := P.metricL2ClosedRealization h k
  let P' := P.metricFormalAdjoint h k
  have hP' : P'.IsElliptic := (P.isElliptic_metricFormalAdjoint_iff h k).mpr hP
  have hP'g := P.isEquivariant_metricFormalAdjoint IG σE σF hσE hσF h k
    hInvariant kInvariant hμInvariant hPg
  -- Select coordinates on the original smooth kernel and original smooth adjoint kernel.
  obtain ⟨κ, κc, a, ac, ha, hac⟩ :=
    P.exists_smoothKernelCokernelRepresentations IG σE σF hσE hσF hPg hP
  obtain ⟨χ, χc, b, bc, hb, hbc⟩ :=
    P'.exists_smoothKernelCokernelRepresentations IG σF σE hσF hσE hP'g hP'
  obtain ⟨j, q, hj, hq⟩ := P.exists_metricL2ClosedRealization_kernel_cokernel_equiv h k hP
  obtain ⟨j', q', hj', hq'⟩ :=
    P'.exists_metricL2ClosedRealization_kernel_cokernel_equiv k h hP'
  have hAdj : (P'.metricL2ClosedRealization k h).ker = L.adjoint.ker :=
    congrArg LinearPMap.ker (P.metricL2ClosedRealization_metricFormalAdjoint h k hP)
  let e := a.trans j
  let f := (b.trans j').trans (LinearEquiv.ofEq _ _ hAdj)
  refine ⟨κ, χ, e, f, ?_, ?_, ?_⟩
  · -- The natural smooth inclusion intertwines precisely the given integral action.
    intro g v
    change (j (a (κ.representation g v))).val = ρ g (j (a v)).val
    rw [hj, hj, ha]
    exact (h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant g _).symm
  · intro g v
    change (j' (b (χ.representation g v))).val = τ g (j' (b v)).val
    rw [hj', hj', hb]
    exact (k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant g _).symm
  · -- Adjoint zero modes represent the actual range quotient via their own section classes.
    obtain ⟨A⟩ := nonempty_smoothBundlePresentation (n := n) (r := E.rank) (E := E.Fiber)
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation (n := n) (r := F.rank) (E := F.Fiber)
    obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
    let c := P.kerMetricFormalAdjointEquivCoker h k A B Q hQ
    let d := b.trans c
    let RE := σE.smoothSectionRepresentation IG hσE
    let RF := σF.smoothSectionRepresentation IG hσF
    have hrange (g : G) : P.toLinearMap.range ≤ P.toLinearMap.range.comap (RF g) := by
      rintro _ ⟨u, rfl⟩
      exact ⟨RE g u, congrArg (fun T ↦ T u) (hPg g)⟩
    let RC := RF.quotient P.toLinearMap.range hrange
    have hd (g : G) (v : Fin χ.dimension → ℂ) :
        d (χ.representation g v) = RC g (d v) := by
      change P.toLinearMap.range.mkQ (b (χ.representation g v)).val =
        P.toLinearMap.range.mkQ (RF g (b v).val)
      rw [hb]
    apply P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP κ χ a d ha
    intro g v
    rw [hd, d.apply_symm_apply]
    rfl

end AtiyahSinger
