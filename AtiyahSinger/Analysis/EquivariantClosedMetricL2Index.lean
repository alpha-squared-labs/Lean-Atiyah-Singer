/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedMetricL2KernelCokernel
public import AtiyahSinger.Analysis.EquivariantClosedMetricL2Realization
public import AtiyahSinger.Analysis.SmoothEquivariantIndex

/-!
# The full index in closed integral kernel and cokernel coordinates

Public module ID: M0487.

Finite coordinates on the actual closed integral kernel and actual range
quotient compute the original smooth representation-valued index whenever
they intertwine the specified geometric unitary actions. The natural smooth
inclusions identify both representations, not merely their dimensions.
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
set_option maxHeartbeats 800000 in
-- Transport the finite coordinates through the two actual smooth inclusions.
/-- Actual closed-kernel and quotient intertwiners compute the full original smooth index. -/
theorem PseudodifferentialOperator.smoothEquivariantAnalyticIndex_eq_of_closed_coordinates
    (hP : P.IsElliptic) :
    let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
    let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
    let L := P.metricL2ClosedRealization h k
    ∀ (κ χ : FiniteContinuousRepresentation G)
      (e : (Fin κ.dimension → ℂ) ≃ₗ[ℂ] L.ker)
      (f : (Fin χ.dimension → ℂ) ≃ₗ[ℂ] (k.L2SectionSpace μ ⧸ L.toFun.range))
      (_he : ∀ (g : G) (v : Fin κ.dimension → ℂ),
        (e (κ.representation g v)).val = ρ g (e v).val)
      (_hf : ∀ (g : G) (v : k.L2SectionSpace μ),
        f (χ.representation g (f.symm (L.toFun.range.mkQ v))) =
          L.toFun.range.mkQ (τ g v)),
      P.smoothEquivariantAnalyticIndex IG σE σF hσE hσF hPg hP =
        finiteRepresentationClass κ - finiteRepresentationClass χ := by
  classical
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let L := P.metricL2ClosedRealization h k
  dsimp only
  intro κ χ e f he hf
  obtain ⟨eS, fS, heS, hfS⟩ :=
    P.exists_metricL2ClosedRealization_kernel_cokernel_equiv h k hP
  let e' := e.trans eS.symm
  let f' := f.trans fS.symm
  -- Kernel coordinates represent precisely the same smooth section in integral L².
  have he' (g : G) (v : Fin κ.dimension → ℂ) :
      (e' (κ.representation g v)).val =
        σE.smoothSectionRepresentation IG hσE g (e' v).val := by
    apply h.smoothToL2_injective μ
    calc
      h.smoothToL2 μ (e' (κ.representation g v)).val =
          (e (κ.representation g v)).val := by
        change h.smoothToL2 μ (eS.symm (e (κ.representation g v))).val = _
        rw [← heS, eS.apply_symm_apply]
      _ = ρ g (e v).val := he g v
      _ = ρ g (h.smoothToL2 μ (e' v).val) := by
        change ρ g (e v).val = ρ g (h.smoothToL2 μ (eS.symm (e v)).val)
        rw [← heS, eS.apply_symm_apply]
      _ = h.smoothToL2 μ (σE.smoothSectionRepresentation IG hσE g (e' v).val) :=
        h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant g _
  -- The quotient comparison also uses the original representative, before and after the action.
  have hf' (g : G) (v : smoothSections (n := n) (r := F.rank) F.Fiber) :
      f' (χ.representation g (f'.symm (P.toLinearMap.range.mkQ v))) =
        P.toLinearMap.range.mkQ (σF.smoothSectionRepresentation IG hσF g v) := by
    apply fS.injective
    change fS (fS.symm (f (χ.representation g
      (f.symm (fS (P.toLinearMap.range.mkQ v)))))) = _
    rw [fS.apply_symm_apply, hfS, hf]
    rw [show τ g (k.smoothToL2 μ v) =
      k.smoothToL2 μ (σF.smoothSectionRepresentation IG hσF g v) from
        k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant g v]
    exact (hfS _).symm
  exact P.smoothEquivariantAnalyticIndex_eq IG σE σF hσE hσF hPg hP
    κ χ e' f' he' hf'

end AtiyahSinger
