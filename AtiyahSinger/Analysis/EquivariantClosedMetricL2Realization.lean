/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedMetricL2Realization
public import AtiyahSinger.Analysis.EquivariantPseudodifferentialOperator
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# The original equivariant closed L² graph

Public module ID: M0488.

The specified unitary section actions preserve the entire graph closure of an
order-one operator, as well as its actual unbounded adjoint under ellipticity.
The argument starts on the original smooth graph and extends by continuity.
It supplies the original invariant domains and kernel subspaces for the graded
Hilbert tensor comparison; no action on an unrelated Sobolev norm is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Topology

set_option maxSynthPendingDepth 40

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [IsManifold IG ∞ G]
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
/-- The original integral unitaries preserve the entire closed graph of the same operator. -/
theorem PseudodifferentialOperator.metricL2ClosedRealization_graph_invariant :
    let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
    let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
    ∀ (g : G) (z : h.L2SectionSpace μ × k.L2SectionSpace μ),
      (ρ g z.1, τ g z.2) ∈ (P.metricL2ClosedRealization h k).graph ↔
        z ∈ (P.metricL2ClosedRealization h k).graph := by
  let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
  let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
  let R := σE.smoothSectionRepresentation IG hσE
  let S := σF.smoothSectionRepresentation IG hσF
  let L := P.metricL2ClosedRealization h k
  let C := P.metricL2SmoothCore h k
  let e := LinearEquiv.ofInjective (h.smoothToL2 μ) (h.smoothToL2_injective μ)
  have hsource (g : G) (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      ρ g (h.smoothToL2 μ u) = h.smoothToL2 μ (R g u) :=
    h.l2IsometryRepresentation_smoothToL2 μ IG σE hσE hInvariant hμInvariant g u
  have htarget (g : G) (u : smoothSections (n := n) (r := F.rank) F.Fiber) :
      τ g (k.smoothToL2 μ u) = k.smoothToL2 μ (S g u) :=
    k.l2IsometryRepresentation_smoothToL2 μ IG σF hσF kInvariant hμInvariant g u
  have hcore (g : G) (z : h.L2SectionSpace μ × k.L2SectionSpace μ)
      (hz : z ∈ C.graph) : (ρ g z.1, τ g z.2) ∈ C.graph := by
    obtain ⟨v, rfl⟩ := C.mem_graph_iff'.mp hz
    let u := e.symm v
    have hv : h.smoothToL2 μ u = v.val := congrArg Subtype.val (e.apply_symm_apply v)
    change (ρ g v.val, τ g (k.smoothToL2 μ (P.toLinearMap u))) ∈ C.graph
    rw [← hv, hsource, htarget]
    have hPu : P.toLinearMap (R g u) = S g (P.toLinearMap u) :=
      congrArg (fun A ↦ A u) (hPg g)
    refine C.mem_graph_iff'.mpr ⟨e (R g u), ?_⟩
    change (h.smoothToL2 μ (R g u), k.smoothToL2 μ (P.toLinearMap (e.symm (e (R g u))))) = _
    rw [e.symm_apply_apply, hPu]
  have hforward (g : G) (z : h.L2SectionSpace μ × k.L2SectionSpace μ)
      (hz : z ∈ L.graph) : (ρ g z.1, τ g z.2) ∈ L.graph := by
    -- Both original graph coordinates move continuously, so the entire closure is preserved.
    rw [(P.metricL2ClosedRealization_realization h k).1] at hz ⊢
    exact map_mem_closure
      (f := fun w : h.L2SectionSpace μ × k.L2SectionSpace μ ↦ (ρ g w.1, τ g w.2))
      (((ρ g).continuous.comp continuous_fst).prodMk
        ((τ g).continuous.comp continuous_snd)) hz (fun _ hw ↦ hcore g _ hw)
  dsimp only
  intro g z
  constructor
  · intro hz
    have hh := hforward g⁻¹ (ρ g z.1, τ g z.2) hz
    have hρ : ρ g⁻¹ (ρ g z.1) = z.1 := by
      change ((ρ g⁻¹) * (ρ g)) z.1 = z.1
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    have hτ : τ g⁻¹ (τ g z.2) = z.2 := by
      change ((τ g⁻¹) * (τ g)) z.2 = z.2
      rw [← map_mul, inv_mul_cancel, map_one]
      rfl
    simpa only [hρ, hτ] using hh
  · exact hforward g z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The same original unitary actions preserve the actual unbounded adjoint graph. -/
theorem PseudodifferentialOperator.metricL2ClosedRealization_adjoint_graph_invariant
    (hP : P.IsElliptic) :
    let ρ := h.l2ContRepresentation μ IG σE hσE hInvariant hμInvariant
    let τ := k.l2ContRepresentation μ IG σF hσF kInvariant hμInvariant
    ∀ (g : G) (z : k.L2SectionSpace μ × h.L2SectionSpace μ),
      (τ g z.1, ρ g z.2) ∈ (P.metricL2ClosedRealization h k).adjoint.graph ↔
        z ∈ (P.metricL2ClosedRealization h k).adjoint.graph := by
  -- Elliptic regularity identifies the full Hilbert adjoint with this geometric formal adjoint.
  rw [← P.metricL2ClosedRealization_metricFormalAdjoint h k hP]
  exact (P.metricFormalAdjoint h k).metricL2ClosedRealization_graph_invariant
    IG F E σF σE hσF hσE k h kInvariant hInvariant μ hμInvariant
    (P.isEquivariant_metricFormalAdjoint IG σE σF hσE hσF h k
      hInvariant kInvariant hμInvariant hPg)

end AtiyahSinger
