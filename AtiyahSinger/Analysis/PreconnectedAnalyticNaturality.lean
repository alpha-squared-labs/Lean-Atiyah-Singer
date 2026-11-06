/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AnalyticIndex
public import AtiyahSinger.Analysis.DiffeomorphEllipticRepresentative
public import AtiyahSinger.Analysis.DiffeomorphSymbolKClass
public import AtiyahSinger.Geometry.DiffeomorphBundlePullback
public import AtiyahSinger.Topology.OpenCotangentKZero

/-!
# Analytic-index naturality on a preconnected compact base

Public module ID: M0859.

The original K-class representative is transported by the specified
inverse-dual diffeomorphism. One finite quantization family produces actual
operators with conjugate smooth section maps and the same displayed symbol
square. Their indices agree; evaluating the two already constructed analytic
homomorphisms proves naturality for every class. Empty bases are allowed.
This is the whole-base coordinate invariance in SG III.13, before excision.
-/

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

@[expose] public noncomputable section

namespace AtiyahSinger

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N]
  [T2Space N] [SecondCountableTopology N] [CompactSpace N] [PreconnectedSpace N]
  [MeasurableSpace N] [BorelSpace N]

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent

/-- Analytic indices on preconnected compact bases commute with the actual cotangent lift. -/
theorem analyticIndex_diffeomorph (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
    (ν : Measure N) [IsSmoothPositiveMeasure (n := n) ν]
    (e : M ≃ₘ⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), 𝓘(ℝ, EuclideanSpace ℝ (Fin n))⟯ N) :
    (analyticIndex ν).comp (cotangentKZeroDiffeomorph e).toAddMonoidHom =
      analyticIndex μ := by
  classical
  apply AddMonoidHom.ext
  intro u
  -- Choose a symbol representing this exact class on the given preconnected base.
  obtain ⟨E, F, a, ha, hclass⟩ :=
    exists_smooth_elliptic_representative_of_preconnected u 0
  let G := E.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
  let H := F.pullback ⟨e.symm, e.symm.continuous⟩ e.symm.contMDiff
  obtain ⟨A⟩ := nonempty_quantizationPresentation
    (n := n) (r := E.rank) (q := F.rank) (E := E.Fiber) (F := F.Fiber)
  obtain ⟨R⟩ := nonempty_quantizationPresentation
    (n := n) (r := G.rank) (q := H.rank) (E := G.Fiber) (F := H.Fiber)
  -- Quantize and transport one finite family, retaining the canonical inverse-pullback fibers.
  obtain ⟨P, Q, b, hPe, hQe, hb, hP, hQ, hsymbol, hindex⟩ :=
    exists_elliptic_representatives_of_diffeomorph E F G H ⊤ ⊤ rfl rfl (diffeomorphTop e)
      (fun x ↦ LinearEquiv.cast (R := ℂ) (M := E.Fiber) (e.symm_apply_apply x.val).symm)
      (isSmoothBundleMap_diffeomorphPullback_top E e)
      (fun x ↦ LinearEquiv.cast (R := ℂ) (M := F.Fiber) (e.symm_apply_apply x.val).symm)
      (isSmoothBundleMap_diffeomorphPullback_top F e) ν μ a ha A R
  -- The geometric symbol square gives the displayed K transport on these same representatives.
  have hu : P.symbolKClassOfHomogeneous A a hP hPe = u := hclass
  have hv : Q.symbolKClassOfHomogeneous R b hQ hQe = cotangentKZeroDiffeomorph e u := by
    rw [← hclass]
    exact (homogeneousSymbolKClass_diffeomorphPullback e E F a ha b hb hsymbol).symm
  -- Evaluate both original homomorphisms and use the actual section-operator index equality.
  change analyticIndex ν (cotangentKZeroDiffeomorph e u) = analyticIndex μ u
  rw [← hv, PseudodifferentialOperator.analyticIndex_symbolKClassOfHomogeneous ν Q R b hQ hQe]
  rw [← hu, PseudodifferentialOperator.analyticIndex_symbolKClassOfHomogeneous μ P A a hP hPe]
  exact hindex.symm

end AtiyahSinger
