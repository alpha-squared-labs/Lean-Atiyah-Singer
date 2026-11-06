/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolMetricInverseBound
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization

/-!
# The actual principal-localized finite full symbol has a metric inverse bound

Public module ID: M0861.

The stored base operator is exactly the sum of its specified native pieces.
Its principal class is therefore represented by the actual finite sum of those
full symbols. Ellipticity and the compact metric inverse estimate are applied
to that same sum. Any original lower-order difference from another principal
representative is contained in this chosen axis, rather than discarded.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

namespace PrincipalPseudodifferentialLocalization

set_option maxSynthPendingDepth 40 in
/-- The original finite sum is an elliptic horizontal axis in the specified native metrics. -/
theorem exists_fullSymbol_metric_inverse_bound
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic)
    (g : SmoothCotangentMetric (n := n) (M := B))
    (h : SmoothHermitianMetric (n := n) (r := a) E)
    (k : SmoothHermitianMetric (n := n) (r := a') E')
    (c : OpenPartialHomeomorph B (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) B)
    (e : Trivialization (EuclideanSpace ℂ (Fin a)) (π (EuclideanSpace ℂ (Fin a)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin a')) (π (EuclideanSpace ℂ (Fin a')) E'))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (K : Set B) (hK : IsCompact K)
    (hKe : K ⊆ c.source ∩ e.baseSet) (hKf : K ⊆ c.source ∩ f.baseSet) :
    let p := ∑ j, (C.piece j).globalSymbol
    ∃ R M : ℝ, 0 < R ∧ 0 ≤ M ∧ ∀ (ξ : EuclideanSpace ℝ (Fin n)), R ≤ ‖ξ‖ →
      let coefficient : ℝ := M / (1 + ‖ξ‖) ^ 2
      ∀ x ∈ K, let A := p.val x (covectorFromChart c x ξ)
        A.IsInvertible ∧ ∀ u : E x,
          (h.pairing x u u).re ≤ coefficient * (k.pairing x (A u) (A u)).re := by
  classical
  intro p
  -- The stored base operator is precisely this sum, so its remainder is the zero kernel.
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := a) E →ₗ[ℂ]
        smoothSections (n := n) (r := a') E') := by
    let K : SmoothKernel (n := n) (r := a) (q := a') E E' := {
      toFun := fun _ _ ↦ 0
      isSmooth := by
        intro f g _ _
        change ContMDiffOn _ _ ∞ (fun z : B × B ↦
          kernelInFrames E E' (fun _ _ ↦ 0) f g z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  have hp : C.baseOperator.principalSymbol = globalPrincipalSymbolClass E E' 1 p :=
    C.baseOperator.principalSymbol_eq_of_representation C.size C.piece (by
      rw [C.baseOperator_eq, sub_self]
      exact hzero)
  have hpEll : IsEllipticFullGlobalSymbol (r := a) (q := a') E E' 1 p.val :=
    (C.baseOperator.isElliptic_iff_of_principalSymbol_eq p hp).mp hC
  obtain ⟨R, M, hR, hM, hbound⟩ := hpEll.exists_compact_metric_inverse_bound
    p.val g h k c hc e f K hK hKe hKf
  refine ⟨R, M, hR, hM, ?_⟩
  intro ξ hξ coefficient x hx A
  -- Use the actual chart covector and the actual inverse of the same finite full symbol.
  have hfreq : covectorInChart c x (covectorFromChart c x ξ) = ξ :=
    covectorInChart_covectorFromChart c hc x (hKe hx).1 ξ
  obtain ⟨hi, hb⟩ := hbound x hx (covectorFromChart c x ξ) (hfreq.symm ▸ hξ)
  refine ⟨hi, ?_⟩
  intro u
  have hu := hb (A u)
  change (h.pairing x (A.inverse (A u)) (A.inverse (A u))).re ≤
    M / (1 + ‖covectorInChart c x (covectorFromChart c x ξ)‖) ^ 2 *
      (k.pairing x (A u) (A u)).re at hu
  rw [hi.inverse_apply_self, hfreq] at hu
  exact hu

end PrincipalPseudodifferentialLocalization

end AtiyahSinger
