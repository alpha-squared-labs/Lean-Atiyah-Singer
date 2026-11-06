/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HermitianMetricL2Realization
public import AtiyahSinger.Analysis.ZeroOrderBundleMap

/-!
# The actual order-zero action of a smooth bundle map

Public module ID: M0962.

Multiplication by a smooth bundle map is an order-zero PDO. A smooth bundle
isomorphism and its original inverse induce bounded inverse maps on the exact
metric L² completions, even when the two metrics do not make it an isometry.
These maps will transport equivariant Fredholm indices without changing the
underlying section action. The compact-base boundedness is supplied by the
already constructed order-zero Sobolev realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

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

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

/-- Multiplication by the specified smooth fiber map is an original order-zero PDO. -/
theorem isPseudodifferentialOperator_smoothSectionMap
    (a : ∀ x, E x →ₗ[ℂ] F x) (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    IsPseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0
      (smoothSectionMap a ha) := by
  let D : DifferentialOperator (n := n) (r := r) (q := q) E F 0 :=
    ⟨smoothSectionMap a ha, isDifferentialOperator_smoothSectionMap a ha⟩
  simpa only [Nat.cast_zero] using D.isPseudodifferentialOperator (μ := μ)

/-- The original fiber multiplication, with its derived PDO certificate. -/
def smoothBundleMapOperator
    (a : ∀ x, E x →ₗ[ℂ] F x) (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a) :
    PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ 0 where
  toLinearMap := smoothSectionMap a ha
  isPseudodifferentialOperator := isPseudodifferentialOperator_smoothSectionMap a ha

/-- The given smooth bundle isomorphism has a bounded inverse on the exact metric L² spaces. -/
theorem exists_l2Equiv_of_smoothBundleIso
    (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap))
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    (k : SmoothHermitianMetric (n := n) (r := q) F) :
    ∃ U : h.L2SectionSpace μ ≃L[ℂ] k.L2SectionSpace μ,
      ∀ u, U (h.smoothToL2 μ u) = k.smoothToL2 μ (smoothSectionEquiv e he u) := by
  let P := smoothBundleMapOperator (μ := μ) (fun x ↦ (e x).toLinearMap) he
  let Q := smoothBundleMapOperator (μ := μ) (fun x ↦ (e x).symm.toLinearMap) (he.symm e)
  let A := P.metricL2Extension h k
  let B := Q.metricL2Extension k h
  let S := smoothSectionEquiv e he
  have hA (u : smoothSections (n := n) (r := r) E) :
      A (h.smoothToL2 μ u) = k.smoothToL2 μ (S u) := P.metricL2Extension_smooth h k u
  have hB (u : smoothSections (n := n) (r := q) F) :
      B (k.smoothToL2 μ u) = h.smoothToL2 μ (S.symm u) := Q.metricL2Extension_smooth k h u
  -- Both inverse identities hold first on the very same dense smooth images.
  have hBA : B.comp A = ContinuousLinearMap.id ℂ (h.L2SectionSpace μ) := by
    apply DFunLike.coe_injective
    apply (h.denseRange_smoothToL2 μ).equalizer (B.comp A).continuous
      (ContinuousLinearMap.id ℂ (h.L2SectionSpace μ)).continuous
    funext u
    change B (A (h.smoothToL2 μ u)) = h.smoothToL2 μ u
    rw [hA, hB, S.symm_apply_apply]
  have hAB : A.comp B = ContinuousLinearMap.id ℂ (k.L2SectionSpace μ) := by
    apply DFunLike.coe_injective
    apply (k.denseRange_smoothToL2 μ).equalizer (A.comp B).continuous
      (ContinuousLinearMap.id ℂ (k.L2SectionSpace μ)).continuous
    funext u
    change A (B (k.smoothToL2 μ u)) = k.smoothToL2 μ u
    rw [hB, hA, S.apply_symm_apply]
  -- Package the actual two bounded maps, retaining the smooth action specification.
  let U : h.L2SectionSpace μ ≃L[ℂ] k.L2SectionSpace μ :=
    { A.toLinearMap with
      invFun := B
      left_inv := fun x ↦ DFunLike.congr_fun hBA x
      right_inv := fun x ↦ DFunLike.congr_fun hAB x
      continuous_toFun := A.continuous
      continuous_invFun := B.continuous }
  exact ⟨U, hA⟩

end AtiyahSinger
