/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential

/-!
# The original kernel through the native atlas section identity

Public module ID: M0804.

The native-to-atlas PDO construction conjugates the same full linear map by
section equivalences that preserve every pointwise value. Restrict those very
maps to their kernels. This equivalence supplies the full kernel
coordinates for associated evaluation and Green maps in both coefficient parities.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  (E F : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] {μ : Measure M}
  [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
/-- The same full native and atlas kernels are equivalent by their literal section values. -/
theorem PseudodifferentialOperator.exists_nativeAtlasKernelEquiv {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m) :
    letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
    ∃ e : P.toLinearMap.ker ≃ₗ[ℂ] P.toAtlasPseudodifferentialOperator.toLinearMap.ker,
      ∀ u x, (e u).val.val x = u.val.val x := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  let A := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let B := nativeSmoothSectionLinearEquiv (n := n) (r := q) F
  let Q := P.toAtlasPseudodifferentialOperator
  let f₀ := A.symm.toLinearMap.comp P.toLinearMap.ker.subtype
  have hf₀ (u : P.toLinearMap.ker) : f₀ u ∈ Q.toLinearMap.ker := by
    change B.symm (P.toLinearMap (A (A.symm u.val))) = 0
    rw [A.apply_symm_apply, u.property, B.symm.map_zero]
  let f := f₀.codRestrict Q.toLinearMap.ker hf₀
  have hbij : Function.Bijective f := by
    constructor
    · -- No values are identified: both section transports and kernel subtypes are injective.
      intro u v h
      apply Subtype.ext
      exact A.symm.injective (congrArg Subtype.val h)
    · -- The original conjugation identity returns every atlas zero mode to the native kernel.
      intro u
      have hu : P.toLinearMap (A u.val) = 0 := by
        have hz := u.property
        change B.symm (P.toLinearMap (A u.val)) = 0 at hz
        exact B.symm.injective (hz.trans B.symm.map_zero.symm)
      exact ⟨⟨A u.val, hu⟩, Subtype.ext (A.symm_apply_apply u.val)⟩
  exact ⟨LinearEquiv.ofBijective f hbij, fun _ _ ↦ rfl⟩

end AtiyahSinger
