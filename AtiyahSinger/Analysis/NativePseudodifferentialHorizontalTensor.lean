/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialManifoldParameter
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Geometry.TensorSectionOperator

/-!
# The complete native PDO on a horizontal tensor family

Public module ID: M0815.

The actual native PDO, including its full smoothing remainder, preserves
joint smoothness of every supplied contraction in the finite coefficient fibers.
For the specified coefficient contraction, pass through the literal
native-to-atlas section equivalence, and use the complete atlas parameter
theorem. The original designated native frames are recovered exactly.

This supplies the horizontal family regularity for actual metric adjoints;
it does not discard smoothing terms before lifting to an associated bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Manifold ComplexBundle MeasureTheory
open scoped ContDiff Manifold TensorProduct

variable {n k r q : ℕ} {M : Type*} [TopologicalSpace M]
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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

local notation "Y" => EuclideanSpace ℝ (Fin k)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Vin" => EuclideanSpace ℂ (Fin r)
local notation "Vout" => EuclideanSpace ℂ (Fin q)

variable [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 20 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full native PDO preserves every specified smooth finite tensor coordinate. -/
theorem PseudodifferentialOperator.contMDiffOn_tensorSectionOperator {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    {N : Type*} [TopologicalSpace N] [ChartedSpace Y N] [IsManifold 𝓘(ℝ, Y) ∞ N]
    (D : N → Type*) [∀ y, AddCommGroup (D y)] [∀ y, Module ℂ (D y)]
    [∀ y, FiniteDimensional ℂ (D y)] (U : Set N) (hU : IsOpen U)
    (w : ∀ y, dualTensorSections (D y) (smoothSections (n := n) (r := r) E))
    (l : ∀ y, D y →ₗ[ℂ] ℂ)
    (hw : ∀ (e : Trivialization Vin (π Vin E)), MemTrivializationAtlas e →
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vin) ∞
        (fun p : N × M ↦ (e ⟨p.2, TensorProduct.lid ℂ (E p.2)
          (TensorProduct.map (l p.1) LinearMap.id ((w p.1).val p.2))⟩).2)
        (U ×ˢ e.baseSet))
    (e : Trivialization Vout (π Vout F)) (he : MemTrivializationAtlas e) :
    ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Vout) ∞
      (fun p : N × M ↦ (e ⟨p.2, TensorProduct.lid ℂ (F p.2)
        (TensorProduct.map (l p.1) LinearMap.id
          ((tensorSectionOperator (D p.1) (smoothSections (n := n) (r := r) E)
            (smoothSections (n := n) (r := q) F) P.toLinearMap (w p.1)).val p.2))⟩).2)
      (U ×ˢ e.baseSet) := by
  let := modelTopology Vin E
  let := modelTopology Vout F
  let A := nativeSmoothComplexBundleAtlas (n := n) (r := r) E
  let B := nativeSmoothComplexBundleAtlas (n := n) (r := q) F
  let eE := nativeSmoothSectionLinearEquiv (n := n) (r := r) E
  let P' := P.toAtlasPseudodifferentialOperator
  let eIn := EuclideanSpace.equiv (Fin r) ℂ
  let eOut := EuclideanSpace.equiv (Fin q) ℂ
  -- Each contraction is the same native section, with unchanged fiber values.
  let u (y : N) : smoothSections (n := n) (r := r) E :=
    ⟨fun x ↦ TensorProduct.lid ℂ (E x)
      (TensorProduct.map (l y) LinearMap.id ((w y).val x)), (w y).property (l y)⟩
  let v (y : N) : A.smoothSections := eE.symm (u y)
  have hv (i : A.Index) :
      ContMDiffOn ((𝓘(ℝ, Y)).prod 𝓘(ℝ, X)) 𝓘(ℝ, Fin (A.rank i) → ℂ) ∞
        (fun p : N × M ↦ (A.chart i ⟨p.2, (v p.1).val p.2⟩).2)
        (U ×ˢ (A.chart i).baseSet) := by
    have hmodel := (eIn.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
    exact hmodel.comp_contMDiffOn (hw i.val i.property)
  -- The complete atlas theorem acts on P itself, retaining its actual remainder.
  have hp := P'.contMDiffOn_apply_manifold_parameter A B U hU v hv ⟨e, he⟩
  have hmodel := (eOut.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff (n := ∞)
  have hnative := hmodel.comp_contMDiffOn hp
  apply hnative.congr
  intro z _
  have h := congrFun (tensorSectionOperator_contract (D z.1)
    (smoothSections (n := n) (r := r) E) (smoothSections (n := n) (r := q) F)
    P.toLinearMap (w z.1) (l z.1)) z.2
  exact congrArg (fun t : F z.2 ↦ (e ⟨z.2, t⟩).2) h

end AtiyahSinger
