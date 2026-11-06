/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.RightProductCutoffRealization

/-!
# Native geometric right-factor product cutoff

Public module ID: M0659.

A compact second-factor PDO piece is cut off in the fixed product chart and
external tensor frames. The construction uses the actual transported Fourier
symbol in the original first-then-second coordinate order.
-/

@[expose] public noncomputable section

namespace AtiyahSinger


open Bundle
open scoped Manifold ContDiff TensorProduct

variable {m n s₀ s₁ r : ℕ} {N M : Type*}
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space N] [T2Space M]
  {F₀ F₁ : N → Type*} {E : M → Type*}
  [∀ x, NormedAddCommGroup (F₀ x)] [∀ x, NormedSpace ℂ (F₀ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₀)) F₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₀)) F₀]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₀)) F₀]
  [IsSmoothComplexBundle (n := m) (r := s₀) F₀]
  [∀ x, NormedAddCommGroup (F₁ x)] [∀ x, NormedSpace ℂ (F₁ x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s₁)) F₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin s₁)) F₁]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin s₁)) F₁]
  [IsSmoothComplexBundle (n := m) (r := s₁) F₁]
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

set_option maxHeartbeats 1000000 in
-- The two native tensor bundle instances and their chosen product frames must be unfolded together.
set_option backward.isDefEq.respectTransparency false in
/-- A compact second-factor piece gives an actual cutoff PDO piece in the selected
external tensor charts, with the same first-factor frame on both sides. -/
def PseudodifferentialPiece.rightProductCutoff
    (L : PseudodifferentialPiece (n := m) (r := s₀) (q := s₁) F₀ F₁ 1)
    (hLK : HasCompactSupport L.symbol)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (B C : BundleChartCutoff (r := r) E c) (hCB : C.frame = B.frame)
    (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
    letI := externalTensorTopology (r := r) (s := s₀) E F₀
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    letI := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
    letI := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
    letI := externalTensorTopology (r := r) (s := s₁) E F₁
    letI := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    letI := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    PseudodifferentialPiece (n := n + m) (r := r * s₀) (q := r * s₁)
      (externalTensorFiber E F₀) (externalTensorFiber E F₁) 1 := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedSpace (r := r) (s := s₀) E F₀
  let := externalTensorTopology (r := r) (s := s₀) E F₀
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
  let := externalTensorFiberNormedAddCommGroup (r := r) (s := s₁) E F₁
  let := externalTensorFiberNormedSpace (r := r) (s := s₁) E F₁
  let := externalTensorTopology (r := r) (s := s₁) E F₁
  let := externalTensorFiberBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorVectorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let := externalTensorIsSmoothComplexBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let A := externalTensorChartCutoff B L.input
  let D := externalTensorChartCutoff C L.output
  let Φ := tensorIdentitySymbolMap s₀ s₁ r
  let a : SymbolFunction m (s₀ * r) (s₁ * r) := fun x ξ ↦ Φ (L.symbol x ξ)
  have ha : IsSymbol Set.univ 1 a := by
    exact isSymbol_continuousLinearMap 1 L.symbol L.isSymbol (Φ.restrictScalars ℝ)
  have haK : HasCompactSupport a := by
    apply hLK.of_isClosed_subset (isClosed_tsupport a)
    apply closure_minimal ?_ (isClosed_tsupport L.symbol)
    intro x hx
    by_contra h
    have hzero := image_eq_zero_of_notMem_tsupport h
    apply hx
    funext ξ
    change Φ (L.symbol x ξ) = 0
    rw [hzero]
    exact Φ.map_zero
  let p := rightProductCutoffSymbol a C.cutoff ε
  have hp : IsSymbol Set.univ 1 p :=
    isSymbol_rightProductCutoffSymbol a ha C.cutoff C.smooth_cutoff ε hε
  have hpK : HasCompactSupport p :=
    hasCompactSupport_rightProductCutoffSymbol a haK C.cutoff C.compact_support ε
  have hB : A.frame.baseSet = B.frame.baseSet ×ˢ L.input.frame.baseSet := by
    let h := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s₀) E F₀
    exact (h.choose_spec.choose_spec.2.1 B.frame B.frame_mem_atlas
        L.input.frame L.input.frame_mem_atlas).choose_spec.2.1
  have hC : D.frame.baseSet = C.frame.baseSet ×ˢ L.output.frame.baseSet := by
    let h := exists_externalTensorBundle (n := n) (m := m) (r := r) (s := s₁) E F₁
    exact (h.choose_spec.choose_spec.2.1 C.frame C.frame_mem_atlas
        L.output.frame L.output.frame_mem_atlas).choose_spec.2.1
  have hsupp (f : EuclideanSpace ℝ (Fin n) → ℝ)
      (g : EuclideanSpace ℝ (Fin m) → ℝ) :
      tsupport (fun z ↦ f (e z).1 * g (e z).2) ⊆
        e ⁻¹' (tsupport f ×ˢ tsupport g) := by
    apply closure_minimal ?_
      (((isClosed_tsupport f).prod (isClosed_tsupport g)).preimage e.continuous)
    intro z hz
    constructor
    · apply subset_tsupport
      intro h
      exact hz (by simp only [h, zero_mul])
    · apply subset_tsupport
      intro h
      exact hz (by simp only [h, mul_zero])
  refine {
    chart := (c.prod L.chart).trans e.symm.toHomeomorph.toOpenPartialHomeomorph
    chart_mem_atlas := ?_
    input := A
    output := D
    input_support_in_output_frame := ?_
    output_support_in_input_frame := ?_
    operator := quantizeSchwartz 1 p hp hpK
    symbol := p
    isSymbol := hp
    operator_apply := quantizeSchwartz_apply 1 p hp hpK }
  · refine ⟨c.prod L.chart, ?_, e.symm.toHomeomorph.toOpenPartialHomeomorph,
      Set.mem_singleton _, rfl⟩
    exact ⟨c, hc, L.chart, L.chart_mem_atlas, rfl⟩
  · intro z hz
    have hz' := hsupp B.cutoff L.input.cutoff hz
    change (c.symm (e z).1, L.chart.symm (e z).2) ∈ D.frame.baseSet
    rw [hC, hCB]
    exact ⟨(B.support_subset hz'.1).2, L.input_support_in_output_frame hz'.2⟩
  · intro z hz
    have hz' := hsupp C.cutoff L.output.cutoff hz
    change (c.symm (e z).1, L.chart.symm (e z).2) ∈ A.frame.baseSet
    rw [hB, ← hCB]
    exact ⟨(C.support_subset hz'.1).2, L.output_support_in_input_frame hz'.2⟩


end AtiyahSinger
