/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactPieceRefinement
public import AtiyahSinger.Analysis.CotangentChartNormBounds
public import AtiyahSinger.Analysis.ProductCutoffHomogeneousTail

/-!
# Homogeneous tails of the original refined quantization pieces

Public module ID: M0911.

Coordinate refinement multiplies the original full symbol only by two spatial
weights. On the original input support, the specified cotangent metric controls
the chart frequency. The actual product cutoff applied to that same refined
piece therefore has a homogeneous tail whenever the supplied full symbol does.

The original cutoffs are multiplied by the two specified spatial refinements;
the chart, frames and underlying full symbol stay fixed. This is the local
input to the associated-sphere homogeneous principal bridge.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [SecondCountableTopology M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

/-- Product cutoff of a specified refined quantization piece retains its homogeneous tail. -/
theorem QuantizationPatch.exists_refined_productCutoff_homogeneous_of_tail
    (A : QuantizationPatch (n := n) (r := r) (q := q) E F)
    (p : globalSymbolSpace (n := n) (r := r) (q := q) E F 1)
    (g : SmoothCotangentMetric (n := n) (M := M)) (R₀ : ℝ)
    (hp : ∀ x ξ (t : ℝ), 0 < t → R₀ ≤ g.length x ξ →
      R₀ ≤ g.length x (t • ξ) → p.val x (t • ξ) = (t : ℂ) • p.val x ξ)
    (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hρ : ContDiff ℝ ∞ ρ) (ε : ℝ) (hε : 0 < ε) :
    let L := (A.toPiece p).coordinateCutoff χ ρ hχ hρ
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (ξ : EuclideanSpace ℝ (Fin n)) (η : Y) (t : ℝ),
      0 < t → R ≤ ‖ξ‖ + ‖η‖ → R ≤ ‖t • ξ‖ + ‖t • η‖ →
      (productFrequencyCutoff ε ‖t • ξ‖ ‖t • η‖ : ℂ) •
          L.globalSymbolFunction x (covectorFromChart A.chart x (t • ξ)) =
        (t : ℂ) • ((productFrequencyCutoff ε ‖ξ‖ ‖η‖ : ℂ) •
          L.globalSymbolFunction x (covectorFromChart A.chart x ξ)) := by
  classical
  intro L
  -- The original symbol is multiplied only by the two specified spatial refinements.
  have hvalue (x : M) (ξ : CotangentFiber (n := n) x) :
      L.globalSymbolFunction x ξ =
        ((χ (A.chart x) * ρ (A.chart x) : ℝ) : ℂ) •
          ((A.weight x : ℂ) • p.val x ξ) := by
    have horiginal := congrArg (fun b : GlobalSymbolFunction (n := n) E F ↦ b x ξ)
      (A.globalSymbolFunction_toPiece p)
    change (A.toPiece p).globalSymbolFunction x ξ = (A.weight x : ℂ) • p.val x ξ
      at horiginal
    rw [← horiginal]
    dsimp only [L, PseudodifferentialPiece.globalSymbolFunction,
      PseudodifferentialPiece.coordinateCutoff]
    split_ifs
    · simp only [Complex.ofReal_mul, smul_smul]
      congr 1
      dsimp only [QuantizationPatch.toPiece]
      ring
    · exact (smul_zero _).symm
  obtain ⟨b, _, hb, _, hbound⟩ := g.exists_length_bounds_on
    A.chart A.chart_mem_atlas (tsupport A.input.cutoff) A.input.compact_support
      (fun _ hx ↦ (A.input.support_subset hx).1)
  let R₁ := max R₀ 1 / b
  let f (x : M) (ξ : EuclideanSpace ℝ (Fin n)) :=
    L.globalSymbolFunction x (covectorFromChart A.chart x ξ)
  have hscale : ∀ (x : M) (ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 < t →
      R₁ ≤ ‖ξ‖ → R₁ ≤ ‖t • ξ‖ → f x (t • ξ) = (t : ℂ) • f x ξ := by
    intro x ξ t ht hξ htξ
    dsimp only [f]
    by_cases hzero : A.weight x = 0
    · simp only [hvalue, hzero, Complex.ofReal_zero, zero_smul, smul_zero]
    have hx : x ∈ A.chart.source := by
      by_contra h
      exact hzero (by simp [QuantizationPatch.weight, h])
    have hsupp : A.chart x ∈ tsupport A.input.cutoff := by
      apply subset_tsupport
      intro h
      exact hzero (by simp [QuantizationPatch.weight, hx, h])
    have hlarge (η : EuclideanSpace ℝ (Fin n)) (hη : R₁ ≤ ‖η‖) :
        R₀ ≤ g.length x (covectorFromChart A.chart x η) := by
      have h := (hbound (A.chart x) hsupp η).1
      rw [A.chart.left_inv hx] at h
      have h' : max R₀ 1 ≤ ‖η‖ * b := (div_le_iff₀ hb).mp hη
      exact (le_max_left _ _).trans (by nlinarith)
    have hcov : covectorFromChart A.chart x (t • ξ) =
        t • covectorFromChart A.chart x ξ := by
      ext v
      change inner ℝ (t • ξ) (mfderiv _ _ A.chart x v) = _
      exact real_inner_smul_left ξ _ t
    have htail := hp x (covectorFromChart A.chart x ξ) t ht (hlarge ξ hξ)
      (hcov ▸ hlarge (t • ξ) htξ)
    rw [hvalue, hvalue, hcov, htail]
    simp only [smul_smul]
    congr 1
    ring
  exact exists_productFrequencyCutoff_homogeneous_of_tail ε R₁ hε f hscale

end AtiyahSinger
