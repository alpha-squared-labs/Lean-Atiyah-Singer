/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Analysis.FiniteAtlasRightHomogeneousCutoff
public import AtiyahSinger.Analysis.HermitianMetricSymbol
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Homogeneity of the actual weighted full graded product symbol

Public module ID: M0697.

The selected full factor symbols agree with their original homogeneous data
outside specified radii. The actual finite cutoff weights then make the same
native graded symbol degree one at infinity. Adjunction uses the original
metrics and real weights, so its reverse blocks have the identical tail.
This is the full representative already attached to the specified cutoff PDO.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {n m : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  (E₀ E₁ : SmoothFiniteComplexBundle (n := n) M)
  (F₀ F₁ : SmoothFiniteComplexBundle (n := m) N)

set_option maxHeartbeats 1400000 in
-- Normalize the full-factor graded cutoff symbol on one common exterior region.
/-- The actual full-factor graded cutoff symbol is homogeneous on one common exterior. -/
theorem exists_gradedProductCutoff_homogeneous_at_infinity
    (C : QuantizationPresentation (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber)
    (D : QuantizationPresentation (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (h₀ : SmoothHermitianMetric (n := n) (r := E₀.rank) E₀.Fiber)
    (h₁ : SmoothHermitianMetric (n := n) (r := E₁.rank) E₁.Fiber)
    (k₀ : SmoothHermitianMetric (n := m) (r := F₀.rank) F₀.Fiber)
    (k₁ : SmoothHermitianMetric (n := m) (r := F₁.rank) F₁.Fiber)
    (p : globalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (q : globalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E₀.rank) (q := E₁.rank) E₀.Fiber E₁.Fiber 1)
    (b : homogeneousGlobalSymbolSpace (n := m) (r := F₀.rank) (q := F₁.rank) F₀.Fiber F₁.Fiber 1)
    (R₁ R₂ : ℝ) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hp : ∀ x ξ, R₁ ≤ g.length x ξ → p.val x ξ = a.val x ξ)
    (hq : ∀ y ξ, R₂ ≤ k.length y ξ → q.val y ξ = b.val y ξ)
    (ε : ℝ) (hε : 0 < ε) :
    letI := euclideanProductChartedSpace (n := n) (m := m) M N
    letI := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
    let pa := h₀.symbolSpaceAdjoint h₁ p
    let qa := k₀.symbolSpaceAdjoint k₁ q
    let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
    let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
      (ξ.comp c.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
    let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
      ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
    let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
      ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
    ∃ R : ℝ, 0 < R ∧ ∀ (S T : SmoothFiniteComplexBundle (n := n + m) (M × N))
      (e : ∀ x : M × N, ((E₀.Fiber x.1 ⊗[ℂ] F₀.Fiber x.2) ×
        (E₁.Fiber x.1 ⊗[ℂ] F₁.Fiber x.2)) ≃ₗ[ℂ] S.Fiber x)
      (f : ∀ x : M × N, ((E₁.Fiber x.1 ⊗[ℂ] F₀.Fiber x.2) ×
        (E₀.Fiber x.1 ⊗[ℂ] F₁.Fiber x.2)) ≃ₗ[ℂ] T.Fiber x)
      (s : GlobalSymbolFunction (n := n + m) S.Fiber T.Fiber),
      (∀ x ξ u v, s x ξ (e x (u, v)) = f x (reciprocalTensorSymbol
        ((α x ξ : ℂ) • (p.val x.1 (l ξ)).toLinearMap)
        ((α x ξ : ℂ) • (pa.val x.1 (l ξ)).toLinearMap)
        ((β x ξ : ℂ) • (q.val x.2 (r ξ)).toLinearMap)
        ((β x ξ : ℂ) • (qa.val x.2 (r ξ)).toLinearMap) (u, v))) →
      ∀ (x : M × N) (ξ : CotangentFiber (n := n + m) x) (t : ℝ), 0 < t →
        R ≤ g.length x.1 (l ξ) + k.length x.2 (r ξ) →
        R ≤ g.length x.1 (l (t • ξ)) + k.length x.2 (r (t • ξ)) →
          s x (t • ξ) = (t : ℂ) • s x ξ := by
  classical
  let := euclideanProductChartedSpace (n := n) (m := m) M N
  let := isManifold_euclideanProductChartedSpace (n := n) (m := m) M N
  let pa := h₀.symbolSpaceAdjoint h₁ p
  let qa := k₀.symbolSpaceAdjoint k₁ q
  let c := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let l (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let r (ξ : EuclideanSpace ℝ (Fin (n + m)) →L[ℝ] ℝ) :=
    (ξ.comp c.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m)))
  let α (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (C.patch i).productCutoffWeight (D.inputEndomorphism.patch j) ε x.1 x.2 ξ
  let β (x : M × N) (ξ : CotangentFiber (n := n + m) x) : ℝ :=
    ∑ i, ∑ j, (D.patch i).rightProductCutoffWeight (C.inputEndomorphism.patch j) ε x.2 x.1 ξ
  obtain ⟨A, hA, hleft⟩ := C.exists_productCutoffWeight_homogeneous_of_tail
    D.inputEndomorphism g k p.val a.val a.property.2 R₁ hR₁ hp ε hε
  obtain ⟨B, _, hright⟩ := D.exists_rightProductCutoffWeight_homogeneous_of_tail
    C.inputEndomorphism k g q.val b.val b.property.2 R₂ hR₂ hq ε hε
  dsimp only
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro S T e f s hs x ξ t ht hξ htξ
  have hl : l (t • ξ) = t • l ξ := by ext v; rfl
  have hr : r (t • ξ) = t • r ξ := by ext v; rfl
  change max A B ≤ g.length x.1 (l ξ) + k.length x.2 (r ξ) at hξ
  change max A B ≤ g.length x.1 (l (t • ξ)) + k.length x.2 (r (t • ξ)) at htξ
  rw [hl, hr] at htξ
  have hP : (α x (t • ξ) : ℂ) • p.val x.1 (l (t • ξ)) =
      (t : ℂ) • ((α x ξ : ℂ) • p.val x.1 (l ξ)) := by
    rw [hl]
    exact hleft x.1 x.2 ξ t ht ((le_max_left _ _).trans hξ)
      ((le_max_left _ _).trans htξ)
  have hQ : (β x (t • ξ) : ℂ) • q.val x.2 (r (t • ξ)) =
      (t : ℂ) • ((β x ξ : ℂ) • q.val x.2 (r ξ)) := by
    rw [hr]
    exact hright x.2 x.1 ξ t ht (by
      have h := (le_max_right A B).trans hξ
      simpa only [add_comm] using h) (by
      have h := (le_max_right A B).trans htξ
      simpa only [add_comm] using h)
  -- The exact adjoint operation conjugates scalars, which fixes these real coefficients.
  have hPi : (α x (t • ξ) : ℂ) • pa.val x.1 (l (t • ξ)) =
      (t : ℂ) • ((α x ξ : ℂ) • pa.val x.1 (l ξ)) := by
    have h := congrArg (h₀.adjoint h₁ x.1) hP
    simpa only [pa, SmoothHermitianMetric.symbolSpaceAdjoint,
      SmoothHermitianMetric.symbolAdjoint, h₀.adjoint_smul, Complex.conj_ofReal] using h
  have hQi : (β x (t • ξ) : ℂ) • qa.val x.2 (r (t • ξ)) =
      (t : ℂ) • ((β x ξ : ℂ) • qa.val x.2 (r ξ)) := by
    have h := congrArg (k₀.adjoint k₁ x.2) hQ
    simpa only [qa, SmoothHermitianMetric.symbolSpaceAdjoint,
      SmoothHermitianMetric.symbolAdjoint, k₀.adjoint_smul, Complex.conj_ofReal] using h
  have hPL := congrArg ContinuousLinearMap.toLinearMap hP
  have hPiL := congrArg ContinuousLinearMap.toLinearMap hPi
  have hQL := congrArg ContinuousLinearMap.toLinearMap hQ
  have hQiL := congrArg ContinuousLinearMap.toLinearMap hQi
  apply ContinuousLinearMap.ext
  intro w
  obtain ⟨⟨u, v⟩, rfl⟩ := (e x).surjective w
  change s x (t • ξ) (e x (u, v)) = (t : ℂ) • s x ξ (e x (u, v))
  rw [hs x (t • ξ) u v, hs x ξ u v, ← map_smul]
  apply congrArg (f x)
  change reciprocalTensorSymbol
    (((α x (t • ξ) : ℂ) • p.val x.1 (l (t • ξ))).toLinearMap)
    (((α x (t • ξ) : ℂ) • pa.val x.1 (l (t • ξ))).toLinearMap)
    (((β x (t • ξ) : ℂ) • q.val x.2 (r (t • ξ))).toLinearMap)
    (((β x (t • ξ) : ℂ) • qa.val x.2 (r (t • ξ))).toLinearMap) (u, v) = _
  rw [hPL, hPiL, hQL, hQiL]
  simp only [ContinuousLinearMap.toLinearMap_smul, reciprocalTensorSymbol,
    TensorProduct.map_smul_left,
    TensorProduct.map_smul_right, LinearMap.prod_apply, Function.prod_apply, LinearMap.coprod_apply,
    LinearMap.neg_apply, LinearMap.smul_apply, Prod.smul_mk, smul_add, smul_neg]
  rfl

end AtiyahSinger
