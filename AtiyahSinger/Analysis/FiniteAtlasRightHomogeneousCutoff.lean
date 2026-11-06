/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteAtlasHomogeneousCutoff
public import AtiyahSinger.Analysis.ProductCoordinateSwap
public import AtiyahSinger.Analysis.RightTensorCutoffGlobalSymbol

/-!
# Homogeneity at infinity of the actual right-factor cutoff

Public module ID: M0620.

The high-frequency angular cutoff vanishes unless its retained factor already
lies beyond the fixed regularization radius. Thus the exact finite-atlas
coefficient, with all original signed weights, is degree one at infinity.
The radius controls both endpoints of a positive rescaling and works for
every original patch pair simultaneously.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option backward.isDefEq.respectTransparency false

variable {n m r₀ r₁ s : ℕ} {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
  {E₀ E₁ : M → Type*} {F : N → Type*}
  [∀ x, NormedAddCommGroup (E₀ x)] [∀ x, NormedSpace ℂ (E₀ x)]
  [∀ x, NormedAddCommGroup (E₁ x)] [∀ x, NormedSpace ℂ (E₁ x)]
  [∀ x, NormedAddCommGroup (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₀)) E₀)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₀)) E₀]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r₁)) E₁)]
  [FiberBundle (EuclideanSpace ℂ (Fin r₁)) E₁]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin s)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin s)) F]

/-- The exact canonical right-factor cutoff coefficient is degree one at infinity. -/
theorem QuantizationPresentation.exists_rightProductCutoffWeight_regularizedSymbol_homogeneous
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a : GlobalSymbolFunction (n := n) E₀ E₁)
    (ha : IsHomogeneousGlobalSymbol E₀ E₁ 1 a) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) (t : ℝ), 0 < t →
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      R ≤ g.length x (t • ξ₁) + k.length y (t • ξ₂) →
        ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
            A.regularizedSymbolFunction a x (t • ξ₁) =
          (t : ℂ) •
            (((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
              A.regularizedSymbolFunction a x ξ₁) := by
  classical
  obtain ⟨R, hR, hscale⟩ :=
    A.exists_productCutoffWeight_regularizedSymbol_homogeneous B g k a ha ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ t ht
  dsimp only
  intro hξ htξ
  let S := (productCoordinateSwap n m).toContinuousLinearEquiv.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let f := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
  have hfst (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (v, 0))) = η (f.symm (0, v))
    rw [productCoordinateSwap_apply]
  have hsnd (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (0, v))) = η (f.symm (v, 0))
    rw [productCoordinateSwap_apply]
  have hweight (i : Fin A.size) (j : Fin B.size)
      (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      (A.patch i).productCutoffWeight (B.patch j) ε x y (η.comp S) =
        (A.patch i).rightProductCutoffWeight (B.patch j) ε x y η := by
    dsimp only [QuantizationPatch.productCutoffWeight, QuantizationPatch.rightProductCutoffWeight]
    rw [hfst, hsnd]
  have hsmul : (t • ξ).comp S = t • ξ.comp S := by ext v; rfl
  -- The block permutation transports the same first-factor argument, with no new symbol.
  have h := hscale x y (ξ.comp S) t ht
  dsimp only at h
  rw [hfst, hsnd] at h
  have h' := h hξ htξ
  rw [← hsmul] at h'
  simpa only [hweight] using h'

/-- On a common exterior, the exact cutoff coefficient removes all dependence
on the original symbol's low-frequency regularization. -/
theorem QuantizationPresentation.exists_rightProductCutoffWeight_regularizedSymbol_eq
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a : GlobalSymbolFunction (n := n) E₀ E₁) (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
        ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            A.regularizedSymbolFunction a x ξ₁ =
          ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            a x ξ₁ := by
  classical
  obtain ⟨R, hR, hscale⟩ := A.exists_productCutoffWeight_regularizedSymbol_eq B g k a ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ
  dsimp only
  intro hξ
  let S := (productCoordinateSwap n m).toContinuousLinearEquiv.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let f := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
  have hfst (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (v, 0))) = η (f.symm (0, v))
    rw [productCoordinateSwap_apply]
  have hsnd (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (0, v))) = η (f.symm (v, 0))
    rw [productCoordinateSwap_apply]
  have hweight (i : Fin A.size) (j : Fin B.size)
      (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      (A.patch i).productCutoffWeight (B.patch j) ε x y (η.comp S) =
        (A.patch i).rightProductCutoffWeight (B.patch j) ε x y η := by
    dsimp only [QuantizationPatch.productCutoffWeight, QuantizationPatch.rightProductCutoffWeight]
    rw [hfst, hsnd]
  -- The very same coordinate block permutation identifies both original weights.
  have h := hscale x y (ξ.comp S)
  dsimp only at h
  rw [hfst, hsnd] at h
  simpa only [hweight] using h hξ

/-- Canonical right cutoffs preserve equality of two original symbols at infinity. -/
theorem QuantizationPresentation.exists_rightProductCutoffWeight_smul_eq_of_eventually_eq
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a b : GlobalSymbolFunction (n := n) E₀ E₁) (R₀ : ℝ) (hR₀ : 0 < R₀)
    (heq : ∀ x ξ, R₀ ≤ g.length x ξ → a x ξ = b x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ),
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
        ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            a x ξ₁ =
          ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
            b x ξ₁ := by
  classical
  obtain ⟨R, hR, hscale⟩ :=
    A.exists_productCutoffWeight_smul_eq_of_eventually_eq B g k a b R₀ hR₀ heq ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ
  dsimp only
  intro hξ
  let S := (productCoordinateSwap n m).toContinuousLinearEquiv.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let f := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
  have hfst (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (v, 0))) = η (f.symm (0, v))
    rw [productCoordinateSwap_apply]
  have hsnd (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (0, v))) = η (f.symm (v, 0))
    rw [productCoordinateSwap_apply]
  have hweight (i : Fin A.size) (j : Fin B.size)
      (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      (A.patch i).productCutoffWeight (B.patch j) ε x y (η.comp S) =
        (A.patch i).rightProductCutoffWeight (B.patch j) ε x y η := by
    dsimp only [QuantizationPatch.productCutoffWeight, QuantizationPatch.rightProductCutoffWeight]
    rw [hfst, hsnd]
  -- The very same coordinate block permutation identifies both original weights.
  have h := hscale x y (ξ.comp S)
  dsimp only at h
  rw [hfst, hsnd] at h
  simpa only [hweight] using h hξ

/-- Homogeneous full-symbol tails give homogeneous canonical cutoffs at infinity. -/
theorem QuantizationPresentation.exists_rightProductCutoffWeight_homogeneous_of_tail
    (A : QuantizationPresentation (n := n) (r := r₀) (q := r₁) E₀ E₁)
    (B : QuantizationPresentation (n := m) (r := s) (q := s) F F)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (k : SmoothCotangentMetric (n := m) (M := N))
    (a b : GlobalSymbolFunction (n := n) E₀ E₁)
    (hb : IsHomogeneousGlobalSymbol E₀ E₁ 1 b)
    (R₀ : ℝ) (hR₀ : 0 < R₀)
    (htail : ∀ x ξ, R₀ ≤ g.length x ξ → a x ξ = b x ξ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ R : ℝ, 0 < R ∧ ∀ (x : M) (y : N)
      (ξ : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) (t : ℝ), 0 < t →
      let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
      let ξ₁ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      let ξ₂ := (ξ.comp e.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)))
      R ≤ g.length x ξ₁ + k.length y ξ₂ →
      R ≤ g.length x (t • ξ₁) + k.length y (t • ξ₂) →
        ((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y (t • ξ) : ℝ) : ℂ) •
            a x (t • ξ₁) =
          (t : ℂ) •
            (((∑ i, ∑ j, (A.patch i).rightProductCutoffWeight (B.patch j) ε x y ξ : ℝ) : ℂ) •
              a x ξ₁) := by
  classical
  obtain ⟨R, hR, hscale⟩ :=
    A.exists_productCutoffWeight_homogeneous_of_tail B g k a b hb R₀ hR₀ htail ε hε
  refine ⟨R, hR, ?_⟩
  intro x y ξ t ht
  dsimp only
  intro hξ htξ
  let S := (productCoordinateSwap n m).toContinuousLinearEquiv.toContinuousLinearMap
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let f := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := n)
  have hfst (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (v, 0))) = η (f.symm (0, v))
    rw [productCoordinateSwap_apply]
  have hsnd (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      ((η.comp S).comp e.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin m))) =
        (η.comp f.symm.toContinuousLinearMap).comp
          (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))) := by
    ext v
    change η (productCoordinateSwap n m (e.symm (0, v))) = η (f.symm (v, 0))
    rw [productCoordinateSwap_apply]
  have hweight (i : Fin A.size) (j : Fin B.size)
      (η : EuclideanSpace ℝ (Fin (m + n)) →L[ℝ] ℝ) :
      (A.patch i).productCutoffWeight (B.patch j) ε x y (η.comp S) =
        (A.patch i).rightProductCutoffWeight (B.patch j) ε x y η := by
    dsimp only [QuantizationPatch.productCutoffWeight, QuantizationPatch.rightProductCutoffWeight]
    rw [hfst, hsnd]
  have hsmul : (t • ξ).comp S = t • ξ.comp S := by ext v; rfl
  -- The block permutation transports the same first-factor argument, with no new symbol.
  have h := hscale x y (ξ.comp S) t ht
  dsimp only at h
  rw [hfst, hsnd] at h
  have h' := h hξ htξ
  rw [← hsmul] at h'
  simpa only [hweight] using h'

end AtiyahSinger
