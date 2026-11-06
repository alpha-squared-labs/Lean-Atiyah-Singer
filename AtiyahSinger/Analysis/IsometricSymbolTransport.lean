/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GeometricProductCutoffRealization
public import AtiyahSinger.Analysis.IsometricSobolevCoordinates

/-!
# Symbol transport with fixed orthogonal base and fiber maps

Public module ID: M0766.

The same maps transport the full symbol, compact spatial support, and exact
Schwartz quantization. This packages the two coordinate permutations required
by right-factor product cutoffs, before any geometric atlas assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff SchwartzMap

variable {n m r q r' q' : ℕ}

/-- Transport a full symbol by the specified base and two coefficient isometries. -/
def isometricSymbolTransport
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : EuclideanSpace ℂ (Fin r') ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (o : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q'))
    (a : SymbolFunction n r q) : SymbolFunction m r' q' :=
  fun x ξ ↦ o.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((a (e x) (e ξ)).comp i.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The specified base and coefficient transport preserves symbol order. -/
theorem isSymbol_isometricSymbolTransport
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : EuclideanSpace ℂ (Fin r') ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (o : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q'))
    (d : ℝ) (a : SymbolFunction n r q) (ha : IsSymbol Set.univ d a) :
    IsSymbol Set.univ d (isometricSymbolTransport e i o a) := by
  let Φ : (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) →L[ℂ]
      (EuclideanSpace ℂ (Fin r') →L[ℂ] EuclideanSpace ℂ (Fin q')) :=
    LinearMap.toContinuousLinearMap {
      toFun b := o.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (b.comp i.toContinuousLinearEquiv.toContinuousLinearMap)
      map_add' b c := by ext v; simp
      map_smul' z b := by ext v; simp }
  exact isSymbol_continuousLinearMap d _ (isSymbol_comp_linearIsometry e d a ha)
    (Φ.restrictScalars ℝ)

/-- Orthogonal transport preserves compact spatial support of a full symbol. -/
theorem hasCompactSupport_isometricSymbolTransport
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : EuclideanSpace ℂ (Fin r') ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (o : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q'))
    (a : SymbolFunction n r q) (ha : HasCompactSupport a) :
    HasCompactSupport (isometricSymbolTransport e i o a) := by
  have hK : IsCompact (e.symm '' tsupport a) := ha.image e.symm.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal ?_ hK.isClosed)
  intro x hx
  refine ⟨e x, ?_, e.symm_apply_apply x⟩
  apply subset_tsupport
  intro hzero
  apply hx
  funext ξ
  simp [isometricSymbolTransport, hzero]

/-- These same coordinate maps transport the actual Schwartz quantization formula. -/
theorem quantize_isometricSymbolTransport
    (e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (i : EuclideanSpace ℂ (Fin r') ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin r))
    (o : EuclideanSpace ℂ (Fin q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q'))
    (a : SymbolFunction n r q)
    (u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (x : EuclideanSpace ℝ (Fin m)) :
    quantize (isometricSymbolTransport e i o a) (schwartzCoordinateEquiv e i.symm u) x =
      o (quantize a u (e x)) := by
  have hu : schwartzCoordinateEquiv e i.symm u =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.toContinuousLinearEquiv
        (SchwartzMap.postcompCLM i.symm.toContinuousLinearEquiv.toContinuousLinearMap u) := by
    apply SchwartzMap.ext
    intro y
    rfl
  rw [hu]
  exact (quantize_comp_linearIsometry e
    (fun y ξ ↦ o.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((a y ξ).comp i.toContinuousLinearEquiv.toContinuousLinearMap))
    (SchwartzMap.postcompCLM i.symm.toContinuousLinearEquiv.toContinuousLinearMap u) x).trans
      (quantize_conjugate_linearIsometry i o a u (e x))

end AtiyahSinger
