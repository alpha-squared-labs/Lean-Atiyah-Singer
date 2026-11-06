/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Local symbols of type (1,0)

Public module ID: M1018.

D03/D05, SL01 and SR01, in a Euclidean bundle trivialization. Smoothness is real
smoothness even though the fibers and their linear maps are complex. `IsSymbol` is
the standard Hörmander S^m_(1,0) condition. No SG-specific "classical" type is introduced.
Having a homogeneous leading representative is imposed explicitly when needed.
These local predicates concern symbols rather than global operators.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ContDiff


set_option maxSynthPendingDepth 10

variable {n r q : ℕ}

/-- The mixed derivative, first in ξ and then in x, as a multilinear map. -/
def symbolDerivative (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
    (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (i j : ℕ) (x ξ : EuclideanSpace ℝ (Fin n)) :
    ContinuousMultilinearMap ℝ (fun _ : Fin i ↦ EuclideanSpace ℝ (Fin n))
      (ContinuousMultilinearMap ℝ (fun _ : Fin j ↦ EuclideanSpace ℝ (Fin n))
        (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) :=
  iteratedFDeriv ℝ i (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) x

/-- The usual S^m_(1,0) symbol estimates on an open coordinate domain U. -/
def IsSymbol (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry a) (U ×ˢ Set.univ) ∧
    ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K → ∀ i j : ℕ,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
        ‖symbolDerivative a i j x ξ‖ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ))

/-- Positive real homogeneity of a principal symbol, away from the zero section. -/
def IsHomogeneousSymbol (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : Prop :=
  ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → ∀ t : ℝ, 0 < t → a x (t • ξ) = (t ^ m) • a x ξ

/-- Ellipticity of a homogeneous principal symbol is invertibility for nonzero covectors. -/
def IsEllipticSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : Prop :=
  ∀ x ∈ U, ∀ ξ, ξ ≠ 0 → Function.Bijective (a x ξ)

/-- Symbols of arbitrarily negative order; this is a condition on symbols, not on operators. -/
def IsSmoothingSymbol (U : Set (EuclideanSpace ℝ (Fin n)))
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : Prop :=
  ∀ m : ℝ, IsSymbol U m a

/-- The partial-sum remainder estimates at the prescribed orders `m N`.
Strict decrease and convergence of `m` to negative infinity are separate hypotheses
when this predicate is used for an asymptotic expansion. -/
def HasSymbolExpansion (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ → ℝ)
    (a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (terms : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q))) : Prop :=
  ∀ N : ℕ, IsSymbol U (m N) (a - ∑ j ∈ Finset.range N, terms j)

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use proved open-domain expansion existence. The arbitrary-domain
uniqueness statement below is outside that route; its historical outline is unverified.
This block defines no Lean constant.

/-- SR01: two asymptotic sums differ by an infinitely smoothing symbol. -/
theorem isSmoothingSymbol_sub_of_expansion
    (U : Set (EuclideanSpace ℝ (Fin n))) (m : ℕ → ℝ)
    (hlim : Filter.Tendsto m Filter.atTop Filter.atBot)
    (terms : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (a b : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)))
    (ha : HasSymbolExpansion U m a terms) (hb : HasSymbolExpansion U m b terms) :
    IsSmoothingSymbol U (a - b) 
  /- Subtract the two remainder estimates at the same N. For every desired order,
  choose N with m N below it. Symbol classes increase with their order. -/
-/

end AtiyahSinger
