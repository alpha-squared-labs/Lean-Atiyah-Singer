/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AveragedGradedTensorSymbol
public import AtiyahSinger.Topology.EquivariantGradedCutoffHomotopy

/-!
# The equivariant support homotopy of an actual averaged graded boundary

Public module ID: M0317.

The full matrix integral determines real cutoff coefficients on the common
compact exterior. The dominant coefficient stays exactly one. The original
boundary maps, their fixed actions and the same Hermitian adjoint pairs then
give an equivariant affine homotopy to the uncut graded boundary.
No continuity or measurability of the auxiliary scalar coefficients is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle ComplexBundle MeasureTheory
open scoped TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {S T : X → Type*}
  [∀ x, NormedAddCommGroup (S x)] [∀ x, NormedSpace ℂ (S x)]
  [∀ x, FiniteDimensional ℂ (S x)]
  [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S]
  [∀ x, NormedAddCommGroup (T x)] [∀ x, NormedSpace ℂ (T x)]
  [∀ x, FiniteDimensional ℂ (T x)]
  [TopologicalSpace (TotalSpace Unit T)] [IsFiniteRank T]
  {E₀ E₁ F₀ F₁ : X → Type*}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, FiniteDimensional ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, FiniteDimensional ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, FiniteDimensional ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]
  [∀ x, FiniteDimensional ℂ (F₁ x)]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

set_option maxHeartbeats 800000 in

/-- The actual averaged graded boundary is equivariantly homotopic to the uncut boundary. -/
theorem CompactSupportTriple.equivariantlyHomotopic_of_averagedGradedTensor
    (a b : CompactSupportTriple S T)
    (ρS : EquivariantStructure G S) (ρT : EquivariantStructure G T)
    (hEA : a.IsEquivariant ρS ρT) (hEB : b.IsEquivariant ρS ρT)
    (K : Set X) (hK : IsCompact K)
    (hInv : ∀ (g : G) (x : X), g • x ∈ K ↔ x ∈ K)
    (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (e : ∀ x, ((E₀ x ⊗[ℂ] F₀ x) × (E₁ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] S x)
    (f : ∀ x, ((E₁ x ⊗[ℂ] F₀ x) × (E₀ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] T x)
    (h₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (h₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (k₀ : ∀ x, InnerProductSpace.Core ℂ (F₀ x))
    (k₁ : ∀ x, InnerProductSpace.Core ℂ (F₁ x))
    (p : ∀ x, E₀ x →ₗ[ℂ] E₁ x) (pi : ∀ x, E₁ x →ₗ[ℂ] E₀ x)
    (q : ∀ x, F₀ x →ₗ[ℂ] F₁ x) (qi : ∀ x, F₁ x →ₗ[ℂ] F₀ x)
    (hp : ∀ x u v, (h₁ x).inner (p x u) v = (h₀ x).inner u (pi x v))
    (hq : ∀ x u v, (k₁ x).inner (q x u) v = (k₀ x).inner u (qi x v))
    (A : ∀ x : (Kᶜ : Set X), Ω → S x.val →L[ℂ] T x.val)
    (hAint : ∀ x, Integrable (A x) μ)
    (α β : (Kᶜ : Set X) → Ω → ℝ)
    (hA : ∀ (x : (Kᶜ : Set X)) v,
      (a.enlarge K hK ha).boundary.linearEquiv x (e x.val v) =
        f x.val (reciprocalTensorSymbol (p x.val) (pi x.val) (q x.val) (qi x.val) v))
    (hB : ∀ (x : (Kᶜ : Set X)) v,
      (b.enlarge K hK hb).boundary.linearEquiv x v = (∫ z, A x z ∂μ) v)
    (hformula : ∀ (x : (Kᶜ : Set X)) z v,
      A x z (e x.val v) = f x.val (reciprocalTensorSymbol
        ((α x z : ℂ) • p x.val) ((α x z : ℂ) • pi x.val)
        ((β x z : ℂ) • q x.val) ((β x z : ℂ) • qi x.val) v))
    (hdominant : ∀ x : (Kᶜ : Set X),
      (Function.Bijective (p x.val) ∧ ∀ z, α x z = 1) ∨
        (Function.Bijective (q x.val) ∧ ∀ z, β x z = 1)) :
    a.EquivariantlyHomotopic b ρS ρT := by
  classical
  have hweights (x : (Kᶜ : Set X)) := exists_integral_reciprocalTensorSymbol_weights
    (p x.val) (pi x.val) (q x.val) (qi x.val) (e x.val) (f x.val)
    (A x) (hAint x) (α x) (β x) (hformula x) (hdominant x)
  choose αbar βbar hmatrix hdom using hweights
  apply a.equivariantlyHomotopic_of_weightedGradedTensor b ρS ρT hEA hEB K hK hInv ha hb
    e f h₀ h₁ k₀ k₁ p pi q qi hp hq αbar βbar hA
  · intro x v
    rw [hB]
    exact hmatrix x v
  · exact hdom

end AtiyahSinger.ComplexBundle
