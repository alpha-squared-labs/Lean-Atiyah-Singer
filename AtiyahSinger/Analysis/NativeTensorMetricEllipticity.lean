/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianTensorMetricInverseTransport
public import AtiyahSinger.Analysis.FiniteMetricEllipticity
public import AtiyahSinger.Algebra.HermitianCoreTensorSymbol

/-!
# Quantitative ellipticity of a specified native tensor family

Public module ID: M0816.

Local inverse bounds on the original metric tensor factors are transported
through the specified native tensor and orthogonal sum identifications.
A finite compact chart cover selects one positive threshold giving full
first-order ellipticity of the same symbol at every smaller allowed parameter.
No homogeneity or choice of another principal representative is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff TensorProduct Topology

variable {n : ℕ} {M ι : Type*} [Finite ι] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]
  (N₀₀ N₁₀ N₀₁ N₁₁ Nplus Nminus : SmoothFiniteComplexBundle (n := n) M)
  (E₀ E₁ F₀ F₁ : M → Type*)
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in
-- All pointwise norms are those of the four supplied positive Hermitian forms.
/-- Finite inverse bounds imply full ellipticity of the same native tensor symbol family. -/
theorem exists_isEllipticFullGlobalSymbol_of_tensor_inverse_bounds
    (e₀₀ : ∀ x, (E₀ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₀₀.Fiber x)
    (e₁₀ : ∀ x, (E₁ x ⊗[ℂ] F₀ x) ≃ₗ[ℂ] N₁₀.Fiber x)
    (e₀₁ : ∀ x, (E₀ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₀₁.Fiber x)
    (e₁₁ : ∀ x, (E₁ x ⊗[ℂ] F₁ x) ≃ₗ[ℂ] N₁₁.Fiber x)
    (k₀₀ : SmoothHermitianMetric (n := n) (r := N₀₀.rank) N₀₀.Fiber)
    (k₁₀ : SmoothHermitianMetric (n := n) (r := N₁₀.rank) N₁₀.Fiber)
    (k₀₁ : SmoothHermitianMetric (n := n) (r := N₀₁.rank) N₀₁.Fiber)
    (k₁₁ : SmoothHermitianMetric (n := n) (r := N₁₁.rank) N₁₁.Fiber)
    (c₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (c₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (d₀ : ∀ x, InnerProductSpace.Core ℂ (F₀ x))
    (d₁ : ∀ x, InnerProductSpace.Core ℂ (F₁ x))
    (hk₀₀ : ∀ x u v a b, k₀₀.pairing x (e₀₀ x (u ⊗ₜ[ℂ] a))
      (e₀₀ x (v ⊗ₜ[ℂ] b)) = (c₀ x).inner u v * (d₀ x).inner a b)
    (hk₁₀ : ∀ x u v a b, k₁₀.pairing x (e₁₀ x (u ⊗ₜ[ℂ] a))
      (e₁₀ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₀ x).inner a b)
    (hk₀₁ : ∀ x u v a b, k₀₁.pairing x (e₀₁ x (u ⊗ₜ[ℂ] a))
      (e₀₁ x (v ⊗ₜ[ℂ] b)) = (c₀ x).inner u v * (d₁ x).inner a b)
    (hk₁₁ : ∀ x u v a b, k₁₁.pairing x (e₁₁ x (u ⊗ₜ[ℂ] a))
      (e₁₁ x (v ⊗ₜ[ℂ] b)) = (c₁ x).inner u v * (d₁ x).inner a b)
    (ePlus : ∀ x, (N₀₀.Fiber x × N₁₁.Fiber x) ≃ₗ[ℂ] Nplus.Fiber x)
    (eMinus : ∀ x, (N₁₀.Fiber x × N₀₁.Fiber x) ≃ₗ[ℂ] Nminus.Fiber x)
    (kPlus : SmoothHermitianMetric (n := n) (r := Nplus.rank) Nplus.Fiber)
    (kMinus : SmoothHermitianMetric (n := n) (r := Nminus.rank) Nminus.Fiber)
    (hkPlus : ∀ x u v, kPlus.pairing x (ePlus x u) (ePlus x v) =
      k₀₀.pairing x u.1 v.1 + k₁₁.pairing x u.2 v.2)
    (hkMinus : ∀ x u v, kMinus.pairing x (eMinus x u) (eMinus x v) =
      k₁₀.pairing x u.1 v.1 + k₀₁.pairing x u.2 v.2)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (c : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : ∀ i, c i ∈ IsManifold.maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M)
    (L : ι → Set M) (hL : ∀ i, IsCompact (L i))
    (hLc : ∀ i, L i ⊆ (c i).source) (hcover : ∀ x, ∃ i, x ∈ L i)
    (pf : ℝ → ∀ x, CotangentFiber (n := n) x → E₀ x →ₗ[ℂ] E₁ x)
    (qf : ℝ → ∀ x, CotangentFiber (n := n) x → F₀ x →ₗ[ℂ] F₁ x)
    (pi : {ε : ℝ // 0 < ε ∧ ε ≤ 1} →
      ∀ x, CotangentFiber (n := n) x → E₁ x →ₗ[ℂ] E₀ x)
    (qi : {ε : ℝ // 0 < ε ∧ ε ≤ 1} →
      ∀ x, CotangentFiber (n := n) x → F₁ x →ₗ[ℂ] F₀ x)
    (p : {ε : ℝ // 0 < ε ∧ ε ≤ 1} → GlobalSymbolFunction (n := n)
      Nplus.Fiber Nminus.Fiber)
    (hp : ∀ ε x ξ u v,
      p ε x ξ (ePlus x (e₀₀ x u, e₁₁ x v)) =
        let w := reciprocalTensorSymbol (pf ε.val x ξ) (pi ε x ξ)
          (qf ε.val x ξ) (qi ε x ξ) (u, v)
        eMinus x (e₁₀ x w.1, e₀₁ x w.2))
    (hlocal : ∀ i, ∃ ε₀ R C : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R ∧ 0 ≤ C ∧
      ∀ ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}, ε.val ≤ ε₀ →
        ∀ x ∈ L i, ∀ ξ : CotangentFiber (n := n) x,
        R ≤ ‖covectorInChart (c i) x ξ‖ →
        letI : InnerProductSpace.Core ℂ (E₀ x) := c₀ x
        letI : InnerProductSpace.Core ℂ (E₁ x) := c₁ x
        letI : InnerProductSpace.Core ℂ (F₀ x) := d₀ x
        letI : InnerProductSpace.Core ℂ (F₁ x) := d₁ x
        letI : NormedAddCommGroup (E₀ x) :=
          InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
        letI : NormedAddCommGroup (E₁ x) :=
          InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
        letI : NormedAddCommGroup (F₀ x) :=
          InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
        letI : NormedAddCommGroup (F₁ x) :=
          InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
        letI : InnerProductSpace ℂ (E₀ x) := InnerProductSpace.ofCore
          (inferInstance : PreInnerProductSpace.Core ℂ _)
        letI : InnerProductSpace ℂ (E₁ x) := InnerProductSpace.ofCore
          (inferInstance : PreInnerProductSpace.Core ℂ _)
        letI : InnerProductSpace ℂ (F₀ x) := InnerProductSpace.ofCore
          (inferInstance : PreInnerProductSpace.Core ℂ _)
        letI : InnerProductSpace ℂ (F₁ x) := InnerProductSpace.ofCore
          (inferInstance : PreInnerProductSpace.Core ℂ _)
        let T := reciprocalTensorSymbol (pf ε.val x ξ) (pi ε x ξ)
          (qf ε.val x ξ) (qi ε x ξ)
        Function.Bijective T ∧ ∀ u,
          ‖u‖ ≤ (C / (1 + ‖covectorInChart (c i) x ξ‖)) * ‖T u‖) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧
      ∀ ε : {ε : ℝ // 0 < ε ∧ ε ≤ 1}, ε.val ≤ ε₀ →
        IsEllipticFullGlobalSymbol (r := Nplus.rank) (q := Nminus.rank)
          Nplus.Fiber Nminus.Fiber 1 (p ε) := by
  classical
  -- Extend the symbol family by zero outside the allowed parameter interval.
  let p' (ε : ℝ) : GlobalSymbolFunction (n := n) Nplus.Fiber Nminus.Fiber :=
    if h : 0 < ε ∧ ε ≤ 1 then p ⟨ε, h⟩ else 0
  have henergy (i : ι) : ∃ ε₀ R C : ℝ, 0 < ε₀ ∧ 0 < R ∧ 0 ≤ C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ x ∈ L i, ∀ ξ : CotangentFiber (n := n) x,
        R ≤ ‖covectorInChart (c i) x ξ‖ → Function.Bijective (p' ε x ξ) ∧
          ∀ u : Nplus.Fiber x, (1 + ‖covectorInChart (c i) x ξ‖) ^ 2 *
            (kPlus.pairing x u u).re ≤ C *
              (kMinus.pairing x (p' ε x ξ u) (p' ε x ξ u)).re := by
    obtain ⟨ε₀, R, C, hε₀, hε₀one, hR, _hC, hbound⟩ := hlocal i
    refine ⟨ε₀, R, 2 * C ^ 2, hε₀, hR, by positivity, ?_⟩
    intro ε hε hεsmall x hx ξ hξ
    let ε' : {ε : ℝ // 0 < ε ∧ ε ≤ 1} := ⟨ε, hε, hεsmall.trans hε₀one⟩
    have hp' : p' ε = p ε' := dite_eq_left ε'.property
    rw [hp']
    let : InnerProductSpace.Core ℂ (E₀ x) := c₀ x
    let : InnerProductSpace.Core ℂ (E₁ x) := c₁ x
    let : InnerProductSpace.Core ℂ (F₀ x) := d₀ x
    let : InnerProductSpace.Core ℂ (F₁ x) := d₁ x
    let : NormedAddCommGroup (E₀ x) :=
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    let : NormedAddCommGroup (E₁ x) :=
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    let : NormedAddCommGroup (F₀ x) :=
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    let : NormedAddCommGroup (F₁ x) :=
      InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
    let : InnerProductSpace ℂ (E₀ x) := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    let : InnerProductSpace ℂ (E₁ x) := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    let : InnerProductSpace ℂ (F₀ x) := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    let : InnerProductSpace ℂ (F₁ x) := InnerProductSpace.ofCore
      (inferInstance : PreInnerProductSpace.Core ℂ _)
    obtain ⟨hbij, hinverse⟩ := hbound ε' hεsmall x hx ξ hξ
    exact bijective_and_energy_bound_of_tensor_orthogonal_sum
      (e₀₀ x) (e₁₀ x) (e₀₁ x) (e₁₁ x) (ePlus x) (eMinus x)
      (k₀₀.toCore x) (k₁₀.toCore x) (k₀₁.toCore x) (k₁₁.toCore x)
      (kPlus.toCore x) (kMinus.toCore x)
      (hk₀₀ x) (hk₁₀ x) (hk₀₁ x) (hk₁₁ x) (hkPlus x) (hkMinus x)
      (reciprocalTensorSymbol (pf ε x ξ) (pi ε' x ξ) (qf ε x ξ) (qi ε' x ξ))
      (p ε' x ξ).toLinearMap (hp ε' x ξ)
      (1 + ‖covectorInChart (c i) x ξ‖) C (by positivity) hbij hinverse
  -- A single parameter now works in every native chart and every original native frame.
  obtain ⟨ε₀, hε₀, hell⟩ := exists_isEllipticFullGlobalSymbol_of_finite_metric_bounds
    Nplus Nminus g kPlus kMinus p' c hc L hL hLc hcover henergy
  refine ⟨min ε₀ 1, lt_min hε₀ zero_lt_one, min_le_right _ _, ?_⟩
  intro ε hεsmall
  have hh := hell ε.val ε.property.1 (hεsmall.trans (min_le_left _ _))
  simpa only [p', dite_eq_left ε.property] using hh

end AtiyahSinger
