/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Analysis.HomogeneousSymbolAtInfinity
public import AtiyahSinger.Geometry.HermitianMetricAdjoint
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Radial extraction for the specified native reciprocal full symbol

Public module ID: M0912.

The two factor tails and the original positive metric pairings determine all
four matrix tails. The radial theorem is applied to the given full symbol
itself, preserving its exact exterior values and every regularized class.
This is the radial-extraction step for the specified associated cutoff construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff TensorProduct

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  (Nplus Nminus : SmoothFiniteComplexBundle (n := n) M)
  (E₀ E₁ F₀ F₁ : M → Type*)
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in

/-- The same reciprocal full symbol has its exact homogeneous elliptic exterior. -/
theorem specified_reciprocal_fullSymbol_homogeneous_call
    (c₀ : ∀ x, InnerProductSpace.Core ℂ (E₀ x))
    (c₁ : ∀ x, InnerProductSpace.Core ℂ (E₁ x))
    (d₀ : ∀ x, InnerProductSpace.Core ℂ (F₀ x))
    (d₁ : ∀ x, InnerProductSpace.Core ℂ (F₁ x))
    (e : ∀ x, ((E₀ x ⊗[ℂ] F₀ x) × (E₁ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] Nplus.Fiber x)
    (f : ∀ x, ((E₁ x ⊗[ℂ] F₀ x) × (E₀ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] Nminus.Fiber x)
    (p : ∀ x, CotangentFiber (n := n) x → E₀ x →ₗ[ℂ] E₁ x)
    (pi : ∀ x, CotangentFiber (n := n) x → E₁ x →ₗ[ℂ] E₀ x)
    (q : ∀ x, CotangentFiber (n := n) x → F₀ x →ₗ[ℂ] F₁ x)
    (qi : ∀ x, CotangentFiber (n := n) x → F₁ x →ₗ[ℂ] F₀ x)
    (hp : ∀ x ξ u v, (c₁ x).inner (p x ξ u) v = (c₀ x).inner u (pi x ξ v))
    (hq : ∀ x ξ u v, (d₁ x).inner (q x ξ u) v = (d₀ x).inner u (qi x ξ v))
    (qK : globalSymbolSpace (n := n) (r := Nplus.rank) (q := Nminus.rank)
      Nplus.Fiber Nminus.Fiber 1)
    (hK : ∀ x ξ w, qK.val x ξ (e x w) =
      f x (reciprocalTensorSymbol (p x ξ) (pi x ξ) (q x ξ) (qi x ξ) w))
    (g : SmoothCotangentMetric (n := n) (M := M)) (R : ℝ) (hR : 0 < R)
    (hpScale : ∀ x ξ (t : ℝ), 0 < t → R ≤ g.length x ξ →
      R ≤ g.length x (t • ξ) → p x (t • ξ) = (t : ℂ) • p x ξ)
    (hqScale : ∀ x ξ (t : ℝ), 0 < t → R ≤ g.length x ξ →
      R ≤ g.length x (t • ξ) → q x (t • ξ) = (t : ℂ) • q x ξ)
    (hbij : ∀ x ξ, R ≤ g.length x ξ →
      Function.Bijective (reciprocalTensorSymbol (p x ξ) (pi x ξ) (q x ξ) (qi x ξ))) :
    ∃ qKh : homogeneousGlobalSymbolSpace (n := n) (r := Nplus.rank) (q := Nminus.rank)
        Nplus.Fiber Nminus.Fiber 1,
      IsEllipticGlobalSymbol Nplus.Fiber Nminus.Fiber qKh.val ∧
      (∀ x ξ, R ≤ g.length x ξ → qKh.val x ξ = qK.val x ξ) ∧
      ∀ A : QuantizationPresentation (n := n) (r := Nplus.rank) (q := Nminus.rank)
          Nplus.Fiber Nminus.Fiber,
        globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1 qK =
          globalPrincipalSymbolClass Nplus.Fiber Nminus.Fiber 1
            (A.regularizedSymbol 1 qKh.val qKh.property.1 qKh.property.2) := by
  -- Positivity identifies the adjoints of the same real-scaled factor maps.
  have hpiScale (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
      (hξ : R ≤ g.length x ξ) (htξ : R ≤ g.length x (t • ξ)) :
      pi x (t • ξ) = (t : ℂ) • pi x ξ := by
    apply LinearMap.ext
    intro v
    have hzero (u : E₀ x) : (c₀ x).inner u
        (pi x (t • ξ) v - (t : ℂ) • pi x ξ v) = 0 := by
      rw [InnerProductSpace.Core.inner_sub_right, ← hp x (t • ξ) u v,
        hpScale x ξ t ht hξ htξ, LinearMap.smul_apply,
        InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
        ← hp x ξ u v]
      simp
    exact sub_eq_zero.mp ((c₀ x).definite _
      (hzero (pi x (t • ξ) v - (t : ℂ) • pi x ξ v)))
  have hqiScale (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
      (hξ : R ≤ g.length x ξ) (htξ : R ≤ g.length x (t • ξ)) :
      qi x (t • ξ) = (t : ℂ) • qi x ξ := by
    apply LinearMap.ext
    intro v
    have hzero (u : F₀ x) : (d₀ x).inner u
        (qi x (t • ξ) v - (t : ℂ) • qi x ξ v) = 0 := by
      rw [InnerProductSpace.Core.inner_sub_right, ← hq x (t • ξ) u v,
        hqScale x ξ t ht hξ htξ, LinearMap.smul_apply,
        InnerProductSpace.Core.inner_smul_left, InnerProductSpace.Core.inner_smul_right,
        ← hq x ξ u v]
      simp
    exact sub_eq_zero.mp ((d₀ x).definite _
      (hzero (qi x (t • ξ) v - (t : ℂ) • qi x ξ v)))
  -- Surjectivity of the fixed source sum transfers the four tails to this qK.
  have hscale (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
      (hξ : R ≤ g.length x ξ) (htξ : R ≤ g.length x (t • ξ)) :
      qK.val x (t • ξ) = (t : ℂ) • qK.val x ξ := by
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨w, rfl⟩ := (e x).surjective w
    change qK.val x (t • ξ) (e x w) = (t : ℂ) • qK.val x ξ (e x w)
    rw [hK, hK, ← map_smul]
    apply congrArg (f x)
    rw [hpScale x ξ t ht hξ htξ, hpiScale x ξ t ht hξ htξ,
      hqScale x ξ t ht hξ htξ, hqiScale x ξ t ht hξ htξ]
    simp only [reciprocalTensorSymbol, TensorProduct.map_smul_left,
      TensorProduct.map_smul_right, LinearMap.prod_apply, Function.prod_apply,
      LinearMap.coprod_apply, LinearMap.neg_apply, LinearMap.smul_apply,
      Prod.smul_mk, smul_add, smul_neg]
  have hqKbij (x : M) (ξ : CotangentFiber (n := n) x) (hξ : R ≤ g.length x ξ) :
      Function.Bijective (qK.val x ξ) := by
    have hmap : (qK.val x ξ : Nplus.Fiber x → Nminus.Fiber x) = f x ∘
        reciprocalTensorSymbol (p x ξ) (pi x ξ) (q x ξ) (qi x ξ) ∘ (e x).symm := by
      funext w
      obtain ⟨w, rfl⟩ := (e x).surjective w
      simpa only [Function.comp_apply, LinearEquiv.symm_apply_apply] using hK x ξ w
    rw [hmap]
    exact (f x).bijective.comp ((hbij x ξ hξ).comp (e x).symm.bijective)
  -- Extract radially from qK itself; the returned equality retains its actual exterior.
  exact exists_ellipticHomogeneousSymbol_of_degree_one_at_infinity
    qK g R hR hscale hqKbij

end AtiyahSinger
