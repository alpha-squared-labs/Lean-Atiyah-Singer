/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.HermitianCoreTensorSymbol
public import AtiyahSinger.Topology.EquivariantBundleAffineHomotopy

/-!
# Equivariant homotopy of the original graded cutoff boundaries

Public module ID: M1785.

The exact affine path from the uncut Hermitian matrix to a weighted cutoff
matrix is invertible on the same compact invariant exterior whenever one
invertible factor retains coefficient one. The two original equivariant
boundary isomorphisms supply joint continuity and the actual fixed actions.
Arbitrary native Hermitian cores are retained; no fiber norm is replaced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle ComplexBundle
open scoped TensorProduct unitInterval

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {S T : X → Type*}
  [∀ x, AddCommGroup (S x)] [∀ x, Module ℂ (S x)]
  [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S]
  [∀ x, AddCommGroup (T x)] [∀ x, Module ℂ (T x)]
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

set_option maxHeartbeats 800000 in
-- Four dependent tensor fibers and both actual native boundary maps remain fixed.
/-- Dominant-weight saturation gives an equivariant homotopy of the actual graded maps. -/
theorem CompactSupportTriple.equivariantlyHomotopic_of_weightedGradedTensor
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
    (α β : (Kᶜ : Set X) → ℝ)
    (hA : ∀ (x : (Kᶜ : Set X)) v,
      (a.enlarge K hK ha).boundary.linearEquiv x (e x.val v) =
        f x.val (reciprocalTensorSymbol (p x.val) (pi x.val) (q x.val) (qi x.val) v))
    (hB : ∀ (x : (Kᶜ : Set X)) v,
      (b.enlarge K hK hb).boundary.linearEquiv x (e x.val v) =
        f x.val (reciprocalTensorSymbol
          ((α x : ℂ) • p x.val) ((α x : ℂ) • pi x.val)
          ((β x : ℂ) • q x.val) ((β x : ℂ) • qi x.val) v))
    (hdominant : ∀ (x : (Kᶜ : Set X)),
      (α x = 1 ∧ Function.Bijective (p x.val)) ∨
        (β x = 1 ∧ Function.Bijective (q x.val))) :
    a.EquivariantlyHomotopic b ρS ρT := by
  apply a.equivariantlyHomotopic_of_affine b ρS ρT hEA hEB K hK hInv ha hb
  intro t x
  let γ : ℝ := (1 - (t : ℝ)) + (t : ℝ) * α x
  let δ : ℝ := (1 - (t : ℝ)) + (t : ℝ) * β x
  let L := reciprocalTensorSymbol ((γ : ℂ) • p x.val) ((γ : ℂ) • pi x.val)
    ((δ : ℂ) • q x.val) ((δ : ℂ) • qi x.val)
  -- The dominant coefficient is exactly one for every time, even for signed atlas weights.
  have hL : Function.Bijective L := by
    apply reciprocalTensorSymbol_bijective_of_hermitian_adjoint
      (h₀ x.val) (h₁ x.val) (k₀ x.val) (k₁ x.val)
      (p x.val) (pi x.val) (q x.val) (qi x.val) (hp x.val) (hq x.val)
    rcases hdominant x with h | h
    · left
      refine ⟨?_, h.2⟩
      simp [γ, h.1]
    · right
      refine ⟨?_, h.2⟩
      simp [δ, h.1]
  have hweights (v : (E₀ x.val ⊗[ℂ] F₀ x.val) × (E₁ x.val ⊗[ℂ] F₁ x.val)) :
      (1 - (t : ℂ)) • reciprocalTensorSymbol (p x.val) (pi x.val) (q x.val) (qi x.val) v +
        (t : ℂ) • reciprocalTensorSymbol
          ((α x : ℂ) • p x.val) ((α x : ℂ) • pi x.val)
          ((β x : ℂ) • q x.val) ((β x : ℂ) • qi x.val) v =
          L v := by
    let u₀ := TensorProduct.map (p x.val) (LinearMap.id : F₀ x.val →ₗ[ℂ] F₀ x.val) v.1
    let u₁ := TensorProduct.map (LinearMap.id : E₁ x.val →ₗ[ℂ] E₁ x.val)
      (qi x.val) v.2
    let v₀ := TensorProduct.map (LinearMap.id : E₀ x.val →ₗ[ℂ] E₀ x.val) (q x.val) v.1
    let v₁ := TensorProduct.map (pi x.val) (LinearMap.id : F₁ x.val →ₗ[ℂ] F₁ x.val) v.2
    simp only [L, reciprocalTensorSymbol,
      TensorProduct.map_smul_left, TensorProduct.map_smul_right]
    change (1 - (t : ℂ)) • (u₀ + -u₁, v₀ + v₁) +
      (t : ℂ) • ((α x : ℂ) • u₀ + -((β x : ℂ) • u₁),
        (β x : ℂ) • v₀ + (α x : ℂ) • v₁) =
      ((γ : ℂ) • u₀ + -((δ : ℂ) • u₁), (δ : ℂ) • v₀ + (γ : ℂ) • v₁)
    apply Prod.ext
    · change (1 - (t : ℂ)) • (u₀ + -u₁) +
        (t : ℂ) • ((α x : ℂ) • u₀ + -((β x : ℂ) • u₁)) =
          (γ : ℂ) • u₀ + -((δ : ℂ) • u₁)
      simp only [γ, δ, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one]
      module
    · change (1 - (t : ℂ)) • (v₀ + v₁) +
        (t : ℂ) • ((β x : ℂ) • v₀ + (α x : ℂ) • v₁) =
          (δ : ℂ) • v₀ + (γ : ℂ) • v₁
      simp only [γ, δ, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one]
      module
  -- Compare the complete boundary maps through the same original fiber identifications.
  have hpath :
      (1 - (t : ℂ)) • ((a.enlarge K hK ha).boundary.linearEquiv x).toLinearMap +
        (t : ℂ) • ((b.enlarge K hK hb).boundary.linearEquiv x).toLinearMap =
      (f x.val).toLinearMap.comp (L.comp (e x.val).symm.toLinearMap) := by
    apply LinearMap.ext
    intro v
    obtain ⟨v, rfl⟩ := (e x.val).surjective v
    change (1 - (t : ℂ)) • (a.enlarge K hK ha).boundary.linearEquiv x (e x.val v) +
      (t : ℂ) • (b.enlarge K hK hb).boundary.linearEquiv x (e x.val v) =
        f x.val (L ((e x.val).symm (e x.val v)))
    rw [(e x.val).symm_apply_apply, hA, hB]
    simpa only [map_add, map_smul] using congrArg (f x.val) (hweights v)
  rw [hpath]
  exact (f x.val).bijective.comp (hL.comp (e x.val).symm.bijective)

end AtiyahSinger.ComplexBundle
