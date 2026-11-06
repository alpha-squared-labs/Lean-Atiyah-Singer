/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexConnection

/-!
# Affine paths of smooth complex connections

Public module ID: M1140.

E01: use mathlib's actual affine combination of the two specified covariant
derivatives. Its real parameter runs over the entire real line, and its
restriction to the unit interval joins the original endpoints. Smoothness
on the base uses the native connection predicate; parameter smoothness is
asserted after evaluation on each fixed section, base point and tangent
vector. No connection on the product manifold is constructed here.

If the original connections agree on differentiable section germs along a
set, the whole path keeps that same germwise action there. No equality on
arbitrary nondifferentiable sections is inferred from that premise.
This is the standard affine-space property of complex connections, used to
compare the auxiliary choices in SG Chapter II and III.13.3. The explicit
native-formulation and the relative preservation assertion are project
supplements; they are not separately numbered claims attributed to SG.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hM hE

set_option linter.unusedSectionVars false in
/-- The native affine path joins the same smooth complex connections and preserves their
common action on differentiable section germs wherever that action is specified. -/
theorem complexConnection_affine_path
    (cov₀ cov₁ : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℂ (Fin r)) E)
    (hc₀ : IsComplexLinearConnectionOn (n := n) (r := r) E cov₀)
    (hc₁ : IsComplexLinearConnectionOn (n := n) (r := r) E cov₁)
    (hs₀ : CovariantDerivative.ContMDiffCovariantDerivative cov₀ ∞)
    (hs₁ : CovariantDerivative.ContMDiffCovariantDerivative cov₁ ∞) :
    let path := fun t : ℝ ↦ CovariantDerivative.affineCombination cov₁ cov₀ (fun _ ↦ t)
    path 0 = cov₀ ∧ path 1 = cov₁ ∧
      (∀ t : ℝ, IsComplexLinearConnectionOn (n := n) (r := r) E (path t) ∧
        CovariantDerivative.ContMDiffCovariantDerivative (path t) ∞) ∧
      (∀ (σ : ∀ x : M, E x) (x : M)
        (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          ContDiff ℝ ∞ (fun t : ℝ ↦ path t σ x v)) ∧
      ∀ (A : Set M),
        (∀ (σ : ∀ x : M, E x) (x : M), x ∈ A →
          MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r)))
            (fun y ↦ (⟨y, σ y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x →
          cov₁ σ x = cov₀ σ x) →
        ∀ (t : ℝ) (σ : ∀ x : M, E x) (x : M), x ∈ A →
          MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            (𝓘(ℝ, EuclideanSpace ℝ (Fin n)).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r)))
            (fun y ↦ (⟨y, σ y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x →
          path t σ x = cov₀ σ x := by
  /- Stage 1: use the native affineCombination, whose actual action is
  t times cov₁ plus (1-t) times cov₀. At t=0 and t=1 the function formulas
  reduce to the original covariant derivatives; their proof fields agree
  by proof irrelevance. This fixes the orientation of the path explicitly.
  Stage 2: complex scalar multiplication commutes with the real weights,
  so the two given complex-linearity identities give complex compatibility
  for every t on the original differentiable section germs. Apply native
  ContMDiffCovariantDerivative.affineCombination to the constant smooth
  weight function to retain smoothness on the same real base manifold.
  Stage 3: for a fixed section, point and tangent vector, the displayed
  derivative value is affine in t, hence smooth in t. This fact needs no
  regularity of that section and asserts no product-manifold connection.
  Stage 4: at a point of A and on a differentiable germ, replace cov₁ by
  the specified common value cov₀. The real coefficients add to one, so
  the affine combination retains that same value for every t. The premise
  is germwise equality only; closure or compactness of A is not required
  for this preservation statement once both connections are supplied. -/
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- At zero only the original initial connection remains.
    ext σ x v
    simp [CovariantDerivative.affineCombination]
  · -- At one only the original terminal connection remains.
    ext σ x v
    simp [CovariantDerivative.affineCombination]
  · intro t
    constructor
    · intro σ x hσ hx z v
      change t • cov₁ (fun y ↦ z • σ y) x v +
          (1 - t) • cov₀ (fun y ↦ z • σ y) x v =
        z • (t • cov₁ σ x v + (1 - t) • cov₀ σ x v)
      rw [hc₁ σ x hσ hx z v, hc₀ σ x hσ hx z v]
      simp only [smul_add, smul_comm t z, smul_comm (1 - t) z]
    · exact CovariantDerivative.ContMDiffCovariantDerivative.affineCombination
        cov₁ cov₀ contMDiff_const hs₁ hs₀
  · intro σ x v
    -- Parameter smoothness follows from this actual affine formula, even for a raw section.
    change ContDiff ℝ ∞ (fun t : ℝ ↦ t • cov₁ σ x v + (1 - t) • cov₀ σ x v)
    exact (contDiff_id.smul contDiff_const).add
      ((contDiff_const.sub contDiff_id).smul contDiff_const)
  · intro A hA t σ x hx hσ
    -- Only the stipulated differentiable germ is used in this relative identity.
    change t • cov₁ σ x + (1 - t) • cov₀ σ x = cov₀ σ x
    rw [hA σ x hx hσ, ← add_smul]
    simp

end AtiyahSinger
