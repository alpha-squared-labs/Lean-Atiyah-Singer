/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorTransport
public import AtiyahSinger.Analysis.EquivariantFullSymbolCovariance
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# The actual orbit formula for a weighted graded tensor symbol

Public module ID: M0517.

In fixed native source and target coordinates, conjugating a weighted graded
matrix transports only its two real weights when its four factor maps are
covariant. The same four moving-fiber equivalences and upper-right minus sign
are retained. This applies to full symbols, including both product axes;
no continuity or integrability of the auxiliary scalar weights is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40
set_option backward.isDefEq.respectTransparency false

variable {VG HG : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G] [IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (S T : SmoothFiniteComplexBundle (n := n) M)
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
    EquivariantStructure G S.Fiber)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
    EquivariantStructure G T.Fiber)
  {E₀ E₁ F₀ F₁ : M → Type}
  [∀ x, AddCommGroup (E₀ x)] [∀ x, Module ℂ (E₀ x)]
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℂ (E₁ x)]
  [∀ x, AddCommGroup (F₀ x)] [∀ x, Module ℂ (F₀ x)]
  [∀ x, AddCommGroup (F₁ x)] [∀ x, Module ℂ (F₁ x)]

set_option maxHeartbeats 1200000 in
-- Constant weights give fixed symbols; at the inverse orbit point use its actual two weights.
/-- Native conjugation preserves the four graded blocks and moves only their real weights. -/
theorem equivariantGlobalSymbolLinearMap_weighted_reciprocalTensor
    (i₀ : ∀ (g : G) (x : M), E₀ x ≃ₗ[ℂ] E₀ (g • x))
    (i₁ : ∀ (g : G) (x : M), E₁ x ≃ₗ[ℂ] E₁ (g • x))
    (j₀ : ∀ (g : G) (x : M), F₀ x ≃ₗ[ℂ] F₀ (g • x))
    (j₁ : ∀ (g : G) (x : M), F₁ x ≃ₗ[ℂ] F₁ (g • x))
    (e : ∀ x, ((E₀ x ⊗[ℂ] F₀ x) × (E₁ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] S.Fiber x)
    (f : ∀ x, ((E₁ x ⊗[ℂ] F₀ x) × (E₀ x ⊗[ℂ] F₁ x)) ≃ₗ[ℂ] T.Fiber x)
    (he : letI := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
      ∀ g x v, σ.linearMap g x (e x v) = e (g • x)
        (((TensorProduct.congr (i₀ g x) (j₀ g x)).prodCongr
          (TensorProduct.congr (i₁ g x) (j₁ g x))) v))
    (hf : letI := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
      ∀ g x v, τ.linearMap g x (f x v) = f (g • x)
        (((TensorProduct.congr (i₁ g x) (j₀ g x)).prodCongr
          (TensorProduct.congr (i₀ g x) (j₁ g x))) v))
    (p : ∀ x, CotangentFiber (n := n) x → E₀ x →ₗ[ℂ] E₁ x)
    (pi : ∀ x, CotangentFiber (n := n) x → E₁ x →ₗ[ℂ] E₀ x)
    (q : ∀ x, CotangentFiber (n := n) x → F₀ x →ₗ[ℂ] F₁ x)
    (qi : ∀ x, CotangentFiber (n := n) x → F₁ x →ₗ[ℂ] F₀ x)
    (hcov : ∀ g x ξ,
      let η := (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g) ⟨x, ξ⟩).snd
      (p (g • x) η).comp (i₀ g x).toLinearMap =
          (i₁ g x).toLinearMap.comp (p x ξ) ∧
      (pi (g • x) η).comp (i₁ g x).toLinearMap =
          (i₀ g x).toLinearMap.comp (pi x ξ) ∧
      (q (g • x) η).comp (j₀ g x).toLinearMap =
          (j₁ g x).toLinearMap.comp (q x ξ) ∧
      (qi (g • x) η).comp (j₁ g x).toLinearMap =
          (j₀ g x).toLinearMap.comp (qi x ξ))
    (a : GlobalSymbolFunction (n := n) S.Fiber T.Fiber)
    (α β : ∀ x, CotangentFiber (n := n) x → ℝ)
    (ha : ∀ x ξ v, a x ξ (e x v) = f x (reciprocalTensorSymbol
      ((α x ξ : ℂ) • p x ξ) ((α x ξ : ℂ) • pi x ξ)
      ((β x ξ : ℂ) • q x ξ) ((β x ξ : ℂ) • qi x ξ) v)) :
    ∀ g x ξ v,
      let η := (cotangentDiffeomorphMap
        (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm ⟨x, ξ⟩).snd
      equivariantGlobalSymbolLinearMap IG σ τ g a x ξ (e x v) =
        f x (reciprocalTensorSymbol
          ((α (g⁻¹ • x) η : ℂ) • p x ξ) ((α (g⁻¹ • x) η : ℂ) • pi x ξ)
          ((β (g⁻¹ • x) η : ℂ) • q x ξ) ((β (g⁻¹ • x) η : ℂ) • qi x ξ) v) := by
  let := modelTopology (EuclideanSpace ℂ (Fin S.rank)) S.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin T.rank)) T.Fiber
  let (x : M) : FiniteDimensional ℂ (S.Fiber x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin S.rank)) S.Fiber x
  let L (c d : ℝ) : GlobalSymbolFunction (n := n) S.Fiber T.Fiber := fun x ξ ↦
    LinearMap.toContinuousLinearMap ((f x).toLinearMap.comp ((reciprocalTensorSymbol
      ((c : ℂ) • p x ξ) ((c : ℂ) • pi x ξ)
      ((d : ℂ) • q x ξ) ((d : ℂ) • qi x ξ)).comp (e x).symm.toLinearMap))
  have hL (c d : ℝ) (x : M) (ξ : CotangentFiber (n := n) x) (v) :
      L c d x ξ (e x v) = f x (reciprocalTensorSymbol
        ((c : ℂ) • p x ξ) ((c : ℂ) • pi x ξ)
        ((d : ℂ) • q x ξ) ((d : ℂ) • qi x ξ) v) := by
    change f x (reciprocalTensorSymbol _ _ _ _ ((e x).symm (e x v))) = _
    rw [LinearEquiv.symm_apply_apply]
  have hconj {A B C D : Type}
      [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
      [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
      (i : A ≃ₗ[ℂ] C) (j : B ≃ₗ[ℂ] D) (u : A →ₗ[ℂ] B) (v : C →ₗ[ℂ] D)
      (h : v.comp i.toLinearMap = j.toLinearMap.comp u) (c : ℂ) :
      j.toLinearMap.comp ((c • u).comp i.symm.toLinearMap) = c • v := by
    ext w
    have hh := LinearMap.congr_fun h (i.symm w)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.smul_apply, map_smul] using
        congrArg (c • ·) hh.symm
  have hfixed (c d : ℝ) : ∀ g,
      equivariantGlobalSymbolLinearMap IG σ τ g (L c d) = L c d := by
    have hpoint := (equivariantGlobalSymbolLinearMap_eq_iff_forall IG σ τ (L c d)).mpr (by
      intro g x ξ v
      obtain ⟨v, rfl⟩ := (e x).surjective v
      rw [he, hL, hL, hf]
      apply congrArg (f (g • x))
      obtain ⟨hp, hpi, hq, hqi⟩ := hcov g x ξ
      have hh := reciprocalTensorSymbol_congr (i₀ g x) (i₁ g x) (j₀ g x) (j₁ g x)
        ((c : ℂ) • p x ξ) ((c : ℂ) • pi x ξ)
        ((d : ℂ) • q x ξ) ((d : ℂ) • qi x ξ)
      rw [hconj (i₀ g x) (i₁ g x) (p x ξ) _ hp (c : ℂ),
        hconj (i₁ g x) (i₀ g x) (pi x ξ) _ hpi (c : ℂ),
        hconj (j₀ g x) (j₁ g x) (q x ξ) _ hq (d : ℂ),
        hconj (j₁ g x) (j₀ g x) (qi x ξ) _ hqi (d : ℂ)] at hh
      exact (LinearMap.congr_fun hh v).symm)
    intro g
    funext x ξ
    exact hpoint g x ξ
  -- The full symbol and the constant-weight comparison agree in the actual inverse fiber.
  intro g x ξ v
  let η := (cotangentDiffeomorphMap
    (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g).symm ⟨x, ξ⟩).snd
  let c := α (g⁻¹ • x) η
  let d := β (g⁻¹ • x) η
  have hsame : a (g⁻¹ • x) η = L c d (g⁻¹ • x) η := by
    apply ContinuousLinearMap.ext
    intro w
    obtain ⟨w, rfl⟩ := (e (g⁻¹ • x)).surjective w
    exact (ha _ _ w).trans (hL c d _ _ w).symm
  have horbit : equivariantGlobalSymbolLinearMap IG σ τ g a x ξ =
      equivariantGlobalSymbolLinearMap IG σ τ g (L c d) x ξ := by
    dsimp only [η] at hsame
    simp only [equivariantGlobalSymbolLinearMap, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hsame]
  rw [horbit, hfixed c d g]
  exact hL c d x ξ v

end AtiyahSinger
