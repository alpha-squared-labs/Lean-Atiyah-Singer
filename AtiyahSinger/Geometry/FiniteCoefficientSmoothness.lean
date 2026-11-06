/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Smoothness detected by separating finite-dimensional coefficients

Public module ID: M1233.

A separating family of linear forms detects smoothness of a map to a finite
complex vector space. The family of forms may be infinite: it spans the dual,
and every coordinate is a finite linear combination of its members. No
continuity of the original map is assumed in advance.

This standard finite-dimensional fact is used to recover smooth coefficients
of an actual finite kernel family from its smooth evaluations along the fiber.
It does not assert weak smoothness implies smoothness in infinite dimension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Manifold ContDiff

variable {E H M I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (IM : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} {s : Set M}

/-- Separating linear coefficients detect smoothness in a finite complex coordinate space. -/
theorem contMDiffOn_of_separating_linearForms
    (L : I → (Fin k → ℂ) →ₗ[ℂ] ℂ)
    (hL : ∀ v : Fin k → ℂ, (∀ i : I, L i v = 0) → v = 0)
    (f : M → Fin k → ℂ)
    (hf : ∀ i : I, ContMDiffOn IM 𝓘(ℝ, ℂ) ∞ (fun x ↦ L i (f x)) s) :
    ContMDiffOn IM 𝓘(ℝ, Fin k → ℂ) ∞ f s := by
  -- Separation makes every coordinate a member of the span of the given forms.
  have hspan (j : Fin k) : (LinearMap.proj j : (Fin k → ℂ) →ₗ[ℂ] ℂ) ∈
      Submodule.span ℂ (Set.range L) := by
    apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
    intro v hv
    have hz : v = 0 := hL v (fun i ↦ (Submodule.mem_iInf _).mp hv i)
    rw [hz]
    exact map_zero _
  -- Span induction uses only finite sums and scalar multiplication of smooth functions.
  have hs (φ : (Fin k → ℂ) →ₗ[ℂ] ℂ) (hφ : φ ∈ Submodule.span ℂ (Set.range L)) :
      ContMDiffOn IM 𝓘(ℝ, ℂ) ∞ (fun x ↦ φ (f x)) s := by
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨i, rfl⟩ := hφ
      exact hf i
    | zero => exact contMDiffOn_const
    | add φ ψ _ _ hφ hψ =>
      have hadd : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 + z.2) := contDiff_add
      exact hadd.contMDiff.comp_contMDiffOn (hφ.prodMk_space hψ)
    | smul c φ _ hφ =>
      have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2) := contDiff_mul
      exact hmul.contMDiff.comp_contMDiffOn (contMDiffOn_const.prodMk_space hφ)
  apply contMDiffOn_pi_space.mpr
  intro j
  exact hs (LinearMap.proj j) (hspan j)

end AtiyahSinger
