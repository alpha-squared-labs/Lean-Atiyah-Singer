/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback

/-!
# Smooth pullback of the specified complex bundle map

Public module ID: M1376.

Pullback preserves the real smoothness of the original complex-linear bundle
map. The proof uses the native pulled frames and keeps their original fiber
norms and topology. In particular the result applies successively to a
cotangent projection and to open submanifolds, including noncompact exteriors.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n m r q : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

omit [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F] in
/-- A smooth complex-linear bundle map pulls back to the same fiber map in the native atlas. -/
theorem IsSmoothBundleMap.pullback {a : ∀ x, E x →ₗ[ℂ] F x}
    (ha : IsSmoothBundleMap (n := n) (r := r) (q := q) a)
    (f : C(N, M))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    IsSmoothBundleMap (n := m) (r := r) (q := q)
      (E := (f : N → M) *ᵖ E) (F := (f : N → M) *ᵖ F)
      (fun x ↦ a (f x)) := by
  -- The original matrix columns compose with the specified smooth base map.
  rintro _ ⟨e, he, rfl⟩ _ ⟨d, hd, rfl⟩ j
  let := he
  let := hd
  apply ((ha e d j).comp hf.contMDiffOn (fun _ hx ↦ hx)).congr
  intro x hx
  have heq : (e.pullback f).symmL ℂ x (EuclideanSpace.single j 1) =
      e.symmL ℂ (f x) (EuclideanSpace.single j 1) := by
    rw [(e.pullback f).symmL_apply (R := ℂ) hx.1,
      e.symmL_apply (R := ℂ) hx.1, (e.pullback f).symm_apply hx.1]
    rfl
  -- The native pullback frame evaluates the same original output vector.
  change (d ⟨f x, a (f x) ((e.pullback f).symmL ℂ x (EuclideanSpace.single j 1))⟩).2 = _
  rw [heq]
  rfl

end AtiyahSinger
