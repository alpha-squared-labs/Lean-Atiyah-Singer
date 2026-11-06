/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.OpenSections

/-!
# Smooth pullback bundles with the original fiber norms

Public module ID: M1382.

D01/E01: smooth pullback of the existing real-smooth complex vector bundles.
The norm and atlas instances are implementation adapters: each retains the original
fiber structure or the native mathlib pullback atlas. They retain the native pullback topology,
choose no new metric, and do not constitute new mathematical definitions.
The smoothness theorem uses mathlib's native pulled-back bundle atlas.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

namespace ComplexBundle

/-- Retain exactly the normed additive structure of the original fiber under pullback. -/
@[reducible]
instance pullbackNormedAddCommGroup {X Y : Type*} (f : X → Y)
    (E : Y → Type*) [∀ y, NormedAddCommGroup (E y)] (x : X) :
    NormedAddCommGroup ((f *ᵖ E) x) :=
  inferInstanceAs (NormedAddCommGroup (E (f x)))

/-- Retain the original complex normed-space structure, with no new norm choice. -/
@[reducible]
instance pullbackNormedSpace {X Y : Type*} (f : X → Y)
    (E : Y → Type*) [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)] (x : X) :
    NormedSpace ℂ ((f *ᵖ E) x) :=
  inferInstanceAs (NormedSpace ℂ (E (f x)))

/-- Use the native pullback atlas with the topology inherited from the original fiber norms. -/
instance pullbackFiberBundleOfNormed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {r : ℕ} (f : C(X, Y))
    (E : Y → Type*) [∀ y, NormedAddCommGroup (E y)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E] :
    @FiberBundle X (EuclideanSpace ℂ (Fin r)) _ _ ((f : X → Y) *ᵖ E) _
      (fun x ↦
        (pullbackNormedAddCommGroup (f : X → Y) E x).toUniformSpace.toTopologicalSpace) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

/-- The same native linear atlas, with the norm-derived algebra and topology made explicit. -/
instance pullbackVectorBundleOfNormed {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {r : ℕ} (f : C(X, Y))
    (E : Y → Type*) [∀ y, NormedAddCommGroup (E y)] [∀ y, NormedSpace ℂ (E y)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
    [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E] :
    @VectorBundle ℂ X (EuclideanSpace ℂ (Fin r)) ((f : X → Y) *ᵖ E) _
      (fun x ↦ (pullbackNormedAddCommGroup (f : X → Y) E x).toAddCommMonoid)
      (fun x ↦ (pullbackNormedSpace (f : X → Y) E x).toModule) _ _ _ _
      (fun x ↦
        (pullbackNormedAddCommGroup (f : X → Y) E x).toUniformSpace.toTopologicalSpace)
      (pullbackFiberBundleOfNormed f E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

end ComplexBundle

variable {n m r : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
  (E : M → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hN : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]

include hE hM hN

set_option linter.unusedSectionVars false in
/-- Smooth pullback preserves real-smooth complex-linear transition functions. -/
theorem isSmoothComplexBundle_pullback (f : C(N, M))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    IsSmoothComplexBundle (n := m) (r := r) ((f : N → M) *ᵖ E) := by
  /- Each chart in the native pullback atlas comes from an original chart.
  On a pair of pullback chart bases its coordinate change is the original
  complex-linear coordinate change composed with f. Smooth composition on the
  inverse-image overlap proves the required real smoothness. No compactness,
  properness, or invertibility of the base map is needed. -/
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  let := he
  let := he'
  -- Compose the original real-smooth complex coordinate-change family with f.
  refine ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) e e').comp
    hf.contMDiffOn (fun x hx ↦ hx)).congr ?_
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  -- The native pulled-back chart acts on the same original fiber vector.
  change ((e.pullback f).coordChangeL ℂ (e'.pullback f) x) v =
    (e.coordChangeL ℂ e' (f x)) v
  rw [e.coordChangeL_apply e' hx, (e.pullback f).coordChangeL_apply' _]
  · rfl
  · exact hx

end AtiyahSinger
