/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Smooth complex bundles over real manifolds

Public module ID: M1133.

D01: use complex-linear transition functions with real smoothness. The base model is
the full Euclidean space, which encodes absence of boundary. Hausdorffness, second
countability and compactness are hypotheses of the particular theorems that need them,
not new components of a project-specific notion of manifold.

This class is the ordinary transition-function definition, analogous to mathlib's
`ContMDiffVectorBundle`, with the two scalar roles separated. It imposes no index,
ellipticity, K-theory or analytic conclusion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type*) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, TopologicalSpace (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- A smooth complex vector bundle has real-smooth complex-linear transition functions. -/
class IsSmoothComplexBundle : Prop where
  /-- Real smoothness on each overlap of the specified complex-linear bundle atlas. -/
  contMDiffOn_coordChange :
    ∀ (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
        (π (EuclideanSpace ℂ (Fin r)) E))
      [MemTrivializationAtlas e] [MemTrivializationAtlas e'],
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ∞
        (fun x ↦ (e.coordChangeL ℂ e' x :
          EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)))
        (e.baseSet ∩ e'.baseSet)

/-- A section is smooth if its coordinates are real-smooth in every bundle chart. -/
def IsSmoothSection (s : ∀ x, E x) : Prop :=
  ∀ e : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E),
    MemTrivializationAtlas e →
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞
        (fun x ↦ (e ⟨x, s x⟩).2) e.baseSet

/-- The zero section is smooth in all complex-linear bundle charts. -/
theorem isSmoothSection_zero : IsSmoothSection (n := n) (r := r) E (fun _ ↦ 0) := by
  intro e he
  let := he
  -- Fiberwise linearity is used only on the chart domain.
  apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin r)))).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_zero

/-- Addition of sections is smooth, checked in the same linear charts. -/
theorem isSmoothSection_add (s t : ∀ x, E x)
    (hs : IsSmoothSection (n := n) (r := r) E s)
    (ht : IsSmoothSection (n := n) (r := r) E t) :
    IsSmoothSection (n := n) (r := r) E (s + t) := by
  intro e he
  let := he
  -- In each chart the sum has the sum of the two original smooth coordinates.
  apply ((hs e he).add (ht e he)).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_add (s x) (t x)

/-- Complex scalar multiplication preserves real smoothness of sections. -/
theorem isSmoothSection_smul (c : ℂ) (s : ∀ x, E x)
    (hs : IsSmoothSection (n := n) (r := r) E s) :
    IsSmoothSection (n := n) (r := r) E (c • s) := by
  intro e he
  let := he
  -- A fixed complex scalar acts real-smoothly on the model fiber.
  have hscale := ((c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))).restrictScalars
    ℝ).contMDiff (n := ∞)
  apply (hscale.comp_contMDiffOn (hs e he)).congr
  intro x hx
  exact (e.linearEquivAt ℂ x hx).map_smul c (s x)

/-- The standard complex vector space of smooth sections, as a submodule of all sections.
Closure follows from the three preceding smooth-section theorems. -/
def smoothSections : Submodule ℂ (∀ x, E x) where
  carrier := {s | IsSmoothSection (n := n) (r := r) E s}
  zero_mem' := isSmoothSection_zero E
  add_mem' := fun hs ht ↦ isSmoothSection_add E _ _ hs ht
  smul_mem' := fun c _ hs ↦ isSmoothSection_smul E c _ hs

end AtiyahSinger
