/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalDifferentialOperator
public import AtiyahSinger.Geometry.OpenSections

/-!
# Differential operators preserve prescribed closed supports

Public module ID: M0437.

D02: the standard support property of differential operators on the original
smooth section spaces. The support set is closed in the ambient manifold;
it need not be compact or have a regular boundary. Compact sets then supply
the test spaces used for formal adjunction on a noncompact base.

This is the usual locality consequence of the coordinate definition in
SG III.1. It introduces no new section model or bounded operator realization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.DifferentialOperator

open Bundle
open scoped Manifold ContDiff

variable {n r q d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

include hM hT hSC hE hF

/-- A differential operator sends sections supported in a closed set to the same support set. -/
theorem map_mem_supportedSmoothSections
    (P : DifferentialOperator (n := n) (r := r) (q := q) E F d)
    (K : Set M) (hK : IsClosed K)
    (s : supportedSmoothSections (n := n) (r := r) E K) :
    P.toLinearMap s.val ∈ supportedSmoothSections (n := n) (r := q) F K := by
  /- At a point outside K, its open complement is a neighborhood on which
  s is identically zero. The existing differential-operator locality theorem
  identifies the image germ with the image of the zero section. Linearity
  makes that image zero. This proves vanishing off the same K, including
  when K is empty. Closedness is essential for this neighborhood argument;
  the pointwise nonzero locus alone need not be preserved by differentiation. -/
  change ∀ x, x ∉ K → (P.toLinearMap s.val).val x = 0
  intro x hx
  -- Closedness makes the original vanishing condition hold on a whole neighborhood.
  have hzero : ∀ᶠ y in nhds x,
      s.val.val y = (0 : smoothSections (n := n) (r := r) E).val y := by
    filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
    exact s.property y hy
  -- Locality compares with the actual zero section; linearity finishes in the same fiber.
  calc
    (P.toLinearMap s.val).val x = (P.toLinearMap 0).val x :=
      P.apply_eq_of_eventually_eq s.val 0 x hzero
    _ = 0 := by
      rw [map_zero]
      rfl

end AtiyahSinger.DifferentialOperator
