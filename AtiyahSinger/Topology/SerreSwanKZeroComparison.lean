/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKZero
public import AtiyahSinger.Topology.ProjectiveKZero

/-!
# Serre-Swan compatibility with the original K₀ classes

Public module ID: M2116.

The class of the actual continuous section module equals the original geometric
bundle class. Both constructions use the existing idempotent quotient; the
comparison identifies their presentations without replacing either definition.
Fibers may lie in an independent universe and their local ranks may vary.

Sources: Karoubi, K-Theory, I.6.17--6.18 and I.6.16; Spin Geometry I.9.
Karoubi writes sections as right modules. Here C(X,ℂ) is commutative and the
existing section module uses its specified left action. The same action can be
written on the right by s·f = f·s; no independently supplied right action is
identified with it. The existing same-matrix K₀ comparison handles that change
of convention, and does not alter the matrix presenting the section module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u v

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] sectionModule

/-- Taking actual continuous sections preserves the original geometric K₀ class. -/
theorem projectiveModuleKZeroClass_continuousSections :
    letI : Module.Finite C(X, ℂ) (continuousSections E) := finite_continuousSections E
    letI : Module.Projective C(X, ℂ) (continuousSections E) :=
      projective_continuousSections E
    AtiyahSinger.projectiveModuleKZeroClass C(X, ℂ) (continuousSections E) =
      kZeroClass E := by
  /- Stage 1: take the original idempotentPresentation of E, not a newly chosen
  geometric representative. The existing presentation_sections identifies Γ(E)
  with the image of this same matrix over C(X,ℂ).
  Stage 2: the projective-module class is invariant under this actual linear
  equivalence. Its image formula therefore gives the matrix class of that
  presentation, which is exactly the defining geometric kZeroClass E.
  No constant rank, chosen basis, connectedness or nonempty base is needed. -/
  let : Module.Finite C(X, ℂ) (continuousSections E) := finite_continuousSections E
  let : Module.Projective C(X, ℂ) (continuousSections E) := projective_continuousSections E
  let p := idempotentPresentation (E := E)
  let : Module.Finite C(X, ℂ) p.image := p.finite_image
  let : Module.Projective C(X, ℂ) p.image := p.projective_image
  obtain ⟨e⟩ := presentation_sections (E := E)
  -- The section equivalence identifies the original presentation, not a replacement matrix.
  exact (projectiveModuleKZeroClass_eq_of_linearEquiv e).trans
    (projectiveModuleKZeroClass_image p)

end AtiyahSinger.ComplexBundle
