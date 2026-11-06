/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Smooth section equivalence for specified bundle atlases

Public module ID: M1102.

A bundle isomorphism smooth in both prescribed atlases acts on their actual
section spaces. The inverse is the original inverse fiber map. This comparison
does not replace either atlas by an independently chosen smooth structure and
allows locally varying ranks. It supplies the section conjugation needed when
expressing an atlas PDO in a compatible native model (SG III.1).
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

/-- The given smooth fiber isomorphism identifies the two original atlas section spaces. -/
def atlasSmoothSectionEquiv
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F) (e : Iso E F)
    (he : IsSmoothAtlasBundleMap A B e.toHom.linearMap)
    (hi : IsSmoothAtlasBundleMap B A e.symm.toHom.linearMap) :
    A.smoothSections ≃ₗ[ℂ] B.smoothSections where
  toLinearMap := atlasSmoothSectionMap A B e.toHom.linearMap he
  invFun := atlasSmoothSectionMap B A e.symm.toHom.linearMap hi
  left_inv u := by
    apply Subtype.ext
    funext x
    exact (e.linearEquiv x).symm_apply_apply (u.val x)
  right_inv u := by
    apply Subtype.ext
    funext x
    exact (e.linearEquiv x).apply_symm_apply (u.val x)

end AtiyahSinger
