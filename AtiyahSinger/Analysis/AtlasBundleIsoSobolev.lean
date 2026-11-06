/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleMapPseudodifferential
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Geometry.AtlasSectionEquiv

/-!
# Sobolev norm comparison for a specified smooth bundle isomorphism

Public module ID: M0229.

At every real order, the original section isomorphism compares the two
specified finite-atlas Sobolev norms in both directions. Multiplication by
the given fiber maps and their inverses is realized by order-zero PDOs.
This keeps the same maps when passing a cutoff estimate to a native metric
model, including the negative order needed before formal adjunction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option maxSynthPendingDepth 20 in
/-- The same smooth bundle isomorphism compares the original Sobolev norms at any real order. -/
theorem exists_atlasSmoothSectionEquiv_sobolev_comparison
    (A : SmoothComplexBundleAtlas (n := n) E)
    (B : SmoothComplexBundleAtlas (n := n) F) (e : Iso E F)
    (he : IsSmoothAtlasBundleMap A B e.toHom.linearMap)
    (hi : IsSmoothAtlasBundleMap B A e.symm.toHom.linearMap)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.smoothSections,
      ‖K.smoothToSobolev s (atlasSmoothSectionEquiv A B e he hi u)‖ ≤
        C * ‖L.smoothToSobolev s u‖ ∧
      ‖L.smoothToSobolev s u‖ ≤
        C * ‖K.smoothToSobolev s (atlasSmoothSectionEquiv A B e he hi u)‖ := by
  let S := atlasSmoothSectionEquiv A B e he hi
  -- The two order-zero operators multiply by these exact inverse fiber maps.
  obtain ⟨_, P, hP, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap A B e.toHom.linearMap he
  obtain ⟨_, Q, hQ, _⟩ :=
    exists_atlasPseudodifferentialOperator_bundleMap B A e.symm.toHom.linearMap hi
  let R := P.sobolevExtension L K s
  let T := Q.sobolevExtension K L s
  have hforward (u : A.smoothSections) :
      ‖K.smoothToSobolev s (S u)‖ ≤ ‖R‖ * ‖L.smoothToSobolev s u‖ := by
    have h := R.le_opNorm (L.smoothToSobolev s u)
    rw [P.sobolevExtension_smoothToSobolev L K s, hP] at h
    have horder := congrArg (fun t : ℝ ↦ ‖K.smoothToSobolev t (S u)‖) (sub_zero s)
    exact horder.symm.trans_le h
  have hbackward (v : B.smoothSections) :
      ‖L.smoothToSobolev s (S.symm v)‖ ≤ ‖T‖ * ‖K.smoothToSobolev s v‖ := by
    have h := T.le_opNorm (K.smoothToSobolev s v)
    rw [Q.sobolevExtension_smoothToSobolev K L s, hQ] at h
    have horder := congrArg (fun t : ℝ ↦ ‖L.smoothToSobolev t (S.symm v)‖) (sub_zero s)
    exact horder.symm.trans_le h
  -- Apply the reverse bound to the image of the same section, using the actual inverse.
  refine ⟨max ‖R‖ ‖T‖, (norm_nonneg R).trans (le_max_left _ _), ?_⟩
  intro u
  constructor
  · exact (hforward u).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  · have h := hbackward (S u)
    rw [S.symm_apply_apply] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

end AtiyahSinger
