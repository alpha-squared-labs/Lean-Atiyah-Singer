/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Topology.AssociatedTrivialAction

/-!
# The smooth product identification for a trivial associated sphere action

Public module ID: M1081.

The original quotient product homeomorphism agrees on every principal chart
with the original associated trivialization. Both directions are therefore
smooth for the original selected associated atlas. This retains the exact
pair formula and provides the geometric product comparison required in the
zero-rank case, without identifying different smooth atlases by assertion.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)

set_option maxSynthPendingDepth 40 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Trivial sphere action identifies the original smooth associated bundle with the product. -/
theorem exists_associatedSphere_productDiffeomorph_of_trivial_action
    (hact : ∀ (g : G) (y : OrthogonalSphere r), g • y = y) :
    letI := associatedSphereChartedSpace S
    ∃ e : Z ≃ₘ⟮𝓘(ℝ, X × Y), (𝓡 n).prod (𝓡 r)⟯ (B × OrthogonalSphere r),
      ∀ (p : P) (y : OrthogonalSphere r),
        e (associatedBundleMk G P (OrthogonalSphere r) p y) = (projection p, y) := by
  classical
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  obtain ⟨e, he⟩ := exists_associatedBundle_homeomorph_of_trivial_action
    S.toIsPrincipalBundle hact
  let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let t (b : B) := associatedSphereTrivialization S b
  have htbase (b : B) : (t b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have heq (b : B) (z : Z) (hz : z ∈ (t b).source) : e z = t b z := by
    induction z using Quotient.inductionOn with
    | h v =>
      have hv : projection v.1 ∈ (S.trivialization b).baseSet :=
        htbase b ▸ (t b).mem_source.mp hz
      have hformula := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.1 v.1 v.2 hv
      have hchart : t b (associatedBundleMk G P (OrthogonalSphere r) v.1 v.2) =
          (projection v.1, v.2) := by
        simpa only [t, associatedSphereTrivialization, hact] using hformula
      exact (he v.1 v.2).trans hchart.symm
  have hinv (b : B) (w : B × OrthogonalSphere r) (hw : w ∈ (t b).target) :
      e.symm w = (t b).toOpenPartialHomeomorph.symm w := by
    apply e.injective
    rw [e.apply_symm_apply, heq b _ ((t b).map_target hw)]
    exact ((t b).toOpenPartialHomeomorph.right_inv hw).symm
  -- Every original point has a neighborhood on which the global map is its original chart.
  have hsmooth : ContMDiff 𝓘(ℝ, X × Y) ((𝓡 n).prod (𝓡 r)) ∞ e := by
    intro z
    let b := base z
    have hz : z ∈ (t b).source :=
      (t b).mem_source.mpr ((htbase b).symm ▸ S.mem_baseSet b)
    have hlocal := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have h : ContMDiffOn 𝓘(ℝ, X × Y) ((𝓡 n).prod (𝓡 r)) ∞ e (t b).source :=
      hlocal.1.congr (fun w hw ↦ heq b w hw)
    exact h.contMDiffAt ((t b).open_source.mem_nhds hz)
  have hsmoothInv : ContMDiff ((𝓡 n).prod (𝓡 r)) 𝓘(ℝ, X × Y) ∞ e.symm := by
    intro w
    let b := w.1
    have hw : w ∈ (t b).target :=
      (t b).mem_target.mpr ((htbase b).symm ▸ S.mem_baseSet b)
    have hlocal := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have h : ContMDiffOn ((𝓡 n).prod (𝓡 r)) 𝓘(ℝ, X × Y) ∞ e.symm (t b).target :=
      hlocal.2.congr (fun z hz ↦ hinv b z hz)
    exact h.contMDiffAt ((t b).open_target.mem_nhds hw)
  exact ⟨{ e with contMDiff_toFun := hsmooth, contMDiff_invFun := hsmoothInv }, he⟩

end AtiyahSinger
