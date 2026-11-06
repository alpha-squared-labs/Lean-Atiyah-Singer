/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereBundle
public import AtiyahSinger.Topology.AssociatedGaugeProduct

/-!
# Product coordinates for an associated sphere over a discrete base

Public module ID: M1075.

The original principal chart selected at each base point gives a continuous
right-equivariant gauge. On that singleton base neighborhood the induced
quotient map is exactly the original associated trivialization, so both
directions are smooth for the original associated atlas. No connectedness,
nonempty base, fixed bundle rank or trivial structure-group action is required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set Topology
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [DiscreteTopology B]
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
/-- Original principal coordinates trivialize the smooth associated sphere over a discrete base. -/
theorem exists_associatedSphere_productDiffeomorph_of_discreteTopology :
    letI := associatedSphereChartedSpace S
    ∃ (θ : C(P, G)),
      (∀ (p : P) (g : G), θ (MulOpposite.op g • p) = θ p * g) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℝ, X × Y), (𝓡 n).prod (𝓡 r)⟯ (B × OrthogonalSphere r),
        ∀ (p : P) (y : OrthogonalSphere r),
          e (associatedBundleMk G P (OrthogonalSphere r) p y) =
            (projection p, θ p • y) := by
  classical
  let := associatedSphereChartedSpace S
  let := associatedSphereIsManifold S
  -- The base coordinate is locally constant, so the selected chart varies locally constantly.
  let θfun (p : P) : G := (S.trivialization (projection p) p).2
  have hcθ : Continuous θfun := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hp : p ∈ (S.trivialization (projection p)).source :=
      (S.trivialization (projection p)).mem_source.mpr (S.mem_baseSet (projection p))
    have ht := ((S.trivialization (projection p)).continuousAt hp).snd
    apply ht.congr_of_eventuallyEq
    have hb := S.toIsPrincipalBundle.projection_properties.1.continuousAt.preimage_mem_nhds
      ((isOpen_discrete ({projection p} : Set B)).mem_nhds (Set.mem_singleton _))
    filter_upwards [hb] with q hq
    change projection q = projection p at hq
    simp only [θfun, hq]
    rfl
  let θ : C(P, G) := ⟨θfun, hcθ⟩
  have hθ (p : P) (g : G) : θ (MulOpposite.op g • p) = θ p * g := by
    change (S.trivialization (projection (MulOpposite.op g • p))
      (MulOpposite.op g • p)).2 = (S.trivialization (projection p) p).2 * g
    rw [S.projection_smul]
    exact S.equivariant (projection p) g p (S.mem_baseSet (projection p))
  obtain ⟨e, he⟩ := exists_associatedBundle_productHomeomorph_of_gauge
    («Y» := OrthogonalSphere r) S.toIsPrincipalBundle θ hθ
  let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let t (b : B) := associatedSphereTrivialization S b
  have htbase (b : B) : (t b).baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have heq (b : B) (z : Z) (hz : base z = b) : e z = t b z := by
    induction z using Quotient.inductionOn with
    | h v =>
      change projection v.1 = b at hz
      have hv : projection v.1 ∈ (S.trivialization b).baseSet := hz ▸ S.mem_baseSet b
      have hformula := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.1 v.1 v.2 hv
      change e (associatedBundleMk G P (OrthogonalSphere r) v.1 v.2) =
        t b (associatedBundleMk G P (OrthogonalSphere r) v.1 v.2)
      rw [he]
      simpa only [θ, θfun, ContinuousMap.coe_mk, hz, t, associatedSphereTrivialization] using
        hformula.symm
  have hinv (b : B) (w : B × OrthogonalSphere r) (hw : w.1 = b) :
      e.symm w = (t b).toOpenPartialHomeomorph.symm w := by
    have htarg : w ∈ (t b).target :=
      (t b).mem_target.mpr ((htbase b).symm ▸ (hw ▸ S.mem_baseSet b))
    apply e.injective
    rw [e.apply_symm_apply, heq b _ (((t b).coe_fst ((t b).map_target htarg)).symm.trans
      ((congrArg Prod.fst ((t b).toOpenPartialHomeomorph.right_inv htarg)).trans hw))]
    exact ((t b).toOpenPartialHomeomorph.right_inv htarg).symm
  -- Both maps agree with an original smooth chart on the same open singleton fiber.
  have hsmooth : ContMDiff 𝓘(ℝ, X × Y) ((𝓡 n).prod (𝓡 r)) ∞ e := by
    intro z
    let b := base z
    have hz : z ∈ (t b).source :=
      (t b).mem_source.mpr ((htbase b).symm ▸ S.mem_baseSet b)
    have hlocal := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have h := hlocal.1.contMDiffAt ((t b).open_source.mem_nhds hz)
    apply h.congr_of_eventuallyEq
    have hb := base.continuous.continuousAt.preimage_mem_nhds
      ((isOpen_discrete ({b} : Set B)).mem_nhds (Set.mem_singleton _))
    filter_upwards [hb] with w hw
    exact heq b w hw
  have hsmoothInv : ContMDiff ((𝓡 n).prod (𝓡 r)) 𝓘(ℝ, X × Y) ∞ e.symm := by
    intro w
    let b := w.1
    have hw : w ∈ (t b).target :=
      (t b).mem_target.mpr ((htbase b).symm ▸ S.mem_baseSet b)
    have hlocal := (exists_associatedSphere_atlas S).choose_spec.2.2.2.1 b
    have h := hlocal.2.contMDiffAt ((t b).open_target.mem_nhds hw)
    apply h.congr_of_eventuallyEq
    have hb := continuous_fst.continuousAt.preimage_mem_nhds
      ((isOpen_discrete ({b} : Set B)).mem_nhds (Set.mem_singleton _))
    filter_upwards [hb] with z hz
    exact hinv b z hz
  exact ⟨θ, hθ, { e with contMDiff_toFun := hsmooth, contMDiff_invFun := hsmoothInv }, he⟩

end AtiyahSinger
