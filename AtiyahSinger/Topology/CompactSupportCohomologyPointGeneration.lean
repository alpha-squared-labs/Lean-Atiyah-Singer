/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityLocal
public import AtiyahSinger.Topology.CompactSupportCohomologyTopGeneration

/-!
# Top-degree compact-support functionals are detected on point supports

Public module ID: M1663.

Each point has an open Euclidean neighborhood. On the Euclidean model, the
actual compact-relative duality at the singleton zero support is bijective.
The same global duality is injective, so every top-degree compact-support class
has a representative at that singleton. Extension through the original open
embedding preserves its singleton image. Open-cover generation then gives
the desired equality of global linear functionals.

Sources: local Poincare duality and its naturality, Hatcher, Algebraic Topology,
Section 3.3. No connectedness, compactness, or positive-dimension assumption
is imposed on the manifold, and no particular normalization of a scalar
functional is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Top-degree compact-support functionals agree if they agree on every point support. -/
theorem compactSupportCohomology_top_ext_of_singletons
    {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [T2Space M] [SecondCountableTopology M] (O : HomologicalOrientation n M)
    (f g : compactSupportCohomology ℚ M n →ₗ[ℚ] ℚ)
    (hfg : ∀ (x : M) (a : relativeSingularCohomology ℚ ({x}ᶜ : Set M) n),
      f (compactSupportCohomologyClass ℚ M ⟨{x}, isCompact_singleton⟩ n a) =
        g (compactSupportCohomologyClass ℚ M ⟨{x}, isCompact_singleton⟩ n a)) :
    f = g := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let eL : E ≃L[ℝ] (Fin n → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ)
  -- Refine each original chart to a ball, retaining a genuine Euclidean homeomorphism.
  have hneighborhood (x : M) :
      ∃ U : Opens M, x ∈ U ∧ Nonempty (E ≃ₜ U) := by
    let c := chartAt E x
    have hx : x ∈ c.source := mem_chart_source E x
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c x) (c.map_source hx)
    let W : Opens E := ⟨Metric.ball (c x) r, Metric.isOpen_ball⟩
    have hW : (W : Set E).Nonempty := ⟨c x, Metric.mem_ball_self hr⟩
    obtain ⟨a, ha, _⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_ball (c x) r) (by rw [Metric.isOpen_ball.interior_eq]; exact hW)
      Metric.isBounded_ball
    have haW : a '' (W : Set E) = Metric.ball (0 : E) 1 := by
      change a '' Metric.ball (c x) r = Metric.ball (0 : E) 1
      simpa only [Metric.isOpen_ball.interior_eq] using ha
    let toBall : W ≃ₜ Metric.ball (0 : E) 1 :=
      (a.image (W : Set E)).trans (Homeomorph.setCongr haW)
    let b : E ≃ₜ W := Homeomorph.unitBall.trans toBall.symm
    let i : C(W, c.target) := ContinuousMap.inclusion hball
    have hi : IsOpenEmbedding i :=
      IsOpenEmbedding.inclusion hball (W.isOpen.preimage continuous_subtype_val)
    let j : C(W, M) := ⟨fun y ↦ c.symm y.val,
      c.symm.isOpenEmbedding_restrict.continuous.comp i.continuous⟩
    have hj : IsOpenEmbedding j := c.symm.isOpenEmbedding_restrict.comp hi
    let q : C(E, M) := j.comp ⟨b, b.continuous⟩
    have hq : IsOpenEmbedding q := hj.comp b.isOpenEmbedding
    let U : Opens M := ⟨Set.range q, hq.isOpen_range⟩
    refine ⟨U, ?_, ⟨hq.isEmbedding.toHomeomorph⟩⟩
    refine ⟨b.symm ⟨c x, Metric.mem_ball_self hr⟩, ?_⟩
    change c.symm (b (b.symm ⟨c x, Metric.mem_ball_self hr⟩)).val = x
    rw [b.apply_symm_apply]
    exact c.left_inv hx
  choose U hU he using hneighborhood
  apply compactSupportCohomology_top_ext_of_openCover O U
    (fun x ↦ ⟨x, hU x⟩) f g
  intro x a
  let e : E ≃ₜ U x := (he x).some
  let j : C(U x, M) := ContinuousMap.subtypeVal (U x : Set M)
  have hj : IsOpenEmbedding j := (U x).isOpen.isOpenEmbedding_subtypeVal
  let q : C(E, U x) := ⟨e, e.continuous⟩
  let P : HomologicalOrientation n (U x) := homologicalOrientationOpenPullback O j hj
  let Q : HomologicalOrientation n E :=
    homologicalOrientationOpenPullback P q e.isOpenEmbedding
  -- On the Euclidean model the same duality already has a representative at {0}.
  obtain ⟨b, hb⟩ :=
    (compactSupportCohomologyOpenExtension_bijective_of_homeomorph ℚ e n).surjective a
  let K : Compacts E := ⟨{0}, isCompact_singleton⟩
  obtain ⟨β, hβ⟩ := (compactRelativeDuality_bijective_of_convex eL Q K
    (convex_singleton 0) (Set.mem_singleton 0) n 0 (Nat.add_zero n)).surjective
      (compactPoincareDuality Q n 0 (Nat.add_zero n) b)
  have hbK : compactSupportCohomologyClass ℚ E K n β = b := by
    apply (compactPoincareDuality_bijective Q n 0 (Nat.add_zero n)).injective
    exact (compactPoincareDuality_representative Q K n 0 (Nat.add_zero n) β).trans hβ
  -- The two original extensions compose, and their actual image support is a singleton.
  rw [← hb, ← hbK]
  change f (compactSupportCohomologyOpenExtension ℚ j hj n
    (compactSupportCohomologyOpenExtension ℚ q e.isOpenEmbedding n
      (compactSupportCohomologyClass ℚ E K n β))) =
    g (compactSupportCohomologyOpenExtension ℚ j hj n
      (compactSupportCohomologyOpenExtension ℚ q e.isOpenEmbedding n
        (compactSupportCohomologyClass ℚ E K n β)))
  have hcomp := compactSupportCohomologyOpenExtension_comp ℚ q e.isOpenEmbedding j hj n
  have hvalue := congrArg (fun h ↦ h (compactSupportCohomologyClass ℚ E K n β)) hcomp
  change compactSupportCohomologyOpenExtension ℚ (j.comp q) (hj.comp e.isOpenEmbedding) n
    (compactSupportCohomologyClass ℚ E K n β) =
    compactSupportCohomologyOpenExtension ℚ j hj n
      (compactSupportCohomologyOpenExtension ℚ q e.isOpenEmbedding n
        (compactSupportCohomologyClass ℚ E K n β)) at hvalue
  rw [← hvalue, compactSupportCohomologyOpenExtension_representative]
  let L := openEmbeddingCompactImage (j.comp q) K
  have hL : L = ⟨{j (q 0)}, isCompact_singleton⟩ := by
    apply Compacts.ext
    change (j.comp q) '' ({0} : Set E) = {j (q 0)}
    exact Set.image_singleton
  have hsingleton (K' : Compacts M) (y : M)
      (hK' : K' = ⟨{y}, isCompact_singleton⟩)
      (γ : relativeSingularCohomology ℚ ((K' : Set M)ᶜ) n) :
      f (compactSupportCohomologyClass ℚ M K' n γ) =
        g (compactSupportCohomologyClass ℚ M K' n γ) := by
    subst K'
    exact hfg y γ
  change f (compactSupportCohomologyClass ℚ M L n _) =
    g (compactSupportCohomologyClass ℚ M L n _)
  exact hsingleton L (j (q 0)) hL _

end AtiyahSinger
