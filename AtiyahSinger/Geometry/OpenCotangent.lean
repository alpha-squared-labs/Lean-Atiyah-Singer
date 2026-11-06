/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentSupport

/-!
# The cotangent inclusion of an open submanifold

Public module ID: M1316.

D03/A10: the inherited chart at a point of an open submanifold is a restriction
of the original chart. Its inclusion has identity differential in these local
coordinates. Consequently the inverse dual differential preserves the displayed
covector. This identifies T*U with the actual inverse image of U in T*M.
The total-space continuity and embedding properties are proved using the actual
inherited chart transitions and the native Hom-bundle topology.
Sources: SG III.1 (1.6), III.3 coordinate covariance, and III.13.4's open inclusions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace Topology Filter
open scoped Topology
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 20

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

/-- Cotangent inclusion for the inherited open-submanifold atlas, with unchanged covector. -/
def cotangentOpenInclusion (U : Opens M) :
    CotangentTotalSpace (n := n) (M := U) → CotangentTotalSpace (n := n) (M := M) :=
  fun z ↦ ⟨z.proj.val, z.snd⟩

include hM in
/-- The natural cotangent inclusion identifies an open submanifold with an open total subspace. -/
theorem isOpenEmbedding_cotangentOpenInclusion (U : Opens M) :
    IsOpenEmbedding (cotangentOpenInclusion (n := n) U) := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let H := EuclideanSpace ℝ (Fin n)
  -- The actual inherited chart transition agrees with its ambient transition near each point.
  have hchange (x y z : U) (hz : z ∈ (chartAt H x).source) :
      (tangentBundleCore I U).coordChange (achart H x) (achart H y) z =
        (tangentBundleCore I M).coordChange (achart H x.val) (achart H y.val) z.val := by
    have heq : (chartAt H x.val).symm =ᶠ[𝓝 (chartAt H x z)]
        Subtype.val ∘ (chartAt H x).symm := by
      filter_upwards [((chartAt H x).open_target.mem_nhds ((chartAt H x).map_source hz))]
        with w hw
      exact ((chartAt H x.val).subtypeRestr_symm_eqOn ⟨x⟩) hw
    have hc := heq.fun_comp (chartAt H y.val)
    simpa [tangentBundleCore_coordChange_achart, extChartAt_coe, extChartAt_coe_symm,
      I, Function.comp_def] using!
      hc.symm.fderivWithin_eq_of_nhds (𝕜 := ℝ) (s := Set.univ)
  have hdual (x y : U) (hy : y ∈ (chartAt H x).source) :
      (trivializationAt H (TangentSpace I : U → Type _) x).symmL ℝ y =
        (trivializationAt H (TangentSpace I : M → Type _) x.val).symmL ℝ y.val := by
    rw [TangentBundle.symmL_trivializationAt_eq_core hy,
      TangentBundle.symmL_trivializationAt_eq_core (show y.val ∈ (chartAt H x.val).source
        from hy.2)]
    exact hchange x y y hy
  have hcoord (x y : U) (hy : y ∈ (chartAt H x).source)
      (ξ : CotangentFiber (n := n) y) :
      ContinuousLinearMap.inCoordinates H (TangentSpace I : U → Type _) ℝ
          (Bundle.Trivial U ℝ) x y x y ξ =
        ContinuousLinearMap.inCoordinates H (TangentSpace I : M → Type _) ℝ
          (Bundle.Trivial M ℝ) x.val y.val x.val y.val ξ := by
    simp only [ContinuousLinearMap.inCoordinates]
    change ((Bundle.Trivial.trivialization U ℝ).continuousLinearMapAt ℝ y).comp
        (ξ.comp ((trivializationAt H (TangentSpace I : U → Type _) x).symmL ℝ y)) =
      ((Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ y.val).comp
        (ξ.comp ((trivializationAt H (TangentSpace I : M → Type _) x.val).symmL ℝ y.val))
    simp only [Bundle.Trivial.continuousLinearMapAt_trivialization,
      ContinuousLinearMap.id_comp]
    rw [hdual x y hy]
  -- Continuity on the original two cotangent bundles is equivalent under this inclusion.
  have hcont (Z : Type _) [TopologicalSpace Z]
      (f : Z → CotangentTotalSpace (n := n) (M := U)) (z : Z) :
      ContinuousAt f z ↔ ContinuousAt (cotangentOpenInclusion (n := n) U ∘ f) z := by
    rw [continuousAt_hom_bundle, continuousAt_hom_bundle]
    constructor
    · rintro ⟨hb, hc⟩
      refine ⟨continuous_subtype_val.continuousAt.comp hb, ?_⟩
      apply hc.congr_of_eventuallyEq
      filter_upwards [hb ((chartAt H (f z).proj).open_source.mem_nhds
        (mem_chart_source H (f z).proj))] with w hw
      exact (hcoord (f z).proj (f w).proj hw (f w).snd).symm
    · rintro ⟨hb, hc⟩
      have hb' : ContinuousAt (fun w ↦ (f w).proj) z :=
        tendsto_subtype_rng.mpr hb
      refine ⟨hb', ?_⟩
      apply hc.congr_of_eventuallyEq
      filter_upwards [hb' ((chartAt H (f z).proj).open_source.mem_nhds
        (mem_chart_source H (f z).proj))] with w hw
      exact hcoord (f z).proj (f w).proj hw (f w).snd
  have hforward : Continuous (cotangentOpenInclusion (n := n) U) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hcont _ id z).mp continuousAt_id
  -- Identify the source with the actual open inverse image of U, using the same covectors.
  let h : CotangentTotalSpace (n := n) (M := U) ≃ₜ
      {z : CotangentTotalSpace (n := n) (M := M) | z.proj ∈ U} :=
    { toFun z := ⟨cotangentOpenInclusion (n := n) U z, z.proj.property⟩
      invFun z := ⟨⟨z.val.proj, z.property⟩, z.val.snd⟩
      left_inv z := by cases z; rfl
      right_inv z := by cases z; rfl
      continuous_toFun := hforward.subtype_mk _
      continuous_invFun := by
        apply continuous_iff_continuousAt.mpr
        intro z
        apply (hcont _ (fun w ↦ ⟨⟨w.val.proj, w.property⟩, w.val.snd⟩) z).mpr
        exact continuous_subtype_val.continuousAt }
  have hopen : IsOpen {z : CotangentTotalSpace (n := n) (M := M) | z.proj ∈ U} :=
    U.isOpen.preimage cotangentProjection.continuous
  change IsOpenEmbedding (Subtype.val ∘ h)
  exact hopen.isOpenEmbedding_subtypeVal.comp h.isOpenEmbedding

include hM in
/-- Cotangent inclusion is proper when the open submanifold is also closed. -/
theorem isProperMap_cotangentOpenInclusion (U : Opens M) (hU : IsClosed (U : Set M)) :
    IsProperMap (cotangentOpenInclusion (n := n) U) := by
  /- The preceding open embedding has image exactly the inverse image of
  U under the continuous cotangent projection. The assumed closedness of U
  makes this image closed, so the map is a closed embedding and hence proper.
  Neither compactness of M nor compactness of its cotangent fibers is used.
  A general open inclusion is not proper, so closedness cannot be dropped. -/
  -- The same inclusion has precisely the inverse image of U as its range.
  have hrange : Set.range (cotangentOpenInclusion (n := n) U) =
      {z : CotangentTotalSpace (n := n) (M := M) | z.proj ∈ U} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact w.proj.property
    · intro hz
      exact ⟨⟨⟨z.proj, hz⟩, z.snd⟩, rfl⟩
  -- Closedness of the base subset makes this actual embedded range closed.
  have hclosed : IsClosed (Set.range (cotangentOpenInclusion (n := n) U)) := by
    rw [hrange]
    exact hU.preimage cotangentProjection.continuous
  have hembed : IsClosedEmbedding (cotangentOpenInclusion (n := n) U) :=
    ⟨(isOpenEmbedding_cotangentOpenInclusion U).isEmbedding, hclosed⟩
  exact hembed.isProperMap

end AtiyahSinger
