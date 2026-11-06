/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasChartLocalization
public import AtiyahSinger.Geometry.CotangentProduct

/-!
# Joint Schwartz coordinates of a compact section family

Public module ID: M0231.

A smooth family of sections with a common compact parameter support has
joint Schwartz coordinates after the specified original atlas cutoff.
The finite coefficient family is flattened in the original base-first order.
The construction retains the actual chart, frame, cutoff, and section values.

This is the local coordinate input for controlled regularization of the
associated horizontal and vertical operators. It asserts no global Sobolev
extension or operator-domain comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped ContDiff Manifold SchwartzMap Topology

variable {n m d : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ M] [T2Space M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  (A : SmoothComplexBundleAtlas (n := m) E)

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The original cutoff of a compact smooth section family has exact joint Schwartz coordinates. -/
theorem exists_jointSchwartz_atlasChartCutoff_localize
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin m)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin m)) M) (C : AtlasChartCutoff A c)
    (u : EuclideanSpace ℝ (Fin n) → Fin d → A.smoothSections)
    (hu : ∀ (i : Fin d) (j : A.Index),
      ContMDiffOn ((𝓘(ℝ, EuclideanSpace ℝ (Fin n))).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin m))) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
        (fun p : EuclideanSpace ℝ (Fin n) × M ↦ (A.chart j ⟨p.2, (u p.1 i).val p.2⟩).2)
        (Set.univ ×ˢ (A.chart j).baseSet))
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hsupport : ∀ x ∉ K, ∀ i, u x i = 0) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin (n + m)),
        EuclideanSpace ℂ (Fin (d * A.rank C.frameIndex))),
      (∀ x y i j, f (EuclideanSpace.finAddEquivProd.symm (x, y))
          (finProdFinEquiv (i, j)) = C.localize hc (u x i) y j) ∧
      tsupport f ⊆ EuclideanSpace.finAddEquivProd.symm '' (K ×ˢ tsupport C.cutoff) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let Y := EuclideanSpace ℝ (Fin m)
  let Z := EuclideanSpace ℝ (Fin (n + m))
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := m)
  let v (i : Fin d) (p : X × Y) := C.localize hc (u p.1 i) p.2
  -- On the original cutoff support, the given joint section coordinates are smooth.
  have hv (i : Fin d) : ContDiff ℝ ∞ (v i) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    by_cases hp : p.2 ∈ tsupport C.cutoff
    · have hpt := (C.support_subset hp).1
      have hpf := (C.support_subset hp).2
      change c.symm p.2 ∈ (A.chart C.frameIndex).baseSet at hpf
      have hchart := contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := 𝓘(ℝ, Y)) (n := ∞) hc) hpt
      have hpair : ContMDiffAt 𝓘(ℝ, X × Y) ((𝓘(ℝ, X)).prod 𝓘(ℝ, Y)) ∞
          (fun z : X × Y ↦ (z.1, c.symm z.2)) p :=
        contDiffAt_fst.contMDiffAt.prodMk (hchart.comp p contDiffAt_snd.contMDiffAt)
      have hsection : ContMDiffAt ((𝓘(ℝ, X)).prod 𝓘(ℝ, Y))
          𝓘(ℝ, Fin (A.rank C.frameIndex) → ℂ) ∞
          (fun z : X × M ↦ (A.chart C.frameIndex ⟨z.2, (u z.1 i).val z.2⟩).2)
          (p.1, c.symm p.2) := (hu i C.frameIndex).contMDiffAt
        ((isOpen_univ.prod (A.chart C.frameIndex).open_baseSet).mem_nhds
          ⟨Set.mem_univ p.1, hpf⟩)
      let er := EuclideanSpace.equiv (Fin (A.rank C.frameIndex)) ℂ
      have hcoords := (er.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiffAt.comp p
        (hsection.comp p hpair)
      have hcutoff : ContDiffAt ℝ ∞ (fun z : X × Y ↦ (C.cutoff z.2 : ℂ)) p :=
        (Complex.ofRealCLM.contDiff.comp (C.smooth_cutoff.comp contDiff_snd)).contDiffAt
      apply (hcutoff.smul hcoords.contDiffAt).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt (c.open_target.mem_nhds hpt)] with z hz
      change C.localizedFunction (u z.1 i) z.2 = _
      have hzt : z.2 ∈ c.target := hz
      simp [AtlasChartCutoff.localizedFunction, atlasSectionInChart, hzt, er]
    · -- Outside the same compact support, the actual zero extension vanishes locally.
      apply (contDiffAt_const (c := (0 : EuclideanSpace ℂ
        (Fin (A.rank C.frameIndex))))).congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt
        ((isClosed_tsupport C.cutoff).isOpen_compl.mem_nhds hp)] with z hz
      change C.localizedFunction (u z.1 i) z.2 = 0
      exact image_eq_zero_of_notMem_tsupport
        (fun h ↦ hz ((C.localizedFunction_properties hc (u z.1 i)).2.1 h))
  let g (z : Z) : EuclideanSpace ℂ (Fin (d * A.rank C.frameIndex)) :=
    WithLp.toLp 2 (fun k ↦ v (finProdFinEquiv.symm k).1 (e z)
      (finProdFinEquiv.symm k).2)
  have hg : ContDiff ℝ ∞ g := by
    apply (contDiff_piLp (𝕜 := ℝ) (p := 2)).mpr
    intro k
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (finProdFinEquiv.symm k).2).restrictScalars ℝ).contDiff
      |>.comp ((hv (finProdFinEquiv.symm k).1).comp e.contDiff)
  -- Every nonzero coordinate lies in the specified common product support.
  have hcompact : IsCompact (e.symm '' (K ×ˢ tsupport C.cutoff)) :=
    (hK.prod C.compact_support).image e.symm.continuous
  have hgsupport : tsupport g ⊆ e.symm '' (K ×ˢ tsupport C.cutoff) := by
    apply closure_minimal ?_ hcompact.isClosed
    intro z hz
    refine ⟨e z, ⟨?_, ?_⟩, e.symm_apply_apply z⟩
    · by_contra h
      apply hz
      apply PiLp.ext
      intro k
      change C.localize hc (u (e z).1 (finProdFinEquiv.symm k).1)
        (e z).2 (finProdFinEquiv.symm k).2 = 0
      rw [hsupport (e z).1 h]
      change (C.localizeLinearMap hc) 0 (e z).2 (finProdFinEquiv.symm k).2 = 0
      rw [map_zero]
      rfl
    · by_contra h
      apply hz
      apply PiLp.ext
      intro k
      have hvzero : C.localize hc (u (e z).1 (finProdFinEquiv.symm k).1) (e z).2 = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h' ↦ h ((C.localizedFunction_properties hc
            (u (e z).1 (finProdFinEquiv.symm k).1)).2.1 h'))
      exact congrArg (fun v ↦ v (finProdFinEquiv.symm k).2) hvzero
  let f := HasCompactSupport.toSchwartzMap
    (show HasCompactSupport g from hcompact.of_isClosed_subset (isClosed_tsupport _) hgsupport) hg
  refine ⟨f, ?_, hgsupport⟩
  intro x y i j
  change v (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
    (e (e.symm (x, y))) (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = _
  rw [Equiv.symm_apply_apply, e.apply_symm_apply]

end AtiyahSinger
