/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasSmoothingOperator
public import AtiyahSinger.Geometry.AtlasChartLocalization

import AtiyahSinger.Analysis.AtlasSobolevLocalization
import AtiyahSinger.Analysis.SmoothingOperator
import AtiyahSinger.Analysis.SobolevLocalization

/-!
# Local kernels of all-order atlas smoothing operators

Public module ID: M0302.

Localize the specified operator with two cutoffs in the same original chart.
The all-order atlas estimates give a native smoothing operator between two
trivial bundles with the actual local ranks. Its smooth kernel then recovers
the original localized action. This is the local kernel characterization in
SG III.3.15, with the varying-rank reduction made explicit. The auxiliary
positive density is absorbed by the final Euclidean kernel and is not an input.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

set_option maxHeartbeats 2000000 in
-- The extended limit accommodates the compact cutoffs, kernel regularity and original integral
-- representation.

/-- Two original atlas cutoffs of an all-order smoothing map have a compact smooth kernel. -/
theorem IsAtlasSmoothingOperator.exists_compactKernel
    (R : A.smoothSections →ₗ[ℂ] B.smoothSections) (hR : IsAtlasSmoothingOperator A B R)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (D : AtlasChartCutoff A c) (K : AtlasChartCutoff B c) :
    ∃ k : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →
        EuclideanSpace ℂ (Fin (A.rank D.frameIndex)) →L[ℂ]
          EuclideanSpace ℂ (Fin (B.rank K.frameIndex)),
      ContDiff ℝ ∞ (Function.uncurry k) ∧ HasCompactSupport (Function.uncurry k) ∧
        ∀ (u : 𝓢(EuclideanSpace ℝ (Fin n),
          EuclideanSpace ℂ (Fin (A.rank D.frameIndex)))) x,
          K.localize hc (R (D.extend hc u)) x = ∫ y, k x y (u y) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let r := A.rank D.frameIndex
  let q := B.rank K.frameIndex
  -- A common plateau is neutral on both of the original compact coordinate supports.
  have hcompact : IsCompact (tsupport D.cutoff ∪ tsupport K.cutoff) :=
    D.compact_support.union K.compact_support
  have hsub : tsupport D.cutoff ∪ tsupport K.cutoff ⊆ c.target :=
    union_subset (fun _ hz ↦ (D.support_subset hz).1) (fun _ hz ↦ (K.support_subset hz).1)
  obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
    exists_open_between_and_isCompact_closure hcompact c.open_target hsub
  obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
    exists_open_between_and_isCompact_closure hOc c.open_target hOU
  obtain ⟨ψ, hψ, _, hsψ, honeψ⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
  have hcψ : HasCompactSupport ψ := by
    simpa only [HasCompactSupport, tsupport, hsψ] using hO'c
  have hψU : tsupport ψ ⊆ c.target := by
    simpa only [tsupport, hsψ] using hO'U
  have hψone (x : X) (hx : x ∈ tsupport D.cutoff ∪ tsupport K.cutoff) : ψ x = 1 :=
    (honeψ x).mp (subset_closure (hKO hx))
  -- Native trivial bundles retain the two independent local ranks.
  let smoothTrivial (j : ℕ) :
      IsSmoothComplexBundle (n := n) (r := j) (Bundle.Trivial M (EuclideanSpace ℂ (Fin j))) := by
    constructor
    intro e e' he he'
    obtain rfl := Bundle.Trivial.eq_trivialization M (EuclideanSpace ℂ (Fin j)) e
    obtain rfl := Bundle.Trivial.eq_trivialization M (EuclideanSpace ℂ (Fin j)) e'
    simp_rw [Bundle.Trivial.trivialization.coordChangeL]
    exact contMDiff_const.contMDiffOn
  let := smoothTrivial r
  let := smoothTrivial q
  let C (j : ℕ) : BundleChartCutoff (r := j)
      (Bundle.Trivial M (EuclideanSpace ℂ (Fin j))) c :=
    { frame := Bundle.Trivial.trivialization M (EuclideanSpace ℂ (Fin j))
      frame_mem_atlas := ⟨rfl⟩
      cutoff := ψ
      smooth_cutoff := hψ
      compact_support := hcψ
      support_subset := fun _ hx ↦ ⟨hψU hx, mem_univ _⟩ }
  let S := ((C q).extendLinearMap hc).comp ((K.localizeLinearMap hc).comp
    (R.comp ((D.extendLinearMap hc).comp ((C r).localizeLinearMap hc))))
  obtain ⟨L⟩ := nonempty_atlasBundlePresentation A
  obtain ⟨H⟩ := nonempty_atlasBundlePresentation B
  obtain ⟨L₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := r)
    (Bundle.Trivial M (EuclideanSpace ℂ (Fin r)))
  obtain ⟨H₀⟩ := nonempty_smoothBundlePresentation (n := n) (r := q)
    (Bundle.Trivial M (EuclideanSpace ℂ (Fin q)))
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let : IsSmoothPositiveMeasure (n := n) μ := hμ
  have hS : IsSmoothingOperator μ S := by
    apply (isSmoothingOperator_iff_sobolevExtensions μ S L₀ H₀).mpr
    intro s t
    obtain ⟨T, hT⟩ := hR L H s t
    obtain ⟨C₁, hC₁, hb₁⟩ := (C r).exists_norm_localize_sobolev_le hc L₀ s
    obtain ⟨C₂, hC₂, hb₂⟩ := D.exists_norm_extend_sobolev_le hc L s
    obtain ⟨C₃, hC₃, hb₃⟩ := K.exists_norm_localize_sobolev_le hc H t
    obtain ⟨C₄, hC₄, hb₄⟩ := (C q).exists_norm_extend_sobolev_le hc H₀ t
    let f := (H₀.smoothToSobolev t).comp S
    have hbound (u : smoothSections (n := n) (r := r)
        (Bundle.Trivial M (EuclideanSpace ℂ (Fin r)))) :
        ‖f u‖ ≤ (C₄ * (C₃ * (‖T‖ * (C₂ * C₁)))) * ‖L₀.smoothToSobolev s u‖ := by
      calc
        ‖f u‖ ≤ C₄ * ‖schwartzSobolevCoordinate t
            (K.localize hc (R (D.extend hc ((C r).localize hc u))))‖ := hb₄ _
        _ ≤ C₄ * (C₃ * ‖H.smoothToSobolev t
            (R (D.extend hc ((C r).localize hc u)))‖) :=
          mul_le_mul_of_nonneg_left (hb₃ _) hC₄
        _ = C₄ * (C₃ * ‖T (L.smoothToSobolev s
            (D.extend hc ((C r).localize hc u)))‖) := by rw [hT]
        _ ≤ C₄ * (C₃ * (‖T‖ * ‖L.smoothToSobolev s
            (D.extend hc ((C r).localize hc u))‖)) := by gcongr; exact T.le_opNorm _
        _ ≤ C₄ * (C₃ * (‖T‖ * (C₂ * ‖schwartzSobolevCoordinate s
            ((C r).localize hc u)‖))) := by gcongr; exact hb₂ _
        _ ≤ C₄ * (C₃ * (‖T‖ * (C₂ * (C₁ * ‖L₀.smoothToSobolev s u‖)))) := by
          gcongr
          exact hb₁ u
        _ = _ := by ring
    refine ⟨f.extendOfNorm (L₀.smoothToSobolev s), ?_⟩
    exact LinearMap.extendOfNorm_eq (L₀.denseRange_smoothToSobolev s) ⟨_, hbound⟩
  obtain ⟨J, hJ⟩ := hS
  obtain ⟨k, hk, hck, hkact⟩ := J.exists_bundleChartCutoff_kernel μ c c hc hc (C r) (C q)
  refine ⟨k, hk, hck, ?_⟩
  intro u x
  -- Each extra round trip contributes ψ², which is one on the corresponding original support.
  have hin : D.extend hc ((C r).localize hc ((C r).extend hc u)) = D.extend hc u := by
    apply Subtype.ext
    funext y
    change D.extendedFunction ((C r).localize hc ((C r).extend hc u)) y = D.extendedFunction u y
    by_cases hy : y ∈ c.source ∩ (A.chart D.frameIndex).baseSet
    · simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hy]
      rw [(C r).localize_extend_apply]
      by_cases hd : c y ∈ tsupport D.cutoff
      · rw [show (C r).cutoff (c y) = 1 from hψone _ (Or.inl hd)]
        simp
      · simp [image_eq_zero_of_notMem_tsupport hd]
    · simp [AtlasChartCutoff.extendedFunction, hy]
  have hout : (C q).localize hc ((C q).extend hc (K.localize hc (R (D.extend hc u)))) =
      K.localize hc (R (D.extend hc u)) := by
    apply SchwartzMap.ext
    intro z
    rw [(C q).localize_extend_apply]
    by_cases hz : z ∈ tsupport K.cutoff
    · rw [show (C q).cutoff z = 1 from hψone _ (Or.inr hz)]
      simp
    · have hzero : K.localize hc (R (D.extend hc u)) z = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun h ↦ hz ((K.localizedFunction_properties hc (R (D.extend hc u))).2.1 h))
      rw [hzero, smul_zero]
  rw [← hkact, hJ]
  change K.localize hc (R (D.extend hc u)) x =
    (C q).localize hc ((C q).extend hc
      (K.localize hc (R (D.extend hc ((C r).localize hc ((C r).extend hc u)))))) x
  rw [hin, hout]

end AtiyahSinger
