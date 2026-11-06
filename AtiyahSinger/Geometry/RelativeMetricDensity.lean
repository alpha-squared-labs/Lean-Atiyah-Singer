/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetric
public import AtiyahSinger.Geometry.OpenDensity
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Geometry.SmoothDensityRatio

/-!
# Extending metrics and positive densities near a compact set

Public module ID: M1354.

E01/D02/UL03: prescribe local geometric data on a neighborhood of the compact
region used in excision. The extension agrees on a possibly smaller open
neighborhood, not necessarily on the entire original open set. Both constructions
use mathlib smooth separation near disjoint closed sets and the existing global
existence results on the Hausdorff second-countable smooth base. The cutoff
interpolates the local and global data; compact support is not required.

Sources: HU III.9.1--9.5 (continuous metrics), SG III.5 and III.13.4.
Smooth relative extension is a project supplement, not a numbered source theorem.
No orientation, compact ambient base, or uniform bounds on given fiber norms enter.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M]

include hM hT hSC

section Metric

variable {r : ℕ} (E : M → Type*)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]

include hE

open Set Function in
open scoped Topology in
set_option maxSynthPendingDepth 35 in
set_option maxHeartbeats 1000000 in
-- Glue the original local Gram entries through the same smooth cutoff.
set_option backward.isDefEq.respectTransparency false in
/-- A local smooth Hermitian metric extends while agreeing near the prescribed compact set. -/
theorem exists_smoothHermitianMetric_extension (U : Opens M)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (h : SmoothHermitianMetric (n := n) (r := r) (M := U)
      ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E)) :
    ∃ H : SmoothHermitianMetric (n := n) (r := r) E,
      ∃ V : Opens M, K ⊆ (V : Set M) ∧ V ≤ U ∧
        ∀ (x : U), x.val ∈ V → ∀ v w : E x.val,
          H.pairing x.val v w = h.pairing x v w := by
  /- Stage 1: choose a global smooth metric H₀. Mathlib's smooth separation
  theorem provides 0 ≤ χ ≤ 1, equal to one near K and zero near the closed
  complement of U. The original Hausdorff second-countable manifold is normal
  and sigma-compact by local compactness. Compact support of χ is not needed
  for the stated neighborhood extension.
  Stage 2: on U form χh+(1-χ)H₀ and outside U keep H₀. Positivity follows
  fiberwise from this convex combination. Smoothness uses the exact native
  pulled-back frames on U and equality with H₀ near every point off U.
  Stage 3: restrict to U intersected with the interior of {χ=1}. It contains K
  and the original pairings agree there. No fiber norm or topology is replaced. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  obtain ⟨H₀⟩ := nonempty_smoothHermitianMetric (n := n) (r := r) E
  -- Separate K from the closed complement by one smooth function valued in [0,1].
  obtain ⟨χ, hχzero, hχone, hχbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := (⊤ : ℕ∞))
      U.isOpen.isClosed_compl hK.isClosed
      (Set.disjoint_left.mpr fun x hxU hxK ↦ hxU (hKU hxK))
  let q (x : U) (v w : E x.val) : ℂ :=
    (χ x.val : ℂ) * h.pairing x v w + ((1 - χ x.val : ℝ) : ℂ) * H₀.pairing x.val v w
  have hqre (x : U) (v : E x.val) : (q x v v).re =
      χ x.val * (h.pairing x v v).re + (1 - χ x.val) * (H₀.pairing x.val v v).re := by
    simp [q, Complex.mul_re]
  -- Convex combinations preserve the original positive Hermitian forms on every fiber.
  let core (x : U) : InnerProductSpace.Core ℂ (E x.val) := {
    inner := q x
    conj_inner_symm := by
      intro v w
      dsimp only [q, SmoothHermitianMetric.pairing]
      simp only [map_add, map_mul, Complex.conj_ofReal,
        (h.toCore x).conj_inner_symm, (H₀.toCore x.val).conj_inner_symm]
    re_inner_nonneg := by
      intro v
      change 0 ≤ (q x v v).re
      rw [hqre]
      exact add_nonneg (mul_nonneg (hχbounds x.val).1 ((h.toCore x).re_inner_nonneg v))
        (mul_nonneg (sub_nonneg.mpr (hχbounds x.val).2)
          ((H₀.toCore x.val).re_inner_nonneg v))
    add_left := by
      intro v w z
      dsimp only [q, SmoothHermitianMetric.pairing]
      rw [(h.toCore x).add_left, (H₀.toCore x.val).add_left]
      ring
    smul_left := by
      intro v w a
      dsimp only [q, SmoothHermitianMetric.pairing]
      rw [(h.toCore x).smul_left, (H₀.toCore x.val).smul_left]
      ring
    definite := by
      intro v hv
      by_contra hn
      have hpos := h.pairing_self_pos x v hn
      have hpos₀ := H₀.pairing_self_pos x.val v hn
      have heq := congrArg Complex.re hv
      rw [hqre] at heq
      change χ x.val * (h.pairing x v v).re +
        (1 - χ x.val) * (H₀.pairing x.val v v).re = 0 at heq
      have hnonneg := mul_nonneg (hχbounds x.val).1 hpos.le
      by_cases hχ : χ x.val = 1
      · simp only [hχ, one_mul, sub_self, zero_mul, add_zero] at heq
        exact hpos.ne' heq
      · have hχlt : χ x.val < 1 := lt_of_le_of_ne (hχbounds x.val).2 hχ
        have hterm := mul_pos (sub_pos.mpr hχlt) hpos₀
        linarith }
  let g (x : M) : InnerProductSpace.Core ℂ (E x) :=
    if hx : x ∈ U then core ⟨x, hx⟩ else H₀.toCore x
  have hpair_zero (x : M) (hxχ : χ x = 0) (v w : E x) :
      (g x).inner v w = H₀.pairing x v w := by
    by_cases hx : x ∈ U
    · have hg : g x = core ⟨x, hx⟩ := dite_eq_left hx
      rw [hg]
      change q ⟨x, hx⟩ v w = _
      simp [q, hxχ]
    · have hg : g x = H₀.toCore x := dite_eq_right hx
      rw [hg]
      rfl
  let H : SmoothHermitianMetric (n := n) (r := r) E := {
    toCore := g
    isSmoothBundle := H₀.isSmoothBundle
    contMDiffOn_gram := by
      intro e he i j x hx
      let := he
      by_cases hxU : x ∈ U
      · -- On U the Gram entries are the weighted original pulled-back frame entries.
        apply ContMDiffAt.contMDiffWithinAt
        rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hxU⟩)]
        let eU := e.pullback (ContinuousMap.subtypeVal (U : Set M))
        have heU : MemTrivializationAtlas eU := ⟨e, he, rfl⟩
        let := heU
        have hh := (h.contMDiffOn_gram eU i j).contMDiffAt
          (eU.open_baseSet.mem_nhds (show (⟨x, hxU⟩ : U) ∈ eU.baseSet from hx))
        have hH₀ := (H₀.contMDiffOn_gram e i j).contMDiffAt (e.open_baseSet.mem_nhds hx)
        have hχ := χ.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
          contMDiff_subtype_val.contMDiffAt
        have hχc := Complex.ofRealCLM.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U) hχ
        have hχ' := Complex.ofRealCLM.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
          ((contMDiffAt_const (c := (1 : ℝ))).sub hχ)
        have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
        have hs := (hmul.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
          (hχc.prodMk_space hh)).add (hmul.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
            (hχ'.prodMk_space (hH₀.comp (⟨x, hxU⟩ : U) contMDiff_subtype_val.contMDiffAt)))
        apply hs.congr_of_eventuallyEq
        filter_upwards [eU.open_baseSet.mem_nhds
          (show (⟨x, hxU⟩ : U) ∈ eU.baseSet from hx)] with y hy
        have hsymm (v : EuclideanSpace ℂ (Fin r)) :
            e.symmL ℂ y.val v = eU.symmL ℂ y v := by
          have hyb : y.val ∈ e.baseSet := hy
          have hcoord : e.continuousLinearMapAt ℂ y.val (eU.symmL ℂ y v) = v := by
            calc
              _ = (e ⟨y.val, eU.symmL ℂ y v⟩).2 :=
                e.continuousLinearMapAt_apply_of_mem ℂ hyb _
              _ = (eU ⟨y, eU.symmL ℂ y v⟩).2 := rfl
              _ = eU.continuousLinearMapAt ℂ y (eU.symmL ℂ y v) :=
                (eU.continuousLinearMapAt_apply_of_mem ℂ hy _).symm
              _ = v := eU.continuousLinearMapAt_symmL hy v
          exact (congrArg (e.symmL ℂ y.val) hcoord).symm.trans
            (e.symmL_continuousLinearMapAt hyb _)
        have hg : g y.val = core y := dite_eq_left y.property
        rw [hg]
        change (χ y.val : ℂ) * h.pairing y
            (e.symmL ℂ y.val (EuclideanSpace.single i 1))
            (e.symmL ℂ y.val (EuclideanSpace.single j 1)) + _ =
          (χ y.val : ℂ) * h.pairing y
            (eU.symmL ℂ y (EuclideanSpace.single i 1))
            (eU.symmL ℂ y (EuclideanSpace.single j 1)) + _
        exact congrArg (fun z : ℂ ↦ (χ y.val : ℂ) * z +
          ((1 - χ y.val : ℝ) : ℂ) * H₀.pairing y.val
            (e.symmL ℂ y.val (EuclideanSpace.single i 1))
            (e.symmL ℂ y.val (EuclideanSpace.single j 1)))
          (congrArg₂ (h.pairing y) (hsymm _) (hsymm _))
      · -- Near every point off U, the cutoff vanishes and the metric is exactly H₀.
        apply ContMDiffAt.contMDiffWithinAt
        apply ((H₀.contMDiffOn_gram e i j).contMDiffAt
          (e.open_baseSet.mem_nhds hx)).congr_of_eventuallyEq
        have hz : ∀ᶠ y in 𝓝 x, χ y = 0 :=
          hχzero.filter_mono (nhds_le_nhdsSet hxU)
        filter_upwards [hz] with y hy
        exact hpair_zero y hy _ _ }
  let V : Opens M := ⟨(U : Set M) ∩ interior {x : M | χ x = 1},
    U.isOpen.inter isOpen_interior⟩
  refine ⟨H, V, ?_, fun x hx ↦ hx.1, ?_⟩
  · intro x hx
    exact ⟨hKU hx, mem_interior_iff_mem_nhds.mpr
      (hχone.filter_mono (nhds_le_nhdsSet hx))⟩
  · intro x hx v w
    have hχ : χ x.val = 1 := (interior_subset (s := {x : M | χ x = 1}) hx.2)
    change (g x.val).inner v w = h.pairing x v w
    change (if hx : x.val ∈ U then core ⟨x.val, hx⟩ else H₀.toCore x.val).inner v w = _
    rw [dite_eq_left x.property]
    change q x v w = _
    simp [q, hχ]

end Metric

variable [MeasurableSpace M] [hBorel : BorelSpace M]

include hBorel

open Set Function in
open scoped Topology in
set_option maxSynthPendingDepth 35 in
set_option maxHeartbeats 1000000 in
-- Compare the original subtype measures and their smooth density ratio near the compact set.
/-- A local positive smooth density extends with equality of the actual measures near K. -/
theorem exists_smoothPositiveMeasure_extension (U : Opens M)
    (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (ν : Measure U) [hν : IsSmoothPositiveMeasure (n := n) ν] :
    ∃ μ : Measure M, IsSmoothPositiveMeasure (n := n) μ ∧
      ∃ V : Opens M, K ⊆ (V : Set M) ∧ V ≤ U ∧
        (μ.comap (Subtype.val : U → M)).restrict
            ((Subtype.val : U → M) ⁻¹' (V : Set M)) =
          ν.restrict ((Subtype.val : U → M) ⁻¹' (V : Set M)) := by
  /- Stage 1: choose a global positive smooth density μ₀ and its native
  subtype comap to U. The actual ratio w=dν/d(μ₀|U) is smooth and positive.
  A mathlib smooth cutoff is one near K and zero near the closed complement.
  Stage 2: interpolate by f=χw+(1-χ) on U, and use f=1 outside. The weight is
  positive and smooth across the boundary, so μ=μ₀.withDensity(ofReal f) has
  positive smooth coordinate densities in the same original atlas.
  Stage 3: compare actual subtype comaps using the subtype integral identity.
  Where χ=1 the weight is precisely w; its defining withDensity identity gives
  the required equality of the two restricted measures on that same open set. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- Compare the prescribed local measure with this same global positive density.
  obtain ⟨μ₀, hμ₀⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let hμ₀inst := hμ₀
  let μU := μ₀.comap (Subtype.val : U → M)
  have hμU : IsSmoothPositiveMeasure (n := n) μU :=
    isSmoothPositiveMeasure_comap_opens μ₀ U
  let w := smoothDensityRatio (n := n) μU ν
  have hw : ContMDiff I 𝓘(ℝ, ℝ) ∞ w := contMDiff_smoothDensityRatio μU ν
  have hwpos : ∀ x, 0 < w x := smoothDensityRatio_pos μU ν
  -- A smooth cutoff is one near K and zero near the closed complement of U.
  obtain ⟨χ, hχzero, hχone, hχbounds⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed I (n := (⊤ : ℕ∞))
      U.isOpen.isClosed_compl hK.isClosed
      (Set.disjoint_left.mpr fun x hxU hxK ↦ hxU (hKU hxK))
  let f (x : M) : ℝ := if hx : x ∈ U then
    χ x * w ⟨x, hx⟩ + (1 - χ x) else 1
  have hfzero (x : M) (hxχ : χ x = 0) : f x = 1 := by
    dsimp only [f]
    split_ifs with hx
    · simp [hxχ]
    · rfl
  have hfpos (x : M) : 0 < f x := by
    dsimp only [f]
    split_ifs with hx
    · have hnonneg := mul_nonneg (hχbounds x).1 (hwpos ⟨x, hx⟩).le
      by_cases hχ : χ x = 1
      · simpa [hχ] using hwpos ⟨x, hx⟩
      · have hlt := lt_of_le_of_ne (hχbounds x).2 hχ
        linarith
    · exact zero_lt_one
  -- The positive interpolation is smooth on U and identically one near its boundary.
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    intro x
    by_cases hxU : x ∈ U
    · rw [← contMDiffAt_subtype_iff (U := U) (x := ⟨x, hxU⟩)]
      have hχ := χ.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
        contMDiff_subtype_val.contMDiffAt
      have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_mul
      have hs := (hmul.contMDiff.contMDiffAt.comp (⟨x, hxU⟩ : U)
        (hχ.prodMk_space (hw ⟨x, hxU⟩))).add
          ((contMDiffAt_const (c := (1 : ℝ))).sub hχ)
      apply hs.congr_of_eventuallyEq
      filter_upwards [] with y
      exact dite_eq_left y.property
    · apply (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [hχzero.filter_mono (nhds_le_nhdsSet hxU)] with y hy
      exact hfzero y hy
  let μ := μ₀.withDensity (fun x ↦ ENNReal.ofReal (f x))
  have hmapDensity (θ : Measure M) (c : M → EuclideanSpace ℝ (Fin n))
      (a : EuclideanSpace ℝ (Fin n) → ENNReal) (hc : AEMeasurable c θ)
      (ha : AEMeasurable a (Measure.map c θ)) :
      (Measure.map c θ).withDensity a =
        Measure.map c (θ.withDensity (fun x ↦ a (c x))) := by
    ext A hA
    rw [withDensity_apply _ hA,
      Measure.map_apply_of_aemeasurable
        (hc.mono_ac (withDensity_absolutelyContinuous _ _)) hA,
      withDensity_apply₀ _ (hc.nullMeasurable hA),
      ← lintegral_indicator hA, ← lintegral_indicator₀ (hc.nullMeasurable hA)]
    rw [lintegral_map' (ha.indicator hA) hc]
    congr 1
  -- In every original chart, multiplication by f multiplies the same coordinate density.
  have hμ : IsSmoothPositiveMeasure (n := n) μ := by
    constructor
    intro c hc
    obtain ⟨a, ha, hapos, hmeasure⟩ := hμ₀.exists_smooth_density c hc
    have hcS := contMDiffOn_symm_of_mem_maximalAtlas
      (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
    have hfc : ContDiffOn ℝ ∞ (fun y ↦ f (c.symm y)) c.target :=
      contMDiffOn_iff_contDiffOn.mp (hf.comp_contMDiffOn hcS)
    refine ⟨fun y ↦ a y * f (c.symm y), ha.mul hfc,
      fun y hy ↦ mul_pos (hapos y hy) (hfpos _), ?_⟩
    have hcf : AEMeasurable (fun y ↦ ENNReal.ofReal (f (c.symm y)))
        (Measure.map c (μ₀.restrict c.source)) := by
      rw [hmeasure]
      exact (hfc.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal.mono_ac
        (withDensity_absolutelyContinuous _ _)
    have hsource : (μ₀.restrict c.source).withDensity (fun x ↦ ENNReal.ofReal (f x)) =
        (μ₀.restrict c.source).withDensity (fun x ↦ ENNReal.ofReal (f (c.symm (c x)))) := by
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      rw [c.left_inv hx]
    dsimp only [μ]
    rw [restrict_withDensity c.open_source.measurableSet, hsource,
      ← hmapDensity (μ₀.restrict c.source) c _
        (c.continuousOn.aemeasurable c.open_source.measurableSet) hcf,
      hmeasure, ← withDensity_mul₀
        (ha.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
        (hfc.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem c.open_target.measurableSet] with y hy
    exact (ENNReal.ofReal_mul (hapos y hy).le).symm
  let V : Opens M := ⟨(U : Set M) ∩ interior {x : M | χ x = 1},
    U.isOpen.inter isOpen_interior⟩
  refine ⟨μ, hμ, V, ?_, fun x hx ↦ hx.1, ?_⟩
  · intro x hx
    exact ⟨hKU hx, mem_interior_iff_mem_nhds.mpr
      (hχone.filter_mono (nhds_le_nhdsSet hx))⟩
  · -- The native subtype comap commutes with this exact global density weight.
    have hcomap : μ.comap (Subtype.val : U → M) =
        μU.withDensity (fun x ↦ ENNReal.ofReal (f x.val)) := by
      ext A hA
      have hsub := MeasurableEmbedding.subtype_coe (s := (U : Set M)) U.isOpen.measurableSet
      erw [hsub.comap_apply μ A]
      change (μ₀.withDensity (fun x ↦ ENNReal.ofReal (f x))) _ = _
      rw [withDensity_apply _ (hsub.measurableSet_image.mpr hA), withDensity_apply _ hA]
      exact (setLIntegral_subtype U.isOpen.measurableSet A
        (fun x ↦ ENNReal.ofReal (f x))).symm
    have hV : MeasurableSet ((Subtype.val : U → M) ⁻¹' (V : Set M)) :=
      V.isOpen.measurableSet.preimage measurable_subtype_coe
    rw [hcomap, ← withDensity_smoothDensityRatio (n := n) μU ν,
      restrict_withDensity hV, restrict_withDensity hV]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hV] with x hx
    have hχ : χ x.val = 1 := interior_subset (s := {x : M | χ x = 1}) hx.2
    congr 1
    dsimp only [f]
    rw [dite_eq_left x.property]
    simp [hχ, w]

end AtiyahSinger
