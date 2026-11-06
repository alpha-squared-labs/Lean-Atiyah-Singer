/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DensityDiffeomorph
public import Mathlib.Geometry.Manifold.Algebra.SMul
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Prod

import AtiyahSinger.Geometry.CompactParameterIntegral
import AtiyahSinger.Geometry.EquivariantDensityFamilies

/-!
# Invariant smooth positive densities by compact-group averaging

Public module ID: M1206.

The averaged measure is the pushforward of normalized Haar measure times the
original measure by the original action map. It is not an unspecified choice
of invariant measure. For a smooth action on a compact manifold, averaging a
positive smooth density gives a positive smooth density for the same atlas.

Sources: SG III.9, pp.211--212, and III.5, pp.194--195. The measure formulation
keeps the absolute inverse Jacobian, hence also covers nonorientable manifolds.
The action-pushforward convention uses left Haar invariance; the forward-action
Hermitian pairing average instead uses right invariance. No metric is changed.
The actual Haar pushforward is invariant and has a positive smooth density.
Compact-parameter integration proves smoothness for the same atlas and action.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory TopologicalSpace Manifold Set Filter Topology
open scoped Manifold ContDiff

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [MulAction G M]

/-- Push normalized Haar times the original measure through the original action. -/
def averagedActionMeasure (μ : Measure M) : Measure M :=
  Measure.map (fun p : G × M ↦ p.1 • p.2)
    ((Measure.haarMeasure (⊤ : PositiveCompacts G)).prod μ)

set_option linter.unusedSectionVars false in
/-- The specified action average is invariant under every element of the compact group. -/
theorem map_averagedActionMeasure [MeasurableSMul₂ G M]
    (μ : Measure M) [hμ : IsFiniteMeasure μ] (g : G) :
    Measure.map (fun x : M ↦ g • x) (averagedActionMeasure G μ) =
      averagedActionMeasure G μ := by
  /- Stage 1: the supplied product-measurable action makes every fixed-group
  action measurable. Compose their actual pushforward maps, keeping the product
  measure on G times M. The resulting action is (k,x) |-> (g*k)*x.
  Stage 2: left multiplication k |-> g*k preserves normalized Haar measure.
  Its product with the identity of M preserves Haar times μ. Applying the
  original action pushforward gives the claimed equality. Finite measures
  justify the product-measure identities. Neither smoothness nor compactness
  of M, nor pre-existing invariance of μ, is assumed here. -/
  -- Translate only the Haar variable; the original measure on M is unchanged.
  let ν : Measure G := Measure.haarMeasure (⊤ : PositiveCompacts G)
  have hprod : Measure.map (Prod.map (fun k : G ↦ g * k) (id : M → M))
      (ν.prod μ) = ν.prod μ :=
    ((measurePreserving_mul_left ν g).prod (MeasurePreserving.id μ)).map_eq
  have hact : Measurable (fun p : G × M ↦ p.1 • p.2) := measurable_smul
  have htranslate : Measurable (Prod.map (fun k : G ↦ g * k) (id : M → M)) :=
    (measurable_const_mul g).prodMap measurable_id
  -- Associativity identifies the composed action with action after Haar translation.
  unfold averagedActionMeasure
  rw [Measure.map_map (measurable_const_smul g) hact]
  have hcompose : (fun x : M ↦ g • x) ∘ (fun p : G × M ↦ p.1 • p.2) =
      (fun p : G × M ↦ p.1 • p.2) ∘
        Prod.map (fun k : G ↦ g * k) (id : M → M) := by
    funext p
    exact (mul_smul g p.1 p.2).symm
  rw [hcompose, ← Measure.map_map hact htranslate]
  change Measure.map (fun p : G × M ↦ p.1 • p.2)
      (Measure.map (Prod.map (fun k : G ↦ g * k) (id : M → M)) (ν.prod μ)) = _
  rw [hprod]

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG) [ChartedSpace HG G]
  [hG : LieGroup IG ∞ G]
  {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hC : CompactSpace M]
  [hSmooth : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 3000000 in
-- The local Jacobian, parameter derivatives, and measure identities are kept in one proof.
include hG hM hT hC hSmooth in
/-- The actual compact action average of a positive smooth density is again positive and smooth. -/
theorem isSmoothPositiveMeasure_averagedActionMeasure
    (μ : Measure M) [hμ : IsSmoothPositiveMeasure (n := n) μ] :
    IsSmoothPositiveMeasure (n := n) (averagedActionMeasure G μ) := by
  /- Fixed-action diffeomorphisms provide the original chart densities. The existing
  inverse-action density family, evaluated at the inverse group parameter, identifies
  these same choices pointwise. Compact-parameter integration gives their positive smooth
  average; Tonelli identifies its measure with the specified action pushforward. -/
  classical
  let W := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, W)
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact W M
  let : ContinuousSMul G M := ⟨(contMDiff_smul (I := IG) (I' := I) (n := ∞)).continuous⟩
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let : ContMDiffMul 𝓘(ℝ, ℝ) ∞ ℝ := by
    constructor
    have hmul : ContDiff ℝ ∞ (fun p : ℝ × ℝ ↦ p.1 * p.2) := contDiff_mul
    exact hmul.contMDiff.comp (contMDiff_fst.prodMk_space contMDiff_snd)
  let η : Measure G := Measure.haarMeasure (⊤ : PositiveCompacts G)
  let e (g : G) : M ≃ₘ⟮I, I⟯ M := Diffeomorph.smul IG I ∞ g
  have hpush (g : G) : IsSmoothPositiveMeasure (n := n) (Measure.map (e g) μ) :=
    IsSmoothPositiveMeasure.map_diffeomorph μ (e g)
  constructor
  intro c hc
  have hcS := contMDiffOn_symm_of_mem_maximalAtlas
    (I := I) (n := (∞ : ℕ∞ω)) (IsManifold.subset_maximalAtlas hc)
  choose w hw using fun g : G ↦ (hpush g).exists_smooth_density c hc
  let θ (g : G) := Measure.map c ((Measure.map (e g) μ).restrict c.source)
  -- Use the existing inverse-action density theorem, with the original inverse parameter.
  obtain ⟨R, hR, hRpos, hRmeasure⟩ :=
    exists_smooth_inv_smul_density (n := n) (M := M) (G := G) IG μ
  obtain ⟨a, ha, hapos, hameasure⟩ := hμ.exists_smooth_density c hc
  have hmeasure (g : G) : Measure.map (e g) μ =
      μ.withDensity (fun x ↦ ENNReal.ofReal (R g⁻¹ x)) := by
    simpa only [Diffeomorph.smul_symm, inv_inv, e] using hRmeasure (g⁻¹)
  -- Push a chart weight through the same source-restricted measure.
  have hmapDensity (θ : Measure M) (f : M → W) (b : W → ENNReal)
      (hf : AEMeasurable f θ) (hb : AEMeasurable b (Measure.map f θ)) :
      (Measure.map f θ).withDensity b =
        Measure.map f (θ.withDensity (fun x ↦ b (f x))) := by
    ext A hA
    rw [withDensity_apply _ hA,
      Measure.map_apply_of_aemeasurable
        (hf.mono_ac (withDensity_absolutelyContinuous _ _)) hA,
      withDensity_apply₀ _ (hf.nullMeasurable hA),
      ← lintegral_indicator hA, ← lintegral_indicator₀ (hf.nullMeasurable hA)]
    rw [lintegral_map' (hb.indicator hA) hf]
    congr 1
  -- Equality of the exact chart measures identifies the originally selected w pointwise.
  have hlocal (g : G) : EqOn (w g)
      (fun z ↦ a z * R g⁻¹ (c.symm z)) c.target := by
    have hRg : ContMDiff I 𝓘(ℝ, ℝ) ∞ (R g⁻¹) :=
      hR.comp (contMDiff_const.prodMk contMDiff_id)
    have hr : ContDiffOn ℝ ∞ (fun z ↦ R g⁻¹ (c.symm z)) c.target :=
      (hRg.comp_contMDiffOn hcS).contDiffOn
    let b (z : W) := ENNReal.ofReal (R g⁻¹ (c.symm z))
    have hb : AEMeasurable b (volume.restrict c.target) :=
      (hr.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
    have hcA := c.continuousOn.aemeasurable (μ := μ) c.open_source.measurableSet
    have hm : θ g = (Measure.map c (μ.restrict c.source)).withDensity b := by
      dsimp only [θ]
      rw [hmeasure g, restrict_withDensity c.open_source.measurableSet,
        hmapDensity _ c b hcA (by
          rw [hameasure]
          exact hb.mono_ac (withDensity_absolutelyContinuous _ _))]
      congr 1
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_source.measurableSet] with x hx
      dsimp only [b]
      rw [c.left_inv hx]
    have heq : (volume.restrict c.target).withDensity
        (fun z ↦ ENNReal.ofReal (w g z)) =
        (volume.restrict c.target).withDensity
          (fun z ↦ ENNReal.ofReal (a z * R g⁻¹ (c.symm z))) := by
      rw [← (hw g).2.2]
      change θ g = _
      rw [hm, hameasure, ← withDensity_mul₀
        (ha.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal hb]
      apply withDensity_congr_ae
      filter_upwards [ae_restrict_mem c.open_target.measurableSet] with z hz
      exact (ENNReal.ofReal_mul (hapos z hz).le).symm
    have hae := (withDensity_eq_iff_of_sigmaFinite
      ((hw g).1.continuousOn.aemeasurable c.open_target.measurableSet).ennreal_ofReal
      ((ha.mul hr).continuousOn.aemeasurable
        c.open_target.measurableSet).ennreal_ofReal).mp heq
    apply Measure.eqOn_open_of_ae_eq (μ := (volume : Measure W)) _
      c.open_target (hw g).1.continuousOn (ha.mul hr).continuousOn
    filter_upwards [hae, ae_restrict_mem c.open_target.measurableSet] with z hz hzc
    have hh := congrArg ENNReal.toReal hz
    simpa only [ENNReal.toReal_ofReal ((hw g).2.1 z hzc).le,
      ENNReal.toReal_ofReal (mul_pos (hapos z hzc) (hRpos g⁻¹ (c.symm z))).le] using hh
  have hjoint : ContMDiffOn (IG.prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : G × W ↦ w p.1 p.2) (univ ×ˢ c.target) := by
    have hchart : ContMDiffOn (IG.prod I) I ∞
        (fun z : G × W ↦ c.symm z.2) (univ ×ˢ c.target) :=
      hcS.comp contMDiffOn_snd (fun _ hz ↦ hz.2)
    have hweight : ContMDiffOn (IG.prod I) 𝓘(ℝ, ℝ) ∞
        (fun z : G × W ↦ R z.1⁻¹ (c.symm z.2)) (univ ×ˢ c.target) :=
      hR.comp_contMDiffOn (contMDiffOn_fst.inv.prodMk hchart)
    have hdensity := (ha.contMDiffOn.comp contMDiffOn_snd
      (fun _ hz ↦ hz.2)).mul hweight
    exact hdensity.congr (fun z hz ↦ hlocal z.1 hz.2)
  let b (y : W) := ∫ g, w g y ∂η
  have hb : ContDiffOn ℝ ∞ b c.target :=
    contDiffOn_integral_of_compact_manifold IG η c.open_target hjoint
  have hwi (y : W) (hy : y ∈ c.target) : Integrable (fun g ↦ w g y) η := by
    have hcont : Continuous (fun g ↦ w g y) :=
      continuousOn_univ.mp (hjoint.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn (fun g _ ↦ ⟨mem_univ g, hy⟩))
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbpos (y : W) (hy : y ∈ c.target) : 0 < b y := by
    apply (integral_pos_iff_support_of_nonneg (fun g ↦ ((hw g).2.1 y hy).le) (hwi y hy)).mpr
    have hs : Function.support (fun g ↦ w g y) = univ := by
      ext g
      simp only [Function.mem_support, mem_univ, iff_true]
      exact ((hw g).2.1 y hy).ne'
    rw [hs]
    exact Measure.measure_univ_pos.mpr (NeZero.ne η)
  refine ⟨b, hb, hbpos, ?_⟩
  -- Tonelli identifies the averaged local density with the specified action pushforward.
  ext A hA
  have hpre : MeasurableSet (c ⁻¹' A ∩ c.source) := by
    simpa only [Set.domRestrict_eq, Set.preimage_comp,
      Set.image_preimage_eq_inter_range, Subtype.range_coe] using
      c.open_source.measurableSet.subtype_image
        (hA.preimage c.continuousOn.domRestrict.measurable)
  have haverage : (Measure.map c ((averagedActionMeasure G μ).restrict c.source)) A =
      ∫⁻ g, θ g A ∂η := by
    rw [Measure.map_apply_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) hA,
      Measure.restrict_apply' c.open_source.measurableSet]
    unfold averagedActionMeasure
    have hactm : Measurable (fun p : G × M ↦ p.1 • p.2) := measurable_smul
    rw [Measure.map_apply hactm hpre, Measure.prod_apply (hactm hpre)]
    apply lintegral_congr
    intro g
    dsimp only [θ]
    rw [Measure.map_apply_of_aemeasurable
      (c.continuousOn.aemeasurable c.open_source.measurableSet) hA,
      Measure.restrict_apply' c.open_source.measurableSet,
      Measure.map_apply (e g).continuous.measurable hpre]
    rfl
  rw [haverage, withDensity_apply _ hA, Measure.restrict_restrict hA]
  have hswap : (∫⁻ g, ∫⁻ y in A ∩ c.target, ENNReal.ofReal (w g y) ∂volume ∂η) =
      ∫⁻ y in A ∩ c.target, ∫⁻ g, ENNReal.ofReal (w g y) ∂η ∂volume := by
    apply lintegral_lintegral_swap
    have hj : AEMeasurable (fun p : G × W ↦ ENNReal.ofReal (w p.1 p.2))
        ((η.prod volume).restrict (univ ×ˢ (A ∩ c.target))) :=
      ((hjoint.continuousOn.mono (prod_mono Subset.rfl inter_subset_right)).aemeasurable
        (MeasurableSet.univ.prod (hA.inter c.open_target.measurableSet))).ennreal_ofReal
    change AEMeasurable (fun p : G × W ↦ ENNReal.ofReal (w p.1 p.2))
      (η.prod (volume.restrict (A ∩ c.target)))
    simpa only [← Measure.prod_restrict, Measure.restrict_univ] using hj
  calc
    _ = ∫⁻ g, ∫⁻ y in A ∩ c.target, ENNReal.ofReal (w g y) ∂volume ∂η := by
      apply lintegral_congr
      intro g
      change (Measure.map c ((Measure.map (e g) μ).restrict c.source)) A = _
      rw [(hw g).2.2, withDensity_apply _ hA, Measure.restrict_restrict hA]
    _ = ∫⁻ y in A ∩ c.target, ∫⁻ g, ENNReal.ofReal (w g y) ∂η ∂volume := hswap
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem (hA.inter c.open_target.measurableSet)] with y hy
      exact (ofReal_integral_eq_lintegral_ofReal (hwi y hy.2)
        (Filter.Eventually.of_forall (fun g ↦ ((hw g).2.1 y hy.2).le))).symm

include hG hM hT hC hSmooth in
/-- A smooth compact-group action on a compact manifold admits an invariant smooth density. -/
theorem exists_invariant_smoothPositiveMeasure :
    ∃ μ : Measure M, IsSmoothPositiveMeasure (n := n) μ ∧
      ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ := by
  let W := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, W)
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact W M
  let : ContinuousSMul G M :=
    ⟨(contMDiff_smul (I := IG) (I' := I) (n := ∞)).continuous⟩
  -- Start with the existing positive smooth density on the original Borel manifold.
  obtain ⟨μ, hμ⟩ := exists_smoothPositiveMeasure (n := n) (M := M)
  let : IsSmoothPositiveMeasure (n := n) μ := hμ
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  -- The same explicit average has both positive smoothness and Haar invariance.
  exact ⟨averagedActionMeasure G μ,
    isSmoothPositiveMeasure_averagedActionMeasure G IG μ,
    map_averagedActionMeasure G μ⟩

end AtiyahSinger
