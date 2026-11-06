/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGlobalSymbolTopology
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Analysis.AtlasQuantization

import AtiyahSinger.Analysis.AtlasSobolevLocalization
import AtiyahSinger.Analysis.QuantizationBounds

/-!
# Operator-norm continuity of the fixed atlas quantizer

Public module ID: M0273.

A03: a single finite quantization presentation, two specified Sobolev
presentations and two real orders are fixed before choosing the full symbol.
The original coordinate Fourier quantizer extends to a continuous linear map
from the existing atlas symbol seminorm topology to bounded Sobolev operators.
Its finite-seminorm estimate is uniform in the symbol and therefore in a
parameter family. Locally varying source and target ranks remain independent.

Sources: SG III.3.2 and III.3.17, pp.178--179 and 186--187. The finite-chart
assembly makes the local estimate uniform for these fixed choices. A family
must be continuous in the weighted derivative topology; pointwise continuity
or joint smoothness on bounded frequency sets alone is insufficient. No
ellipticity or Fredholm premise is needed for the boundedness and continuity.
The uniform estimate and complex linearity retain the same coordinate quantizer.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff NNReal Topology

set_option maxSynthPendingDepth 25

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

-- Every source continuity assertion uses the actual weighted derivative topology.
attribute [local instance] atlasGlobalSymbolTopology

namespace AtlasQuantizationPresentation

variable (C : AtlasQuantizationPresentation A B)
  (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B) (s m : ℝ)

include hM hT hSC hC

/-- The original quantizer followed by its unique Sobolev extension is complex-linear. -/
theorem isLinearMap_sobolevQuantization :
    IsLinearMap ℂ (fun p : atlasGlobalSymbolSpace A B m ↦
      (C.quantize p).sobolevExtension L K s) := by
  /- Stage 1: the fixed quantizationLinearMap preserves addition and complex
  scalar multiplication on the original smooth sections. Keep every local
  chart, frame, cutoff and Fourier map in C unchanged in these identities.
  Stage 2: use the defining smooth-section action of the Sobolev extensions
  and linearity of the same smoothToSobolev inclusions. The resulting equalities
  hold on the dense smooth image in L.SobolevSpace s, hence on the whole space
  by continuity into K.SobolevSpace (s-m). This proves both linearity laws for
  the displayed original bounded operators, including their lower-order terms. -/
  constructor
  · intro p q
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      ((C.quantize (p + q)).sobolevExtension L K s).continuous
      (((C.quantize p).sobolevExtension L K s) +
        ((C.quantize q).sobolevExtension L K s)).continuous
    funext u
    simp only [Function.comp_apply, add_apply,
      AtlasPseudodifferentialOperator.sobolevExtension_smoothToSobolev]
    change K.smoothToSobolev (s - m) ((C.quantizationLinearMap m (p + q)) u) = _
    rw [map_add, LinearMap.add_apply, map_add]
    rfl
  · intro z p
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev s).equalizer
      ((C.quantize (z • p)).sobolevExtension L K s).continuous
      (z • ((C.quantize p).sobolevExtension L K s)).continuous
    funext u
    simp only [Function.comp_apply, smul_apply,
      AtlasPseudodifferentialOperator.sobolevExtension_smoothToSobolev]
    change K.smoothToSobolev (s - m) ((C.quantizationLinearMap m (z • p)) u) = _
    rw [map_smul, LinearMap.smul_apply, map_smul]
    rfl

/-- Fixed full-symbol quantization into the actual critical Sobolev operator space. -/
def sobolevQuantizationLinearMap :
    atlasGlobalSymbolSpace A B m →ₗ[ℂ]
      (L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - m)) :=
  IsLinearMap.mk' (fun p ↦ (C.quantize p).sobolevExtension L K s)
    (C.isLinearMap_sobolevQuantization L K s m)

/-- Finitely many weighted derivative seminorms uniformly bound this fixed quantizer. -/
theorem exists_sobolevQuantization_seminorm_bound :
    ∃ (J : Finset (AtlasGlobalSymbolSeminormIndex A B)) (c : ℝ≥0),
      ∀ p : atlasGlobalSymbolSpace A B m,
        ‖C.sobolevQuantizationLinearMap L K s m p‖ ≤
          (c : ℝ) * (J.sup (atlasGlobalSymbolSeminorm A B m)) p := by
  /- Stage 1: apply the local Fourier/Schur estimate to the actual cutoff
  coordinate symbol in each patch of C. For the fixed real orders s and m,
  integration by parts uses finitely many spatial and frequency derivatives.
  The cutoff supports lie in compact subsets of the same valid chart/frame
  domains, so the required bounds are original atlas symbol seminorms.
  Stage 2: pass between these coordinate estimates and the fixed L and K
  Sobolev presentations. The finitely many smooth chart and frame transitions,
  and all cutoffs, contribute constants independent of p. Each local estimate
  uses that patch's source and target ranks; no global equality is required.
  Stage 3: sum the finite estimates and absorb their finite sum into a
  nonnegative multiple of a finite supremum. Thus J and c are chosen before
  p. Empty presentations give zero maps and allow the empty J. Dimension zero
  and rank-zero frames obey the same estimate without nonemptiness premises. -/
  classical
  -- Each fixed patch retains its original localization, coordinate symbol and extension.
  have hpatch (Q : AtlasQuantizationPatch A B) :
      ∃ (J : Finset (AtlasGlobalSymbolSeminormIndex A B))
        (c : ℝ≥0), ∀ (p : atlasGlobalSymbolSpace A B m)
        (u : A.smoothSections),
          ‖K.smoothToSobolev (s - m) ((Q.toPiece p).toLinearMap u)‖ ≤
            (c : ℝ) * (J.sup (atlasGlobalSymbolSeminorm A B m)) p *
              ‖L.smoothToSobolev s u‖ := by
    let U := atlasSymbolChartDomain A B Q.chart Q.input.frameIndex Q.output.frameIndex
    have hU : IsOpen U :=
      isOpen_atlasSymbolChartDomain A B Q.chart Q.input.frameIndex Q.output.frameIndex
    obtain ⟨J, c, hc⟩ := exists_quantizeSchwartz_zeroExtendedSymbol_seminorm_bound
      (r := A.rank Q.input.frameIndex) (q := B.rank Q.output.frameIndex)
      U hU m s Q.input.cutoff Q.input.smooth_cutoff Q.input.compact_support
      (fun z hz ↦ ⟨Q.input.support_subset hz, Q.input_support_in_output_frame hz⟩)
    let index (j : SymbolSeminormIndex U) :
        AtlasGlobalSymbolSeminormIndex A B :=
      { chart := Q.chart
        mem_atlas := Q.chart_mem_atlas
        inputIndex := Q.input.frameIndex
        outputIndex := Q.output.frameIndex
        localIndex := j }
    let J' := J.image index
    obtain ⟨Ci, hCi, hinput⟩ :=
      Q.input.exists_norm_localize_sobolev_le Q.chart_mem_atlas L s
    obtain ⟨Co, hCo, houtput⟩ :=
      Q.output.exists_norm_extend_sobolev_le Q.chart_mem_atlas K (s - m)
    refine ⟨J', ⟨Co * (c : ℝ) * Ci, mul_nonneg (mul_nonneg hCo c.coe_nonneg) hCi⟩, ?_⟩
    intro p u
    let localP : symbolSpace U hU m (A.rank Q.input.frameIndex) (B.rank Q.output.frameIndex) :=
      ⟨atlasGlobalSymbolInChart A B p.val Q.chart Q.input.frameIndex Q.output.frameIndex,
        p.property Q.chart Q.chart_mem_atlas Q.input.frameIndex Q.output.frameIndex⟩
    have hsup : (J.sup (symbolSeminorm hU m)) localP ≤
        (J'.sup (atlasGlobalSymbolSeminorm A B m)) p := by
      apply Seminorm.finset_sup_apply_le
      · exact apply_nonneg _ p
      · intro j hj
        change atlasGlobalSymbolSeminorm A B m (index j) p ≤ _
        exact Seminorm.le_finset_sup_apply (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    let v := Q.input.localize Q.chart_mem_atlas u
    let w := (Q.toPiece p).operator v
    have hlocal : ‖schwartzSobolevCoordinate (s - m) w‖ ≤
        (c : ℝ) * (J'.sup (atlasGlobalSymbolSeminorm A B m)) p *
          ‖schwartzSobolevCoordinate s v‖ := by
      exact (hc localP v).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsup c.coe_nonneg)
          (norm_nonneg _))
    change ‖K.smoothToSobolev (s - m) (Q.output.extend Q.chart_mem_atlas w)‖ ≤ _
    calc
      _ ≤ Co * ‖schwartzSobolevCoordinate (s - m) w‖ := houtput w
      _ ≤ Co * ((c : ℝ) * (J'.sup (atlasGlobalSymbolSeminorm A B m)) p *
          ‖schwartzSobolevCoordinate s v‖) := mul_le_mul_of_nonneg_left hlocal hCo
      _ ≤ Co * ((c : ℝ) * (J'.sup (atlasGlobalSymbolSeminorm A B m)) p *
          (Ci * ‖L.smoothToSobolev s u‖)) := by
        gcongr
        exact hinput u
      _ = _ := by
        change Co * ((c : ℝ) * (J'.sup (atlasGlobalSymbolSeminorm A B m)) p *
          (Ci * ‖L.smoothToSobolev s u‖)) =
            (Co * (c : ℝ) * Ci) * (J'.sup (atlasGlobalSymbolSeminorm A B m)) p *
              ‖L.smoothToSobolev s u‖
        ring
  choose J c hc using fun j ↦ hpatch (C.patch j)
  let S : Finset (AtlasGlobalSymbolSeminormIndex A B) :=
    Finset.univ.biUnion J
  refine ⟨S, ∑ j, c j, ?_⟩
  intro p
  let b : ℝ := (S.sup (atlasGlobalSymbolSeminorm A B m)) p
  have hb : 0 ≤ b := apply_nonneg _ p
  have hsup (j : Fin C.size) : (J j).sup (atlasGlobalSymbolSeminorm A B m) p ≤ b := by
    apply Seminorm.finset_sup_apply_le hb
    intro k hk
    exact Seminorm.le_finset_sup_apply (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hk⟩)
  -- The finite-sum bound on smooth sections extends to the whole Sobolev domain.
  have hsmooth (u : A.smoothSections) :
      ‖C.sobolevQuantizationLinearMap L K s m p (L.smoothToSobolev s u)‖ ≤
        ((∑ j, c j : ℝ≥0) : ℝ) * b * ‖L.smoothToSobolev s u‖ := by
    change ‖(C.quantize p).sobolevExtension L K s (L.smoothToSobolev s u)‖ ≤ _
    rw [AtlasPseudodifferentialOperator.sobolevExtension_smoothToSobolev]
    change ‖K.smoothToSobolev (s - m) ((∑ j, ((C.patch j).toPiece p).toLinearMap) u)‖ ≤ _
    rw [LinearMap.sum_apply, map_sum]
    calc
      _ ≤ ∑ j, ‖K.smoothToSobolev (s - m) (((C.patch j).toPiece p).toLinearMap u)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ j, (c j : ℝ) * (J j).sup (atlasGlobalSymbolSeminorm A B m) p *
          ‖L.smoothToSobolev s u‖ := Finset.sum_le_sum (fun j _ ↦ hc j p u)
      _ ≤ ∑ j, (c j : ℝ) * b * ‖L.smoothToSobolev s u‖ := by
        gcongr with j hj
        exact hsup j
      _ = _ := by simp only [← Finset.sum_mul, NNReal.coe_sum]
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (NNReal.coe_nonneg _) hb)
  intro u
  exact (L.denseRange_smoothToSobolev s).induction_on u
    (isClosed_le (C.sobolevQuantizationLinearMap L K s m p).continuous.norm
      (continuous_const.mul continuous_norm)) hsmooth

/-- The same linear quantizer is continuous for the specified symbol and operator topologies. -/
theorem continuous_sobolevQuantizationLinearMap :
    Continuous (C.sobolevQuantizationLinearMap L K s m) := by
  /- Apply the seminorm continuity criterion to the preceding uniform bound
  and withSeminorms_atlasGlobalSymbolTopology. Its codomain seminorm is the
  actual operator norm on H^s to H^(s-m); every source seminorm is measured
  on the unchanged full symbol in the original charts. The fixed linearity
  turns the same estimate into a bound on differences of any two symbols. -/
  obtain ⟨J, c, hc⟩ := C.exists_sobolevQuantization_seminorm_bound L K s m
  apply WithSeminorms.continuous_normedSpace_rng _
    (withSeminorms_atlasGlobalSymbolTopology A B m)
  exact ⟨J, c, hc⟩

/-- The original fixed quantization with its proven symbol-topology continuity certificate. -/
def sobolevQuantizationCLM :
    atlasGlobalSymbolSpace A B m →L[ℂ]
      (L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - m)) where
  toLinearMap := C.sobolevQuantizationLinearMap L K s m
  cont := C.continuous_sobolevQuantizationLinearMap L K s m

/-- A continuous full-symbol family gives a norm-continuous family of these same quantized PDOs. -/
theorem continuous_sobolevQuantization {Z : Type*} [TopologicalSpace Z]
    (p : Z → atlasGlobalSymbolSpace A B m) (hp : Continuous p) :
    Continuous (fun z ↦ (C.quantize (p z)).sobolevExtension L K s) := by
  /- Compose hp with the continuous fixed quantization map. Its defining
  function is exactly the unique Sobolev extension of C.quantize, so no new
  operator representative is chosen at a parameter. The quantization data,
  the two Sobolev presentations and both real orders remain fixed throughout.
  The parameter space need not be compact, finite dimensional or smooth;
  its hypothesis is continuity in all actual weighted derivative seminorms. -/
  exact (C.continuous_sobolevQuantizationLinearMap L K s m).comp hp

end AtlasQuantizationPresentation

end AtiyahSinger
