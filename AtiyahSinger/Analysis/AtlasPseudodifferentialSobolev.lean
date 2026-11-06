/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasHomogeneousSymbol
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Analysis.Fredholm

import AtiyahSinger.Analysis.AtlasSobolevLocalization
import AtiyahSinger.Analysis.CompactQuantization
import AtiyahSinger.Analysis.TwoSidedCutoff

/-!
# Sobolev realizations on the original finite-rank atlases

Public module ID: M0293.

A10: every atlas PDO has a unique bounded extension between the specified
real-order atlas Sobolev completions, from order s to order s-m. The extension
agrees with its original smooth section action. Locally varying source and
target ranks remain independent, and no norm is added to the abstract fibers.

Each local Fourier piece is bounded using the original input localization
and an output plateau extension. The all-order smoothing remainder supplies
its own critical-order bound and may couple different components. Density
then gives existence and uniqueness on the same completions.

Source: SG III.3.17. The finite atlas adaptation is a project supplement of
the local Sobolev estimates. Elliptic parametrices, Fredholmness and smooth
kernel/cokernel comparisons are proved in AtlasPseudodifferentialFredholm,
using a specified homogeneous elliptic principal representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

variable {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
  (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)

set_option maxHeartbeats 1000000 in

/-- Every actual PDO extends uniquely to the critical pair of original Sobolev completions. -/
theorem existsUnique_sobolevExtension (s : ℝ) :
    ∃! T : L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - m),
      ∀ u : A.smoothSections,
        T (L.smoothToSobolev s u) = K.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- Stage 1: take the finite local Fourier representation of this P.
  Localize each piece with the original L and K cutoffs. The coordinate
  change estimates and the finite-dimensional local PDO bound control it
  from order s to order s-m. Overlapping frames can have their own ranks;
  their coordinate changes are genuine inverses, so no global rank is used.
  Stage 2: the actual all-order smoothing remainder has precisely such a
  bounded extension by its defining property. Add these bounded maps. The
  local sum agrees with P on each original smooth section, including any
  cross-component contribution of the remainder.
  Stage 3: extend across the dense smooth image in the actual completion.
  Equality on that dense image makes the continuous extension unique. This
  argument works for negative and zero orders and for zero-dimensional bases. -/
  classical
  -- Bound each specified piece before summing the original representation.
  have hpiece (R : AtlasPseudodifferentialPiece A B m) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u : A.smoothSections,
        ‖K.smoothToSobolev (s - m) (R.toLinearMap u)‖ ≤
          C * ‖L.smoothToSobolev s u‖ := by
    let X := EuclideanSpace ℝ (Fin n)
    let Vin := EuclideanSpace ℂ (Fin (A.rank R.input.frameIndex))
    let Vout := EuclideanSpace ℂ (Fin (B.rank R.output.frameIndex))
    -- Plateaus retain the original frames and are one near the existing cutoff supports.
    have plateau (K U : Set X) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
        ∃ χ : X → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
          tsupport χ ⊆ U ∧ K ⊆ interior {x | χ x = 1} := by
      obtain ⟨O, hOo, hKO, hOU, hOc⟩ :=
        exists_open_between_and_isCompact_closure hK hU hKU
      obtain ⟨O', hO'o, hOO', hO'U, hO'c⟩ :=
        exists_open_between_and_isCompact_closure hOc hU hOU
      obtain ⟨χ, hχ, _, hsχ, honeχ⟩ := exists_contDiff_support_eq_eq_one_iff
        (n := (⊤ : ℕ∞)) hO'o hOc.isClosed hOO'
      have hχsupport : tsupport χ = closure O' := congrArg closure hsχ
      refine ⟨χ, hχ, by simpa [HasCompactSupport, hχsupport] using hO'c,
        by rwa [hχsupport], ?_⟩
      intro x hx
      apply mem_interior.mpr
      refine ⟨O, ?_, hOo, hKO hx⟩
      intro y hy
      exact (honeχ y).mp (subset_closure hy)
    have hUi : IsOpen (R.chart.target ∩ R.chart.symm ⁻¹' (A.chart R.input.frameIndex).baseSet) :=
      R.chart.continuousOn_symm.isOpen_inter_preimage
        R.chart.open_target (A.chart R.input.frameIndex).open_baseSet
    have hUo : IsOpen (R.chart.target ∩ R.chart.symm ⁻¹' (B.chart R.output.frameIndex).baseSet) :=
      R.chart.continuousOn_symm.isOpen_inter_preimage
        R.chart.open_target (B.chart R.output.frameIndex).open_baseSet
    obtain ⟨ρ, hρ, hcρ, hρU, hρnear⟩ :=
      plateau _ _ R.input.compact_support hUi R.input.support_subset
    obtain ⟨σ, hσ, hcσ, hσU, hσnear⟩ :=
      plateau _ _ R.output.compact_support hUo R.output.support_subset
    have hρone (x : X) (hx : x ∈ tsupport R.input.cutoff) : ρ x = 1 :=
      (interior_subset (s := {x | ρ x = 1})) (hρnear hx)
    have hσone (x : X) (hx : x ∈ tsupport R.output.cutoff) : σ x = 1 :=
      (interior_subset (s := {x | σ x = 1})) (hσnear hx)
    let D : AtlasChartCutoff B R.chart :=
      { R.output with cutoff := σ
                      smooth_cutoff := hσ
                      compact_support := hcσ
                      support_subset := hσU }
    -- Only the original output cutoff appears in the compact symbol; the input plateau is neutral.
    let p := cutoffSymbol R.output.cutoff ρ R.symbol
    have hp : IsSymbol univ m p := isSymbol_cutoffSymbol m R.symbol R.isSymbol _ _
      R.output.smooth_cutoff hρ R.output.compact_support hcρ
    have hcp : HasCompactSupport p := hasCompactSupport_amplitudeSymbol _
      (hasCompactSupport_cutoffAmplitude R.symbol _ _ R.output.compact_support hcρ)
    let T := quantizeSobolev m s p hp hcp
    have hρgrowth : (fun x ↦ (ρ x : ℂ)).HasTemperateGrowth :=
      (hcρ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hρ)
    have hχgrowth : (fun x ↦ (R.output.cutoff x : ℂ)).HasTemperateGrowth :=
      (R.output.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp R.output.smooth_cutoff)
    let v (u : A.smoothSections) : 𝓢(X, Vin) :=
      R.input.localize R.chart_mem_atlas u
    let w (u : A.smoothSections) : 𝓢(X, Vout) :=
      SchwartzMap.smulLeftCLM Vout (fun x ↦ (R.output.cutoff x : ℂ)) (R.operator (v u))
    have hwin (u : A.smoothSections) :
        SchwartzMap.smulLeftCLM Vin (fun x ↦ (ρ x : ℂ)) (v u) = v u := by
      apply DFunLike.ext
      intro x
      rw [SchwartzMap.smulLeftCLM_apply_apply hρgrowth]
      by_cases hx : x ∈ tsupport R.input.cutoff
      · rw [hρone x hx, Complex.ofReal_one, one_smul]
      · have hvzero : v u x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ hx ((R.input.localizedFunction_properties R.chart_mem_atlas u).2.1 h))
        rw [hvzero, smul_zero]
    have hwout (u : A.smoothSections) (x : X) :
        w u x = (R.output.cutoff x : ℂ) • R.operator (v u) x :=
      SchwartzMap.smulLeftCLM_apply_apply hχgrowth _ x
    have hquant (u : A.smoothSections) (x : X) :
        quantize p (v u) x = w u x := by
      rw [show p = cutoffSymbol R.output.cutoff ρ R.symbol from rfl,
        quantize_cutoffSymbol m R.symbol R.isSymbol _ _
          R.output.smooth_cutoff hρ R.output.compact_support hcρ, hwin, ← R.operator_apply,
        hwout, Complex.coe_smul]
    -- The named Euclidean Sobolev quantizer has precisely this Schwartz output.
    have hT (u : A.smoothSections) :
        T (schwartzSobolevCoordinate s (v u)) = schwartzSobolevCoordinate (s - m) (w u) := by
      apply besselRealization_injective n (B.rank R.output.frameIndex) (s - m)
      ext1 φ
      rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
        SchwartzMap.coe_apply]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [hquant]
    -- The extension plateau removes the outer support boundary without squaring its cutoff.
    have hreconstruct (u : A.smoothSections) :
        D.extend R.chart_mem_atlas (w u) = R.toLinearMap u := by
      apply Subtype.ext
      funext x
      change D.extendedFunction (w u) x = R.output.extendedFunction (R.operator (v u)) x
      by_cases hx : x ∈ R.chart.source ∩ (B.chart R.output.frameIndex).baseSet
      · simp only [AtlasChartCutoff.extendedFunction, D, dite_eq_left hx]
        change (σ (R.chart x) : ℂ) • (B.frameLinearEquiv R.output.frameIndex x hx.2).symm
          ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ) (w u (R.chart x))) =
            (R.output.cutoff (R.chart x) : ℂ) •
              (B.frameLinearEquiv R.output.frameIndex x hx.2).symm
                ((EuclideanSpace.equiv (Fin (B.rank R.output.frameIndex)) ℂ)
                  (R.operator (v u) (R.chart x)))
        rw [hwout, map_smul, map_smul, smul_smul]
        by_cases hz : R.chart x ∈ tsupport R.output.cutoff
        · rw [hσone _ hz, Complex.ofReal_one, one_mul]
        · simp only [image_eq_zero_of_notMem_tsupport hz, Complex.ofReal_zero, mul_zero,
            zero_smul]
      · simp only [AtlasChartCutoff.extendedFunction, D, dite_eq_right hx]
    -- Compose the actual input, compact quantizer and plateau-extension estimates.
    obtain ⟨Ci, hCi, hinput⟩ :=
      R.input.exists_norm_localize_sobolev_le R.chart_mem_atlas L s
    obtain ⟨Co, hCo, houtput⟩ :=
      D.exists_norm_extend_sobolev_le R.chart_mem_atlas K (s - m)
    refine ⟨Co * ‖T‖ * Ci, mul_nonneg (mul_nonneg hCo (norm_nonneg T)) hCi, ?_⟩
    intro u
    rw [← hreconstruct]
    calc
      _ ≤ Co * ‖schwartzSobolevCoordinate (s - m) (w u)‖ := houtput (w u)
      _ = Co * ‖T (schwartzSobolevCoordinate s (v u))‖ := by rw [hT]
      _ ≤ Co * (‖T‖ * ‖schwartzSobolevCoordinate s (v u)‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm _) hCo
      _ ≤ Co * (‖T‖ * (Ci * ‖L.smoothToSobolev s u‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hinput u) (norm_nonneg T)) hCo
      _ = _ := by ring
  -- The actual all-order remainder supplies the same critical-order map.
  obtain ⟨N, R, hR⟩ := P.isPseudodifferentialOperator
  choose C hC hb using fun j ↦ hpiece (R j)
  obtain ⟨T₀, hT₀⟩ := hR L K s (s - m)
  let Ctotal := (∑ j, C j) + ‖T₀‖
  have hdecomp : P.toLinearMap = (∑ j, (R j).toLinearMap) +
      (P.toLinearMap - ∑ j, (R j).toLinearMap) := by abel
  have hbound (u : A.smoothSections) :
      ‖K.smoothToSobolev (s - m) (P.toLinearMap u)‖ ≤
        Ctotal * ‖L.smoothToSobolev s u‖ := by
    have hzero : ‖K.smoothToSobolev (s - m)
        ((P.toLinearMap - ∑ j, (R j).toLinearMap) u)‖ ≤
        ‖T₀‖ * ‖L.smoothToSobolev s u‖ := by
      rw [← hT₀]
      exact T₀.le_opNorm _
    conv_lhs => rw [hdecomp]
    rw [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum]
    calc
      _ ≤ ‖∑ j, K.smoothToSobolev (s - m) ((R j).toLinearMap u)‖ +
          ‖K.smoothToSobolev (s - m) ((P.toLinearMap - ∑ j, (R j).toLinearMap) u)‖ :=
        norm_add_le _ _
      _ ≤ (∑ j, ‖K.smoothToSobolev (s - m) ((R j).toLinearMap u)‖) +
          ‖T₀‖ * ‖L.smoothToSobolev s u‖ := add_le_add (norm_sum_le _ _) hzero
      _ ≤ (∑ j, C j * ‖L.smoothToSobolev s u‖) + ‖T₀‖ * ‖L.smoothToSobolev s u‖ :=
        add_le_add (Finset.sum_le_sum fun j _ ↦ hb j u) le_rfl
      _ = _ := by rw [← Finset.sum_mul, ← add_mul]
  -- Extend this same action from the dense smooth image; density also gives uniqueness.
  let f := (K.smoothToSobolev (s - m)).comp P.toLinearMap
  let T : L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - m) :=
    f.extendOfNorm (L.smoothToSobolev s)
  have hT (u : A.smoothSections) :
      T (L.smoothToSobolev s u) = K.smoothToSobolev (s - m) (P.toLinearMap u) :=
    LinearMap.extendOfNorm_eq (L.denseRange_smoothToSobolev s) ⟨Ctotal, hbound⟩ u
  refine ⟨T, hT, ?_⟩
  intro R hR
  apply DFunLike.coe_injective
  apply (L.denseRange_smoothToSobolev s).equalizer R.continuous T.continuous
  funext u
  exact (hR u).trans (hT u).symm

/-- The unique continuous extension of the original atlas section action. -/
def sobolevExtension (s : ℝ) : L.SobolevSpace s →L[ℂ] K.SobolevSpace (s - m) :=
  (P.existsUnique_sobolevExtension L K s).exists.choose

/-- The chosen extension retains the same original section and the same PDO output. -/
theorem sobolevExtension_smoothToSobolev (s : ℝ) (u : A.smoothSections) :
    P.sobolevExtension L K s (L.smoothToSobolev s u) =
      K.smoothToSobolev (s - m) (P.toLinearMap u) := by
  /- Use the exact defining property of the chosen extension. This is the
  compatibility needed by all subsequent kernel and quotient comparisons;
  it does not replace P by a separately chosen representative. -/
  exact (P.existsUnique_sobolevExtension L K s).exists.choose_spec u

end AtlasPseudodifferentialOperator

end AtiyahSinger
