/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.OpenOperatorRefinement

/-!
# Refinement of native pieces without a source density

Public module ID: M0355.

A finite coordinate partition is absorbed into the two cutoffs of the original
piece. Its chart, frames, full symbol and uncut operator remain the specified
ones. The exact global leading-symbol sum and the compact smoothing remainder
therefore concern the same finite family. No compactness or measure on the base
is needed. This is the local partition argument in SG III.3, used for open
transport before introducing the density on the target manifold.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold SchwartzMap Topology

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

namespace PseudodifferentialPiece

variable {m : ℝ} (L : PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)

/-- Absorb coordinate multipliers while retaining the original native chart and frames.
This adapter identifies the native pieces in the coordinate refinement theorem. -/
def coordinateCutoff (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hρ : ContDiff ℝ ∞ ρ) :
    PseudodifferentialPiece (n := n) (r := r) (q := q) E F m :=
  { L with
    input := { L.input with
      cutoff := fun z ↦ L.input.cutoff z * ρ z
      smooth_cutoff := L.input.smooth_cutoff.mul hρ
      compact_support := L.input.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans L.input.support_subset }
    output := { L.output with
      cutoff := fun z ↦ L.output.cutoff z * χ z
      smooth_cutoff := L.output.smooth_cutoff.mul hχ
      compact_support := L.output.compact_support.of_isClosed_subset isClosed_closure
        tsupport_mul_subset_left
      support_subset := tsupport_mul_subset_left.trans L.output.support_subset }
    input_support_in_output_frame :=
      tsupport_mul_subset_left.trans L.input_support_in_output_frame
    output_support_in_input_frame :=
      tsupport_mul_subset_left.trans L.output_support_in_input_frame }

/-- Native coordinate cutoffs realize exactly the same two-sided Schwartz operator. -/
theorem coordinateOperator_coordinateCutoff (χ ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hρ : ContDiff ℝ ∞ ρ)
    (hcχ : HasCompactSupport χ) (hcρ : HasCompactSupport ρ) :
    (L.coordinateCutoff χ ρ hχ hρ).coordinateOperator =
      ((SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q))
        (fun z ↦ (χ z : ℂ))).comp L.coordinateOperator).comp
          (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
            (fun z ↦ (ρ z : ℂ))) := by
  have hg (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ ∞ f)
      (hcf : HasCompactSupport f) : (fun z ↦ (f z : ℂ)).HasTemperateGrowth :=
    (hcf.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hf)
  apply ContinuousLinearMap.ext
  intro u
  apply SchwartzMap.ext
  intro z
  -- The two input multipliers commute pointwise inside the same original operator.
  have hin : SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
      (fun y ↦ ((L.input.cutoff y * ρ y : ℝ) : ℂ)) u =
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun y ↦ (L.input.cutoff y : ℂ))
          (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
            (fun y ↦ (ρ y : ℂ)) u) := by
    apply SchwartzMap.ext
    intro y
    rw [SchwartzMap.smulLeftCLM_apply_apply
      (hg _ (L.input.smooth_cutoff.mul hρ)
        (L.input.compact_support.of_isClosed_subset isClosed_closure
          tsupport_mul_subset_left)),
      SchwartzMap.smulLeftCLM_apply_apply
        (hg _ L.input.smooth_cutoff L.input.compact_support),
      SchwartzMap.smulLeftCLM_apply_apply (hg _ hρ hcρ), Complex.ofReal_mul, mul_smul]
  simp only [ContinuousLinearMap.comp_apply]
  rw [coordinateOperator_apply,
    SchwartzMap.smulLeftCLM_apply_apply (hg _ hχ hcχ), L.coordinateOperator_apply]
  change (L.output.cutoff z * χ z) • L.operator
    (SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
      (fun y ↦ ((L.input.cutoff y * ρ y : ℝ) : ℂ)) u) z = _
  rw [hin, mul_smul, smul_comm]
  rfl

/-- A common pair of coordinate plateaus reconstructs the exact native section map.
The same plateaus can be used for every refined piece whose supports shrink. -/
theorem extend_coordinateOperator_localize
    (A : BundleChartCutoff (r := r) E L.chart)
    (B : BundleChartCutoff (r := q) F L.chart)
    (hA : A.frame = L.input.frame) (hB : B.frame = L.output.frame)
    (hAone : ∀ z ∈ tsupport L.input.cutoff, A.cutoff z = 1)
    (hBone : ∀ z ∈ tsupport L.output.cutoff, B.cutoff z = 1) :
    (B.extendLinearMap L.chart_mem_atlas).comp
      (L.coordinateOperator.toLinearMap.comp (A.localizeLinearMap L.chart_mem_atlas)) =
        L.toLinearMap := by
  have hg : (fun z ↦ (L.input.cutoff z : ℂ)).HasTemperateGrowth :=
    (L.input.compact_support.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp L.input.smooth_cutoff)
  -- The input plateau cancels on precisely the original input support.
  have hinput (u : smoothSections (n := n) (r := r) E) :
      SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun z ↦ (L.input.cutoff z : ℂ)) (A.localize L.chart_mem_atlas u) =
          L.input.localize L.chart_mem_atlas u := by
    apply SchwartzMap.ext
    intro z
    rw [SchwartzMap.smulLeftCLM_apply_apply hg]
    change (L.input.cutoff z : ℂ) • A.localizedFunction u z = L.input.localizedFunction u z
    by_cases hz : z ∈ tsupport L.input.cutoff
    · have hzt := (L.input.support_subset hz).1
      simp only [BundleChartCutoff.localizedFunction, hzt, ↓reduceIte, hA]
      rw [hAone z hz, Complex.ofReal_one, one_smul]
    · simp [BundleChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hz]
  -- The output plateau cancels after the same full coordinate operator is applied.
  apply LinearMap.ext
  intro u
  apply Subtype.ext
  funext x
  change B.extendedFunction (L.coordinateOperator (A.localize L.chart_mem_atlas u)) x =
    L.output.extendedFunction (L.operator (L.input.localize L.chart_mem_atlas u)) x
  by_cases hx : x ∈ L.chart.source
  · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte, hB]
    rw [L.coordinateOperator_apply, hinput, ← Complex.coe_smul, map_smul, smul_smul]
    by_cases hz : L.chart x ∈ tsupport L.output.cutoff
    · rw [hBone _ hz, Complex.ofReal_one, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  · simp only [BundleChartCutoff.extendedFunction, hx, ↓reduceIte]

/-- A native piece refines over any cover with exact symbol sum and compact coordinate error.
The existential multipliers specify the same native family in every conclusion. -/
theorem exists_coordinate_refinement {ι : Type*} (U : ι → Set M)
    (hU : ∀ i, IsOpen (U i))
    (hcover : L.chart.symm '' (tsupport L.output.cutoff ∪ tsupport L.input.cutoff) ⊆
      ⋃ i, U i) :
    ∃ (N : ℕ) (a : Fin N → ι) (χ ρ : Fin N → EuclideanSpace ℝ (Fin n) → ℝ)
      (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)),
      let R := fun j ↦ L.coordinateCutoff (χ j) (ρ j) (hχ j) (hρ j)
      (∑ j, (R j).globalSymbol) = L.globalSymbol ∧
      (∀ j, (R j).chart.symm ''
        (tsupport (R j).output.cutoff ∪ tsupport (R j).input.cutoff) ⊆ U (a j)) ∧
      HasCompactSmoothingSchwartzSymbol
        (L.coordinateOperator - ∑ j, (R j).coordinateOperator) ∧
      HasOperatorSupport (tsupport L.output.cutoff ∪ tsupport L.input.cutoff)
        (L.coordinateOperator - ∑ j, (R j).coordinateOperator) := by
  classical
  let K := tsupport L.output.cutoff ∪ tsupport L.input.cutoff
  have hK : IsCompact K := L.output.compact_support.union L.input.compact_support
  let W (i : ι) := L.chart.target ∩ L.chart.symm ⁻¹' U i
  have hW (i : ι) : IsOpen (W i) := L.chart.isOpen_inter_preimage_symm (hU i)
  have hKW : K ⊆ ⋃ i, W i := by
    intro z hz
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover ⟨z, hz, rfl⟩)
    refine Set.mem_iUnion.mpr ⟨i, ?_, hi⟩
    rcases hz with hz | hz
    · exact (L.output.support_subset hz).1
    · exact (L.input.support_subset hz).1
  -- The actual compact coordinate operator has its original exact reduced full symbol.
  let p := cutoffSymbol L.output.cutoff L.input.cutoff L.symbol
  have hp : IsSymbol Set.univ m p := isSymbol_cutoffSymbol m L.symbol L.isSymbol _ _
    L.output.smooth_cutoff L.input.smooth_cutoff
    L.output.compact_support L.input.compact_support
  have hcp : HasCompactSupport p := hK.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_symbol_subset_of_hasOperatorSupport m p hp L.coordinateOperator
      L.coordinateOperator_eq_quantize K hK.isClosed L.hasOperatorSupport_coordinateOperator)
  have hP : HasCompactSchwartzSymbol m L.coordinateOperator := by
    refine ⟨p, hp, hcp, ?_⟩
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro z
    rw [L.coordinateOperator_eq_quantize, quantizeSchwartz_apply]
  obtain ⟨N, a, χ, ρ, Q, hQ, herror, hsupport, hsum⟩ :=
    hP.exists_refinement K hK L.hasOperatorSupport_coordinateOperator W hW hKW
  let R (j : Fin N) := L.coordinateCutoff (χ j) (ρ j) (hQ j).1 (hQ j).2.2.1
  have hRQ (j : Fin N) : (R j).coordinateOperator = Q j :=
    (L.coordinateOperator_coordinateCutoff (χ j) (ρ j) (hQ j).1 (hQ j).2.2.1
      (hQ j).2.1 (hQ j).2.2.2.1).trans (hQ j).2.2.2.2.2.2.1.symm
  have hprod (j : Fin N) (z : EuclideanSpace ℝ (Fin n)) : χ j z * ρ j z = χ j z := by
    by_cases hz : χ j z = 0
    · simp [hz]
    · rw [show ρ j z = 1 from
        interior_subset (s := {z | ρ j z = 1})
          ((hQ j).2.2.2.2.2.1 (subset_tsupport _ hz)), mul_one]
  -- The same partition gives the exact leading-symbol sum, not just an order comparison.
  have hsymbol (j : Fin N) (x : M) (ξ) :
      (R j).globalSymbolFunction x ξ =
        (χ j (L.chart x) : ℂ) • L.globalSymbolFunction x ξ := by
    by_cases hx : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
    · dsimp only [R, coordinateCutoff, globalSymbolFunction]
      rw [ite_eq_left hx, ite_eq_left hx, smul_smul]
      congr 1
      calc
        _ = ((χ j (L.chart x) * ρ j (L.chart x) : ℝ) : ℂ) *
            ((L.output.cutoff (L.chart x) * L.input.cutoff (L.chart x) : ℝ) : ℂ) := by
          push_cast
          ring
        _ = _ := by rw [hprod]
    · simp [R, coordinateCutoff, globalSymbolFunction, hx]
  refine ⟨N, a, χ, ρ, fun j ↦ (hQ j).1, fun j ↦ (hQ j).2.2.1, ?_, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Submodule.coe_sum]
    change (∑ j, (R j).globalSymbolFunction) = L.globalSymbolFunction
    funext x ξ
    simp only [Finset.sum_apply, hsymbol]
    by_cases hx : L.chart x ∈ K
    · rw [← Finset.sum_smul, ← Complex.ofReal_sum, hsum _ hx,
        Complex.ofReal_one, one_smul]
    · have hz : L.globalSymbolFunction x ξ = 0 := by
        by_cases hxd : x ∈ L.chart.source ∩ L.input.frame.baseSet ∩ L.output.frame.baseSet
        · have ho : L.output.cutoff (L.chart x) = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h ↦ hx (Or.inl h))
          simp [globalSymbolFunction, hxd, ho]
        · simp [globalSymbolFunction, hxd]
      simp [hz]
  · intro j x hx
    rcases hx with ⟨z, hz | hz, rfl⟩
    · exact ((hQ j).2.2.2.2.1 (Or.inl (tsupport_mul_subset_right hz))).2
    · exact ((hQ j).2.2.2.2.1 (Or.inr (tsupport_mul_subset_right hz))).2
  · change HasCompactSmoothingSchwartzSymbol
      (L.coordinateOperator - ∑ j, (R j).coordinateOperator)
    simpa only [hRQ] using herror
  · change HasOperatorSupport K (L.coordinateOperator - ∑ j, (R j).coordinateOperator)
    simpa only [hRQ] using hsupport

end PseudodifferentialPiece

end AtiyahSinger
