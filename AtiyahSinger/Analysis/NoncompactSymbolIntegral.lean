/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolIntegral

/-!
# Symbol integration over an arbitrary measure space

Public module ID: M0817.

Local integrable bounds on the actual jets replace compactness of the
parameter. The integral is pointwise in the original matrix space. Every mixed
derivative is the integral of the corresponding original mixed derivative.

The final symbol estimate allows its parameter majorant to depend on frequency.
Its scalar integral is bounded before taking a symbol weight or a supremum.
No norm or Bochner integral in a final-order symbol space is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Filter MeasureTheory Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 25

section DominatedJets

variable {Y H F : Type*} [MeasurableSpace Y]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  (μ : Measure Y) {f : Y → H → F} {s : Set H} (hs : IsOpen s)
  (hf : ∀ y, ContDiffOn ℝ ∞ (f y) s)
  (hmeas : ∀ (k : ℕ) (x : H), x ∈ s →
    AEStronglyMeasurable (fun y ↦ iteratedFDeriv ℝ k (f y) x) μ)
  (hdom : ∀ (k : ℕ) (x : H), x ∈ s →
    ∃ t : Set H, t ∈ 𝓝 x ∧ t ⊆ s ∧ ∃ B : Y → ℝ, Integrable B μ ∧
      ∀ᵐ y ∂μ, ∀ z ∈ t, ‖iteratedFDeriv ℝ k (f y) z‖ ≤ B y)

include hs hf hmeas hdom

private theorem hasFTaylorSeriesUpToOn_integral_of_locally_dominated_jets :
    HasFTaylorSeriesUpToOn ∞ (fun x ↦ ∫ y, f y x ∂μ)
      (fun x k ↦ ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ) s := by
  -- The bound at the center makes each actual jet integrable.
  have hint (k : ℕ) (x : H) (hx : x ∈ s) :
      Integrable (fun y ↦ iteratedFDeriv ℝ k (f y) x) μ := by
    obtain ⟨t, ht, _, B, hB, hbound⟩ := hdom k x hx
    apply hB.mono' (hmeas k x hx)
    filter_upwards [hbound] with y hy
    exact hy x (mem_of_mem_nhds ht)
  -- One further locally dominated jet justifies differentiation of each jet integral.
  have hderiv (k : ℕ) (x : H) (hx : x ∈ s) :
      HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (f y) z ∂μ)
        ((∫ y, iteratedFDeriv ℝ (k + 1) (f y) x ∂μ).curryLeft) x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ H) F
    let d (y : Y) (z : H) : H →L[ℝ] H [×k]→L[ℝ] F :=
      C (iteratedFDeriv ℝ (k + 1) (f y) z)
    obtain ⟨t, ht, hts, B, hB, hbound⟩ := hdom (k + 1) x hx
    have hD : HasFDerivAt (fun z ↦ ∫ y, iteratedFDeriv ℝ k (f y) z ∂μ)
        (∫ y, d y x ∂μ) x := by
      apply hasFDerivAt_integral_of_dominated_of_fderiv_le
        (F' := fun z y ↦ d y z) (bound := B) ht
      · filter_upwards [hs.mem_nhds hx] with z hz
        exact hmeas k z hz
      · exact hint k x hx
      · exact C.continuous.comp_aestronglyMeasurable (hmeas (k + 1) x hx)
      · filter_upwards [hbound] with y hy
        intro z hz
        change ‖C (iteratedFDeriv ℝ (k + 1) (f y) z)‖ ≤ B y
        rw [C.norm_map]
        exact hy z hz
      · exact hB
      · apply Eventually.of_forall
        intro y z hz
        have hsmooth : ContDiffAt ℝ ∞ (f y) z :=
          (hf y z (hts hz)).contDiffAt (hs.mem_nhds (hts hz))
        exact (hsmooth.differentiableAt_iteratedFDeriv (m := k)
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl k)).hasFDerivAt
    have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hint (k + 1) x hx)
    change (∫ y, d y x ∂μ) =
      (∫ y, iteratedFDeriv ℝ (k + 1) (f y) x ∂μ).curryLeft at hcomm
    rwa [hcomm] at hD
  -- The integrated jets form a compatible derivative tower; each jet is continuous.
  constructor
  · intro x hx
    let C := continuousMultilinearCurryFin0 ℝ H F
    have hcomm := C.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (hint 0 x hx)
    change (∫ y, (iteratedFDeriv ℝ 0 (f y) x).curry0 ∂μ) =
      (∫ y, iteratedFDeriv ℝ 0 (f y) x ∂μ).curry0 at hcomm
    simpa only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply] using
      hcomm.symm
  · intro k _ x hx
    exact (hderiv k x hx).hasFDerivWithinAt
  · intro k _ x hx
    exact (hderiv k x hx).continuousAt.continuousWithinAt

/-- Local integrable domination of all actual jets makes the pointwise integral smooth. -/
theorem contDiffOn_integral_of_locally_dominated_jets :
    ContDiffOn ℝ ∞ (fun x ↦ ∫ y, f y x ∂μ) s := by
  exact (hasFTaylorSeriesUpToOn_integral_of_locally_dominated_jets
    μ hs hf hmeas hdom).contDiffOn

/-- Every actual derivative commutes with a locally dominated parameter integral. -/
theorem iteratedFDeriv_integral_of_locally_dominated_jets
    (k : ℕ) {x : H} (hx : x ∈ s) :
    iteratedFDeriv ℝ k (fun z ↦ ∫ y, f y z ∂μ) x =
      ∫ y, iteratedFDeriv ℝ k (f y) x ∂μ := by
  have hseries := hasFTaylorSeriesUpToOn_integral_of_locally_dominated_jets
    μ hs hf hmeas hdom
  have hsmooth := contDiffOn_integral_of_locally_dominated_jets μ hs hf hmeas hdom
  have heq := hseries.eq_iteratedFDerivWithin_of_uniqueDiffOn (m := k)
    (by simp) hs.uniqueDiffOn hx
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn
    (((hsmooth x hx).contDiffAt (hs.mem_nhds hx)).of_le (by simp)) hx] at heq
  exact heq.symm

end DominatedJets

section Symbols

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
  {n r q : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
  (a : Y → SymbolFunction n r q)
  (ha : ∀ y, ContDiffOn ℝ ∞ (Function.uncurry (a y)) (U ×ˢ univ))
  (hmeasMixed : ∀ (i j : ℕ)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), z ∈ U ×ˢ univ →
      AEStronglyMeasurable (fun y ↦ symbolDerivative (a y) i j z.1 z.2) μ)
  (hdomMixed : ∀ (i j : ℕ)
    (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), z ∈ U ×ˢ univ →
      ∃ t : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        t ∈ 𝓝 z ∧ t ⊆ U ×ˢ univ ∧ ∃ B : Y → ℝ, Integrable B μ ∧
          ∀ᵐ y ∂μ, ∀ w ∈ t, ‖symbolDerivative (a y) i j w.1 w.2‖ ≤ B y)

include hU ha hmeasMixed hdomMixed

/-- The original nested mixed derivative commutes with a noncompact parameter integral. -/
theorem symbolDerivative_integral_of_locally_dominated_jets (i j : ℕ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    symbolDerivative (fun x ξ ↦ ∫ y, a y x ξ ∂μ) i j x ξ =
      ∫ y, symbolDerivative (a y) i j x ξ ∂μ := by
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  -- The original joint smoothness supplies smooth frequency jets with their base parameter.
  have hpartial (y : Y) (k : ℕ) : ContDiffOn ℝ ∞
      (fun z : X × X ↦ iteratedFDeriv ℝ k (a y z.1) z.2) (U ×ˢ univ) := by
    intro z hz
    have hs : ContDiffAt ℝ ∞ (Function.uncurry (a y)) z :=
      (ha y).contDiffAt ((hU.prod isOpen_univ).mem_nhds hz)
    have hj : ContDiffAt ℝ ∞
        (fun z : X × X ↦ iteratedFDeriv ℝ k (a y z.1) z.2) z := by
      induction k with
      | zero =>
        exact hs.continuousLinearMap_comp
          ((continuousMultilinearCurryFin0 ℝ X V).symm : _ →L[ℝ] X [×0]→L[ℝ] V)
      | succ k ih =>
        have h : ContDiffAt ℝ ∞
            (Function.uncurry (fun p : X × X ↦ fun η : X ↦
              iteratedFDeriv ℝ k (a y p.1) η)) (z, z.2) :=
          ih.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
        have hd : ContDiffAt ℝ ∞
            (fun p : X × X ↦ fderiv ℝ (iteratedFDeriv ℝ k (a y p.1)) p.2) z :=
          h.fderiv contDiffAt_snd (by simp)
        exact hd.continuousLinearMap_comp
          ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) ↦ X) V).symm :
            _ →L[ℝ] X [×(k + 1)]→L[ℝ] V)
    exact hj.contDiffWithinAt
  -- First integrate each frequency jet; its local dominator is pulled back along a slice.
  have hfrequency (z : X) (hz : z ∈ U) :
      iteratedFDeriv ℝ j (fun η ↦ ∫ y, a y z η ∂μ) ξ =
        ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ := by
    apply iteratedFDeriv_integral_of_locally_dominated_jets μ isOpen_univ
      (fun y ↦ (ha y).comp (contDiffOn_const.prodMk contDiffOn_id)
        (fun η _ ↦ ⟨hz, mem_univ η⟩))
    · intro k η _
      let C := continuousMultilinearCurryFin0 ℝ X (X [×k]→L[ℝ] V)
      have hzero (y : Y) :
          C (symbolDerivative (a y) 0 k z η) = iteratedFDeriv ℝ k (a y z) η := by
        change (iteratedFDeriv ℝ 0
          (fun z ↦ iteratedFDeriv ℝ k (a y z) η) z).curry0 = _
        simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply]
      simpa only [Function.comp_def, Function.uncurry, id_eq, hzero] using
        C.continuous.comp_aestronglyMeasurable (hmeasMixed 0 k (z, η) ⟨hz, mem_univ η⟩)
    · intro k η _
      obtain ⟨t, ht, _, B, hB, hbound⟩ := hdomMixed 0 k (z, η) ⟨hz, mem_univ η⟩
      refine ⟨(fun w : X ↦ (z, w)) ⁻¹' t,
        (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds ht,
        subset_univ _, B, hB, ?_⟩
      filter_upwards [hbound] with y hy
      intro w hw
      let C := continuousMultilinearCurryFin0 ℝ X (X [×k]→L[ℝ] V)
      have hzero :
          C (symbolDerivative (a y) 0 k z w) = iteratedFDeriv ℝ k (a y z) w := by
        change (iteratedFDeriv ℝ 0
          (fun z ↦ iteratedFDeriv ℝ k (a y z) w) z).curry0 = _
        simp only [iteratedFDeriv_zero_apply, ContinuousMultilinearMap.curry0_apply]
      simp only [Function.comp_def, Function.uncurry, id_eq]
      rw [← hzero, C.norm_map]
      exact hy (z, w) hw
    · exact mem_univ ξ
  -- Then integrate the base jets of that same frequency derivative family.
  have hbase :
      iteratedFDeriv ℝ i (fun z ↦ ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ) x =
        ∫ y, iteratedFDeriv ℝ i (fun z ↦ iteratedFDeriv ℝ j (a y z) ξ) x ∂μ := by
    apply iteratedFDeriv_integral_of_locally_dominated_jets μ hU
      (fun y ↦ (hpartial y j).comp (contDiffOn_id.prodMk contDiffOn_const)
        (fun z hz ↦ ⟨hz, mem_univ ξ⟩))
    · intro k z hz
      exact hmeasMixed k j (z, ξ) ⟨hz, mem_univ ξ⟩
    · intro k z hz
      obtain ⟨t, ht, hts, B, hB, hbound⟩ := hdomMixed k j (z, ξ) ⟨hz, mem_univ ξ⟩
      refine ⟨(fun w : X ↦ (w, ξ)) ⁻¹' t,
        (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds ht,
        ?_, B, hB, ?_⟩
      · intro w hw
        exact (hts hw).1
      · filter_upwards [hbound] with y hy
        intro w hw
        exact hy (w, ξ) hw
    · exact hx
  -- Equality of the inner jets holds near x, so the actual outer derivatives agree.
  have hnear : (fun z ↦ iteratedFDeriv ℝ j (fun η ↦ ∫ y, a y z η ∂μ) ξ) =ᶠ[𝓝 x]
      (fun z ↦ ∫ y, iteratedFDeriv ℝ j (a y z) ξ ∂μ) :=
    Filter.eventuallyEq_of_mem (hU.mem_nhds hx) hfrequency
  exact ((hnear.iteratedFDeriv ℝ i).eq_of_nhds).trans hbase

/-- Frequency-dependent integrable scalar majorants give the order of the integral symbol. -/
theorem isSymbol_integral_of_locally_dominated_jets {m : ℝ}
    (hmeasJoint : ∀ (k : ℕ)
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), z ∈ U ×ˢ univ →
        AEStronglyMeasurable (fun y ↦ iteratedFDeriv ℝ k (Function.uncurry (a y)) z) μ)
    (hdomJoint : ∀ (k : ℕ)
      (z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)), z ∈ U ×ˢ univ →
        ∃ t : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
          t ∈ 𝓝 z ∧ t ⊆ U ×ˢ univ ∧ ∃ B : Y → ℝ, Integrable B μ ∧
            ∀ᵐ y ∂μ, ∀ w ∈ t, ‖iteratedFDeriv ℝ k (Function.uncurry (a y)) w‖ ≤ B y)
    (hbound : ∀ K : Set (EuclideanSpace ℝ (Fin n)), K ⊆ U → IsCompact K →
      ∀ i j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ, ∃ B : Y → ℝ, Integrable B μ ∧
        (∀ᵐ y ∂μ, ∀ x ∈ K, ‖symbolDerivative (a y) i j x ξ‖ ≤ B y) ∧
        (∫ y, B y ∂μ) ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ))) :
    IsSymbol U m (fun x ξ ↦ ∫ y, a y x ξ ∂μ) := by
  constructor
  · -- Joint smoothness follows from locally dominated actual full jets.
    exact contDiffOn_integral_of_locally_dominated_jets μ (hU.prod isOpen_univ)
      ha hmeasJoint hdomJoint
  · intro K hKU hK i j
    obtain ⟨C, hC, hbound⟩ := hbound K hKU hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    obtain ⟨B, hB, hpointwise, hintegral⟩ := hbound ξ
    obtain ⟨t, ht, _, D, hD, hlocal⟩ :=
      hdomMixed i j (x, ξ) ⟨hKU hx, mem_univ ξ⟩
    have hi : Integrable (fun y ↦ symbolDerivative (a y) i j x ξ) μ := by
      apply hD.mono' (hmeasMixed i j (x, ξ) ⟨hKU hx, mem_univ ξ⟩)
      filter_upwards [hlocal] with y hy
      exact hy (x, ξ) (mem_of_mem_nhds ht)
    rw [symbolDerivative_integral_of_locally_dominated_jets
      μ hU a ha hmeasMixed hdomMixed i j (hKU hx) ξ]
    -- Integrate the frequency-dependent majorant before forming the uniform symbol bound.
    calc
      _ ≤ ∫ y, ‖symbolDerivative (a y) i j x ξ‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, B y ∂μ := integral_mono_ae hi.norm hB
        (hpointwise.mono (fun y hy ↦ hy x hx))
      _ ≤ C * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := hintegral

end Symbols

end AtiyahSinger
