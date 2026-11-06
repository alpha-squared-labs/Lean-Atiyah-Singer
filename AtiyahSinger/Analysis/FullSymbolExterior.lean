/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteCotangentChartExterior
public import AtiyahSinger.Analysis.GlobalFullSymbolEllipticity

/-!
# Exterior invertibility of the original general full symbol

Public module ID: M2282.

Quantitative full-symbol ellipticity gives one compact metric disk outside which the
original bundle map is invertible. A finite common chart presentation supplies compact
windows. The existing finite cotangent chart theorem combines their local radii; the two
original frame equivalences then transport matrix invertibility back to the original fibers.

Sources: SG III.3.13 and III.13 (13.1), for general symbols rather than homogeneous data.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold
open scoped Manifold ContDiff

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

/-- A general elliptic full symbol is invertible beyond one positive metric radius. -/
theorem IsEllipticFullGlobalSymbol.exists_metric_radius {m : ℝ}
    {a : GlobalSymbolFunction (n := n) E F}
    (ha : IsEllipticFullGlobalSymbol (r := r) (q := q) E F m a)
    (g : SmoothCotangentMetric (n := n) (M := M)) :
    ∃ R : ℝ, 0 < R ∧ ∀ x (ξ : CotangentFiber (n := n) x),
      R < g.length x ξ → (a x ξ).IsInvertible := by
  /- Local inverse estimates yield radii on compact common chart windows. Their finite cover
  gives one metric exterior. In the detected chart, conjugation by the original input and
  output frame equivalences recovers invertibility of the original fiber map. -/
  classical
  obtain ⟨A⟩ := nonempty_quantizationPresentation (n := n) (r := r) (q := q) (E := E) (F := F)
  let K (i : Fin A.size) := tsupport (A.patch i).input.cutoff
  let (i : Fin A.size) : MemTrivializationAtlas (A.patch i).input.frame :=
    (A.patch i).input.frame_mem_atlas
  let (i : Fin A.size) : MemTrivializationAtlas (A.patch i).output.frame :=
    (A.patch i).output.frame_mem_atlas
  -- Retain the common domain and its compact-local radius in each original patch.
  have hKU (i : Fin A.size) :
      K i ⊆ symbolChartDomain E F (A.patch i).chart
        (A.patch i).input.frame (A.patch i).output.frame := by
    intro z hz
    exact ⟨(A.patch i).input.support_subset hz,
      (A.patch i).input_support_in_output_frame hz⟩
  have hlocal (i : Fin A.size) : ∃ R : ℝ,
      ∀ z ∈ K i, ∀ η : EuclideanSpace ℝ (Fin n), R ≤ ‖η‖ →
        (globalSymbolInChart E F a (A.patch i).chart
          (A.patch i).input.frame (A.patch i).output.frame z η).IsInvertible := by
    obtain ⟨R, _, _, _, hbound⟩ :=
      ha (A.patch i).chart (A.patch i).chart_mem_atlas
        (A.patch i).input.frame (A.patch i).output.frame (K i) (hKU i)
        (A.patch i).input.compact_support
    exact ⟨R, fun z hz η hη ↦ (hbound z hz η hη).1⟩
  choose R hbound using hlocal
  -- A nonzero input weight places every base point in one of these compact windows.
  have hcover (x : M) : ∃ i : Fin A.size,
      x ∈ (A.patch i).chart.source ∧ (A.patch i).chart x ∈ K i := by
    have hactive : ∃ i : Fin A.size, (A.patch i).weight x ≠ 0 := by
      by_contra h
      push Not at h
      have hsum := A.sum_weight x
      simp only [h, Finset.sum_const_zero] at hsum
      exact zero_ne_one hsum
    obtain ⟨i, hi⟩ := hactive
    have hx : x ∈ (A.patch i).chart.source := by
      by_contra hx
      exact hi (by simp [QuantizationPatch.weight, hx])
    have hcut : (A.patch i).input.cutoff ((A.patch i).chart x) ≠ 0 := by
      simpa only [QuantizationPatch.weight, ite_eq_left hx] using hi
    exact ⟨i, hx, subset_tsupport _ hcut⟩
  obtain ⟨L, hL, hlarge⟩ := exists_metric_radius_of_cotangent_chart_cover g
    (fun i : Fin A.size ↦ (A.patch i).chart)
    (fun i ↦ subset_maximalAtlas (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (n := ∞) (A.patch i).chart_mem_atlas)
    K (fun i ↦ (A.patch i).input.compact_support)
    (fun i z hz ↦ ((A.patch i).input.support_subset hz).1) hcover R
  refine ⟨L, hL, ?_⟩
  intro x ξ hξ
  obtain ⟨i, hx, hwindow, hfreq⟩ := hlarge x ξ hξ.le
  -- This same coordinate window is in the two original frames over x.
  have he : x ∈ (A.patch i).input.frame.baseSet := by
    have h := (hKU i hwindow).1.2
    simpa only [Set.mem_preimage, (A.patch i).chart.left_inv hx] using h
  have hf : x ∈ (A.patch i).output.frame.baseSet := by
    have h := (hKU i hwindow).2
    simpa only [Set.mem_preimage, (A.patch i).chart.left_inv hx] using h
  let ec := (A.patch i).input.frame.continuousLinearEquivAt ℂ x he
  let fc := (A.patch i).output.frame.continuousLinearEquivAt ℂ x hf
  let η := covectorInChart (A.patch i).chart x ξ
  have hinv := hbound i ((A.patch i).chart x) hwindow η hfreq
  have hmatrix :
      globalSymbolInChart E F a (A.patch i).chart
        (A.patch i).input.frame (A.patch i).output.frame ((A.patch i).chart x) η =
          fc.toContinuousLinearMap.comp ((a x ξ).comp ec.symm.toContinuousLinearMap) := by
    dsimp only [globalSymbolInChart]
    rw [(A.patch i).chart.left_inv hx,
      covectorFromChart_covectorInChart (A.patch i).chart (A.patch i).chart_mem_atlas x hx ξ]
    rw [← (A.patch i).output.frame.coe_continuousLinearEquivAt_eq' (R := ℂ) hf,
      ← (A.patch i).input.frame.symm_continuousLinearEquivAt_eq' (R := ℂ) he]
  rw [hmatrix] at hinv
  simpa only [ContinuousLinearMap.isInvertible_equiv_comp,
    ContinuousLinearMap.isInvertible_comp_equiv] using hinv

end AtiyahSinger
