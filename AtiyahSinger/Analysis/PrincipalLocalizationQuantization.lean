/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalQuantization
public import AtiyahSinger.Analysis.PrincipalPseudodifferentialLocalization

/-!
# Principal localization retaining the specified full-symbol pieces

Public module ID: M0869.

Refine the actual pieces of a given quantization into the original principal
atlas. Both the exact sum of full symbols and the source of every refined
piece are retained. This permits homogeneous tails to be checked on those
same pieces before constructing the associated cutoff operator.

The ordinary localization theorem only retains the principal class. Here the
stronger witness is constructed directly from the specified quantization;
no arbitrary representation of its operator is selected afterward.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped ContDiff Manifold Topology

variable {n r a a' : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  (μ : Measure B) [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in
-- Retain the actual refined family and its dependent source-piece equalities.
/-- A specified quantization admits refinement preserving its exact full-symbol sum. -/
theorem QuantizationPresentation.exists_principalLocalization_of_fullSymbol {m : ℝ}
    (R : QuantizationPresentation (n := n) (r := a) (q := a') E E')
    (p : globalSymbolSpace (n := n) (r := a) (q := a') E E' m) :
    ∃ C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m,
      (∑ j, (C.piece j).globalSymbol) = p ∧
      C.baseOperator.principalSymbol = globalPrincipalSymbolClass E E' m p ∧
      ∃ (index : Fin C.size → Fin R.size)
        (χ ρ : Fin C.size → EuclideanSpace ℝ (Fin n) → ℝ)
        (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hρ : ∀ j, ContDiff ℝ ∞ (ρ j)),
        ∀ j, C.piece j = ((R.patch (index j)).toPiece p).coordinateCutoff
          (χ j) (ρ j) (hχ j) (hρ j) := by
  classical
  let U (b : B) := (S.trivialization b).baseSet
  let L (j : Fin R.size) := (R.patch j).toPiece p
  have hrefine (j : Fin R.size) := (L j).exists_coordinate_refinement U
    (fun b ↦ (S.trivialization b).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, S.mem_baseSet x⟩)
  choose N b χ ρ hχ hρ hparts using hrefine
  let V (j : Fin R.size) (k : Fin (N j)) :=
    (L j).coordinateCutoff (χ j k) (ρ j k) (hχ j k) (hρ j k)
  let J := Σ j : Fin R.size, Fin (N j)
  let e := (Fintype.equivFin J).symm
  let piece (k : Fin (Fintype.card J)) := V (e k).1 (e k).2
  let center (k : Fin (Fintype.card J)) := b (e k).1 (e k).2
  -- Refinement preserves the full-symbol sum before passing to the principal quotient.
  have hsum : (∑ k, (piece k).globalSymbol) = p := by
    calc
      (∑ k, (piece k).globalSymbol) = ∑ j : J, (V j.1 j.2).globalSymbol :=
        e.sum_comp (fun j : J ↦ (V j.1 j.2).globalSymbol)
      _ = ∑ j : Fin R.size, ∑ k : Fin (N j), (V j k).globalSymbol := Fintype.sum_sigma _
      _ = ∑ j, (L j).globalSymbol :=
        Finset.sum_congr rfl (fun j _ ↦ (hparts j).1)
      _ = p := by
        apply Subtype.ext
        simp only [Submodule.coe_sum]
        change (∑ j, (L j).globalSymbolFunction) = p.val
        funext x ξ
        simp only [Finset.sum_apply, L, QuantizationPatch.globalSymbolFunction_toPiece,
          ← Finset.sum_smul,
          ← Complex.ofReal_sum, R.sum_weight, Complex.ofReal_one, one_smul]
  have hsupp (j : Fin (Fintype.card J)) : (piece j).chart.symm ''
      (tsupport (piece j).output.cutoff ∪ tsupport (piece j).input.cutoff) ⊆
        (S.trivialization (center j)).baseSet := (hparts (e j).1).2.1 (e j).2
  have hzero : IsSmoothingOperator μ
      (0 : smoothSections (n := n) (r := a) E →ₗ[ℂ]
        smoothSections (n := n) (r := a') E') := by
    let K : SmoothKernel (n := n) (r := a) (q := a') E E' := {
      toFun := fun _ _ ↦ 0
      isSmooth := by
        intro f g _ _
        change ContMDiffOn _ _ ∞ (fun z : B × B ↦
          kernelInFrames E E' (fun _ _ ↦ 0) f g z) _
        simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
        exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  have hrep : IsSmoothingOperator μ
      ((∑ j, (piece j).toLinearMap) - ∑ j, (piece j).toLinearMap) := by
    rw [sub_self]
    exact hzero
  let Q : PseudodifferentialOperator (n := n) (r := a) (q := a') E E' μ m :=
    ⟨∑ j, (piece j).toLinearMap, ⟨Fintype.card J, piece, hrep⟩⟩
  have hprincipal : Q.principalSymbol = globalPrincipalSymbolClass E E' m p := by
    rw [Q.principalSymbol_eq_of_representation (Fintype.card J) piece hrep, hsum]
  -- The original input supports have smooth plateaus in their same selected principal charts.
  have hcutoff (j : Fin (Fintype.card J)) : ∃ η : B → ℝ,
      ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ η ∧ tsupport η ⊆ (S.trivialization (center j)).baseSet ∧
      ∀ x ∈ (piece j).chart.symm '' tsupport (piece j).input.cutoff, η x = 1 := by
    let K := (piece j).chart.symm '' tsupport (piece j).input.cutoff
    have hK : IsCompact K := (piece j).input.compact_support.image_of_continuousOn
      ((piece j).chart.continuousOn_symm.mono
        (fun x hx ↦ ((piece j).input.support_subset hx).1))
    have hKU : K ⊆ (S.trivialization (center j)).baseSet := by
      rintro x ⟨y, hy, rfl⟩
      exact hsupp j ⟨y, Or.inr hy, rfl⟩
    obtain ⟨W, hW, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure
      hK (S.trivialization (center j)).open_baseSet hKU
    obtain ⟨η, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (I := 𝓡 n) (n := ⊤) hK.isClosed (hKW.trans hW.subset_interior_closure)
    have hs : tsupport η ⊆ closure W := by
      apply closure_minimal ?_ hWc.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero x hn)
    exact ⟨η, η.contMDiff, hs.trans hWU, fun x hx ↦ hone.self_of_nhdsSet x hx⟩
  choose η hη hsη honeη using hcutoff
  let C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ m := {
    size := Fintype.card J
    center := center
    piece := piece
    baseOperator := Q
    baseOperator_eq := rfl
    piece_support := hsupp
    inputCutoff := η
    smooth_inputCutoff := hη
    inputCutoff_support := hsη
    inputCutoff_eq_one := honeη }
  exact ⟨C, hsum, hprincipal, fun j ↦ (e j).1,
    fun j ↦ χ (e j).1 (e j).2, fun j ↦ ρ (e j).1 (e j).2,
    fun j ↦ hχ (e j).1 (e j).2, fun j ↦ hρ (e j).1 (e j).2, fun _ ↦ rfl⟩

end AtiyahSinger
