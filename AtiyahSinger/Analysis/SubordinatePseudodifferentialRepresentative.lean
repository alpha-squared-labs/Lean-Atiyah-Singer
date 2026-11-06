/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactPieceRefinement

/-!
# A native PDO representative subordinate to a prescribed open cover

Refine each original local piece using the same native coordinate cutoffs,
then flatten the finite family. The resulting operator is exactly their sum
and retains the original principal class. In elliptic applications its base
index can therefore be compared before any horizontal lifting is performed.
No smoothing remainder is tensor extended to the sphere.
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

variable [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

namespace PseudodifferentialOperator

set_option maxSynthPendingDepth 15 in
/-- Every native PDO has an equal-principal representative formed from pieces in any open cover. -/
theorem exists_subordinate_representative {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    {ι : Type*} (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    ∃ (N : ℕ) (a : Fin N → ι)
      (L : Fin N → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
      (Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m),
      (∀ j, (L j).chart.symm ''
        (tsupport (L j).output.cutoff ∪ tsupport (L j).input.cutoff) ⊆ U (a j)) ∧
      Q.toLinearMap = ∑ j, (L j).toLinearMap ∧ Q.principalSymbol = P.principalSymbol := by
  classical
  obtain ⟨d, R, hR⟩ := P.isPseudodifferentialOperator
  -- Refine the specified native pieces; their full leading-symbol sum is unchanged.
  have hrefine (j : Fin d) := (R j).exists_coordinate_refinement U hU (by
    intro x _
    obtain ⟨i, hi⟩ := hcover x
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  choose N a χ ρ hχ hρ hparts using hrefine
  let V (j : Fin d) (k : Fin (N j)) := (R j).coordinateCutoff (χ j k) (ρ j k) (hχ j k) (hρ j k)
  let J := Σ j : Fin d, Fin (N j)
  let e := (Fintype.equivFin J).symm
  let L (k : Fin (Fintype.card J)) := V (e k).1 (e k).2
  have hsymbol : (∑ k, (L k).globalSymbol) = ∑ j, (R j).globalSymbol := by
    calc
      (∑ k, (L k).globalSymbol) = ∑ j : J, (V j.1 j.2).globalSymbol :=
        e.sum_comp (fun j : J ↦ (V j.1 j.2).globalSymbol)
      _ = ∑ j : Fin d, ∑ k : Fin (N j), (V j k).globalSymbol := Fintype.sum_sigma _
      _ = ∑ j, (R j).globalSymbol := Finset.sum_congr rfl (fun j _ ↦ (hparts j).1)
  -- Bundle exactly this finite sum; the defining remainder is the actual zero kernel.
  have hzero : IsSmoothingOperator (n := n) (r := r) (q := q) μ
      (0 : smoothSections E →ₗ[ℂ] smoothSections F) := by
    let K : SmoothKernel (n := n) (r := r) (q := q) E F :=
      { toFun := fun _ _ ↦ 0
        isSmooth := by
          intro f g _ _
          change ContMDiffOn _ _ ∞ (fun z : M × M ↦
            kernelInFrames E F (fun _ _ ↦ 0) f g z) _
          simp only [kernelInFrames, ContinuousLinearMap.zero_comp,
            ContinuousLinearMap.comp_zero]
          exact contMDiffOn_const }
    refine ⟨K, ?_⟩
    ext u x
    change K.apply μ u x = 0
    simp [SmoothKernel.apply, K]
  have hrep : IsSmoothingOperator μ
      ((∑ k, (L k).toLinearMap) - ∑ k, (L k).toLinearMap) := by
    simpa only [sub_self] using hzero
  let Q : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m :=
    ⟨∑ k, (L k).toLinearMap, ⟨Fintype.card J, L, hrep⟩⟩
  refine ⟨Fintype.card J, fun k ↦ a (e k).1 (e k).2, L, Q, ?_, rfl, ?_⟩
  · intro k
    exact (hparts (e k).1).2.1 (e k).2
  · -- Both principal computations use the same flattened native family and symbol sum.
    rw [Q.principalSymbol_eq_of_representation (Fintype.card J) L hrep,
      P.principalSymbol_eq_of_representation d R hR, hsymbol]

end PseudodifferentialOperator

end AtiyahSinger
