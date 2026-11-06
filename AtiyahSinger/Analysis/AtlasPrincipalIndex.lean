/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialFiltration
public import AtiyahSinger.Analysis.AtlasPseudodifferentialFredholm

/-!
# Index invariance for a common atlas principal symbol

Public module ID: M0275.

Principal quotient equality makes the difference of the two PDO actions
one order lower. Its Sobolev realization factors through a compact inclusion.
For a common homogeneous elliptic principal representative, compact
perturbation invariance and the smooth-to-Sobolev index comparisons give
equality of the original smooth indices. The atlases and symbol stay fixed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Set
open scoped Manifold ContDiff BigOperators

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F} {m : ℝ}

namespace AtlasPseudodifferentialOperator

/-- Equal original principal classes make the actual difference one order lower. -/
theorem isAtlasPseudodifferentialOperator_sub_of_principalSymbol_eq
    (P Q : AtlasPseudodifferentialOperator A B m) (hPQ : P.principalSymbol = Q.principalSymbol) :
    IsAtlasPseudodifferentialOperator A B (m - 1) (P.toLinearMap - Q.toLinearMap) := by
  classical
  obtain ⟨N, L, hL⟩ := P.isPseudodifferentialOperator
  obtain ⟨N', K, hK⟩ := Q.isPseudodifferentialOperator
  -- Negate the actual coordinate operator and its symbol together; the frames stay fixed.
  let J (j : Fin N') : AtlasPseudodifferentialPiece A B m :=
    { K j with
      operator := (-1 : ℂ) • (K j).operator
      symbol := (-1 : ℂ) • (K j).symbol
      isSymbol := (K j).isSymbol.smul isOpen_univ (-1)
      operator_apply := by
        intro u x
        change (-1 : ℂ) • (K j).operator u x = quantize ((-1 : ℂ) • (K j).symbol) u x
        rw [(K j).operator_apply]
        simp only [quantize, Pi.smul_apply, smul_apply]
        simp_rw [smul_comm (Complex.exp _) (-1 : ℂ)]
        rw [MeasureTheory.integral_smul, smul_comm] }
  have hJmap (j : Fin N') : (J j).toLinearMap = -(K j).toLinearMap := by
    apply LinearMap.ext
    intro u
    change (K j).output.extendLinearMap (K j).chart_mem_atlas
      ((-1 : ℂ) • (K j).operator ((K j).input.localize (K j).chart_mem_atlas u)) = _
    rw [map_smul, neg_one_smul]
    rfl
  have hJsymbol (j : Fin N') : (J j).globalSymbol = -(K j).globalSymbol := by
    apply Subtype.ext
    funext x ξ
    apply LinearMap.ext
    intro v
    by_cases hx : x ∈ (K j).chart.source ∩ (A.chart (K j).input.frameIndex).baseSet ∩
      (B.chart (K j).output.frameIndex).baseSet
    <;> simp [AtlasPseudodifferentialPiece.globalSymbol,
      AtlasPseudodifferentialPiece.globalSymbolFunction, J, hx]
  -- The concatenated family represents exactly P-Q with the difference of the old remainders.
  have hrem : IsAtlasSmoothingOperator A B
      (P.toLinearMap - Q.toLinearMap - ∑ j, ((Fin.append L J) j).toLinearMap) := by
    intro C D s t
    obtain ⟨T, hT⟩ := hL C D s t
    obtain ⟨S, hS⟩ := hK C D s t
    refine ⟨T - S, fun u ↦ ?_⟩
    rw [sub_apply, hT, hS, ← map_sub]
    congr 1
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hJmap, Finset.sum_neg_distrib,
      LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply]
    abel
  let R : AtlasPseudodifferentialOperator A B m :=
    ⟨P.toLinearMap - Q.toLinearMap, N + N', Fin.append L J, hrem⟩
  apply R.principalSymbol_eq_zero_iff.mp
  rw [R.principalSymbol_eq_of_representation (N + N') (Fin.append L J) hrem]
  have hsum : (∑ j, ((Fin.append L J) j).globalSymbol) =
      (∑ j, (L j).globalSymbol) - ∑ j, (K j).globalSymbol := by
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right, hJsymbol, Finset.sum_neg_distrib,
      sub_eq_add_neg]
  rw [hsum, map_sub, ← P.principalSymbol_eq_of_representation N L hL,
    ← Q.principalSymbol_eq_of_representation N' K hK, hPQ, sub_self]

/-- The smooth index depends only on the specified homogeneous elliptic principal class. -/
theorem index_eq_of_principalSymbol_eq_homogeneous
    (P Q : AtlasPseudodifferentialOperator A B m)
    (g : SmoothCotangentMetric (n := n) (M := M))
    (a : AtlasSymbolFunction (n := n) E F)
    (hs : IsSmoothOffZeroAtlasSymbol A B a) (hh : IsHomogeneousAtlasSymbol m a)
    (hP : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m
      (atlasRegularizedSymbol A B g m a hs hh))
    (hi : IsEllipticAtlasSymbol a) (hPQ : P.principalSymbol = Q.principalSymbol) :
    P.toLinearMap.index = Q.toLinearMap.index := by
  classical
  let L := (nonempty_atlasBundlePresentation A).some
  let K := (nonempty_atlasBundlePresentation B).some
  have hQ := hPQ.symm.trans hP
  let R : AtlasPseudodifferentialOperator A B (m - 1) :=
    ⟨Q.toLinearMap - P.toLinearMap,
      Q.isAtlasPseudodifferentialOperator_sub_of_principalSymbol_eq P hPQ.symm⟩
  let T := P.sobolevExtension L K 0
  let S := Q.sobolevExtension L K 0
  let V := R.sobolevExtension L K 0
  have hord : 0 - m < 0 - (m - 1) := by linarith
  let J := K.sobolevInclusion (0 - (m - 1)) (0 - m) hord.le
  -- Density identifies the actual perturbation, not merely its principal class.
  have hsum : T + J.comp V = S := by
    apply DFunLike.coe_injective
    apply (L.denseRange_smoothToSobolev 0).equalizer
      (T + J.comp V).continuous S.continuous
    funext u
    simp only [Function.comp_apply, add_apply, ContinuousLinearMap.comp_apply,
      T, S, V, J, sobolevExtension_smoothToSobolev,
      K.sobolevInclusion_smoothToSobolev, R, LinearMap.sub_apply, map_sub]
    abel
  have hcompact : IsCompactOperator (J.comp V) :=
    (K.isCompactOperator_sobolevInclusion (0 - (m - 1)) (0 - m) hord).comp_clm V
  have hindex := index_add_compact T (J.comp V)
    (P.isFredholm_sobolevExtension_of_homogeneous L K g a hs hh hP hi 0) hcompact
  rw [hsum] at hindex
  have hPT := (P.index_sobolevExtension_of_homogeneous L K g a hs hh hP hi 0).2.2
  have hQS := (Q.index_sobolevExtension_of_homogeneous L K g a hs hh hQ hi 0).2.2
  exact hPT.symm.trans (hindex.symm.trans hQS)

end AtlasPseudodifferentialOperator

end AtiyahSinger
