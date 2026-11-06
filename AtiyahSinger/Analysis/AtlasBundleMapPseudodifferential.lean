/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasDifferentialPseudodifferential
public import AtiyahSinger.Geometry.AtlasSectionMaps

/-!
# Multiplication by a map of the specified smooth atlases

Public module ID: M0230.

A smooth fiber map acts as an order-zero differential operator on the original
atlas sections. Its principal symbol is precisely that same map at every
covector. On a compact base the existing differential-to-PDO construction gives
its actual multiplication PDO and the same homogeneous principal class.

This is the zero-order case of SG III.1 and III.3, with independent local ranks
and the originally specified atlases. It supplies the inclusion and projection
operators used to transfer quantization along smooth equivariant retracts.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  (A : SmoothComplexBundleAtlas (n := n) E)
  (B : SmoothComplexBundleAtlas (n := n) F)
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M]

/-- Multiplication by the specified smooth map has exactly that order-zero principal symbol. -/
theorem exists_atlasDifferentialOperator_bundleMap
    (a : ∀ x, E x →ₗ[ℂ] F x) (ha : IsSmoothAtlasBundleMap A B a) :
    ∃ D : AtlasDifferentialOperator A B 0,
      D.toLinearMap = atlasSmoothSectionMap A B a ha ∧
      D.principalSymbol = fun x _ ↦ a x := by
  classical
  -- Construct the actual matrix in each specified pair of frames, using its smooth columns.
  have hlocal (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (i : A.Index) (j : B.Index) :
      ∃ Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) 0
          (c '' (c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet)),
        HasAtlasCoordinateExpression A B 0 (atlasSmoothSectionMap A B a ha) c i j
          (c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet) Q ∧
        ∀ x ∈ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet,
          ∀ ξ v, (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm
              ((B.chart j ⟨x, a x v⟩).2) =
            Q.principalSymbol (c x) ξ
              ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
                ((A.chart i ⟨x, v⟩).2)) := by
    let V := EuclideanSpace ℂ (Fin (A.rank i))
    let W := EuclideanSpace ℂ (Fin (B.rank j))
    let eA := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
    let eB := EuclideanSpace.equiv (Fin (B.rank j)) ℂ
    let column (k : Fin (A.rank i)) (x : M) : Fin (B.rank j) → ℂ :=
      if hx : x ∈ (A.chart i).baseSet then
        (B.chart j ⟨x, a x ((A.frameLinearEquiv i x hx).symm (Pi.single k 1))⟩).2
      else 0
    let L (x : M) : V →L[ℂ] W := ∑ k : Fin (A.rank i),
      ContinuousLinearMap.smulRightL ℂ V W (EuclideanSpace.proj k) (eB.symm (column k x))
    have hL : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, V →L[ℂ] W) ∞ L
        ((A.chart i).baseSet ∩ (B.chart j).baseSet) := by
      apply contMDiffOn_finsetSum
      intro k _
      exact ((ContinuousLinearMap.smulRightL ℂ V W
        (EuclideanSpace.proj k)).restrictScalars ℝ).contMDiff.comp_contMDiffOn
          ((eB.symm.toContinuousLinearMap.restrictScalars ℝ).contMDiff.comp_contMDiffOn
            (ha.2 i j k))
    have hLeq (x : M) (hx : x ∈ (A.chart i).baseSet ∩ (B.chart j).baseSet)
        (v : E x) : L x (eA.symm ((A.chart i ⟨x, v⟩).2)) =
          eB.symm ((B.chart j ⟨x, a x v⟩).2) := by
      let T := eB.symm.toLinearMap.comp ((B.frameLinearEquiv j x hx.2).toLinearMap.comp
        ((a x).comp (A.frameLinearEquiv i x hx.1).symm.toLinearMap))
      have hsum := congrArg T ((Pi.basisFun ℂ (Fin (A.rank i))).sum_repr
        ((A.frameLinearEquiv i x hx.1) v))
      simp only [map_sum, map_smul, Pi.basisFun_apply, Pi.basisFun_repr] at hsum
      dsimp only [T, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        ContinuousLinearEquiv.coe_coe] at hsum
      rw [LinearEquiv.symm_apply_apply] at hsum
      simpa [L, column, hx.1, EuclideanSpace.proj, PiLp.proj, PiLp.projₗ,
        WithLp.linearEquiv, eA,
        SmoothComplexBundleAtlas.frameLinearEquiv] using hsum
    let U := c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet
    have hsymm := contMDiffOn_symm_of_mem_maximalAtlas
      (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞)
        (IsManifold.subset_maximalAtlas hc)
    have hcoeff : ContDiffOn ℝ ∞ (fun z ↦ L (c.symm z)) (c '' U) := by
      apply ContMDiffOn.contDiffOn
      apply hL.comp (hsymm.mono ?_) ?_
      · rintro z ⟨y, hy, rfl⟩
        exact c.map_source hy.1.1
      · rintro z ⟨y, hy, rfl⟩
        change c.symm (c y) ∈ (A.chart i).baseSet ∩ (B.chart j).baseSet
        rw [c.left_inv hy.1.1]
        exact ⟨hy.1.2, hy.2⟩
    let Q : CoordinateDifferentialOperator n (A.rank i) (B.rank j) 0 (c '' U) := {
      coefficient := fun _ _ z ↦ L (c.symm z)
      smooth_coefficient := fun _ _ ↦ hcoeff }
    refine ⟨Q, ⟨Set.Subset.rfl, ?_⟩, ?_⟩
    · intro s y hy
      have hsection : atlasSectionInChart A c i s.val (c y) =
          eA.symm ((A.chart i ⟨y, s.val y⟩).2) := by
        unfold atlasSectionInChart
        rw [c.left_inv hy.1.1]
      change eB.symm ((B.chart j ⟨y, a y (s.val y)⟩).2) = _
      simpa [CoordinateDifferentialOperator.apply, Q, hsection, c.left_inv hy.1.1] using
        (hLeq y ⟨hy.1.2, hy.2⟩ (s.val y)).symm
    · intro y hy ξ v
      simpa [CoordinateDifferentialOperator.principalSymbol, Q, c.left_inv hy.1.1, eA, eB] using
        (hLeq y ⟨hy.1.2, hy.2⟩ v).symm
  -- The same local coefficient supplies the section action and principal-symbol identity.
  let D : AtlasDifferentialOperator A B 0 := {
    toLinearMap := atlasSmoothSectionMap A B a ha
    isAtlasDifferentialOperator := by
      intro c hc i j x hx
      obtain ⟨Q, hQ, _⟩ := hlocal c hc i j
      exact ⟨_, (c.open_source.inter (A.chart i).open_baseSet).inter
        (B.chart j).open_baseSet, hx, Q, hQ⟩ }
  refine ⟨D, rfl, ?_⟩
  funext x ξ
  apply LinearMap.ext
  intro v
  let c := chartAt (EuclideanSpace ℝ (Fin n)) x
  obtain ⟨i, hi⟩ := A.covers x
  obtain ⟨j, hj⟩ := B.covers x
  obtain ⟨Q, hQ, hsymbol⟩ := hlocal c (chart_mem_atlas _ x) i j
  have hx : x ∈ c.source ∩ (A.chart i).baseSet ∩ (B.chart j).baseSet :=
    ⟨⟨mem_chart_source _ x, hi⟩, hj⟩
  have hp := D.hasAtlasPrincipalSymbol c (chart_mem_atlas _ x) i j _
    ((c.open_source.inter (A.chart i).open_baseSet).inter (B.chart j).open_baseSet)
    Q hQ x hx ξ v
  apply (B.frameLinearEquiv j x hj).injective
  apply (EuclideanSpace.equiv (Fin (B.rank j)) ℂ).symm.injective
  exact hp.trans (hsymbol x hx (covectorInChart c x ξ) v).symm

variable [CompactSpace M]

/-- The same multiplication map is an actual PDO with its specified full-symbol class. -/
theorem exists_atlasPseudodifferentialOperator_bundleMap
    (a : ∀ x, E x →ₗ[ℂ] F x) (ha : IsSmoothAtlasBundleMap A B a) :
    ∃ hg : IsAtlasGlobalSymbol A B 0 (fun x _ ↦ a x),
    ∃ P : AtlasPseudodifferentialOperator A B 0,
      P.toLinearMap = atlasSmoothSectionMap A B a ha ∧
      P.principalSymbol = atlasGlobalPrincipalSymbolClass A B 0
        ⟨(fun x _ ↦ a x), hg⟩ := by
  -- The differential representative already acts on precisely the specified section spaces.
  obtain ⟨D, hD, hsymbol⟩ := exists_atlasDifferentialOperator_bundleMap A B a ha
  have hg : IsAtlasGlobalSymbol A B ((0 : ℕ) : ℝ) (fun x _ ↦ a x) := by
    rw [← hsymbol]
    exact D.isAtlasGlobalSymbol_principalSymbol
  have hraw : ∃ hg : IsAtlasGlobalSymbol A B ((0 : ℕ) : ℝ) (fun x _ ↦ a x),
      ∃ P : AtlasPseudodifferentialOperator A B ((0 : ℕ) : ℝ),
        P.toLinearMap = atlasSmoothSectionMap A B a ha ∧
        P.principalSymbol = atlasGlobalPrincipalSymbolClass A B ((0 : ℕ) : ℝ)
          ⟨(fun x _ ↦ a x), hg⟩ := by
    refine ⟨hg, D.toAtlasPseudodifferentialOperator, hD, ?_⟩
    -- The principal quotient retains the original full constant-in-frequency fiber map.
    have hclass := D.principalSymbol_toAtlasPseudodifferentialOperator
    simpa only [AtlasDifferentialOperator.principalGlobalSymbol, hsymbol] using hclass
  -- Transport the whole package, so its map, symbol and order use the same equality.
  have htransfer (l : ℝ) (hl : l = 0)
      (h : ∃ hg : IsAtlasGlobalSymbol A B l (fun x _ ↦ a x),
        ∃ P : AtlasPseudodifferentialOperator A B l,
          P.toLinearMap = atlasSmoothSectionMap A B a ha ∧
          P.principalSymbol = atlasGlobalPrincipalSymbolClass A B l
            ⟨(fun x _ ↦ a x), hg⟩) :
      ∃ hg : IsAtlasGlobalSymbol A B 0 (fun x _ ↦ a x),
        ∃ P : AtlasPseudodifferentialOperator A B 0,
          P.toLinearMap = atlasSmoothSectionMap A B a ha ∧
          P.principalSymbol = atlasGlobalPrincipalSymbolClass A B 0
            ⟨(fun x _ ↦ a x), hg⟩ := by
    subst l
    exact h
  exact htransfer _ Nat.cast_zero hraw

end AtiyahSinger
