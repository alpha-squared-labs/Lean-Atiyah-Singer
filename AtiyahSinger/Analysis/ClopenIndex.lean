/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClopenDiagonalOperator
public import AtiyahSinger.Analysis.ClopenPseudodifferential
public import AtiyahSinger.Analysis.IndexFiniteSum
public import AtiyahSinger.Analysis.SymbolIndexInvariance
public import AtiyahSinger.Geometry.ClopenSmoothSections

/-!
# Additivity of the smooth index over a finite clopen decomposition

Public module ID: M0330.

The actual diagonal restrictions of a supplied elliptic PDO have its original
restricted homogeneous symbols. Their smooth indices sum to the original
index: clopen diagonalization preserves the principal symbol, and actual
restriction identifies the new section map with the finite product of those
same blocks. This is the finite-component step of SG III.13, p.247.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  (μ : Measure M) [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)

attribute [local instance] isSmoothPositiveMeasure_comap_opens

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual clopen diagonal blocks have the restricted symbol and sum to the original index. -/
theorem PseudodifferentialOperator.exists_clopen_index_decomposition {ι : Type*} [Fintype ι]
    (P : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ 0)
    (R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber)
    (a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber 0)
    (hp : P.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber 0
      (R.regularizedSymbol 0 a.val a.property.1 a.property.2)) (hi : P.IsElliptic)
    (U : ι → Opens M) (hclosed : ∀ i, IsClosed (U i : Set M)) [∀ i, CompactSpace (U i)]
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (U i : Set M) (U j : Set M)))
    (hcover : (⋃ i, (U i : Set M)) = Set.univ) :
    ∃ PU : ∀ i, PseudodifferentialOperator (M := U i) (n := n) (r := E.rank) (q := F.rank)
        (E.restrictOpen (U i)).Fiber (F.restrictOpen (U i)).Fiber
        (μ.comap (Subtype.val : U i → M)) 0,
      ∃ RU : ∀ i, QuantizationPresentation (M := U i) (n := n) (r := E.rank) (q := F.rank)
          (E.restrictOpen (U i)).Fiber (F.restrictOpen (U i)).Fiber,
        ∃ aU : ∀ i, homogeneousGlobalSymbolSpace (M := U i) (n := n)
            (r := E.rank) (q := F.rank) (E.restrictOpen (U i)).Fiber
              (F.restrictOpen (U i)).Fiber 0,
          (∀ i, (PU i).principalSymbol = globalPrincipalSymbolClass
            (E.restrictOpen (U i)).Fiber (F.restrictOpen (U i)).Fiber 0
              ((RU i).regularizedSymbol 0 (aU i).val (aU i).property.1 (aU i).property.2)) ∧
          (∀ i, (PU i).IsElliptic) ∧
          (∀ i x ξ, (aU i).val x ξ = a.val x.val ξ) ∧
          P.toLinearMap.index = ∑ i, (PU i).toLinearMap.index := by
  classical
  -- The same restriction witnesses supply both the principal symbols and the section actions.
  choose PU RU aU hpU hiU haU haction using fun i ↦
    PseudodifferentialOperator.exists_clopen_restriction μ E F P R a hp hi (U i) (hclosed i)
  refine ⟨PU, RU, aU, hpU, hiU, haU, ?_⟩
  obtain ⟨Q, hQ, hdiag⟩ := P.exists_clopen_diagonal μ E F R a hp U hclosed hdisjoint hcover
  have hpQ := hQ.trans hp
  have hiQ : Q.IsElliptic := (Q.isElliptic_iff_of_principalSymbol_eq_operator P hQ).mpr hi
  have hindex : P.toLinearMap.index = Q.toLinearMap.index :=
    P.index_eq_of_symbolKClass_eq R a hp hi Q R a hpQ hiQ rfl
  -- Actual restrictions identify the diagonalized map with the product of these same blocks.
  obtain ⟨S, hS, _⟩ := exists_smoothSectionClopenEquiv
    (n := n) (r := E.rank) E.Fiber U hclosed hdisjoint hcover
  obtain ⟨T, hT, _⟩ := exists_smoothSectionClopenEquiv
    (n := n) (r := F.rank) F.Fiber U hclosed hdisjoint hcover
  let L := LinearMap.piMap (fun i ↦ (PU i).toLinearMap)
  have hinter (u : smoothSections (n := n) (r := E.rank) E.Fiber) :
      L (S u) = T (Q.toLinearMap u) := by
    funext i
    apply Subtype.ext
    funext x
    change ((PU i).toLinearMap (S u i)).val x = (T (Q.toLinearMap u) i).val x
    rw [hT, hdiag, haction]
    have hsection : S u i = smoothSectionRestriction E.Fiber (U i) u := by
      apply Subtype.ext
      funext y
      exact hS u i y
    rw [hsection]
  -- Intertwining identifies the kernel and the genuine algebraic quotient cokernel.
  let kerEquiv : Q.toLinearMap.ker ≃ₗ[ℂ] L.ker := {
    toFun u := ⟨S u.val, by rw [LinearMap.mem_ker, hinter, u.property, map_zero]⟩
    invFun u := ⟨S.symm u.val, by
      apply T.injective
      rw [map_zero, ← hinter, S.apply_symm_apply]
      exact u.property⟩
    left_inv u := Subtype.ext (S.symm_apply_apply u.val)
    right_inv u := Subtype.ext (S.apply_symm_apply u.val)
    map_add' u v := Subtype.ext (S.map_add u.val v.val)
    map_smul' t u := Subtype.ext (S.map_smul t u.val) }
  have hrange : Q.toLinearMap.range.map T.toLinearMap = L.range := by
    ext v
    constructor
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      exact ⟨S u, hinter u⟩
    · rintro ⟨u, rfl⟩
      exact ⟨Q.toLinearMap (S.symm u), ⟨S.symm u, rfl⟩,
        (hinter (S.symm u)).symm.trans (congrArg L (S.apply_symm_apply u))⟩
  let cokerEquiv := Submodule.Quotient.equiv Q.toLinearMap.range L.range T hrange
  have hindexQ : Q.toLinearMap.index = L.index := by
    rw [LinearMap.index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
      kerEquiv.finrank_eq, cokerEquiv.finrank_eq]
  -- Elliptic regularity supplies finite defects for every original diagonal block.
  have hfinite (i : ι) : FiniteDimensional ℂ (PU i).toLinearMap.ker ∧
      FiniteDimensional ℂ
        (smoothSections (n := n) (r := F.rank) (F.restrictOpen (U i)).Fiber ⧸
          (PU i).toLinearMap.range) := by
    obtain ⟨A⟩ := nonempty_smoothBundlePresentation
      (n := n) (r := E.rank) (E.restrictOpen (U i)).Fiber
    obtain ⟨B⟩ := nonempty_smoothBundlePresentation
      (n := n) (r := F.rank) (F.restrictOpen (U i)).Fiber
    exact ⟨(PU i).finiteDimensional_ker_of_isElliptic A B (hiU i),
      (PU i).finiteDimensional_coker_of_isElliptic A B (hiU i)⟩
  let : ∀ i, FiniteDimensional ℂ (PU i).toLinearMap.ker := fun i ↦ (hfinite i).1
  let : ∀ i, FiniteDimensional ℂ
      (smoothSections (n := n) (r := F.rank) (F.restrictOpen (U i)).Fiber ⧸
        (PU i).toLinearMap.range) := fun i ↦ (hfinite i).2
  exact hindex.trans (hindexQ.trans (index_piMap (fun i ↦ (PU i).toLinearMap)))

end AtiyahSinger
