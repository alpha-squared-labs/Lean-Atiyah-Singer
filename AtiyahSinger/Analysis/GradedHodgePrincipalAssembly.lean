/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedHodgeFiniteAssembly
public import AtiyahSinger.Analysis.HomogeneousPrincipalComposition
public import AtiyahSinger.Analysis.SmoothBundleMapPrincipalSymbol
public import AtiyahSinger.Analysis.SmoothBundleMapOperator
public import AtiyahSinger.Geometry.SmoothBundleMapFromSections

/-!
# Principal symbols of finite native operator matrices

Public module ID: M0701.

The same smooth projections and inclusions identify the homogeneous principal
symbol of a finite matrix of actual PDOs. Both the block operators and native
section coordinates are specified, so this does not combine independent
existence witnesses. Used for the original positive Hodge realization.

Source: SG III.3, finite direct sums and principal-symbol composition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped BigOperators Manifold ContDiff

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  {ι κ : Type} [Fintype ι] [Fintype κ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A : ι → SmoothFiniteComplexBundle (n := n) M)
  (B : κ → SmoothFiniteComplexBundle (n := n) M)
  (e : ∀ x, ((i : ι) → (A i).Fiber x) ≃ₗ[ℂ] E.Fiber x)
  (f : ∀ x, ((j : κ) → (B j).Fiber x) ≃ₗ[ℂ] F.Fiber x)
  (Φ : ((i : ι) → smoothSections (n := n) (r := (A i).rank) (A i).Fiber) ≃ₗ[ℂ]
    smoothSections (n := n) (r := E.rank) E.Fiber)
  (Ψ : ((j : κ) → smoothSections (n := n) (r := (B j).rank) (B j).Fiber) ≃ₗ[ℂ]
    smoothSections (n := n) (r := F.rank) F.Fiber)
  (hΦ : ∀ u x, (Φ u).val x = e x (fun i ↦ (u i).val x))
  (hΨ : ∀ u x, (Ψ u).val x = f x (fun j ↦ (u j).val x))
  {m : ℝ}
  (P : (j : κ) → (i : ι) → PseudodifferentialOperator (n := n)
    (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber μ m)


set_option maxHeartbeats 1500000 in
-- The extended limit accommodates elaboration of the specified homogeneous finite block matrix.
set_option maxRecDepth 5000 in
set_option backward.isDefEq.respectTransparency false in
/-- The specified finite matrix has the same pointwise homogeneous block matrix. -/
theorem exists_finiteMatrixPseudodifferentialOperator_homogeneous
    (a : (j : κ) → (i : ι) → homogeneousGlobalSymbolSpace (n := n)
      (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber m)
    (ha : ∀ j i (R : QuantizationPresentation (n := n)
        (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber),
      (P j i).principalSymbol = globalPrincipalSymbolClass (A i).Fiber (B j).Fiber m
        (R.regularizedSymbol m (a j i).val (a j i).property.1 (a j i).property.2)) :
    ∃ b : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m,
      (∀ x ξ u, b.val x ξ (e x u) = f x (fun j ↦ ∑ i, (a j i).val x ξ (u i))) ∧
      ∀ R : QuantizationPresentation (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber,
        (finiteMatrixPseudodifferentialOperator E F A B e f Φ Ψ hΦ hΨ P).principalSymbol =
          globalPrincipalSymbolClass E.Fiber F.Fiber m
            (R.regularizedSymbol m b.val b.property.1 b.property.2) := by
  classical
  let projection (i : ι) (x : M) : E.Fiber x →ₗ[ℂ] (A i).Fiber x :=
    (LinearMap.proj i).comp (e x).symm.toLinearMap
  let inclusion (j : κ) (x : M) : (B j).Fiber x →ₗ[ℂ] F.Fiber x :=
    (f x).toLinearMap.comp (LinearMap.single ℂ (fun j ↦ (B j).Fiber x) j)
  -- The stated section equivalences prove smoothness of these very coordinate maps.
  have hprojection (i : ι) : IsSmoothBundleMap (n := n) (r := E.rank)
      (q := (A i).rank) (projection i) := by
    apply (isSmoothBundleMap_iff_map_smoothSections _).mpr
    intro u
    have heval (x : M) : projection i x (u.val x) = (Φ.symm u i).val x := by
      have h := hΦ (Φ.symm u) x
      rw [Φ.apply_symm_apply] at h
      change (e x).symm (u.val x) i = _
      rw [h, LinearEquiv.symm_apply_apply]
    have hs := (Φ.symm u i).property
    change IsSmoothSection (n := n) (r := (A i).rank) (A i).Fiber
      (fun x ↦ (Φ.symm u i).val x) at hs
    simpa only [heval] using hs
  have hinclusion (j : κ) : IsSmoothBundleMap (n := n) (r := (B j).rank)
      (q := F.rank) (inclusion j) := by
    apply (isSmoothBundleMap_iff_map_smoothSections _).mpr
    intro u
    have heval (x : M) : inclusion j x (u.val x) = (Ψ (Pi.single j u)).val x := by
      rw [hΨ]
      apply congrArg (f x)
      funext k
      by_cases hk : k = j
      · subst k
        simp
      · simp [Pi.single_eq_of_ne hk]
    have hs := (Ψ (Pi.single j u)).property
    change IsSmoothSection (n := n) (r := F.rank) F.Fiber
      (fun x ↦ (Ψ (Pi.single j u)).val x) at hs
    simpa only [heval] using hs
  let R (i : ι) := smoothBundleMapOperator (μ := μ) (projection i) (hprojection i)
  let J (j : κ) := smoothBundleMapOperator (μ := μ) (inclusion j) (hinclusion j)
  have hR (i : ι) (u : (i : ι) →
      smoothSections (n := n) (r := (A i).rank) (A i).Fiber) :
      (R i).toLinearMap (Φ u) = u i := by
    apply Subtype.ext
    funext x
    change (e x).symm ((Φ u).val x) i = (u i).val x
    rw [hΦ, LinearEquiv.symm_apply_apply]
  have hJ (j : κ) (u : smoothSections (n := n) (r := (B j).rank) (B j).Fiber) :
      (J j).toLinearMap u = Ψ (Pi.single j u) := by
    apply Subtype.ext
    funext x
    rw [hΨ]
    change f x (Pi.single j (u.val x)) = f x (fun k ↦
      ((Pi.single j u : (k : κ) → smoothSections (n := n)
        (r := (B k).rank) (B k).Fiber) k).val x)
    apply congrArg (f x)
    funext k
    by_cases hk : k = j
    · subst k
      simp
    · simp [Pi.single_eq_of_ne hk]
  let matrix := finiteMatrixPseudodifferentialOperator E F A B e f Φ Ψ hΦ hΨ P
  -- Keep the genuine zero-order maps; their homogeneous symbols are their fiber maps.
  choose α hα hRclass using fun i ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) (projection i) (hprojection i)
  choose β hβ hJclass using fun j ↦
    exists_homogeneousSymbol_smoothBundleMap (μ := μ) (inclusion j) (hinclusion j)
  let u (j : κ) (i : ι) : homogeneousGlobalSymbolSpace (n := n)
      (r := E.rank) (q := (B j).rank) E.Fiber (B j).Fiber m :=
    ⟨globalSymbolComp (a j i).val (α i).val,
      (a j i).property.1.globalSymbolComp (α i).property.1,
      by simpa only [add_zero] using (a j i).property.2.globalSymbolComp (α i).property.2⟩
  let c (j : κ) (i : ι) : homogeneousGlobalSymbolSpace (n := n)
      (r := E.rank) (q := F.rank) E.Fiber F.Fiber m :=
    ⟨globalSymbolComp (β j).val (u j i).val,
      (β j).property.1.globalSymbolComp (u j i).property.1,
      by simpa only [zero_add] using (β j).property.2.globalSymbolComp (u j i).property.2⟩
  let U (j : κ) (i : ι) : PseudodifferentialOperator (n := n)
      (r := E.rank) (q := (B j).rank) E.Fiber (B j).Fiber μ m :=
    ⟨(P j i).toLinearMap.comp (R i).toLinearMap, by
      simpa only [add_zero] using (P j i).isPseudodifferentialOperator.comp (P j i).toLinearMap
        (R i).toLinearMap (R i).isPseudodifferentialOperator⟩
  let V (j : κ) (i : ι) : PseudodifferentialOperator (n := n)
      (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ m :=
    ⟨(J j).toLinearMap.comp (U j i).toLinearMap, by
      simpa only [zero_add] using (J j).isPseudodifferentialOperator.comp (J j).toLinearMap
        (U j i).toLinearMap (U j i).isPseudodifferentialOperator⟩
  have hmatrix : matrix.toSpace = ∑ j : κ, ∑ i : ι, (V j i).toSpace := by
    apply Subtype.ext
    apply LinearMap.ext
    intro s
    obtain ⟨v, rfl⟩ := Φ.surjective s
    change matrix.toLinearMap (Φ v) =
      (∑ j : κ, ∑ i : ι, (V j i).toSpace).val (Φ v)
    rw [finiteMatrixPseudodifferentialOperator_apply]
    simp only [Submodule.coe_sum, LinearMap.sum_apply]
    change Ψ (fun j ↦ ∑ i, (P j i).toLinearMap (v i)) =
      ∑ j, ∑ i, (J j).toLinearMap ((P j i).toLinearMap ((R i).toLinearMap (Φ v)))
    simp only [hR, hJ]
    simp_rw [← map_sum]
    apply congrArg Ψ
    funext j
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    symm
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      exact Pi.single_eq_of_ne (Ne.symm hk) _
    · simp
  refine ⟨∑ j, ∑ i, c j i, ?_, ?_⟩
  · -- On each fiber these are the given coordinate projections and inclusions.
    intro x ξ v
    simp only [Submodule.coe_sum, Finset.sum_apply, sum_apply]
    have hc (j : κ) (i : ι) : (c j i).val x ξ (e x v) =
        f x (Pi.single j ((a j i).val x ξ (v i))) := by
      change (β j).val x ξ ((a j i).val x ξ ((α i).val x ξ (e x v))) = _
      rw [hα, hβ]
      change f x (Pi.single j ((a j i).val x ξ ((e x).symm (e x v) i))) = _
      rw [LinearEquiv.symm_apply_apply]
    simp_rw [hc, ← map_sum]
    apply congrArg (f x)
    funext j
    simp only [Finset.sum_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      exact Pi.single_eq_of_ne (Ne.symm hk) _
    · simp
  · intro Q
    have hblock (j : κ) (i : ι) : (V j i).principalSymbol =
        globalPrincipalSymbolClass E.Fiber F.Fiber m
          (Q.regularizedSymbol m (c j i).val (c j i).property.1 (c j i).property.2) := by
      obtain ⟨RA⟩ := nonempty_quantizationPresentation (n := n)
        (r := E.rank) (q := (A i).rank) (E := E.Fiber) (F := (A i).Fiber)
      obtain ⟨RP⟩ := nonempty_quantizationPresentation (n := n)
        (r := (A i).rank) (q := (B j).rank) (E := (A i).Fiber) (F := (B j).Fiber)
      obtain ⟨RU⟩ := nonempty_quantizationPresentation (n := n)
        (r := E.rank) (q := (B j).rank) (E := E.Fiber) (F := (B j).Fiber)
      obtain ⟨RJ⟩ := nonempty_quantizationPresentation (n := n)
        (r := (B j).rank) (q := F.rank) (E := (B j).Fiber) (F := F.Fiber)
      have hU := PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp_order
        (add_zero m) RA RP RU (α i) (a j i) (u j i) (R i) (P j i) (U j i)
        (hRclass i RA) (ha j i RP) rfl (fun _ _ _ ↦ rfl)
      exact PseudodifferentialOperator.principalSymbol_eq_regularizedSymbol_of_comp_order
        (zero_add m) RU RJ Q (u j i) (β j) (c j i) (U j i) (J j) (V j i)
        hU (hJclass j RJ) rfl (fun _ _ _ ↦ rfl)
    -- Additivity of the principal quotient uses this same finite operator sum.
    let reg : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m →ₗ[ℂ] globalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
        E.Fiber F.Fiber m := {
      toFun a := Q.regularizedSymbol m a.val a.property.1 a.property.2
      map_add' a b := Subtype.ext (Q.regularizedSymbolFunction_add a.val b.val)
      map_smul' z a := Subtype.ext (Q.regularizedSymbolFunction_smul z a.val) }
    change principalSymbolLinearMap E.Fiber F.Fiber μ m matrix.toSpace = _
    rw [hmatrix, map_sum]
    simp_rw [map_sum]
    change (∑ j, ∑ i, (V j i).principalSymbol) = _
    simp_rw [hblock]
    change (∑ j, ∑ i, globalPrincipalSymbolClass E.Fiber F.Fiber m (reg (c j i))) =
      globalPrincipalSymbolClass E.Fiber F.Fiber m (reg (∑ j, ∑ i, c j i))
    simp only [map_sum]

end AtiyahSinger
