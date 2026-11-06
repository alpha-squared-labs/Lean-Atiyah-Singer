/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FiniteMatrixGlobalSymbol
public import AtiyahSinger.Analysis.GradedBundleOperator

/-!
# The full principal symbol of a specified native graded PDO

Public module ID: M0692.

The same native operator whose smooth action is the prescribed graded matrix
has the full block symbol of its four entries. Smooth sum coordinates and the
upper-right sign agree with the Sobolev assembly. Arbitrary global symbols
are admitted, including the actual frequency cutoffs before regularization.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  [CompactSpace M] {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (A B : Fin 2 → SmoothFiniteComplexBundle (n := n) M)

set_option maxHeartbeats 1500000 in
-- The extended limit accommodates the full native block symbol on the specified graded bundle.
/-- The specified native graded PDO has its exact full block symbol as principal representative. -/
theorem exists_globalSymbol_of_gradedBundlePseudodifferentialOperator
    (e : ∀ x, ((A 0).Fiber x × (A 1).Fiber x) ≃ₗ[ℂ] E.Fiber x)
    (f : ∀ x, ((B 0).Fiber x × (B 1).Fiber x) ≃ₗ[ℂ] F.Fiber x)
    (he₀ : IsSmoothBundleMap (n := n) (r := (A 0).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inl ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (he₁ : IsSmoothBundleMap (n := n) (r := (A 1).rank) (q := E.rank)
      (fun x ↦ (e x).toLinearMap.comp (LinearMap.inr ℂ ((A 0).Fiber x) ((A 1).Fiber x))))
    (hf₀ : IsSmoothBundleMap (n := n) (r := (B 0).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inl ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    (hf₁ : IsSmoothBundleMap (n := n) (r := (B 1).rank) (q := F.rank)
      (fun x ↦ (f x).toLinearMap.comp (LinearMap.inr ℂ ((B 0).Fiber x) ((B 1).Fiber x))))
    {m : ℝ}
    (U : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber μ m)
    (V : PseudodifferentialOperator (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber μ m)
    (W : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 0).rank)
      (A 1).Fiber (B 0).Fiber μ m)
    (Z : PseudodifferentialOperator (n := n) (r := (A 1).rank) (q := (B 1).rank)
      (A 1).Fiber (B 1).Fiber μ m)
    (K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ m)
    (hK : ∀ u v, K.toLinearMap (smoothSectionSumEquiv e he₀ he₁ (u, v)) =
      smoothSectionSumEquiv f hf₀ hf₁
        (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v))
    (a : globalSymbolSpace (n := n) (r := (A 0).rank) (q := (B 0).rank)
      (A 0).Fiber (B 0).Fiber m)
    (b : globalSymbolSpace (n := n) (r := (A 0).rank) (q := (B 1).rank)
      (A 0).Fiber (B 1).Fiber m)
    (c : globalSymbolSpace (n := n) (r := (A 1).rank) (q := (B 0).rank)
      (A 1).Fiber (B 0).Fiber m)
    (d : globalSymbolSpace (n := n) (r := (A 1).rank) (q := (B 1).rank)
      (A 1).Fiber (B 1).Fiber m)
    (ha : U.principalSymbol = globalPrincipalSymbolClass (A 0).Fiber (B 0).Fiber m a)
    (hb : V.principalSymbol = globalPrincipalSymbolClass (A 0).Fiber (B 1).Fiber m b)
    (hc : W.principalSymbol = globalPrincipalSymbolClass (A 1).Fiber (B 0).Fiber m c)
    (hd : Z.principalSymbol = globalPrincipalSymbolClass (A 1).Fiber (B 1).Fiber m d) :
    ∃ s : globalSymbolSpace (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m,
      (∀ x ξ u v, s.val x ξ (e x (u, v)) =
        f x (a.val x ξ u - c.val x ξ v, b.val x ξ u + d.val x ξ v)) ∧
      K.principalSymbol = globalPrincipalSymbolClass E.Fiber F.Fiber m s := by
  classical
  let Φ := smoothSectionSumEquiv e he₀ he₁
  let Ψ := smoothSectionSumEquiv f hf₀ hf₁
  let e' (x : M) := (LinearEquiv.piFinTwo ℂ (fun i ↦ (A i).Fiber x)).trans (e x)
  let f' (x : M) := (LinearEquiv.piFinTwo ℂ (fun j ↦ (B j).Fiber x)).trans (f x)
  let Φ' := (LinearEquiv.piFinTwo ℂ
    (fun i ↦ smoothSections (n := n) (r := (A i).rank) (A i).Fiber)).trans Φ
  let Ψ' := (LinearEquiv.piFinTwo ℂ
    (fun j ↦ smoothSections (n := n) (r := (B j).rank) (B j).Fiber)).trans Ψ
  have hΦ' (u : (i : Fin 2) → smoothSections (n := n) (r := (A i).rank) (A i).Fiber)
      (x : M) : (Φ' u).val x = e' x (fun i ↦ (u i).val x) :=
    smoothSectionSumEquiv_apply e he₀ he₁ (u 0) (u 1) x
  have hΨ' (u : (j : Fin 2) → smoothSections (n := n) (r := (B j).rank) (B j).Fiber)
      (x : M) : (Ψ' u).val x = f' x (fun j ↦ (u j).val x) :=
    smoothSectionSumEquiv_apply f hf₀ hf₁ (u 0) (u 1) x
  let P : (j : Fin 2) → (i : Fin 2) → PseudodifferentialOperator (n := n)
      (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber μ m := by
    intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · intro i
      refine Fin.cases U (fun i ↦ ?_) i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact W.smul (-1)
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      intro i
      refine Fin.cases V (fun i ↦ ?_) i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact Z
  let matrix := finiteMatrixPseudodifferentialOperator E F A B e' f' Φ' Ψ' hΦ' hΨ' P
  -- The existing finite-matrix PDO is used with its actual two-component section coordinates.
  have hmatrix (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      matrix.toLinearMap (Φ (u, v)) =
        Ψ (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v) := by
    let w := (LinearEquiv.piFinTwo ℂ
      (fun i ↦ smoothSections (n := n) (r := (A i).rank) (A i).Fiber)).symm (u, v)
    have hw : Φ' w = Φ (u, v) := congrArg Φ
      ((LinearEquiv.piFinTwo ℂ
        (fun i ↦ smoothSections (n := n) (r := (A i).rank) (A i).Fiber)).apply_symm_apply (u, v))
    rw [← hw, finiteMatrixPseudodifferentialOperator_apply]
    change Ψ ((∑ i, (P 0 i).toLinearMap (w i)), (∑ i, (P 1 i).toLinearMap (w i))) = _
    have h00 : P 0 0 = U := rfl
    have h01 : P 0 1 = W.smul (-1) := rfl
    have h10 : P 1 0 = V := rfl
    have h11 : P 1 1 = Z := rfl
    simp only [Fin.sum_univ_two, h00, h01, h10, h11]
    change Ψ (U.toLinearMap u + (-1 : ℂ) • W.toLinearMap v,
      V.toLinearMap u + Z.toLinearMap v) = _
    simp only [neg_one_smul, sub_eq_add_neg]
  let q : (j : Fin 2) → (i : Fin 2) → globalSymbolSpace (n := n)
      (r := (A i).rank) (q := (B j).rank) (A i).Fiber (B j).Fiber m := by
    intro j
    refine Fin.cases ?_ (fun j ↦ ?_) j
    · intro i
      refine Fin.cases a (fun i ↦ ?_) i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact (-1 : ℂ) • c
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      intro i
      refine Fin.cases b (fun i ↦ ?_) i
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact d
  have hq (j i : Fin 2) : (P j i).principalSymbol =
      globalPrincipalSymbolClass (A i).Fiber (B j).Fiber m (q j i) := by
    fin_cases j <;> fin_cases i
    · exact ha
    · change (W.smul (-1)).principalSymbol =
        globalPrincipalSymbolClass (A 1).Fiber (B 0).Fiber m ((-1 : ℂ) • c)
      rw [W.principalSymbol_smul, hc, map_smul]
    · exact hb
    · exact hd
  obtain ⟨s, hs, hclass⟩ := exists_finiteMatrixPseudodifferentialOperator_globalSymbol
    E F A B e' f' Φ' Ψ' hΦ' hΨ' P q hq
  refine ⟨s, ?_, ?_⟩
  · -- The same ordered tensor-free matrix formula holds at every actual covector.
    intro x ξ u v
    let w := (LinearEquiv.piFinTwo ℂ (fun i ↦ (A i).Fiber x)).symm (u, v)
    have hw : e' x w = e x (u, v) := congrArg (e x)
      ((LinearEquiv.piFinTwo ℂ (fun i ↦ (A i).Fiber x)).apply_symm_apply (u, v))
    rw [← hw, hs]
    change f x ((∑ i, (q 0 i).val x ξ (w i)), (∑ i, (q 1 i).val x ξ (w i))) = _
    have h00 : q 0 0 = a := rfl
    have h01 : q 0 1 = (-1 : ℂ) • c := rfl
    have h10 : q 1 0 = b := rfl
    have h11 : q 1 1 = d := rfl
    simp only [Fin.sum_univ_two, h00, h01, h10, h11]
    change f x (a.val x ξ u + (-1 : ℂ) • c.val x ξ v,
      b.val x ξ u + d.val x ξ v) = _
    simp only [neg_one_smul, sub_eq_add_neg]
  · -- Equality of original section maps identifies the symbol of the specified operator K.
    have heq : K.toLinearMap = matrix.toLinearMap := by
      apply LinearMap.ext
      intro u
      obtain ⟨⟨u, v⟩, rfl⟩ := Φ.surjective u
      exact (hK u v).trans (hmatrix u v).symm
    exact (K.principalSymbol_eq_of_toLinearMap_eq μ matrix heq).trans hclass

end AtiyahSinger
