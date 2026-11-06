/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedBlockOperator
public import AtiyahSinger.Analysis.GradedHodgeFiniteAssembly
public import AtiyahSinger.Analysis.SmoothSectionBundleSum
public import AtiyahSinger.Analysis.SobolevBundleSum

/-!
# A graded block matrix on its original native smooth sums

Public module ID: M0694.

The existing finite-matrix construction assembles four actual PDOs into one
native operator, using the specified sum inclusions and their actual inverses.
Its realization in any specified Sobolev orders is exactly the graded bounded
matrix under the same completion identifications. This is the analytic sum
bridge used for product cutoffs, with the original upper-right minus sign.
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
-- The extended limit accommodates the four specified native PDO blocks and their Sobolev matrix.
/-- Four actual PDO blocks form one native graded operator with exactly its Sobolev matrix. -/
theorem exists_gradedBundlePseudodifferentialOperator
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
    (D : (i : Fin 2) → SmoothBundlePresentation (n := n) (r := (A i).rank) (A i).Fiber)
    (H : (j : Fin 2) → SmoothBundlePresentation (n := n) (r := (B j).rank) (B j).Fiber)
    (S : SmoothBundlePresentation (n := n) (r := E.rank) E.Fiber)
    (T : SmoothBundlePresentation (n := n) (r := F.rank) F.Fiber)
    (s t : ℝ) (hst : t ≤ s - m) :
    let Φ := smoothSectionSumEquiv e he₀ he₁
    let Ψ := smoothSectionSumEquiv f hf₀ hf₁
    ∃ K : PseudodifferentialOperator (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber μ m,
      (∀ u v, K.toLinearMap (Φ (u, v)) =
        Ψ (U.toLinearMap u - W.toLinearMap v, V.toLinearMap u + Z.toLinearMap v)) ∧
      ∃ (I : S.SobolevSpace s ≃L[ℂ]
          WithLp 2 ((D 0).SobolevSpace s × (D 1).SobolevSpace s))
        (O : T.SobolevSpace t ≃L[ℂ]
          WithLp 2 ((H 0).SobolevSpace t × (H 1).SobolevSpace t)),
        (∀ u v, I (S.smoothToSobolev s (Φ (u, v))) =
          WithLp.toLp 2 ((D 0).smoothToSobolev s u, (D 1).smoothToSobolev s v)) ∧
        (∀ u v, O (T.smoothToSobolev t (Ψ (u, v))) =
          WithLp.toLp 2 ((H 0).smoothToSobolev t u, (H 1).smoothToSobolev t v)) ∧
        O.toContinuousLinearMap.comp (K.sobolevRealization S T s t hst) =
          (gradedBlockOperator (U.sobolevRealization (D 0) (H 0) s t hst)
            (V.sobolevRealization (D 0) (H 1) s t hst)
            (W.sobolevRealization (D 1) (H 0) s t hst)
            (Z.sobolevRealization (D 1) (H 1) s t hst)).comp I.toContinuousLinearMap := by
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
  let K := finiteMatrixPseudodifferentialOperator E F A B e' f' Φ' Ψ' hΦ' hΨ' P
  -- The existing finite-matrix PDO is used with its actual two-component section coordinates.
  have hK (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      K.toLinearMap (Φ (u, v)) =
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
  obtain ⟨I₀, hI₀⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ)
    e he₀ he₁ (D 0) (D 1) S s
  obtain ⟨O₀, hO₀⟩ := exists_sobolevEquiv_of_smoothBundleSum (μ := μ)
    f hf₀ hf₁ (H 0) (H 1) T t
  let I := I₀.trans (WithLp.prodContinuousLinearEquiv 2 ℂ
    ((D 0).SobolevSpace s) ((D 1).SobolevSpace s)).symm
  let O := O₀.trans (WithLp.prodContinuousLinearEquiv 2 ℂ
    ((H 0).SobolevSpace t) ((H 1).SobolevSpace t)).symm
  have hI (u : smoothSections (n := n) (r := (A 0).rank) (A 0).Fiber)
      (v : smoothSections (n := n) (r := (A 1).rank) (A 1).Fiber) :
      I (S.smoothToSobolev s (Φ (u, v))) =
        WithLp.toLp 2 ((D 0).smoothToSobolev s u, (D 1).smoothToSobolev s v) := by
    have h := hI₀ (Φ (u, v))
    change I₀ (S.smoothToSobolev s (Φ (u, v))) =
      ((D 0).smoothToSobolev s ((Φ.symm (Φ (u, v))).1),
        (D 1).smoothToSobolev s ((Φ.symm (Φ (u, v))).2)) at h
    rw [Φ.symm_apply_apply] at h
    exact congrArg (WithLp.toLp 2) h
  have hO (u : smoothSections (n := n) (r := (B 0).rank) (B 0).Fiber)
      (v : smoothSections (n := n) (r := (B 1).rank) (B 1).Fiber) :
      O (T.smoothToSobolev t (Ψ (u, v))) =
        WithLp.toLp 2 ((H 0).smoothToSobolev t u, (H 1).smoothToSobolev t v) := by
    have h := hO₀ (Ψ (u, v))
    change O₀ (T.smoothToSobolev t (Ψ (u, v))) =
      ((H 0).smoothToSobolev t ((Ψ.symm (Ψ (u, v))).1),
        (H 1).smoothToSobolev t ((Ψ.symm (Ψ (u, v))).2)) at h
    rw [Ψ.symm_apply_apply] at h
    exact congrArg (WithLp.toLp 2) h
  refine ⟨K, hK, I, O, hI, hO, ?_⟩
  -- Agreement on the original native smooth core identifies the complete bounded maps.
  apply DFunLike.coe_injective
  apply (S.denseRange_smoothToSobolev s).equalizer
    (O.toContinuousLinearMap.comp (K.sobolevRealization S T s t hst)).continuous
    ((gradedBlockOperator (U.sobolevRealization (D 0) (H 0) s t hst)
      (V.sobolevRealization (D 0) (H 1) s t hst)
      (W.sobolevRealization (D 1) (H 0) s t hst)
      (Z.sobolevRealization (D 1) (H 1) s t hst)).comp I.toContinuousLinearMap).continuous
  funext u
  obtain ⟨⟨u, v⟩, rfl⟩ := Φ.surjective u
  change O (K.sobolevRealization S T s t hst (S.smoothToSobolev s (Φ (u, v)))) = _
  rw [K.sobolevRealization_smoothToSobolev, hK, hO]
  change _ = gradedBlockOperator _ _ _ _ (I (S.smoothToSobolev s (Φ (u, v))))
  rw [hI]
  apply WithLp.ofLp_injective
  change ((H 0).smoothToSobolev t (U.toLinearMap u - W.toLinearMap v),
      (H 1).smoothToSobolev t (V.toLinearMap u + Z.toLinearMap v)) =
    (U.sobolevRealization (D 0) (H 0) s t hst ((D 0).smoothToSobolev s u) +
      -(W.sobolevRealization (D 1) (H 0) s t hst ((D 1).smoothToSobolev s v)),
      V.sobolevRealization (D 0) (H 1) s t hst ((D 0).smoothToSobolev s u) +
        Z.sobolevRealization (D 1) (H 1) s t hst ((D 1).smoothToSobolev s v))
  simp only [PseudodifferentialOperator.sobolevRealization_smoothToSobolev,
    map_add, map_neg, sub_eq_add_neg]

end AtiyahSinger
