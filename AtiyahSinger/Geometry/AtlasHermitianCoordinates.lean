/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AtlasHermitianMetric
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Gram operators of the original atlas metric

Public module ID: M1096.

Each original frame identifies the specified Hermitian pairing with its positive
Gram operator on that frame's finite coordinate space. Positivity gives invertibility
on the frame domain, including rank zero. A smooth specified metric gives smooth
Gram operators there. These coordinates support
both opposite-order Sobolev duality and local connection computations.

This is the standard coordinate description of a Hermitian metric, as used in
Spin Geometry III.2. No original fiber topology or metric is replaced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothComplexBundleAtlas

open Bundle
open scoped BigOperators Manifold ContDiff ComplexConjugate Matrix.Norms.Elementwise

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] (A : SmoothComplexBundleAtlas (n := n) E)
  (h : ComplexBundle.ContinuousHermitianMetric E)

open Classical in
/-- The specified metric as an operator in each original finite frame. -/
def hermitianGramOperator (i : A.Index) (x : M) :
    EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i)) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    (fun a b ↦ if hx : x ∈ (A.chart i).baseSet then
      (h.toCore x).inner ((A.frameLinearEquiv i x hx).symm (Pi.single a 1))
        ((A.frameLinearEquiv i x hx).symm (Pi.single b 1)) else 0))

/-- The Gram coordinates recover the exact original fiber pairing. -/
theorem pairing_eq_hermitianGramOperator (i : A.Index) (x : M)
    (hx : x ∈ (A.chart i).baseSet) (u v : E x) :
    (h.toCore x).inner u v =
      inner ℂ ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
        ((A.frameLinearEquiv i x hx) u))
        (A.hermitianGramOperator h i x
          ((EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm
            ((A.frameLinearEquiv i x hx) v))) := by
  classical
  let V (i : A.Index) := EuclideanSpace ℂ (Fin (A.rank i))
  let e (i : A.Index) := EuclideanSpace.equiv (Fin (A.rank i)) ℂ
  let C (i : A.Index) (x : M) (hx : x ∈ (A.chart i).baseSet) : E x ≃ₗ[ℂ] V i :=
    (A.frameLinearEquiv i x hx).trans (e i).symm.toLinearEquiv
  let G (i : A.Index) (x : M) : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ :=
    fun a b ↦ if hx : x ∈ (A.chart i).baseSet then
      (h.toCore x).inner ((C i x hx).symm (EuclideanSpace.single a 1))
        ((C i x hx).symm (EuclideanSpace.single b 1)) else 0
  let Q := A.hermitianGramOperator h
  have hQapply (i : A.Index) (x : M) (v : V i) (a : Fin (A.rank i)) :
      Q i x v a = ∑ b, G i x a b * v b := rfl
  change (h.toCore x).inner u v = inner ℂ (C i x hx u) (Q i x (C i x hx v))
  -- Expand both vectors in the same original inverse frame and use sesquilinearity.
  let : InnerProductSpace.Core ℂ (E x) := h.toCore x
  let B : E x →ₗ⋆[ℂ] E x →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ _ _ (h.toCore x).inner
      (fun a b c ↦ (h.toCore x).add_left a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_left _ _)
      (fun a b c ↦ InnerProductSpace.Core.inner_add_right a b c)
      (fun _ _ _ ↦ InnerProductSpace.Core.inner_smul_right _ _)
  have hexpand (w : E x) :
      ∑ a : Fin (A.rank i), (C i x hx w) a •
        (C i x hx).symm (EuclideanSpace.single a 1) = w := by
    simpa only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr, LinearEquiv.symm_apply_apply] using
        congrArg (C i x hx).symm
          ((EuclideanSpace.basisFun (Fin (A.rank i)) ℂ).sum_repr (C i x hx w))
  have hexpansion : (h.toCore x).inner u v =
      ∑ a, ∑ b, conj ((C i x hx u) a) * G i x a b * (C i x hx v) b := by
    change B u v = _
    conv_lhs => rw [← hexpand u, map_sum]
    simp only [LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply]
    apply Finset.sum_congr rfl
    intro a _
    conv_lhs => rw [← hexpand v, map_sum]
    simp only [map_smul, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    dsimp only [G]
    rw [dite_eq_left hx]
    change conj ((C i x hx u) a) * ((C i x hx v) b *
      (h.toCore x).inner ((C i x hx).symm (EuclideanSpace.single a 1))
        ((C i x hx).symm (EuclideanSpace.single b 1))) = _
    ring
  rw [hexpansion, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro a _
  change (∑ b, conj ((C i x hx u) a) * G i x a b * (C i x hx v) b) =
    (Q i x (C i x hx v)) a * conj ((C i x hx u) a)
  rw [hQapply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The original smooth metric gives smooth Gram operators on every actual frame domain. -/
theorem contMDiffOn_hermitianGramOperator (hh : A.IsSmoothHermitianMetric h) (i : A.Index) :
    ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ]
        EuclideanSpace ℂ (Fin (A.rank i))) ∞
      (A.hermitianGramOperator h i) (A.chart i).baseSet := by
  let toOp : Matrix (Fin (A.rank i)) (Fin (A.rank i)) ℂ →L[ℝ]
      (EuclideanSpace ℂ (Fin (A.rank i)) →L[ℂ] EuclideanSpace ℂ (Fin (A.rank i))) :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap.toLinearMap.comp
        Matrix.toEuclideanLin.toLinearMap).restrictScalars ℝ)
  apply toOp.contDiff.contMDiff.comp_contMDiffOn
  apply contMDiffOn_pi_space.mpr
  intro a
  apply contMDiffOn_pi_space.mpr
  intro b
  exact hh i a b

/-- Positivity makes the same Gram operator an equivalence, including in rank zero. -/
theorem exists_equiv_hermitianGramOperator (i : A.Index) (x : M)
    (hx : x ∈ (A.chart i).baseSet) :
    ∃ Q : EuclideanSpace ℂ (Fin (A.rank i)) ≃L[ℂ] EuclideanSpace ℂ (Fin (A.rank i)),
      Q.toContinuousLinearMap = A.hermitianGramOperator h i x := by
  let V := EuclideanSpace ℂ (Fin (A.rank i))
  let C : E x ≃ₗ[ℂ] V := (A.frameLinearEquiv i x hx).trans
    (EuclideanSpace.equiv (Fin (A.rank i)) ℂ).symm.toLinearEquiv
  let Q := A.hermitianGramOperator h i x
  -- A zero image has zero original metric length, hence is the zero vector.
  have hinj : Function.Injective Q := by
    intro u v huv
    have hz : Q (u - v) = 0 := by rw [map_sub, huv, sub_self]
    have hp := A.pairing_eq_hermitianGramOperator h i x hx
      (C.symm (u - v)) (C.symm (u - v))
    change (h.toCore x).inner (C.symm (u - v)) (C.symm (u - v)) =
      inner ℂ (C (C.symm (u - v))) (Q (C (C.symm (u - v)))) at hp
    rw [LinearEquiv.apply_symm_apply, hz, inner_zero_right] at hp
    have hv : C.symm (u - v) = 0 := (h.toCore x).definite _ hp
    apply sub_eq_zero.mp
    simpa only [LinearEquiv.apply_symm_apply, map_zero] using congrArg C hv
  -- Finite dimensionality upgrades the injective endomorphism to an equivalence.
  let e := (LinearEquiv.ofBijective Q.toLinearMap
    ⟨hinj, LinearMap.surjective_of_injective hinj⟩).toContinuousLinearEquiv
  exact ⟨e, rfl⟩

end AtiyahSinger.SmoothComplexBundleAtlas
