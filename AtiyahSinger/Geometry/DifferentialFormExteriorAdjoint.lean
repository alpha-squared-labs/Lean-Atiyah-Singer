/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DifferentialFormMetric
public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Exterior multiplication and insertion for the normalized form metric

Public module ID: M1164.

For the original induced form metric, exterior multiplication by the covector
flat(v) is adjoint to insertion of v in the first slot. The factor 1/p! in the
original metric cancels exactly the p+1 choices in the alternating sum.
The proof retains the original tangent fibers and complex-valued forms.

Source: the induced metric on exterior powers and the Hodge principal symbol,
Lawson--Michelsohn, Spin Geometry, II.5.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Module
open scoped BigOperators Manifold ContDiff ComplexConjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

set_option maxHeartbeats 1600000 in
-- Keep the original ordered-tuple normalization and each finite insertion reindexing.
set_option backward.isDefEq.respectTransparency false in
/-- Exterior multiplication by `flat(v)` is adjoint to insertion for the original form metric. -/
theorem differentialFormInner_alternatizeUncurryFin
    (g : SmoothTangentMetric (n := n) (M := M)) (p : ℕ) (x : M)
    (v : EuclideanSpace ℝ (Fin n))
    (α : DifferentialFormFiber (n := n) p x)
    (β : DifferentialFormFiber (n := n) (p + 1) x) :
    differentialFormInner g (p + 1) x
        (ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ)
          (E := EuclideanSpace ℝ (Fin n)) ((g.inner x v).smulRight α)) β =
      differentialFormInner g p x α (β.curryLeft v) := by
  classical
  change EuclideanSpace ℝ (Fin n) [⋀^Fin p]→L[ℝ] ℂ at α
  change EuclideanSpace ℝ (Fin n) [⋀^Fin (p + 1)]→L[ℝ] ℂ at β
  let V := EuclideanSpace ℝ (Fin n)
  -- Choose coordinates using a temporary metric copy, retaining the original form topology.
  obtain ⟨e, he⟩ : ∃ e : Fin n → V,
      ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0 := by
    let a : Basis (Fin n) ℝ V := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    let : FiniteDimensional ℝ V := Module.Finite.of_basis a
    let W := ULift.{0} V
    let core : InnerProductSpace.Core ℝ W :=
      { inner u v := g.inner x u.down v.down
        conj_inner_symm u v := g.symm x v.down u.down
        re_inner_nonneg v := by
          by_cases hv : v.down = 0
          · simp [hv]
          · exact (g.pos x v.down hv).le
        add_left u v w := by
          change g.inner x (u.down + v.down) w.down = _
          simp
        smul_left u v c := by
          change g.inner x (c • u.down) v.down = c * g.inner x u.down v.down
          simp
        definite v h := by
          have hv : v.down = 0 := by
            by_contra hv
            exact (ne_of_gt (g.pos x v.down hv)) h
          exact ULift.ext hv }
    let : InnerProductSpace.Core ℝ W := core
    let : NormedAddCommGroup W := core.toNormedAddCommGroup
    let : SeminormedAddCommGroup W := core.toNormedAddCommGroup.toSeminormedAddCommGroup
    let : InnerProductSpace ℝ W := InnerProductSpace.ofCore core.toCore
    let : FiniteDimensional ℝ W :=
      (ULift.moduleEquiv (R := ℝ) (M := V)).symm.finiteDimensional
    have hdim : Module.finrank ℝ W = n := by
      rw [(ULift.moduleEquiv (R := ℝ) (M := V)).finrank_eq]
      simpa using Module.finrank_eq_card_basis a
    let b : OrthonormalBasis (Fin n) ℝ W :=
      (stdOrthonormalBasis ℝ W).reindex (finCongr hdim)
    let e : Fin n → V := fun i ↦ (b i).down
    have he (i j : Fin n) : g.inner x (e i) (e j) = if i = j then 1 else 0 :=
      b.inner_eq_ite i j
    exact ⟨e, he⟩
  have hspan (w : V) : (∑ i, g.inner x w (e i) • e i) = w := by
    -- Orthonormality gives a basis; compute its coefficients in the original normed space.
    have hli : LinearIndependent ℝ e := by
      apply Fintype.linearIndependent_iff.mpr
      intro c hc i
      have h := congrArg (g.inner x (e i)) hc
      simpa [map_sum, map_smul, he] using h
    let d : Basis (Fin n) ℝ V := Basis.mk hli
      (hli.span_eq_top_of_card_eq_finrank' (by simp [V])).ge
    have hd (i : Fin n) : d i = e i := Basis.mk_apply hli _ i
    have hc (i : Fin n) : d.repr w i = g.inner x w (e i) := by
      have hs := congrArg (g.inner x (e i)) (d.sum_repr w)
      simp only [map_sum, map_smul, hd, he, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true] at hs
      exact hs.trans (g.symm x (e i) w)
    simpa only [hc, hd] using d.sum_repr w
  let ξ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := g.inner x v
  let Wα := ContinuousAlternatingMap.alternatizeUncurryFin (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin n)) (ξ.smulRight α)
  let T := ∑ I : Fin p → Fin n,
    conj (α (fun k ↦ e (I k))) * (β.curryLeft v) (fun k ↦ e (I k))
  -- Inserting one index is a bijection of the full ordered tuples; no repeated tuples are dropped.
  have hterm (j : Fin (p + 1)) :
      (∑ I : Fin (p + 1) → Fin n,
        conj (((-1 : ℤ) ^ j.val) • (ξ (e (I j)) •
          α (fun k ↦ e (I (j.succAbove k))))) * β (fun k ↦ e (I k))) = T := by
    let split : (Fin n × (Fin p → Fin n)) ≃ (Fin (p + 1) → Fin n) :=
      Fin.insertNthEquiv (fun _ ↦ Fin n) j
    rw [← split.sum_comp]
    rw [Fintype.sum_prod_type]
    have hvalue (i : Fin n) (I : Fin p → Fin n) :
        conj (((-1 : ℤ) ^ j.val) • (ξ (e ((split (i, I)) j)) •
            α (fun k ↦ e ((split (i, I)) (j.succAbove k))))) *
          β (fun k ↦ e ((split (i, I)) k)) =
        conj (α (fun k ↦ e (I k))) *
          (ξ (e i) • β (Matrix.vecCons (e i) (fun k ↦ e (I k)))) := by
      have hvector : (fun k ↦ e (Fin.insertNth (α := fun _ ↦ Fin n) j i I k)) =
          Fin.insertNth (α := fun _ ↦ V) j (e i) (fun k ↦ e (I k)) := by
        symm
        apply (Fin.insertNth_eq_iff).mpr
        constructor
        · simp only [Fin.insertNth_apply_same]
        · funext k
          simp only [Fin.removeNth_apply, Fin.insertNth_apply_succAbove]
      have hb := β.toAlternatingMap.neg_one_pow_smul_map_insertNth j (e i)
        (fun k ↦ e (I k))
      change ((-1 : ℤ) ^ j.val) • β (j.insertNth (e i) (fun k ↦ e (I k))) =
        β (Matrix.vecCons (e i) (fun k ↦ e (I k))) at hb
      simp only [split, Fin.insertNthEquiv_apply, Fin.insertNth_apply_same,
        Fin.insertNth_apply_succAbove]
      rw [hvector]
      calc
        _ = conj (α (fun k ↦ e (I k))) *
            (ξ (e i) • (((-1 : ℤ) ^ j.val) •
              β (j.insertNth (e i) (fun k ↦ e (I k))))) := by
          simp only [Complex.real_smul, zsmul_eq_mul, map_mul, map_intCast,
            Complex.conj_ofReal]
          ring
        _ = _ := by rw [hb]
    simp_rw [hvalue]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    rw [← Finset.mul_sum]
    apply congrArg (conj (α (fun k ↦ e (I k))) * ·)
    have hv := congrArg (fun w : V ↦ (β.curryLeft w) (fun k ↦ e (I k))) (hspan v)
    simp only [map_sum, map_smul, ContinuousAlternatingMap.sum_apply,
      ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.curryLeft_apply_apply] at hv
    exact hv
  have hsum : (∑ I : Fin (p + 1) → Fin n,
      conj (Wα (fun k ↦ e (I k))) * β (fun k ↦ e (I k))) = (p + 1 : ℂ) * T := by
    simp only [Wα, ContinuousAlternatingMap.alternatizeUncurryFin_apply,
      ContinuousLinearMap.smulRight_apply, ContinuousAlternatingMap.smul_apply,
      map_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    change (∑ j : Fin (p + 1), ∑ I : Fin (p + 1) → Fin n,
      conj (((-1 : ℤ) ^ j.val) • (ξ (e (I j)) •
        α (fun k ↦ e (I (j.succAbove k))))) * β (fun k ↦ e (I k))) = _
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
  -- The p+1 equal insertion terms cancel precisely the successor factorial normalization.
  rw [differentialFormInner_eq_sum_orthonormal g (p + 1) x e he,
    differentialFormInner_eq_sum_orthonormal g p x e he]
  change ((p + 1).factorial : ℂ)⁻¹ *
    (∑ I : Fin (p + 1) → Fin n, conj (Wα (fun k ↦ e (I k))) * β (fun k ↦ e (I k))) =
      (p.factorial : ℂ)⁻¹ * T
  rw [hsum, Nat.factorial_succ, Nat.cast_mul]
  have hp : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
  have hsucc : (p + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero p
  push_cast
  field_simp

end AtiyahSinger
