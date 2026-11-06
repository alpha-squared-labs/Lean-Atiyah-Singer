/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ScalarSupportHomotopy
public import AtiyahSinger.Topology.SupportTripleTransport

/-!
# Opposite support classes from a negative scalar square

Public module ID: M2187.

When the two original exterior symbols compose to a negative positive scalar,
their composite deforms to the global negative identity on one fixed exterior.
Their support classes are therefore opposite. The scalar need not be bounded
or bounded away from zero near the compact control.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]

set_option maxHeartbeats 600000 in

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- Two original boundary maps with a negative scalar composite give opposite support classes. -/
theorem CompactSupportTriple.compactSupportClass_eq_neg_of_comp_neg_scalar
    (a : CompactSupportTriple E F) (b : CompactSupportTriple F E)
    (K : Set X) (hK : IsCompact K) (ha : a.control ⊆ K) (hb : b.control ⊆ K)
    (r : C((Kᶜ : Set X), ℝ)) (hr : ∀ x, 0 < r x)
    (hcomp : ∀ (x : (Kᶜ : Set X)) (v : E x.val),
      (b.enlarge K hK hb).boundary.linearEquiv x
        ((a.enlarge K hK ha).boundary.linearEquiv x v) = -(r x : ℂ) • v) :
    b.compactSupportClass = -a.compactSupportClass := by
  let d := a.compose b
  have hdK : d.control ⊆ K := Set.union_subset ha hb
  let n := Iso.scalar E (ContinuousMap.const _ (-1)) (fun _ ↦ neg_ne_zero.mpr one_ne_zero)
  let t := CompactSupportTriple.ofIso n
  let c : C(I × (Kᶜ : Set X), ℂ) :=
    ⟨fun z ↦ -((((1 - (z.1 : ℝ)) * r z.2 + (z.1 : ℝ)) : ℝ) : ℂ), by fun_prop⟩
  have hc (z : I × (Kᶜ : Set X)) : c z ≠ 0 := by
    have hpos : 0 < (1 - (z.1 : ℝ)) * r z.2 + (z.1 : ℝ) := by
      by_cases hz : (z.1 : ℝ) = 1
      · simp only [hz, sub_self, zero_mul, zero_add, zero_lt_one]
      · have ht : (z.1 : ℝ) < 1 := lt_of_le_of_ne z.1.property.2 hz
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht) (hr z.2)) z.1.property.1
    exact neg_ne_zero.mpr (by exact_mod_cast ne_of_gt hpos)
  have hhom : d.Homotopic t := by
    apply CompactSupportTriple.homotopic_of_scalar E d t K hK hdK (Set.empty_subset _) c hc
    · intro x v
      have h := hcomp x v
      rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply] at h
      rw [CompactSupportTriple.enlarge_apply]
      dsimp only [d, CompactSupportTriple.compose, Iso.trans, LinearEquiv.trans_apply]
      rw [CompactSupportTriple.enlarge_apply b (a.control ∪ b.control)
          (a.isCompact_control.union b.isCompact_control) Set.subset_union_right,
        CompactSupportTriple.enlarge_apply a (a.control ∪ b.control)
          (a.isCompact_control.union b.isCompact_control) Set.subset_union_left]
      simpa only [c, ContinuousMap.coe_mk, Set.Icc.coe_zero, sub_zero,
        one_mul, add_zero] using h
    · intro x v
      rw [CompactSupportTriple.enlarge_apply]
      change (-1 : ℂ) • v = c (1, x) • v
      simp only [c, ContinuousMap.coe_mk, Set.Icc.coe_one, sub_self, zero_mul,
        zero_add, Complex.ofReal_one]
  have hzero : a.compactSupportClass + b.compactSupportClass = 0 := by
    rw [← a.compactSupportClass_compose b]
    exact (d.compactSupportClass_eq_of_homotopic t hhom).trans
      (CompactSupportTriple.compactSupportClass_ofIso n)
  exact eq_neg_of_add_eq_zero_right hzero

end AtiyahSinger.ComplexBundle
