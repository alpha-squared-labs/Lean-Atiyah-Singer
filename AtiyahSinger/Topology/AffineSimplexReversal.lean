/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AffineSimplexChains
public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Signed reversal of ordered affine simplices

Public module ID: M1523.

Reversing all vertices with its permutation sign gives a chain map. Coning the
boundary discrepancy to the original first vertex gives a homotopy to the
identity. These finite vertex expressions stay inside the supplied simplex on
geometric realization, including when it lies in a specified subspace.

Source: the standard reversal proof of graded commutativity of the singular
cup product; the cone construction is the same elementary acyclic-carrier
argument used for affine subdivision.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators

universe u v w

variable (R : Type u) [CommRing R]

/-- The sign of reversing an ordered tuple of k vertices. -/
def vertexReversalSign (k : ℕ) : R := (-1 : R) ^ (k.choose 2)

/-- Appending one vertex introduces precisely k new reversed pairs. -/
theorem vertexReversalSign_succ (k : ℕ) :
    vertexReversalSign R (k + 1) = (-1 : R) ^ k * vertexReversalSign R k := by
  simp only [vertexReversalSign, Nat.choose_succ_succ, Nat.choose_one_right, pow_add]

/-- The tuple sign agrees with the usual sign for a simplex of dimension n. -/
theorem vertexReversalSign_eq_degree (n : ℕ) :
    vertexReversalSign R (n + 1) = (-1 : R) ^ (n * (n + 1) / 2) := by
  simp only [vertexReversalSign, Nat.choose_two_right, Nat.add_sub_cancel]
  rw [Nat.mul_comm]

/-- The sign difference of product dimensions is exactly the graded-commutativity sign. -/
theorem vertexReversalSign_add_degree (p q : ℕ) :
    vertexReversalSign R (p + q + 1) =
      (-1 : R) ^ (p * q) * vertexReversalSign R (p + 1) *
        vertexReversalSign R (q + 1) := by
  have hchoose : (p + q + 1).choose 2 = (p + 1).choose 2 + (q + 1).choose 2 + p * q := by
    induction p with
    | zero => simp
    | succ p ih =>
      have hp : (p + 1 + 1).choose 2 = (p + 1) + (p + 1).choose 2 := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
      rw [show p + 1 + q + 1 = (p + q + 1) + 1 by omega,
        Nat.choose_succ_succ, Nat.choose_one_right, ih, hp]
      ring
  simp only [vertexReversalSign, hchoose, pow_add]
  ring

variable (E : Type v)

/-- Reverse an ordered tuple and multiply by its orientation sign. -/
def vertexChainReversal (k : ℕ) :
    SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R E k :=
  vertexReversalSign R k • Finsupp.lmapDomain R R (fun v : Fin k → E ↦ v ∘ Fin.rev)

/-- Signed reversal retains precisely one reversed generator with its original coefficient. -/
theorem vertexChainReversal_single (k : ℕ) (v : Fin k → E) (a : R) :
    vertexChainReversal R E k (Finsupp.single v a) =
      vertexReversalSign R k • Finsupp.single (v ∘ Fin.rev) a := by
  simp [vertexChainReversal]

/-- Signed reversal commutes with the original alternating boundary, including augmentation. -/
theorem vertexChainReversal_boundary (k : ℕ) (c : SimplexVertexChain R E (k + 1)) :
    vertexChainBoundary R E k (vertexChainReversal R E (k + 1) c) =
      vertexChainReversal R E k (vertexChainBoundary R E k c) := by
  classical
  suffices h : (vertexChainBoundary R E k).comp (vertexChainReversal R E (k + 1)) =
      (vertexChainReversal R E k).comp (vertexChainBoundary R E k) from
    congrArg (fun f ↦ f c) h
  apply Finsupp.lhom_ext
  intro v a
  simp only [LinearMap.comp_apply, vertexChainReversal_single, vertexChainBoundary_single,
    map_smul, map_sum, Finset.smul_sum]
  -- Reverse the face index together with every remaining vertex.
  apply Finset.sum_bij (fun i _ ↦ i.rev)
  · simp
  · intro i _ j _ hij
    exact Fin.rev_injective hij
  · intro j _
    exact ⟨j.rev, Finset.mem_univ _, Fin.rev_rev j⟩
  · intro i _
    have hface : (v ∘ Fin.rev) ∘ i.succAbove = (v ∘ i.rev.succAbove) ∘ Fin.rev := by
      funext j
      simp only [Function.comp_apply, Fin.rev_succAbove]
    have hsign : vertexReversalSign R (k + 1) * (-1 : R) ^ i.val =
        (-1 : R) ^ i.rev.val * vertexReversalSign R k := by
      rw [vertexReversalSign_succ]
      have hdim : k = i.rev.val + i.val := by simp only [Fin.val_rev]; omega
      have hp : (-1 : R) ^ k = (-1 : R) ^ i.rev.val * (-1 : R) ^ i.val := by
        calc
          _ = (-1 : R) ^ (i.rev.val + i.val) := congrArg (fun n ↦ (-1 : R) ^ n) hdim
          _ = _ := pow_add _ _ _
      rw [hp]
      have hsquare : (-1 : R) ^ i.val * (-1 : R) ^ i.val = 1 := by
        rw [← mul_pow]
        simp
      calc
        _ = (-1 : R) ^ i.rev.val * vertexReversalSign R k *
            ((-1 : R) ^ i.val * (-1 : R) ^ i.val) := by ring
        _ = _ := by rw [hsquare, mul_one]
    rw [hface]
    simp only [smul_smul]
    congr 1
    calc
      _ = a * (vertexReversalSign R (k + 1) * (-1 : R) ^ i.val) := by ring
      _ = _ := by rw [hsign]

variable {E}

/-- Mapping vertices commutes with signed reversal of their order. -/
theorem vertexChainMap_reversal {F : Type w} (f : E → F) (k : ℕ)
    (c : SimplexVertexChain R E k) :
    vertexChainMap R E f k (vertexChainReversal R E k c) =
      vertexChainReversal R F k (vertexChainMap R E f k c) := by
  classical
  suffices h : (vertexChainMap R E f k).comp (vertexChainReversal R E k) =
      (vertexChainReversal R F k).comp (vertexChainMap R E f k) from
    congrArg (fun g ↦ g c) h
  apply Finsupp.lhom_ext
  intro v a
  simp [vertexChainMap, vertexChainReversal_single, Function.comp_assoc]

variable (E)

/-- The cone homotopy from signed reversal to the identity on augmented vertex chains. -/
def vertexChainReversalHomotopy :
    (k : ℕ) → SimplexVertexChain R E k →ₗ[R] SimplexVertexChain R E (k + 1)
  | 0 => 0
  | k + 1 => Finsupp.linearCombination R (fun v : Fin (k + 1) → E ↦
      vertexChainCone R E (v 0) (k + 1)
        (Finsupp.single v 1 - vertexChainReversal R E (k + 1) (Finsupp.single v 1) -
          vertexChainReversalHomotopy k
            (vertexChainBoundary R E k (Finsupp.single v 1))))

/-- The homotopy cones the same simplex discrepancy at its original first vertex. -/
theorem vertexChainReversalHomotopy_single (k : ℕ) (v : Fin (k + 1) → E) (a : R) :
    vertexChainReversalHomotopy R E (k + 1) (Finsupp.single v a) =
      a • vertexChainCone R E (v 0) (k + 1)
        (Finsupp.single v 1 - vertexChainReversal R E (k + 1) (Finsupp.single v 1) -
          vertexChainReversalHomotopy R E k
            (vertexChainBoundary R E k (Finsupp.single v 1))) := by
  exact Finsupp.linearCombination_single _ _ _

/-- The finite cone construction satisfies the actual augmented chain homotopy equation. -/
theorem vertexChainReversalHomotopy_boundary (k : ℕ)
    (c : SimplexVertexChain R E (k + 1)) :
    vertexChainBoundary R E (k + 1) (vertexChainReversalHomotopy R E (k + 1) c) =
      c - vertexChainReversal R E (k + 1) c -
        vertexChainReversalHomotopy R E k (vertexChainBoundary R E k c) := by
  classical
  induction k with
  | zero =>
    suffices h : (vertexChainBoundary R E 1).comp (vertexChainReversalHomotopy R E 1) =
        LinearMap.id - vertexChainReversal R E 1 -
          (vertexChainReversalHomotopy R E 0).comp (vertexChainBoundary R E 0) from
      congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    -- In the first degree the augmentation of the discrepancy is zero.
    simp only [LinearMap.comp_apply, vertexChainReversalHomotopy_single, map_smul,
      vertexChainBoundary_cone, map_sub, vertexChainReversal_boundary,
      LinearMap.sub_apply, LinearMap.id_apply]
    simp only [vertexChainReversalHomotopy, LinearMap.zero_apply, map_zero, sub_zero]
    have haug (d : SimplexVertexChain R E 0) : vertexChainReversal R E 0 d = d := by
      have hempty : (fun v : Fin 0 → E ↦ v ∘ Fin.rev) = id := by
        funext v i
        exact Fin.elim0 i
      simp [vertexChainReversal, vertexReversalSign, hempty]
    rw [haug]
    rw [← Finsupp.smul_single_one v a, map_smul, smul_sub]
    simp only [smul_sub]
    abel
  | succ k hk =>
    suffices h : (vertexChainBoundary R E (k + 2)).comp
        (vertexChainReversalHomotopy R E (k + 2)) =
        LinearMap.id - vertexChainReversal R E (k + 2) -
          (vertexChainReversalHomotopy R E (k + 1)).comp
            (vertexChainBoundary R E (k + 1)) from congrArg (fun f ↦ f c) h
    apply Finsupp.lhom_ext
    intro v a
    let b : SimplexVertexChain R E (k + 2) := Finsupp.single v 1
    -- The induction equation and boundary-square identity make this discrepancy a cycle.
    have hcycle : vertexChainBoundary R E (k + 1)
        (b - vertexChainReversal R E (k + 2) b -
          vertexChainReversalHomotopy R E (k + 1) (vertexChainBoundary R E (k + 1) b)) =
        0 := by
      rw [map_sub, map_sub, vertexChainReversal_boundary, hk,
        vertexChainBoundary_boundary, map_zero, sub_zero, sub_self]
    simp only [LinearMap.comp_apply, vertexChainReversalHomotopy_single, map_smul,
      vertexChainBoundary_cone, LinearMap.sub_apply, LinearMap.id_apply]
    change a • (b - vertexChainReversal R E (k + 2) b -
      vertexChainReversalHomotopy R E (k + 1) (vertexChainBoundary R E (k + 1) b) -
      vertexChainCone R E (v 0) (k + 1) _) = _
    rw [hcycle, map_zero, sub_zero]
    rw [← Finsupp.smul_single_one v a]
    simp only [map_smul, smul_sub]
    rfl

variable {E}

/-- The same cone homotopy is natural for maps of its vertices. -/
theorem vertexChainMap_reversalHomotopy {F : Type w} (f : E → F) (k : ℕ)
    (c : SimplexVertexChain R E k) :
    vertexChainMap R E f (k + 1) (vertexChainReversalHomotopy R E k c) =
      vertexChainReversalHomotopy R F k (vertexChainMap R E f k c) := by
  classical
  induction k with
  | zero => simp [vertexChainReversalHomotopy]
  | succ k hk =>
    suffices h : (vertexChainMap R E f (k + 2)).comp
        (vertexChainReversalHomotopy R E (k + 1)) =
        (vertexChainReversalHomotopy R F (k + 1)).comp
          (vertexChainMap R E f (k + 1)) from congrArg (fun g ↦ g c) h
    apply Finsupp.lhom_ext
    intro v a
    simp only [LinearMap.comp_apply, vertexChainReversalHomotopy_single, map_smul,
      vertexChainMap_cone, map_sub, vertexChainMap_reversal, hk,
      vertexChainMap_boundary]
    simp [vertexChainMap, vertexChainReversalHomotopy_single]

end AtiyahSinger
