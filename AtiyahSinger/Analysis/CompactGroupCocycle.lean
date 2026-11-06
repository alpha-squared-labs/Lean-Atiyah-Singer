/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Group.Seminorm
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Uniform seminorm bounds for compact-group cocycles

Public module ID: M0350.

A cocycle on a compact Hausdorff group is bounded in every invariant seminorm
whose integer sublevel sets are closed. No topology on the target additive group
is required. In particular, the proof does not infer closedness of a stronger
regularity subspace in a weaker topology.

This is a project supplement for fixed-principal-class averaging. That application
supplies an invariant saturation of a lower-order symbol seminorm together with
its closed sublevel sets. The proof uses Baire category, the cocycle identity,
and a finite translate cover.
-/

@[expose] public section

namespace AtiyahSinger

open Set Topology

/-- Closed seminorm sublevels and compactness give a uniform bound for a cocycle. -/
theorem bddAbove_range_seminorm_cocycle
    {G W : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [AddCommGroup W] [SMul G W]
    (p : AddGroupSeminorm W) (d : G → W)
    (hinvariant : ∀ (g : G) (v : W), p (g • v) = p v)
    (hcocycle : ∀ g h : G, d (g * h) = g • d h + d g)
    (hclosed : ∀ n : ℕ, IsClosed {g : G | p (d g) ≤ (n : ℝ)}) :
    BddAbove (Set.range (fun g : G ↦ p (d g))) := by
  classical
  -- Baire category supplies one open region with a uniform seminorm bound.
  let S (n : ℕ) : Set G := {g | p (d g) ≤ (n : ℝ)}
  have hcover : ⋃ n : ℕ, S n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨n, hn⟩ := exists_nat_ge (p (d g))
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcover
  let U : Set G := (fun g : G ↦ a * g) ⁻¹' interior (S n)
  have hU : IsOpen U := isOpen_interior.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ U := by simpa [U] using ha
  have haBound : p (d a) ≤ (n : ℝ) := interior_subset (s := S n) ha
  -- Subtract the value at a and use invariance to move the bound to the identity.
  have hlocal (g : G) (hg : g ∈ U) : p (d g) ≤ (n : ℝ) + n := by
    have hag : p (d (a * g)) ≤ (n : ℝ) := interior_subset (s := S n) hg
    calc
      p (d g) = p (a • d g) := (hinvariant a (d g)).symm
      _ = p (d (a * g) - d a) := by rw [hcocycle, add_sub_cancel_right]
      _ ≤ p (d (a * g)) + p (d a) := map_sub_le_add p _ _
      _ ≤ (n : ℝ) + n := add_le_add hag haBound
  -- The same neighborhood has finitely many translates covering the compact group.
  let V (a : G) : Set G := (fun g : G ↦ a⁻¹ * g) ⁻¹' U
  have hV (a : G) : IsOpen (V a) :=
    hU.preimage (continuous_const.mul continuous_id)
  have hVcover : Set.univ ⊆ ⋃ a : G, V a := by
    intro g _
    exact Set.mem_iUnion.mpr ⟨g, by simpa [V] using h1⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover V hV hVcover
  refine ⟨(n : ℝ) + n + ∑ a ∈ s, p (d a), ?_⟩
  rintro b ⟨g, rfl⟩
  obtain ⟨a, has, hag⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ g))
  have haSum : p (d a) ≤ ∑ b ∈ s, p (d b) :=
    Finset.single_le_sum (fun b _ ↦ apply_nonneg p (d b)) has
  calc
    p (d g) = p (a • d (a⁻¹ * g) + d a) := by rw [← hcocycle, mul_inv_cancel_left]
    _ ≤ p (a • d (a⁻¹ * g)) + p (d a) := map_add_le_add p _ _
    _ = p (d (a⁻¹ * g)) + p (d a) := by rw [hinvariant]
    _ ≤ (n : ℝ) + n + ∑ b ∈ s, p (d b) := add_le_add (hlocal _ hag) haSum

end AtiyahSinger
