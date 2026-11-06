/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RetractionBundleHomotopy

/-!
# Trivializing a complex bundle along the time direction

Public module ID: M1697.

The original bundle on a real cylinder is isomorphic to the pullback of its
zero-time slice. The resulting total-space homeomorphism retains both time and
base point and is the identity on the original zero-time fibers. It uses bundle
homotopy invariance and the actual induced pullback topologies; no connection,
smooth transport, or properness of the contraction is required.

This is the bundle transport needed to compare the actual Thom operators at
the endpoints of a moving embedding. The underlying homotopy invariance is
Hatcher, Vector Bundles and K-Theory, Proposition 1.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology
open scoped unitInterval

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  [ParacompactSpace (ℝ × X)]
  (B : ℝ × X → Type*) [∀ p, AddCommGroup (B p)] [∀ p, Module ℂ (B p)]
  [TopologicalSpace (TotalSpace Unit B)] [IsFiniteRank B]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A cylinder bundle has fiberwise complex transport with the exact time-preserving total map. -/
theorem exists_cylinderTransport :
    ∃ (e : ∀ (t : ℝ) (x : X), B (0, x) ≃ₗ[ℂ] B (t, x))
      (q : (ℝ × TotalSpace Unit ((fun x : X ↦ (0, x)) *ᵖ B)) ≃ₜ TotalSpace Unit B),
      (∀ (t : ℝ) (x : X) (v : B (0, x)), q (t, ⟨x, v⟩) = ⟨(t, x), e t x v⟩) ∧
        ∀ (x : X) (v : B (0, x)), e 0 x v = v := by
  classical
  let s : C(X, ℝ × X) := ⟨fun x ↦ (0, x), continuous_const.prodMk continuous_id⟩
  let r : C(ℝ × X, ℝ × X) := ⟨fun p ↦ (0, p.2), continuous_const.prodMk continuous_snd⟩
  let H : ContinuousMap.Homotopy r (ContinuousMap.id (ℝ × X)) := {
    toFun p := ((p.1 : ℝ) * p.2.1, p.2.2)
    continuous_toFun :=
      ((continuous_subtype_val.comp continuous_fst).mul continuous_snd.fst).prodMk
        continuous_snd.snd
    map_zero_left := by intro p; simp [r]
    map_one_left := by intro p; simp }
  -- Normalize the actual bundle homotopy isomorphism along the zero-time retraction.
  obtain ⟨a, ha⟩ := exists_pullback_iso_of_homotopic_retraction B
    (ContinuousMap.id (ℝ × X)) r (fun _ ↦ rfl) ⟨H⟩
  let A := a.trans (pullbackIdIso (E := B))
  let e (t : ℝ) (x : X) : B (0, x) ≃ₗ[ℂ] B (t, x) := A.linearEquiv (t, x)
  let D := TotalSpace Unit ((s : X → ℝ × X) *ᵖ B)
  let R := TotalSpace Unit ((r : ℝ × X → ℝ × X) *ᵖ B)
  -- The induced pullback topology identifies the retraction pullback with this same product.
  let c : (ℝ × D) ≃ₜ R := {
    toFun p := ⟨(p.1, p.2.proj), p.2.snd⟩
    invFun z := (z.proj.1, ⟨z.proj.2, z.snd⟩)
    left_inv _ := rfl
    right_inv _ := rfl
    continuous_toFun := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit B r).continuous_iff]
      exact (continuous_fst.prodMk
        ((Pullback.continuous_proj Unit B s).comp continuous_snd)).prodMk
          ((Pullback.continuous_lift Unit B s).comp continuous_snd)
    continuous_invFun := by
      refine (Pullback.continuous_proj Unit B r).fst.prodMk ?_
      rw [(inducing_pullbackTotalSpaceEmbedding Unit B s).continuous_iff]
      exact (Pullback.continuous_proj Unit B r).snd.prodMk
        (Pullback.continuous_lift Unit B r) }
  refine ⟨e, c.trans A.totalHomeomorph, fun _ _ _ ↦ rfl, ?_⟩
  intro x v
  -- The original vector is retained at zero time, not just its isomorphism class.
  change (pullbackIdIso (E := B)).linearEquiv (0, x) (a.linearEquiv (0, x) v) = v
  rw [pullbackIdIso_apply]
  exact eq_of_heq (ha (0, x) rfl v)

end AtiyahSinger.ComplexBundle
