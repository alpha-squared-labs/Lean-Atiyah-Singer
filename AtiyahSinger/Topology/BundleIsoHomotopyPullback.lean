/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopy

/-!
# Pullback of the original bundle-isomorphism homotopy

Public module ID: M1581.

The standard pullback operation preserves the entire given homotopy, including
its specified endpoints and its action on every fiber vector. The iterated
pullback topologies are kept throughout. This supplies the common base-change
step for restriction and proper pullback of uniformly controlled homotopies.
It is a functoriality supplement to the relative-triple homotopies of Karoubi II.2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {E F : X → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]

/-- Pullback preserves the specified endpoints and every intermediate fiber map. -/
theorem IsoHomotopy.exists_pullback {e₀ e₁ : Iso E F}
    (H : IsoHomotopy e₀ e₁) (f : C(Y, X)) :
    ∃ K : IsoHomotopy (e₀.pullback f) (e₁.pullback f),
      ∀ (t : I) (y : Y) (v : E (f y)),
        K.iso.linearEquiv (t, y) v = H.iso.linearEquiv (t, f y) v := by
  let p : I × X → X := Prod.snd
  let q : I × Y → Y := Prod.snd
  -- Send the new cylinder into the original cylinder, keeping its fiber vector.
  have hE : Continuous (fun z : TotalSpace Unit (q *ᵖ ((f : Y → X) *ᵖ E)) ↦
      (⟨(z.proj.1, f z.proj.2), z.snd⟩ : TotalSpace Unit (p *ᵖ E))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E p).continuous_iff]
    exact ((Pullback.continuous_proj Unit ((f : Y → X) *ᵖ E) q).fst.prodMk
      (f.continuous.comp (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ E) q).snd)).prodMk
      ((Pullback.continuous_lift Unit E f).comp
        (Pullback.continuous_lift Unit ((f : Y → X) *ᵖ E) q))
  have hF : Continuous (fun z : TotalSpace Unit (q *ᵖ ((f : Y → X) *ᵖ F)) ↦
      (⟨(z.proj.1, f z.proj.2), z.snd⟩ : TotalSpace Unit (p *ᵖ F))) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
    exact ((Pullback.continuous_proj Unit ((f : Y → X) *ᵖ F) q).fst.prodMk
      (f.continuous.comp (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ F) q).snd)).prodMk
      ((Pullback.continuous_lift Unit F f).comp
        (Pullback.continuous_lift Unit ((f : Y → X) *ᵖ F) q))
  -- Joint continuity of both original directions gives both pulled-back directions.
  let e : Iso (q *ᵖ ((f : Y → X) *ᵖ E)) (q *ᵖ ((f : Y → X) *ᵖ F)) :=
    { linearEquiv := fun z ↦ H.iso.linearEquiv (z.1, f z.2)
      continuous_total := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit ((f : Y → X) *ᵖ F) q).continuous_iff]
        apply (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ E) q).prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit F f).continuous_iff]
        exact (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ E) q).snd.prodMk
          ((Pullback.continuous_lift Unit F p).comp (H.iso.continuous_total.comp hE))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit ((f : Y → X) *ᵖ E) q).continuous_iff]
        apply (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ F) q).prodMk
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E f).continuous_iff]
        exact (Pullback.continuous_proj Unit ((f : Y → X) *ᵖ F) q).snd.prodMk
          ((Pullback.continuous_lift Unit E p).comp (H.iso.continuous_symm.comp hF)) }
  -- The construction evaluates the original path; its endpoint equations pull back verbatim.
  exact ⟨{ iso := e
           map_zero := fun y v ↦ H.map_zero (f y) v
           map_one := fun y v ↦ H.map_one (f y) v }, fun _ _ _ ↦ rfl⟩

end AtiyahSinger.ComplexBundle
