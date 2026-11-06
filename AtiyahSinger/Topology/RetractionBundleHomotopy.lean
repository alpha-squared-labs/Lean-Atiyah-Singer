/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType

/-!
# Bundle homotopy transport normalized on a retraction

Public module ID: M2104.

A homotopy from the composite with a retraction to the original map identifies
their actual complex pullback bundles. Normalize any such identification by
its restriction to the retraction image, pulled back along that same retraction.
The resulting isomorphism is the vector identity at every fixed point.

This applies to radial contraction of a tubular normal bundle. It requires no
stationary open neighborhood, no finite CW condition, and no properness of the
contraction. Only bundles are pulled back; this result gives no pullback of
compact-support K classes along the generally nonproper retraction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [ParacompactSpace X]
  (E : Y → Type*) [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

attribute [local instance] isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Normalize actual homotopy bundle transport to the identity on the retraction image. -/
theorem exists_pullback_iso_of_homotopic_retraction (g : C(X, Y)) (r : C(X, X))
    (hr : ∀ x, r (r x) = r x) (H : (g.comp r).Homotopic g) :
    ∃ e : Iso (((g.comp r : C(X, Y)) : X → Y) *ᵖ E) ((g : X → Y) *ᵖ E),
      ∀ (x : X), r x = x → ∀ v : E ((g.comp r) x), HEq (e.linearEquiv x v) v := by
  classical
  let k := g.comp r
  -- Obtain one isomorphism between the original pullbacks, through the existing small model.
  let P := smallBundle E
  let j := smallBundleIso E
  obtain ⟨bP⟩ := nonempty_pullback_iso_of_homotopic P k g H
  let b : Iso ((k : X → Y) *ᵖ E) ((g : X → Y) *ᵖ E) :=
    (j.pullback k).trans (bP.trans (j.pullback g).symm)
  have hk (x : X) : k (r x) = k x := congrArg g (hr x)
  let transport (y z : Y) (h : y = z) : E y ≃ₗ[ℂ] E z := by
    subst z
    exact LinearEquiv.refl ℂ (E y)
  have htransport (y z : Y) (h : y = z) (v : E y) :
      HEq (transport y z h v) v := by
    subst z
    rfl
  have htransportTotal (y z : Y) (h : y = z) (v : E y) :
      (⟨z, transport y z h v⟩ : TotalSpace Unit E) = ⟨y, v⟩ := by
    subst z
    rfl
  let t (x : X) : E (k x) ≃ₗ[ℂ] E (k (r x)) := transport _ _ (hk x).symm
  let A (x : X) : E (k x) ≃ₗ[ℂ] E (k x) :=
    (t x).trans (b.linearEquiv (r x))
  -- Pull back the restriction of b to the retraction image, retaining each original vector.
  let R : TotalSpace Unit ((k : X → Y) *ᵖ E) →
      TotalSpace Unit ((k : X → Y) *ᵖ E) := fun z ↦ ⟨r z.proj, t z.proj z.snd⟩
  have hR : Continuous R := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit E k).continuous_iff]
    refine (r.continuous.comp (Pullback.continuous_proj Unit E k)).prodMk ?_
    apply (Pullback.continuous_lift Unit E k).congr
    intro z
    exact (htransportTotal _ _ (hk z.proj).symm z.snd).symm
  let a : Hom ((k : X → Y) *ᵖ E) ((k : X → Y) *ᵖ E) := {
    linearMap x := (A x).toLinearMap
    continuous_total := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit E k).continuous_iff]
      exact (Pullback.continuous_proj Unit E k).prodMk
        ((Pullback.continuous_lift Unit E g).comp (b.continuous_total.comp hR)) }
  let aIso := a.toIso (fun x ↦ (A x).bijective)
  refine ⟨aIso.symm.trans b, ?_⟩
  intro x hx v
  -- At a fixed point, the pulled-back automorphism is exactly b at that same point.
  have hfixed (w : E (k x)) :
      (⟨k x, aIso.linearEquiv x w⟩ : TotalSpace Unit E) =
        ⟨g x, b.linearEquiv x w⟩ := by
    have hz : R (⟨x, w⟩ : TotalSpace Unit ((k : X → Y) *ᵖ E)) = ⟨x, w⟩ :=
      TotalSpace.ext hx (htransport _ _ (hk x).symm w)
    have hb := congrArg b.totalHomeomorph hz
    exact congrArg (Pullback.lift (g : X → Y)) hb
  have hcancel := hfixed ((aIso.linearEquiv x).symm v)
  rw [LinearEquiv.apply_symm_apply] at hcancel
  exact HEq.symm (congr_arg_heq (fun z : TotalSpace Unit E ↦ z.snd) hcancel)

end AtiyahSinger.ComplexBundle
