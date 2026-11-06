/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleIsoHomotopyPullback
public import AtiyahSinger.Topology.EquivariantOpenExtension

/-!
# Restriction of a controlled equivariant homotopy to an open image

Public module ID: M1796.

An open embedding pulls back an actual equivariant boundary cylinder when its
image contains the entire compact control. The resulting control is precisely
the inverse image of the old one. Both bundles, actions and every boundary map
are the original pullbacks. No properness of the open embedding is asserted.

This is the controlled homotopy form of open excision in the original support
triple model. In analytic excision it justifies retaining the class on the
common open source through relative deformations in a compact environment.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle Topology

variable {X Y G : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MulAction G X] [ContinuousSMul G X] [MulAction G Y] [ContinuousSMul G Y]
  {E F : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Compare the same nested pullback fibers throughout the original equivariant cylinder.
/-- Pull back a uniformly controlled homotopy through an open image containing its control. -/
theorem CompactSupportTriple.EquivariantHomotopy.exists_openRestrict
    {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}
    {a b : CompactSupportTriple E F}
    (H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b)
    (f : C(X, Y)) (hf : IsOpenEmbedding f)
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x)
    (hc : H.control ⊆ Set.range f) :
    ∃ J : CompactSupportTriple.EquivariantHomotopy (ρE.pullback f heq) (ρF.pullback f heq)
        (a.openRestrict f hf (H.left_control.trans hc))
        (b.openRestrict f hf (H.right_control.trans hc)),
      J.control = f ⁻¹' H.control := by
  classical
  let C : Set X := f ⁻¹' H.control
  have hC : IsCompact C :=
    hf.isEmbedding.isInducing.isCompact_preimage' H.isCompact_control hc
  have hInv (g : G) (x : X) : g • x ∈ C ↔ x ∈ C := by
    change f (g • x) ∈ H.control ↔ f x ∈ H.control
    rw [heq g x]
    exact H.invariant_control g (f x)
  let a' := a.openRestrict f hf (H.left_control.trans hc)
  let b' := b.openRestrict f hf (H.right_control.trans hc)
  have haC : a'.control ⊆ C := fun _ hx ↦ H.left_control hx
  have hbC : b'.control ⊆ C := fun _ hx ↦ H.right_control hx
  let iX : C((Cᶜ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iY : C((H.controlᶜ : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let fD : C((Cᶜ : Set X), (H.controlᶜ : Set Y)) :=
    ⟨fun x ↦ ⟨f x.val, x.property⟩,
      (f.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let cE : Iso ((iX : _ → X) *ᵖ ((f : X → Y) *ᵖ E))
      ((fD : _ → _) *ᵖ ((iY : _ → Y) *ᵖ E)) :=
    (pullbackCompIso (E := E) f iX).trans (pullbackCompIso (E := E) iY fD).symm
  let cF : Iso ((iX : _ → X) *ᵖ ((f : X → Y) *ᵖ F))
      ((fD : _ → _) *ᵖ ((iY : _ → Y) *ᵖ F)) :=
    (pullbackCompIso (E := F) f iX).trans (pullbackCompIso (E := F) iY fD).symm
  have hcE (x : (Cᶜ : Set X)) (v : E (f x.val)) : cE.linearEquiv x v = v := by
    change ((pullbackCompIso (E := E) iY fD).linearEquiv x).symm
      ((pullbackCompIso (E := E) f iX).linearEquiv x v) = v
    apply ((pullbackCompIso (E := E) iY fD).linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hcF (x : (Cᶜ : Set X)) (v : F (f x.val)) : cF.symm.linearEquiv x v = v := by
    change ((pullbackCompIso (E := F) f iX).linearEquiv x).symm
      ((pullbackCompIso (E := F) iY fD).linearEquiv x v) = v
    apply ((pullbackCompIso (E := F) f iX).linearEquiv x).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  -- Pull back the actual original cylinder, with value-preserving reassociation.
  obtain ⟨Q, hQ⟩ := H.homotopy.exists_pullback fD
  let πD : C(unitInterval × (Cᶜ : Set X), (Cᶜ : Set X)) :=
    ⟨Prod.snd, continuous_snd⟩
  let L := (cE.pullback πD).trans (Q.iso.trans (cF.symm.pullback πD))
  have hL (t : unitInterval) (x : (Cᶜ : Set X)) (v : E (f x.val)) :
      L.linearEquiv (t, x) v = H.homotopy.iso.linearEquiv (t, fD x) v := by
    change cF.symm.linearEquiv x (Q.iso.linearEquiv (t, x) (cE.linearEquiv x v)) = _
    rw [hcE, hcF]
    exact hQ t x v
  have hend (d : CompactSupportTriple E F) (hd : d.control ⊆ H.control)
      (x : (Cᶜ : Set X)) (v : E (f x.val)) :
      (d.enlarge H.control H.isCompact_control hd).boundary.linearEquiv (fD x) v =
        ((d.openRestrict f hf (hd.trans hc)).enlarge C hC
          (fun _ hx ↦ hd hx)).boundary.linearEquiv x v := by
    let x' : ((f ⁻¹' d.control)ᶜ : Set X) :=
      ⟨x.val, fun hz ↦ x.property (hd hz)⟩
    exact (d.enlarge_apply H.control H.isCompact_control hd (fD x) v).trans
      ((RelativeTriple.pullback_apply d.boundary f x' v).symm.trans
        ((d.openRestrict f hf (hd.trans hc)).enlarge_apply C hC
          (fun _ hx ↦ hd hx) x v).symm)
  refine ⟨{ control := C
            isCompact_control := hC
            invariant_control := hInv
            left_control := haC
            right_control := hbC
            homotopy := { iso := L, map_zero := ?_, map_one := ?_ }
            intertwines := ?_ }, rfl⟩
  · intro x v
    exact (hL 0 x v).trans ((H.homotopy.map_zero (fD x) v).trans
      (hend a H.left_control x v))
  · intro x v
    exact (hL 1 x v).trans ((H.homotopy.map_one (fD x) v).trans
      (hend b H.right_control x v))
  · intro t g x v
    -- Transport the same old square through the specified equivariance of f.
    have htransport (y z : Y) (hyz : y = z)
        (hy : y ∈ H.controlᶜ) (hz : z ∈ H.controlᶜ)
        (LE : E (f x.val) →ₗ[ℂ] E z) (LF : F (f x.val) →ₗ[ℂ] F z)
        (hsquare : ∀ w, H.homotopy.iso.linearEquiv (t, ⟨z, hz⟩) (LE w) =
          LF (H.homotopy.iso.linearEquiv (t, fD x) w)) :
        H.homotopy.iso.linearEquiv (t, ⟨y, hy⟩)
            ((Eq.mpr (congrArg (fun b ↦ E (f x.val) →ₗ[ℂ] E b) hyz) LE) v) =
          (Eq.mpr (congrArg (fun b ↦ F (f x.val) →ₗ[ℂ] F b) hyz) LF)
            (H.homotopy.iso.linearEquiv (t, fD x) v) := by
      subst z
      exact hsquare v
    let gx : (Cᶜ : Set X) :=
      ⟨g • x.val, fun hz ↦ x.property ((hInv g x.val).mp hz)⟩
    have hsquare := htransport (f (g • x.val)) (g • f x.val) (heq g x.val)
      gx.property (fun hz ↦ x.property ((H.invariant_control g (f x.val)).mp hz))
      (ρE.linearMap g (f x.val)) (ρF.linearMap g (f x.val))
      (H.intertwines t g (fD x))
    exact (hL t gx ((ρE.pullback f heq).linearMap g x.val v)).trans
      (hsquare.trans (congrArg ((ρF.pullback f heq).linearMap g x.val) (hL t x v)).symm)

end AtiyahSinger.ComplexBundle
