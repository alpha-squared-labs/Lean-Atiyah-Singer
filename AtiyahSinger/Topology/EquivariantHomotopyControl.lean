/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantSupportTriple

/-!
# Controlled composition of equivariant boundary homotopies

Public module ID: M1790.

Enlargement and composition retain a specified compact control on the original
space. Composition uses exactly the union of the input controls, which allows
all deformations to be restricted through a common open image. This control
information is used in relative analytic excision.

These are the controlled forms of the standard fixed-bundle homotopy operations
in SG I.9.23--9.26 and Atiyah--Singer I, section 2.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped unitInterval

variable {G X : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  {E F : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {ρE : EquivariantStructure G E} {ρF : EquivariantStructure G F}

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Enlarge a fixed-action boundary homotopy to a specified invariant compact control. -/
theorem CompactSupportTriple.EquivariantHomotopy.exists_enlarge
    {a b : CompactSupportTriple E F}
    (H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b)
    (L : Set X) (hL : IsCompact L) (hHL : H.control ⊆ L)
    (hInv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L) :
    ∃ J : CompactSupportTriple.EquivariantHomotopy ρE ρF a b, J.control = L := by
  classical
  -- Restriction preserves the entire original cylinder, not only its endpoints.
  have hrestrict {S T : Set X} (hTS : T ⊆ S)
      {e₀ e₁ : RelativeTriple E F S} (H : IsoHomotopy e₀ e₁) :
      ∃ J : IsoHomotopy (e₀.restrictTo hTS) (e₁.restrictTo hTS),
        ∀ (t : I) (x : T) (v : E x), J.iso.linearEquiv (t, x) v =
          H.iso.linearEquiv (t, Set.inclusion hTS x) v := by
    obtain ⟨K, hK⟩ := H.exists_pullback ⟨Set.inclusion hTS, continuous_inclusion hTS⟩
    let U := restrictSubsetIso (E := E) S T hTS
    let V := restrictSubsetIso (E := F) S T hTS
    let L := (U.symm.pullback ⟨Prod.snd, continuous_snd⟩).trans
      (K.iso.trans (V.pullback ⟨Prod.snd, continuous_snd⟩))
    have hU (x : T) (v : E x) : (U.linearEquiv x).symm v = v := by
      exact (restrictSubsetIso_apply (E := E) S T hTS x _).symm.trans
        ((U.linearEquiv x).apply_symm_apply v)
    have hL (t : I) (x : T) (v : E x) :
        L.linearEquiv (t, x) v = H.iso.linearEquiv (t, Set.inclusion hTS x) v := by
      change V.linearEquiv x (K.iso.linearEquiv (t, x) ((U.linearEquiv x).symm v)) = _
      rw [hU]
      exact (restrictSubsetIso_apply (E := F) S T hTS x _).trans (hK t x v)
    refine ⟨{ iso := L, map_zero := ?_, map_one := ?_ }, hL⟩
    · intro x v
      exact (hL 0 x v).trans ((H.map_zero (Set.inclusion hTS x) v).trans
        (Iso.restrictTo_apply e₀ hTS x v).symm)
    · intro x v
      exact (hL 1 x v).trans ((H.map_one (Set.inclusion hTS x) v).trans
        (Iso.restrictTo_apply e₁ hTS x v).symm)
  obtain ⟨K, hK⟩ := hrestrict (Set.compl_subset_compl.mpr hHL) H.homotopy
  -- Retain this same restricted cylinder, with the endpoints computed in the original triples.
  let Q : IsoHomotopy
      (a.enlarge L hL (H.left_control.trans hHL)).boundary
      (b.enlarge L hL (H.right_control.trans hHL)).boundary :=
    { iso := K.iso
      map_zero := by
        intro x v
        exact (hK 0 x v).trans ((H.homotopy.map_zero
          (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
          ((a.enlarge_apply H.control H.isCompact_control H.left_control
              (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
            (a.enlarge_apply L hL (H.left_control.trans hHL) x v).symm))
      map_one := by
        intro x v
        exact (hK 1 x v).trans ((H.homotopy.map_one
          (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
          ((b.enlarge_apply H.control H.isCompact_control H.right_control
              (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v).trans
            (b.enlarge_apply L hL (H.right_control.trans hHL) x v).symm)) }
  refine ⟨{ control := L
            isCompact_control := hL
            invariant_control := hInv
            left_control := H.left_control.trans hHL
            right_control := H.right_control.trans hHL
            homotopy := Q
            intertwines := ?_ }, rfl⟩
  intro t g x v
  change K.iso.linearEquiv
    (t, ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩)
    (ρE.linearMap g x.val v) = ρF.linearMap g x.val (K.iso.linearEquiv (t, x) v)
  rw [hK, hK]
  exact H.intertwines t g (Set.inclusion (Set.compl_subset_compl.mpr hHL) x) v

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compose actual equivariant cylinders with exactly the union of their compact controls. -/
theorem CompactSupportTriple.EquivariantHomotopy.exists_trans_control
    {a b c : CompactSupportTriple E F} (hb : b.IsEquivariant ρE ρF)
    (H : CompactSupportTriple.EquivariantHomotopy ρE ρF a b)
    (J : CompactSupportTriple.EquivariantHomotopy ρE ρF b c) :
    ∃ Q : CompactSupportTriple.EquivariantHomotopy ρE ρF a c,
      Q.control = H.control ∪ J.control := by
  classical
  let S := H.control ∪ J.control
  have hS : IsCompact S := H.isCompact_control.union J.isCompact_control
  have hInv (g : G) (x : X) : g • x ∈ S ↔ x ∈ S :=
    or_congr (H.invariant_control g x) (J.invariant_control g x)
  obtain ⟨H', hH'⟩ := H.exists_enlarge S hS Set.subset_union_left hInv
  obtain ⟨J', hJ'⟩ := J.exists_enlarge S hS Set.subset_union_right hInv
  -- Work on precisely one control; equality transport changes only its proof certificates.
  rcases H' with ⟨K, hK, hKI, haK, hbK, H₀, hH₀⟩
  rcases J' with ⟨L, hL, hLI, hbL, hcL, J₀, hJ₀⟩
  dsimp only at hH' hJ'
  subst K
  subst L
  let mid := (b.enlarge S hS hbK).boundary
  have hmid := (hb.enlarge S hS hbK hInv).inverse
  let C := mid.symm.pullback (⟨Prod.snd, continuous_snd⟩ : C(I × (Sᶜ : Set X), (Sᶜ : Set X)))
  let Q := H₀.iso.trans (C.trans J₀.iso)
  -- The explicit path is J(t) composed with b inverse composed with H(t).
  -- Its original middle map cancels at both endpoints and intertwines at every time.
  refine ⟨{ control := S
            isCompact_control := hS
            invariant_control := hInv
            left_control := haK
            right_control := hcL
            homotopy := { iso := Q, map_zero := ?_, map_one := ?_ }
            intertwines := ?_ }, rfl⟩
  · intro x v
    change J₀.iso.linearEquiv (0, x)
      ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (0, x) v)) = _
    rw [J₀.map_zero, H₀.map_zero]
    exact (mid.linearEquiv x).apply_symm_apply _
  · intro x v
    change J₀.iso.linearEquiv (1, x)
      ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (1, x) v)) = _
    rw [H₀.map_one, LinearEquiv.symm_apply_apply]
    exact J₀.map_one x v
  · intro t g x v
    let gx : (Sᶜ : Set X) :=
      ⟨g • x.val, fun hx ↦ x.property ((hInv g x.val).mp hx)⟩
    change J₀.iso.linearEquiv (t, gx)
      ((mid.linearEquiv gx).symm (H₀.iso.linearEquiv (t, gx)
        (ρE.linearMap g x.val v))) =
      ρF.linearMap g x.val (J₀.iso.linearEquiv (t, x)
        ((mid.linearEquiv x).symm (H₀.iso.linearEquiv (t, x) v)))
    rw [hH₀ t g x v]
    have hi := hmid.boundary_intertwines g x (H₀.iso.linearEquiv (t, x) v)
    change (mid.linearEquiv gx).symm
      (ρF.linearMap g x.val (H₀.iso.linearEquiv (t, x) v)) =
      ρE.linearMap g x.val ((mid.linearEquiv x).symm
        (H₀.iso.linearEquiv (t, x) v)) at hi
    rw [hi]
    exact hJ₀ t g x _

end AtiyahSinger.ComplexBundle
