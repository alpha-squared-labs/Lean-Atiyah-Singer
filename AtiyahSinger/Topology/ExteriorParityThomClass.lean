/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleThom
public import AtiyahSinger.Topology.SupportSkewInverse

/-!
# Both parity conventions for the original exterior Thom class

Public module ID: M1845.

The even-to-odd symbol is the original Thom triple. The odd-to-even symbol
has its negative class because its composite with the original symbol is
negative squared length. The proof keeps the actual zero section and metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

attribute [local instance] sumTopology exteriorTopology exteriorParityTopology
  isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))

set_option maxHeartbeats 600000 in
-- Both parity fibers retain the same native exterior and pullback topology.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- A specified exterior parity symbol has the original Thom class with its parity sign. -/
theorem compactSupportClass_exteriorParity (i : ZMod 2) :
    let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    let P (j : ZMod 2) : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) j
    let K : Set (TotalSpace Unit E) := {z | z.snd = 0}
    ∀ (a : CompactSupportTriple (p *ᵖ (P i)) (p *ᵖ (P (i + 1))))
      (_hcontrol : a.control = K)
      (_hboundary : ∀ (x : (a.controlᶜ : Set (TotalSpace Unit E))) v,
        a.boundary.linearEquiv x v = cliffordSymbolParity x.val.snd i v),
      a.compactSupportClass = (if i = 0 then (1 : ℤ) else -1) • exteriorThomClass E hinner := by
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let P (j : ZMod 2) : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) j
  let K : Set (TotalSpace Unit E) := {z | z.snd = 0}
  let (j : ZMod 2) : IsFiniteRank ((π Unit E) *ᵖ (P j)) := isFiniteRank_pullback p
  dsimp only
  fin_cases i
  · intro a hcontrol hboundary
    change a.compactSupportClass =
      (if (0 : ZMod 2) = 0 then (1 : ℤ) else -1) • exteriorThomClass E hinner
    rw [ite_eq_left rfl, one_zsmul]
    have heq : a = exteriorThomTriple E hinner := by
      cases a with
      | mk L hL boundary =>
        change L = K at hcontrol
        subst L
        have hbound : boundary = exteriorThomBoundary E hinner := by
          apply Iso.ext
          intro x
          apply LinearEquiv.ext
          intro v
          exact hboundary x v
        cases hbound
        rfl
    rw [heq]
    rfl
  · intro a hcontrol hboundary
    change a.compactSupportClass =
      (if (1 : ZMod 2) = 0 then (1 : ℤ) else -1) • exteriorThomClass E hinner
    rw [ite_eq_right (by decide : (1 : ZMod 2) ≠ 0), neg_one_zsmul]
    let t := exteriorThomTriple E hinner
    have hK : IsCompact K := t.isCompact_control
    have haK : a.control ⊆ K := hcontrol.le
    have hnorm : Continuous (fun z : TotalSpace Unit E ↦ ‖z.snd‖ ^ 2) := by
      have hdiag : Continuous (fun z : TotalSpace Unit E ↦
          (⟨z.proj, z.snd, z.snd⟩ : TotalSpace Unit (E ×ᵇ E))) :=
        continuous_induced_rng.mpr (continuous_id.prodMk continuous_id)
      have h := Complex.continuous_re.comp (hinner.comp hdiag)
      change Continuous (fun z : TotalSpace Unit E ↦ RCLike.re (inner ℂ z.snd z.snd)) at h
      simpa only [inner_self_eq_norm_sq] using h
    let r : C((Kᶜ : Set (TotalSpace Unit E)), ℝ) :=
      ⟨fun x ↦ ‖x.val.snd‖ ^ 2, hnorm.comp continuous_subtype_val⟩
    have hr (x : (Kᶜ : Set (TotalSpace Unit E))) : 0 < r x :=
      sq_pos_of_pos (norm_pos_iff.mpr x.property)
    have hcomp (x : (Kᶜ : Set (TotalSpace Unit E)))
        (v : (p *ᵖ (P 0)) x.val) :
        (a.enlarge K hK haK).boundary.linearEquiv x
          ((t.enlarge K hK (Set.Subset.refl _)).boundary.linearEquiv x v) =
        -(r x : ℂ) • v := by
      rw [CompactSupportTriple.enlarge_apply, CompactSupportTriple.enlarge_apply, hboundary]
      apply Subtype.ext
      change cliffordSymbol x.val.snd (cliffordSymbol x.val.snd v.val) =
        -((‖x.val.snd‖ ^ 2 : ℝ) : ℂ) • v.val
      rw [Complex.ofReal_pow]
      exact LinearMap.congr_fun (cliffordSymbol_sq x.val.snd) v.val
    exact t.compactSupportClass_eq_neg_of_comp_neg_scalar a K hK
      (Set.Subset.refl _) haK r hr hcomp

end AtiyahSinger.ComplexBundle
