/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantCoordinateFamilies

import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A fixed original cutoff for a moving coordinate family

Public module ID: M0494.

Near a given group element, a compact original coordinate support admits one
fixed smooth near-diagonal cutoff whose transformed support lies in a common
valid frequency-change region. The cutoff is chosen before varying the group
parameter, so the corresponding original off-diagonal remainder stays fixed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hG hAction

set_option maxSynthPendingDepth 20 in
/-- One original near-diagonal cutoff works throughout a neighborhood of a group element. -/
theorem exists_inverse_smul_chart_cutoff
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (g₀ : G)
    (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) :
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e (g : G) := d.symm.trans
      ((Diffeomorph.smul (M := M) IG I ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
    K ⊆ (e g₀).source →
    ∃ (U : Set G)
        (W : Set (G × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))),
      IsOpen U ∧ g₀ ∈ U ∧ IsOpen W ∧
      (∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target ∧
        (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible) ∧
      ∃ γ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ γ ∧ HasCompactSupport γ ∧
        (fun x ↦ (x, x)) '' K ⊆ interior {z | γ z = 1} ∧
        ∀ g ∈ U, ∀ z ∈ tsupport γ,
          z.1 ∈ (e g).source ∧ z.2 ∈ (e g).source ∧ (g, (e g z.1, e g z.2)) ∈ W := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let e (g : G) := d.symm.trans
    ((Diffeomorph.smul (M := M) IG I ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
  change K ⊆ (e g₀).source → _
  intro hKsource
  obtain ⟨W, hW, hdiag, hvalid⟩ :=
    exists_inverse_smul_chart_coordinate_neighborhood (G := G) IG c d hc hd
  let D₀ : Set (G × (X × X)) := {p | p.2.1 ∈ d.target ∧ p.2.2 ∈ d.target}
  have hD₀ : IsOpen D₀ := (d.open_target.preimage continuous_snd.fst).inter
    (d.open_target.preimage continuous_snd.snd)
  let moved₁ (p : G × (X × X)) : M := p.1 • d.symm p.2.1
  let moved₂ (p : G × (X × X)) : M := p.1 • d.symm p.2.2
  have hmoved₁ : ContinuousOn moved₁ D₀ := continuous_fst.continuousOn.smul
    (d.continuousOn_symm.comp continuous_snd.fst.continuousOn (fun _ hp ↦ hp.1))
  have hmoved₂ : ContinuousOn moved₂ D₀ := continuous_fst.continuousOn.smul
    (d.continuousOn_symm.comp continuous_snd.snd.continuousOn (fun _ hp ↦ hp.2))
  let D := (D₀ ∩ moved₁ ⁻¹' c.source) ∩ moved₂ ⁻¹' c.source
  have hD : IsOpen D := (hmoved₂.mono inter_subset_left).isOpen_inter_preimage
    (hmoved₁.isOpen_inter_preimage hD₀ c.open_source) c.open_source
  let T (p : G × (X × X)) : G × (X × X) := (p.1, (e p.1 p.2.1, e p.1 p.2.2))
  have hT : ContinuousOn T D := by
    have h₁ : ContinuousOn (fun p : G × (X × X) ↦ c (moved₁ p)) D :=
      c.continuousOn.comp (hmoved₁.mono (fun _ hp ↦ hp.1.1)) (fun _ hp ↦ hp.1.2)
    have h₂ : ContinuousOn (fun p : G × (X × X) ↦ c (moved₂ p)) D :=
      c.continuousOn.comp (hmoved₂.mono (fun _ hp ↦ hp.1.1)) (fun _ hp ↦ hp.2)
    exact continuous_fst.continuousOn.prodMk (h₁.prodMk h₂)
  let N := D ∩ T ⁻¹' W
  have hN : IsOpen N := hT.isOpen_inter_preimage hD hW
  let ΔK : Set (X × X) := (fun x ↦ (x, x)) '' K
  have hΔK : IsCompact ΔK := hK.image (continuous_id.prodMk continuous_id)
  have hKN : ({g₀} : Set G) ×ˢ ΔK ⊆ N := by
    rintro ⟨g, z⟩ ⟨hg, hz⟩
    have hg' : g = g₀ := mem_singleton_iff.mp hg
    subst g
    obtain ⟨x, hx, rfl⟩ := hz
    have hxsource : x ∈ (e g₀).source := hKsource hx
    refine ⟨⟨⟨⟨hxsource.1, hxsource.1⟩, hxsource.2.2⟩, hxsource.2.2⟩, ?_⟩
    exact hdiag g₀ (e g₀ x) ((e g₀).map_source hxsource)
  -- The tube lemma gives one spatial neighborhood valid for every parameter in U.
  obtain ⟨U, O, hU, hO, hgU, hKO, hUO⟩ :=
    generalized_tube_lemma isCompact_singleton hΔK hN hKN
  obtain ⟨O₁, hO₁, hKO₁, hO₁O, hO₁c⟩ :=
    exists_open_between_and_isCompact_closure hΔK hO hKO
  obtain ⟨O₂, hO₂, hO₁O₂, hO₂O, hO₂c⟩ :=
    exists_open_between_and_isCompact_closure hO₁c hO hO₁O
  obtain ⟨γ, hγ, _, hsγ, honeγ⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hO₂ hO₁c.isClosed hO₁O₂
  have hsupport : tsupport γ = closure O₂ := congrArg closure hsγ
  have hcγ : HasCompactSupport γ := by
    change IsCompact (tsupport γ)
    rwa [hsupport]
  have hγO : tsupport γ ⊆ O := by rwa [hsupport]
  have hplateau : ΔK ⊆ interior {z | γ z = 1} := by
    apply hKO₁.trans
    apply interior_maximal ?_ hO₁
    intro z hz
    exact (honeγ z).mp (subset_closure hz)
  refine ⟨U, W, hU, hgU (mem_singleton g₀), hW, hvalid, γ, hγ, hcγ, hplateau, ?_⟩
  intro g hg z hz
  have hmem : (g, z) ∈ N := hUO ⟨hg, hγO hz⟩
  exact ⟨⟨hmem.1.1.1.1, mem_univ _, hmem.1.1.2⟩,
    ⟨hmem.1.1.1.2, mem_univ _, hmem.1.2⟩, hmem.2⟩

end AtiyahSinger
