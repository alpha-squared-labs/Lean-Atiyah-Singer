/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineChern

/-!
# The localized first Chern class of a section

Public module ID: M1711.

A continuous section pulls the original normalized line Thom class back to
the pair consisting of the base and the nonzero locus of that section. Its
ordinary image is the original first Chern class, since scalar multiplication
homotopes the section to the zero section in the original bundle charts.
This is the relative Euler-class construction used for projective coordinate
sections; no transversality or nonvanishing hypothesis on the section is needed.

Source: Milnor--Stasheff, Characteristic Classes, Sections 9 and 14.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]
  (hline : ∀ x, Module.finrank ℂ (E x) = 1)

/-- A section localizes the original first Chern class on its actual zero set. -/
def complexLineSectionClass (s : ∀ x, E x)
    (hs : Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E))) :
    relativeSingularCohomology ℤ {x | s x ≠ 0} 2 :=
  relativeSingularCohomologyPullback ℤ
    (⟨fun x ↦ ⟨x, s x⟩, hs⟩ : C(X, TotalSpace Unit E))
    (A := {x | s x ≠ 0}) (B := {z : TotalSpace Unit E | z.snd ≠ 0})
    (fun _ hx ↦ hx) 2 (complexLineThomClass E hline)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Forgetting the zero-set support of a section recovers the same first Chern class. -/
theorem complexLineSectionClass_toOrdinary (s : ∀ x, E x)
    (hs : Continuous (fun x ↦ (⟨x, s x⟩ : TotalSpace Unit E))) :
    relativeSingularCohomologyToOrdinary ℤ {x | s x ≠ 0} 2
        (complexLineSectionClass E hline s hs) = firstChernClass E hline := by
  let A : Set (TotalSpace Unit E) := {z | z.snd ≠ 0}
  let z : C(X, TotalSpace Unit E) :=
    ⟨fun x ↦ ⟨x, 0⟩, ComplexBundle.continuous_zero_section E⟩
  let σ : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, s x⟩, hs⟩
  -- Scalar multiplication is continuous in the original finite linear bundle charts.
  have hcontinuous : Continuous (fun p : unitInterval × X ↦
      (⟨p.2, ((p.1 : ℝ) : ℂ) • s p.2⟩ : TotalSpace Unit E)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    obtain ⟨r, t, hp, ht⟩ :=
      ComplexBundle.IsFiniteRank.exists_linear_trivialization (E := E) p.2
    have hσ := (t.toOpenPartialHomeomorph.continuousAt (t.mem_source.mpr hp)).comp
      (hs.continuousAt.comp continuousAt_snd)
    have hscalar : Continuous (fun a : unitInterval × X ↦ ((a.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)
    apply t.continuousAt_of_comp_left
      (f := fun a : unitInterval × X ↦
        (⟨a.2, ((a.1 : ℝ) : ℂ) • s a.2⟩ : TotalSpace Unit E)) continuousAt_snd hp
    apply (continuousAt_snd.prodMk (hscalar.continuousAt.smul hσ.snd)).congr_of_eventuallyEq
    filter_upwards [continuousAt_snd.eventually (t.open_baseSet.mem_nhds hp)] with a ha
    exact Prod.ext (t.proj_toFun _ (t.mem_source.mpr ha))
      ((ht a.2 ha).map_smul ((a.1 : ℝ) : ℂ) (s a.2))
  let H : ContinuousMap.Homotopy z σ :=
    { toFun := fun p ↦ ⟨p.2, ((p.1 : ℝ) : ℂ) • s p.2⟩
      continuous_toFun := hcontinuous
      map_zero_left := by
        intro x
        change (⟨x, ((0 : unitInterval) : ℝ) • s x⟩ : TotalSpace Unit E) = ⟨x, 0⟩
        simp
      map_one_left := by
        intro x
        change (⟨x, ((1 : unitInterval) : ℝ) • s x⟩ : TotalSpace Unit E) = ⟨x, s x⟩
        simp }
  -- The relative square uses that very section, then its ordinary homotopy identifies c₁.
  have hnat := relativeSingularCohomologyPullback_toOrdinary ℤ σ
    (A := {x | s x ≠ 0}) (B := A) (fun _ hx ↦ hx) 2
  have hvalue := congrArg (fun f ↦ f (complexLineThomClass E hline)) hnat
  change relativeSingularCohomologyToOrdinary ℤ {x | s x ≠ 0} 2
      (complexLineSectionClass E hline s hs) =
    singularCohomologyPullback ℤ σ 2
      (relativeSingularCohomologyToOrdinary ℤ A 2 (complexLineThomClass E hline)) at hvalue
  rw [hvalue, ← singularCohomologyPullback_homotopic ℤ H]
  rfl

end AtiyahSinger
