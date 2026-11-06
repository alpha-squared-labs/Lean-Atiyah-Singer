/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Path

/-!
# Circle and interval descriptions of based loops

Public module ID: M1612.

The Laurent-loop argument in Karoubi III.1.12–1.14 uses circle maps. The project's
stable matrix loop quotient uses paths whose two endpoints are the identity.
The positively oriented parametrization exp(2πit) identifies these two descriptions,
including based homotopies. These are standard quotient-space comparisons, not
additional analytic assumptions on a loop or its target.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- A based circle map traversed once in the positive direction. -/
def circleMapPath (f : C(Circle, X)) (x : X) (hbase : f 1 = x) : Path x x where
  toFun t := f (Circle.exp (2 * Real.pi * (t : ℝ)))
  continuous_toFun := f.continuous.comp (by fun_prop)
  source' := by simpa using hbase
  target' := by simpa using hbase

/-- Every based interval loop descends to a circle map with the same parametrized path. -/
theorem exists_circleMap_of_path (x : X) (p : Path x x) :
    ∃ f : C(Circle, X), ∃ hbase : f 1 = x, circleMapPath f x hbase = p := by
  /- Stage 1: the positive parametrization of the unit interval is a quotient map
  onto the circle. Its only nontrivial fiber identifies the two interval endpoints.
  Stage 2: the endpoint equations for p make it constant on those fibers. Descend
  p by the quotient universal property; the resulting map has precisely the
  specified values, and its value at the circle base point is x. -/
  -- Identify the circle with the interval quotient by its two endpoints.
  let e : Quot (AddCircle.EndpointIdent (1 : ℝ) 0) ≃ₜ Circle :=
    (AddCircle.homeoIccQuot (1 : ℝ) 0).symm.trans
      (AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0))
  let p' : Set.Icc (0 : ℝ) (0 + 1) → X := fun t ↦ p ⟨t, by simpa using t.property⟩
  have hp' : ∀ a b, AddCircle.EndpointIdent (1 : ℝ) 0 a b → p' a = p' b := by
    rintro a b ⟨⟩
    simp [p']
  -- The endpoint equation makes the original path descend through that quotient.
  let f : C(Circle, X) := ⟨(Quot.lift p' hp') ∘ e.symm,
    (continuous_quot_lift _ (p.continuous.comp (by fun_prop))).comp e.symm.continuous⟩
  -- Check the prescribed positive parameterization, not just an abstract circle map.
  have he (t : unitInterval) :
      e (Quot.mk _ ⟨t, by simp⟩) =
        Circle.exp (2 * Real.pi * (t : ℝ)) := by
    change AddCircle.homeomorphCircle _ ((t : ℝ) : AddCircle (1 : ℝ)) = _
    simp [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk]
  have hval (t : unitInterval) : f (Circle.exp (2 * Real.pi * (t : ℝ))) = p t := by
    rw [← he t]
    change Quot.lift p' hp' (e.symm (e _)) = _
    rw [e.symm_apply_apply]
  have hbase : f 1 = x := by simpa using (hval 0).trans p.source
  refine ⟨f, hbase, ?_⟩
  exact Path.ext (funext hval)

/-- Based circle homotopies correspond exactly to homotopies of based interval loops. -/
theorem circleMapPath_homotopic_iff (f g : C(Circle, X)) (x : X)
    (hf : f 1 = x) (hg : g 1 = x) :
    Path.Homotopic (circleMapPath f x hf) (circleMapPath g x hg) ↔
      Nonempty (ContinuousMap.HomotopyWith f g (fun h ↦ h 1 = x)) := by
  /- Precompose a circle homotopy with the same positive parametrization.
  Its fixed base point gives the endpoints required by Path.Homotopic.
  In the reverse direction, curry the path homotopy in its homotopy parameter
  to obtain a based interval loop in C(I,X). Apply the same circle descent
  to this loop, then uncurry. Surjectivity of the positive parametrization
  gives the exact endpoint circle maps, and the descended base value stays
  fixed. The compact interval supplies the continuous curry/uncurry operations;
  no separation assumption on X is required. -/
  -- Every point of the circle has a representative in the closed unit interval.
  have hsurj : Function.Surjective
      (fun t : unitInterval ↦ Circle.exp (2 * Real.pi * (t : ℝ))) := by
    intro z
    let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
    have hz : e.symm z ∈ (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Set.Icc 0 (0 + 1) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ _
    obtain ⟨t, ht, he⟩ := hz
    refine ⟨⟨t, by simpa using ht⟩, ?_⟩
    have := congrArg e he
    simpa [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] using this
  constructor
  · rintro ⟨H⟩
    -- Curry in the homotopy parameter so descent is continuous for the whole family.
    let swapped : C(unitInterval × unitInterval, X) :=
      ⟨fun z ↦ H (z.2, z.1), H.continuous.comp continuous_swap⟩
    let p : Path (ContinuousMap.const unitInterval x) (ContinuousMap.const unitInterval x) :=
      { toContinuousMap := swapped.curry
        source' := by ext t; exact H.source t
        target' := by ext t; exact H.target t }
    obtain ⟨F, hF, hpath⟩ := exists_circleMap_of_path (ContinuousMap.const unitInterval x) p
    have hval (s t : unitInterval) :
        F (Circle.exp (2 * Real.pi * (s : ℝ))) t = H (t, s) := by
      have he := congrArg (fun q : Path (ContinuousMap.const unitInterval x)
        (ContinuousMap.const unitInterval x) ↦ q s t) hpath
      exact he
    refine ⟨{
      toFun := fun z ↦ F z.2 z.1
      continuous_toFun := F.uncurry.continuous.comp continuous_swap
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }⟩
    · intro z
      obtain ⟨s, rfl⟩ := hsurj z
      exact (hval s 0).trans (H.apply_zero s)
    · intro z
      obtain ⟨s, rfl⟩ := hsurj z
      exact (hval s 1).trans (H.apply_one s)
    · intro t
      exact congrArg (fun k : C(unitInterval, X) ↦ k t) hF
  · rintro ⟨H⟩
    -- Precomposition preserves the base point at both interval endpoints.
    refine ⟨{
      toFun := fun z ↦ H (z.1, Circle.exp (2 * Real.pi * (z.2 : ℝ)))
      continuous_toFun := H.continuous.comp (by fun_prop)
      map_zero_left := fun t ↦ H.apply_zero _
      map_one_left := fun t ↦ H.apply_one _
      prop' := ?_ }⟩
    intro t s hs
    rcases hs with hs | hs
    · subst s
      simpa [circleMapPath, hf] using H.prop t
    · have hs' : s = 1 := Set.mem_singleton_iff.mp hs
      subst s
      simpa [circleMapPath, hf] using H.prop t

end AtiyahSinger
