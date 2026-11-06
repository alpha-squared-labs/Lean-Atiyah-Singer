/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DeRhamComplex
public import AtiyahSinger.Geometry.EuclideanPoincareLemma

/-!
# Positive-degree de Rham cohomology of Euclidean space

Public module ID: M1215.

The radial Poincaré primitive is interpreted as an original smooth differential
form. The coordinate formula identifies its exterior derivative with the
project's selected operator, so the original quotient of closed forms by exact
forms vanishes in every positive degree. No comparison cohomology is used.

Source: the standard Poincaré lemma, in the actual de Rham quotient convention.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff Manifold

variable {n : ℕ}

set_option backward.isDefEq.respectTransparency false in
/-- The original de Rham quotient of Euclidean space vanishes in every positive degree. -/
theorem subsingleton_deRhamCohomology_euclidean (p : ℕ) (hp : p ≠ 0) :
    Subsingleton (DeRhamCohomology (n := n) (EuclideanSpace ℝ (Fin n)) p) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
  let V := EuclideanSpace ℝ (Fin n)
  let c : OpenPartialHomeomorph V V := OpenPartialHomeomorph.refl V
  have hc : c ∈ atlas V V := by simp [c]
  -- The self-chart preserves every actual tensor and the selected exterior derivative.
  have hchart (q : ℕ) (form : ∀ x : V, DifferentialFormFiber (n := n) q x) :
      differentialFormInChart (n := n) form c = form := by
    funext x
    change (form x).compContinuousLinearMap (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, V) (id : V → V) x) = _
    rw [mfderiv_id]
    ext v
    rfl
  have hd (q : ℕ) (form : SmoothDifferentialForm (n := n) V q) (x : V) :
      (smoothFormExteriorDerivative (n := n) q form).val x = extDeriv form.val x := by
    have h := smoothFormExteriorDerivative_inChart form c hc x (mem_univ x)
    simpa only [hchart] using h
  -- Every original closed form has the radial primitive as an original smooth form.
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply top_unique
  intro form _
  change ∃ primitive : SmoothDifferentialForm (n := n) V p,
    smoothFormExteriorDerivative (n := n) p primitive = form.val
  let α : V → V [⋀^Fin (p + 1)]→L[ℝ] ℂ := form.val.val
  have hsmooth : ContDiff ℝ ∞ α := by
    have h := form.val.property c hc
    rw [hchart] at h
    exact contDiffOn_univ.mp h
  have hclosed (x : V) : extDeriv α x = 0 := by
    rw [← hd]
    have h : smoothFormExteriorDerivative (n := n) (p + 1) form.val = 0 := form.property
    exact congrArg (fun a : SmoothDifferentialForm (n := n) V (p + 1 + 1) ↦ a.val x) h
  obtain ⟨η, hη, hprimitive⟩ := exists_smooth_euclideanFormPrimitive p α
    hsmooth hclosed
  have hηform : IsSmoothDifferentialForm (n := n) η := by
    intro a ha
    have ha' : a = c := chartedSpaceSelf_atlas.mp ha
    rw [ha', hchart]
    exact hη.contDiffOn
  refine ⟨⟨η, hηform⟩, ?_⟩
  apply Subtype.ext
  funext x
  exact (hd p ⟨η, hηform⟩ x).trans (hprimitive x)

end AtiyahSinger
