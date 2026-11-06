/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexCohomologyEulerSum
public import AtiyahSinger.Topology.ComplexLineEulerComparison
public import AtiyahSinger.Topology.EvenCohomologyRing
public import AtiyahSinger.Topology.FiniteSumBundle
public import AtiyahSinger.Topology.ZeroRankEuler

/-!
# The Euler class of the specified finite sum of complex lines

Public module ID: M1828.

The canonical complex Euler class is the original rational Euler class in the
metric's native real model. Its zero-rank normalization uses the positive empty
basis. The binary normalized cup formula then gives the product of the actual
line roots, with the original line norms retained through identity bundle maps.
The splitting is an actual isomorphism to the same finite sum used by the flag
and projective constructions.

Source: Milnor--Stasheff, sections 9 and 14, Euler multiplication and the complex
line normalization. No cancellation hypothesis on the base is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

universe u

variable {X : Type u} [TopologicalSpace X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The original rational Euler class in the canonical complex native real model. -/
def complexCohomologyEulerClass (h : ContinuousHermitianMetric E) (r : ℕ)
    (hr : ∀ x, Module.finrank ℂ (E x) = r) : singularCohomology ℚ X (2 * r) := by
  letI : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  letI : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  letI := nativeModelTopology E (EuclideanSpace ℝ (Fin (2 * r)))
  letI := h.realNativeFiberBundle r hr
  letI := h.realNativeVectorBundle r hr
  exact cohomologyEulerClass ℚ (2 * r) E (h.complexCohomologyOrientation r hr).rationalization

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical complex Euler class at rank zero is the original cohomological unit. -/
theorem complexCohomologyEulerClass_zero (h : ContinuousHermitianMetric E)
    (hr : ∀ x, Module.finrank ℂ (E x) = 0) :
    h.complexCohomologyEulerClass 0 hr = singularCohomologyOne ℚ X := by
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let : ∀ x, InnerProductSpace ℝ (E x) := h.realFiberInnerProductSpace
  let : ∀ x, FiniteDimensional ℂ (E x) := fun x ↦ finite_fiber (E := E) x
  let := nativeModelTopology E (EuclideanSpace ℝ (Fin 0))
  let := h.realNativeFiberBundle 0 hr
  let := h.realNativeVectorBundle 0 hr
  -- Any two actual empty real frames coincide, so both prescribed orientations agree.
  have ho : h.complexRealOrientation 0 hr = zeroRankBundleOrientation E := by
    funext x
    let b := Module.finBasisOfFinrankEq ℂ (E x) (hr x)
    rw [← h.complexRealOrientation_basis 0 hr x b]
    unfold zeroRankBundleOrientation
    congr 1
    apply DFunLike.ext
    intro i
    exact Fin.elim0 i
  have hc : h.complexCohomologyOrientation 0 hr = zeroRankIntegralCohomologyOrientation E := by
    unfold complexCohomologyOrientation zeroRankIntegralCohomologyOrientation
    congr 1
  change cohomologyEulerClass ℚ 0 E
    (h.complexCohomologyOrientation 0 hr).rationalization = _
  rw [hc, ← cohomologyEulerClass_rationalization]
  exact zeroRankRationalEulerClass_eq_one E

attribute [local instance] finiteSumTopology isFiniteRank_finiteSum sumTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- An actual finite line splitting gives the product of the original rational first Chern roots. -/
theorem complexCohomologyEulerClass_eq_prod_of_lineSplitting [T2Space X]
    (n : ℕ) (L : Fin n → X → Type u)
    [∀ i x, NormedAddCommGroup (L i x)] [∀ i x, NormedSpace ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)]
    (hL : ∀ i, ContinuousHermitianMetric (L i))
    (hline : ∀ i x, Module.finrank ℂ (L i x) = 1)
    (h : ContinuousHermitianMetric E) (hr : ∀ x, Module.finrank ℂ (E x) = n)
    (e : Iso E (FiniteSum n L)) :
    singularEvenCohomologyOf ℚ X n (h.complexCohomologyEulerClass n hr) =
      ∏ i, singularEvenCohomologyOf ℚ X 1
        (singularCohomologyRationalization X 2 (firstChernClass (L i) (hline i))) := by
  induction n generalizing E with
  | zero =>
      -- The empty product has exactly the positive empty-frame Euler normalization.
      rw [h.complexCohomologyEulerClass_zero hr, singularEvenCohomologyOf_one]
      simp
  | succ n ih =>
      -- Split off one actual line, putting the tail first so the degree is literally n+1.
      let T := FiniteSum n (fun i ↦ L i.succ)
      let hT := ContinuousHermitianMetric.finiteSum (fun i ↦ hL i.succ)
      have hTdim (x : X) : Module.finrank ℂ (T x) = n := by
        rw [finrank_finiteSum]
        simp only [hline, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
          mul_one]
      let split : Iso E (T ×ᵇ L 0) :=
        (e.trans (finiteSumSuccIso n L)).trans sumCommIso
      have hp : h.complexCohomologyEulerClass (n + 1) hr =
          singularCohomologyEvenCup ℚ X n 1
            (hT.complexCohomologyEulerClass n hTdim)
            ((hL 0).complexCohomologyEulerClass 1 (hline 0)) :=
        hT.cohomologyEulerClass_complex_prod (hL 0) h n 1 hTdim (hline 0) hr split
      rw [hp, singularEvenCohomologyOf_cup]
      rw [ih (fun i ↦ L i.succ) (fun i ↦ hL i.succ) (fun i ↦ hline i.succ)
        hT hTdim (Iso.refl T)]
      -- The identity bundle map compares the supplied line norms with its metric native norms.
      have hnorm := @firstChernClass_eq_of_iso X _ (L 0) (hL 0).fiberNormedAddCommGroup
        (fun x ↦ ((hL 0).fiberInnerProductSpace x).toNormedSpace) _ _ (hline 0) (L 0)
        (inferInstance : ∀ x, NormedAddCommGroup (L 0 x))
        (inferInstance : ∀ x, NormedSpace ℂ (L 0 x)) _ _ (hline 0) (Iso.refl (L 0))
      have hfirst : (hL 0).complexCohomologyEulerClass 1 (hline 0) =
          singularCohomologyRationalization X 2 (firstChernClass (L 0) (hline 0)) :=
        ((hL 0).cohomologyEulerClass_complex_line (hline 0)).trans
          (congrArg (singularCohomologyRationalization X 2) hnorm)
      rw [hfirst, Fin.prod_univ_succ, mul_comm]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
