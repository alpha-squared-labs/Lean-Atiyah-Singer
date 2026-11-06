/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexThomDefectEuler
public import AtiyahSinger.Topology.ComplexThomDefectNaturality
public import AtiyahSinger.Topology.InverseToddOperations
public import AtiyahSinger.Topology.ProjectiveSplitDetection
public import AtiyahSinger.Topology.SplitThomCharacteristicIdentity

/-!
# The Thom defect for an actual finite line splitting

Public module ID: M1718.

Extend the specified lines along an actual finite projective tower. The Euler
equation there annihilates the difference between the original defect and its
signed inverse Todd value. The stable projective detection theorem then gives
zero after restriction along the actual common section. Naturality along the
same pullback isomorphism returns both classes to the original bundle.

No Euler class is canceled on the original base. Source: SG III.12, the splitting
argument for the characteristic Thom defect, realized on actual projective bundles.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

attribute [local instance] finiteSumTopology isFiniteRank_finiteSum isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original defect has its inverse Todd value for any actual finite line splitting. -/
theorem complexThomDefectComponent_eq_inverseTodd_of_lineSplitting
    {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    (r : ℕ) (L : Fin r → X → Type u)
    [∀ i x, NormedAddCommGroup (L i x)] [∀ i x, NormedSpace ℂ (L i x)]
    [∀ i, TopologicalSpace (TotalSpace Unit (L i))] [∀ i, IsFiniteRank (L i)]
    (hL : ∀ i, ContinuousHermitianMetric (L i))
    (hline : ∀ i x, Module.finrank ℂ (L i x) = 1)
    (h : ContinuousHermitianMetric E) (hr : ∀ x, Module.finrank ℂ (E x) = r)
    (e : Iso E (FiniteSum r L)) (j : ℕ) :
    h.complexThomDefectComponent r hr j =
      (-1 : ℚ) ^ (r + j) • inverseToddClassComponent E h j := by
  classical
  obtain ⟨Q, cQ, tQ, M, nM, sM, τM, fM, hM, hm, p, s, hps, hes, hdet⟩ :=
    exists_projectiveSplitDetection r j L hL hline
  let := cQ
  let := tQ
  let := nM
  let := sM
  let := τM
  let := fM
  let G := FiniteSum r M
  let hG := ContinuousHermitianMetric.finiteSum hM
  have hGdim (q : Q) : Module.finrank ℂ (G q) = r := by
    rw [finrank_finiteSum]
    simp only [hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  let roots := ∏ i : Fin r, singularEvenCohomologyOf ℚ Q 1
    (singularCohomologyRationalization Q 2 (firstChernClass (M i) (hm i)))
  let d := hG.complexThomDefectComponent r hGdim j
  let t := (-1 : ℚ) ^ (r + j) • inverseToddClassComponent G hG j
  -- On this actual enlarged bundle the two zero-section equations have the identical root factor.
  have heuler := complexCohomologyEulerClass_eq_prod_of_lineSplitting r M hM hm hG hGdim
    (Iso.refl G)
  have hzero := hG.complexThomDefectComponent_mul_euler r hGdim j
  have hcharacter := chernCharacterKZeroComponent_lambdaMinusOne_of_lineSplitting r M hM hm
    hG (Iso.refl G) j
  rw [heuler, hcharacter] at hzero
  have hann : roots * singularEvenCohomologyOf ℚ Q j (d - t) = 0 := by
    rw [map_sub, mul_sub]
    apply sub_eq_zero.mpr
    exact (mul_comm roots (singularEvenCohomologyOf ℚ Q j d)).trans hzero
  have hrestricted := hdet (d - t) hann
  rw [map_sub, sub_eq_zero] at hrestricted
  -- The common section recovers exactly the specified original lines, coordinate by coordinate.
  let es : Iso ((s : X → Q) *ᵖ G) (FiniteSum r L) :=
    (finiteSumPullbackIso s r M).trans (Iso.finiteSum (fun i ↦ (hes i).some))
  let eback : Iso E ((s : X → Q) *ᵖ G) := e.trans es.symm
  have hdefect := complexThomDefectComponent_eq_pullback_of_iso h hG r hr hGdim s eback j
  have htodd : singularCohomologyPullback ℚ s (2 * j) (inverseToddClassComponent G hG j) =
      inverseToddClassComponent E h j := by
    rw [inverseToddClassComponent_pullback]
    exact inverseToddClassComponent_eq_of_iso _ (hG.pullback s) E h eback.symm j
  rw [hdefect]
  change singularCohomologyPullback ℚ s (2 * j) d = _
  rw [hrestricted]
  change singularCohomologyPullback ℚ s (2 * j)
    ((-1 : ℚ) ^ (r + j) • inverseToddClassComponent G hG j) = _
  rw [map_smul, htodd]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
