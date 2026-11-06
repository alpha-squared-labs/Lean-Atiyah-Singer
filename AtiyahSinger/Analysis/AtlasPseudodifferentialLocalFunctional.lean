/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasPseudodifferentialLocalSchwartzAction

/-!
# Point functionals of the original whole atlas PDO

Public module ID: M0288.

After original cutoff extension, every specified fiber dual applied to the
whole PDO output is a continuous scalar Schwartz functional. A nonzero member
of the original output partition recovers the actual value exactly from the
proved localized Schwartz action. The fixed fiber functional requires no
separate chosen norm on the original abstract fiber.

This supplies the original local distribution functionals for the horizontal
and vertical matrix-pairing argument, retaining the smoothing remainder.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set Topology
open scoped Manifold ContDiff SchwartzMap

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {E F : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  {A : SmoothComplexBundleAtlas (n := n) E} {B : SmoothComplexBundleAtlas (n := n) F}

namespace AtlasPseudodifferentialOperator

set_option maxSynthPendingDepth 30 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every specified fiber dual of the whole PDO output is a local Schwartz functional. -/
theorem exists_localActionFunctional {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)
    (L : AtlasBundlePresentation A) (K : AtlasBundlePresentation B)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (D : AtlasChartCutoff A c) (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (x : M) (l : F x →ₗ[ℂ] ℂ) :
    ∃ T : 𝓢(EuclideanSpace ℝ (Fin n),
        EuclideanSpace ℂ (Fin (A.rank D.frameIndex))) →L[ℂ] ℂ,
      ∀ v, T v = l ((P.toLinearMap (D.extend hc v)).val x) := by
  classical
  -- At the specified point, some member of the original partition is nonzero.
  have hchoose : ∃ j : Fin K.size, K.cutoff j x ≠ 0 := by
    by_contra! h
    have hsum := K.sum_cutoff x
    simp only [h, Finset.sum_const_zero] at hsum
    exact zero_ne_one hsum
  obtain ⟨j, hj⟩ := hchoose
  have hx := K.support_subset j (subset_tsupport _ hj)
  let X := EuclideanSpace ℝ (Fin n)
  let V := EuclideanSpace ℂ (Fin (B.rank (K.frameIndex j)))
  let e := EuclideanSpace.equiv (Fin (B.rank (K.frameIndex j))) ℂ
  let f := B.frameLinearEquiv (K.frameIndex j) x hx.2
  let q : V →ₗ[ℂ] ℂ := l.comp (f.symm.toLinearMap.comp e.toLinearMap)
  let qC : V →L[ℂ] ℂ := { q with cont := q.continuous_of_finiteDimensional }
  let ev : 𝓢(X, V) →L[ℂ] V := (BoundedContinuousFunction.evalCLM ℂ (K.chart j x)).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ X V)
  obtain ⟨T, hT⟩ := P.exists_localActionSchwartz L K D hc j
  let R := (K.cutoff j x : ℂ)⁻¹ • (qC.comp (ev.comp T))
  refine ⟨R, ?_⟩
  intro v
  let u := P.toLinearMap (D.extend hc v)
  have hlocal : K.localize j u (K.chart j x) = (K.cutoff j x : ℂ) • e.symm (f (u.val x)) := by
    change K.localizedFunction j u (K.chart j x) = _
    simp only [AtlasBundlePresentation.localizedFunction,
      ite_eq_left ((K.chart j).map_source hx.1), (K.chart j).left_inv hx.1]
    change (K.cutoff j x : ℂ) • e.symm ((B.chart (K.frameIndex j)
      ⟨(K.chart j).symm (K.chart j x), u.val ((K.chart j).symm (K.chart j x))⟩).2) = _
    have hpoint := congrArg (fun y : M ↦ (⟨y, u.val y⟩ : TotalSpace Unit F))
      ((K.chart j).left_inv hx.1)
    rw [hpoint]
    rfl
  -- Undo exactly this cutoff and frame; the original output section is unchanged.
  change (K.cutoff j x : ℂ)⁻¹ * q (T v (K.chart j x)) = l (u.val x)
  rw [hT v, hlocal, map_smul]
  change (K.cutoff j x : ℂ)⁻¹ * ((K.cutoff j x : ℂ) *
    l (f.symm (e (e.symm (f (u.val x)))))) = _
  rw [e.apply_symm_apply, f.symm_apply_apply, inv_mul_cancel_left₀]
  exact_mod_cast hj

end AtlasPseudodifferentialOperator

end AtiyahSinger
