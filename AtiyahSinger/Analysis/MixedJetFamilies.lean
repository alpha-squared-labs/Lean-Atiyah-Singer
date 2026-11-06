/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Amplitude
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Mixed jets of continuous smooth families

Public module ID: M0799.

Joint continuity of full jets in the spatial and frequency variables implies
continuity of the original mixed amplitude derivatives.
Fixed continuous-linear restrictions of jets and permutations of
product coordinates preserve the same family. No derivative in the external
topological parameter is taken.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set Topology
open scoped ContDiff

set_option maxSynthPendingDepth 20

private theorem continuous_twice_jets
    {T X V : Type*} [TopologicalSpace T] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : T → X → V)
    (hjets : ∀ k : ℕ, Continuous (fun p : T × X ↦ iteratedFDeriv ℝ k (f p.1) p.2))
    (j : ℕ) : ∀ i : ℕ, Continuous
      (fun p : T × X ↦ iteratedFDeriv ℝ i (iteratedFDeriv ℝ j (f p.1)) p.2) := by
  induction j with
  | zero =>
    intro i
    let C := (continuousMultilinearCurryFin0 ℝ X V).symm.toContinuousLinearEquiv
    let P := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ X)
      V (X [×0]→L[ℝ] V) C.toContinuousLinearMap
    have h := P.continuous.comp (hjets i)
    apply h.congr
    intro p
    symm
    change iteratedFDeriv ℝ i (C ∘ f p.1) p.2 =
      C.toContinuousLinearMap.compContinuousMultilinearMap (iteratedFDeriv ℝ i (f p.1) p.2)
    exact C.iteratedFDeriv_comp_left
  | succ j ih =>
    intro i
    let C :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) ↦ X) V).symm
        |>.toContinuousLinearEquiv
    let R := continuousMultilinearCurryRightEquiv' ℝ i X (X [×j]→L[ℝ] V)
    let P := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin i ↦ X)
      (X →L[ℝ] X [×j]→L[ℝ] V) (X [×(j + 1)]→L[ℝ] V) C.toContinuousLinearMap
    have h := P.continuous.comp (R.continuous.comp (ih (i + 1)))
    apply h.congr
    intro p
    symm
    rw [iteratedFDeriv_succ_eq_comp_left]
    change iteratedFDeriv ℝ i (C ∘ fderiv ℝ (iteratedFDeriv ℝ j (f p.1))) p.2 = _
    rw [C.iteratedFDeriv_comp_left]
    congr 1
    change iteratedFDeriv ℝ i (fderiv ℝ (iteratedFDeriv ℝ j (f p.1))) p.2 =
      R (iteratedFDeriv ℝ (i + 1) (iteratedFDeriv ℝ j (f p.1)) p.2)
    rw [iteratedFDeriv_succ_eq_comp_right]
    exact (R.apply_symm_apply _).symm

private theorem partial_jet_family
    {T X Y V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : T → X × Y → V) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hjets : ∀ k : ℕ, Continuous
      (fun p : T × (X × Y) ↦ iteratedFDeriv ℝ k (f p.1) p.2)) (j : ℕ) :
    (∀ t, ContDiff ℝ ∞ (fun w : X × Y ↦ iteratedFDeriv ℝ j (fun y ↦ f t (w.1, y)) w.2)) ∧
    ∀ k : ℕ, Continuous (fun p : T × (X × Y) ↦ iteratedFDeriv ℝ k
      (fun w : X × Y ↦ iteratedFDeriv ℝ j (fun y ↦ f p.1 (w.1, y)) w.2) p.2) := by
  let R : Y →L[ℝ] X × Y := ContinuousLinearMap.inr ℝ X Y
  let P : ((X × Y) [×j]→L[ℝ] V) →L[ℝ] (Y [×j]→L[ℝ] V) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j ↦ R)
  have heq (t : T) : (fun w : X × Y ↦ iteratedFDeriv ℝ j (fun y ↦ f t (w.1, y)) w.2) =
      P ∘ iteratedFDeriv ℝ j (f t) := by
    funext w
    let g (z : X × Y) : V := f t ((w.1, 0) + z)
    have hg : ContDiff ℝ ∞ g := (hf t).comp (contDiff_const.add contDiff_id)
    have hcomp : (fun y ↦ f t (w.1, y)) = g ∘ R := by
      funext y
      simp only [g, R, Function.comp_apply, ContinuousLinearMap.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add]
    rw [hcomp, R.iteratedFDeriv_comp_right hg w.2 (by simp)]
    change _ = (iteratedFDeriv ℝ j (f t) w).compContinuousLinearMap _
    congr 1
    dsimp only [g]
    rw [iteratedFDeriv_comp_add_left]
    simp only [R, ContinuousLinearMap.inr_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.eta]
  have hDj (t : T) : ContDiff ℝ ∞ (iteratedFDeriv ℝ j (f t)) :=
    (hf t).iteratedFDeriv_right (by simp)
  constructor
  · intro t
    rw [heq]
    exact P.contDiff.comp (hDj t)
  · intro k
    let Q := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
      (fun _ : Fin k ↦ X × Y) ((X × Y) [×j]→L[ℝ] V) (Y [×j]→L[ℝ] V) P
    have h := Q.continuous.comp (continuous_twice_jets f hjets j k)
    apply h.congr
    intro p
    symm
    rw [heq]
    exact P.iteratedFDeriv_comp_left (hDj p.1).contDiffAt (by simp)

private theorem linear_pullback_jet_family
    {T X Y V : Type*} [TopologicalSpace T]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : T → Y → V) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hjets : ∀ k : ℕ, Continuous (fun p : T × Y ↦ iteratedFDeriv ℝ k (f p.1) p.2))
    (L : X →L[ℝ] Y) :
    (∀ t, ContDiff ℝ ∞ (f t ∘ L)) ∧ ∀ k : ℕ,
      Continuous (fun p : T × X ↦ iteratedFDeriv ℝ k (f p.1 ∘ L) p.2) := by
  refine ⟨fun t ↦ (hf t).comp L.contDiff, ?_⟩
  intro k
  let P : (Y [×k]→L[ℝ] V) →L[ℝ] (X [×k]→L[ℝ] V) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin k ↦ L)
  have h := P.continuous.comp ((hjets k).comp
    (continuous_fst.prodMk (L.continuous.comp continuous_snd)))
  apply h.congr
  intro p
  symm
  exact L.iteratedFDeriv_comp_right (hf p.1) p.2 (by simp)

set_option maxHeartbeats 600000 in
-- Restrict full jets to each of the three original coordinate directions.
/-- Joint full-jet continuity implies continuity of every original mixed amplitude derivative. -/
theorem continuous_amplitudeDerivative_of_continuous_jets
    {T : Type*} [TopologicalSpace T] {n r s : ℕ}
    (a : T → AmplitudeFunction n r s)
    (ha : ∀ t, ContDiff ℝ ∞ (fun z : (EuclideanSpace ℝ (Fin n) ×
      EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n) ↦ a t z.1.1 z.1.2 z.2))
    (hjets : ∀ l : ℕ, Continuous
      (fun p : T × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
          EuclideanSpace ℝ (Fin n)) ↦ iteratedFDeriv ℝ l
        (fun z ↦ a p.1 z.1.1 z.1.2 z.2) p.2)) (i j k : ℕ) :
    Continuous
      (fun p : T × ((EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ×
        EuclideanSpace ℝ (Fin n)) ↦ amplitudeDerivative (a p.1) i j k p.2.1.1 p.2.1.2 p.2.2) := by
  let X := EuclideanSpace ℝ (Fin n)
  let f (t : T) (z : (X × X) × X) := a t z.1.1 z.1.2 z.2
  let f₁ (t : T) (z : (X × X) × X) := iteratedFDeriv ℝ k (fun ξ ↦ f t (z.1, ξ)) z.2
  have h₁ := partial_jet_family f ha hjets k
  let P₁ : ((X × X) × X) →L[ℝ] ((X × X) × X) := {
    toFun := fun z ↦ ((z.1.1, z.2), z.1.2)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl
    cont := by fun_prop }
  have hp₁ := linear_pullback_jet_family f₁ h₁.1 h₁.2 P₁
  let f₂ (t : T) (z : (X × X) × X) :=
    iteratedFDeriv ℝ j (fun y ↦ f₁ t (P₁ (z.1, y))) z.2
  have h₂ := partial_jet_family (fun t ↦ f₁ t ∘ P₁) hp₁.1 hp₁.2 j
  let P₂ : ((X × X) × X) →L[ℝ] ((X × X) × X) := {
    toFun := fun z ↦ ((z.2, z.1.1), z.1.2)
    map_add' := by intro x y; rfl
    map_smul' := by intro c x; rfl
    cont := by fun_prop }
  have hp₂ := linear_pullback_jet_family f₂ h₂.1 h₂.2 P₂
  let f₃ (t : T) (z : (X × X) × X) :=
    iteratedFDeriv ℝ i (fun x ↦ f₂ t (P₂ (z.1, x))) z.2
  have h₃ := partial_jet_family (fun t ↦ f₂ t ∘ P₂) hp₂.1 hp₂.2 i
  have hc := (continuousMultilinearCurryFin0 ℝ ((X × X) × X)
    (X [×i]→L[ℝ] X [×j]→L[ℝ] X [×k]→L[ℝ]
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin s)))).continuous.comp (h₃.2 0)
  change Continuous (fun p : T × ((X × X) × X) ↦
    (iteratedFDeriv ℝ 0 (f₃ p.1) p.2).curry0) at hc
  have hc' : Continuous (fun p : T × ((X × X) × X) ↦ f₃ p.1 p.2) := by
    simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using hc
  exact hc'.comp (continuous_fst.prodMk
    ((continuous_snd.snd.prodMk continuous_snd.fst.snd).prodMk continuous_snd.fst.fst))

end AtiyahSinger
