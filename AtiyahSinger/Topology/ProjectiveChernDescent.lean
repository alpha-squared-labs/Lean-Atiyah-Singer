/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ModelPullbackTopology
public import AtiyahSinger.Topology.ProjectiveChernNaturality
public import AtiyahSinger.Topology.ProjectiveSplitChern
public import AtiyahSinger.Topology.ProjectiveTautologicalComparison

/-!
# Projective Chern coefficients on a specified split pullback

Public module ID: M2005.

Naturality of the genuine leading-power expansion and the actual coordinate
open-cover relation identify the pulled-back coefficients with the elementary
symmetric classes of the specified line coordinates. The coordinate maps have
the original Unit pullback topology; its exact equality with native retyping
lets the proof retain all original vectors, norms and metrics.

Both projective power-basis bijections remain explicit premises here. The
actual projective bundle theorem is needed before applying this comparison
to construct the original higher Chern classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle

universe u

variable (r : ℕ) {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  (h : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ContinuousHermitianMetric E) (f : C(Y, X))

local instance : ∀ y, NormedAddCommGroup (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedAddCommGroup (E (f y)))

local instance : ∀ y, NormedSpace ℂ (((f : Y → X) *ᵖ E) y) :=
  fun y ↦ inferInstanceAs (NormedSpace ℂ (E (f y)))

local instance : FiberBundle (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  FiberBundle.pullback (F := EuclideanSpace ℂ (Fin r)) (E := E) f

local instance : VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) ((f : Y → X) *ᵖ E) :=
  VectorBundle.pullback ℂ (F := EuclideanSpace ℂ (Fin r)) (E := E) f

attribute [local instance] hermitianProjectiveTopology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Specified line coordinates identify the genuine Chern coefficients on an actual pullback. -/
theorem hermitianProjectiveChernCoefficient_pullback_eq_elementarySymmetric
    (hb : Function.Bijective
      (singularCohomologyPowerCombination ℤ (hermitianProjectiveProjection r E h)
        (hermitianProjectiveChernRoot r E h) r r (fun i ↦ Nat.le_of_lt i.isLt)))
    (hb' : Function.Bijective
      (singularCohomologyPowerCombination ℤ
        (hermitianProjectiveProjection r ((f : Y → X) *ᵖ E)
          (hermitianProjectivePullbackMetric r E h f))
        (hermitianProjectiveChernRoot r ((f : Y → X) *ᵖ E)
          (hermitianProjectivePullbackMetric r E h f)) r r
        (fun i ↦ Nat.le_of_lt i.isLt)))
    (L : Fin r → Y → Type u) [∀ i y, NormedAddCommGroup (L i y)]
    [∀ i y, NormedSpace ℂ (L i y)] [∀ i, TopologicalSpace (TotalSpace Unit (L i))]
    [∀ i, IsFiniteRank (L i)]
    (a : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ i : Fin r, Hom ((f : Y → X) *ᵖ E) (L i))
    (hL : ∀ i y, Module.finrank ℂ (L i y) = 1)
    (hdetect : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      ∀ (y : Y) (v : E (f y)), (∀ i, (a i).linearMap y v = 0) → v = 0)
    (k : ℕ) :
    singularCohomologyPullback ℤ f (2 * k)
        (projectiveChernCoefficient (hermitianProjectiveProjection r E h) r
          (hermitianProjectiveChernRoot r E h) hb k) =
      singularCohomologyElementarySymmetric ℤ Y
        (List.ofFn (fun i ↦ firstChernClass (L i) (hL i))) k := by
  let V := EuclideanSpace ℂ (Fin r)
  let F := (f : Y → X) *ᵖ E
  let hF := hermitianProjectivePullbackMetric r E h f
  let p := hermitianProjectiveProjection r E h
  let q := hermitianProjectiveProjection r F hF
  let g := hermitianProjectivePullback r E h f
  let t := hermitianProjectiveChernRoot r E h
  let t' := hermitianProjectiveChernRoot r F hF
  -- First transport the leading-power expansion along the original projective square.
  have ht : singularCohomologyPullback ℤ g 2 t = t' :=
    hermitianProjectiveChernRoot_pullback r E h f
  have hb'' : Function.Bijective
      (singularCohomologyPowerCombination ℤ q (singularCohomologyPullback ℤ g 2 t)
        r r (fun i ↦ Nat.le_of_lt i.isLt)) := by
    rw [ht]
    exact hb'
  have hnatural := projectiveChernCoefficient_pullback p q f g
    (hermitianProjectiveProjection_comp_pullback r E h f) r t hb hb'' k
  have hcoeff (s₁ s₂ : singularCohomology ℤ (HermitianProjectiveBundle r F hF) 2)
      (hb₁ : Function.Bijective
        (singularCohomologyPowerCombination ℤ q s₁ r r (fun i ↦ Nat.le_of_lt i.isLt)))
      (hb₂ : Function.Bijective
        (singularCohomologyPowerCombination ℤ q s₂ r r (fun i ↦ Nat.le_of_lt i.isLt)))
      (hs : s₁ = s₂) :
      projectiveChernCoefficient q r s₁ hb₁ k = projectiveChernCoefficient q r s₂ hb₂ k := by
    subst s₂
    rfl
  have hnatural' := hnatural.trans (hcoeff _ _ hb'' hb' ht)
  -- Retyping the native pullback changes no topology or coordinate map.
  let := modelTopology V E
  let a₀ (i : Fin r) := (a i).linearMap
  have ha₀ (i : Fin r) := (a i).continuous_total
  have hdetect₀ : ∀ (y : Y) (v : F y), (∀ i, a₀ i y v = 0) → v = 0 := hdetect
  let := modelTopology V F
  let a' (i : Fin r) : Hom F (L i) :=
    { linearMap := a₀ i
      continuous_total := by
        change @Continuous (TotalSpace Unit F) (TotalSpace Unit (L i))
          (modelTopology V F) _ _
        rw [modelTopology_pullback V E (f : Y → X)]
        exact ha₀ i }
  have hproduct := hermitianProjectiveChernRoot_prod_sub_eq_zero r F hF L a' hL hdetect₀
  -- The same line-coordinate product determines every signed coefficient, including rank zero.
  exact hnatural'.trans (projectiveChernCoefficient_eq_elementarySymmetric q r t' hb'
    (fun i ↦ firstChernClass (L i) (hL i)) hproduct k)

end AtiyahSinger.ComplexBundle
