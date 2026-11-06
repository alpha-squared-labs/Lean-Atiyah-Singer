/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LeviCivitaRegularity
public import AtiyahSinger.Geometry.SpinConnectionFrames

import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Levi-Civita coefficients in the original lifted spin frames

Public module ID: M1455.

The real connection matrix uses the actual native Levi-Civita connection and
the zero-extended columns of the specified lifted frame. Its first index is
the differentiated column and its second index is the output coordinate.
The coefficients are smooth on the original chart and skew by compatibility
with the given metric. No global extension of a local smooth field is used.

Source: Spin Geometry II.4, the orthonormal-frame expression for a metric
connection and its spin lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff Matrix.Norms.Elementwise

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology

set_option maxSynthPendingDepth 50

variable {m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [RiemannianBundle
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞
    (EuclideanSpace ℝ (Fin (2 * m)))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) : M → Type _)]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m} {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m)))
local notation "TM" => TangentSpace I (M := M)
local notation "V" => EuclideanSpace ℝ (Fin (2 * m))

namespace TopologicalSpinStructure

/-- The actual Levi-Civita coefficient matrix, with differentiated frame index first. -/
def liftedLeviCivitaCoefficients (S : TopologicalSpinStructure m (TM) o hm hP)
    (b x : M) : TM x →L[ℝ] (Fin (2 * m) → Fin (2 * m) → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X a j ↦ inner ℝ
        (CovariantDerivative.leviCivitaConnection I M
          (S.liftedFrameField (n := 2 * m) b a) x X)
        (S.liftedFrameField (n := 2 * m) b j x)
      map_add' := by
        intro X Y
        funext a j
        simp only [map_add, inner_add_left]
        rfl
      map_smul' := by
        intro c X
        funext a j
        simp only [map_smul, real_inner_smul_left, RingHom.id_apply]
        rfl }

/-- Along every locally smooth tangent field, the same lifted coefficients are smooth. -/
theorem contMDiffOn_liftedLeviCivitaCoefficients
    (S : TopologicalSpinStructure m (TM) o hm hP) (b : M) (U : Set M) (hU : IsOpen U)
    (hUb : U ⊆ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (X : ∀ x : M, TM x)
    (hX : ContMDiffOn I (I).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle I M))
      U) :
    ContMDiffOn I 𝓘(ℝ, (Fin (2 * m) → Fin (2 * m) → ℝ)) ∞
      (fun x ↦ S.liftedLeviCivitaCoefficients b x (X x))
      U := by
  apply contMDiffOn_pi_space.mpr
  intro a
  apply contMDiffOn_pi_space.mpr
  intro j
  exact contMDiffOn_leviCivitaConnection_inner _ hU X _ _ hX
    (((S.isLocalFrameOn_liftedFrameField (n := 2 * m) b).contMDiffOn a).mono hUb)
    (((S.isLocalFrameOn_liftedFrameField (n := 2 * m) b).contMDiffOn j).mono hUb)

/-- The original metric-compatible connection has a skew matrix in these same lifted frames. -/
theorem liftedLeviCivitaCoefficients_skew
    (S : TopologicalSpinStructure m (TM) o hm hP) (b x : M)
    (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (X : TM x) (a j : Fin (2 * m)) :
    S.liftedLeviCivitaCoefficients b x X a j =
      -S.liftedLeviCivitaCoefficients b x X j a := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let s := S.liftedFrameField (n := 2 * m) b
  let hs := S.isLocalFrameOn_liftedFrameField (n := 2 * m) b
  have hpair : (fun y ↦ inner ℝ (s a y) (s j y)) =ᶠ[nhds x]
      (fun _ ↦ inner ℝ (EuclideanSpace.basisFun (Fin (2 * m)) ℝ a)
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)) := by
    filter_upwards [t.open_baseSet.mem_nhds hx] with y hy
    dsimp only [s, liftedFrameField]
    rw [dite_eq_left hy, dite_eq_left hy, LinearIsometryEquiv.inner_map_map]
  have hzero : mvfderiv I (fun y ↦ inner ℝ (s a y) (s j y)) x X = 0 := by
    unfold mvfderiv
    rw [hpair.mfderiv_eq, mfderiv_const]
    rfl
  have hmetric :=
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection I (M := M)).mvfderiv_inner_eq
      (fun _ ↦ X) ((hs.contMDiffAt t.open_baseSet hx a).mdifferentiableAt (by simp))
      ((hs.contMDiffAt t.open_baseSet hx j).mdifferentiableAt (by simp))
  change mvfderiv I (fun y ↦ inner ℝ (s a y) (s j y)) x X =
    inner ℝ (CovariantDerivative.leviCivitaConnection I M (s a) x X) (s j x) +
      inner ℝ (s a x) (CovariantDerivative.leviCivitaConnection I M (s j) x X) at hmetric
  rw [hzero] at hmetric
  conv_rhs at hmetric =>
    rhs
    rw [real_inner_comm]
  exact eq_neg_of_add_eq_zero_left hmetric.symm

/-- The same native coefficient form pulled back through a supplied original base chart. -/
def liftedLeviCivitaForm (S : TopologicalSpinStructure m (TM) o hm hP)
    (c : OpenPartialHomeomorph M V) (b : M) (z : V) :
    V →L[ℝ] (Fin (2 * m) → Fin (2 * m) → ℝ) :=
  (S.liftedLeviCivitaCoefficients b (c.symm z)).comp (mfderiv I I c.symm z)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- In every original smooth base chart the lifted Levi-Civita form is smooth. -/
theorem contDiffOn_liftedLeviCivitaForm
    (S : TopologicalSpinStructure m (TM) o hm hP)
    (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (b : M) :
    ContDiffOn ℝ ∞ (S.liftedLeviCivitaForm c b)
      (c.target ∩ c.symm ⁻¹' ((S.smoothPrincipalAtlas I).trivialization b).baseSet) := by
  let t := (S.smoothPrincipalAtlas I).trivialization b
  let U := c.source ∩ t.baseSet
  have hU : IsOpen U := c.open_source.inter t.open_baseSet
  apply contDiffOn_clm_apply.mpr
  intro v
  let X (y : M) : TM y := mfderiv I I c.symm (c y) v
  -- A fixed coordinate vector pulls back to a smooth local tangent field.
  have hX : ContMDiffOn I (I).tangent ∞
      (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) U := by
    intro x hx
    have hcx := contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas («I» := I) (n := ∞) hc) hx.1
    have hci := contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas («I» := I) (n := ∞) hc) (c.map_source hx.1)
    have hconst : ContMDiffAt I (I).tangent ∞
        (fun z : V ↦ (⟨z, v⟩ : TangentBundle I V)) (c x) :=
      contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
    have htan := hci.contMDiffAt_tangentMap
      (X := (⟨c x, v⟩ : TangentBundle I V)) (m := ∞) (by simp)
    have hmap := (htan.comp (c x) hconst).comp x hcx
    apply ContMDiffAt.contMDiffWithinAt
    apply hmap.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds hx.1] with y hy
    simp only [Function.comp_apply, tangentMap, X]
    exact TotalSpace.ext (c.left_inv hy).symm HEq.rfl
  -- The Koszul regularity theorem applies to the original zero-extended frame.
  have hcoeff := S.contMDiffOn_liftedLeviCivitaCoefficients b U hU
    (fun _ h ↦ h.2) X hX
  intro z hz
  have hcz : c.symm z ∈ U := ⟨c.map_target hz.1, hz.2⟩
  have hci := contMDiffAt_symm_of_mem_maximalAtlas
    (IsManifold.subset_maximalAtlas («I» := I) (n := ∞) hc) hz.1
  have hcomp := ((hcoeff (c.symm z) hcz).contMDiffAt (hU.mem_nhds hcz)).comp z hci
  apply ContDiffAt.contDiffWithinAt
  apply hcomp.contDiffAt.congr_of_eventuallyEq
  filter_upwards [c.open_target.mem_nhds hz.1] with w hw
  simp only [liftedLeviCivitaForm, ContinuousLinearMap.comp_apply, Function.comp_apply,
    X]
  exact congrArg (S.liftedLeviCivitaCoefficients b (c.symm w))
    (congrArg (fun z : V ↦ (mfderiv I I c.symm z v : V)) (c.right_inv hw).symm)

end TopologicalSpinStructure

end AtiyahSinger
