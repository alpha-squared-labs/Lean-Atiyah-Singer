/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.LocalFrameConnection
public import AtiyahSinger.Geometry.SpinFrameTransition
public import AtiyahSinger.Geometry.SpinLeviCivitaCoefficients

/-!
# Gauge transformation of the original lifted Levi-Civita coefficients

Public module ID: M1456.

The two original unit-section frames have the standard vector connection
transformation law. The same principal transition determines their vector
matrix, and the derivative is the actual manifold derivative of that matrix.
The coefficient convention keeps the differentiated frame index first.

Source: the local connection transformation law in Spin Geometry II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

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

/-- The vector endomorphism of the same lifted coefficient matrix. -/
def liftedLeviCivitaEndomorphism (S : TopologicalSpinStructure m (TM) o hm hP)
    (b x : M) (X : TM x) : V →L[ℝ] V :=
  (Matrix.toEuclideanLin (Matrix.transpose
    (S.liftedLeviCivitaCoefficients b x X))).toContinuousLinearMap

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The vector matrix satisfies the gauge law for the same native connection in both frames. -/
theorem liftedLeviCivitaEndomorphism_gauge
    (S : TopologicalSpinStructure m (TM) o hm hP) (a b x : M)
    (ha : x ∈ ((S.smoothPrincipalAtlas I).trivialization a).baseSet)
    (hb : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet) (X : TM x) (v : V) :
    let t := (S.smoothPrincipalAtlas I).trivialization
    let G := fun y ↦ (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm
        ((t b) ((t a).toPartialEquiv.symm (y, 1))).2)).toLinearMap.toContinuousLinearMap
    S.liftedLeviCivitaEndomorphism b x X (G x v) + mvfderiv I G x X v =
      G x (S.liftedLeviCivitaEndomorphism a x X v) := by
  classical
  let t := (S.smoothPrincipalAtlas I).trivialization
  let U := (t a).baseSet ∩ (t b).baseSet
  have hU : IsOpen U := (t a).open_baseSet.inter (t b).open_baseSet
  have hx : x ∈ U := ⟨ha, hb⟩
  let s := S.liftedFrameField (n := 2 * m) a
  let r := S.liftedFrameField (n := 2 * m) b
  let hs := (S.isLocalFrameOn_liftedFrameField (n := 2 * m) a).mono
    (show U ⊆ (t a).baseSet from Set.inter_subset_left)
  let hr := (S.isLocalFrameOn_liftedFrameField (n := 2 * m) b).mono
    (show U ⊆ (t b).baseSet from Set.inter_subset_right)
  let e := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
  let G (y : M) : V →L[ℝ] V :=
    (euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm
      ((t b) ((t a).toPartialEquiv.symm (y, 1))).2)).toLinearMap.toContinuousLinearMap
  let Aa := S.liftedLeviCivitaEndomorphism a x X
  let Ab := S.liftedLeviCivitaEndomorphism b x X
  have hsa (y : M) (hy : y ∈ U) (j : Fin (2 * m)) (w : TM y) :
      hs.coeff j y w = inner ℝ (s j y) w := by
    rw [← S.liftedFrameField_coeff (n := 2 * m) a y hy.1 j w]
    have hy' : y ∈ ((S.smoothPrincipalAtlas I).trivialization a).baseSet := hy.1
    simp only [IsLocalFrameOn.coeff, dite_eq_left hy, dite_eq_left hy']
    rfl
  have hrb (y : M) (hy : y ∈ U) (j : Fin (2 * m)) (w : TM y) :
      hr.coeff j y w = inner ℝ (r j y) w := by
    rw [← S.liftedFrameField_coeff (n := 2 * m) b y hy.2 j w]
    have hy' : y ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet := hy.2
    simp only [IsLocalFrameOn.coeff, dite_eq_left hy, dite_eq_left hy']
    rfl
  have hcoordinate (y : M) (hy : y ∈ U) (i j : Fin (2 * m)) :
      hr.coeff j y (s i y) = G y (e i) j := by
    rw [hrb y hy]
    have hframe := S.frame_principal_transition (n := 2 * m) a b y hy.1 hy.2 (e i)
    dsimp only [s, r, liftedFrameField]
    rw [dite_eq_left hy.2, dite_eq_left hy.1, hframe]
    rw [LinearIsometryEquiv.inner_map_map]
    exact EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ _ _
  have hGd : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) G x :=
    ((S.contMDiffOn_principal_vector_transition (n := 2 * m) a b x hx).contMDiffAt
      (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hT (i j : Fin (2 * m)) : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun y ↦ hr.coeff j y (s i y)) x := by
    have h := ((hr.contMDiffAt hU hx j).inner_bundle
      (hs.contMDiffAt hU hx i)).mdifferentiableAt (by simp)
    apply h.congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hrb y hy j (s i y)
  have hderivative (i j : Fin (2 * m)) :
      mvfderiv I (fun y ↦ hr.coeff j y (s i y)) x X =
        mvfderiv I G x X (e i) j := by
    let L : (V →L[ℝ] V) →L[ℝ] ℝ :=
      (EuclideanSpace.proj j).comp (ContinuousLinearMap.apply ℝ V (e i))
    have heq : (fun y ↦ hr.coeff j y (s i y)) =ᶠ[nhds x] (fun y ↦ L (G y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hcoordinate y hy i j
    have hc := mvfderiv_comp («I» := 𝓘(ℝ, V →L[ℝ] V)) (I' := I) x
      L.differentiableAt.mdifferentiableAt hGd
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.fderiv] at hc
    have heqD : mvfderiv I (fun y ↦ hr.coeff j y (s i y)) x =
        mvfderiv I (fun y ↦ L (G y)) x := by
      unfold mvfderiv
      rw [heq.mfderiv_eq]
      rfl
    rw [heqD]
    exact congrArg (fun D ↦ D X) hc
  have hA (d : M) (w : V) (k : Fin (2 * m)) :
      S.liftedLeviCivitaEndomorphism d x X w k =
        ∑ j : Fin (2 * m), S.liftedLeviCivitaCoefficients d x X j k * w j := by
    rfl
  have hAe (d : M) (i k : Fin (2 * m)) :
      S.liftedLeviCivitaEndomorphism d x X (e i) k =
        S.liftedLeviCivitaCoefficients d x X i k := by
    rw [hA]
    simp [e, EuclideanSpace.basisFun_apply, PiLp.single_apply]
  -- The native local-frame formula gives exactly the scalar entries of the gauge law.
  have hentry (i k : Fin (2 * m)) :
      Ab (G x (e i)) k + mvfderiv I G x X (e i) k = G x (Aa (e i)) k := by
    have h := tangentCovariantDerivative_localFrame_gauge
      (CovariantDerivative.leviCivitaConnection I M) s r U hU hs hr x hx hT i k X
    simp only [hsa x hx, hrb x hx] at h
    have hleft (j : Fin (2 * m)) :
        inner ℝ (s j x) (CovariantDerivative.leviCivitaConnection I M (s i) x X) =
          S.liftedLeviCivitaCoefficients a x X i j := by
      exact real_inner_comm _ _
    have hright (j : Fin (2 * m)) :
        inner ℝ (r k x) (CovariantDerivative.leviCivitaConnection I M (r j) x X) =
          S.liftedLeviCivitaCoefficients b x X j k := by
      exact real_inner_comm _ _
    have hGentry (j l : Fin (2 * m)) : inner ℝ (r l x) (s j x) = G x (e j) l :=
      (hrb x hx l (s j x)).symm.trans (hcoordinate x hx j l)
    simp only [hleft, hright, hGentry, hderivative] at h
    have hexpand := congrArg ((EuclideanSpace.proj k : V →L[ℝ] ℝ).comp (G x))
      (e.sum_repr (Aa (e i)))
    simp only [map_sum, map_smul, smul_eq_mul] at hexpand
    change (∑ j, (Aa (e i)) j * G x (e j) k) = G x (Aa (e i)) k at hexpand
    simp only [Aa, hAe] at hexpand
    change (∑ j, S.liftedLeviCivitaCoefficients b x X j k * G x (e i) j) + _ = _
    rw [← hexpand]
    simpa only [mul_comm] using h.symm
  have hop : Ab.comp (G x) + mvfderiv I G x X = (G x).comp Aa := by
    apply ContinuousLinearMap.coe_injective
    apply e.toBasis.ext
    intro i
    apply PiLp.ext
    intro k
    exact hentry i k
  exact congrArg (fun L : V →L[ℝ] V ↦ L v) hop

end TopologicalSpinStructure

end AtiyahSinger
