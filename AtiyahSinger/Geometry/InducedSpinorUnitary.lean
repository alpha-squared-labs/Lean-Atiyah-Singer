/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.InducedSpinorCompatibility
public import AtiyahSinger.Geometry.SpinConnectionForms

/-!
# Unitarity of the original Levi-Civita half-spin formula

Public module ID: M1282.

The original Fock pairing becomes the fixed Hermitian pairing in the same exterior
coordinates. The native product rule and skewness of the actual lifted Levi-Civita
matrix show that the prescribed derivative-plus-bivector formula preserves this
metric on the original associated fibers.

Source: Spin Geometry II.4, the unitary spin lift of a metric connection.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff ComplexConjugate

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

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

namespace TopologicalSpinStructure

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 1000000 in
-- The local proof compares the original quotient metric and both native section derivatives.
/-- The prescribed Levi-Civita half-spin coordinate formula preserves the original Fock metric. -/
theorem isUnitary_of_halfSpinorConnection_coordinates
    (S : TopologicalSpinStructure m (TM) o hm hP) (i : ZMod 2)
    (cov : AtlasComplexConnection
      (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i))
    (hcov : ∀ (b x : M)
      (hx : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
      (u : (halfSpinorBundleSmoothAtlas m hP (S.smoothPrincipalAtlas I) i).smoothSections)
      (X : TangentSpace I x),
      let A := S.smoothPrincipalAtlas I
      let E := associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m i)
        ((A.trivialization b).toPartialEquiv.symm (x, 1))
        ((A.trivialization b).proj_symm_apply' hx)
      let q := associatedSpinSectionCoordinates hP (complexSpinParityContRepresentation m i)
        A b u.val
      E.symm (cov.covariantDerivative u x X) =
        mvfderiv I q x X + S.liftedHalfSpinConnectionForm i b x X (q x)) :
    cov.IsUnitary (halfSpinorHermitianMetric m hP (S.smoothPrincipalAtlas I) i) := by
  classical
  let A := S.smoothPrincipalAtlas I
  let H := halfSpinorBundleSmoothAtlas m hP A i
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let ρ := complexSpinParityContRepresentation m i
  let metric := halfSpinorHermitianMetric m hP A i
  let : FiniteDimensional ℝ W := FiniteDimensional.trans ℝ ℂ W
  -- Express the original Fock form as one fixed real bilinear continuous map.
  let c := (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra.equivFun
  let J : W →L[ℂ] EuclideanSpace ℂ (Finset (Fin m)) :=
    (EuclideanSpace.equiv (Finset (Fin m)) ℂ).symm.toContinuousLinearMap.comp
      (c.toContinuousLinearMap.comp W.subtypeL)
  have hQ (s t : W) : spinorFockPairing m s.val t.val = inner ℂ (J s) (J t) := by
    simp [spinorFockPairing, J, c, PiLp.inner_apply, mul_comm]
  let Jr := J.restrictScalars ℝ
  let B : W →ₗ[ℝ] W →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun s t ↦ inner ℂ (Jr s) (Jr t))
    (by intro s t u; simp only [map_add, inner_add_left])
    (by
      intro a s t
      rw [map_smul]
      change inner ℂ ((a : ℂ) • Jr s) (Jr t) = _
      exact inner_smul_real_left (𝕜 := ℂ) (Jr s) (Jr t) a)
    (by intro s t u; simp only [map_add, inner_add_right])
    (by
      intro a s t
      rw [map_smul]
      change inner ℂ (Jr s) ((a : ℂ) • Jr t) = _
      exact inner_smul_real_right (𝕜 := ℂ) (Jr s) (Jr t) a)
  let L : W →L[ℝ] W →L[ℝ] ℂ :=
    (LinearMap.toContinuousLinearMap.toLinearMap.comp B).toContinuousLinearMap
  have hL (s t : W) : L s t = spinorFockPairing m s.val t.val := (hQ s t).symm
  intro u v x X
  let E (y : M) (hy : y ∈ (A.trivialization x).baseSet) :
      W ≃ₗ[ℂ] HalfSpinorBundle m hP i y :=
    associatedVectorFiberMkLinearEquiv hP ρ
      ((A.trivialization x).toPartialEquiv.symm (y, 1))
      ((A.trivialization x).proj_symm_apply' hy)
  let q := associatedSpinSectionCoordinates hP ρ A x u.val
  let r := associatedSpinSectionCoordinates hP ρ A x v.val
  have hx := A.mem_baseSet x
  have hpair (y : M) (hy : y ∈ (A.trivialization x).baseSet)
      (s t : HalfSpinorBundle m hP i y) :
      (metric.toCore y).inner s t = L ((E y hy).symm s) ((E y hy).symm t) := by
    rw [hL]
    have h := (halfSpinorHermitianMetric_properties m hP A i).2
      ((A.trivialization x).toPartialEquiv.symm (y, 1)) y
      ((A.trivialization x).proj_symm_apply' hy) ((E y hy).symm s) ((E y hy).symm t)
    change (metric.toCore y).inner (E y hy ((E y hy).symm s))
      (E y hy ((E y hy).symm t)) = _ at h
    simpa only [LinearEquiv.apply_symm_apply] using h
  have hq : MDifferentiableAt I 𝓘(ℝ, W) q x :=
    ((contMDiffOn_associatedSpinSectionCoordinates hP ρ A H
      ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i) x u).contMDiffAt
        ((A.trivialization x).open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  have hr : MDifferentiableAt I 𝓘(ℝ, W) r x :=
    ((contMDiffOn_associatedSpinSectionCoordinates hP ρ A H
      ((spinorBundleSmoothAtlases_compatibility m hP A).2.1 i) x v).contMDiffAt
        ((A.trivialization x).open_baseSet.mem_nhds hx)).mdifferentiableAt (by simp)
  -- Differentiate the actual fiber pairing through these same smooth representatives.
  have heq : (fun y ↦ (metric.toCore y).inner (u.val y) (v.val y)) =ᶠ[nhds x]
      (fun y ↦ L (q y) (r y)) := by
    filter_upwards [(A.trivialization x).open_baseSet.mem_nhds hx] with y hy
    rw [hpair y hy]
    simp only [q, r, associatedSpinSectionCoordinates, dite_eq_left hy]
    rfl
  have hder : mfderiv I 𝓘(ℝ, ℂ)
      (fun y ↦ (metric.toCore y).inner (u.val y) (v.val y)) x X =
        L (q x) (mvfderiv I r x X) + L (mvfderiv I q x X) (r x) := by
    rw [heq.mfderiv_eq]
    exact mvfderiv_bilinear L q r x hq hr X
  have hux : (E x hx).symm (u.val x) = q x := by
    simp only [q, associatedSpinSectionCoordinates, dite_eq_left hx]
    rfl
  have hvx : (E x hx).symm (v.val x) = r x := by
    simp only [r, associatedSpinSectionCoordinates, dite_eq_left hx]
    rfl
  have hcu : (E x hx).symm (cov.covariantDerivative u x X) =
      mvfderiv I q x X + halfSpinBivector m i (S.liftedLeviCivitaCoefficients x x X)
        (q x) := hcov x x hx u X
  have hcv : (E x hx).symm (cov.covariantDerivative v x X) =
      mvfderiv I r x X + halfSpinBivector m i (S.liftedLeviCivitaCoefficients x x X)
        (r x) := hcov x x hx v X
  -- The two connection-form terms cancel by the original skew Fock identity.
  have hskew : L (halfSpinBivector m i (S.liftedLeviCivitaCoefficients x x X) (q x))
      (r x) = -L (q x)
        (halfSpinBivector m i (S.liftedLeviCivitaCoefficients x x X) (r x)) := by
    simp only [hL]
    exact spinorFockPairing_halfSpinBivector m i _
      (S.liftedLeviCivitaCoefficients_skew x x hx X) (q x) (r x)
  have hright :
      (metric.toCore x).inner (cov.covariantDerivative u x X) (v.val x) +
        (metric.toCore x).inner (u.val x) (cov.covariantDerivative v x X) =
          L (q x) (mvfderiv I r x X) + L (mvfderiv I q x X) (r x) := by
    rw [hpair x hx (cov.covariantDerivative u x X) (v.val x),
      hpair x hx (u.val x) (cov.covariantDerivative v x X)]
    rw [hux, hvx, hcu, hcv]
    simp only [map_add, add_apply, hskew]
    abel
  exact hder.trans hright.symm

end TopologicalSpinStructure

end AtiyahSinger
