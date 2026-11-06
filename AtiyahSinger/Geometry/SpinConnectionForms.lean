/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HalfSpinConnectionGauge
public import AtiyahSinger.Geometry.SpinLeviCivitaGauge

/-!
# Smooth compatible half-spin forms from the original Levi-Civita connection

Public module ID: M1449.

The original half-spin bivector applied to the actual lifted Levi-Civita matrix
is a smooth connection form. Its genuine gauge law uses the same principal
transition and the original half-spin representation. The derivative calculation
passes through a base chart only to invoke ordinary finite-dimensional calculus.

Source: the Levi-Civita spin lift, Spin Geometry II.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology realSpinorCliffordNormedAddCommGroup
  realSpinorCliffordNormedSpace exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

set_option maxSynthPendingDepth 50

section Principal

variable {n m : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "V" => EuclideanSpace ℝ (Fin n)

omit [IsManifold I ∞ M] in
private theorem principalSpinTransition_contMDiffAt
    (A : SmoothSpinPrincipalAtlas m I projection) (a b x : M)
    (ha : x ∈ (A.trivialization a).baseSet) (hb : x ∈ (A.trivialization b).baseSet) :
    ContMDiffAt I 𝓘(ℝ, CliffordAlgebra (realSpinorQuadraticForm m)) ∞
      (fun y ↦ ((A.trivialization b)
        ((A.trivialization a).toPartialEquiv.symm (y, 1))).2.val) x := by
  have hs := (A.contMDiffOn_transition a b).contMDiffAt
    (((A.trivialization a).open_baseSet.inter (A.trivialization b).open_baseSet).mem_nhds
      ⟨ha, hb⟩)
  have h := (realSpinorCliffordCoordinates m).symm.toContinuousLinearMap.contDiff.contMDiff
    |>.contMDiffAt.comp x hs
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro y
  exact ((realSpinorCliffordCoordinates m).symm_apply_apply _).symm

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original half-spin transition is differentiable in each actual principal overlap. -/
theorem SmoothSpinPrincipalAtlas.mdifferentiableAt_halfSpinTransition
    (A : SmoothSpinPrincipalAtlas m I projection) (i : ZMod 2) (a b x : M)
    (ha : x ∈ (A.trivialization a).baseSet) (hb : x ∈ (A.trivialization b).baseSet) :
    MDifferentiableAt I 𝓘(ℝ, (CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i))
      (fun y ↦ complexSpinParityContRepresentation m i ((A.trivialization b)
        ((A.trivialization a).toPartialEquiv.symm (y, 1))).2) x := by
  let c := chartAt V x
  let f (z : V) := ((A.trivialization b)
    ((A.trivialization a).toPartialEquiv.symm (c.symm z, 1))).2
  have hc := mdifferentiable_of_mem_atlas («I» := I) (chart_mem_atlas V x)
  have hcx : x ∈ c.source := mem_chart_source V x
  have hi := hc.mdifferentiableAt_symm (c.map_source hcx)
  have hτ : MDifferentiableAt I 𝓘(ℝ, CliffordAlgebra (realSpinorQuadraticForm m))
      (fun y ↦ ((A.trivialization b)
        ((A.trivialization a).toPartialEquiv.symm (y, 1))).2.val) (c.symm (c x)) := by
    rw [c.left_inv hcx]
    exact (principalSpinTransition_contMDiffAt A a b x ha hb).mdifferentiableAt (by simp)
  have hf : DifferentiableAt ℝ (fun z ↦ (f z).val) (c x) :=
    mdifferentiableAt_iff_differentiableAt.mp (hτ.comp (c x) hi)
  have hR := differentiableAt_complexSpinParityContRepresentation m i f (c x) hf
  have hcomp := hR.mdifferentiableAt.comp x (hc.mdifferentiableAt hcx)
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hcx] with y hy
  simp only [Function.comp_apply, f, c.left_inv hy]

end Principal

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

/-- The prescribed quarter-bivector form of the original lifted Levi-Civita matrix. -/
def liftedHalfSpinConnectionForm (S : TopologicalSpinStructure m (TM) o hm hP)
    (i : ZMod 2) (b x : M) : TangentSpace I x →L[ℝ]
      ((CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i)) :=
  (LinearMap.toContinuousLinearMap (show (Fin (2 * m) → Fin (2 * m) → ℝ) →ₗ[ℝ]
    ((CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) →L[ℂ]
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i))
    from halfSpinBivector m i)).comp (S.liftedLeviCivitaCoefficients b x)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual half-spin form is smooth in every original smooth base chart. -/
theorem contDiffOn_liftedHalfSpinConnectionForm
    (S : TopologicalSpinStructure m (TM) o hm hP) (i : ZMod 2)
    (c : OpenPartialHomeomorph M V) (hc : c ∈ atlas V M) (b : M) :
    ContDiffOn ℝ ∞
      (fun z : V ↦ (S.liftedHalfSpinConnectionForm i b (c.symm z)).comp
        (show V →L[ℝ] TangentSpace I (c.symm z) from mfderiv I I c.symm z))
      (c.target ∩ c.symm ⁻¹' ((S.smoothPrincipalAtlas I).trivialization b).baseSet) := by
  let W := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i
  let B : (Fin (2 * m) → Fin (2 * m) → ℝ) →L[ℝ] (W →L[ℂ] W) :=
    (halfSpinBivector m i : (Fin (2 * m) → Fin (2 * m) → ℝ) →ₗ[ℝ]
      (W →L[ℂ] W)).toContinuousLinearMap
  have h := (contDiffOn_const (c := B)).clm_comp (S.contDiffOn_liftedLeviCivitaForm c hc b)
  apply h.congr
  intro z _
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 0 in
-- This compares all native and chart derivatives with both original representation gauges.
/-- The Levi-Civita half-spin forms satisfy the actual original principal gauge law. -/
theorem liftedHalfSpinConnectionForm_gauge
    (S : TopologicalSpinStructure m (TM) o hm hP) (i : ZMod 2) (a b x : M)
    (ha : x ∈ ((S.smoothPrincipalAtlas I).trivialization a).baseSet)
    (hb : x ∈ ((S.smoothPrincipalAtlas I).trivialization b).baseSet)
    (X : TangentSpace I x)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    let A := S.smoothPrincipalAtlas I
    let R := fun y ↦ complexSpinParityContRepresentation m i ((A.trivialization b)
      ((A.trivialization a).toPartialEquiv.symm (y, 1))).2
    S.liftedHalfSpinConnectionForm i b x X (R x s) + mvfderiv I R x X s =
      R x (S.liftedHalfSpinConnectionForm i a x X s) := by
  let A := S.smoothPrincipalAtlas I
  let τ (y : M) := ((A.trivialization b)
    ((A.trivialization a).toPartialEquiv.symm (y, 1))).2
  let G (y : M) : V →L[ℝ] V :=
    (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm (τ y))).toLinearMap.toContinuousLinearMap
  let R (y : M) := complexSpinParityContRepresentation m i (τ y)
  have hτd := (principalSpinTransition_contMDiffAt A a b x ha hb).mdifferentiableAt (by simp)
  have hGd : MDifferentiableAt I 𝓘(ℝ, V →L[ℝ] V) G x :=
    ((S.contMDiffOn_principal_vector_transition (n := 2 * m) a b x ⟨ha, hb⟩).contMDiffAt
      (((A.trivialization a).open_baseSet.inter (A.trivialization b).open_baseSet).mem_nhds
        ⟨ha, hb⟩)).mdifferentiableAt (by simp)
  have hRd := A.mdifferentiableAt_halfSpinTransition i a b x ha hb
  let c := chartAt V x
  have hcx : x ∈ c.source := mem_chart_source V x
  have hc := mdifferentiable_of_mem_atlas («I» := I) (chart_mem_atlas V x)
  have hi := hc.mdifferentiableAt_symm (c.map_source hcx)
  let f (z : V) := τ (c.symm z)
  -- Native derivatives and coordinate derivatives refer to the very same local functions.
  have hlocal {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (k : M → F) (hk : MDifferentiableAt I 𝓘(ℝ, F) k x) :
      DifferentiableAt ℝ (k ∘ c.symm) (c x) := by
    have hk' : MDifferentiableAt I 𝓘(ℝ, F) k (c.symm (c x)) := by
      simpa only [c.left_inv hcx] using hk
    exact mdifferentiableAt_iff_differentiableAt.mp (hk'.comp (c x) hi)
  have hD {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
      (k : M → F) (hk : MDifferentiableAt I 𝓘(ℝ, F) k x) :
      fderiv ℝ (k ∘ c.symm) (c x) (mfderiv I I c x X) = mvfderiv I k x X := by
    have hk' : MDifferentiableAt I 𝓘(ℝ, F) k (c.symm (c x)) := by
      simpa only [c.left_inv hcx] using hk
    have h := mvfderiv_comp («I» := I) (I' := I) (c x) hk' hi
    rw [mvfderiv_eq_fderiv, c.left_inv hcx] at h
    have hv := congrArg (fun L ↦ L (mfderiv I I c x X)) h
    change fderiv ℝ (k ∘ c.symm) (c x) (mfderiv I I c x X) =
      mvfderiv I k x (((mfderiv I I c.symm (c x)).comp (mfderiv I I c x)) X) at hv
    rw [hc.symm_comp_deriv hcx] at hv
    exact hv
  have hf : HasFDerivAt (fun z ↦ (f z).val)
      (fderiv ℝ (fun z ↦ (f z).val) (c x)) (c x) := (hlocal _ hτd).hasFDerivAt
  have hg : HasFDerivAt (fun z ↦ (euclideanSpinVectorRepresentation (2 * m)
      ((euclideanSpinEvenEquiv m).symm (f z))).toLinearMap.toContinuousLinearMap)
      (fderiv ℝ (G ∘ c.symm) (c x)) (c x) := (hlocal G hGd).hasFDerivAt
  have hr : HasFDerivAt (fun z ↦ complexSpinParityContRepresentation m i (f z))
      (fderiv ℝ (R ∘ c.symm) (c x)) (c x) := (hlocal R hRd).hasFDerivAt
  have hgauge := halfSpinBivector_gauge m i f (c x) (mfderiv I I c x X)
    _ _ _ hf hg hr (S.liftedLeviCivitaEndomorphism a x X)
    (S.liftedLeviCivitaEndomorphism b x X)
  have hvector : ∀ v, S.liftedLeviCivitaEndomorphism b x X
      (euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f (c x))) v) +
      fderiv ℝ (G ∘ c.symm) (c x) (mfderiv I I c x X) v =
        euclideanSpinVectorRepresentation (2 * m) ((euclideanSpinEvenEquiv m).symm (f (c x)))
          (S.liftedLeviCivitaEndomorphism a x X v) := by
    intro v
    rw [hD G hGd]
    simp only [f, c.left_inv hcx]
    change S.liftedLeviCivitaEndomorphism b x X (G x v) + mvfderiv I G x X v =
      G x (S.liftedLeviCivitaEndomorphism a x X v)
    exact S.liftedLeviCivitaEndomorphism_gauge a b x ha hb X v
  have hcoeff (d : M) (j k : Fin (2 * m)) :
      inner ℝ (S.liftedLeviCivitaEndomorphism d x X
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j))
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ k) =
          S.liftedLeviCivitaCoefficients d x X j k := by
    rw [EuclideanSpace.inner_basisFun_real]
    change (∑ l : Fin (2 * m), S.liftedLeviCivitaCoefficients d x X l k *
      (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j) l) = _
    simp [EuclideanSpace.basisFun_apply, PiLp.single_apply]
  have h := hgauge hvector s
  simp only [hcoeff, hD R hRd, f, c.left_inv hcx] at h
  exact h

end TopologicalSpinStructure

end AtiyahSinger
