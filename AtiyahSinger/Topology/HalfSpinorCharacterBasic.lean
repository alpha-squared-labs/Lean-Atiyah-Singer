/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinorCharacter
public import AtiyahSinger.Geometry.SpinCliffordSymbol
public import AtiyahSinger.Topology.BundleCohomologyLowRestriction
public import AtiyahSinger.Topology.HermitianMetricPullback
public import AtiyahSinger.Topology.InverseAhat
public import AtiyahSinger.Topology.RationalCohomologyOrientation
public import AtiyahSinger.Topology.SpinCohomologyOrientation
public import AtiyahSinger.Topology.SpinorBundle

/-!
# The original half-spinor character and lower-degree vanishing

Public module ID: M1876.

The half-spinor character is the difference of the degreewise rational Chern
characters of the actual even and odd associated bundles. For a specified
positive-even-rank spin structure, its components below the real rank vanish:
the original Clifford map identifies the two pullbacks off the zero section,
and low-degree Thom restriction detects equality on the original base.

Sources: Spin Geometry III.11, Construction 11.23 and Proposition 11.24, p.238.
The base is arbitrary and the auxiliary Hermitian metrics are supplied explicitly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped TensorProduct

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

universe u v

section AssociatedCharacter

variable (m : ℕ) {B : Type u} {P : Type v}
  [TopologicalSpace B] [TopologicalSpace P]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection)

/-- The degree-2k Chern character of the original even-minus-odd associated spinor bundles. -/
def halfSpinorCharacterComponent
    (hPlus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 0))
    (hMinus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 1))
    (k : ℕ) : singularCohomology ℚ B (2 * k) :=
  letI : ComplexBundle.IsFiniteRank (HalfSpinorBundle m hP 0) :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
      (continuous_complexSpinParityRepresentation m 0)
  letI : ComplexBundle.IsFiniteRank (HalfSpinorBundle m hP 1) :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
      (continuous_complexSpinParityRepresentation m 1)
  ComplexBundle.globalChernCharacterComponent (HalfSpinorBundle m hP 0) hPlus k -
    ComplexBundle.globalChernCharacterComponent (HalfSpinorBundle m hP 1) hMinus k

end AssociatedCharacter

variable {m : ℕ} {B : Type u} {P : Type v} {E : B → Type u}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [TopologicalSpace P]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ x, Orientation ℝ (E x) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original half-spinor difference has no Chern-character component below the real rank. -/
theorem TopologicalSpinStructure.halfSpinorCharacterComponent_eq_zero_of_lt
    (S : TopologicalSpinStructure m E o hm hP)
    (hPlus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 0))
    (hMinus : ComplexBundle.ContinuousHermitianMetric (HalfSpinorBundle m hP 1))
    (k : ℕ) (hk : k < m) :
    halfSpinorCharacterComponent m hP hPlus hMinus k = 0 := by
  classical
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 0)
    (continuous_complexSpinParityRepresentation m 0)
  let := isFiniteRank_associatedVector hP (complexSpinParityContRepresentation m 1)
    (continuous_complexSpinParityRepresentation m 1)
  let V := EuclideanSpace ℝ (Fin (2 * m))
  let A := bundleNonzero (2 * m) E
  let p := bundleProjection (2 * m) E
  let i := ContinuousMap.subtypeVal A
  let f := p.comp i
  let FPlus := HalfSpinorBundle m hP (0 : ZMod 2)
  let FMinus := HalfSpinorBundle m hP (1 : ZMod 2)
  let := isFiniteRank_pullback (E := FPlus) p
  let := isFiniteRank_pullback (E := FMinus) p
  let := isFiniteRank_pullback (E := (p : TotalSpace V E → B) *ᵖ FPlus) i
  let := isFiniteRank_pullback (E := (p : TotalSpace V E → B) *ᵖ FMinus) i
  let := isFiniteRank_pullback (E := FPlus) f
  let := isFiniteRank_pullback (E := FMinus) f
  -- The supplied spin frame lift makes the original parity symbol invertible off zero.
  let c : ComplexBundle.Hom ((p : TotalSpace V E → B) *ᵖ FPlus)
      ((p : TotalSpace V E → B) *ᵖ FMinus) := S.cliffordParityHom 0
  let ce := (c.pullback i).toIso (fun z ↦
    S.cliffordParity_bijective z.val.proj z.val.snd z.property 0)
  let e : ComplexBundle.Iso ((f : A → B) *ᵖ FPlus) ((f : A → B) *ᵖ FMinus) :=
    (pullbackCompIso (E := FPlus) p i).symm.trans
      (ce.trans (pullbackCompIso (E := FMinus) p i))
  -- Compare both characters using one actual pulled-back metric and those same fiber maps.
  let h := hPlus.pullback f
  have hplus := globalChernCharacterComponent_pullback FPlus hPlus f
    ((f : A → B) *ᵖ FPlus) h (ComplexBundle.Iso.refl _) k
  have hminus := globalChernCharacterComponent_pullback FMinus hMinus f
    ((f : A → B) *ᵖ FPlus) h e k
  -- Low-degree restriction is injective by the original relative Thom cochain sequence.
  apply singularCohomologyPullback_nonzeroBundle_injective ℚ (2 * m) E
    S.integralCohomologyOrientation.rationalization (2 * k) (by omega)
  change singularCohomologyPullback ℚ f (2 * k)
    (globalChernCharacterComponent FPlus hPlus k - globalChernCharacterComponent FMinus hMinus k) =
    singularCohomologyPullback ℚ f (2 * k) 0
  rw [map_sub, map_zero]
  exact sub_eq_zero.mpr (hplus.symm.trans hminus)

end AtiyahSinger
