/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ZeroRankBundle
public import AtiyahSinger.Topology.SpinorBundle

/-!
# Clifford multiplication in the native rank-zero spin model

Public module ID: M1518.

SC01. Every vector of the original zero-rank real bundle is zero. Clifford
multiplication is consequently the zero linear map on the original full
and half-spin associated fibers. These are the same quotient fibers and
representations used in positive rank, specialized at m=0. Their pullbacks
retain the original topology, and the parity map is an actual continuous Hom.

The vector-bundle hypotheses are explicit on both fiber maps, even though
their values are zero. Continuity is assembled from the original finite
pullback charts, the base projection and the zero section. The full-spin
and parity fiber maps are defined directly as zero linear maps.

Sources: Lawson--Michelsohn, Spin Geometry, I.2 Definition 2.3 and
(2.24)--(2.25), and the symbol construction III.12 (12.13). At rank zero
the unit-generated spin group has only the empty product. This degenerate
extension does not assert a two-sheeted frame lift or identify it with a
different stabilized rank-zero spin convention. No positive-half bundle
trivialization, spin connection or Dirac operator is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

variable {B P : Type*} [TopologicalSpace B] [TopologicalSpace P]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

/-- Clifford multiplication on the original full-spin fiber in real rank zero. -/
def zeroSpinClifford [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
    (b : B) (_v : E b) : Module.End ℂ (SpinorBundle 0 hP b) :=
  0

/-- The zero-vector Clifford map between the original associated parity fibers. -/
def zeroSpinCliffordParity [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
    (b : B) (_v : E b) (i : ZMod 2) :
    HalfSpinorBundle 0 hP i b →ₗ[ℂ] HalfSpinorBundle 0 hP (i + 1) b :=
  0

variable [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]

/-- The actual rank-zero Clifford Hom on the original half-spin pullbacks. -/
def zeroSpinCliffordParityHom (i : ZMod 2) :
    Hom ((π (EuclideanSpace ℝ (Fin 0)) E) *ᵖ (HalfSpinorBundle 0 hP i))
      ((π (EuclideanSpace ℝ (Fin 0)) E) *ᵖ (HalfSpinorBundle 0 hP (i + 1))) where
  linearMap z := zeroSpinCliffordParity E hP z.proj z.snd i
  continuous_total := by
    -- Use the original associated finite bundle structures, then their actual pullbacks.
    let : IsFiniteRank (HalfSpinorBundle 0 hP i) :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 i)
        (continuous_complexSpinParityRepresentation 0 i)
    let : IsFiniteRank (HalfSpinorBundle 0 hP (i + 1)) :=
      isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 (i + 1))
        (continuous_complexSpinParityRepresentation 0 (i + 1))
    let p : C(TotalSpace (EuclideanSpace ℝ (Fin 0)) E, B) :=
      ⟨π (EuclideanSpace ℝ (Fin 0)) E,
        FiberBundle.continuous_proj (EuclideanSpace ℝ (Fin 0)) E⟩
    let : IsFiniteRank ((p : TotalSpace (EuclideanSpace ℝ (Fin 0)) E → B) *ᵖ
        (HalfSpinorBundle 0 hP i)) := isFiniteRank_pullback p
    let : IsFiniteRank ((p : TotalSpace (EuclideanSpace ℝ (Fin 0)) E → B) *ᵖ
        (HalfSpinorBundle 0 hP (i + 1))) := isFiniteRank_pullback p
    -- The total map is the target zero section composed with the source projection.
    exact (ComplexBundle.continuous_zero_section
      ((π (EuclideanSpace ℝ (Fin 0)) E) *ᵖ (HalfSpinorBundle 0 hP (i + 1)))).comp
        (ComplexBundle.continuous_proj (E :=
          (π (EuclideanSpace ℝ (Fin 0)) E) *ᵖ (HalfSpinorBundle 0 hP i)))

end AtiyahSinger
