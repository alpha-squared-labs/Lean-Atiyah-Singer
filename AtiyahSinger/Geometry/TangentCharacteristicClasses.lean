/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.TangentMusical
public import AtiyahSinger.Topology.BundleCompactSupportCharacter
public import AtiyahSinger.Topology.PontryaginAhat

/-!
# Characteristic components on the original tangent bundle

Public module ID: M1469.

T02. A supplied smooth tangent metric installs mathlib's native
RiemannianBundle instances, whose fiber topology is definitionally the
original topology. The existing bundle compact-support Chern character
therefore acts on the unchanged tangent total space and original K class.
Its one-point comparison retains that same class, singleton infinity and
original reduced character.

The ordinary A-hat square is the finite degreewise convolution of the
existing A-hat components of the original tangent bundle. Its auxiliary
Hermitian metric lives on the genuine tensor complexification with the
already specified real/imaginary topology. The supplied metric is explicit;
it is not a replacement tangent norm or total-space topology. Existence
follows from the existing finite-rank complexification and metric-existence
results on a compact Hausdorff base. The square is independent of this
auxiliary choice and is the original complexification's Todd component.

Sources: SG III.11, Proposition 11.14, and III.13, the first Theorem 13.8,
equation (13.18), pp.254--255. The unoriented rational Todd identity uses
PontryaginAhat's already recorded extension of SG's oriented proof. The
original real manifold need not be oriented. The total tangent manifold's
canonical interleaved orientation and its LF fundamental class are separate
constructions. No index map or numerical index equality is defined here.

The base and Euclidean fibers are in Type, matching the universe convention
of the existing native bundle compact-support character. This is a technical
choice of universe, not a dimension, connectedness or positivity condition.
The one-point, metric and Todd-square comparisons retain the exact native inputs.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped Bundle Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 25

attribute [local instance] t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

variable {n : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "TM" => TangentBundle 𝓘(ℝ, V) M
local notation "T" => (TangentSpace 𝓘(ℝ, V) : M → Type)

namespace SmoothTangentMetric

/-- The original supported character on TM, with the supplied metric's native fiber instances. -/
def tangentCompactSupportChernCharacterComponent
    (g : SmoothTangentMetric (n := n) (M := M)) (k : ℕ) :
    CompactSupportKZero TM →+ compactSupportCohomology ℚ TM (2 * k) := by
  -- The native mechanism retains the original fiber topology and vector operations.
  letI : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  -- State the continuity certificate explicitly for these same induced inner products.
  letI : IsContinuousRiemannianBundle V T :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  exact bundleCompactSupportChernCharacterComponent n T k

/-- The tangent character maps to the reduced character of exactly its original supported class. -/
theorem tangentCompactSupportChernCharacterComponent_toOnePoint
    (g : SmoothTangentMetric (n := n) (M := M)) (k : ℕ) (a : CompactSupportKZero TM) :
    compactSupportCohomologyToOnePoint ℚ TM (2 * k)
        (g.tangentCompactSupportChernCharacterComponent k a) =
      reducedChernCharacterComponent (OnePoint.infty : OnePoint TM) k a := by
  /- Stage 1: install the same native RiemannianBundle certificate from
  g.toRiemannianMetric as in the character definition. This preserves
  the original tangent topology and all vector operations.
  Stage 2: apply bundleCompactSupportChernCharacterComponent_toOnePoint
  at n, the unchanged tangent family T, k and the original class a.
  It cancels the inverse of the specified one-point comparison, giving
  exactly the displayed reduced character, without replacing the symbol. -/
  let : RiemannianBundle T := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V T :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  exact bundleCompactSupportChernCharacterComponent_toOnePoint n T k a

end SmoothTangentMetric

/-- The degree-2k component of the square of the original tangent bundle's A-hat class. -/
def tangentAHatSquareComponent
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x)) (k : ℕ) :
    singularCohomology ℚ M (2 * k) := by
  letI := RealBundle.isFiniteRank_of_vectorBundle V T
  -- Use the original ordinary cup and only the canonical equality of total degrees.
  exact ∑ i : Fin (k + 1),
    (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
        singularCohomology ℚ M (2 * (i.val + (k - i.val))) ≅
          singularCohomology ℚ M (2 * k)).hom
      (singularCohomologyEvenCup ℚ M i.val (k - i.val)
        (RealBundle.aHatEvenComponent V T hV i.val)
        (RealBundle.aHatEvenComponent V T hV (k - i.val)))

-- Retain the original compact Hausdorff hypotheses in the public type.
set_option linter.unusedSectionVars false in
/-- Changing the auxiliary Hermitian metric does not change the original tangent A-hat square. -/
theorem tangentAHatSquareComponent_metric_independent
    (hV hV' : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x)) (k : ℕ) :
    tangentAHatSquareComponent (n := n) hV k =
      tangentAHatSquareComponent (n := n) hV' k := by
  /- Stage 1: retain the original native finite-rank certificate and
  expand the degree-k finite convolution defining both squares.
  Stage 2: in each summand, use the aHatEvenComponent equality in
  RealBundle.pontryagin_aHat_metric_independent for i and k-i, with
  the same tangent family and original complexification topology.
  The ordinary cup and canonical degree transport are unchanged,
  so equality of these summands gives equality of the finite sums. -/
  let := RealBundle.isFiniteRank_of_vectorBundle V T
  unfold tangentAHatSquareComponent
  apply Finset.sum_congr rfl
  intro i _
  rw [(RealBundle.pontryagin_aHat_metric_independent V T hV hV' i.val).2.2,
    (RealBundle.pontryagin_aHat_metric_independent V T hV hV' (k - i.val)).2.2]

-- Retain the original compact Hausdorff hypotheses in the public type.
set_option linter.unusedSectionVars false in
/-- The square equals the existing Todd component of the genuine tensor complexification. -/
theorem tangentAHatSquareComponent_eq_todd
    (hV : letI := complexificationTopology V T
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x)) (k : ℕ) :
    letI := RealBundle.isFiniteRank_of_vectorBundle V T
    letI := complexificationTopology V T
    letI := RealBundle.isFiniteRank_complexification V T
    tangentAHatSquareComponent (n := n) hV k =
      toddClassComponent (fun x : M ↦ ℂ ⊗[ℝ] TangentSpace 𝓘(ℝ, V) x) hV k := by
  /- Stage 1: use the original native tangent finite-rank certificate
  and its actual tensor complexification certificate, with hV unchanged.
  Stage 2: apply RealBundle.todd_complexification_eq_aHat_sq to V, T,
  hV and k. Its finite convolution is exactly tangentAHatSquareComponent;
  reverse that equality. The existing rational argument permits an
  unoriented tangent bundle and does not introduce a splitting premise. -/
  let := RealBundle.isFiniteRank_of_vectorBundle V T
  exact (RealBundle.todd_complexification_eq_aHat_sq V T hV k).symm

end AtiyahSinger
