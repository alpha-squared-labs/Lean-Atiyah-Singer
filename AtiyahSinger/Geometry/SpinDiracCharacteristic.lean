/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.BaseCohomologicalIndexTheorem
public import AtiyahSinger.Geometry.SpinTangentOrientation
public import AtiyahSinger.Topology.SpinThomCharacter
public import AtiyahSinger.Topology.ZeroSpinThomCharacter

/-!
# The original spin Dirac characteristic class on the base

Public module ID: M1451.

The finite top-degree component of ch(u) cup A-hat(TM) uses the existing
K-zero Chern character, original tangent bundle and its genuine tensor
complexification. For an actual coefficient bundle it is the convolution
of that bundle's original global Chern character with the same A-hat class.
Ranks may vary on different components and may be zero.

The original spin frame lift determines the base homological orientation.
Its induced tangent-fiber orientation is exactly the one in S04. Both
fiber-integration maps invert the same ordered Thom map pi*(-) cup U,
so their comparison introduces no freely chosen orientation or scalar.
The original spin symbol's character contributes (-1)^m inverse A-hat.
Multiplying by the existing A-hat square leaves (-1)^m ch(u) cup A-hat.
This includes odd m; no restriction to dimensions divisible by four is used.

Sources: Lawson--Michelsohn, Spin Geometry, III.12.5 and III.13.10,
pp.242--243 and 256--257. The explicit singular-model comparisons and
native rank-zero endpoint are project supplements. The zero endpoint uses
the original vacuum-normalized spin Thom class and the positive point
orientation; its source-minus-target class is not replaced by a rank count.
The tangent integration comparisons preserve the original normalized Thom maps.
The positive-rank identity uses the original supported spin Thom character;
the vacuum-normalized endpoint treats rank zero separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory ComplexBundle
open scoped Manifold ContDiff TensorProduct

set_option maxSynthPendingDepth 40

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

section CharacteristicClass

variable {m : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "V" => EuclideanSpace ℝ (Fin (2 * m))
local notation "TM" => (TangentSpace 𝓘(ℝ, V) : M → Type)

/-- The degree-2m component of the original ch(u) cup A-hat(TM). -/
def spinDiracCharacteristicClass
    (hV : letI := complexificationTopology V TM
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x))
    (u : ComplexKZero M) : singularCohomology ℚ M (2 * m) := by
  letI := RealBundle.isFiniteRank_of_vectorBundle V TM
  exact ∑ i : Fin (m + 1),
    (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
        singularCohomology ℚ M (2 * (i.val + (m - i.val))) ≅
          singularCohomology ℚ M (2 * m)).hom
      (singularCohomologyEvenCup ℚ M i.val (m - i.val)
        (chernCharacterKZeroComponent M i.val u)
        (RealBundle.aHatEvenComponent V TM hV (m - i.val)))

/-- On an original bundle class, the characteristic factor retains its actual global character. -/
theorem spinDiracCharacteristicClass_bundle
    (hV : letI := complexificationTopology V TM
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x))
    (W : M → Type*) [∀ x, AddCommGroup (W x)] [∀ x, Module ℂ (W x)]
    [TopologicalSpace (TotalSpace Unit W)] [ComplexBundle.IsFiniteRank W]
    (c : ContinuousHermitianMetric W) :
    letI := RealBundle.isFiniteRank_of_vectorBundle V TM
    spinDiracCharacteristicClass hV (ComplexBundle.kZeroClass W) =
      ∑ i : Fin (m + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ M (2 * (i.val + (m - i.val))) ≅
              singularCohomology ℚ M (2 * m)).hom
          (singularCohomologyEvenCup ℚ M i.val (m - i.val)
            (globalChernCharacterComponent W c i.val)
            (RealBundle.aHatEvenComponent V TM hV (m - i.val))) := by
  /- Expand only the standard finite top-degree convolution. In each term
  chernCharacterKZeroComponent_bundle identifies the original K class's
  character with globalChernCharacterComponent of the same W and c.
  The original tangent complexification, hV, cup order and degree transports
  are unchanged. The global character handles locally varying finite rank;
  no replacement by a rank function or a new coefficient bundle occurs. -/
  let := RealBundle.isFiniteRank_of_vectorBundle V TM
  unfold spinDiracCharacteristicClass
  apply Finset.sum_congr rfl
  intro i _
  rw [chernCharacterKZeroComponent_bundle W c]

end CharacteristicClass

section Spin

variable {m : ℕ} {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 * m))) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → M}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}
  {hm : 0 < m}
  {o : ∀ x : M,
    Orientation ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin (2 * m))) x) (Fin (2 * m))}
  (g : SmoothTangentMetric (n := 2 * m) (M := M))

local notation "V" => EuclideanSpace ℝ (Fin (2 * m))
local notation "TM" => (TangentSpace 𝓘(ℝ, V) : M → Type)

-- Retain the original second-countability hypothesis in the public type.
set_option linter.unusedSectionVars false in
/-- Both original tangent integration maps invert the same spin-normalized ordered Thom map. -/
theorem TopologicalSpinStructure.tangentCohomologyFiberIntegral_eq :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    ∀ (S : TopologicalSpinStructure m TM o hm hP) (p : ℕ),
      tangentCohomologyFiberIntegral g (S.homologicalOrientation g) p =
        compactSupportCohomologyFiberIntegral ℚ (2 * m) TM
          S.integralCohomologyOrientation.rationalization p := by
  /- Stage 1: tangentCohomologyOrientation_eq identifies the two normalized
  integral fiber orientations; apply the actual rationalization functor.
  Stage 2: compactSupportCohomologyThomMap_compact identifies the forward
  tangent Thom map, including the original compact-base comparison, with
  the original cohomologyZeroSectionPushforward. This is exactly the map
  used in compactBaseCohomologyThomEquiv, with pi*(a) to the left of U.
  Stage 3: two linear equivalences with that same forward map have the
  same inverse. Their inverse linear maps are precisely the two displayed
  integrals. No orientation sign, proper bundle projection or scalar
  normalization is assumed, and the maps agree in every degree p. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S p
  have hforward : tangentCohomologyThomEquiv g (S.homologicalOrientation g) p =
      compactBaseCohomologyThomEquiv ℚ (2 * m) TM
        S.integralCohomologyOrientation.rationalization p := by
    apply LinearEquiv.ext
    intro a
    change compactSupportCohomologyThomMap ℚ (2 * m) TM
      (tangentCohomologyOrientation g (S.homologicalOrientation g)).rationalization p
      ((compactSupportCohomologyIso ℚ M p).inv a) = _
    rw [S.tangentCohomologyOrientation_eq g, compactSupportCohomologyThomMap_compact]
    exact congrArg (cohomologyZeroSectionPushforward ℚ (2 * m) TM
      S.integralCohomologyOrientation.rationalization p)
        (congrArg (fun f ↦ f a) (compactSupportCohomologyIso ℚ M p).inv_hom_id)
  exact congrArg (fun e ↦ e.symm.toLinearMap) hforward

set_option maxHeartbeats 800000 in
-- Retain the explicit dependent cup transports throughout the original top-degree convolution.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original base-index class of a spin Thom coefficient is the signed Dirac characteristic. -/
theorem TopologicalSpinStructure.baseIndexCharacteristicClass_spinThom
    (hV : letI := complexificationTopology V TM
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x))
    (u : ComplexKZero M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    ∀ S : TopologicalSpinStructure m TM o hm hP,
      baseIndexCharacteristicClass (S.homologicalOrientation g) g hV (S.spinThomHom u) =
        (-1 : ℚ) ^ m • spinDiracCharacteristicClass hV u := by
  /- Stage 1: expand baseIndexCharacteristicClass in dimension 2*m.
  Every retained index k is at most m, so its supported character degree
  is 2*(2*m-k) = 2*(m+(m-k)), and its integrated degree is 2*(m-k).
  No character component below the Thom rank is manufactured by truncated
  natural subtraction. The supplied g installs exactly the native metrics
  used in its tangentCompactSupportChernCharacterComponent.
  Stage 2: tangentCohomologyFiberIntegral_eq identifies the original
  tangent integral with the same spin-oriented integral in S04. Apply
  fiberIntegral_chernCharacter_spinThom with j=m-k to the original u,
  original tangent complexification and this exact hV. Each term is
  (-1)^m times the finite convolution ch(u) cup inverse A-hat.
  Stage 3: expand tangentAHatSquareComponent. Reassociate the finite cup
  sums and reindex their nonnegative indices with total m. All degrees
  involved are even, so these rearrangements have no graded sign.
  The existing aHatEvenComponent_mul_inverse cancels one A-hat factor
  against its actual inverse characteristic series, leaving precisely
  ch(u) cup A-hat. This is cancellation of a unit formal series, never
  cancellation of the Euler class on M or division by a possibly zero class.
  Stage 4: collect the fixed (-1)^m and the canonical degree transports.
  This is the displayed spinDiracCharacteristicClass, including odd m;
  individual A-hat components vanish in degrees 2 modulo 4 but the
  coefficient ch(u) can contribute those degrees. No m-even hypothesis,
  connectedness, constant coefficient rank or desired numerical index
  equality is used. The subsequent T03 index sign cancels separately. -/
  classical
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  intro S
  let := RealBundle.isFiniteRank_of_vectorBundle V TM
  let R := SingularEvenCohomology ℚ M
  let ι := singularEvenCohomologyOf ℚ M
  let series (a : ∀ j, singularCohomology ℚ M (2 * j)) : PowerSeries R :=
    PowerSeries.mk (fun j ↦ ι j (a j))
  let A := series (RealBundle.aHatEvenComponent V TM hV)
  let I := series (RealBundle.inverseAHatEvenComponent V TM hV)
  let C := series (fun j ↦ chernCharacterKZeroComponent M j u)
  have hcoeff (a b : PowerSeries R) (k : ℕ) :
      PowerSeries.coeff k (a * b) =
        ∑ i : Fin (k + 1), PowerSeries.coeff i.val a * PowerSeries.coeff (k - i.val) b := by
    rw [PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j ↦ PowerSeries.coeff i a * PowerSeries.coeff j b) k,
      Fin.sum_univ_eq_sum_range
        (fun i ↦ PowerSeries.coeff i a * PowerSeries.coeff (k - i) b) (k + 1)]
  -- Include homogeneous classes into the actual even cup ring, retaining every degree transport.
  have hcup (p q k : ℕ) (h : p + q = k)
      (a : singularCohomology ℚ M (2 * p)) (b : singularCohomology ℚ M (2 * q)) :
      ι k ((eqToIso (by congr 1; omega) :
        singularCohomology ℚ M (2 * p + 2 * q) ≅ singularCohomology ℚ M (2 * k)).hom
          (singularCohomologyCup ℚ M (2 * p) (2 * q) a b)) = ι p a * ι q b := by
    subst k
    exact singularEvenCohomologyOf_cup ℚ M p q a b
  have hconv (a b : ∀ j, singularCohomology ℚ M (2 * j)) (k : ℕ) :
      ι k (∑ i : Fin (k + 1),
        (eqToIso (by congr 1; omega) :
          singularCohomology ℚ M (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ M (2 * k)).hom
          (singularCohomologyEvenCup ℚ M i.val (k - i.val) (a i.val) (b (k - i.val)))) =
        PowerSeries.coeff k (series a * series b) := by
    rw [map_sum, hcoeff]
    apply Finset.sum_congr rfl
    intro i _
    change singularEvenCohomologyOf ℚ M k _ = _
    rw [singularEvenCohomologyOf_eqToIso ℚ M (by omega), singularEvenCohomologyOf_cup]
    simp only [series, PowerSeries.coeff_mk, ι]
  -- The constructed inverse A-hat is a unit inverse in this same cohomology ring.
  have hAI : A * I = 1 := by
    apply PowerSeries.ext
    intro k
    change PowerSeries.coeff k
      (series (RealBundle.aHatEvenComponent V TM hV) *
        series (RealBundle.inverseAHatEvenComponent V TM hV)) = _
    rw [← hconv (RealBundle.aHatEvenComponent V TM hV)
      (RealBundle.inverseAHatEvenComponent V TM hV) k,
      RealBundle.aHatEvenComponent_mul_inverse V TM hV]
    change singularEvenCohomologyOf ℚ M k _ = _
    rw [singularEvenCohomologyOf_degreeTwoPow, map_zero]
    cases k <;> simp
  have hA2 (k : ℕ) : ι k (tangentAHatSquareComponent hV k) =
      PowerSeries.coeff k (A * A) :=
    hconv (RealBundle.aHatEvenComponent V TM hV) (RealBundle.aHatEvenComponent V TM hV) k
  have htarget : ι m (spinDiracCharacteristicClass hV u) =
      PowerSeries.coeff m (C * A) :=
    hconv (fun j ↦ chernCharacterKZeroComponent M j u) (RealBundle.aHatEvenComponent V TM hV) m
  let D (j : ℕ) := compactSupportCohomologyFiberIntegral ℚ (2 * m) TM
    S.integralCohomologyOrientation.rationalization (2 * j)
      ((eqToIso (by congr 1; omega) :
        compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M) (2 * (m + j)) ≅
          compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M) (2 * j + 2 * m)).hom
        (bundleCompactSupportChernCharacterComponent (2 * m) TM (m + j) (S.spinThomHom u)))
  have hD (j : ℕ) : ι j (D j) = (-1 : ℚ) ^ m • PowerSeries.coeff j (C * I) := by
    change ι j (compactSupportCohomologyFiberIntegral ℚ (2 * m) TM
      S.integralCohomologyOrientation.rationalization (2 * j) _) = _
    rw [S.fiberIntegral_chernCharacter_spinThom hV u j, map_smul,
      hconv (fun k ↦ chernCharacterKZeroComponent M k u)
        (RealBundle.inverseAHatEvenComponent V TM hV) j]
  have hdegree (r k p j : ℕ) (hp : p = 2 * r) (hj : j = m + r)
      (ht : p + 2 * k = 2 * m) (hc : 2 * j = p + 2 * m) :
      ι m ((eqToIso (congrArg (singularCohomology ℚ M) ht)).hom
        (singularCohomologyCup ℚ M p (2 * k)
          (tangentCohomologyFiberIntegral g (S.homologicalOrientation g) p
            ((eqToIso (congrArg
              (compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M)) hc)).hom
                (g.tangentCompactSupportChernCharacterComponent j (S.spinThomHom u))))
          (tangentAHatSquareComponent hV k))) =
        ι r (D r) * ι k (tangentAHatSquareComponent hV k) := by
    subst p
    subst j
    rw [hcup r k m (by omega), S.tangentCohomologyFiberIntegral_eq g]
    rfl
  -- Every retained original index has precisely the shifted supported degree used in S04.
  apply singularEvenCohomologyOf_injective ℚ M m
  change ι m (baseIndexCharacteristicClass (S.homologicalOrientation g) g hV
    (S.spinThomHom u)) = ι m ((-1 : ℚ) ^ m • spinDiracCharacteristicClass hV u)
  rw [map_smul, htarget]
  unfold baseIndexCharacteristicClass
  rw [map_sum]
  have hterm (k : ℕ) (hk : k ≤ m)
      (ht : (2 * m - 2 * k) + 2 * k = 2 * m)
      (hc : 2 * (2 * m - k) = (2 * m - 2 * k) + 2 * m) :
      ι m ((eqToIso (congrArg (singularCohomology ℚ M)
          ht) :
        singularCohomology ℚ M ((2 * m - 2 * k) + 2 * k) ≅
          singularCohomology ℚ M (2 * m)).hom
        (singularCohomologyCup ℚ M (2 * m - 2 * k) (2 * k)
          (tangentCohomologyFiberIntegral g (S.homologicalOrientation g) (2 * m - 2 * k)
            ((eqToIso (congrArg
                (compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M))
                  hc) :
              compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M) (2 * (2 * m - k)) ≅
                compactSupportCohomology ℚ (TangentBundle 𝓘(ℝ, V) M)
                  ((2 * m - 2 * k) + 2 * m)).hom
              (g.tangentCompactSupportChernCharacterComponent (2 * m - k)
                (S.spinThomHom u))))
          (tangentAHatSquareComponent hV k))) =
        (-1 : ℚ) ^ m •
          (PowerSeries.coeff k (A * A) * PowerSeries.coeff (m - k) (C * I)) := by
    calc
      _ = ι (m - k) (D (m - k)) * ι k (tangentAHatSquareComponent hV k) :=
        hdegree (m - k) k (2 * m - 2 * k) (2 * m - k)
          (by omega) (by omega) (by omega) (by omega)
      _ = _ := by rw [hD, hA2, smul_mul_assoc, mul_comm]
  trans ∑ k : Fin (2 * m / 2 + 1), (-1 : ℚ) ^ m •
    (PowerSeries.coeff k.val (A * A) * PowerSeries.coeff (m - k.val) (C * I))
  · apply Finset.sum_congr rfl
    intro k _
    exact hterm k.val (by omega) (by omega) (by omega)
  rw [← Finset.smul_sum,
    Fin.sum_univ_eq_sum_range
      (fun k ↦ PowerSeries.coeff k (A * A) * PowerSeries.coeff (m - k) (C * I))
        (2 * m / 2 + 1),
    show 2 * m / 2 + 1 = m + 1 by omega,
    ← Fin.sum_univ_eq_sum_range
      (fun k ↦ PowerSeries.coeff k (A * A) * PowerSeries.coeff (m - k) (C * I)) (m + 1),
    ← hcoeff (A * A) (C * I) m]
  -- One genuine unit-series cancellation leaves the original ch(u) cup A-hat coefficient.
  have hseries : (A * A) * (C * I) = C * A := by
    calc
      (A * A) * (C * I) = (C * A) * (A * I) := by ring
      _ = C * A := by rw [hAI, mul_one]
  rw [hseries]

end Spin

section Zero

variable {M P : Type} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → M}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)
  (g : SmoothTangentMetric (n := 0) (M := M))

local notation "V" => EuclideanSpace ℝ (Fin 0)
local notation "TM" => (TangentSpace 𝓘(ℝ, V) : M → Type)

-- Retain the original second-countability hypothesis in the public type.
set_option linter.unusedSectionVars false in
/-- The canonical positive-point tangent integral is the native zero-rank Thom inverse. -/
theorem tangentCohomologyFiberIntegral_zero (p : ℕ) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    tangentCohomologyFiberIntegral g (zeroTangentHomologicalOrientation g) p =
      compactSupportCohomologyFiberIntegral ℚ 0 TM
        (zeroRankIntegralCohomologyOrientation TM).rationalization p := by
  /- The integral orientation equality is tangentCohomologyOrientation_zero.
  Rationalize it and compare the two forward Thom maps by the original
  compact-base comparison. Their inverse maps agree, as in positive rank.
  The canonical empty basis has sign +1; arbitrary negative point
  orientations are not substituted for this specific endpoint. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  have hforward : tangentCohomologyThomEquiv g (zeroTangentHomologicalOrientation g) p =
      compactBaseCohomologyThomEquiv ℚ 0 TM
        (zeroRankIntegralCohomologyOrientation TM).rationalization p := by
    apply LinearEquiv.ext
    intro a
    change compactSupportCohomologyThomMap ℚ 0 TM
      (tangentCohomologyOrientation g (zeroTangentHomologicalOrientation g)).rationalization p
      ((compactSupportCohomologyIso ℚ M p).inv a) = _
    rw [tangentCohomologyOrientation_zero g, compactSupportCohomologyThomMap_compact]
    exact congrArg (cohomologyZeroSectionPushforward ℚ 0 TM
      (zeroRankIntegralCohomologyOrientation TM).rationalization p)
        (congrArg (fun f ↦ f a) (compactSupportCohomologyIso ℚ M p).inv_hom_id)
  exact congrArg (fun e ↦ e.symm.toLinearMap) hforward

set_option maxHeartbeats 1000000 in
-- Use the native tangent metric instances in the dependent degree transports.
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The native zero-spin Thom action gives the original degree-zero Dirac characteristic. -/
theorem baseIndexCharacteristicClass_zeroSpinThom
    (hV : letI := complexificationTopology V TM
      ContinuousHermitianMetric (fun x : M ↦ ℂ ⊗[ℝ] TM x))
    (u : ComplexKZero M) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle V TM :=
      ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
    baseIndexCharacteristicClass (zeroTangentHomologicalOrientation g) g hV
        (zeroSpinThomHom TM hP u) =
      spinDiracCharacteristicClass (m := 0) hV u := by
  /- Stage 1: dimension zero leaves precisely one term in the original
  baseIndexCharacteristicClass. tangentCohomologyFiberIntegral_zero gives
  the same canonical empty-basis integral used by the native spin endpoint.
  Stage 2: apply fiberIntegral_chernCharacter_zeroSpinThom to this exact
  hP, tangent family, hV and u. Its proof uses the actual positive vacuum
  line isomorphism and original odd zero bundle, not dimension alone.
  The original support class and its graph coefficient action are retained.
  Stage 3: the A-hat and inverse A-hat zero components are the actual unit,
  and the only convolution term is the degree-zero character of u. It is
  exactly spinDiracCharacteristicClass at m=0, with (-1)^0=1. Empty and
  disconnected bases retain the same componentwise original K classes. -/
  let : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V TM :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  let := RealBundle.isFiniteRank_of_vectorBundle V TM
  have hzero := fiberIntegral_chernCharacter_zeroSpinThom TM hP hV u 0
  have hhat : RealBundle.aHatEvenComponent V TM hV 0 = singularCohomologyOne ℚ M := by
    simpa [RealBundle.aHatEvenComponent] using
      (RealBundle.pontryagin_aHat_zero V TM hV).2
  dsimp only at hzero
  simp only [pow_zero, one_smul] at hzero
  rw [Fin.sum_univ_one] at hzero
  unfold baseIndexCharacteristicClass spinDiracCharacteristicClass
  rw [Fin.sum_univ_one, Fin.sum_univ_one]
  change singularCohomologyCup ℚ M 0 0
      (tangentCohomologyFiberIntegral g (zeroTangentHomologicalOrientation g) 0
        (g.tangentCompactSupportChernCharacterComponent 0 (zeroSpinThomHom TM hP u)))
      (tangentAHatSquareComponent (n := 0) hV 0) =
    singularCohomologyEvenCup ℚ M 0 0 (chernCharacterKZeroComponent M 0 u)
      (RealBundle.aHatEvenComponent V TM hV 0)
  rw [hhat]
  have hsq : tangentAHatSquareComponent (n := 0) hV 0 = singularCohomologyOne ℚ M := by
    unfold tangentAHatSquareComponent
    rw [Fin.sum_univ_one]
    change singularCohomologyEvenCup ℚ M 0 0
      (RealBundle.aHatEvenComponent V TM hV 0)
      (RealBundle.aHatEvenComponent V TM hV 0) = _
    rw [hhat]
    change singularCohomologyCup ℚ M 0 0
      (singularCohomologyOne ℚ M) (singularCohomologyOne ℚ M) = _
    exact singularCohomologyCup_one ℚ M 0 _
  rw [hsq, singularCohomologyCup_one]
  have ht := congrArg (fun f ↦ f
      (g.tangentCompactSupportChernCharacterComponent 0 (zeroSpinThomHom TM hP u)))
    (tangentCohomologyFiberIntegral_zero g 0)
  apply ht.trans
  simp only [Fin.val_zero, Nat.add_zero, Nat.mul_zero, eqToIso_refl,
    Iso.refl_hom, ModuleCat.id_apply] at hzero
  simp only [Nat.sub_zero, RealBundle.inverseAHatEvenComponent_zero] at hzero
  dsimp only [SmoothTangentMetric.tangentCompactSupportChernCharacterComponent]
  exact hzero

end Zero

end AtiyahSinger
