/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleTensorKZero
public import AtiyahSinger.Topology.ChernCharacterNormalization
public import AtiyahSinger.Topology.GeometricKZeroUniversal
public import AtiyahSinger.Topology.KZeroRing
public import AtiyahSinger.Topology.VariableRankChernOperations

/-!
# The original degreewise Chern character on the actual complex K group

Public module ID: M1606.

C02, SG III.11 Corollary 11.17, p.235. The original locally finite-rank
bundle character descends through the existing geometric Grothendieck lift
into ComplexKZero X. Its input is the actual class of a bundle, including
locally varying rank. An arbitrary characteristic map is never supplied.
The auxiliary metric is chosen only from metric existence and disappears
from the bundle-value theorem by metric independence.

The base is compact Hausdorff, exactly as in SG Corollary 11.17. Components
are additive maps into the original H^(2k)(X;Q). Their finite cup convolution
and unit formula give the degreewise unital ring-morphism statement. This
formulation is valid even when the cohomology is not bounded above; it does
not put an unsupported infinite character sum in direct-sum cohomology.
Hatcher VBKT pp.109--110 explicitly distinguishes the direct-product target.
Compact-support characters and their Thom compatibility are downstream.

Data are actual selections and the existing K-zero lift. The additive lift,
bundle values, uniqueness, unit and naturality use the original geometric
relations. The actual tensor-bundle law and biadditivity prove multiplicativity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory

universe u v

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

namespace ComplexBundle

/-- The original component of a bundled finite-rank bundle, using an auxiliary chosen metric. -/
def FiniteBundle.chernCharacterComponent (E : FiniteBundle X) (k : ℕ) :
    singularCohomology ℚ X (2 * k) :=
  globalChernCharacterComponent E.Fiber
    (nonempty_continuousHermitianMetric E.Fiber).some k

/-- The isomorphism and direct-sum laws needed by the existing geometric K-zero lift. -/
theorem finiteBundleChernCharacterComponent_properties (k : ℕ) :
    (∀ E F : FiniteBundle X, Iso E.Fiber F.Fiber →
      E.chernCharacterComponent k = F.chernCharacterComponent k) ∧
    (∀ E F : FiniteBundle X,
      (E.sum F).chernCharacterComponent k =
        E.chernCharacterComponent k + F.chernCharacterComponent k) := by
  /- Stage 1: each selected metric exists on the original bundle because
  a compact Hausdorff space is paracompact. An original continuous complex
  bundle isomorphism preserves globalChernCharacterComponent by its actual
  isomorphism law; the selected metrics need not be related or preserved.
  Stage 2: the bundled sum has the original product fibers and sumTopology.
  Apply the global direct-sum law to the identity isomorphism of that very
  sum. Metric independence permits the separately chosen metric on the sum.
  Both steps include varying and zero ranks and the empty base. -/
  constructor
  · intro E F e
    exact globalChernCharacterComponent_eq_of_iso E.Fiber _ F.Fiber _ e k
  · intro E F
    let := (E.sum F).totalTopology
    let := (E.sum F).isFiniteRank
    exact globalChernCharacterComponent_sum E.Fiber _ F.Fiber _
      (E.sum F).Fiber _ (Iso.refl _) k

end ComplexBundle

/-- The actual additive Chern-character component on the existing complex Grothendieck group. -/
def chernCharacterKZeroComponent (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (k : ℕ) :
    ComplexKZero X →+ singularCohomology ℚ X (2 * k) :=
  ComplexBundle.bundleKZeroLift
    (fun E : ComplexBundle.FiniteBundle X ↦ E.chernCharacterComponent k)
    (ComplexBundle.finiteBundleChernCharacterComponent_properties (X := X) k).1
    (ComplexBundle.finiteBundleChernCharacterComponent_properties (X := X) k).2

/-- The character of every original bundle class is its actual metric-independent component. -/
theorem chernCharacterKZeroComponent_bundle
    (E : X → Type v) [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [TopologicalSpace (TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]
    (h : ComplexBundle.ContinuousHermitianMetric E) (k : ℕ) :
    chernCharacterKZeroComponent X k (ComplexBundle.kZeroClass E) =
      ComplexBundle.globalChernCharacterComponent E h k := by
  /- Stage 1: use smallBundleIso for the given original family. Its bundle
  isomorphism preserves the actual K class and the actual character even
  if the original fibers inhabit a larger universe. It does not change
  the base, impose constant rank or infer an unstabilized isomorphism
  merely from an equality of K classes.
  Stage 2: bundleKZeroLift_bundle evaluates the selected geometric lift
  on that same small bundle. The value is its actual character with its
  selected metric. The global isomorphism and metric-independence laws
  identify it with the displayed component of E and the supplied h. -/
  -- Pass through the specified small model without identifying its chosen metric with h.
  let F := ComplexBundle.smallBundle E
  let e := ComplexBundle.smallBundleIso E
  rw [ComplexBundle.kZeroClass_eq_of_iso e]
  change ComplexBundle.bundleKZeroLift _ _ _ F.kZeroClass = _
  rw [ComplexBundle.bundleKZeroLift_bundle]
  exact (ComplexBundle.globalChernCharacterComponent_eq_of_iso E h F.Fiber _ e k).symm

/-- Values on the original geometric bundle generators uniquely determine this additive map. -/
theorem chernCharacterKZeroComponent_unique (k : ℕ)
    (f : ComplexKZero X →+ singularCohomology ℚ X (2 * k))
    (hf : ∀ E : ComplexBundle.FiniteBundle X,
      f E.kZeroClass = E.chernCharacterComponent k) :
    f = chernCharacterKZeroComponent X k := by
  /- Apply the uniqueness clause of bundleKZero_universal_property to the
  same concrete bundle-character function. Its iso/sum certificates are
  exactly those used to construct chernCharacterKZeroComponent. Equivalently
  every K class is an actual image-bundle class minus a trivial-bundle class,
  and additivity determines the value on that difference. -/
  -- Both maps satisfy the same geometric universal property with the same two relations.
  let φ := fun E : ComplexBundle.FiniteBundle X ↦ E.chernCharacterComponent k
  let h := ComplexBundle.finiteBundleChernCharacterComponent_properties (X := X) k
  exact (ComplexBundle.bundleKZero_universal_property φ h.1 h.2).unique hf
    (ComplexBundle.bundleKZeroLift_bundle φ h.1 h.2)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG Corollary 11.17: multiplication is the finite even-cup convolution in every degree. -/
theorem chernCharacterKZeroComponent_mul (a b : ComplexKZero X) (k : ℕ) :
    chernCharacterKZeroComponent X k (a * b) =
      ∑ i : Fin (k + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
              singularCohomology ℚ X (2 * k)).hom
          (singularCohomologyEvenCup ℚ X i.val (k - i.val)
            (chernCharacterKZeroComponent X i.val a)
            (chernCharacterKZeroComponent X (k - i.val) b)) := by
  classical
  let C (a b : ComplexKZero X) : singularCohomology ℚ X (2 * k) :=
    ∑ i : Fin (k + 1),
      (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
          singularCohomology ℚ X (2 * (i.val + (k - i.val))) ≅
            singularCohomology ℚ X (2 * k)).hom
        (singularCohomologyEvenCup ℚ X i.val (k - i.val)
          (chernCharacterKZeroComponent X i.val a)
          (chernCharacterKZeroComponent X (k - i.val) b))
  change chernCharacterKZeroComponent X k (a * b) = C a b
  -- The finite convolution is additive in both of the original K-group variables.
  have hleft (a a' b : ComplexKZero X) : C (a - a') b = C a b - C a' b := by
    dsimp only [C]
    simp only [map_sub, LinearMap.sub_apply, Finset.sum_sub_distrib]
  have hright (a b b' : ComplexKZero X) : C a (b - b') = C a b - C a b' := by
    dsimp only [C]
    simp only [map_sub, Finset.sum_sub_distrib]
  have hbundle (E F : X → Type)
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [TopologicalSpace (TotalSpace Unit E)] [ComplexBundle.IsFiniteRank E]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [TopologicalSpace (TotalSpace Unit F)] [ComplexBundle.IsFiniteRank F] :
      chernCharacterKZeroComponent X k (ComplexBundle.kZeroClass E * ComplexBundle.kZeroClass F) =
        C (ComplexBundle.kZeroClass E) (ComplexBundle.kZeroClass F) := by
    let T := fun x ↦ TensorProduct ℂ (E x) (F x)
    let := ComplexBundle.tensorTopology (E := E) (F := F)
    let := ComplexBundle.isFiniteRank_tensor (E := E) (F := F)
    let hE := (ComplexBundle.nonempty_continuousHermitianMetric E).some
    let hF := (ComplexBundle.nonempty_continuousHermitianMetric F).some
    let hT := (ComplexBundle.nonempty_continuousHermitianMetric T).some
    have hmul : ComplexBundle.kZeroClass E * ComplexBundle.kZeroClass F =
        ComplexBundle.kZeroClass T := (ComplexBundle.kZeroClass_tensor (E := E) (F := F)).symm
    rw [hmul, chernCharacterKZeroComponent_bundle T hT k]
    dsimp only [C]
    simp only [chernCharacterKZeroComponent_bundle E hE, chernCharacterKZeroComponent_bundle F hF]
    exact ComplexBundle.globalChernCharacterComponent_tensor E hE F hF T hT
      (ComplexBundle.Iso.refl T) k
  -- Use the actual image-minus-trivial presentations; no cancellation of bundles is assumed.
  obtain ⟨p, m, ha⟩ := ComplexBundle.exists_class_sub_trivial a
  obtain ⟨q, n, hb⟩ := ComplexBundle.exists_class_sub_trivial b
  let := IdempotentMatrix.fiberTotalSpaceTopology p
  let := IdempotentMatrix.isFiniteRank_fiber p
  let := IdempotentMatrix.fiberTotalSpaceTopology q
  let := IdempotentMatrix.isFiniteRank_fiber q
  let := ComplexBundle.trivialTopology (X := X) m
  let := ComplexBundle.isFiniteRank_trivial (X := X) m
  let := ComplexBundle.trivialTopology (X := X) n
  let := ComplexBundle.isFiniteRank_trivial (X := X) n
  rw [ha, hb, sub_mul, mul_sub, mul_sub, map_sub, map_sub, map_sub,
    hbundle, hbundle, hbundle, hbundle, hleft, hright, hright]

/-- The free line is sent to the cohomological unit, with zero higher components. -/
theorem chernCharacterKZeroComponent_one (k : ℕ) :
    chernCharacterKZeroComponent X k (1 : ComplexKZero X) =
      singularCohomologyDegreeTwoPow ℚ X (0 : singularCohomology ℚ X 2) k := by
  /- The installed K-zero unit is the class of the original trivial line.
  Apply the bundle-value theorem and its actual character normalization:
  degree zero is the rank, and positive components vanish by pullback from
  a point. The displayed zeroth power is the cohomological unit, and every
  positive power is zero. No infinite series is formed. -/
  let := ComplexBundle.trivialTopology (X := X) 1
  let := ComplexBundle.isFiniteRank_trivial (X := X) 1
  let E := Bundle.Trivial X (Fin 1 → ℂ)
  let h := (ComplexBundle.nonempty_continuousHermitianMetric E).some
  -- The installed ring unit is the identity idempotent of this same trivial line.
  have hunit : (1 : ComplexKZero X) = ComplexBundle.kZeroClass E :=
    (ComplexBundle.kZeroClass_trivial (X := X) 1).symm
  rw [hunit, chernCharacterKZeroComponent_bundle E h k]
  exact ComplexBundle.globalChernCharacterComponent_trivial_line h k

/-- The same degreewise character commutes with the original K-theory and cohomology pullbacks. -/
theorem chernCharacterKZeroComponent_pullback
    {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (f : C(X, Y)) (a : ComplexKZero Y) (k : ℕ) :
    chernCharacterKZeroComponent X k (complexKZeroPullback f a) =
      singularCohomologyPullback ℚ f (2 * k) (chernCharacterKZeroComponent Y k a) := by
  /- Stage 1: on an actual bundle class, kZeroClass_pullback uses exactly
  the original map f and original pullback topology. The bundle-value
  theorem and global character naturality identify its component with
  singular pullback along this same f, independently of selected metrics.
  Stage 2: both sides are additive on the original K group. Its geometric
  generators therefore determine equality on arbitrary virtual classes.
  No smoothness or additional properness premise is needed for f. -/
  classical
  -- Compare the two additive maps on the actual geometric generators of K⁰(Y).
  let p := (singularCohomologyPullback ℚ f (2 * k)).hom.toAddMonoidHom
  let φ := fun E : ComplexBundle.FiniteBundle Y ↦ p (E.chernCharacterComponent k)
  let h := ComplexBundle.finiteBundleChernCharacterComponent_properties (X := Y) k
  have hi (E F : ComplexBundle.FiniteBundle Y) (e : ComplexBundle.Iso E.Fiber F.Fiber) :
      φ E = φ F := congrArg p (h.1 E F e)
  have hs (E F : ComplexBundle.FiniteBundle Y) : φ (E.sum F) = φ E + φ F := by
    dsimp [φ]
    rw [h.2, map_add]
  have hleft (E : ComplexBundle.FiniteBundle Y) :
      ((chernCharacterKZeroComponent X k).comp (complexKZeroPullback f)) E.kZeroClass =
        φ E := by
    let := (E.pullback f).totalTopology
    let := (E.pullback f).isFiniteRank
    -- The bundled pullback uses exactly the topology and map of the geometric K⁰ law.
    change chernCharacterKZeroComponent X k (complexKZeroPullback f E.kZeroClass) = _
    rw [← E.kZeroClass_pullback f]
    change chernCharacterKZeroComponent X k
      (ComplexBundle.kZeroClass (E.pullback f).Fiber) = _
    rw [chernCharacterKZeroComponent_bundle (E.pullback f).Fiber
      (ComplexBundle.nonempty_continuousHermitianMetric (E.pullback f).Fiber).some k]
    exact ComplexBundle.globalChernCharacterComponent_pullback E.Fiber _ f
      (E.pullback f).Fiber _ (ComplexBundle.Iso.refl _) k
  have hright (E : ComplexBundle.FiniteBundle Y) :
      (p.comp (chernCharacterKZeroComponent Y k)) E.kZeroClass = φ E := by
    change p (ComplexBundle.bundleKZeroLift _ _ _ E.kZeroClass) = _
    rw [ComplexBundle.bundleKZeroLift_bundle]
  -- Uniqueness extends the generator equality to every original virtual class.
  have heq := (ComplexBundle.bundleKZero_universal_property φ hi hs).unique hleft hright
  exact DFunLike.congr_fun heq a

end AtiyahSinger
