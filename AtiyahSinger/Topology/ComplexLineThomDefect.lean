/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ComplexLineSelfIntersection
public import AtiyahSinger.Topology.ComplexThomZeroSectionCharacter
public import AtiyahSinger.Topology.ComplexThomDefectNaturality
public import AtiyahSinger.Topology.HermitianCompactness
public import AtiyahSinger.Topology.InverseToddOperations
public import AtiyahSinger.Topology.ProjectiveLineExtension
public import AtiyahSinger.Topology.ProjectiveStableDegreeDetection
public import AtiyahSinger.Topology.LambdaLineClass
public import AtiyahSinger.Topology.LineCharacteristicClasses
public import AtiyahSinger.Topology.LineFirstChernComparison

/-!
# The line Thom defect and its zero-section equation

Public module ID: M1714.

The exterior convention gives the zero-section character 1-exp(c). The canonical
complex orientation supplies exactly the original first Chern class c as its
Euler class. Cancellation is stated only under explicit injectivity of cup by c;
the projective enlargement argument supplies that hypothesis on an actual larger
space before returning to the original line.

Source: SG III.12, the rank-one calculation for the characteristic Thom defect.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (hline : ∀ x, Module.finrank ℂ (E x) = 1)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual line defect times its first Chern class is the positive-degree exterior character. -/
theorem complexThomDefectComponent_evenCup_firstChern_line (j : ℕ) :
    singularCohomologyEvenCup ℚ X j 1 (h.complexThomDefectComponent 1 hline j)
        (singularCohomologyRationalization X 2 (globalChernClass E h 1)) =
      -(Nat.factorial (j + 1) : ℚ)⁻¹ • singularCohomologyDegreeTwoPow ℚ X
        (singularCohomologyRationalization X 2 (globalChernClass E h 1)) (j + 1) := by
  let c : singularCohomology ℚ X 2 := singularCohomologyRationalization X 2 (globalChernClass E h 1)
  let i : C(X, TotalSpace Unit E) := ⟨fun x ↦ ⟨x, 0⟩, continuous_zero_section E⟩
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let τ := h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK)
  let d := h.compactSupportChernCharacterComponent 1 hline (1 + j) τ
  let cT {p q : ℕ} (hpq : p = q) : compactSupportCohomology ℚ (TotalSpace Unit E) p →ₗ[ℚ]
      compactSupportCohomology ℚ (TotalSpace Unit E) q :=
    (eqToIso (congrArg (compactSupportCohomology ℚ (TotalSpace Unit E)) hpq)).hom.hom
  let cH {p q : ℕ} (hpq : p = q) : singularCohomology ℚ X p →ₗ[ℚ]
      singularCohomology ℚ X q :=
    (eqToIso (congrArg (singularCohomology ℚ X) hpq)).hom.hom
  have cH_trans {p q n : ℕ} (hpq : p = q) (hqn : q = n)
      (b : singularCohomology ℚ X p) : cH hqn (cH hpq b) = cH (hpq.trans hqn) b := by
    subst q
    subst n
    rfl
  have htransport {p q : ℕ} (hpq : p = q)
      (b : compactSupportCohomology ℚ (TotalSpace Unit E) p) :
      singularCohomologyPullback ℚ i q
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) q (cT hpq b)) =
      cH hpq (singularCohomologyPullback ℚ i p
        (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) p b)) := by
    subst q
    rfl
  -- Self-intersection uses the same canonically oriented Thom inverse and the original first class.
  have hthom : h.complexCohomologyThomMap 1 hline (2 * j)
      (h.complexThomDefectComponent 1 hline j) = cT (by omega) d :=
    h.complexCohomologyThomMap_fiberIntegral 1 hline (2 * j) _
  have hself := h.zeroSectionPullback_complexCohomologyThomMap_line hline (2 * j)
    (h.complexThomDefectComponent 1 hline j)
  have hfirst := globalChernClass_one_eq_firstChernClass_of_finrank_eq_one E h hline
  dsimp only at hself hfirst
  rw [← hfirst, hthom] at hself
  change singularCohomologyPullback ℚ i (2 * j + 2)
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * j + 2)
      (cT (by omega) d)) =
    singularCohomologyCup ℚ X (2 * j) 2 (h.complexThomDefectComponent 1 hline j) c at hself
  rw [htransport (show 2 * (1 + j) = 2 * j + 2 by omega)] at hself
  have hz := h.zeroSectionPullback_compactSupportChernCharacter_supportedThom_unit 1 hline (1 + j)
  change singularCohomologyPullback ℚ i (2 * (1 + j))
    (compactSupportCohomologyToOrdinary ℚ (TotalSpace Unit E) (2 * (1 + j)) d) =
      chernCharacterKZeroComponent X (1 + j) (lambdaMinusOne E) at hz
  -- In positive degree the unit term vanishes, leaving minus the original line exponential.
  have hchar (k : ℕ) (hk : 0 < k) : chernCharacterKZeroComponent X k (lambdaMinusOne E) =
      -(Nat.factorial k : ℚ)⁻¹ • singularCohomologyDegreeTwoPow ℚ X c k := by
    rw [lambdaMinusOne_eq_one_sub_of_finrank_eq_one E hline, map_sub]
    change chernCharacterKZeroComponent X k (1 : ComplexKZero X) -
      chernCharacterKZeroComponent X k (kZeroClass E) = _
    rw [chernCharacterKZeroComponent_one, chernCharacterKZeroComponent_bundle E h,
      globalChernCharacterComponent_eq_pow_of_finrank_eq_one E h hline]
    apply singularEvenCohomologyOf_injective ℚ X k
    simp only [map_sub, map_smul, map_neg, singularEvenCohomologyOf_degreeTwoPow, map_zero,
      zero_pow (Nat.ne_of_gt hk), zero_sub, neg_smul]
    rfl
  change cH (show 2 * j + 2 = 2 * (j + 1) by omega)
    (singularCohomologyCup ℚ X (2 * j) 2 (h.complexThomDefectComponent 1 hline j) c) = _
  rw [← hself, cH_trans (show 2 * (1 + j) = 2 * j + 2 by omega)
    (show 2 * j + 2 = 2 * (j + 1) by omega), hz, hchar (1 + j) (by omega)]
  have hpow_cast {p q : ℕ} (hpq : p = q) (z : ℚ) :
      cH (congrArg (2 * ·) hpq) (z • singularCohomologyDegreeTwoPow ℚ X c p) =
        z • singularCohomologyDegreeTwoPow ℚ X c q := by
    subst q
    rfl
  rw [hpow_cast (Nat.add_comm 1 j)]
  rw [Nat.add_comm 1 j]

attribute [local instance] trivialTopology isFiniteRank_trivial sumTopology isFiniteRank_sum
  hermitianProjectiveTopology hermitianProjectiveLineTopology isFiniteRank_hermitianProjectiveLine
  isFiniteRank_pullback

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original line Thom defect has the inverse Todd value via an actual projective extension. -/
theorem complexThomDefectComponent_line_eq_inverseTodd (j : ℕ) :
    h.complexThomDefectComponent 1 hline j =
      (-1 : ℚ) ^ (1 + j) • inverseToddClassComponent E h j := by
  -- On any detecting line, its zero-section equation determines the defect in the chosen degree.
  have hcancel {Y : Type u} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
      {L : Y → Type u} [∀ y, AddCommGroup (L y)] [∀ y, Module ℂ (L y)]
      [TopologicalSpace (TotalSpace Unit L)] [IsFiniteRank L]
      (hL : ContinuousHermitianMetric L) (hLrank : ∀ y, Module.finrank ℂ (L y) = 1)
      (hinj : Function.Injective ((singularCohomologyEvenCup ℚ Y j 1).flip
        (singularCohomologyRationalization Y 2 (globalChernClass L hL 1)))) :
      hL.complexThomDefectComponent 1 hLrank j =
        (-1 : ℚ) ^ (1 + j) • inverseToddClassComponent L hL j := by
    apply hinj
    change singularCohomologyEvenCup ℚ Y j 1 _ _ = singularCohomologyEvenCup ℚ Y j 1 _ _
    rw [hL.complexThomDefectComponent_evenCup_firstChern_line hLrank j,
      inverseToddClassComponent_eq_pow_of_finrank_eq_one L hL hLrank j]
    apply singularEvenCohomologyOf_injective ℚ Y (j + 1)
    rw [singularEvenCohomologyOf_cup]
    simp only [map_smul, singularEvenCohomologyOf_degreeTwoPow]
    rw [smul_smul, smul_mul_assoc, ← pow_succ]
    have hsign : (-1 : ℚ) ^ (1 + j) * ((-1 : ℚ) ^ j / (Nat.factorial (j + 1) : ℚ)) =
        -(Nat.factorial (j + 1) : ℚ)⁻¹ := by
      have hsquare : ((-1 : ℚ) ^ j) ^ 2 = 1 := by
        rw [← pow_mul, Nat.mul_comm j 2, pow_mul, neg_one_sq, one_pow]
      rw [pow_add, pow_one, div_eq_mul_inv]
      calc
        _ = -(((-1 : ℚ) ^ j) ^ 2) * (Nat.factorial (j + 1) : ℚ)⁻¹ := by ring
        _ = _ := by rw [hsquare]; ring
    rw [hsign]
  -- Add a trivial complement of adequate size, retaining the original line as an actual summand.
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let F := Bundle.Trivial X (ULift.{u} (EuclideanSpace ℂ (Fin (j + 2))))
  let := modelTopology (ULift.{u} (EuclideanSpace ℂ (Fin (j + 2)))) F
  let := isFiniteRank_model (ULift.{u} (EuclideanSpace ℂ (Fin (j + 2)))) F
  let hF := (nonempty_continuousHermitianMetric F).some
  have hFdim (x : X) : Module.finrank ℂ (F x) = j + 2 :=
    ULift.moduleEquiv.finrank_eq.trans finrank_euclideanSpace_fin
  let D := E ×ᵇ F
  let V := EuclideanSpace ℂ (Fin (1 + (j + 2)))
  let := nativeModelTopology D V
  obtain ⟨b, v, s, hs, ⟨e⟩⟩ :=
    exists_hermitianProjective_sum_line_section E F (j + 2) h hF hline hFdim
  let := b
  let := v
  let hD := (h.sum hF).normedNativeModelMetric D (1 + (j + 2))
  let Q := HermitianProjectiveBundle (1 + (j + 2)) D hD
  let L := HermitianProjectiveLine (1 + (j + 2)) D hD
  let := compactSpace_hermitianProjectiveBundle (1 + (j + 2)) D hD
  let := t2Space_hermitianProjectiveBundle (1 + (j + 2)) D hD
  let hL := (nonempty_continuousHermitianMetric L).some
  have hLrank (q : Q) : Module.finrank ℂ (L q) = 1 := q.2.property.2.1
  -- Auxiliary fiber norms do not change the normalized original line class.
  have hroot : globalChernClass L hL 1 = hermitianProjectiveChernRoot (1 + (j + 2)) D hD := by
    have hfirst := globalChernClass_one_eq_firstChernClass_of_finrank_eq_one L hL hLrank
    have hnorm := @firstChernClass_eq_of_iso Q _ L hL.fiberNormedAddCommGroup
      (fun q ↦ (hL.fiberInnerProductSpace q).toNormedSpace) _ _ hLrank L
      (inferInstance : ∀ q, NormedAddCommGroup (L q))
      (inferInstance : ∀ q, NormedSpace ℂ (L q)) _ _ hLrank (Iso.refl L)
    exact hfirst.trans hnorm
  have hinj : Function.Injective ((singularCohomologyEvenCup ℚ Q j 1).flip
      (singularCohomologyRationalization Q 2 (globalChernClass L hL 1))) := by
    rw [hroot, ← singularCohomologyChangeCoefficients_rat]
    exact hermitianProjectiveChernRoot_evenCup_injective ℚ (1 + (j + 2)) D hD j (by omega)
  have hvalue := hcancel hL hLrank hinj
  -- Pull back along that same actual summand section; no cancellation occurs on X.
  have hdefect := complexThomDefectComponent_eq_pullback_of_iso h hL 1 hline hLrank s e.symm j
  have htodd : singularCohomologyPullback ℚ s (2 * j) (inverseToddClassComponent L hL j) =
      inverseToddClassComponent E h j := by
    rw [inverseToddClassComponent_pullback]
    exact inverseToddClassComponent_eq_of_iso _ (hL.pullback s) E h e j
  rw [hdefect, hvalue, map_smul, htodd]

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
