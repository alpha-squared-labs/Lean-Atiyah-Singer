/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianFlagManifold
public import AtiyahSinger.Topology.ComplexBundleCohomologyThom
public import AtiyahSinger.Topology.ComplexBundleCohomologyVanishing
public import AtiyahSinger.Topology.ComplexBundleCompactSupportCharacter
public import AtiyahSinger.Topology.ComplexCohomologyProjectionFormula
public import AtiyahSinger.Topology.CompactSupportChernAction
public import AtiyahSinger.Topology.ComplexThomDefectDefinition
public import AtiyahSinger.Topology.ComplexSplitThomDefect
public import AtiyahSinger.Topology.HermitianCompactness
public import AtiyahSinger.Topology.InverseTodd
public import AtiyahSinger.Topology.ThomZeroSection

/-!
# The complex Thom character and its characteristic defect

Public module ID: M1719.

C04: SG III.12, equations (12.5)--(12.11), with the original exterior Thom
symbol on E itself. The defect is defined by integrating the supported Chern
character of its actual K-Thom image of the unit. Fiber integration is the
inverse of the original cup-product Thom map, transported through the identity
on the original total-space vectors, with the canonical complex orientation.

SG's formula is (-1)^r Td(conjugate E)^(-1). Here its degree-2j component is
written (-1)^(r+j) times inverseToddClassComponent E h j: conjugation negates
the formal Chern roots and the component is homogeneous of weight j. Thus the
formula keeps the actual original E and never presupposes an unconstructed
conjugate bundle. This convention differs from a dual-exterior Thom symbol.

The base is compact Hausdorff and the complex rank is fixed, including zero.
Under the second-countable manifold and integral homological-orientation
hypotheses of ThomGysinComparison, the independent Poincare-duality Gysin
is compared with the rational Thom inverse, with the prescribed cap sign.
That theorem does not apply to every compact Hausdorff base used here.
Atiyah--Singer III, section 2, uses Cech cohomology in its general
compact-space formulation; no general Cech-to-singular support
comparison is assumed here.
The below-rank vanishing and the fiber-integral convolution use the original
supported action. The inverse-Todd defect formula follows on the actual full
flag bundle from finite projective line enlargements and descends through its
injective singular-cohomology pullback. No Euler cancellation on the original
base or unconstructed universal supported comparison is assumed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle CategoryTheory

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace

universe u

variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  {E : X → Type u} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (h : ContinuousHermitianMetric E) (r : ℕ) (hr : ∀ x, Module.finrank ℂ (E x) = r)

/-- The supported character of any actual complex Thom image vanishes below its Thom degree. -/
theorem compactSupportChernCharacter_supportedThom_eq_zero_of_lt
    (u : ComplexKZero X) (k : ℕ) (hk : k < r) :
    h.compactSupportChernCharacterComponent r hr k
        (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm u)) = 0 := by
  /- Stage 1: the same Hermitian metric and native real model identify
  the original support colimit with the relative Thom pair using cofinal
  compact disk bundles. The relative Thom theorem gives zero in degrees
  below real rank 2*r; transport through the original total homeomorphism.
  Stage 2: 2*k < 2*r, so the specified supported character is zero in that
  group for every original virtual coefficient u. This concerns supported
  cohomology itself, not an injectivity assertion after forgetting support.
  The rank-zero branch has no natural-number degree below the Thom degree. -/
  have hdegree : 2 * k < 2 * r := by omega
  exact (h.compactSupportCohomology_subsingleton_below_complex_rank r hr
    (2 * k) hdegree).elim _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG (12.11), expressed on the original bundle by the homogeneous conjugation sign. -/
theorem complexThomDefectComponent_eq_inverseTodd (j : ℕ) :
    h.complexThomDefectComponent r hr j =
      (-1 : ℚ) ^ (r + j) • inverseToddClassComponent E h j := by
  /- The original full flag splits this bundle into its projection range
  lines. On that compact Hausdorff base the split-bundle theorem uses
  actual projective enlargements: the common Euler-root factor annihilates
  the difference, and detection makes its section restriction zero.
  Naturality compares both classes along the same flag projection; its
  injective cohomology pullback then returns the equality to X. -/
  classical
  let : ∀ x, NormedAddCommGroup (E x) := h.fiberNormedAddCommGroup
  let : ∀ x, InnerProductSpace ℂ (E x) := h.fiberInnerProductSpace
  let V := EuclideanSpace ℂ (Fin r)
  let := nativeModelTopology E V
  let := h.nativeFiberBundle r hr
  let := h.nativeVectorBundle r hr
  let hN := h.nativeModelMetric r
  let := hermitianFlagTopology r E hN
  let Q := HermitianFlagBundle r E hN
  let p := hermitianFlagProjection r E hN
  let : CompactSpace Q := by
    constructor
    simpa only [Set.preimage_univ] using
      (hermitianFlagProjection_isProperMap r E hN).isCompact_preimage isCompact_univ
  let : T2Space Q := t2Space_hermitianFlagBundle r E hN
  let L := HermitianFlagLine r E hN
  let : ∀ i, TopologicalSpace (TotalSpace Unit (L i)) :=
    fun i ↦ hermitianFlagLineTopology r E hN i
  let : ∀ i, IsFiniteRank (L i) := fun i ↦ isFiniteRank_hermitianFlagLine r E hN i
  let := finiteSumTopology r L
  let hL (i : Fin r) : ContinuousHermitianMetric (L i) :=
    (nonempty_continuousHermitianMetric (L i)).some
  have hline (i : Fin r) (q : Q) : Module.finrank ℂ (L i q) = 1 := q.2.property.2.1 i
  let P := (p : Q → X) *ᵖ E
  let := isFiniteRank_pullback (E := E) p
  let hP := h.pullback p
  have hPdim (q : Q) : Module.finrank ℂ (P q) = r := hr (p q)
  -- The inverse phantom retyping recovers the original Unit pullback topology exactly.
  have ht := modelTopology_nativeModelTopology (E := E) r
  dsimp only at ht
  let originalTopology : TopologicalSpace (TotalSpace Unit E) := inferInstance
  let := modelTopology V E
  let nativeSplit := hermitianFlagSplitting r E hN
  let splitLinear (q : Q) : P q ≃ₗ[ℂ] FiniteSum r L q :=
    (nativeSplit.linearEquiv q).symm
  have hforward : Continuous (fun z : TotalSpace Unit P ↦
      (⟨z.proj, splitLinear z.proj z.snd⟩ : TotalSpace Unit (FiniteSum r L))) :=
    nativeSplit.continuous_symm
  have hbackward : Continuous (fun z : TotalSpace Unit (FiniteSum r L) ↦
      (⟨z.proj, (splitLinear z.proj).symm z.snd⟩ : TotalSpace Unit P)) :=
    nativeSplit.continuous_total
  let := originalTopology
  have hpullback :
      @Pullback.TotalSpace.topologicalSpace _ Unit E _ p inferInstance (modelTopology V E) =
        @Pullback.TotalSpace.topologicalSpace _ Unit E _ p inferInstance inferInstance :=
    congrArg (fun t ↦ @Pullback.TotalSpace.topologicalSpace _ Unit E _ p inferInstance t) ht
  let e : Iso P (FiniteSum r L) :=
    { linearEquiv := splitLinear
      continuous_total := by
        rw [hpullback] at hforward
        exact hforward
      continuous_symm := by
        rw [hpullback] at hbackward
        exact hbackward }
  have hvalue := complexThomDefectComponent_eq_inverseTodd_of_lineSplitting r L hL hline
    hP hPdim e j
  -- Both pullbacks use the same p, the original metric, and the identity on its actual fibers.
  have hdefect := complexThomDefectComponent_eq_pullback_of_iso hP h r hPdim hr p
    (Iso.refl P) j
  apply hermitianFlagProjection_cohomology_injective ℚ r E hN (2 * j)
  rw [← hdefect, hvalue, map_smul, inverseToddClassComponent_pullback]

set_option maxHeartbeats 600000 in
-- Normalize the original supported Thom graph action and its fiber-integral character.
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- SG (12.9): fiber integration of the actual Thom character is multiplication by its defect. -/
theorem fiberIntegral_chernCharacter_supportedThom (u : ComplexKZero X) (j : ℕ) :
    h.complexCohomologyFiberIntegral r hr (2 * j)
        ((eqToIso (by congr 1; omega) :
            compactSupportCohomology ℚ (TotalSpace Unit E) (2 * (r + j)) ≅
              compactSupportCohomology ℚ (TotalSpace Unit E) (2 * j + 2 * r)).hom
          (h.compactSupportChernCharacterComponent r hr (r + j)
            (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm u)))) =
      ∑ i : Fin (j + 1),
        (eqToIso (by rw [Nat.add_sub_of_le (Nat.le_of_lt_succ i.isLt)]) :
            singularCohomology ℚ X (2 * (i.val + (j - i.val))) ≅
              singularCohomology ℚ X (2 * j)).hom
          (singularCohomologyEvenCup ℚ X i.val (j - i.val)
            (chernCharacterKZeroComponent X i.val u)
            (h.complexThomDefectComponent r hr (j - i.val))) := by
  let Y := TotalSpace Unit E
  let πE : C(Y, X) := ⟨π Unit E, continuous_proj (E := E)⟩
  let oneK := AtiyahSinger.kZeroClass C(X, ℂ) (IdempotentMatrix.identity C(X, ℂ) 1)
  let τ := h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm oneK)
  let d (n : ℕ) := h.compactSupportChernCharacterComponent r hr n τ
  -- The original compact-base Thom map is the graph action on its own unit symbol.
  have haction : h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm u) =
      complexKZeroCompactSupportAction πE u τ := by
    let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
      InnerProductSpace.ofCore (h.toCore x).toCore
    have hcompact (v : ComplexKZero X) :
        h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm v) =
          exteriorThomHom E h.continuous_pairing v := by
      change ComplexBundle.supportedThomHom E h.continuous_pairing _ = _
      rw [supportedThomHom_compact, AddMonoidHom.comp_apply]
      exact congrArg (exteriorThomHom E h.continuous_pairing)
        ((compactSupportKZeroCompactEquiv X).apply_symm_apply v)
    have hunit : τ = exteriorThomClass E h.continuous_pairing := by
      rw [show τ = exteriorThomHom E h.continuous_pairing oneK from hcompact oneK]
      exact complexKZeroCompactSupportAction_one πE _
    rw [hcompact u, hunit]
    rfl
  -- Keep all canonical degree changes local; they carry no mathematical choices.
  let cT {m n : ℕ} (hmn : m = n) : compactSupportCohomology ℚ Y m →ₗ[ℚ]
      compactSupportCohomology ℚ Y n :=
    (eqToIso (congrArg (compactSupportCohomology ℚ Y) hmn)).hom.hom
  let cH {m n : ℕ} (hmn : m = n) : singularCohomology ℚ X m →ₗ[ℚ]
      singularCohomology ℚ X n :=
    (eqToIso (congrArg (singularCohomology ℚ X) hmn)).hom.hom
  have cT_trans {m n l : ℕ} (hmn : m = n) (hnl : n = l)
      (b : compactSupportCohomology ℚ Y m) :
      cT hnl (cT hmn b) = cT (hmn.trans hnl) b := by
    subst n
    subst l
    rfl
  have cH_trans {m n l : ℕ} (hmn : m = n) (hnl : n = l)
      (b : singularCohomology ℚ X m) : cH hnl (cH hmn b) = cH (hmn.trans hnl) b := by
    subst n
    subst l
    rfl
  have cT_action (p : ℕ) {q q' : ℕ} (hqq : q = q')
      (a : singularCohomology ℚ Y p) (b : compactSupportCohomology ℚ Y q) :
      cT (congrArg (p + ·) hqq) (compactSupportCohomologyAction ℚ Y p q a b) =
        compactSupportCohomologyAction ℚ Y p q' a (cT hqq b) := by
    subst q'
    rfl
  have cT_integral {p q : ℕ} (hpq : p = q)
      (b : compactSupportCohomology ℚ Y (p + 2 * r)) :
      h.complexCohomologyFiberIntegral r hr q (cT (congrArg (· + 2 * r) hpq) b) =
        cH hpq (h.complexCohomologyFiberIntegral r hr p b) := by
    subst q
    rfl
  have cT_d {m n : ℕ} (hmn : m = n) : cT (congrArg (2 * ·) hmn) (d m) = d n := by
    subst n
    rfl
  let F (i : Fin (r + j + 1)) : singularCohomology ℚ X (2 * j) :=
    h.complexCohomologyFiberIntegral r hr (2 * j)
      (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val)
        (2 * (r + j - i.val))
        (singularCohomologyPullback ℚ πE (2 * i.val) (chernCharacterKZeroComponent X i.val u))
        (d (r + j - i.val))))
  -- Apply the proven support action before distributing the specified integral over the finite sum.
  have hsum : h.complexCohomologyFiberIntegral r hr (2 * j)
      ((eqToIso (by congr 1; omega) : compactSupportCohomology ℚ Y (2 * (r + j)) ≅
        compactSupportCohomology ℚ Y (2 * j + 2 * r)).hom
        (h.compactSupportChernCharacterComponent r hr (r + j)
          (h.supportedThomHom ((compactSupportKZeroCompactEquiv X).symm u)))) =
      ∑ i : Fin (r + j + 1), F i := by
    rw [haction, h.compactSupportChernCharacterComponent_action]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    change h.complexCohomologyFiberIntegral r hr (2 * j)
      (cT (by omega) (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val)
        (2 * (r + j - i.val)) _ (d (r + j - i.val))))) = F i
    rw [cT_trans (show 2 * i.val + 2 * (r + j - i.val) = 2 * (r + j) by omega)
      (show 2 * (r + j) = 2 * j + 2 * r by omega)]
  -- Each retained term uses the projection formula and exactly the original unit-symbol defect.
  have hterm (i : Fin (r + j + 1)) (hi : i.val ≤ j) : F i =
      (eqToIso (by congr 1; omega) : singularCohomology ℚ X (2 * (i.val + (j - i.val))) ≅
        singularCohomology ℚ X (2 * j)).hom
        (singularCohomologyEvenCup ℚ X i.val (j - i.val)
          (chernCharacterKZeroComponent X i.val u)
          (h.complexThomDefectComponent r hr (j - i.val))) := by
    let a := chernCharacterKZeroComponent X i.val u
    let b := d (r + j - i.val)
    have hindex : r + j - i.val = r + (j - i.val) := by omega
    have hdegree : 2 * i.val + 2 * (j - i.val) = 2 * j := by omega
    have hbdegree : 2 * (r + j - i.val) = 2 * (j - i.val) + 2 * r := by omega
    change h.complexCohomologyFiberIntegral r hr (2 * j)
      (cT (by omega) (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (r + j - i.val))
        (singularCohomologyPullback ℚ πE (2 * i.val) a) (d (r + j - i.val)))) = _
    have hnormalize : cT (by omega)
        (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (r + j - i.val))
          (singularCohomologyPullback ℚ πE (2 * i.val) a) b) =
      cT (congrArg (· + 2 * r) hdegree)
        (cT (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * r)).symm
          (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (j - i.val) + 2 * r)
            (singularCohomologyPullback ℚ πE (2 * i.val) a) (cT hbdegree b))) := by
      rw [← cT_action (2 * i.val) hbdegree,
        cT_trans (congrArg (2 * i.val + ·) hbdegree)
          (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * r)).symm,
        cT_trans ((congrArg (2 * i.val + ·) hbdegree).trans
          (Nat.add_assoc (2 * i.val) (2 * (j - i.val)) (2 * r)).symm)
          (congrArg (· + 2 * r) hdegree)]
    rw [hnormalize, cT_integral hdegree]
    change cH hdegree
      (h.complexCohomologyFiberIntegral r hr (2 * i.val + 2 * (j - i.val))
        ((eqToIso (by rw [Nat.add_assoc]) :
            compactSupportCohomology ℚ Y ((2 * i.val + 2 * (j - i.val)) + 2 * r) ≅
              compactSupportCohomology ℚ Y (2 * i.val + (2 * (j - i.val) + 2 * r))).inv
          (compactSupportCohomologyAction ℚ Y (2 * i.val) (2 * (j - i.val) + 2 * r)
            (singularCohomologyPullback ℚ πE (2 * i.val) a) (cT hbdegree b)))) = _
    rw [h.complexCohomologyFiberIntegral_action]
    have hdefect : h.complexCohomologyFiberIntegral r hr (2 * (j - i.val))
        (cT hbdegree b) = h.complexThomDefectComponent r hr (j - i.val) := by
      change h.complexCohomologyFiberIntegral r hr (2 * (j - i.val)) (cT hbdegree b) =
        h.complexCohomologyFiberIntegral r hr (2 * (j - i.val))
          (cT (show 2 * (r + (j - i.val)) = 2 * (j - i.val) + 2 * r by omega)
            (d (r + (j - i.val))))
      rw [← cT_d hindex, cT_trans (congrArg (2 * ·) hindex)
        (show 2 * (r + (j - i.val)) = 2 * (j - i.val) + 2 * r by omega)]
    rw [hdefect]
    change cH hdegree (singularCohomologyCup ℚ X (2 * i.val) (2 * (j - i.val)) a
      (h.complexThomDefectComponent r hr (j - i.val))) =
      cH (by omega) (cH (by omega) (singularCohomologyCup ℚ X (2 * i.val) (2 * (j - i.val)) a
        (h.complexThomDefectComponent r hr (j - i.val))))
    rw [cH_trans (show 2 * i.val + 2 * (j - i.val) = 2 * (i.val + (j - i.val)) by omega)
      (show 2 * (i.val + (j - i.val)) = 2 * j by omega)]
  -- Terms beyond j vanish in the original support group before integration.
  have hzero (i : Fin (r + j + 1)) (hi : j < i.val) : F i = 0 := by
    have hd : d (r + j - i.val) = 0 :=
      h.compactSupportChernCharacter_supportedThom_eq_zero_of_lt r hr oneK _ (by omega)
    dsimp only [F]
    rw [hd]
    simp only [map_zero]
  rw [hsum]
  have hsize : (j + 1) + r = r + j + 1 := by omega
  rw [← Fin.sum_congr' F hsize]
  have htail (i : Fin r) : F ((Fin.natAdd (j + 1) i).cast hsize) = 0 :=
    hzero _ (by simp only [Fin.val_cast, Fin.val_natAdd]; omega)
  rw [Fin.sum_trunc (fun i : Fin ((j + 1) + r) ↦ F (i.cast hsize)) htail]
  apply Finset.sum_congr rfl
  intro i _
  exact hterm _ (by simpa only [Fin.val_cast, Fin.val_castAdd] using Nat.le_of_lt_succ i.isLt)

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
