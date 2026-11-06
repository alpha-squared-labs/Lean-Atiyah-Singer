/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SuspendedKModule
public import AtiyahSinger.Topology.ZeroSpinorThomClass

import AtiyahSinger.Topology.ZeroHalfSpinorCharacter

/-!
# The spin Thom map at the native rank-zero endpoint

Public module ID: M2277.

S03. The actual graph action of the base K group multiplies the original
zeroSpinorThomClass. The same degree-zero class gives a bijection in every
nonpositive degree, and the ordinary K(B) map gives an additive equivalence.
The original real total space, principal certificate, associated parity
quotients and zero section are retained in all four declarations.

Sources: Lawson--Michelsohn, Spin Geometry, Appendix C.1--C.2 and C.12,
and III.12, Proposition 12.6. This is their degenerate extension using the
unit-generated Spin(0) convention of I.2, as fixed by SpinZero. The native
group is trivial. The canonical vacuum vector therefore supplies a global
trivialization of the original positive associated line; its rank alone
would not justify identifying its K class with the unit. This identification
is established in the proof below using the vacuum-normalized bundle isomorphism.

The positive-rank geometric spin theorem is stated separately. No different
stable rank-zero double-cover convention is identified here. The two bijectivity
proofs below use the original all-degree graph and the specified compact-base
and degree-zero comparisons; the homomorphism and equivalence retain their values.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

variable {B P : Type*} [TopologicalSpace B] [TopologicalSpace P]
  [CompactSpace B] [T2Space B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin 0)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin 0)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin 0)) E]
  [MulAction (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm 0))ᵐᵒᵖ P]
  {projection : P → B}
  (hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm 0)) projection)

local notation "RealModel" => EuclideanSpace ℝ (Fin 0)

/-- The original base action on the specified native rank-zero spin symbol class. -/
def zeroSpinThomHom : ComplexKZero B →+ CompactSupportKZero (TotalSpace RealModel E) :=
  (complexKZeroCompactSupportAction
    (⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩ :
      C(TotalSpace RealModel E, B))).flip (zeroSpinorThomClass E hP)

/-- The original native rank-zero spin class is a K-orientation in every suspended degree. -/
theorem zeroSpinorThomClass_isKOrientation (n : ℕ) :
    Function.Bijective
      ((compactSupportKAction n
        (⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩ :
          C(TotalSpace RealModel E, B))).flip (zeroSpinorThomClass E hP)) := by
  /- Stage 1: use the vacuum-normalized trivialization from
  ZeroHalfSpinorCharacter and its negative zero-bundle comparison. The
  positive isomorphism is fixed by the identity Spin(0) action on the
  vacuum, rather than inferred from the dimension of the associated line.
  Stage 2: retain the native projection and zero-section homeomorphism.
  Transport the original empty-boundary support triple along that map; the
  preceding bundle comparisons identify its class with the compact-base unit.
  The original class is not replaced before this comparison is established.
  Stage 3: in every suspension degree the actual graph action is transported
  along projection times the identity on the suspension coordinate. Tensoring
  with the same unit class is the identity, so this specific map is bijective.
  There is no swap of suspended factors or inference from degree zero alone.
  The empty-base case gives the unique map between zero groups. -/
  classical
  let e := zeroRankBundleProjectionHomeomorph E
  let : CompactSpace (TotalSpace RealModel E) := e.symm.compactSpace
  let p : C(TotalSpace RealModel E, B) :=
    ⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩
  let i : C(B, TotalSpace RealModel E) :=
    ⟨zeroSection RealModel E, Bundle.Trivialization.continuous_zeroSection ℝ⟩
  have hi : IsProperMap i := i.continuous.isProperMap
  let c : C(TotalSpace RealModel E, PUnit.{1}) :=
    ContinuousMap.const _ PUnit.unit
  have hc : IsProperMap c := c.continuous.isProperMap
  -- The vacuum-normalized associated line and the zero parity bundle fix the class.
  let := exteriorAlgebraNormedAddCommGroup (V := EuclideanSpace ℂ (Fin 0))
  let := exteriorAlgebraNormedSpace (V := EuclideanSpace ℂ (Fin 0))
  let (i : ZMod 2) (b : B) :=
    associatedVectorFiberAddCommGroup hP (complexSpinParityContRepresentation 0 i) b
  let (i : ZMod 2) (b : B) :=
    associatedVectorFiberModule hP (complexSpinParityContRepresentation 0 i) b
  let (i : ZMod 2) :=
    associatedVectorTotalTopology hP (complexSpinParityContRepresentation 0 i)
  let : ComplexBundle.IsFiniteRank (HalfSpinorBundle 0 hP 0) :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 0)
      (continuous_complexSpinParityRepresentation 0 0)
  let : ComplexBundle.IsFiniteRank (HalfSpinorBundle 0 hP 1) :=
    isFiniteRank_associatedVector hP (complexSpinParityContRepresentation 0 1)
      (continuous_complexSpinParityRepresentation 0 1)
  let := ComplexBundle.trivialTopology (X := B) 1
  let := ComplexBundle.trivialTopology (X := B) 0
  let := ComplexBundle.isFiniteRank_trivial (X := B) 1
  let := ComplexBundle.isFiniteRank_trivial (X := B) 0
  obtain ⟨j₀, _, _⟩ := existsUnique_halfSpinorBundle_zero_positive_trivial_iso hP
  obtain ⟨j₁⟩ := exists_halfSpinorBundle_zero_negative_trivial_iso hP
  have hclass : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback i hi (zeroSpinorThomClass E hP)) =
        kZeroClass C(B, ℂ) (IdempotentMatrix.identity C(B, ℂ) 1) := by
    rw [zeroSectionPullback_zeroSpinorThomClass E hP,
      ComplexBundle.kZeroClass_eq_of_iso j₀, ComplexBundle.kZeroClass_eq_of_iso j₁,
      ComplexBundle.kZeroClass_trivial, ComplexBundle.kZeroClass_trivial_zero, sub_zero]
  have hpoint : compactSupportKZeroToAbsolute compactSupportKZeroPointOne =
      kZeroClass C(PUnit.{1}, ℂ) (IdempotentMatrix.identity C(PUnit.{1}, ℂ) 1) :=
    (compactSupportKZeroCompactEquiv PUnit.{1}).apply_symm_apply _
  let q : C(B, PUnit.{1}) := c.comp i
  have hq : IsProperMap q := hc.comp hi
  have hfinite : compactSupportKZeroToAbsolute
      (compactSupportKZeroPullback q hq compactSupportKZeroPointOne) =
        complexKZeroPullback q
          (compactSupportKZeroToAbsolute compactSupportKZeroPointOne) := by
    change complexKZeroPullback
        ⟨((↑) : B → OnePoint B), OnePoint.continuous_coe⟩
        (complexKZeroPullback (properOnePointMap q hq) compactSupportKZeroPointOne.val) =
      complexKZeroPullback q
        (complexKZeroPullback
          ⟨((↑) : PUnit.{1} → OnePoint PUnit.{1}), OnePoint.continuous_coe⟩
          compactSupportKZeroPointOne.val)
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hunit : zeroSpinorThomClass E hP =
      compactSupportKZeroPullback c hc compactSupportKZeroPointOne := by
    apply (compactSupportKZeroHomeomorphEquiv e).injective
    apply compactSupportKZeroToAbsolute_bijective.1
    change compactSupportKZeroToAbsolute
        (compactSupportKZeroPullback i hi (zeroSpinorThomClass E hP)) =
      compactSupportKZeroToAbsolute (compactSupportKZeroPullback i hi
        (compactSupportKZeroPullback c hc compactSupportKZeroPointOne))
    have hcomp : compactSupportKZeroPullback i hi
        (compactSupportKZeroPullback c hc compactSupportKZeroPointOne) =
          compactSupportKZeroPullback q hq compactSupportKZeroPointOne :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp i c hi hc)
        compactSupportKZeroPointOne).symm
    rw [hclass, hcomp, hfinite, hpoint]
    symm
    change kZeroMap _ (kZeroClass _ _) = _
    rw [kZeroMap_class]
    congr 1
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact (ContinuousMap.compRightAlgHom ℂ ℂ q).toRingHom.mapMatrix.map_one
  -- In every degree, the original graph keeps the real suspension coordinate with B.
  let T := Fin n → ℝ
  let F : C((TotalSpace RealModel E) × T, (B × T) × TotalSpace RealModel E) :=
    (p.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
  let r : C((B × T) × TotalSpace RealModel E, (TotalSpace RealModel E) × T) :=
    ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
  have hF : IsProperMap F :=
    isProperMap_of_comp_of_t2 F.continuous r.continuous isProperMap_id
  let G : C((TotalSpace RealModel E) × T, B × T) := p.prodMap (ContinuousMap.id T)
  have hG : IsProperMap G := e.isProperMap.prodMap isProperMap_id
  have hI : IsProperMap (ContinuousMap.id (B × T)) := isProperMap_id
  let L : C((B × T) × TotalSpace RealModel E, (B × T) × PUnit.{1}) :=
    (ContinuousMap.id (B × T)).prodMap c
  have hL : IsProperMap L := hI.prodMap hc
  let j : C(B × T, (B × T) × PUnit.{1}) :=
    ⟨(Homeomorph.prodUnique (B × T) PUnit.{1}).symm,
      (Homeomorph.prodUnique (B × T) PUnit.{1}).symm.continuous⟩
  have hj : IsProperMap j := (Homeomorph.prodUnique (B × T) PUnit.{1}).symm.isProperMap
  have haction (a : CompactSupportK n B) :
      compactSupportKAction n p a (zeroSpinorThomClass E hP) =
        compactSupportKZeroPullback G hG a := by
    rw [hunit]
    have hproduct := compactSupportKZeroExternalProduct_properPullback
      (ContinuousMap.id (B × T)) hI c hc a compactSupportKZeroPointOne
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
    change compactSupportKZeroPullback F hF
        (compactSupportKZeroExternalProduct a
          (compactSupportKZeroPullback c hc compactSupportKZeroPointOne)) = _
    rw [← hproduct]
    let t := compactSupportKZeroExternalProduct a compactSupportKZeroPointOne
    calc
      compactSupportKZeroPullback F hF (compactSupportKZeroPullback L hL t) =
          compactSupportKZeroPullback (L.comp F) (hL.comp hF) t :=
        (DFunLike.congr_fun (compactSupportKZeroPullback_comp F L hF hL) t).symm
      _ = compactSupportKZeroPullback (j.comp G) (hj.comp hG) t := by rfl
      _ = compactSupportKZeroPullback G hG (compactSupportKZeroPullback j hj t) :=
        DFunLike.congr_fun (compactSupportKZeroPullback_comp G j hG hj) t
      _ = compactSupportKZeroPullback G hG a := by
        rw [show compactSupportKZeroPullback j hj t = a from
          compactSupportKZeroExternalProduct_one_right a]
  -- The graph map is exactly inverse transport along projection times the identity.
  have hmap : ((compactSupportKAction n p).flip (zeroSpinorThomClass E hP)) =
      compactSupportKZeroHomeomorph ((e.prodCongr (Homeomorph.refl T)).symm) := by
    apply AddMonoidHom.ext
    intro a
    exact haction a
  rw [hmap]
  exact compactSupportKZeroHomeomorph_bijective _

/-- The ordinary native rank-zero spin Thom homomorphism is bijective. -/
theorem zeroSpinThomHom_bijective : Function.Bijective (zeroSpinThomHom E hP) := by
  /- Stage 1: specialize the preceding all-degree assertion to degree zero.
  The fixed compactSupportKZeroDegreeEquiv maps identify the suspended graph
  with compactSupportKZeroAction by compactSupportKAction_zero.
  Stage 2: identify compactly supported K of B with ComplexKZero B through
  the original compact-base equivalence. The resulting map is exactly
  zeroSpinThomHom, with the original symbol class as its right factor.
  Composition with these specified equivalences preserves bijectivity. -/
  let p : C(TotalSpace RealModel E, B) :=
    ⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩
  let eB := compactSupportKZeroDegreeEquiv B
  let eE := compactSupportKZeroDegreeEquiv (TotalSpace RealModel E)
  let eC := compactSupportKZeroCompactEquiv B
  -- The specified degree-zero comparison recovers precisely the original base action.
  have hmap : (zeroSpinThomHom E hP :
      ComplexKZero B → CompactSupportKZero (TotalSpace RealModel E)) =
      fun a ↦ eE (compactSupportKAction 0 p (eB.symm (eC.symm a))
        (zeroSpinorThomClass E hP)) := by
    funext a
    rw [compactSupportKAction_zero]
    change compactSupportKZeroAction p (eC.symm a) (zeroSpinorThomClass E hP) =
      compactSupportKZeroAction p (eB (eB.symm (eC.symm a))) (zeroSpinorThomClass E hP)
    rw [eB.apply_symm_apply]
  -- Compose only these fixed equivalences with the already proved all-degree action.
  rw [hmap]
  exact eE.bijective.comp ((zeroSpinorThomClass_isKOrientation E hP 0).comp
    (eB.symm.bijective.comp eC.symm.bijective))

/-- The native rank-zero spin Thom equivalence retains the prescribed forward homomorphism. -/
def zeroSpinThomEquiv : ComplexKZero B ≃+ CompactSupportKZero (TotalSpace RealModel E) :=
  AddEquiv.ofBijective (zeroSpinThomHom E hP) (zeroSpinThomHom_bijective E hP)

end AtiyahSinger
