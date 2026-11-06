/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.GradedKProductNaturality
public import AtiyahSinger.Topology.KTheoryPairExact

/-!
# Closed-cover Mayer--Vietoris with a specified connecting map

Public module ID: M1918.

Karoubi II.4.18 uses the closed pairs (X,A) and (B,A ∩ B), identifying their
open complements when A ∪ B = X. The connecting map is the boundary of the
second pair followed by extension into X, with positive sign for the difference
map (a,b) ↦ a| - b|. All maps below preserve those actual inclusions.

The new suspension coordinate is first, as in KTheoryPairExact. The statements
hold for arbitrary locally compact Hausdorff X and a closed cover; no open-cover,
CW, cofibration, compact-base or proper-f assumption is inserted. The degree-zero
module compatibility retains the same original class under proper closed pullback.
All three exactness statements and the degree-zero boundary/action square are proved
below. Closed-cover gluing uses finite projective images on the actual suspended
one-point compactifications, with entrywise extension and elementary matrix shears.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The overlap as a subspace of B, retaining the original point and both memberships. -/
def mayerVietorisOverlapHomeomorph (A B : Set X) :
    (A ∩ B : Set X) ≃ₜ ((Subtype.val : B → X) ⁻¹' A) where
  toFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  invFun x := ⟨x.1.1, x.2, x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

/-- For a closed cover the complement in B is the same open complement in X. -/
def mayerVietorisComplementHomeomorph (A B : Set X) (hcover : A ∪ B = Set.univ) :
    (((Subtype.val : B → X) ⁻¹' A)ᶜ : Set B) ≃ₜ (Aᶜ : Set X) where
  toFun x := ⟨x.1.1, x.2⟩
  invFun x := ⟨⟨x.1, (show x.1 ∈ A ∪ B from hcover ▸ Set.mem_univ x.1).resolve_left x.2⟩,
    x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [LocallyCompactSpace X] [T2Space X] [LocallyCompactSpace Y] [T2Space Y]

/-- The two actual closed restrictions form the Mayer--Vietoris diagonal map. -/
def compactSupportKMayerVietorisRestriction (n : ℕ) (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) :
    letI := hA.locallyCompactSpace
    letI := hB.locallyCompactSpace
    CompactSupportK n X →+ CompactSupportK n A × CompactSupportK n B :=
  letI := hA.locallyCompactSpace
  letI := hB.locallyCompactSpace
  (compactSupportKClosedRestriction n A hA).prod (compactSupportKClosedRestriction n B hB)

/-- The overlap map is restriction from A minus restriction from B, in this order. -/
def compactSupportKMayerVietorisDifference (n : ℕ) (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) :
    letI := hA.locallyCompactSpace
    letI := hB.locallyCompactSpace
    letI := (hA.inter hB).locallyCompactSpace
    CompactSupportK n A × CompactSupportK n B →+ CompactSupportK n (A ∩ B : Set X) :=
  letI := hA.locallyCompactSpace
  letI := hB.locallyCompactSpace
  letI := (hA.inter hB).locallyCompactSpace
  let left : C((A ∩ B : Set X), A) :=
    ⟨fun x ↦ ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩
  let right : C((A ∩ B : Set X), B) :=
    ⟨fun x ↦ ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩
  (compactSupportKPullback n left
    (isProperMap_of_comp_of_t2 left.continuous continuous_subtype_val
      (hA.inter hB).isProperMap_subtypeVal)).comp (AddMonoidHom.fst _ _) -
    (compactSupportKPullback n right
      (isProperMap_of_comp_of_t2 right.continuous continuous_subtype_val
        (hA.inter hB).isProperMap_subtypeVal)).comp (AddMonoidHom.snd _ _)

/-- KA II.4.18: the positive zigzag boundary for the ordered closed cover (A,B). -/
def compactSupportKMayerVietorisBoundary (n : ℕ) (A B : Set X)
    (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = Set.univ) :
    letI := (hA.inter hB).locallyCompactSpace
    CompactSupportK (n + 1) (A ∩ B : Set X) →+ CompactSupportK n X :=
  letI := hB.locallyCompactSpace
  letI := (hA.inter hB).locallyCompactSpace
  letI := hA.isOpen_compl.locallyCompactSpace
  let C : Set B := Subtype.val ⁻¹' A
  let hC : IsClosed C := hA.preimage continuous_subtype_val
  letI := hC.locallyCompactSpace
  letI := hC.isOpen_compl.locallyCompactSpace
  (compactSupportKOpenExtension n Aᶜ hA.isOpen_compl).comp
    ((compactSupportKHomeomorphEquiv n
      (mayerVietorisComplementHomeomorph A B hcover)).toAddMonoidHom.comp
      ((compactSupportKBoundary n C hC).comp
        (compactSupportKHomeomorphEquiv (n + 1)
          (mayerVietorisOverlapHomeomorph A B)).toAddMonoidHom))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
-- The two literal cylinder charts retain their dependent subspace and properness witnesses.
/-- KA II.4.18: exactness at the suspended overlap. -/
theorem range_compactSupportKMayerVietorisDifference_eq_ker_boundary
    (n : ℕ) (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = Set.univ) :
    letI := hA.locallyCompactSpace
    letI := hB.locallyCompactSpace
    letI := (hA.inter hB).locallyCompactSpace
    (compactSupportKMayerVietorisDifference (n + 1) A B hA hB).range =
      (compactSupportKMayerVietorisBoundary n A B hA hB hcover).ker := by
  /- Stage 1: form the commuting pair sequences for (X,A) and (B,A ∩ B),
  identifying the complements by the specified point-preserving homeomorphism.
  Their boundaries use the same first suspension coordinate.
  Stage 2: chase the two exact rows. A difference of restricted classes maps
  to zero by the positive zigzag; conversely a class killed by that zigzag can
  be adjusted using the upper row to such a difference. This is II.4.18's
  actual diagram with v(a,b)=a|-b|, not an arbitrary connecting homomorphism. -/
  classical
  let := hA.locallyCompactSpace
  let := hB.locallyCompactSpace
  let := (hA.inter hB).locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let C : Set B := Subtype.val ⁻¹' A
  have hC : IsClosed C := hA.preimage continuous_subtype_val
  let := hC.locallyCompactSpace
  let := hC.isOpen_compl.locallyCompactSpace
  let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hi : IsProperMap i := hB.isProperMap_subtypeVal
  let := (hA.isOpen_compl.preimage i.continuous).locallyCompactSpace
  let j : C((Cᶜ : Set B), (Aᶜ : Set X)) := preimageSubspaceMap Aᶜ i
  have hj : IsProperMap j := isProperMap_preimageSubspaceMap Aᶜ i hi
  let k : C(C, A) := preimageSubspaceMap A i
  have hk : IsProperMap k := isProperMap_preimageSubspaceMap A i hi
  let overlap := mayerVietorisOverlapHomeomorph A B
  let oinv : C(C, (A ∩ B : Set X)) := ⟨overlap.symm, overlap.symm.continuous⟩
  let eO := compactSupportKHomeomorphEquiv (n + 1) overlap
  let e := mayerVietorisComplementHomeomorph A B hcover
  let H := compactSupportKHomeomorphEquiv n e
  let E := compactSupportKOpenExtension n Aᶜ hA.isOpen_compl
  let deltaA := compactSupportKBoundary n A hA
  let deltaC := compactSupportKBoundary n C hC
  let RC := compactSupportKClosedRestriction (n + 1) C hC
  let rA : C((A ∩ B : Set X), A) :=
    ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let rB : C((A ∩ B : Set X), B) :=
    ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hrA : IsProperMap rA := isProperMap_of_comp_of_t2 rA.continuous
    continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
  have hrB : IsProperMap rB := isProperMap_of_comp_of_t2 rB.continuous
    continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
  let L := compactSupportKPullback (n + 1) rA hrA
  let R := compactSupportKPullback (n + 1) rB hrB
  -- The proper closed inclusion lifts to the same literal cylinder, keeping height unchanged.
  let := locallyCompactSpace_boundaryCylinder A hA
  let := locallyCompactSpace_boundaryCylinder C hC
  let cylinderSet : Set (X × ℝ) :=
    {p | 0 ≤ p.2 ∧ p.2 < 1 ∧ (p.2 = 0 ∨ p.1 ∈ A)}
  let iR := i.prodMap (ContinuousMap.id ℝ)
  let F : C(BoundaryCylinder C, BoundaryCylinder A) := preimageSubspaceMap cylinderSet iR
  have hF : IsProperMap F :=
    isProperMap_preimageSubspaceMap cylinderSet iR (hi.prodMap isProperMap_id)
  let alphaA := compactSupportKBoundaryBase n A hA
  let alphaC := compactSupportKBoundaryBase n C hC
  let betaA := compactSupportKBoundaryTube n A hA
  let betaC := compactSupportKBoundaryTube n C hC
  -- Proper base change and the zero-height charts give the square for alpha.
  have halpha (a : CompactSupportK n (Aᶜ : Set X)) :
      compactSupportKPullback n F hF (alphaA a) =
        alphaC (compactSupportKPullback n j hj a) := by
    let UA := boundaryCylinderBaseOpen A
    let UC := boundaryCylinderBaseOpen C
    have hUA : IsOpen UA := isOpen_boundaryCylinderBaseOpen A hA
    have hUC : IsOpen UC := isOpen_boundaryCylinderBaseOpen C hC
    let := hUA.locallyCompactSpace
    let := hUC.locallyCompactSpace
    let := (hUA.preimage F.continuous).locallyCompactSpace
    let bA := boundaryCylinderBaseHomeomorph A
    let bC := boundaryCylinderBaseHomeomorph C
    let q : C(UC, UA) := preimageSubspaceMap UA F
    have hq : IsProperMap q := isProperMap_preimageSubspaceMap UA F hF
    have hcharts : compactSupportKPullback n q hq
        (compactSupportKHomeomorphEquiv n bA a) =
          compactSupportKHomeomorphEquiv n bC (compactSupportKPullback n j hj a) := by
      change compactSupportKPullback n q hq
        (compactSupportKPullback n ⟨bA.symm, bA.symm.continuous⟩ bA.symm.isProperMap a) =
          compactSupportKPullback n ⟨bC.symm, bC.symm.continuous⟩ bC.symm.isProperMap
            (compactSupportKPullback n j hj a)
      rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
      rfl
    have hbase := DFunLike.congr_fun (compactSupportKPullback_openExtension n UA hUA F hF)
      (compactSupportKHomeomorphEquiv n bA a)
    change compactSupportKPullback n F hF (alphaA a) =
      compactSupportKOpenExtension n UC hUC
        (compactSupportKPullback n q hq (compactSupportKHomeomorphEquiv n bA a)) at hbase
    exact hbase.trans (congrArg (compactSupportKOpenExtension n UC hUC) hcharts)
  -- Tube base change uses the fixed increasing height chart and the first real coordinate.
  have hbeta (a : CompactSupportK (n + 1) A) :
      compactSupportKPullback n F hF (betaA a) =
        betaC (compactSupportKPullback (n + 1) k hk a) := by
    let UA := boundaryCylinderTubeOpen A
    let UC := boundaryCylinderTubeOpen C
    have hUA : IsOpen UA := isOpen_boundaryCylinderTubeOpen A
    have hUC : IsOpen UC := isOpen_boundaryCylinderTubeOpen C
    let := hUA.locallyCompactSpace
    let := hUC.locallyCompactSpace
    let := (hUA.preimage F.continuous).locallyCompactSpace
    let bA := boundaryCylinderTubeHomeomorph A
    let bC := boundaryCylinderTubeHomeomorph C
    let q : C(UC, UA) := preimageSubspaceMap UA F
    have hq : IsProperMap q := isProperMap_preimageSubspaceMap UA F hF
    let kR := k.prodMap (ContinuousMap.id ℝ)
    have hkR : IsProperMap kR := hk.prodMap isProperMap_id
    let sA := compactSupportKZeroHomeomorphEquiv (suspensionCoordinateHomeomorph A n).symm
    let sC := compactSupportKZeroHomeomorphEquiv (suspensionCoordinateHomeomorph C n).symm
    have hsusp : compactSupportKPullback n kR hkR (sA a) =
        sC (compactSupportKPullback (n + 1) k hk a) := by
      change compactSupportKZeroPullback _ _ (compactSupportKZeroPullback _ _ a) =
        compactSupportKZeroPullback _ _ (compactSupportKZeroPullback _ _ a)
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      rfl
    have hcharts : compactSupportKPullback n q hq
        (compactSupportKHomeomorphEquiv n bA (sA a)) =
          compactSupportKHomeomorphEquiv n bC
            (compactSupportKPullback n kR hkR (sA a)) := by
      change compactSupportKPullback n q hq
        (compactSupportKPullback n ⟨bA.symm, bA.symm.continuous⟩ bA.symm.isProperMap _) =
          compactSupportKPullback n ⟨bC.symm, bC.symm.continuous⟩ bC.symm.isProperMap
            (compactSupportKPullback n kR hkR _)
      rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
      rfl
    have hbase := DFunLike.congr_fun (compactSupportKPullback_openExtension n UA hUA F hF)
      (compactSupportKHomeomorphEquiv n bA (sA a))
    change compactSupportKPullback n F hF (betaA a) =
      compactSupportKOpenExtension n UC hUC
        (compactSupportKPullback n q hq
          (compactSupportKHomeomorphEquiv n bA (sA a))) at hbase
    rw [hcharts, hsusp] at hbase
    exact hbase
  -- Invert exactly alpha, so the naturality square fixes the original boundary and its sign.
  have hspecA (a : CompactSupportK (n + 1) A) : alphaA (deltaA a) = betaA a :=
    (AddEquiv.ofBijective alphaA (compactSupportKBoundaryBase_bijective n A hA)).apply_symm_apply _
  have hspecC (a : CompactSupportK (n + 1) C) : alphaC (deltaC a) = betaC a :=
    (AddEquiv.ofBijective alphaC (compactSupportKBoundaryBase_bijective n C hC)).apply_symm_apply _
  have hnatural (a : CompactSupportK (n + 1) A) :
      compactSupportKPullback n j hj (deltaA a) =
        deltaC (compactSupportKPullback (n + 1) k hk a) := by
    apply (compactSupportKBoundaryBase_bijective n C hC).injective
    rw [← halpha, hspecA, hbeta, hspecC]
  -- Identify both overlap restrictions with the same actual inclusions in the lower row.
  have hleft (a : CompactSupportK (n + 1) A) :
      eO (L a) = compactSupportKPullback (n + 1) k hk a := by
    change compactSupportKPullback (n + 1) oinv overlap.symm.isProperMap
      (compactSupportKPullback (n + 1) rA hrA a) =
        compactSupportKPullback (n + 1) k hk a
    rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
    rfl
  have hright (b : CompactSupportK (n + 1) B) : eO (R b) = RC b := by
    change compactSupportKPullback (n + 1) oinv overlap.symm.isProperMap
      (compactSupportKPullback (n + 1) rB hrB b) =
        compactSupportKPullback (n + 1)
          ⟨Subtype.val, continuous_subtype_val⟩ hC.isProperMap_subtypeVal b
    rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
    rfl
  have hcancel (a : CompactSupportK n (Aᶜ : Set X)) :
      H (compactSupportKPullback n j hj a) = a := by
    change compactSupportKPullback n ⟨e.symm, e.symm.continuous⟩ e.symm.isProperMap
      (compactSupportKPullback n j hj a) = a
    rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
    have hid : j.comp ⟨e.symm, e.symm.continuous⟩ = ContinuousMap.id (Aᶜ : Set X) := by
      ext x
      rfl
    simp only [hid, compactSupportKPullback_id, AddMonoidHom.id_apply]
  have hboundaryLeft (a : CompactSupportK (n + 1) A) :
      H (deltaC (eO (L a))) = deltaA a := by
    rw [hleft, ← hnatural, hcancel]
  have hpairA : deltaA.range = E.ker :=
    range_compactSupportKBoundary_eq_ker_openExtension n A hA
  have hpairC : RC.range = deltaC.ker :=
    range_compactSupportKClosedRestriction_eq_ker_boundary n C hC
  -- The two exact rows now give both inclusions for the ordered difference a| - b|.
  apply le_antisymm
  · rintro x ⟨⟨a, b⟩, rfl⟩
    change E (H (deltaC (eO (L a - R b)))) = 0
    rw [map_sub, map_sub, map_sub, map_sub, hboundaryLeft]
    have hb : deltaC (eO (R b)) = 0 := hpairC.le ⟨b, (hright b).symm⟩
    rw [hb, map_zero, map_zero, sub_zero]
    exact hpairA.le ⟨a, rfl⟩
  · intro x hx
    have hx0 : E (H (deltaC (eO x))) = 0 := hx
    obtain ⟨a, ha⟩ := hpairA.ge hx0
    have hrem : deltaC (eO (x - L a)) = 0 := by
      apply H.injective
      rw [map_zero, map_sub, map_sub, map_sub, hboundaryLeft, ha, sub_self]
    obtain ⟨b, hb⟩ := hpairC.ge hrem
    refine ⟨(a, -b), ?_⟩
    change L a - R (-b) = x
    have hsame : R b = x - L a := by
      apply eO.injective
      exact (hright b).trans hb
    rw [map_neg, sub_neg_eq_add, hsame]
    abel

/-- KA II.4.18: exactness at the union, represented by the original ambient X. -/
theorem range_compactSupportKMayerVietorisBoundary_eq_ker_restriction
    (n : ℕ) (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = Set.univ) :
    letI := hA.locallyCompactSpace
    letI := hB.locallyCompactSpace
    letI := (hA.inter hB).locallyCompactSpace
    (compactSupportKMayerVietorisBoundary n A B hA hB hcover).range =
      (compactSupportKMayerVietorisRestriction n A B hA hB).ker := by
  /- Stage 1: the boundary extends from X ∖ A, so its restriction to A is zero.
  Its restriction to B is zero by the exact sequence of (B,A ∩ B).
  Stage 2: if a class restricts to zero on both pieces, pair exactness for (X,A)
  lifts it to the common complement. Its zero restriction to B and exactness
  for (B,A ∩ B) then lift that complement class to the suspended overlap. -/
  classical
  let := hA.locallyCompactSpace
  let := hB.locallyCompactSpace
  let := (hA.inter hB).locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let C : Set B := Subtype.val ⁻¹' A
  have hC : IsClosed C := hA.preimage continuous_subtype_val
  let := hC.locallyCompactSpace
  let := hC.isOpen_compl.locallyCompactSpace
  let eO := compactSupportKHomeomorphEquiv (n + 1) (mayerVietorisOverlapHomeomorph A B)
  let e := mayerVietorisComplementHomeomorph A B hcover
  let H := compactSupportKHomeomorphEquiv n e
  let E := compactSupportKOpenExtension n Aᶜ hA.isOpen_compl
  let F := compactSupportKOpenExtension n Cᶜ hC.isOpen_compl
  let RA := compactSupportKClosedRestriction n A hA
  let RB := compactSupportKClosedRestriction n B hB
  let delta := compactSupportKBoundary n C hC
  have hpairX : E.range = RA.ker :=
    range_compactSupportKOpenExtension_eq_ker_closedRestriction n A hA
  have hpairB : delta.range = F.ker :=
    range_compactSupportKBoundary_eq_ker_openExtension n C hC
  -- Proper restriction of the ambient complement is the same point-preserving chart.
  have hres (c : CompactSupportK n (Cᶜ : Set B)) : RB (E (H c)) = F c := by
    let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : IsProperMap i := hB.isProperMap_subtypeVal
    let := (hA.isOpen_compl.preimage i.continuous).locallyCompactSpace
    let j : C((Cᶜ : Set B), (Aᶜ : Set X)) := preimageSubspaceMap Aᶜ i
    have hj : IsProperMap j := isProperMap_preimageSubspaceMap Aᶜ i hi
    let k : C((Aᶜ : Set X), (Cᶜ : Set B)) := ⟨e.symm, e.symm.continuous⟩
    have hk : IsProperMap k := e.symm.isProperMap
    have hcomp : k.comp j = ContinuousMap.id (Cᶜ : Set B) := by
      ext z
      rfl
    have hcancel : compactSupportKPullback n j hj (H c) = c := by
      change compactSupportKPullback n j hj (compactSupportKPullback n k hk c) = c
      rw [← AddMonoidHom.comp_apply, ← compactSupportKPullback_comp]
      simp only [hcomp, compactSupportKPullback_id, AddMonoidHom.id_apply]
    have hbase := DFunLike.congr_fun
      (compactSupportKPullback_openExtension n Aᶜ hA.isOpen_compl i hi) (H c)
    change RB (E (H c)) = F (compactSupportKPullback n j hj (H c)) at hbase
    exact hbase.trans (congrArg F hcancel)
  apply le_antisymm
  · rintro x ⟨a, rfl⟩
    change (RA (E (H (delta (eO a)))), RB (E (H (delta (eO a))))) = (0, 0)
    apply Prod.ext
    · exact hpairX.le ⟨H (delta (eO a)), rfl⟩
    · change RB (E (H (delta (eO a)))) = 0
      rw [hres]
      exact hpairB.le ⟨eO a, rfl⟩
  · intro x hx
    have hzero : (RA x, RB x) = (0, 0) := hx
    have hxA : RA x = 0 := congrArg Prod.fst hzero
    have hxB : RB x = 0 := congrArg Prod.snd hzero
    obtain ⟨c, hc⟩ := hpairX.ge hxA
    let b := H.symm c
    have hb : H b = c := H.apply_symm_apply c
    have hF : F b = 0 := by
      rw [← hres, hb, hc]
      exact hxB
    obtain ⟨aC, haC⟩ := hpairB.ge hF
    refine ⟨eO.symm aC, ?_⟩
    change E (H (delta (eO (eO.symm aC)))) = x
    rw [eO.apply_symm_apply, haC, hb, hc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
-- The matrix gluing keeps the original dependent subspaces and suspension witnesses.
open OnePoint Topology in
/-- KA II.4.18: compatible classes on a closed cover glue in every nonpositive degree. -/
theorem range_compactSupportKMayerVietorisRestriction_eq_ker_difference
    (n : ℕ) (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = Set.univ) :
    letI := hA.locallyCompactSpace
    letI := hB.locallyCompactSpace
    letI := (hA.inter hB).locallyCompactSpace
    (compactSupportKMayerVietorisRestriction n A B hA hB).range =
      (compactSupportKMayerVietorisDifference n A B hA hB).ker := by
  /- Stage 1: use the actual closed cover of the suspended one-point compactification.
  Continuous entries descend along its quotient map, and entries of the overlap
  isomorphism extend to one closed piece. Globally invertible elementary shears
  conjugate stabilized projections so that their overlap matrices agree.
  Stage 2: equalize the negative trivial summands of the two virtual classes.
  Their positive overlap classes admit a common free stabilization; the matrix
  gluing construction gives one idempotent on the original compactification.
  Stage 3: subtract the same trivial class and check evaluation at the shared
  infinity. This produces a supported class with the two prescribed restrictions,
  also when a cover member is empty. -/
  classical
  let := hA.locallyCompactSpace
  let := hB.locallyCompactSpace
  let := (hA.inter hB).locallyCompactSpace
  let V := Fin n → ℝ
  let Z := OnePoint (X × V)
  let ZA := OnePoint (A × V)
  let ZB := OnePoint (B × V)
  let ZO := OnePoint ((A ∩ B : Set X) × V)
  let iA : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iB : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let oA : C((A ∩ B : Set X), A) :=
    ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩
  let oB : C((A ∩ B : Set X), B) :=
    ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩
  have hoA : IsProperMap oA := isProperMap_of_comp_of_t2 oA.continuous
    continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
  have hoB : IsProperMap oB := isProperMap_of_comp_of_t2 oB.continuous
    continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
  let jA : C(ZA, Z) := properOnePointMap (iA.prodMap (ContinuousMap.id V))
    (hA.isProperMap_subtypeVal.prodMap isProperMap_id)
  let jB : C(ZB, Z) := properOnePointMap (iB.prodMap (ContinuousMap.id V))
    (hB.isProperMap_subtypeVal.prodMap isProperMap_id)
  let s : C(ZO, ZA) := properOnePointMap (oA.prodMap (ContinuousMap.id V))
    (hoA.prodMap isProperMap_id)
  let t : C(ZO, ZB) := properOnePointMap (oB.prodMap (ContinuousMap.id V))
    (hoB.prodMap isProperMap_id)
  -- These are the literal suspended closed inclusions, extended by the same infinity.
  have hjAinj : Function.Injective jA := by
    apply Option.map_injective
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    change (x.val, v) = (y.val, w) at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun z : X × V ↦ z.2) h)
  have hjBinj : Function.Injective jB := by
    apply Option.map_injective
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    change (x.val, v) = (y.val, w) at h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h))
      (congrArg (fun z : X × V ↦ z.2) h)
  have hsinj : Function.Injective s := by
    apply Option.map_injective
    rintro ⟨x, v⟩ ⟨y, w⟩ h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun z : A × V ↦ z.1.val) h)
    · exact congrArg (fun z : A × V ↦ z.2) h
  have hs : IsClosedEmbedding s := s.continuous.isClosedEmbedding hsinj
  have hcomm : jA.comp s = jB.comp t := by
    ext z
    cases z using OnePoint.rec <;> rfl
  let cover : ZA ⊕ ZB → Z := Sum.elim jA jB
  have hcoverSurj : Function.Surjective cover := by
    intro z
    cases z using OnePoint.rec with
    | infty => exact ⟨Sum.inl ∞, rfl⟩
    | coe p =>
      rcases (show p.1 ∈ A ∪ B from hcover ▸ Set.mem_univ p.1) with ha | hb
      · exact ⟨Sum.inl (((⟨p.1, ha⟩, p.2) : A × V) : ZA), rfl⟩
      · exact ⟨Sum.inr (((⟨p.1, hb⟩, p.2) : B × V) : ZB), rfl⟩
  have hquot : Topology.IsQuotientMap cover :=
    .of_surjective_continuous hcoverSurj (jA.continuous.sumElim jB.continuous)
  have hoverlap (a : ZA) (b : ZB) (h : jA a = jB b) :
      ∃ o : ZO, s o = a ∧ t o = b := by
    cases a using OnePoint.rec with
    | infty =>
      cases b using OnePoint.rec with
      | infty => exact ⟨∞, rfl, rfl⟩
      | coe b => exact False.elim (OnePoint.infty_ne_coe _ h)
    | coe a =>
      cases b using OnePoint.rec with
      | infty => exact False.elim (OnePoint.coe_ne_infty _ h)
      | coe b =>
        rcases a with ⟨⟨x, hx⟩, v⟩
        rcases b with ⟨⟨y, hy⟩, w⟩
        obtain ⟨hxy, hvw⟩ := Prod.mk.inj (OnePoint.coe_injective h)
        change x = y at hxy
        change v = w at hvw
        subst y
        subst w
        exact ⟨(((⟨x, hx, hy⟩, v) : (A ∩ B : Set X) × V) : ZO), rfl, rfl⟩
  let φA : C(Z, ℂ) →+* C(ZA, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ jA).toRingHom
  let φB : C(Z, ℂ) →+* C(ZB, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ jB).toRingHom
  let ψA : C(ZA, ℂ) →+* C(ZO, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ s).toRingHom
  let ψB : C(ZB, ℂ) →+* C(ZO, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ t).toRingHom
  -- Continuous entries descend along the actual compact closed cover, including infinity.
  have descend (f : C(ZA, ℂ)) (g : C(ZB, ℂ)) (hfg : f.comp s = g.comp t) :
      ∃ F : C(Z, ℂ), F.comp jA = f ∧ F.comp jB = g := by
    let G : ZA ⊕ ZB → ℂ := Sum.elim f g
    have hG (a b : ZA ⊕ ZB) (h : cover a = cover b) : G a = G b := by
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg f (hjAinj h)
        | inr b =>
          obtain ⟨o, rfl, rfl⟩ := hoverlap a b h
          exact congrArg (fun u : C(ZO, ℂ) ↦ u o) hfg
      | inr a =>
        cases b with
        | inl b =>
          obtain ⟨o, rfl, rfl⟩ := hoverlap b a h.symm
          exact (congrArg (fun u : C(ZO, ℂ) ↦ u o) hfg).symm
        | inr b => exact congrArg g (hjBinj h)
    let F : Z → ℂ := fun z ↦ G (Function.surjInv hcoverSurj z)
    have hF (a : ZA ⊕ ZB) : F (cover a) = G a :=
      hG _ _ (Function.surjInv_eq hcoverSurj (cover a))
    have hFc : Continuous F := hquot.continuous_iff.mpr (by
      rw [show F ∘ cover = G from funext hF]
      exact f.continuous.sumElim g.continuous)
    refine ⟨⟨F, hFc⟩, ?_, ?_⟩
    · ext a
      exact hF (Sum.inl a)
    · ext b
      exact hF (Sum.inr b)
  have hfactor {R : Type _} [CommRing R] (p q : IdempotentMatrix R)
      (M : Matrix (Fin p.size) (Fin q.size) R)
      (N : Matrix (Fin q.size) (Fin p.size) R)
      (hMN : M * N = p.matrix) (hNM : N * M = q.matrix) : p.IsEquivalent q := by
    have hMq : M * q.matrix = p.matrix * M := by
      rw [← hNM, ← Matrix.mul_assoc, hMN]
    have hNp : N * p.matrix = q.matrix * N := by
      rw [← hMN, ← Matrix.mul_assoc, hNM]
    refine ⟨p.matrix * M, q.matrix * N, ?_, ?_, ?_, ?_⟩
    · calc
        _ = p.matrix * (M * q.matrix) * N := by simp only [Matrix.mul_assoc]
        _ = p.matrix * (p.matrix * M) * N := by rw [hMq]
        _ = p.matrix := by
          rw [← Matrix.mul_assoc p.matrix p.matrix, p.mul_self,
            Matrix.mul_assoc, hMN, p.mul_self]
    · calc
        _ = q.matrix * (N * p.matrix) * M := by simp only [Matrix.mul_assoc]
        _ = q.matrix * (q.matrix * N) * M := by rw [hNp]
        _ = q.matrix := by
          rw [← Matrix.mul_assoc q.matrix q.matrix, q.mul_self,
            Matrix.mul_assoc, hNM, q.mul_self]
    · rw [← Matrix.mul_assoc, p.mul_self]
    · rw [← Matrix.mul_assoc, q.mul_self]
  -- Entrywise extensions and globally invertible shears glue the overlap projective images.
  have glue (p : IdempotentMatrix C(ZA, ℂ)) (q : IdempotentMatrix C(ZB, ℂ))
      (he : (p.map ψA).IsEquivalent (q.map ψB)) :
      ∃ r : IdempotentMatrix C(Z, ℂ),
        (r.map φA).IsEquivalent p ∧ (r.map φB).IsEquivalent q := by
    obtain ⟨Ba, La, hBaLa, hLaBa, hPBa, hQLa⟩ := he
    dsimp only [IdempotentMatrix.map] at Ba La hBaLa hLaBa hPBa hQLa
    change Ba * La = p.matrix.map ψA at hBaLa
    change La * Ba = q.matrix.map ψB at hLaBa
    change p.matrix.map ψA * Ba = Ba at hPBa
    change q.matrix.map ψB * La = La at hQLa
    choose Bc hBc using fun i j ↦ (Ba i j).exists_extension hs
    choose Lc hLc using fun i j ↦ (La i j).exists_extension hs
    have hψB : Matrix.map Bc ψA = Ba := by
      ext i j z
      exact congrArg (fun f : C(ZO, ℂ) ↦ f z) (hBc i j)
    have hψL : Matrix.map Lc ψA = La := by
      ext i j z
      exact congrArg (fun f : C(ZO, ℂ) ↦ f z) (hLc i j)
    let S : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZA, ℂ) :=
      Matrix.fromBlocks 1 (-Bc) 0 1
    let T : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZA, ℂ) :=
      Matrix.fromBlocks 1 0 Lc 1
    let S' : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZA, ℂ) :=
      Matrix.fromBlocks 1 Bc 0 1
    let T' : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZA, ℂ) :=
      Matrix.fromBlocks 1 0 (-Lc) 1
    let U := S * T * S
    let W := S' * T' * S'
    have hSS : S * S' = 1 := by
      simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hS'S : S' * S = 1 := by
      simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hTT : T * T' = 1 := by
      simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hT'T : T' * T = 1 := by
      simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
    have hUW : U * W = 1 := by
      change (S * T * S) * (S' * T' * S') = 1
      calc
        _ = S * T * (S * S') * T' * S' := by noncomm_ring
        _ = 1 := by rw [hSS, mul_one, mul_assoc S T T', hTT, mul_one, hSS]
    have hWU : W * U = 1 := by
      change (S' * T' * S') * (S * T * S) = 1
      calc
        _ = S' * T' * (S' * S) * T * S := by noncomm_ring
        _ = 1 := by rw [hS'S, mul_one, mul_assoc S' T' T, hT'T, mul_one, hS'S]
    let P₀ : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZA, ℂ) :=
      Matrix.fromBlocks p.matrix 0 0 0
    let Q₀ : Matrix (Fin p.size ⊕ Fin q.size) (Fin p.size ⊕ Fin q.size) C(ZB, ℂ) :=
      Matrix.fromBlocks 0 0 0 q.matrix
    have hP₀ : P₀ * P₀ = P₀ := by
      simp [P₀, Matrix.fromBlocks_multiply, p.mul_self]
    have hQ₀ : Q₀ * Q₀ = Q₀ := by
      simp [Q₀, Matrix.fromBlocks_multiply, q.mul_self]
    have hLaP : La * (p.matrix.map ψA) = La := by
      calc
        La * (p.matrix.map ψA) = La * (Ba * La) := congrArg (La * ·) hBaLa.symm
        _ = (La * Ba) * La := (Matrix.mul_assoc _ _ _).symm
        _ = La := by rw [hLaBa, hQLa]
    have hPψ : p.matrix.map ψA * p.matrix.map ψA = p.matrix.map ψA :=
      (p.map ψA).mul_self
    have hQψ : q.matrix.map ψB * q.matrix.map ψB = q.matrix.map ψB :=
      (q.map ψB).mul_self
    have hSmap : ψA.mapMatrix S = Matrix.fromBlocks 1 (-Ba) 0 1 := by
      ext i j
      cases i <;> cases j <;> simp [S, RingHom.mapMatrix_apply, Matrix.fromBlocks,
        ← hψB, Matrix.map_apply, Matrix.one_apply]
    have hTmap : ψA.mapMatrix T = Matrix.fromBlocks 1 0 La 1 := by
      ext i j
      cases i <;> cases j <;> simp [T, RingHom.mapMatrix_apply, Matrix.fromBlocks,
        ← hψL, Matrix.map_apply, Matrix.one_apply]
    have hPmap : ψA.mapMatrix P₀ = Matrix.fromBlocks (p.matrix.map ψA) 0 0 0 := by
      ext i j
      cases i <;> cases j <;> simp [P₀, RingHom.mapMatrix_apply, Matrix.fromBlocks]
    have hQmap : ψB.mapMatrix Q₀ = Matrix.fromBlocks 0 0 0 (q.matrix.map ψB) := by
      ext i j
      cases i <;> cases j <;> simp [Q₀, RingHom.mapMatrix_apply, Matrix.fromBlocks]
    have hrestrict : ψA.mapMatrix (U * P₀ * W) = ψB.mapMatrix Q₀ := by
      have hUa : ψA.mapMatrix U = Matrix.fromBlocks
          (1 - p.matrix.map ψA) (-Ba) La (1 - q.matrix.map ψB) := by
        simp only [U, map_mul, hSmap, hTmap, Matrix.fromBlocks_multiply,
          Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul,
          Matrix.mul_neg, hBaLa, hLaBa]
        congr 1
        · simp [Matrix.add_mul, Matrix.neg_mul, hPBa]
        · abel
      have hi : ψA.mapMatrix U * ψA.mapMatrix P₀ =
          ψB.mapMatrix Q₀ * ψA.mapMatrix U := by
        rw [hUa, hPmap, hQmap]
        simp [Matrix.fromBlocks_multiply, Matrix.sub_mul, Matrix.mul_sub,
          hPψ, hQψ, hLaP, hQLa]
      rw [map_mul, map_mul, hi, mul_assoc, ← map_mul, hUW, map_one, mul_one]
    let reindexA := Matrix.reindexRingEquiv C(ZA, ℂ)
      (finSumFinEquiv (m := p.size) (n := q.size))
    let reindexB := Matrix.reindexRingEquiv C(ZB, ℂ)
      (finSumFinEquiv (m := p.size) (n := q.size))
    let Rl := reindexA (U * P₀ * W)
    let Rr := reindexB Q₀
    have hRl : Rl * Rl = Rl := by
      dsimp only [Rl]
      rw [← map_mul]
      apply congrArg reindexA
      calc
        _ = U * P₀ * (W * U) * P₀ * W := by noncomm_ring
        _ = U * P₀ * W := by rw [hWU, mul_one, mul_assoc U P₀ P₀, hP₀]
    have hRr : Rr * Rr = Rr := by
      dsimp only [Rr]
      rw [← map_mul, hQ₀]
    have hseam (i j) : (Rl i j).comp s = (Rr i j).comp t := by
      ext o
      exact congrArg (fun M ↦ M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) o)
        hrestrict
    choose D hDA hDB using fun i j ↦ descend (Rl i j) (Rr i j) (hseam i j)
    let Dm : Matrix (Fin (p.size + q.size)) (Fin (p.size + q.size)) C(Z, ℂ) := D
    have hDmapA : φA.mapMatrix Dm = Rl := by
      ext i j z
      exact congrArg (fun f : C(ZA, ℂ) ↦ f z) (hDA i j)
    have hDmapB : φB.mapMatrix Dm = Rr := by
      ext i j z
      exact congrArg (fun f : C(ZB, ℂ) ↦ f z) (hDB i j)
    have hD : Dm * Dm = Dm := by
      have ha : φA.mapMatrix (Dm * Dm) = φA.mapMatrix Dm := by
        rw [map_mul, hDmapA, hRl]
      have hb : φB.mapMatrix (Dm * Dm) = φB.mapMatrix Dm := by
        rw [map_mul, hDmapB, hRr]
      ext i j z
      obtain ⟨a | b, rfl⟩ := hcoverSurj z
      · exact congrArg (fun M ↦ M i j a) ha
      · exact congrArg (fun M ↦ M i j b) hb
    let r : IdempotentMatrix C(Z, ℂ) :=
      { size := p.size + q.size
        matrix := Dm
        mul_self := hD }
    have hrA : (r.map φA).matrix = Rl := hDmapA
    have hrB : (r.map φB).matrix = Rr := hDmapB
    let Ml : Matrix (Fin (p.size + q.size)) (Fin p.size) C(ZA, ℂ) :=
      (U * Matrix.fromRows p.matrix (0 : Matrix (Fin q.size) (Fin p.size) C(ZA, ℂ))).submatrix
        finSumFinEquiv.symm id
    let Nl : Matrix (Fin p.size) (Fin (p.size + q.size)) C(ZA, ℂ) :=
      (Matrix.fromCols p.matrix (0 : Matrix (Fin p.size) (Fin q.size) C(ZA, ℂ)) * W).submatrix
        id finSumFinEquiv.symm
    let Mr : Matrix (Fin (p.size + q.size)) (Fin q.size) C(ZB, ℂ) :=
      (Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) C(ZB, ℂ)) q.matrix).submatrix
        finSumFinEquiv.symm id
    let Nr : Matrix (Fin q.size) (Fin (p.size + q.size)) C(ZB, ℂ) :=
      (Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) C(ZB, ℂ)) q.matrix).submatrix
        id finSumFinEquiv.symm
    have hNlMl : Nl * Ml = p.matrix := by
      dsimp only [Nl, Ml]
      rw [Matrix.submatrix_mul_equiv]
      have hc : (Matrix.fromCols p.matrix (0 : Matrix (Fin p.size) (Fin q.size) C(ZA, ℂ)) *
          W) * (U * Matrix.fromRows p.matrix 0) = p.matrix := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc W, hWU, Matrix.one_mul,
          Matrix.fromCols_mul_fromRows, p.mul_self, Matrix.zero_mul, add_zero]
      rw [hc]
      rfl
    have hMlNl : Ml * Nl = (r.map φA).matrix := by
      rw [hrA]
      change (U * Matrix.fromRows p.matrix (0 : Matrix (Fin q.size) (Fin p.size)
        C(ZA, ℂ))).submatrix finSumFinEquiv.symm id *
        (Matrix.fromCols p.matrix (0 : Matrix (Fin p.size) (Fin q.size) C(ZA, ℂ)) *
          W).submatrix id finSumFinEquiv.symm =
            (U * P₀ * W).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
      erw [Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin p.size))]
      congr 1
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.fromRows _ _),
        Matrix.fromRows_mul_fromCols, p.mul_self]
      simp [P₀, Matrix.mul_assoc]
    have hNrMr : Nr * Mr = q.matrix := by
      dsimp only [Nr, Mr]
      rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows,
        Matrix.zero_mul, zero_add, q.mul_self]
      rfl
    have hMrNr : Mr * Nr = (r.map φB).matrix := by
      rw [hrB]
      have hm : Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) C(ZB, ℂ)) q.matrix *
          Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) C(ZB, ℂ)) q.matrix = Q₀ := by
        rw [Matrix.fromRows_mul_fromCols]
        simp only [Matrix.mul_zero, Matrix.zero_mul, q.mul_self]
        rfl
      change (Matrix.fromRows (0 : Matrix (Fin p.size) (Fin q.size) C(ZB, ℂ))
        q.matrix).submatrix finSumFinEquiv.symm (Equiv.refl (Fin q.size)) *
        (Matrix.fromCols (0 : Matrix (Fin q.size) (Fin p.size) C(ZB, ℂ))
          q.matrix).submatrix (Equiv.refl (Fin q.size)) finSumFinEquiv.symm =
            Q₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
      exact (Matrix.submatrix_mul_equiv _ _ _ (Equiv.refl (Fin q.size)) _).trans
        (congrArg (fun v ↦ v.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) hm)
    exact ⟨r, hfactor _ _ Ml Nl hMlNl hNlMl, hfactor _ _ Mr Nr hMrNr hNrMr⟩
  have hmapblock {R S : Type _} [CommRing R] [CommRing S] (φ : R →+* S)
      (p q : IdempotentMatrix R) :
      (p.blockSum q).map φ = (p.map φ).blockSum (q.map φ) := by
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.blockSum]
    congr 1
    ext i j
    simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
  have hmapid {R S : Type _} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
      (IdempotentMatrix.identity R k).map φ = IdempotentMatrix.identity S k := by
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact map_one φ.mapMatrix
  have hfree {R : Type _} [CommRing R] (m k : ℕ) :
      kZeroClass R (IdempotentMatrix.identity R (m + k)) =
        kZeroClass R (IdempotentMatrix.identity R m) +
          kZeroClass R (IdempotentMatrix.identity R k) := by
    have hmatrix : (IdempotentMatrix.identity R m).blockSum
        (IdempotentMatrix.identity R k) = IdempotentMatrix.identity R (m + k) := by
      dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
      congr 1
      simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
    rw [← hmatrix, kZeroClass_blockSum]
  apply le_antisymm
  · rintro x ⟨c, rfl⟩
    change compactSupportKPullback n oA hoA (compactSupportKClosedRestriction n A hA c) -
      compactSupportKPullback n oB hoB (compactSupportKClosedRestriction n B hB c) = 0
    apply sub_eq_zero.mpr
    apply Subtype.ext
    change complexKZeroPullback s (complexKZeroPullback jA c.val) =
      complexKZeroPullback t (complexKZeroPullback jB c.val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hcomm]
  rintro ⟨a, b⟩ hab
  have hab' : kZeroMap ψA a.val = kZeroMap ψB b.val := by
    change compactSupportKPullback n oA hoA a - compactSupportKPullback n oB hoB b = 0 at hab
    exact congrArg Subtype.val (sub_eq_zero.mp hab)
  -- Equalize the negative trivial summands before using the effective stable isomorphism.
  obtain ⟨p, m, hp⟩ := ComplexBundle.exists_class_sub_trivial a.val
  obtain ⟨q, k, hq⟩ := ComplexBundle.exists_class_sub_trivial b.val
  rw [ComplexBundle.kZeroClass_image, ComplexBundle.kZeroClass_trivial] at hp hq
  let p₀ := p.blockSum (IdempotentMatrix.identity C(ZA, ℂ) k)
  let q₀ := q.blockSum (IdempotentMatrix.identity C(ZB, ℂ) m)
  have ha₀ : a.val = kZeroClass C(ZA, ℂ) p₀ -
      kZeroClass C(ZA, ℂ) (IdempotentMatrix.identity C(ZA, ℂ) (m + k)) := by
    dsimp only [p₀]
    rw [kZeroClass_blockSum, hfree, hp]
    abel
  have hb₀ : b.val = kZeroClass C(ZB, ℂ) q₀ -
      kZeroClass C(ZB, ℂ) (IdempotentMatrix.identity C(ZB, ℂ) (m + k)) := by
    dsimp only [q₀]
    rw [kZeroClass_blockSum, hfree, hq]
    abel
  have heq : kZeroClass C(ZO, ℂ) (p₀.map ψA) =
      kZeroClass C(ZO, ℂ) (q₀.map ψB) := by
    rw [ha₀, hb₀, map_sub, map_sub, kZeroMap_class, kZeroMap_class,
      kZeroMap_class, kZeroMap_class, hmapid, hmapid] at hab'
    exact sub_left_inj.mp hab'
  obtain ⟨d, hd⟩ := IdempotentMatrix.exists_isEquivalent_stabilization_of_kZeroClass_eq
    (p₀.map ψA) (q₀.map ψB) heq
  let P := p₀.blockSum (IdempotentMatrix.identity C(ZA, ℂ) d)
  let Q := q₀.blockSum (IdempotentMatrix.identity C(ZB, ℂ) d)
  have hPQ : (P.map ψA).IsEquivalent (Q.map ψB) := by
    dsimp only [P, Q]
    rw [hmapblock ψA p₀ (IdempotentMatrix.identity C(ZA, ℂ) d),
      hmapblock ψB q₀ (IdempotentMatrix.identity C(ZB, ℂ) d), hmapid ψA d, hmapid ψB d]
    exact hd
  obtain ⟨r, hrA, hrB⟩ := glue P Q hPQ
  let c : ComplexKZero Z := kZeroClass C(Z, ℂ) r -
    kZeroClass C(Z, ℂ) (IdempotentMatrix.identity C(Z, ℂ) (m + k + d))
  have hca : complexKZeroPullback jA c = a.val := by
    change kZeroMap φA c = a.val
    dsimp only [c]
    rw [map_sub, kZeroMap_class, kZeroMap_class, hmapid,
      kZeroClass_eq_of_isEquivalent _ _ hrA]
    dsimp only [P]
    rw [kZeroClass_blockSum, hfree, ha₀]
    abel
  have hcb : complexKZeroPullback jB c = b.val := by
    change kZeroMap φB c = b.val
    dsimp only [c]
    rw [map_sub, kZeroMap_class, kZeroMap_class, hmapid,
      kZeroClass_eq_of_isEquivalent _ _ hrB]
    dsimp only [Q]
    rw [kZeroClass_blockSum, hfree, hb₀]
    abel
  -- Infinity is shared even for an empty piece; its evaluation is the original reduced condition.
  have hc : c ∈ reducedComplexKZero (∞ : Z) := by
    have heval : (ContinuousMap.evalAlgHom ℂ ℂ (∞ : ZA)).toRingHom.comp φA =
        (ContinuousMap.evalAlgHom ℂ ℂ (∞ : Z)).toRingHom := by
      ext f
      rfl
    have ha : kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : ZA)).toRingHom
        (complexKZeroPullback jA c) = 0 := hca ▸ a.property
    change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : Z)).toRingHom c = 0
    change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (∞ : ZA)).toRingHom
      (kZeroMap φA c) = 0 at ha
    rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp, heval] at ha
    exact ha
  refine ⟨⟨c, hc⟩, Prod.ext ?_ ?_⟩
  · exact Subtype.ext hca
  · exact Subtype.ext hcb

set_option maxHeartbeats 2000000 in

open Topology in
/-- The same degree-zero graph action commutes with the specified closed-cover boundary. -/
theorem compactSupportKAction_mayerVietorisBoundary
    (n : ℕ) (A B : Set X) (hA : IsClosed A) (hB : IsClosed B)
    (hcover : A ∪ B = Set.univ) (f : C(Y, X)) :
    letI := (hA.inter hB).locallyCompactSpace
    let hYA := hA.preimage f.continuous
    let hYB := hB.preimage f.continuous
    letI := (hYA.inter hYB).locallyCompactSpace
    letI := ((hA.inter hB).preimage f.continuous).locallyCompactSpace
    let hcoverY : f ⁻¹' A ∪ f ⁻¹' B = Set.univ := by
      rw [← Set.preimage_union, hcover, Set.preimage_univ]
    ∀ (a : CompactSupportK (n + 1) (A ∩ B : Set X)) (u : CompactSupportKZero Y),
      compactSupportKAction n f (compactSupportKMayerVietorisBoundary n A B hA hB hcover a) u =
        compactSupportKMayerVietorisBoundary n (f ⁻¹' A) (f ⁻¹' B) hYA hYB hcoverY
          (compactSupportKAction (n + 1) (preimageSubspaceMap (A ∩ B) f) a
            (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
              (hYA.inter hYB).isProperMap_subtypeVal u)) := by
  /- Stage 1: tensor the two cylinder extensions defining the pair boundary
  with the original degree-zero class, using base change of the full proper
  graph and retaining the height and suspension coordinates. The class u stays
  on Y; no pullback along the nonproper cylinder projection is asserted. On open
  complements keep u on Y: compactSupportKOpenAction uses its proper graph
  and never pulls u back along a potentially nonproper open inclusion.
  Stage 2: the same product commutes with α and β. Invertibility of the specified
  α transfers the commuting square to α⁻¹β. The unsuspended second factor
  produces no Koszul sign, and both boundaries use the first-coordinate convention.
  Stage 3: combine with closed restriction and open-extension compatibility
  along the actual common complements. The overlap class is the proper closed
  pullback of the original u. This is the square used in KA IV.1.3. -/
  classical
  -- Pullback of an open extension is computed on the exact graph preimage.
  have open_square
      {P : Type _} {Q : Type _} {P' : Type _} {Q' : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      [TopologicalSpace P'] [LocallyCompactSpace P'] [T2Space P']
      [TopologicalSpace Q'] [LocallyCompactSpace Q'] [T2Space Q']
      (j : Q' → Q) (hj : IsOpenEmbedding j) (k : P' → P) (hk : IsOpenEmbedding k)
      (g : C(P, Q)) (hg : IsProperMap g) (h : C(P', Q')) (hh : IsProperMap h)
      (hsquare : ∀ x : P', g (k x) = j (h x))
      (himage : ∀ x : P, g x ∈ Set.range j ↔ x ∈ Set.range k) :
      (compactSupportKZeroPullback g hg).comp (compactSupportKZeroOpenPushforward j hj) =
        (compactSupportKZeroOpenPushforward k hk).comp (compactSupportKZeroPullback h hh) := by
    let := hj.isOpen_range.locallyCompactSpace
    let := hk.isOpen_range.locallyCompactSpace
    let ej := hj.isEmbedding.toHomeomorph
    let ek := hk.isEmbedding.toHomeomorph
    let ij : C(Set.range j, Q') := ⟨ej.symm, ej.symm.continuous⟩
    let ik : C(Set.range k, P') := ⟨ek.symm, ek.symm.continuous⟩
    let cj : C(OnePoint Q, OnePoint Q') :=
      (properOnePointMap ij ej.symm.isProperMap).comp
        ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
    let ck : C(OnePoint P, OnePoint P') :=
      (properOnePointMap ik ek.symm.isProperMap).comp
        ⟨onePointCollapse (Set.range k), continuous_onePointCollapse _ hk.isOpen_range⟩
    have hcj (x : Q') : cj (j x) = (x : OnePoint Q') := by
      change OnePoint.map ij (onePointCollapse (Set.range j) (j x)) = (x : OnePoint Q')
      rw [onePointCollapse_coe_of_mem (Set.range j) (j x) ⟨x, rfl⟩, OnePoint.map_some]
      exact congrArg OnePoint.some (hj.isEmbedding.toHomeomorph_symm_apply x)
    have hck (x : P') : ck (k x) = (x : OnePoint P') := by
      change OnePoint.map ik (onePointCollapse (Set.range k) (k x)) = (x : OnePoint P')
      rw [onePointCollapse_coe_of_mem (Set.range k) (k x) ⟨x, rfl⟩, OnePoint.map_some]
      exact congrArg OnePoint.some (hk.isEmbedding.toHomeomorph_symm_apply x)
    have hpointed : cj.comp (properOnePointMap g hg) =
        (properOnePointMap h hh).comp ck := by
      ext z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe x =>
        by_cases hx : x ∈ Set.range k
        · obtain ⟨x, rfl⟩ := hx
          change cj (g (k x)) = (properOnePointMap h hh) (ck (k x))
          rw [hsquare, hcj, hck]
          rfl
        · have hgx : g x ∉ Set.range j := fun hxj ↦ hx ((himage x).mp hxj)
          change OnePoint.map ij (onePointCollapse (Set.range j) (g x)) =
            (properOnePointMap h hh)
              (OnePoint.map ik (onePointCollapse (Set.range k) x))
          rw [onePointCollapse_coe_of_notMem _ _ hgx,
            onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty, OnePoint.map_infty]
          rfl
    have heq := congrArg complexKZeroPullback hpointed
    simp only [cj, ck, complexKZeroPullback_comp] at heq
    apply AddMonoidHom.ext
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun heq a.val
  -- The cylinder graph is proper even though f need not be proper.
  -- It is identified with the closed graph inside the cylinder times Y.
  let cylinderGraph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) :
      C(BoundaryCylinder (f ⁻¹' A), BoundaryCylinder A × Y) :=
    { toFun := fun z ↦
        (⟨(f z.val.1, z.val.2), z.property.1, z.property.2.1, z.property.2.2⟩, z.val.1)
      continuous_toFun := by fun_prop }
  let cylinderGraphImage {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y]
      (A : Set X) (f : C(Y, X)) : Set (BoundaryCylinder A × Y) :=
    {z | z.1.val.1 = f z.2}
  let cylinderGraphHomeomorph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) :
      BoundaryCylinder (f ⁻¹' A) ≃ₜ cylinderGraphImage A f :=
    { toFun := fun z ↦ ⟨cylinderGraph A f z, rfl⟩
      invFun := fun z ↦
        ⟨(z.val.2, z.val.1.val.2), z.val.1.property.1, z.val.1.property.2.1, by
          rcases z.val.1.property.2.2 with ht | hx
          · exact Or.inl ht
          · exact Or.inr (by change f z.val.2 ∈ A; rw [← z.property]; exact hx)⟩
      left_inv := fun z ↦ rfl
      right_inv := fun z ↦ by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          exact Prod.ext z.property.symm rfl
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have cylinderGraph_proper {X : Type _} {Y : Type _}
      [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) :
      IsProperMap (cylinderGraph A f) := by
    have hclosed : IsClosed (cylinderGraphImage A f) :=
      isClosed_eq continuous_fst.subtype_val.fst (f.continuous.comp continuous_snd)
    exact hclosed.isProperMap_subtypeVal.comp (cylinderGraphHomeomorph A f).isProperMap
  let suspendedCylinderGraph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (A : Set X) (f : C(Y, X)) :
      C(BoundaryCylinder (f ⁻¹' A) × (Fin n → ℝ),
        (BoundaryCylinder A × (Fin n → ℝ)) × Y) :=
    { toFun := fun z ↦ (((cylinderGraph A f z.1).1, z.2), (cylinderGraph A f z.1).2)
      continuous_toFun := by fun_prop }
  have suspendedCylinderGraph_proper {X : Type _} {Y : Type _}
      [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] (n : ℕ) (A : Set X) (f : C(Y, X)) :
      IsProperMap (suspendedCylinderGraph n A f) := by
    let e : (BoundaryCylinder A × Y) × (Fin n → ℝ) ≃ₜ
        (BoundaryCylinder A × (Fin n → ℝ)) × Y :=
      { toFun := fun z ↦ ((z.1.1, z.2), z.1.2)
        invFun := fun z ↦ ((z.1.1, z.2), z.1.2)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact e.isProperMap.comp ((cylinderGraph_proper A f).prodMap isProperMap_id)
  -- Keep the original zero-height base and the original increasing tube chart.
  -- Source and target charts are local copies on their respective spaces.
  let baseEmbedding {X : Type _} (A : Set X) : (Aᶜ : Set X) → BoundaryCylinder A :=
    fun x ↦ ⟨(x.val, 0), le_rfl, zero_lt_one, Or.inl rfl⟩
  let baseEmbeddingTarget {X : Type _} (A : Set X) : (Aᶜ : Set X) → BoundaryCylinder A :=
    fun x ↦ ⟨(x.val, 0), le_rfl, zero_lt_one, Or.inl rfl⟩
  have baseEmbedding_open {X : Type _} [TopologicalSpace X] (A : Set X) (hA : IsClosed A) :
      IsOpenEmbedding (baseEmbedding A) :=
    (isOpen_boundaryCylinderBaseOpen A hA).isOpenEmbedding_subtypeVal.comp
      (boundaryCylinderBaseHomeomorph A).isOpenEmbedding
  have baseEmbedding_openTarget {X : Type _} [TopologicalSpace X] (A : Set X) (hA : IsClosed A) :
      IsOpenEmbedding (baseEmbeddingTarget A) :=
    (isOpen_boundaryCylinderBaseOpen A hA).isOpenEmbedding_subtypeVal.comp
      (boundaryCylinderBaseHomeomorph A).isOpenEmbedding
  let baseSuspendedEmbedding {X : Type _} (n : ℕ) (A : Set X) :
      (Aᶜ : Set X) × (Fin n → ℝ) → BoundaryCylinder A × (Fin n → ℝ) :=
    Prod.map (baseEmbedding A) id
  let baseSuspendedEmbeddingTarget {X : Type _} (n : ℕ) (A : Set X) :
      (Aᶜ : Set X) × (Fin n → ℝ) → BoundaryCylinder A × (Fin n → ℝ) :=
    Prod.map (baseEmbeddingTarget A) id
  have baseSuspendedEmbedding_open {X : Type _}
      [TopologicalSpace X] (n : ℕ) (A : Set X) (hA : IsClosed A) :
      IsOpenEmbedding (baseSuspendedEmbedding n A) :=
    (baseEmbedding_open A hA).prodMap IsOpenEmbedding.id
  have baseSuspendedEmbedding_openTarget {X : Type _}
      [TopologicalSpace X] (n : ℕ) (A : Set X) (hA : IsClosed A) :
      IsOpenEmbedding (baseSuspendedEmbeddingTarget n A) :=
    (baseEmbedding_openTarget A hA).prodMap IsOpenEmbedding.id
  have alpha_push {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      (n : ℕ) (A : Set X) (hA : IsClosed A) :
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryBase n A hA =
        compactSupportKZeroOpenPushforward (baseSuspendedEmbedding n A)
          (baseSuspendedEmbedding_open n A hA) := by
    let := hA.isOpen_compl.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let U := boundaryCylinderBaseOpen A
    have hU : IsOpen U := isOpen_boundaryCylinderBaseOpen A hA
    let := hU.locallyCompactSpace
    let T := Fin n → ℝ
    let e := (boundaryCylinderBaseHomeomorph A).prodCongr (Homeomorph.refl T)
    let j : U × T → BoundaryCylinder A × T := Prod.map Subtype.val id
    have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
    have hcomp := compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding j hj
    have hsub := compactSupportKOpenPushforward_subtype_val n U hU
    change compactSupportKZeroOpenPushforward j hj = compactSupportKOpenExtension n U hU
      at hsub
    rw [compactSupportKZeroOpenPushforward_homeomorph, hsub] at hcomp
    exact hcomp.symm
  have alpha_pushTarget {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      (n : ℕ) (A : Set X) (hA : IsClosed A) :
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryBase n A hA =
        compactSupportKZeroOpenPushforward (baseSuspendedEmbeddingTarget n A)
          (baseSuspendedEmbedding_openTarget n A hA) := by
    let := hA.isOpen_compl.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let U := boundaryCylinderBaseOpen A
    have hU : IsOpen U := isOpen_boundaryCylinderBaseOpen A hA
    let := hU.locallyCompactSpace
    let T := Fin n → ℝ
    let e := (boundaryCylinderBaseHomeomorph A).prodCongr (Homeomorph.refl T)
    let j : U × T → BoundaryCylinder A × T := Prod.map Subtype.val id
    have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
    have hcomp := compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding j hj
    have hsub := compactSupportKOpenPushforward_subtype_val n U hU
    change compactSupportKZeroOpenPushforward j hj = compactSupportKOpenExtension n U hU
      at hsub
    rw [compactSupportKZeroOpenPushforward_homeomorph, hsub] at hcomp
    exact hcomp.symm
  let tubeSuspendedEmbedding {X : Type _} [TopologicalSpace X] (n : ℕ) (A : Set X) :
      A × (Fin (n + 1) → ℝ) → BoundaryCylinder A × (Fin n → ℝ) :=
    fun z ↦ ((boundaryCylinderTubeHomeomorph A (z.1, z.2 0)).val, Matrix.vecTail z.2)
  let tubeSuspendedEmbeddingTarget {X : Type _} [TopologicalSpace X] (n : ℕ) (A : Set X) :
      A × (Fin (n + 1) → ℝ) → BoundaryCylinder A × (Fin n → ℝ) :=
    fun z ↦ ((boundaryCylinderTubeHomeomorph A (z.1, z.2 0)).val, Matrix.vecTail z.2)
  have tubeSuspendedEmbedding_open {X : Type _} [TopologicalSpace X] (n : ℕ) (A : Set X) :
      IsOpenEmbedding (tubeSuspendedEmbedding n A) :=
    ((isOpen_boundaryCylinderTubeOpen A).isOpenEmbedding_subtypeVal.prodMap
      IsOpenEmbedding.id).comp
        (((boundaryCylinderTubeHomeomorph A).prodCongr
          (Homeomorph.refl (Fin n → ℝ))).isOpenEmbedding.comp
            (suspensionCoordinateHomeomorph A n).symm.isOpenEmbedding)
  have tubeSuspendedEmbedding_openTarget {X : Type _} [TopologicalSpace X] (n : ℕ) (A : Set X) :
      IsOpenEmbedding (tubeSuspendedEmbeddingTarget n A) :=
    ((isOpen_boundaryCylinderTubeOpen A).isOpenEmbedding_subtypeVal.prodMap
      IsOpenEmbedding.id).comp
        (((boundaryCylinderTubeHomeomorph A).prodCongr
          (Homeomorph.refl (Fin n → ℝ))).isOpenEmbedding.comp
            (suspensionCoordinateHomeomorph A n).symm.isOpenEmbedding)
  have beta_push {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      (n : ℕ) (A : Set X) (hA : IsClosed A) :
      letI := hA.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryTube n A hA =
        compactSupportKZeroOpenPushforward (tubeSuspendedEmbedding n A)
          (tubeSuspendedEmbedding_open n A) := by
    let := hA.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let U := boundaryCylinderTubeOpen A
    have hU : IsOpen U := isOpen_boundaryCylinderTubeOpen A
    let := hU.locallyCompactSpace
    let T := Fin n → ℝ
    let e := (boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl T)
    let j : U × T → BoundaryCylinder A × T := Prod.map Subtype.val id
    have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
    let d := (suspensionCoordinateHomeomorph A n).symm
    have hfirst := compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding j hj
    have hsecond := compactSupportKZeroOpenPushforward_comp d d.isOpenEmbedding
      (j ∘ e) (hj.comp e.isOpenEmbedding)
    have hsub := compactSupportKOpenPushforward_subtype_val n U hU
    change compactSupportKZeroOpenPushforward j hj = compactSupportKOpenExtension n U hU
      at hsub
    rw [compactSupportKZeroOpenPushforward_homeomorph, hsub] at hfirst
    rw [compactSupportKZeroOpenPushforward_homeomorph, hfirst] at hsecond
    exact hsecond.symm
  have beta_pushTarget {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      (n : ℕ) (A : Set X) (hA : IsClosed A) :
      letI := hA.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryTube n A hA =
        compactSupportKZeroOpenPushforward (tubeSuspendedEmbeddingTarget n A)
          (tubeSuspendedEmbedding_openTarget n A) := by
    let := hA.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let U := boundaryCylinderTubeOpen A
    have hU : IsOpen U := isOpen_boundaryCylinderTubeOpen A
    let := hU.locallyCompactSpace
    let T := Fin n → ℝ
    let e := (boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl T)
    let j : U × T → BoundaryCylinder A × T := Prod.map Subtype.val id
    have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
    let d := (suspensionCoordinateHomeomorph A n).symm
    have hfirst := compactSupportKZeroOpenPushforward_comp e e.isOpenEmbedding j hj
    have hsecond := compactSupportKZeroOpenPushforward_comp d d.isOpenEmbedding
      (j ∘ e) (hj.comp e.isOpenEmbedding)
    have hsub := compactSupportKOpenPushforward_subtype_val n U hU
    change compactSupportKZeroOpenPushforward j hj = compactSupportKOpenExtension n U hU
      at hsub
    rw [compactSupportKZeroOpenPushforward_homeomorph, hsub] at hfirst
    rw [compactSupportKZeroOpenPushforward_homeomorph, hfirst] at hsecond
    exact hsecond.symm
  -- The open-complement graph keeps the coefficient class on Y.
  let subsetGraph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) : C(f ⁻¹' A, A × Y) :=
    { toFun := fun y ↦ (⟨f y.val, y.property⟩, y.val)
      continuous_toFun := by fun_prop }
  let subsetGraphImage {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) : Set (A × Y) :=
    {z | z.1.val = f z.2}
  let subsetGraphHomeomorph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (A : Set X) (f : C(Y, X)) :
      (f ⁻¹' A) ≃ₜ subsetGraphImage A f :=
    { toFun := fun y ↦ ⟨subsetGraph A f y, rfl⟩
      invFun := fun z ↦ ⟨z.val.2, by
        change f z.val.2 ∈ A
        rw [← z.property]
        exact z.val.1.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun z ↦ by
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          exact z.property.symm
        · rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have subsetGraph_proper {X : Type _} {Y : Type _}
      [TopologicalSpace X] [T2Space X] [TopologicalSpace Y]
      (A : Set X) (f : C(Y, X)) : IsProperMap (subsetGraph A f) := by
    have hclosed : IsClosed (subsetGraphImage A f) :=
      isClosed_eq continuous_fst.subtype_val (f.continuous.comp continuous_snd)
    exact hclosed.isProperMap_subtypeVal.comp (subsetGraphHomeomorph A f).isProperMap
  let suspendedSubsetGraph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (A : Set X) (f : C(Y, X)) :
      C((f ⁻¹' A) × (Fin n → ℝ), (A × (Fin n → ℝ)) × Y) :=
    { toFun := fun z ↦ (((subsetGraph A f z.1).1, z.2), (subsetGraph A f z.1).2)
      continuous_toFun := by fun_prop }
  have suspendedSubsetGraph_proper {X : Type _} {Y : Type _}
      [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] (n : ℕ) (A : Set X) (f : C(Y, X)) :
      IsProperMap (suspendedSubsetGraph n A f) := by
    let e : (A × Y) × (Fin n → ℝ) ≃ₜ (A × (Fin n → ℝ)) × Y :=
      { toFun := fun z ↦ ((z.1.1, z.2), z.1.2)
        invFun := fun z ↦ ((z.1.1, z.2), z.1.2)
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact e.isProperMap.comp ((subsetGraph_proper A f).prodMap isProperMap_id)
  have openAction_graph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] (n : ℕ) (U : Set X) (hU : IsOpen U)
      (f : C(Y, X)) (u : CompactSupportKZero Y)
      (a : letI := hU.locallyCompactSpace; CompactSupportK n U) :
      letI := hU.locallyCompactSpace
      letI := (hU.preimage f.continuous).locallyCompactSpace
      compactSupportKZeroPullback (suspendedSubsetGraph n U f)
          (suspendedSubsetGraph_proper n U f) (compactSupportKZeroExternalProduct a u) =
        compactSupportKOpenAction n U hU f a u := by
    rfl
  have closedAction_graph {X : Type _} {Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y] (n : ℕ) (A : Set X) (hA : IsClosed A)
      (f : C(Y, X)) (u : CompactSupportKZero Y)
      (a : letI := hA.locallyCompactSpace; CompactSupportK n A) :
      letI := hA.locallyCompactSpace
      letI := (hA.preimage f.continuous).locallyCompactSpace
      compactSupportKZeroPullback (suspendedSubsetGraph n A f)
          (suspendedSubsetGraph_proper n A f) (compactSupportKZeroExternalProduct a u) =
        compactSupportKAction n (preimageSubspaceMap A f) a
          (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hA.preimage f.continuous).isProperMap_subtypeVal u) := by
    let := hA.locallyCompactSpace
    let := (hA.preimage f.continuous).locallyCompactSpace
    let T := Fin n → ℝ
    let C : Set Y := f ⁻¹' A
    let i : C(C, Y) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : IsProperMap i := (hA.preimage f.continuous).isProperMap_subtypeVal
    let F : C(C × T, (A × T) × C) :=
      ((preimageSubspaceMap A f).prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let r : C((A × T) × C, C × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    have hF : IsProperMap F :=
      isProperMap_of_comp_of_t2 F.continuous r.continuous isProperMap_id
    let J : C((A × T) × C, (A × T) × Y) := (ContinuousMap.id (A × T)).prodMap i
    have hJ : IsProperMap J := isProperMap_id.prodMap hi
    have hprod := compactSupportKZeroExternalProduct_properPullback
      (ContinuousMap.id (A × T)) isProperMap_id i hi a u
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprod
    change compactSupportKZeroPullback (suspendedSubsetGraph n A f)
        (suspendedSubsetGraph_proper n A f) (compactSupportKZeroExternalProduct a u) =
      compactSupportKZeroPullback F hF
        (compactSupportKZeroExternalProduct a (compactSupportKZeroPullback i hi u))
    rw [← hprod]
    exact DFunLike.congr_fun (compactSupportKZeroPullback_comp F J hF hJ)
      (compactSupportKZeroExternalProduct a u)
  -- The two cylinder image conditions give the same base-change squares.
  have base_range {X : Type _} (n : ℕ) (A : Set X) (z : BoundaryCylinder A × (Fin n → ℝ)) :
      z ∈ Set.range (baseSuspendedEmbedding n A) ↔ z.1.val.1 ∉ A := by
    constructor
    · rintro ⟨⟨x, s⟩, rfl⟩
      exact x.property
    · intro hz
      refine ⟨(⟨z.1.val.1, hz⟩, z.2), ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext rfl (z.1.property.2.2.resolve_right hz).symm
      · rfl
  have base_rangeTarget {X : Type _} (n : ℕ) (A : Set X) (z : BoundaryCylinder A × (Fin n → ℝ)) :
      z ∈ Set.range (baseSuspendedEmbeddingTarget n A) ↔ z.1.val.1 ∉ A := by
    constructor
    · rintro ⟨⟨x, s⟩, rfl⟩
      exact x.property
    · intro hz
      refine ⟨(⟨z.1.val.1, hz⟩, z.2), ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext rfl (z.1.property.2.2.resolve_right hz).symm
      · rfl
  have tube_range {X : Type _}
      [TopologicalSpace X] (n : ℕ) (A : Set X) (z : BoundaryCylinder A × (Fin n → ℝ)) :
      z ∈ Set.range (tubeSuspendedEmbedding n A) ↔ 0 < z.1.val.2 := by
    let e := (suspensionCoordinateHomeomorph A n).symm.trans
      ((boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl (Fin n → ℝ)))
    constructor
    · rintro ⟨p, rfl⟩
      exact (e p).1.property
    · intro hz
      let q : boundaryCylinderTubeOpen A × (Fin n → ℝ) := (⟨z.1, hz⟩, z.2)
      refine ⟨e.symm q, ?_⟩
      change ((e (e.symm q)).1.val, (e (e.symm q)).2) = z
      rw [e.apply_symm_apply]
  have tube_rangeTarget {X : Type _}
      [TopologicalSpace X] (n : ℕ) (A : Set X) (z : BoundaryCylinder A × (Fin n → ℝ)) :
      z ∈ Set.range (tubeSuspendedEmbeddingTarget n A) ↔ 0 < z.1.val.2 := by
    let e := (suspensionCoordinateHomeomorph A n).symm.trans
      ((boundaryCylinderTubeHomeomorph A).prodCongr (Homeomorph.refl (Fin n → ℝ)))
    constructor
    · rintro ⟨p, rfl⟩
      exact (e p).1.property
    · intro hz
      let q : boundaryCylinderTubeOpen A × (Fin n → ℝ) := (⟨z.1, hz⟩, z.2)
      refine ⟨e.symm q, ?_⟩
      change ((e (e.symm q)).1.val, (e (e.symm q)).2) = z
      rw [e.apply_symm_apply]
  -- Tensoring with the original coefficient commutes with both cylinder extensions.
  have alpha_action {X : Type _} {Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (n : ℕ) (A : Set X) (hA : IsClosed A) (f : C(Y, X))
      (u : CompactSupportKZero Y)
      (a : letI := hA.isOpen_compl.locallyCompactSpace; CompactSupportK n (Aᶜ : Set X)) :
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := (hA.preimage f.continuous).isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      letI := locallyCompactSpace_boundaryCylinder (f ⁻¹' A) (hA.preimage f.continuous)
      compactSupportKZeroPullback (suspendedCylinderGraph n A f)
          (suspendedCylinderGraph_proper n A f)
          (compactSupportKZeroExternalProduct (compactSupportKBoundaryBase n A hA a) u) =
        compactSupportKBoundaryBase n (f ⁻¹' A) (hA.preimage f.continuous)
          (compactSupportKOpenAction n Aᶜ hA.isOpen_compl f a u) := by
    let C : Set Y := f ⁻¹' A
    have hC : IsClosed C := hA.preimage f.continuous
    let := hA.isOpen_compl.locallyCompactSpace
    let := hC.isOpen_compl.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let := locallyCompactSpace_boundaryCylinder C hC
    let j := Prod.map (baseSuspendedEmbedding n A) (id : Y → Y)
    have hj : IsOpenEmbedding j :=
      (baseSuspendedEmbedding_open n A hA).prodMap IsOpenEmbedding.id
    let k := baseSuspendedEmbeddingTarget n C
    have hk : IsOpenEmbedding k := baseSuspendedEmbedding_openTarget n C hC
    let g := suspendedCylinderGraph n A f
    have hg : IsProperMap g := suspendedCylinderGraph_proper n A f
    let h := suspendedSubsetGraph n Aᶜ f
    have hh : IsProperMap h := suspendedSubsetGraph_proper n Aᶜ f
    have hsquare (z : (Cᶜ : Set Y) × (Fin n → ℝ)) : g (k z) = j (h z) := rfl
    have himage (z : BoundaryCylinder C × (Fin n → ℝ)) :
        g z ∈ Set.range j ↔ z ∈ Set.range k := by
      change g z ∈ Set.range (Prod.map (baseSuspendedEmbedding n A) id) ↔
        z ∈ Set.range (baseSuspendedEmbeddingTarget n C)
      simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, and_true]
      rw [base_range, base_rangeTarget]
      rfl
    have hs := open_square j hj k hk g hg h hh hsquare himage
    have hprod := compactSupportKZeroExternalProduct_openPushforward
      (baseSuspendedEmbedding n A) (baseSuspendedEmbedding_open n A hA)
      (id : Y → Y) IsOpenEmbedding.id a u
    rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hprod
    rw [alpha_push n A hA, alpha_pushTarget n C hC, ← hprod,
      ← openAction_graph n Aᶜ hA.isOpen_compl f u a]
    exact DFunLike.congr_fun hs (compactSupportKZeroExternalProduct a u)
  have beta_action {X : Type _} {Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (n : ℕ) (A : Set X) (hA : IsClosed A) (f : C(Y, X))
      (u : CompactSupportKZero Y)
      (a : letI := hA.locallyCompactSpace; CompactSupportK (n + 1) A) :
      letI := hA.locallyCompactSpace
      letI := (hA.preimage f.continuous).locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      letI := locallyCompactSpace_boundaryCylinder (f ⁻¹' A) (hA.preimage f.continuous)
      compactSupportKZeroPullback (suspendedCylinderGraph n A f)
          (suspendedCylinderGraph_proper n A f)
          (compactSupportKZeroExternalProduct (compactSupportKBoundaryTube n A hA a) u) =
        compactSupportKBoundaryTube n (f ⁻¹' A) (hA.preimage f.continuous)
          (compactSupportKAction (n + 1) (preimageSubspaceMap A f) a
            (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
              (hA.preimage f.continuous).isProperMap_subtypeVal u)) := by
    let C : Set Y := f ⁻¹' A
    have hC : IsClosed C := hA.preimage f.continuous
    let := hA.locallyCompactSpace
    let := hC.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let := locallyCompactSpace_boundaryCylinder C hC
    let j := Prod.map (tubeSuspendedEmbedding n A) (id : Y → Y)
    have hj : IsOpenEmbedding j :=
      (tubeSuspendedEmbedding_open n A).prodMap IsOpenEmbedding.id
    let k := tubeSuspendedEmbeddingTarget n C
    have hk : IsOpenEmbedding k := tubeSuspendedEmbedding_openTarget n C
    let g := suspendedCylinderGraph n A f
    have hg : IsProperMap g := suspendedCylinderGraph_proper n A f
    let h := suspendedSubsetGraph (n + 1) A f
    have hh : IsProperMap h := suspendedSubsetGraph_proper (n + 1) A f
    have hsquare (z : C × (Fin (n + 1) → ℝ)) : g (k z) = j (h z) := rfl
    have himage (z : BoundaryCylinder C × (Fin n → ℝ)) :
        g z ∈ Set.range j ↔ z ∈ Set.range k := by
      change g z ∈ Set.range (Prod.map (tubeSuspendedEmbedding n A) id) ↔
        z ∈ Set.range (tubeSuspendedEmbeddingTarget n C)
      simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, and_true]
      rw [tube_range, tube_rangeTarget]
      rfl
    have hs := open_square j hj k hk g hg h hh hsquare himage
    have hprod := compactSupportKZeroExternalProduct_openPushforward
      (tubeSuspendedEmbedding n A) (tubeSuspendedEmbedding_open n A)
      (id : Y → Y) IsOpenEmbedding.id a u
    rw [compactSupportKZeroOpenPushforward_id, AddMonoidHom.id_apply] at hprod
    rw [beta_push n A hA, beta_pushTarget n C hC, ← hprod,
      ← closedAction_graph (n + 1) A hA f u a]
    exact DFunLike.congr_fun hs (compactSupportKZeroExternalProduct a u)
  -- Injectivity of the specified alpha transfers the square to alpha⁻¹ beta.
  have boundary_base_spec {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (n : ℕ) (A : Set X) (hA : IsClosed A)
      (a : letI := hA.locallyCompactSpace; CompactSupportK (n + 1) A) :
      letI := hA.locallyCompactSpace
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryBase n A hA (compactSupportKBoundary n A hA a) =
        compactSupportKBoundaryTube n A hA a := by
    exact (AddEquiv.ofBijective (compactSupportKBoundaryBase n A hA)
      (compactSupportKBoundaryBase_bijective n A hA)).apply_symm_apply _
  have boundary_base_specTarget {X : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] (n : ℕ) (A : Set X) (hA : IsClosed A)
      (a : letI := hA.locallyCompactSpace; CompactSupportK (n + 1) A) :
      letI := hA.locallyCompactSpace
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := locallyCompactSpace_boundaryCylinder A hA
      compactSupportKBoundaryBase n A hA (compactSupportKBoundary n A hA a) =
        compactSupportKBoundaryTube n A hA a := by
    exact (AddEquiv.ofBijective (compactSupportKBoundaryBase n A hA)
      (compactSupportKBoundaryBase_bijective n A hA)).apply_symm_apply _
  have boundary_action {X : Type _} {Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (n : ℕ) (A : Set X) (hA : IsClosed A) (f : C(Y, X))
      (u : CompactSupportKZero Y)
      (a : letI := hA.locallyCompactSpace; CompactSupportK (n + 1) A) :
      letI := hA.locallyCompactSpace
      letI := hA.isOpen_compl.locallyCompactSpace
      letI := (hA.preimage f.continuous).locallyCompactSpace
      letI := (hA.preimage f.continuous).isOpen_compl.locallyCompactSpace
      compactSupportKOpenAction n Aᶜ hA.isOpen_compl f
          (compactSupportKBoundary n A hA a) u =
        compactSupportKBoundary n (f ⁻¹' A) (hA.preimage f.continuous)
          (compactSupportKAction (n + 1) (preimageSubspaceMap A f) a
            (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
              (hA.preimage f.continuous).isProperMap_subtypeVal u)) := by
    let C : Set Y := f ⁻¹' A
    have hC : IsClosed C := hA.preimage f.continuous
    let := hA.locallyCompactSpace
    let := hA.isOpen_compl.locallyCompactSpace
    let := hC.locallyCompactSpace
    let := hC.isOpen_compl.locallyCompactSpace
    let := locallyCompactSpace_boundaryCylinder A hA
    let := locallyCompactSpace_boundaryCylinder C hC
    let Phi (b : CompactSupportK n (BoundaryCylinder A)) :
        CompactSupportK n (BoundaryCylinder C) :=
      compactSupportKZeroPullback (suspendedCylinderGraph n A f)
        (suspendedCylinderGraph_proper n A f) (compactSupportKZeroExternalProduct b u)
    apply (compactSupportKBoundaryBase_bijective n C hC).injective
    calc
      _ = Phi (compactSupportKBoundaryBase n A hA (compactSupportKBoundary n A hA a)) :=
        (alpha_action n A hA f u (compactSupportKBoundary n A hA a)).symm
      _ = Phi (compactSupportKBoundaryTube n A hA a) := by rw [boundary_base_spec]
      _ = _ := (beta_action n A hA f u a).trans (boundary_base_specTarget n C hC _).symm
  dsimp only
  intro a u
  let YA : Set Y := f ⁻¹' A
  let YB : Set Y := f ⁻¹' B
  have hYA : IsClosed YA := hA.preimage f.continuous
  have hYB : IsClosed YB := hB.preimage f.continuous
  have hcoverY : YA ∪ YB = Set.univ := by
    rw [← Set.preimage_union, hcover, Set.preimage_univ]
  let := hA.locallyCompactSpace
  let := hB.locallyCompactSpace
  let := (hA.inter hB).locallyCompactSpace
  let := hYA.locallyCompactSpace
  let := hYB.locallyCompactSpace
  let := (hYA.inter hYB).locallyCompactSpace
  let C : Set B := Subtype.val ⁻¹' A
  have hC : IsClosed C := hA.preimage continuous_subtype_val
  let D : Set YB := Subtype.val ⁻¹' YA
  have hD : IsClosed D := hYA.preimage continuous_subtype_val
  let := hC.locallyCompactSpace
  let := hD.locallyCompactSpace
  let := hA.isOpen_compl.locallyCompactSpace
  let := hYA.isOpen_compl.locallyCompactSpace
  let := hC.isOpen_compl.locallyCompactSpace
  let := hD.isOpen_compl.locallyCompactSpace
  let eO := mayerVietorisOverlapHomeomorph A B
  let eOY := mayerVietorisOverlapHomeomorph YA YB
  let eC := mayerVietorisComplementHomeomorph A B hcover
  let eCY := mayerVietorisComplementHomeomorph YA YB hcoverY
  let fB := preimageSubspaceMap B f
  let fC := preimageSubspaceMap C fB
  let fO := preimageSubspaceMap (A ∩ B) f
  let := (hC.preimage fB.continuous).locallyCompactSpace
  let := (hC.isOpen_compl.preimage fB.continuous).locallyCompactSpace
  let := ((hA.inter hB).preimage f.continuous).locallyCompactSpace
  let := (hA.isOpen_compl.preimage f.continuous).locallyCompactSpace
  let iB : C(YB, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let iD : C(D, YB) := ⟨Subtype.val, continuous_subtype_val⟩
  let iO : C((YA ∩ YB : Set Y), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hiB : IsProperMap iB := hYB.isProperMap_subtypeVal
  have hiD : IsProperMap iD := hD.isProperMap_subtypeVal
  have hiO : IsProperMap iO := (hYA.inter hYB).isProperMap_subtypeVal
  let uB := compactSupportKZeroPullback iB hiB u
  let uD := compactSupportKZeroPullback iD hiD uB
  let uO := compactSupportKZeroPullback iO hiO u
  -- The overlap comparison retains the original point and both closed memberships.
  have hoverlap :
      compactSupportKAction (n + 1) fC (compactSupportKHomeomorphEquiv (n + 1) eO a) uD =
        compactSupportKHomeomorphEquiv (n + 1) eOY
          (compactSupportKAction (n + 1) fO a uO) := by
    let T := Fin (n + 1) → ℝ
    let j : C(C × T, (A ∩ B : Set X) × T) :=
      ⟨eO.symm.prodCongr (Homeomorph.refl T),
        (eO.symm.prodCongr (Homeomorph.refl T)).continuous⟩
    let k : C(D × T, (YA ∩ YB : Set Y) × T) :=
      ⟨eOY.symm.prodCongr (Homeomorph.refl T),
        (eOY.symm.prodCongr (Homeomorph.refl T)).continuous⟩
    have hj : IsProperMap j := (eO.symm.prodCongr (Homeomorph.refl T)).isProperMap
    have hk : IsProperMap k := (eOY.symm.prodCongr (Homeomorph.refl T)).isProperMap
    let F : C(D × T, (C × T) × D) :=
      (fC.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let G : C((YA ∩ YB : Set Y) × T, ((A ∩ B : Set X) × T) × (YA ∩ YB : Set Y)) :=
      (fO.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let rF : C((C × T) × D, D × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    let rG : C(((A ∩ B : Set X) × T) × (YA ∩ YB : Set Y),
        (YA ∩ YB : Set Y) × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    have hF : IsProperMap F :=
      isProperMap_of_comp_of_t2 F.continuous rF.continuous isProperMap_id
    have hG : IsProperMap G :=
      isProperMap_of_comp_of_t2 G.continuous rG.continuous isProperMap_id
    let i := iB.comp iD
    have hi : IsProperMap i := hiB.comp hiD
    let L := j.prodMap i
    let R := (ContinuousMap.id ((A ∩ B : Set X) × T)).prodMap iO
    have hL : IsProperMap L := hj.prodMap hi
    have hR : IsProperMap R := isProperMap_id.prodMap hiO
    have huD : uD = compactSupportKZeroPullback i hi u :=
      (DFunLike.congr_fun (compactSupportKZeroPullback_comp iD iB hiD hiB) u).symm
    have hprodL := compactSupportKZeroExternalProduct_properPullback j hj i hi a u
    have hprodR := compactSupportKZeroExternalProduct_properPullback
      (ContinuousMap.id ((A ∩ B : Set X) × T)) isProperMap_id iO hiO a u
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprodR
    change compactSupportKZeroPullback F hF
        (compactSupportKZeroExternalProduct (compactSupportKZeroPullback j hj a) uD) =
      compactSupportKZeroPullback k hk
        (compactSupportKZeroPullback G hG
          (compactSupportKZeroExternalProduct a (compactSupportKZeroPullback iO hiO u)))
    rw [huD, ← hprodL, ← hprodR]
    let t := compactSupportKZeroExternalProduct a u
    calc
      _ = compactSupportKZeroPullback (L.comp F) (hL.comp hF) t :=
        (DFunLike.congr_fun (compactSupportKZeroPullback_comp F L hF hL) t).symm
      _ = compactSupportKZeroPullback (R.comp (G.comp k)) (hR.comp (hG.comp hk)) t := by rfl
      _ = _ := by
        rw [compactSupportKZeroPullback_comp (G.comp k) R (hG.comp hk) hR,
          AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp k G hk hG,
          AddMonoidHom.comp_apply]
  -- On the common open complement, retain u on Y and only use its proper restriction to YB.
  have hcomplement (b : CompactSupportK n (Cᶜ : Set B)) :
      compactSupportKOpenAction n Aᶜ hA.isOpen_compl f
          (compactSupportKHomeomorphEquiv n eC b) u =
        compactSupportKHomeomorphEquiv n eCY
          (compactSupportKOpenAction n Cᶜ hC.isOpen_compl fB b uB) := by
    let T := Fin n → ℝ
    let j : C((Aᶜ : Set X) × T, (Cᶜ : Set B) × T) :=
      ⟨eC.symm.prodCongr (Homeomorph.refl T),
        (eC.symm.prodCongr (Homeomorph.refl T)).continuous⟩
    let k : C((YAᶜ : Set Y) × T, (Dᶜ : Set YB) × T) :=
      ⟨eCY.symm.prodCongr (Homeomorph.refl T),
        (eCY.symm.prodCongr (Homeomorph.refl T)).continuous⟩
    have hj : IsProperMap j := (eC.symm.prodCongr (Homeomorph.refl T)).isProperMap
    have hk : IsProperMap k := (eCY.symm.prodCongr (Homeomorph.refl T)).isProperMap
    let F : C((YAᶜ : Set Y) × T, ((Aᶜ : Set X) × T) × Y) :=
      suspendedSubsetGraph n Aᶜ f
    let G : C((Dᶜ : Set YB) × T, ((Cᶜ : Set B) × T) × YB) :=
      suspendedSubsetGraph n Cᶜ fB
    have hF : IsProperMap F := suspendedSubsetGraph_proper n Aᶜ f
    have hG : IsProperMap G := suspendedSubsetGraph_proper n Cᶜ fB
    let L := j.prodMap (ContinuousMap.id Y)
    let R := (ContinuousMap.id ((Cᶜ : Set B) × T)).prodMap iB
    have hL : IsProperMap L := hj.prodMap isProperMap_id
    have hR : IsProperMap R := isProperMap_id.prodMap hiB
    have hprodL := compactSupportKZeroExternalProduct_properPullback j hj
      (ContinuousMap.id Y) isProperMap_id b u
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprodL
    have hprodR := compactSupportKZeroExternalProduct_properPullback
      (ContinuousMap.id ((Cᶜ : Set B) × T)) isProperMap_id iB hiB b u
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hprodR
    rw [← openAction_graph n Aᶜ hA.isOpen_compl f u,
      ← openAction_graph n Cᶜ hC.isOpen_compl fB uB]
    change compactSupportKZeroPullback F hF
        (compactSupportKZeroExternalProduct (compactSupportKZeroPullback j hj b) u) =
      compactSupportKZeroPullback k hk
        (compactSupportKZeroPullback G hG
          (compactSupportKZeroExternalProduct b (compactSupportKZeroPullback iB hiB u)))
    rw [← hprodL, ← hprodR]
    let t := compactSupportKZeroExternalProduct b u
    calc
      _ = compactSupportKZeroPullback (L.comp F) (hL.comp hF) t :=
        (DFunLike.congr_fun (compactSupportKZeroPullback_comp F L hF hL) t).symm
      _ = compactSupportKZeroPullback (R.comp (G.comp k)) (hR.comp (hG.comp hk)) t := by rfl
      _ = _ := by
        rw [compactSupportKZeroPullback_comp (G.comp k) R (hG.comp hk) hR,
          AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp k G hk hG,
          AddMonoidHom.comp_apply]
  -- Transfer the original pair boundary through the same overlap and complement maps.
  change compactSupportKAction n f
      (compactSupportKOpenExtension n Aᶜ hA.isOpen_compl
        (compactSupportKHomeomorphEquiv n eC
          (compactSupportKBoundary n C hC
            (compactSupportKHomeomorphEquiv (n + 1) eO a)))) u =
    compactSupportKOpenExtension n YAᶜ hYA.isOpen_compl
      (compactSupportKHomeomorphEquiv n eCY
        (compactSupportKBoundary n D hD
          (compactSupportKHomeomorphEquiv (n + 1) eOY
            (compactSupportKAction (n + 1) fO a uO))))
  have hboundary :
      compactSupportKOpenAction n Cᶜ hC.isOpen_compl fB
          (compactSupportKBoundary n C hC
            (compactSupportKHomeomorphEquiv (n + 1) eO a)) uB =
        compactSupportKBoundary n D hD
          (compactSupportKAction (n + 1) fC
            (compactSupportKHomeomorphEquiv (n + 1) eO a) uD) := by
    exact boundary_action n C hC fB uB _
  rw [compactSupportKOpenExtension_action, hcomplement]
  change compactSupportKOpenExtension n YAᶜ hYA.isOpen_compl
      (compactSupportKHomeomorphEquiv n eCY
        (compactSupportKOpenAction n Cᶜ hC.isOpen_compl fB
          (compactSupportKBoundary n C hC
            (compactSupportKHomeomorphEquiv (n + 1) eO a)) uB)) = _
  rw [hboundary, hoverlap]

end AtiyahSinger
