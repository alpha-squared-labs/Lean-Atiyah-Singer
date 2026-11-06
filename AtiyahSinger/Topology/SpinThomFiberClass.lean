/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinCliffordSymbol
public import AtiyahSinger.Topology.ExteriorBott
public import AtiyahSinger.Topology.SpinorThomClass

/-!
# The original spin Thom class in a specified fiber frame

Public module ID: M2173.

Restriction to a single original fiber, followed by the specified principal
spin frame, is exactly the original exterior Bott class. The same principal
point supplies both parity coordinates and the Clifford symbol comparison.
This explicit equality fixes the supported generator for the degree-zero
spin characteristic normalization.

Source: SG Appendix C.3 and III.12, using the fixed interleaved coordinate
convention of the original spinor representation.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology
  t2Space_fiberBundleTotal locallyCompactSpace_fiberBundleTotal

variable {m : ℕ} {B P : Type*} {E : B → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace B] [CompactSpace B] [T2Space B] [TopologicalSpace P]
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

set_option maxHeartbeats 1200000 in

set_option maxRecDepth 4096 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The supported spin class in the specified spin frame is exactly the exterior Bott class. -/
theorem TopologicalSpinStructure.spinorThomClass_pullback_frame
    (S : TopologicalSpinStructure m E o hm hP) (p : P) (b : B) (hp : projection p = b) :
    let R := EuclideanSpace ℝ (Fin (2 * m))
    let V := EuclideanSpace ℂ (Fin m)
    let e := (realSpinorCoordinateIsometry m).symm.trans (S.frame p b hp)
    let μ : C(V, TotalSpace R E) :=
      ⟨fun v ↦ ⟨b, e v⟩, (FiberBundle.continuous_totalSpaceMk R E b).comp e.continuous⟩
    compactSupportKZeroPullback μ
        ((FiberBundle.totalSpaceMk_isClosedEmbedding R E b).isProperMap.comp
          e.toHomeomorph.isProperMap) S.spinorThomClass = exteriorBottClass V := by
  classical
  let R := EuclideanSpace ℝ (Fin (2 * m))
  let V := EuclideanSpace ℂ (Fin m)
  let Z := TotalSpace R E
  let e := (realSpinorCoordinateIsometry m).symm.trans (S.frame p b hp)
  let μ : C(V, Z) := ⟨fun v ↦ ⟨b, e v⟩,
    (FiberBundle.continuous_totalSpaceMk R E b).comp e.continuous⟩
  have hμ : IsProperMap μ :=
    (FiberBundle.totalSpaceMk_isClosedEmbedding R E b).isProperMap.comp
      e.toHomeomorph.isProperMap
  let πE : C(Z, B) := ⟨π R E, FiberBundle.continuous_proj R E⟩
  let Parity (i : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) i
  let Q (i : ZMod 2) := HalfSpinorBundle m hP i
  let T (i : ZMod 2) := Bundle.Trivial V (Parity i)
  let A (i : ZMod 2) := πE *ᵖ (Q i)
  let AP (i : ZMod 2) := μ *ᵖ (A i)
  let ρ (i : ZMod 2) := complexSpinParityContRepresentation m i
  let (i : ZMod 2) : IsFiniteRank (Q i) :=
    isFiniteRank_associatedVector hP (ρ i) (continuous_complexSpinParityRepresentation m i)
  let (i : ZMod 2) := modelTopology (Parity i) (T i)
  let (i : ZMod 2) := isFiniteRank_model (Parity i) (T i)
  let (i : ZMod 2) := isFiniteRank_pullback (E := Q i) πE
  let (i : ZMod 2) := isFiniteRank_pullback (E := A i) μ
  -- Both parity coordinates use the very same original principal point.
  let coordinates (i : ZMod 2) : Hom (T i) (AP i) :=
    { linearMap := fun _ ↦ (associatedVectorFiberMkLinearEquiv hP (ρ i) p hp).toLinearMap
      continuous_total := by
        let t := (unitTotalHomeomorph (Parity i) (T i)).trans
          (Bundle.Trivial.homeomorphProd V (Parity i))
        have hz : Continuous (fun z : TotalSpace Unit (T i) ↦ z.proj) := t.continuous.fst
        have hv : Continuous (fun z : TotalSpace Unit (T i) ↦ z.snd) := t.continuous.snd
        have hmk : Continuous (fun z : TotalSpace Unit (T i) ↦
            (⟨b, associatedVectorFiberMk hP (ρ i) p hp z.snd⟩ : TotalSpace Unit (Q i))) := by
          apply (associatedVectorTotalHomeomorph hP (ρ i)).isInducing.continuous_iff.mpr
          exact continuous_quot_mk.comp (continuous_const.prodMk hv)
        apply (inducing_pullbackTotalSpaceEmbedding Unit (A i) μ).continuous_iff.mpr
        apply hz.prodMk
        apply (inducing_pullbackTotalSpaceEmbedding Unit (Q i) πE).continuous_iff.mpr
        exact (μ.continuous.comp hz).prodMk hmk }
  let u (i : ZMod 2) := (coordinates i).toIso (fun _ ↦
    (associatedVectorFiberMkLinearEquiv hP (ρ i) p hp).bijective)
  let a := S.spinorSymbolTriple.pullback μ hμ
  let aB := exteriorBottTriple V
  have hcontrol : a.control = aB.control := by
    ext v
    change (⟨b, e v⟩ : Z) ∈ Set.range (zeroSection R E) ↔ v ∈ ({0} : Set V)
    rw [Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, hx⟩
      have hn := congrArg (fun z : Z ↦ ‖z.snd‖) hx
      apply norm_eq_zero.mp
      simpa only [zeroSection, norm_zero, LinearIsometryEquiv.norm_map] using hn.symm
    · intro hv
      refine ⟨b, ?_⟩
      simp only [hv, map_zero]
      rfl
  -- The frame formula compares the full original boundary, including the negative-square inverse.
  have htriple : aB.congr (u 0) (u 1) =
      a.enlarge aB.control aB.isCompact_control hcontrol.subset := by
    change CompactSupportTriple.mk aB.control _ _ = CompactSupportTriple.mk aB.control _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    let v := (u 0).symm.linearEquiv z.val w
    have hw : associatedVectorFiberMk hP (ρ 0) p hp v = w :=
      ((u 0).linearEquiv z.val).apply_symm_apply w
    have h := S.cliffordParity_apply_mk p b hp (e z.val) 0 v
    have hc : realSpinorCoordinateIsometry m ((S.frame p b hp).symm (e z.val)) = z.val := by
      simp only [e, LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.symm_apply_apply,
        LinearIsometryEquiv.apply_symm_apply]
    have ha : (a.enlarge aB.control aB.isCompact_control hcontrol.subset).boundary.linearEquiv
        z w = S.cliffordParity b (e z.val) 0 w :=
      (a.enlarge_apply aB.control aB.isCompact_control hcontrol.subset z w).trans
        (S.spinorSymbolTriple.boundary.pullback_apply μ
          ⟨z.val, fun hz ↦ z.property (hcontrol.subset hz)⟩ w)
    change (aB.congr (u 0) (u 1)).boundary.linearEquiv z w =
      (a.enlarge aB.control aB.isCompact_control hcontrol.subset).boundary.linearEquiv z w
    rw [aB.congr_apply, ha]
    change associatedVectorFiberMk hP (ρ 1) p hp (cliffordSymbolParity z.val 0 v) = _
    rw [hw, hc] at h
    exact h.symm
  -- Congruence and harmless control enlargement retain the original compact-support class.
  change compactSupportKZeroPullback μ hμ S.spinorSymbolTriple.compactSupportClass =
    aB.compactSupportClass
  rw [← CompactSupportTriple.compactSupportClass_pullback]
  change a.compactSupportClass = aB.compactSupportClass
  exact (a.compactSupportClass_enlarge aB.control aB.isCompact_control hcontrol.subset).symm.trans
    ((congrArg CompactSupportTriple.compactSupportClass htriple.symm).trans
      (aB.compactSupportClass_congr (u 0) (u 1)))

end AtiyahSinger
