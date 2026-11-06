/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ExteriorBottComparison
public import AtiyahSinger.Topology.KTheoryLocalToGlobal
public import AtiyahSinger.Topology.SpinorThomClass
public import Mathlib.Topology.ShrinkingLemma

/-!
# The Thom isomorphism of the original positive even-rank spin symbol

Public module ID: M2169.

S03. The specified spinor symbol class acts through the existing proper-graph
construction along the original real bundle projection. The degree-zero map
has domain K(B), using the fixed compact-to-absolute comparison, and the same
class gives bijections in every nonpositive suspended degree. The resulting
additive equivalence retains that exact degree-zero map as its forward map.

Sources: Lawson--Michelsohn, Spin Geometry, Appendix C.12 and III.12,
Proposition 12.6; the class is the symbol of equation (12.13). Local spin
frames identify this original symbol with the already specified exterior
Bott symbol. The proof compares the actual supported triples in each local
spin frame, then uses all suspended degrees and finite closed-cover descent,
as in C.7 and Karoubi IV.1.3. The existing graded descent theorem supplies the
exact-sequence compatibility for this same class and its prescribed graph action.

The base is compact Hausdorff, and the supplied topological spin structure
has positive even real rank. The real bundle, metric, principal bundle,
spinor fibers and parity conventions are exactly those used to construct
spinorThomClass. No complex structure on the real bundle is assumed. The
bundle projection need not be proper: properness belongs to the graph used
by the existing action. Rank zero is treated separately with the native
unit-generated group. No smooth structure or Dirac operator is asserted.
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
  [CompactSpace B] [T2Space B]

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))

/-- Multiply by the original spinor symbol through the graph of the native bundle projection. -/
def TopologicalSpinStructure.spinThomHom (S : TopologicalSpinStructure m E o hm hP) :
    ComplexKZero B →+ CompactSupportKZero (TotalSpace RealModel E) :=
  (complexKZeroCompactSupportAction
    (⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩ :
      C(TotalSpace RealModel E, B))).flip S.spinorThomClass

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in

/-- SG C.12: the same original spinor class is a K-orientation in every nonpositive degree. -/
theorem TopologicalSpinStructure.spinorThomClass_isKOrientation
    (S : TopologicalSpinStructure m E o hm hP) (n : ℕ) :
    Function.Bijective
      ((compactSupportKAction n
        (⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩ :
          C(TotalSpace RealModel E, B))).flip S.spinorThomClass) := by
  /- Stage 1: use an original local principal spin section and its specified
  orthogonal frame. The associated-coordinate maps use that same section for
  both half-spin bundles. The representative formula for the global Clifford
  action identifies the original boundary with the fixed exterior Bott symbol,
  including its negative-square sign and interleaved orientation. The compact
  control restricts to the original zero section in these same coordinates.
  Stage 2: on every closed subset contained in this chart, retain the real
  suspension coordinate and compare the given graph action with external
  multiplication by that Bott class. Bott periodicity supplies bijectivity in
  each degree -n. The proof uses a local spin section, rather than assuming a
  continuous global section or a global complex structure on the real bundle.
  Stage 3: compact Hausdorff B admits a finite closed refinement of these local
  spin charts. Apply the one-generator local-to-global theorem simultaneously
  in all suspended degrees. Its proper restriction maps and Mayer--Vietoris
  boundary compatibility retain the same spinor class and graph action; these
  are supplied by the proved all-degree descent theorem.
  Stage 4: the finite-cover conclusion for degree -n is precisely the displayed
  map. No properness of the original vector-bundle projection is invoked. -/
  classical
  let R := EuclideanSpace ℝ (Fin (2 * m))
  let V := EuclideanSpace ℂ (Fin m)
  let Z := TotalSpace R E
  let p : C(Z, B) := ⟨π R E, FiberBundle.continuous_proj R E⟩
  -- A section over a closed subset supplies both the real frame and its spinor coordinates.
  have local_orientation (C : Set B) (hC : IsClosed C)
      (s : C(C, P)) (hs : ∀ x : C, projection (s x) = x.val) (k : ℕ) :
      letI := hC.locallyCompactSpace
      letI := (hC.preimage p.continuous).locallyCompactSpace
      Function.Bijective ((compactSupportKAction k (preimageSubspaceMap C p)).flip
        (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
          (hC.preimage p.continuous).isProperMap_subtypeVal S.spinorThomClass)) := by
    let := hC.isClosedEmbedding_subtypeVal.compactSpace
    let := hC.locallyCompactSpace
    let D := p ⁻¹' C
    have hD : IsClosed D := hC.preimage p.continuous
    let := hD.locallyCompactSpace
    let f (x : C) := S.frame (s x) x.val (hs x)
    let c := realSpinorCoordinateIsometry m
    let b := EuclideanSpace.basisFun (Fin (2 * m)) ℝ
    have hframe₀ (q : P) (x : B) (hx : projection q = x) (v : R) :
        (⟨x, S.frame q x hx v⟩ : Z) =
          ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 v⟩ := by
      unfold TopologicalSpinStructure.frame
      cases (S.frameMap_projection q).trans hx
      rfl
    have hframe (x : C) (v : R) :
        (⟨x.val, f x v⟩ : Z) =
          ⟨(S.frameMap (s x)).val.1, (S.frameMap (s x)).val.2 v⟩ :=
      hframe₀ (s x) x.val (hs x) v
    let := orthogonalFrameTopology (2 * m) E
    have hforget : Continuous (fun q : OrientedOrthogonalFrameBundle m E o ↦ q.val) :=
      continuous_induced_dom
    have hcols : Continuous (fun q : OrthogonalFrameBundle (2 * m) E ↦
        (q.1, fun j : Fin (2 * m) ↦ (⟨q.1, q.2 (b j)⟩ : Z))) :=
      continuous_induced_dom
    have hcolumn (j : Fin (2 * m)) : Continuous (fun x : C ↦
        (⟨x.val, f x (b j)⟩ : Z)) := by
      have h := (continuous_apply j).comp
        (hcols.comp (hforget.comp (S.frameMap.continuous.comp s.continuous))).snd
      exact h.congr (fun x ↦ (hframe x _).symm)
    -- The original metric recovers inverse frame coordinates continuously.
    have hinverse : Continuous (fun z : D ↦
        c ((f ⟨z.val.proj, z.property⟩).symm z.val.snd)) := by
      apply c.continuous.comp
      apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm.continuous.comp
      apply continuous_pi
      intro j
      have hbase : Continuous (fun z : D ↦ (⟨z.val.proj, z.property⟩ : C)) :=
        (p.continuous.comp continuous_subtype_val).subtype_mk _
      have hpair := ((hcolumn j).comp hbase).inner_bundle continuous_subtype_val
      apply hpair.congr
      intro z
      let x : C := ⟨z.val.proj, z.property⟩
      calc
        inner ℝ (f x (b j)) z.val.snd =
            inner ℝ (f x (b j)) (f x ((f x).symm z.val.snd)) := by
              rw [(f x).apply_symm_apply]
        _ = inner ℝ (b j) ((f x).symm z.val.snd) := (f x).inner_map_map _ _
        _ = _ := EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ _ j
    -- Forward continuity follows from the same continuous frame columns in a native chart.
    have hforward : Continuous (fun z : C × V ↦ (⟨z.1.val, f z.1 (c.symm z.2)⟩ : Z)) := by
      apply continuous_iff_continuousAt.mpr
      intro z₀
      let t := trivializationAt R E z₀.1.val
      have ht₀ : z₀.1.val ∈ t.baseSet := mem_baseSet_trivializationAt R E z₀.1.val
      let U : Set (C × V) := {z | z.1.val ∈ t.baseSet}
      have hU : IsOpen U := t.open_baseSet.preimage
        (continuous_subtype_val.comp continuous_fst)
      have hcoord (j : Fin (2 * m)) :
          ContinuousOn (fun z : C × V ↦ (t ⟨z.1.val, f z.1 (b j)⟩).2) U :=
        (t.continuousOn.comp ((hcolumn j).comp continuous_fst).continuousOn
          (fun z hz ↦ t.mem_source.mpr hz)).snd
      have hsum : ContinuousOn (fun z : C × V ↦
          ∑ j, (c.symm z.2) j • (t ⟨z.1.val, f z.1 (b j)⟩).2) U := by
        apply continuousOn_finsetSum
        intro j _
        exact ((continuous_apply j).comp
          ((EuclideanSpace.equiv (Fin (2 * m)) ℝ).continuous.comp
            (c.symm.continuous.comp continuous_snd))).continuousOn.smul (hcoord j)
      have hformula (z : C × V) (hz : z ∈ U) :
          (t ⟨z.1.val, f z.1 (c.symm z.2)⟩).2 =
            ∑ j, (c.symm z.2) j • (t ⟨z.1.val, f z.1 (b j)⟩).2 := by
        have he : f z.1 (c.symm z.2) = ∑ j, (c.symm z.2) j • f z.1 (b j) := by
          have h := congrArg (f z.1) (b.sum_repr (c.symm z.2))
          simpa only [b, map_sum, map_smul, EuclideanSpace.basisFun_repr] using h.symm
        change t.linearEquivAt ℝ z.1.val hz (f z.1 (c.symm z.2)) =
          ∑ j, (c.symm z.2) j • t.linearEquivAt ℝ z.1.val hz (f z.1 (b j))
        rw [he, map_sum]
        simp only [map_smul]
      apply (FiberBundle.continuousAt_totalSpace R _).mpr
      refine ⟨(continuous_subtype_val.comp continuous_fst).continuousAt, ?_⟩
      exact (hsum.congr (fun z hz ↦ hformula z hz)).continuousAt (hU.mem_nhds ht₀)
    let e : C × V ≃ₜ D :=
      { toFun z := ⟨⟨z.1.val, f z.1 (c.symm z.2)⟩, z.1.property⟩
        invFun z := (⟨z.val.proj, z.property⟩, c ((f ⟨z.val.proj, z.property⟩).symm z.val.snd))
        left_inv z := by simp only [LinearIsometryEquiv.symm_apply_apply,
          LinearIsometryEquiv.apply_symm_apply]
        right_inv z := by
          apply Subtype.ext
          change (⟨z.val.proj, f ⟨z.val.proj, z.property⟩
            (c.symm (c ((f ⟨z.val.proj, z.property⟩).symm z.val.snd)))⟩ : Z) = z.val
          simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
          rfl
        continuous_toFun := hforward.subtype_mk _
        continuous_invFun :=
          ((p.continuous.comp continuous_subtype_val).subtype_mk _).prodMk hinverse }
    let η : C(C × V, D) := ⟨e, e.continuous⟩
    let i : C(D, Z) := ⟨Subtype.val, continuous_subtype_val⟩
    have hi : IsProperMap i := hD.isProperMap_subtypeVal
    let μ := i.comp η
    have hμ : IsProperMap μ := hi.comp e.isProperMap
    let q : C(C × V, V) := ContinuousMap.snd
    have hq : IsProperMap q := isProperMap_snd_of_compactSpace
    let Parity (j : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) j
    let Q (j : ZMod 2) := HalfSpinorBundle m hP j
    let T (j : ZMod 2) := Bundle.Trivial V (Parity j)
    let A (j : ZMod 2) := (p : Z → B) *ᵖ (Q j)
    let AP (j : ZMod 2) := (μ : C × V → Z) *ᵖ (A j)
    let TP (j : ZMod 2) := (q : C × V → V) *ᵖ (T j)
    let ρ (j : ZMod 2) := complexSpinParityContRepresentation m j
    let (j : ZMod 2) : IsFiniteRank (Q j) :=
      isFiniteRank_associatedVector hP (ρ j) (continuous_complexSpinParityRepresentation m j)
    let (j : ZMod 2) : TopologicalSpace (TotalSpace Unit (T j)) :=
      modelTopology (Parity j) (T j)
    let (j : ZMod 2) : IsFiniteRank (T j) := isFiniteRank_model (Parity j) (T j)
    let (j : ZMod 2) : IsFiniteRank (A j) := isFiniteRank_pullback (E := Q j) p
    let (j : ZMod 2) : IsFiniteRank (AP j) := isFiniteRank_pullback (E := A j) μ
    let (j : ZMod 2) : IsFiniteRank (TP j) := isFiniteRank_pullback (E := T j) q
    -- The very same principal point gives both parity bundle isomorphisms.
    let coordinates (j : ZMod 2) : Hom (TP j) (AP j) :=
      { linearMap z := (associatedVectorFiberMkLinearEquiv hP (ρ j)
          (s z.1) (hs z.1)).toLinearMap
        continuous_total := by
          let D₀ := TotalSpace Unit (TP j)
          have hz : Continuous (fun z : D₀ ↦ z.proj) :=
            Pullback.continuous_proj Unit (T j) (q : C × V → V)
          let t := (unitTotalHomeomorph (Parity j) (T j)).trans
            (Bundle.Trivial.homeomorphProd V (Parity j))
          have hv : Continuous (fun z : D₀ ↦ z.snd) := t.continuous.snd.comp
            (Pullback.continuous_lift Unit (T j) (q : C × V → V))
          have hmk : Continuous (fun z : D₀ ↦
              (⟨z.proj.1.val, associatedVectorFiberMk hP (ρ j)
                (s z.proj.1) (hs z.proj.1) z.snd⟩ : TotalSpace Unit (Q j))) := by
            apply (associatedVectorTotalHomeomorph hP (ρ j)).isInducing.continuous_iff.mpr
            exact continuous_quot_mk.comp ((s.continuous.comp hz.fst).prodMk hv)
          apply (inducing_pullbackTotalSpaceEmbedding Unit (A j)
            (μ : C × V → Z)).continuous_iff.mpr
          apply hz.prodMk
          apply (inducing_pullbackTotalSpaceEmbedding Unit (Q j)
            (p : Z → B)).continuous_iff.mpr
          exact (μ.continuous.comp hz).prodMk hmk }
    let u (j : ZMod 2) := (coordinates j).toIso (fun z ↦
      (associatedVectorFiberMkLinearEquiv hP (ρ j) (s z.1) (hs z.1)).bijective)
    let a := S.spinorSymbolTriple.pullback μ hμ
    let aB := (exteriorBottTriple V).pullback q hq
    have hcontrol : a.control = aB.control := by
      ext z
      change (⟨z.1.val, f z.1 (c.symm z.2)⟩ : Z) ∈
        Set.range (zeroSection R E) ↔ z.2 ∈ ({0} : Set V)
      rw [Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx⟩
        have hn := congrArg (fun w : Z ↦ ‖w.snd‖) hx
        apply norm_eq_zero.mp
        simpa only [zeroSection, norm_zero, LinearIsometryEquiv.norm_map] using hn.symm
      · intro hz
        refine ⟨z.1.val, ?_⟩
        simp only [hz, map_zero]
        rfl
    -- The reciprocal inverse is retained automatically by the original boundary equivalences.
    have htriple : aB.congr (u 0) (u 1) =
        a.enlarge aB.control aB.isCompact_control hcontrol.subset := by
      change CompactSupportTriple.mk aB.control _ _ = CompactSupportTriple.mk aB.control _ _
      congr 1
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro w
      let v := (u 0).symm.linearEquiv z.val w
      have hw : associatedVectorFiberMk hP (ρ 0) (s z.val.1) (hs z.val.1) v = w :=
        ((u 0).linearEquiv z.val).apply_symm_apply w
      have h := S.cliffordParity_apply_mk (s z.val.1) z.val.1.val (hs z.val.1)
        (f z.val.1 (c.symm z.val.2)) 0 v
      have hc : c ((f z.val.1).symm (f z.val.1 (c.symm z.val.2))) = z.val.2 := by
        simp only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
      have hb : aB.boundary.linearEquiv z v = cliffordSymbolParity z.val.2 0 v :=
        (exteriorBottTriple V).boundary.pullback_apply q z v
      have ha : (a.enlarge aB.control aB.isCompact_control hcontrol.subset).boundary.linearEquiv
          z w = S.cliffordParity z.val.1.val (f z.val.1 (c.symm z.val.2)) 0 w :=
        (a.enlarge_apply aB.control aB.isCompact_control hcontrol.subset z w).trans
          (S.spinorSymbolTriple.boundary.pullback_apply μ
            ⟨z.val, fun hz ↦ z.property (hcontrol.subset hz)⟩ w)
      change (aB.congr (u 0) (u 1)).boundary.linearEquiv z w =
        (a.enlarge aB.control aB.isCompact_control hcontrol.subset).boundary.linearEquiv z w
      rw [aB.congr_apply, ha]
      change (u 1).linearEquiv z.val (aB.boundary.linearEquiv z v) = _
      rw [hb]
      change associatedVectorFiberMk hP (ρ 1) (s z.val.1) (hs z.val.1)
        (cliffordSymbolParity z.val.2 0 v) = _
      change S.cliffordParity z.val.1.val (f z.val.1 (c.symm z.val.2)) 0
        (associatedVectorFiberMk hP (ρ 0) (s z.val.1) (hs z.val.1) v) =
          associatedVectorFiberMk hP (ρ 1) (s z.val.1) (hs z.val.1)
            (cliffordSymbolParity (c ((f z.val.1).symm
              (f z.val.1 (c.symm z.val.2)))) 0 v) at h
      rw [hw, hc] at h
      exact h.symm
    have hclass : compactSupportKZeroPullback μ hμ S.spinorThomClass =
        compactSupportKZeroPullback q hq (exteriorBottClass V) := by
      change compactSupportKZeroPullback μ hμ S.spinorSymbolTriple.compactSupportClass =
        compactSupportKZeroPullback q hq (exteriorBottTriple V).compactSupportClass
      rw [← CompactSupportTriple.compactSupportClass_pullback,
        ← CompactSupportTriple.compactSupportClass_pullback]
      change a.compactSupportClass = aB.compactSupportClass
      exact (a.compactSupportClass_enlarge
        aB.control aB.isCompact_control hcontrol.subset).symm.trans
        ((congrArg CompactSupportTriple.compactSupportClass htriple.symm).trans
          (aB.compactSupportClass_congr (u 0) (u 1)))
    let r := preimageSubspaceMap C p
    let uD := compactSupportKZeroPullback i hi S.spinorThomClass
    have hclassD : compactSupportKZeroPullback η e.isProperMap uD =
        compactSupportKZeroPullback q hq (exteriorBottClass V) := by
      change compactSupportKZeroPullback η e.isProperMap
        (compactSupportKZeroPullback i hi S.spinorThomClass) = _
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      exact hclass
    -- Keep all suspension coordinates and compare the specified graph with external Bott product.
    let T₀ := Fin k → ℝ
    let perm : (C × V) × T₀ ≃ₜ (C × T₀) × V :=
      (Homeomorph.prodAssoc C V T₀).trans
        (((Homeomorph.refl C).prodCongr (Homeomorph.prodComm V T₀)).trans
          (Homeomorph.prodAssoc C T₀ V).symm)
    let H := compactSupportKZeroHomeomorphEquiv perm
    let G := compactSupportKHomeomorphEquiv k e.symm
    let Bott : CompactSupportK k C →+ CompactSupportKZero ((C × T₀) × V) :=
      compactSupportKZeroExternalProduct.flip (exteriorBottClass V)
    have hBott : Function.Bijective Bott := exteriorBottExternalProduct_bijective (C × T₀) V
    have hsquare (x : CompactSupportK k C) : H (G (compactSupportKAction k r x uD)) = Bott x := by
      change H (compactSupportKPullback k η e.isProperMap
        (compactSupportKAction k r x uD)) = _
      rw [compactSupportKPullback_action, hclassD]
      have hbase : r.comp η = ContinuousMap.fst := rfl
      rw [hbase]
      let graph : C((C × V) × T₀, (C × T₀) × (C × V)) :=
        (ContinuousMap.fst.prodMap (ContinuousMap.id T₀)).prodMk ContinuousMap.fst
      let retract : C((C × T₀) × (C × V), (C × V) × T₀) :=
        ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
      have hgraph : IsProperMap graph :=
        isProperMap_of_comp_of_t2 graph.continuous retract.continuous isProperMap_id
      let lift := (ContinuousMap.id (C × T₀)).prodMap q
      have hlift : IsProperMap lift := isProperMap_id.prodMap hq
      let back : C((C × T₀) × V, (C × V) × T₀) := ⟨perm.symm, perm.symm.continuous⟩
      change compactSupportKZeroPullback back perm.symm.isProperMap
        (compactSupportKZeroPullback graph hgraph
          (compactSupportKZeroExternalProduct x
            (compactSupportKZeroPullback q hq (exteriorBottClass V)))) = Bott x
      have hproduct := compactSupportKZeroExternalProduct_properPullback
        (ContinuousMap.id (C × T₀)) isProperMap_id q hq x (exteriorBottClass V)
      rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
      rw [← hproduct, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      have hid : lift.comp (graph.comp back) = ContinuousMap.id ((C × T₀) × V) := rfl
      change compactSupportKZeroPullback (lift.comp (graph.comp back))
        (hlift.comp (hgraph.comp perm.symm.isProperMap))
          (compactSupportKZeroExternalProduct x (exteriorBottClass V)) = Bott x
      simp only [hid, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
      rfl
    constructor
    · intro x y hxy
      apply hBott.injective
      exact (hsquare x).symm.trans ((congrArg (fun z ↦ H (G z)) hxy).trans (hsquare y))
    · intro y
      obtain ⟨x, hx⟩ := hBott.surjective (H (G y))
      refine ⟨x, G.injective (H.injective ?_)⟩
      exact (hsquare x).trans hx
  -- The one-generator Leray--Hirsch map is exactly the original action on the chosen class.
  have one_generator {X Y : Type _}
      [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
      (k : ℕ) (f : C(Y, X)) (u : CompactSupportKZero Y) :
      Function.Bijective (compactSupportKLerayHirschMap k f (fun _ : Fin 1 ↦ u)) ↔
        Function.Bijective ((compactSupportKAction k f).flip u) := by
    have hsum (x : Fin 1 → CompactSupportK k X) :
        compactSupportKLerayHirschMap k f (fun _ : Fin 1 ↦ u) x =
          ((compactSupportKAction k f).flip u) (x 0) := by
      change (∑ j : Fin 1, compactSupportKAction k f (x j) u) = _
      simp
    constructor
    · intro h
      constructor
      · intro x y hxy
        have heq : (fun _ : Fin 1 ↦ x) = (fun _ : Fin 1 ↦ y) :=
          h.injective (by simpa only [hsum] using hxy)
        exact congrFun heq 0
      · intro y
        obtain ⟨x, hx⟩ := h.surjective y
        exact ⟨x 0, (hsum x).symm.trans hx⟩
    · intro h
      constructor
      · intro x y hxy
        have heq : x 0 = y 0 := h.injective (by simpa only [hsum] using hxy)
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        simpa only [hj] using heq
      · intro y
        obtain ⟨x, hx⟩ := h.surjective y
        exact ⟨fun _ ↦ x, (hsum (fun _ ↦ x)).trans hx⟩
  -- Shrink finitely many of the original principal charts to a closed cover.
  choose t ht he using hP.exists_trivialization
  obtain ⟨J, hJ⟩ := isCompact_univ.elim_finite_subcover
    (fun x : B ↦ (t x).baseSet) (fun x ↦ (t x).open_baseSet) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, ht x⟩)
  let index : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let U (j : Fin (Fintype.card J)) : Set B := (t (index j).val).baseSet
  have hU (j : Fin (Fintype.card J)) : IsOpen (U j) := (t (index j).val).open_baseSet
  have hcoverU : ⋃ j, U j = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨j, hj, hx⟩ := Set.mem_iUnion₂.mp (hJ (Set.mem_univ x))
    refine Set.mem_iUnion.mpr ⟨index.symm ⟨j, hj⟩, ?_⟩
    change x ∈ (t (index (index.symm ⟨j, hj⟩)).val).baseSet
    rw [index.apply_symm_apply]
    exact hx
  obtain ⟨W, hcoverW, hW, hWU⟩ := exists_iUnion_eq_closed_subset hU
    (fun _ ↦ Set.toFinite _) hcoverU
  have hlocal (j : Fin (Fintype.card J)) (C : Set B) (hC : IsClosed C)
      (hCW : C ⊆ W j) :
      letI := hC.locallyCompactSpace
      letI := (hC.preimage p.continuous).locallyCompactSpace
      ∀ k : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap k (preimageSubspaceMap C p)
          (fun _ : Fin 1 ↦ compactSupportKZeroPullback
            ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage p.continuous).isProperMap_subtypeVal S.spinorThomClass)) := by
    let := hC.locallyCompactSpace
    let := (hC.preimage p.continuous).locallyCompactSpace
    let chart := t (index j).val
    have hchart (x : C) : x.val ∈ chart.baseSet := hWU j (hCW x.property)
    let s : C(C, P) :=
      ⟨fun x ↦ chart.toOpenPartialHomeomorph.symm (x.val, 1),
        chart.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
          (continuous_subtype_val.prodMk continuous_const)
          (fun x ↦ chart.mem_target.mpr (hchart x))⟩
    have hs (x : C) : projection (s x) = x.val := chart.proj_symm_apply' (hchart x)
    intro k
    exact (one_generator k (preimageSubspaceMap C p) _).mpr (local_orientation C hC s hs k)
  exact (one_generator n p S.spinorThomClass).mp
    (compactSupportKLerayHirschMap_bijective_of_closed_cover
      p (fun _ : Fin 1 ↦ S.spinorThomClass) W hW hcoverW hlocal n)

/-- SG III.12.6: the prescribed spin-symbol multiplication is a degree-zero Thom isomorphism. -/
theorem TopologicalSpinStructure.spinThomHom_bijective
    (S : TopologicalSpinStructure m E o hm hP) : Function.Bijective S.spinThomHom := by
  /- Stage 1: specialize the preceding K-orientation theorem to n=0. The fixed
  zero-suspension equivalences on B and on the original total space identify
  its suspended graph action with compactSupportKZeroAction, by the existing
  compactSupportKAction_zero comparison on that same projection and class.
  Stage 2: the compact-base comparison identifies Kc(B) with K(B). Its inverse
  is exactly the first factor in complexKZeroCompactSupportAction, hence the
  resulting map is spinThomHom itself. Compose these specified bijections to
  obtain the assertion without selecting an unrelated abstract isomorphism. -/
  let p : C(TotalSpace RealModel E, B) :=
    ⟨π RealModel E, FiberBundle.continuous_proj RealModel E⟩
  let source := (compactSupportKZeroDegreeEquiv B).trans (compactSupportKZeroCompactEquiv B)
  let target := compactSupportKZeroDegreeEquiv (TotalSpace RealModel E)
  let thom := AddEquiv.ofBijective ((compactSupportKAction 0 p).flip S.spinorThomClass)
    (S.spinorThomClass_isKOrientation 0)
  -- The zero-suspension comparison retains the same graph and the same spinor class.
  have hcompare (x : CompactSupportK 0 B) : target (thom x) = S.spinThomHom (source x) := by
    change compactSupportKZeroDegreeEquiv (TotalSpace RealModel E)
      (compactSupportKAction 0 p x S.spinorThomClass) = _
    rw [compactSupportKAction_zero]
    change compactSupportKZeroAction p (compactSupportKZeroDegreeEquiv B x) S.spinorThomClass =
      compactSupportKZeroAction p ((compactSupportKZeroCompactEquiv B).symm
        ((compactSupportKZeroCompactEquiv B) (compactSupportKZeroDegreeEquiv B x)))
          S.spinorThomClass
    rw [AddEquiv.symm_apply_apply]
  constructor
  · intro x y hxy
    have h : thom (source.symm x) = thom (source.symm y) := by
      apply target.injective
      rw [hcompare, hcompare, source.apply_symm_apply, source.apply_symm_apply]
      exact hxy
    exact source.symm.injective (thom.injective h)
  · intro y
    refine ⟨source (thom.symm (target.symm y)), ?_⟩
    rw [← hcompare, thom.apply_symm_apply, target.apply_symm_apply]

/-- The spin Thom equivalence has the original graph-action multiplication as forward map. -/
def TopologicalSpinStructure.spinThomEquiv (S : TopologicalSpinStructure m E o hm hP) :
    ComplexKZero B ≃+ CompactSupportKZero (TotalSpace RealModel E) :=
  AddEquiv.ofBijective S.spinThomHom S.spinThomHom_bijective

end AtiyahSinger
