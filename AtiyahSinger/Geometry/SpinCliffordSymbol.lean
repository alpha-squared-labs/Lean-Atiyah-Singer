/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinFrame
public import AtiyahSinger.Topology.AssociatedVectorCoordinates
public import AtiyahSinger.Topology.SpinorBundle

/-!
# Clifford multiplication on the original associated spinor bundles

Public module ID: M1445.

SC01. A point of the specified principal Spin fiber gives both its actual
oriented orthogonal frame and coordinates on the original associated spinor
fibers. Conjugating the original model Clifford symbol through these maps
constructs the global fiber map. The representative formulas below show that
it has this same value at every principal point, so the algebraic choice in
the definition is not assumed to be a continuous global section.

The half-spin symbol is a continuous map between the two original pulled-back
bundles over the total space of the given real metric bundle. Its full-spin
square is negative squared length, and its positive-half inverse off zero is
minus the negative-half action divided by squared length. The parity labels
and interleaved coordinate orientation are those already fixed in S01/E07.

Sources: Lawson--Michelsohn, Spin Geometry, II.3 pp.93--99 and III.12 (12.13),
p.242. This continuous construction does not introduce a connection or a
Dirac operator. Compact support and the K class are assembled separately.
The representative, square, continuity and inverse identities are proved on
these original associated fibers and pullback topologies.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orientedOrthogonalFrameTopology exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace
  associatedVectorFiberAddCommGroup associatedVectorFiberModule associatedVectorTotalTopology

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

/-- Clifford multiplication on the actual full-spin quotient fiber over the given base point. -/
def TopologicalSpinStructure.clifford (S : TopologicalSpinStructure m E o hm hP)
    (b : B) (v : E b) : Module.End ℂ (SpinorBundle m hP b) :=
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP (complexSpinContRepresentation m) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  e.toLinearMap.comp ((cliffordSymbol w).comp e.symm.toLinearMap)

/-- The actual parity-changing Clifford map on the original associated half-spin fibers. -/
def TopologicalSpinStructure.cliffordParity (S : TopologicalSpinStructure m E o hm hP)
    (b : B) (v : E b) (i : ZMod 2) :
    HalfSpinorBundle m hP i b →ₗ[ℂ] HalfSpinorBundle m hP (i + 1) b :=
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p.val p.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m (i + 1)) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  f.toLinearMap.comp ((cliffordSymbolParity w i).comp e.symm.toLinearMap)

/-- The full-spin action has its prescribed value at every original principal representative. -/
theorem TopologicalSpinStructure.clifford_apply_mk (S : TopologicalSpinStructure m E o hm hP)
    (p : P) (b : B) (hp : projection p = b) (v : E b) (s : ComplexSpinor m) :
    S.clifford b v (associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp s) =
      associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp
        (cliffordSymbol (realSpinorCoordinateIsometry m ((S.frame p b hp).symm v)) s) := by
  /- Stage 1: compare p with the principal point chosen in the definition by
  the unique right group element of the original principal torsor. The given
  frame equivariance says that frame coordinates change by the inverse of
  that same vector representation, while associated coordinates change by
  the spin representation, using [p*g,s]=[p,rho(g)s].
  Stage 2: complexSpinRepresentation_cliffordSymbol intertwines precisely
  these two changes. Therefore conjugating the model symbol gives the same
  map in either set of coordinates, proving the displayed formula for the
  actual original representative. No continuous global choice is used. -/
  -- Compare the supplied representative with exactly the principal point in the definition.
  let p₀ : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinContRepresentation m) p₀.val p₀.property
  let w := realSpinorCoordinateIsometry m ((S.frame p b hp).symm v)
  let w₀ := realSpinorCoordinateIsometry m ((S.frame p₀.val b p₀.property).symm v)
  obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p₀.val p (p₀.property.trans hp.symm)
  have hframe (q : P) (hq : projection q = b) (z : EuclideanSpace ℝ (Fin (2 * m))) :
      (⟨b, S.frame q b hq z⟩ : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 z⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  -- The same group element relates the original frame coordinates by its vector action.
  have hcoords : realSpinVectorRepresentation m g w = w₀ := by
    have h := S.equivariant g p₀.val ((S.frame p b hp).symm v)
    rw [hg, ← hframe p hp, ← hframe p₀.val p₀.property] at h
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    apply (realSpinorCoordinateIsometry m).symm.injective
    apply (S.frame p₀.val b p₀.property).injective
    rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    exact ((TotalSpace.mk_injective b) h).symm
  have hrep (t : ComplexSpinor m) :
      associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp t =
        e (complexSpinRepresentation m g t) := by
    let := associatedRepresentationAction (complexSpinContRepresentation m)
    apply Subtype.ext
    change associatedBundleMk _ _ _ p t =
      associatedBundleMk _ _ _ p₀.val (complexSpinRepresentation m g t)
    rw [← hg]
    exact associatedBundleMk_smul p₀.val g t
  -- Clifford covariance cancels the coordinate change on the actual quotient fiber.
  change e (cliffordSymbol w₀ (e.symm
    (associatedVectorFiberMk hP (complexSpinContRepresentation m) p hp s))) = _
  rw [hrep, e.symm_apply_apply, ← hcoords, complexSpinRepresentation_cliffordSymbol]
  exact (hrep (cliffordSymbol w s)).symm

/-- The half-spin action retains the same representative and the original model parity symbol. -/
theorem TopologicalSpinStructure.cliffordParity_apply_mk
    (S : TopologicalSpinStructure m E o hm hP) (p : P) (b : B) (hp : projection p = b)
    (v : E b) (i : ZMod 2)
    (s : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :
    S.cliffordParity b v i
        (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp s) =
      associatedVectorFiberMk hP (complexSpinParityContRepresentation m (i + 1)) p hp
        (cliffordSymbolParity
          (realSpinorCoordinateIsometry m ((S.frame p b hp).symm v)) i s) := by
  /- Stage 1: apply the same torsor change of coordinates as for the full
  spinor representation. The original action preserves exterior parity,
  and Clifford multiplication changes it by one in ZMod 2.
  Stage 2: restrict the full Clifford covariance identity to these very
  subspaces. Both original associated quotient maps use the same p and hp,
  so the result descends without an independently chosen half-spin frame. -/
  -- Compare the supplied representative with exactly the principal point in the definition.
  let p₀ : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p₀.val p₀.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m (i + 1)) p₀.val p₀.property
  let w := realSpinorCoordinateIsometry m ((S.frame p b hp).symm v)
  let w₀ := realSpinorCoordinateIsometry m ((S.frame p₀.val b p₀.property).symm v)
  obtain ⟨g, hg, _⟩ := hP.existsUnique_smul p₀.val p (p₀.property.trans hp.symm)
  have hframe (q : P) (hq : projection q = b) (z : EuclideanSpace ℝ (Fin (2 * m))) :
      (⟨b, S.frame q b hq z⟩ : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 z⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  -- The same group element relates the original frame coordinates by its vector action.
  have hcoords : realSpinVectorRepresentation m g w = w₀ := by
    have h := S.equivariant g p₀.val ((S.frame p b hp).symm v)
    rw [hg, ← hframe p hp, ← hframe p₀.val p₀.property] at h
    rw [LinearIsometryEquiv.apply_symm_apply] at h
    apply (realSpinorCoordinateIsometry m).symm.injective
    apply (S.frame p₀.val b p₀.property).injective
    rw [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    exact ((TotalSpace.mk_injective b) h).symm
  have hrep (j : ZMod 2)
      (t : CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) j) :
      associatedVectorFiberMk hP (complexSpinParityContRepresentation m j) p hp t =
        associatedVectorFiberMkLinearEquiv hP (complexSpinParityContRepresentation m j)
          p₀.val p₀.property (complexSpinParityRepresentation m j g t) := by
    let := associatedRepresentationAction (complexSpinParityContRepresentation m j)
    apply Subtype.ext
    change associatedBundleMk _ _ _ p t =
      associatedBundleMk _ _ _ p₀.val (complexSpinParityRepresentation m j g t)
    rw [← hg]
    exact associatedBundleMk_smul p₀.val g t
  -- The full covariance law restricts to the specified parity subspaces and actions.
  have hcov : cliffordSymbolParity (realSpinVectorRepresentation m g w) i
      (complexSpinParityRepresentation m i g s) =
        complexSpinParityRepresentation m (i + 1) g (cliffordSymbolParity w i s) := by
    apply Subtype.ext
    exact complexSpinRepresentation_cliffordSymbol m g w s.val
  change f (cliffordSymbolParity w₀ i (e.symm
    (associatedVectorFiberMk hP (complexSpinParityContRepresentation m i) p hp s))) = _
  rw [hrep i s, e.symm_apply_apply, ← hcoords, hcov]
  exact (hrep (i + 1) (cliffordSymbolParity w i s)).symm

/-- The full geometric Clifford action squares to negative original squared length. -/
theorem TopologicalSpinStructure.clifford_sq (S : TopologicalSpinStructure m E o hm hP)
    (b : B) (v : E b) (s : SpinorBundle m hP b) :
    S.clifford b v (S.clifford b v s) = -(‖v‖ ^ 2 : ℂ) • s := by
  /- Stage 1: use one principal point to identify the original spinor fiber
  with the full model space. The same frame and canonical real coordinate
  isometry send v to a model vector w with exactly the same norm.
  Stage 2: the square is the conjugate of cliffordSymbol_sq at w. The middle
  inverse coordinate maps cancel, and linearity transports the scalar back
  to the original associated fiber. The formula includes v=0. -/
  -- Use precisely the principal point and the two coordinate maps in the original definition.
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP (complexSpinContRepresentation m) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  change e (cliffordSymbol w (e.symm (e (cliffordSymbol w (e.symm s))))) = _
  rw [e.symm_apply_apply]
  -- Cancel the middle coordinates and transport the original negative-square identity.
  have hsq := LinearMap.congr_fun (cliffordSymbol_sq w) (e.symm s)
  simp only [pow_two, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at hsq
  rw [hsq, map_smul, e.apply_symm_apply]
  simp only [w, LinearIsometryEquiv.norm_map, pow_two]

/-- Clifford multiplication defines a continuous total map on the original parity pullbacks. -/
theorem TopologicalSpinStructure.continuous_cliffordParity
    (S : TopologicalSpinStructure m E o hm hP) (i : ZMod 2) :
    Continuous (fun z : TotalSpace Unit
      ((fun t : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E ↦ t.proj) *ᵖ
        (HalfSpinorBundle m hP i)) ↦
      (⟨z.proj, S.cliffordParity z.proj.proj z.proj.snd i z.snd⟩ : TotalSpace Unit
        ((fun t : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E ↦ t.proj) *ᵖ
          (HalfSpinorBundle m hP (i + 1))))) := by
  /- Stage 1: use a continuous local principal section of the original hP.
  Compose it with S.frameMap to obtain the original continuous orthogonal
  frames. In these finite-dimensional frames, both the forward coordinate
  maps and their inverses are continuous in the original bundle topology.
  Stage 2: cliffordParity_apply_mk identifies the defined map in those same
  associated local charts with the original jointly continuous model
  cliffordSymbolParity. The pullback topologies retain the base vector and
  spinor coordinate, so these local expressions give continuity on their
  whole total spaces. The principal neighborhoods cover B, hence also the
  real bundle total space. No continuity of the definition's global choice
  of principal points is needed. -/
  -- Work in one original principal chart near each base point of the pullback total space.
  let R := EuclideanSpace ℝ (Fin (2 * m))
  let V := EuclideanSpace ℂ (Fin m)
  let Parity (j : ZMod 2) : Type := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ V) j
  let G : Type := spinGroup (realSpinorQuadraticForm m)
  let ρ (j : ZMod 2) : ContRepresentation ℂ G (Parity j) :=
    complexSpinParityContRepresentation m j
  let : ∀ j, MulAction G (Parity j) := fun j ↦ associatedRepresentationAction (ρ j)
  let : ∀ j, ContinuousSMul G (Parity j) := fun j ↦
    ⟨continuous_complexSpinParityRepresentation m j⟩
  let X := TotalSpace Unit
    ((fun t : TotalSpace R E ↦ t.proj) *ᵖ (HalfSpinorBundle m hP i))
  have hvector : Continuous (fun z : X ↦ z.proj) :=
    Pullback.continuous_proj Unit (HalfSpinorBundle m hP i) (fun t : TotalSpace R E ↦ t.proj)
  have hbase : Continuous (fun z : X ↦ z.proj.proj) :=
    (FiberBundle.continuous_proj R E).comp hvector
  apply continuous_iff_continuousAt.mpr
  intro z₀
  obtain ⟨t, ht₀, ht⟩ := hP.exists_trivialization z₀.proj.proj
  let U : Set X := {z | z.proj.proj ∈ t.baseSet}
  have hU : IsOpen U := t.open_baseSet.preimage hbase
  let p (z : U) : P := t.toOpenPartialHomeomorph.symm (z.val.proj.proj, 1)
  have hp (z : U) : projection (p z) = z.val.proj.proj := t.proj_symm_apply' z.property
  have hpcont : Continuous p :=
    t.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
      ((hbase.comp continuous_subtype_val).prodMk continuous_const)
      (fun z ↦ t.mem_target.mpr z.property)
  let f (z : U) := S.frame (p z) z.val.proj.proj (hp z)
  have hframe₀ (q : P) (b : B) (hq : projection q = b) (v : R) :
      (⟨b, S.frame q b hq v⟩ : TotalSpace R E) =
        ⟨(S.frameMap q).val.1, (S.frameMap q).val.2 v⟩ := by
    unfold TopologicalSpinStructure.frame
    cases (S.frameMap_projection q).trans hq
    rfl
  have hframe (z : U) (v : R) :
      (⟨z.val.proj.proj, f z v⟩ : TotalSpace R E) =
        ⟨(S.frameMap (p z)).val.1, (S.frameMap (p z)).val.2 v⟩ :=
    hframe₀ (p z) z.val.proj.proj (hp z) v
  -- Inverse frame coordinates are the original metric pairings with its continuous columns.
  let := orthogonalFrameTopology (2 * m) E
  have hforget : Continuous (fun q : OrientedOrthogonalFrameBundle m E o ↦ q.val) :=
    continuous_induced_dom
  have hcols : Continuous (fun q : OrthogonalFrameBundle (2 * m) E ↦
      (q.1, fun j : Fin (2 * m) ↦
        (⟨q.1, q.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩ : TotalSpace R E))) :=
    continuous_induced_dom
  have hcolumn (j : Fin (2 * m)) : Continuous (fun z : U ↦
      (⟨z.val.proj.proj, f z (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)⟩ :
        TotalSpace R E)) := by
    have h := (continuous_apply j).comp
      (hcols.comp (hforget.comp (S.frameMap.continuous.comp hpcont))).snd
    exact h.congr (fun z ↦ (hframe z _).symm)
  have hreal : Continuous (fun z : U ↦ (f z).symm z.val.proj.snd) := by
    apply (EuclideanSpace.equiv (Fin (2 * m)) ℝ).symm.continuous.comp
    apply continuous_pi
    intro j
    have hpair := (hcolumn j).inner_bundle (hvector.comp continuous_subtype_val)
    apply hpair.congr
    intro z
    calc
      inner ℝ (f z (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)) z.val.proj.snd =
          inner ℝ (f z (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j))
            (f z ((f z).symm z.val.proj.snd)) := by rw [(f z).apply_symm_apply]
      _ = inner ℝ (EuclideanSpace.basisFun (Fin (2 * m)) ℝ j)
            ((f z).symm z.val.proj.snd) := (f z).inner_map_map _ _
      _ = _ := EuclideanSpace.basisFun_inner (Fin (2 * m)) ℝ _ j
  let w : U → V := fun z ↦ realSpinorCoordinateIsometry m ((f z).symm z.val.proj.snd)
  have hw : Continuous w :=
    (realSpinorCoordinateIsometry m).continuous.comp hreal
  -- The actual associated chart gives continuous spinor coordinates at the same principal section.
  let H := associatedVectorTotalHomeomorph hP (ρ i)
  obtain ⟨tA, hAb, _, hAi⟩ := exists_associatedBundleTrivialization (F := Parity i) hP t ht
  let q (z : U) := H ⟨z.val.proj.proj, z.val.snd⟩
  have hq : Continuous q := H.continuous.comp
    ((Pullback.continuous_lift Unit (HalfSpinorBundle m hP i)
      (fun t : TotalSpace R E ↦ t.proj)).comp continuous_subtype_val)
  have hqs (z : U) : q z ∈ tA.source := by
    apply tA.mem_source.mpr
    change associatedBundleProjection (F := Parity i) hP (q z) ∈ tA.baseSet
    change associatedBundleProjection (F := Parity i) hP z.val.snd.val ∈ tA.baseSet
    rw [z.val.snd.property, hAb]
    exact z.property
  let a (z : U) : Parity i := (tA (q z)).2
  have ha : Continuous a :=
    (tA.toOpenPartialHomeomorph.continuousOn.comp_continuous hq hqs).snd
  have hin (z : U) :
      associatedVectorFiberMk hP (ρ i) (p z) (hp z) (a z) = z.val.snd := by
    apply Subtype.ext
    change associatedBundleMk G P (Parity i) (p z) (a z) = q z
    rw [← hAi z.val.proj.proj (a z) z.property]
    have hb : (tA (q z)).1 = z.val.proj.proj :=
      (tA.proj_toFun (q z) (hqs z)).trans z.val.snd.property
    change tA.toOpenPartialHomeomorph.symm (z.val.proj.proj, (tA (q z)).2) = q z
    rw [← hb]
    exact tA.toOpenPartialHomeomorph.left_inv (hqs z)
  -- In these coordinates the map is the original jointly continuous model Clifford action.
  have hsymbol : Continuous (fun z : U ↦
      cliffordSymbolParity (w z) i (a z)) :=
    (continuous_cliffordSymbolParity (V := V) i).comp
      (f := fun z : U ↦ (w z, a z)) (hw.prodMk ha)
  have htarget : Continuous (fun z : U ↦
      (⟨z.val.proj.proj, S.cliffordParity z.val.proj.proj z.val.proj.snd i z.val.snd⟩ :
        TotalSpace Unit (HalfSpinorBundle m hP (i + 1)))) := by
    apply (associatedVectorTotalHomeomorph hP (ρ (i + 1))).isInducing.continuous_iff.mpr
    have hquot : Continuous (fun z : U ↦ associatedBundleMk G P (Parity (i + 1))
        (p z) (cliffordSymbolParity (w z) i (a z))) :=
      continuous_quot_mk.comp (hpcont.prodMk hsymbol)
    apply hquot.congr
    intro z
    change _ = (S.cliffordParity z.val.proj.proj z.val.proj.snd i z.val.snd).val
    have h := S.cliffordParity_apply_mk (p z) z.val.proj.proj (hp z)
      z.val.proj.snd i (a z)
    rw [hin z] at h
    exact (congrArg Subtype.val h).symm
  have hlocal : Continuous (fun z : U ↦
      (⟨z.val.proj, S.cliffordParity z.val.proj.proj z.val.proj.snd i z.val.snd⟩ :
        TotalSpace Unit ((fun t : TotalSpace R E ↦ t.proj) *ᵖ
          (HalfSpinorBundle m hP (i + 1))))) := by
    apply (inducing_pullbackTotalSpaceEmbedding Unit (HalfSpinorBundle m hP (i + 1))
      (fun t : TotalSpace R E ↦ t.proj)).continuous_iff.mpr
    exact (hvector.comp continuous_subtype_val).prodMk htarget
  -- The original principal neighborhoods cover every pullback point, so locality finishes.
  exact (continuousOn_iff_continuous_domRestrict.mpr hlocal).continuousAt
    (hU.mem_nhds ht₀)

/-- The actual parity Clifford symbol as a map between the original pulled-back bundles. -/
def TopologicalSpinStructure.cliffordParityHom (S : TopologicalSpinStructure m E o hm hP)
    (i : ZMod 2) :
    ComplexBundle.Hom
      ((fun t : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E ↦ t.proj) *ᵖ
        (HalfSpinorBundle m hP i))
      ((fun t : TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E ↦ t.proj) *ᵖ
        (HalfSpinorBundle m hP (i + 1))) where
  linearMap z := S.cliffordParity z.proj z.snd i
  continuous_total := S.continuous_cliffordParity i

/-- The geometric parity symbol is bijective when the real vector is nonzero. -/
theorem TopologicalSpinStructure.cliffordParity_bijective
    (S : TopologicalSpinStructure m E o hm hP) (b : B) (v : E b) (hv : v ≠ 0) (i : ZMod 2) :
    Function.Bijective (S.cliffordParity b v i) := by
  /- Both selected associated coordinate maps are linear equivalences. The
  original frame and canonical coordinate isometry send nonzero v to a
  nonzero model vector. Apply cliffordSymbolParity_bijective at that vector,
  then compose its injectivity and surjectivity with the same equivalences.
  This proves invertibility of the actual geometric symbol, not merely of
  some abstract isomorphism between fibers of equal dimension. -/
  -- The existing definition uses genuine linear equivalences at one fixed principal point.
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m i) p.val p.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m (i + 1)) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  have hw : w ≠ 0 := by
    intro h
    apply hv
    apply (S.frame p.val b p.property).symm.injective
    apply (realSpinorCoordinateIsometry m).injective
    simpa only [map_zero] using h
  -- Both coordinate changes preserve bijectivity of this same nonzero model symbol.
  exact f.bijective.comp ((cliffordSymbolParity_bijective w hw i).comp e.symm.bijective)

/-- The off-zero equivalence with exactly the specified parity Clifford forward map. -/
def TopologicalSpinStructure.cliffordParityEquiv (S : TopologicalSpinStructure m E o hm hP)
    (b : B) (v : E b) (hv : v ≠ 0) (i : ZMod 2) :
    HalfSpinorBundle m hP i b ≃ₗ[ℂ] HalfSpinorBundle m hP (i + 1) b :=
  LinearEquiv.ofBijective (S.cliffordParity b v i) (S.cliffordParity_bijective b v hv i)

/-- The inverse positive-half symbol is minus the negative-half symbol divided by length squared. -/
theorem TopologicalSpinStructure.cliffordParityEquiv_zero_symm_apply
    (S : TopologicalSpinStructure m E o hm hP) (b : B) (v : E b) (hv : v ≠ 0)
    (s : HalfSpinorBundle m hP 1 b) :
    (S.cliffordParityEquiv b v hv 0).symm s =
      -(‖v‖ ^ 2 : ℂ)⁻¹ • S.cliffordParity b v 1 s := by
  /- Stage 1: express both parity maps in the coordinates of the same
  principal point. Their composition is negative squared length on each
  parity space by the original Clifford square identity.
  Stage 2: v is nonzero, so its squared length is nonzero. The displayed
  negative reciprocal multiple is a two-sided inverse. Uniqueness identifies
  it with the inverse of the equivalence built from the actual forward map.
  The closed index equality 1+1=0 preserves the positive-half target. -/
  -- Express both half-spin maps in exactly the point chosen by the original definitions.
  let p : {p : P // projection p = b} :=
    ⟨Classical.choose (hP.projection_properties.2.2 b),
      Classical.choose_spec (hP.projection_properties.2.2 b)⟩
  let e := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 0) p.val p.property
  let f := associatedVectorFiberMkLinearEquiv hP
    (complexSpinParityContRepresentation m 1) p.val p.property
  let w := realSpinorCoordinateIsometry m ((S.frame p.val b p.property).symm v)
  have hw : w ≠ 0 := by
    intro h
    apply hv
    apply (S.frame p.val b p.property).symm.injective
    apply (realSpinorCoordinateIsometry m).injective
    simpa only [map_zero] using h
  -- Uniqueness of the inverse reduces the geometric formula to the actual model inverse.
  apply (S.cliffordParityEquiv b v hv 0).injective
  rw [LinearEquiv.apply_symm_apply]
  change s = f (cliffordSymbolParity w 0
    (e.symm (-(‖v‖ ^ 2 : ℂ)⁻¹ • e (cliffordSymbolParity w 1 (f.symm s)))))
  rw [map_smul, e.symm_apply_apply]
  have hmodel : (cliffordSymbolParityEquiv w hw 0).symm (f.symm s) =
      -(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbolParity w 1 (f.symm s) := by
    apply Subtype.ext
    change ((cliffordSymbolParityEquiv w hw 0).symm (f.symm s) : ComplexSpinor m) =
      -(‖v‖ ^ 2 : ℂ)⁻¹ • cliffordSymbol w (f.symm s).val
    have h := cliffordSymbolParityEquiv_symm_apply w hw 0 (f.symm s)
    simpa only [w, LinearIsometryEquiv.norm_map] using h
  rw [← hmodel]
  exact (f.apply_symm_apply s).symm.trans
    (congrArg f ((cliffordSymbolParityEquiv w hw 0).apply_symm_apply (f.symm s))).symm

end AtiyahSinger
