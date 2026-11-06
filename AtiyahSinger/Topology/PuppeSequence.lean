/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KTheoryContractibleCollapse
public import AtiyahSinger.Topology.MappingCone
public import AtiyahSinger.Topology.Suspension

/-!
# The actual Puppe maps and their reduced K-theory sequence

Public module ID: M2030.

For f : Y → X the cone collapse sends the bottom copy of X to the south pole
of the unreduced suspension of Y, and sends (y,t) to its suspension class.
Its apex goes to the north pole. The original cylinder and cone quotient lifts
define this continuous map, rather than selecting it from an exactness property.

Karoubi II.3.29 uses reduced K-groups at every position. The source defines
reduced K as a cokernel in II.1.20. Our existing model is the evaluation kernel
of II.1.21, so we state the compatible pointed specialization: f(y₀)=x₀,
the cone base point is the image of x₀, and suspension base points are south poles.
The cone apex is a different point and is not silently used as the base point
of the cone inclusion. The proof compares these reductions along the y₀ meridian.

Sources: Karoubi II.2.42 and II.3.28--3.29. The third exactness position follows
the original two-cone argument and contractible-collapse comparison. It does not
use the later suspension/automorphism comparison or suspended compact-support
exactness.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- Collapse the bottom copy of X in the actual mapping cone to the south pole. -/
def puppeConeCollapse (f : C(Y, X)) : C(MappingCone f, UnreducedSuspension Y) :=
  mappingConeLift f (ContinuousMap.const X (UnreducedSuspension.south (X := Y)))
    UnreducedSuspension.ofMap (UnreducedSuspension.north (X := Y))
    (fun y ↦ UnreducedSuspension.of_zero y)
    (fun y ↦ UnreducedSuspension.of_one y)

variable [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

attribute [local instance] MappingCylinder.compactSpace MappingCylinder.t2Space
  MappingCone.compactSpace MappingCone.t2Space
  UnreducedSuspension.compactSpace UnreducedSuspension.t2Space

/-- Pullback along the actual inclusion of X, with its original point as the cone base point. -/
def puppeConeRestriction (f : C(Y, X)) (x₀ : X) :
    reducedComplexKZero (mappingConeIn f x₀) →+ reducedComplexKZero x₀ :=
  reducedComplexKZeroPullback x₀ (mappingConeIn f x₀) (mappingConeIn f) rfl

/-- Pullback along the specified cone collapse, retaining the bottom cone base point. -/
def puppeConeCollapsePullback (f : C(Y, X)) (x₀ : X) :
    reducedComplexKZero (UnreducedSuspension.south (X := Y)) →+
      reducedComplexKZero (mappingConeIn f x₀) :=
  reducedComplexKZeroPullback (mappingConeIn f x₀) (UnreducedSuspension.south (X := Y))
    (puppeConeCollapse f) rfl

/-- The first arrow of the five-term sequence is induced by the actual suspension of f. -/
def puppeSuspensionPullback (f : C(Y, X)) :
    reducedComplexKZero (UnreducedSuspension.south (X := X)) →+
      reducedComplexKZero (UnreducedSuspension.south (X := Y)) :=
  reducedComplexKZeroPullback (UnreducedSuspension.south (X := Y))
    (UnreducedSuspension.south (X := X)) (UnreducedSuspension.map f)
    (UnreducedSuspension.map_south f)

/-- KA II.3.29(a): the cone inclusion fills precisely the kernel of the original pullback. -/
theorem range_puppeConeRestriction (f : C(Y, X)) (y₀ : Y) (x₀ : X) (hf₀ : f y₀ = x₀) :
    (puppeConeRestriction f x₀).range = (reducedComplexKZeroPullback y₀ x₀ f hf₀).ker := by
  /- Stage 1: use the literal mapping cylinder M_f, its top closed embedding of
  Y, and its projection homotopy equivalence to X. Under these maps the top
  inclusion followed by the projection is exactly f, not merely an unrelated
  homotopy-equivalent map. K-theory homotopy invariance compares the restrictions.
  Stage 2: apply closed-pair exactness at K^0(M_f), equivalently II.2.42 for
  its pointed quotient C'f. Restrict to the kernels of evaluation at the
  compatible points. The y₀ cylinder path joins the bottom point to the top;
  after collapse it joins the chosen cone base point to the apex, identifying
  the two evaluation kernels used by the relative and pointed descriptions.
  Stage 3: functoriality on the actual inclusion identifies the resulting image
  with the displayed range. Splitting the constant rank summands justifies the
  reduced sequence; no endpoint injectivity or surjectivity is asserted. -/
  classical
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    apply Subtype.ext
    -- The original tube contracts the composite Y → X → C'f to its actual apex.
    let j : C(Y, MappingCone f) := (mappingConeIn f).comp f
    let k : C(Y, MappingCone f) := ContinuousMap.const Y (mappingConeTip f)
    let H : ContinuousMap.Homotopy j k := {
      toFun := fun p ↦ mappingConeTube f (p.2, p.1)
      continuous_toFun := (mappingConeTube f).continuous.comp
        (continuous_snd.prodMk continuous_fst)
      map_zero_left := fun y ↦ (mappingCone_tube_endpoints f y).1
      map_one_left := fun y ↦ (mappingCone_tube_endpoints f y).2 }
    have hhom := DFunLike.congr_fun (complexKZeroPullback_eq_of_homotopy j k H) b.val
    let ev : C(Y, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ y₀).toRingHom
    let evTip : C(MappingCone f, ℂ) →+* ℂ :=
      (ContinuousMap.evalAlgHom ℂ ℂ (mappingConeTip f)).toRingHom
    let c : ℂ →+* C(Y, ℂ) := algebraMap ℂ C(Y, ℂ)
    have hpoint : j y₀ = mappingConeIn f x₀ := by
      change mappingConeIn f (f y₀) = mappingConeIn f x₀
      rw [hf₀]
    have hzero : kZeroMap ev (complexKZeroPullback j b.val) = 0 :=
      complexKZeroPullback_mem_reduced y₀ (mappingConeIn f x₀) j hpoint b.val b.property
    have hconst : complexKZeroPullback k b.val = kZeroMap c (kZeroMap evTip b.val) := by
      rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp]
      rfl
    -- Evaluation at y₀ detects the constant summand, also when Y is disconnected.
    have heval : (kZeroMap ev).comp (kZeroMap c) = AddMonoidHom.id (KZero ℂ) := by
      rw [← kZeroMap_comp]
      have hc : ev.comp c = RingHom.id ℂ := by
        ext z
        rfl
      rw [hc, kZeroMap_id]
    have htip : kZeroMap evTip b.val = 0 := by
      have h := congrArg (kZeroMap ev) hhom
      rw [hzero, hconst, ← AddMonoidHom.comp_apply, heval, AddMonoidHom.id_apply] at h
      exact h.symm
    have hcomp : complexKZeroPullback j b.val = 0 :=
      hhom.trans (hconst.trans (by rw [htip, map_zero]))
    change complexKZeroPullback f (complexKZeroPullback (mappingConeIn f) b.val) = 0
    simpa only [j, complexKZeroPullback_comp, AddMonoidHom.comp_apply] using hcomp
  · intro a ha
    change reducedComplexKZeroPullback y₀ x₀ f hf₀ a = 0 at ha
    have hfa : complexKZeroPullback f a.val = 0 := congrArg Subtype.val ha
    let M := MappingCylinder f
    let A : Set M := Set.range (mappingCylinderTop f)
    have htop := (mappingCylinder_closedEmbeddings f).2.1
    have hA : IsClosed A := htop.isClosed_range
    let := hA.isClosedEmbedding_subtypeVal.compactSpace
    let e : Y ≃ₜ A := htop.isEmbedding.toHomeomorph
    let r : C(A, Y) := ⟨e.symm, e.symm.continuous⟩
    let i : C(A, M) := ⟨Subtype.val, continuous_subtype_val⟩
    have htopr : (mappingCylinderTop f).comp r = i := by
      ext z
      exact congrArg Subtype.val (e.apply_symm_apply z)
    -- Pull the given class to the cylinder and apply the original closed-pair exactness.
    let u : ComplexKZero M := complexKZeroPullback (mappingCylinderProj f) a.val
    have huTop : complexKZeroPullback (mappingCylinderTop f) u = 0 := by
      change complexKZeroPullback (mappingCylinderTop f)
        (complexKZeroPullback (mappingCylinderProj f) a.val) = 0
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
      exact hfa
    have hu : u ∈ (complexKZeroRestriction A hA).ker := by
      change complexKZeroPullback i u = 0
      rw [← htopr, complexKZeroPullback_comp, AddMonoidHom.comp_apply, huTop, map_zero]
    rw [← range_relativeKZeroForget A hA] at hu
    obtain ⟨b, hb⟩ := hu
    -- The same lift vanishes at the bottom base point, because its cylinder pullback does.
    have hb₀ : b.val ∈ reducedComplexKZero (mappingConeIn f x₀) := by
      have hbottom : relativeKZeroForget A hA b ∈
          reducedComplexKZero (mappingCylinderIn f x₀) := by
        rw [hb]
        exact complexKZeroPullback_mem_reduced (mappingCylinderIn f x₀) x₀
          (mappingCylinderProj f) rfl a.val a.property
      change kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ (mappingCylinderIn f x₀)).toRingHom
        (complexKZeroPullback (mappingConeQuotient f) b.val) = 0 at hbottom
      unfold complexKZeroPullback at hbottom
      rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp] at hbottom
      exact hbottom
    refine ⟨⟨b.val, hb₀⟩, ?_⟩
    apply Subtype.ext
    have hbottom := congrArg (complexKZeroPullback (mappingCylinderIn f)) hb
    change complexKZeroPullback (mappingCylinderIn f)
      (complexKZeroPullback (mappingConeQuotient f) b.val) =
        complexKZeroPullback (mappingCylinderIn f)
          (complexKZeroPullback (mappingCylinderProj f) a.val) at hbottom
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp] at hbottom
    have hid : (mappingCylinderProj f).comp (mappingCylinderIn f) =
        ContinuousMap.id X := rfl
    rw [hid] at hbottom
    change complexKZeroPullback (mappingConeIn f) b.val =
      kZeroMap (RingHom.id _) a.val at hbottom
    change complexKZeroPullback (mappingConeIn f) b.val = a.val
    simpa only [kZeroMap_id, AddMonoidHom.id_apply] using hbottom

/-- KA II.3.29(b): the cone-collapse image is the kernel of restriction to X. -/
theorem range_puppeConeCollapsePullback (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    (puppeConeCollapsePullback f x₀).range = (puppeConeRestriction f x₀).ker := by
  /- Stage 1: the bottom inclusion of X is a closed embedding in C'f. Its
  pointed quotient is the unreduced suspension S'Y: both maps keep each tube
  representative (y,t), collapse the bottom X to the south pole, and retain
  the cone apex as the north pole. This is a specified pointed homeomorphism
  by the compact-to-Hausdorff quotient criterion, not an arbitrary equivalence.
  Stage 2: apply II.2.42 to this closed pair. The quotient pullback is precisely
  puppeConeCollapsePullback, and its following arrow is puppeConeRestriction.
  The common base point lies in the collapsed X. Evaluation kernels therefore
  give exactly the stated reduced range and kernel, including disconnected X. -/
  classical
  let C := MappingCone f
  let A : Set C := Set.range (mappingConeIn f)
  have hbase := (mappingConeIn_closedEmbedding f).1
  have hA : IsClosed A := hbase.isClosed_range
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let Q := PointedQuotient.{_, 0} A
  let := PointedQuotient.compactSpace A
  let := PointedQuotient.t2Space A hA
  let q : C(C, Q) := ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let s : Q := PointedQuotient.basepoint A
  let n : Q := q (mappingConeTip f)
  have hpoint : q (mappingConeIn f x₀) = s := by
    apply (PointedQuotient.of_eq_basepoint_iff A _).2
    rw [← hf₀]
    exact ⟨f y₀, rfl⟩
  -- Descend the actual cone collapse, sending precisely its bottom copy of X to south.
  have hcollapsed (z : C ⊕ PUnit) (hz : z ∈ pairCollapsedSet A) :
      Sum.elim (puppeConeCollapse f) (fun _ : PUnit ↦ UnreducedSuspension.south) z =
        UnreducedSuspension.south := by
    rcases hz with ⟨z, ⟨x, rfl⟩, rfl⟩ | ⟨u, rfl⟩ <;> rfl
  have hrel (z w : C ⊕ PUnit) (h : PairCollapseRel A z w) :
      Sum.elim (puppeConeCollapse f) (fun _ : PUnit ↦ UnreducedSuspension.south) z =
        Sum.elim (puppeConeCollapse f) (fun _ : PUnit ↦ UnreducedSuspension.south) w := by
    rcases h with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hcollapsed z hz).trans (hcollapsed w hw).symm
  let g : C(Q, UnreducedSuspension Y) := {
    toFun := Quotient.lift
      (Sum.elim (puppeConeCollapse f) (fun _ : PUnit ↦ UnreducedSuspension.south)) hrel
    continuous_toFun := ((puppeConeCollapse f).continuous.sumElim
      continuous_const).quotient_lift hrel }
  -- A proof-local quotient lift constructs the inverse on the two successive suspension quotients.
  let lift {U : Type _} [TopologicalSpace U] (B : Set U) (a : C(U, Q)) (p : Q)
      (ha : ∀ z ∈ B, a z = p) : C(PointedQuotient.{_, 0} B, Q) := by
    let F : U ⊕ PUnit → Q := Sum.elim a (fun _ ↦ p)
    have hF (z : U ⊕ PUnit) (hz : z ∈ pairCollapsedSet B) : F z = p := by
      rcases hz with ⟨z, hz, rfl⟩ | ⟨u, rfl⟩
      · exact ha z hz
      · rfl
    have hr (z w : U ⊕ PUnit) (h : PairCollapseRel B z w) : F z = F w := by
      rcases h with rfl | ⟨hz, hw⟩
      · rfl
      · exact (hF z hz).trans (hF w hw).symm
    exact ⟨Quotient.lift F hr, (a.continuous.sumElim continuous_const).quotient_lift hr⟩
  let tube : C(Y × I, Q) := q.comp (mappingConeTube f)
  have hzero (z : Y × I) (hz : z ∈ UnreducedSuspension.lowerEnd Y) : tube z = s := by
    rcases z with ⟨y, t⟩
    change t = 0 at hz
    subst t
    change q (mappingConeTube f (y, 0)) = s
    rw [(mappingCone_tube_endpoints f y).1]
    exact (PointedQuotient.of_eq_basepoint_iff A _).2 ⟨f y, rfl⟩
  let lower : C(UnreducedSuspension.LowerCone Y, Q) :=
    lift (UnreducedSuspension.lowerEnd Y) tube s hzero
  have hone (z : UnreducedSuspension.LowerCone Y)
      (hz : z ∈ UnreducedSuspension.upperEnd Y) : lower z = n := by
    obtain ⟨y, rfl⟩ := hz
    change q (mappingConeTube f (y, 1)) = q (mappingConeTip f)
    rw [(mappingCone_tube_endpoints f y).2]
  let inv : C(UnreducedSuspension Y, Q) :=
    lift (UnreducedSuspension.upperEnd Y) lower n hone
  have hleft : Function.LeftInverse inv g := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => rfl
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inr u => rfl
          | inl z =>
            induction z using Quotient.inductionOn with
            | h z =>
              cases z with
              | inl x =>
                exact ((PointedQuotient.of_eq_basepoint_iff A
                  (mappingConeIn f x)).2 ⟨x, rfl⟩).symm
              | inr yt => rfl
  have hright : Function.RightInverse inv g := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => rfl
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z <;> rfl
  let e : Q ≃ₜ UnreducedSuspension Y :=
    (Equiv.ofBijective g ⟨hleft.injective, hright.surjective⟩).toHomeomorphOfContinuousClosed
      g.continuous g.continuous.isClosedMap
  have hquot : inv.comp (puppeConeCollapse f) = q := by
    ext z
    exact hleft (q z)
  -- Closed-pair exactness now concerns this actual quotient, including its pointed maps.
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    apply Subtype.ext
    change complexKZeroPullback (mappingConeIn f)
      (complexKZeroPullback (puppeConeCollapse f) b.val) = 0
    unfold complexKZeroPullback
    rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp]
    have hc : (ContinuousMap.compRightAlgHom ℂ ℂ (mappingConeIn f)).toRingHom.comp
        (ContinuousMap.compRightAlgHom ℂ ℂ (puppeConeCollapse f)).toRingHom =
          (algebraMap ℂ C(X, ℂ)).comp
            (ContinuousMap.evalAlgHom ℂ ℂ (UnreducedSuspension.south (X := Y))).toRingHom := by
      ext a x
      rfl
    rw [hc, kZeroMap_comp, AddMonoidHom.comp_apply, b.property, map_zero]
  · intro b hb
    change puppeConeRestriction f x₀ b = 0 at hb
    have hres : complexKZeroPullback (mappingConeIn f) b.val = 0 :=
      congrArg Subtype.val hb
    let eX : X ≃ₜ A := hbase.isEmbedding.toHomeomorph
    let r : C(A, X) := ⟨eX.symm, eX.symm.continuous⟩
    let i : C(A, C) := ⟨Subtype.val, continuous_subtype_val⟩
    have hir : (mappingConeIn f).comp r = i := by
      ext z
      exact congrArg Subtype.val (eX.apply_symm_apply z)
    have hz : b.val ∈ (complexKZeroRestriction A hA).ker := by
      change complexKZeroPullback i b.val = 0
      rw [← hir, complexKZeroPullback_comp, AddMonoidHom.comp_apply, hres, map_zero]
    rw [← range_relativeKZeroForget A hA] at hz
    obtain ⟨a, ha⟩ := hz
    let c : reducedComplexKZero (UnreducedSuspension.south (X := Y)) :=
      reducedComplexKZeroPullback UnreducedSuspension.south s inv rfl a
    refine ⟨c, ?_⟩
    apply Subtype.ext
    change complexKZeroPullback (puppeConeCollapse f)
      (complexKZeroPullback inv a.val) = b.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hquot]
    exact ha

set_option maxHeartbeats 400000 in

/-- KA II.3.29(c): suspension of f fills the kernel of the same cone-collapse pullback. -/
theorem range_puppeSuspensionPullback (f : C(Y, X)) (y₀ : Y)
    (x₀ : X) (hf₀ : f y₀ = x₀) :
    (puppeSuspensionPullback f).range = (puppeConeCollapsePullback f x₀).ker := by
  /- Stage 1: contract the actual cone CX of the identity to its apex. Form
  D as the cone of the original inclusion X → C'f and embed its lower CX,
  with the folding map as a left inverse. Its image is closed and contractible.
  The specified collapse of this image identifies the quotient with S'Y and
  gives a bijective pullback q*, at the retained bottom base point.
  Stage 2: form the doubled suspension from two copies of CX and construct
  the explicit cone-swap involution. The reduced group of CX is zero; the
  preceding closed-pair exactness gives surjectivity of both half-collapse
  pullbacks p* and t*. These are distinct maps. The actual two-cone diagram
  identifies p after r with the collapse of the inclusion, and t after r
  with S'f after q, without identifying the two half-collapse arrows.
  Stage 3: use the preceding exactness for X → C'f. Surjectivity of p* and t*
  compares its image with q* of the suspension image. Bijectivity of q* and
  the original restriction square give the displayed range/kernel equality.
  All reductions use the specified compatible bottom points; no later
  automorphism comparison or compact-support exactness is used. -/
  classical
  let idX : C(X, X) := ContinuousMap.id X
  let CX := MappingCone idX
  let tip : CX := mappingConeTip idX
  have coneCases (P : CX → Prop) (hbase : ∀ x, P (mappingConeIn idX x))
      (htube : ∀ x t, P (mappingConeTube idX (x, t))) (htip : P tip) : ∀ z, P z := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => exact htip
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl x => exact hbase x
          | inr xt => exact htube xt.1 xt.2
  -- Contract one actual cone to its apex, jointly continuously through both quotients.
  let h (s t : I) : I := σ (σ s * σ t)
  have hh : Continuous (fun p : I × I ↦ h p.1 p.2) :=
    unitInterval.continuous_symm.comp
      ((unitInterval.continuous_symm.comp continuous_fst).mul
        (unitInterval.continuous_symm.comp continuous_snd))
  let base (s : I) : C(X, CX) :=
    (mappingConeTube idX).comp ⟨fun x ↦ (x, s), continuous_id.prodMk continuous_const⟩
  let tube (s : I) : C(X × I, CX) :=
    (mappingConeTube idX).comp
      ⟨fun p ↦ (p.1, h s p.2),
        continuous_fst.prodMk (hh.comp (continuous_const.prodMk continuous_snd))⟩
  have hglue (s : I) (x : X) : tube s (x, 0) = base s (idX x) := by
    change mappingConeTube idX (x, h s 0) = mappingConeTube idX (x, s)
    simp [h]
  have htop (s : I) (x : X) : tube s (x, 1) = tip := by
    change mappingConeTube idX (x, h s 1) = tip
    simp only [h, unitInterval.symm_one, mul_zero, unitInterval.symm_zero]
    exact (mappingCone_tube_endpoints idX x).2
  let scale (s : I) : C(CX, CX) := mappingConeLift idX (base s) (tube s) tip
    (hglue s) (htop s)
  have hscale : Continuous (fun p : I × CX ↦ scale p.1 p.2) := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hm : Continuous (fun p : I × MappingCylinder idX ↦
        mappingCylinderLift idX (base p.1) (tube p.1) (hglue p.1) p.2) := by
      apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
      have hc : Continuous (Sum.elim
          (fun p : I × X ↦ mappingConeTube idX (p.2, p.1))
          (fun p : I × (X × I) ↦ mappingConeTube idX (p.2.1, h p.1 p.2.2))) :=
        ((mappingConeTube idX).continuous.comp (continuous_snd.prodMk continuous_fst)).sumElim
          ((mappingConeTube idX).continuous.comp
            (continuous_snd.fst.prodMk (hh.comp (continuous_fst.prodMk continuous_snd.snd))))
      convert hc.comp (Homeomorph.prodSumDistrib
        (X := I) (Y := X) (Z := X × I)).continuous using 1
      funext p
      rcases p with ⟨s, z⟩
      cases z <;> rfl
    have hc : Continuous (Sum.elim
        (fun p : I × MappingCylinder idX ↦
          mappingCylinderLift idX (base p.1) (tube p.1) (hglue p.1) p.2)
        (fun _ : I × PUnit ↦ tip)) := hm.sumElim continuous_const
    convert hc.comp (Homeomorph.prodSumDistrib
      (X := I) (Y := MappingCylinder idX) (Z := PUnit)).continuous using 1
    funext p
    rcases p with ⟨s, z⟩
    cases z <;> rfl
  have hscale₀ : ∀ z : CX, scale 0 z = z := by
    apply coneCases
    · intro x
      change mappingConeTube idX (x, 0) = mappingConeIn idX x
      exact (mappingCone_tube_endpoints idX x).1
    · intro x t
      change mappingConeTube idX (x, h 0 t) = mappingConeTube idX (x, t)
      simp [h]
    · rfl
  have hscale₁ : ∀ z : CX, scale 1 z = tip := by
    apply coneCases
    · intro x
      exact (mappingCone_tube_endpoints idX x).2
    · intro x t
      change mappingConeTube idX (x, h 1 t) = tip
      simp only [h, unitInterval.symm_one, zero_mul, unitInterval.symm_zero]
      exact (mappingCone_tube_endpoints idX x).2
    · rfl
  let contraction : ContinuousMap.Homotopy (ContinuousMap.id CX)
      (ContinuousMap.const CX tip) := {
    toFun := fun p ↦ scale p.1 p.2
    continuous_toFun := hscale
    map_zero_left := hscale₀
    map_one_left := hscale₁ }
  let : ContractibleSpace CX :=
    (contractible_iff_id_nullhomotopic CX).2 ⟨tip, ⟨contraction⟩⟩
  let C := MappingCone f
  let i : C(X, C) := mappingConeIn f
  let D := MappingCone i
  let j : C(C, D) := mappingConeIn i
  let d₀ : D := j (i x₀)
  have originalCases (P : C → Prop) (hbase : ∀ x, P (i x))
      (htube : ∀ y t, P (mappingConeTube f (y, t)))
      (htip : P (mappingConeTip f)) : ∀ z, P z := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => exact htip
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl x => exact hbase x
          | inr yt => exact htube yt.1 yt.2
  have doubleCases (P : D → Prop) (hbase : ∀ z, P (j z))
      (htube : ∀ x t, P (mappingConeTube i (x, t)))
      (htip : P (mappingConeTip i)) : ∀ z, P z := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => exact htip
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl z => exact hbase z
          | inr xt => exact htube xt.1 xt.2
  -- The lower cone is an actual embedded copy of CX; folding the upper cone supplies its inverse.
  let coneF : C(C, CX) := mappingConeLift f (mappingConeIn idX)
    ((mappingConeTube idX).comp (f.prodMap (ContinuousMap.id I))) tip
    (fun y ↦ (mappingCone_tube_endpoints idX (f y)).1)
    (fun y ↦ (mappingCone_tube_endpoints idX (f y)).2)
  let lowerCone : C(CX, D) := mappingConeLift idX (j.comp i) (mappingConeTube i)
    (mappingConeTip i) (fun x ↦ (mappingCone_tube_endpoints i x).1)
    (fun x ↦ (mappingCone_tube_endpoints i x).2)
  let fold : C(D, CX) := mappingConeLift i coneF (mappingConeTube idX) tip
    (fun x ↦ (mappingCone_tube_endpoints idX x).1)
    (fun x ↦ (mappingCone_tube_endpoints idX x).2)
  have hfold : Function.LeftInverse fold lowerCone := by
    apply coneCases
    · intro x
      rfl
    · intro x t
      rfl
    · rfl
  have hlower := lowerCone.continuous.isClosedEmbedding hfold.injective
  let A : Set D := Set.range lowerCone
  have hA : IsClosed A := hlower.isClosed_range
  let eA : CX ≃ₜ A := hlower.isEmbedding.toHomeomorph
  let : ContractibleSpace A := eA.symm.contractibleSpace
  have hd₀ : d₀ ∈ A := ⟨mappingConeIn idX (f y₀), congrArg (fun x ↦ j (i x)) hf₀⟩
  let q : C(D, UnreducedSuspension Y) := mappingConeLift i (puppeConeCollapse f)
    (ContinuousMap.const (X × I) UnreducedSuspension.south) UnreducedSuspension.south
    (fun _ ↦ rfl) (fun _ ↦ rfl)
  have hqLower : ∀ z : CX, q (lowerCone z) = UnreducedSuspension.south := by
    apply coneCases
    · intro x
      rfl
    · intro x t
      rfl
    · rfl
  let Q := PointedQuotient.{_, 0} A
  let := PointedQuotient.compactSpace A
  let := PointedQuotient.t2Space A hA
  let qa : C(D, Q) := ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let s : Q := PointedQuotient.basepoint A
  have hqCollapsed (z : D ⊕ PUnit) (hz : z ∈ pairCollapsedSet A) :
      Sum.elim q (fun _ : PUnit ↦ UnreducedSuspension.south) z =
        UnreducedSuspension.south := by
    rcases hz with ⟨z, ⟨c, rfl⟩, rfl⟩ | ⟨u, rfl⟩
    · exact hqLower c
    · rfl
  have hqRel (z w : D ⊕ PUnit) (h : PairCollapseRel A z w) :
      Sum.elim q (fun _ : PUnit ↦ UnreducedSuspension.south) z =
        Sum.elim q (fun _ : PUnit ↦ UnreducedSuspension.south) w := by
    rcases h with rfl | ⟨hz, hw⟩
    · rfl
    · exact (hqCollapsed z hz).trans (hqCollapsed w hw).symm
  let g : C(Q, UnreducedSuspension Y) := {
    toFun := Quotient.lift (Sum.elim q (fun _ : PUnit ↦ UnreducedSuspension.south)) hqRel
    continuous_toFun := (q.continuous.sumElim continuous_const).quotient_lift hqRel }
  -- After this lower-cone collapse the remaining upper tube is exactly the suspension of Y.
  let liftY {U : Type _} [TopologicalSpace U] (B : Set U) (a : C(U, Q)) (p : Q)
      (ha : ∀ z ∈ B, a z = p) : C(PointedQuotient.{_, 0} B, Q) := by
    let F : U ⊕ PUnit → Q := Sum.elim a (fun _ ↦ p)
    have hF (z : U ⊕ PUnit) (hz : z ∈ pairCollapsedSet B) : F z = p := by
      rcases hz with ⟨z, hz, rfl⟩ | ⟨u, rfl⟩
      · exact ha z hz
      · rfl
    have hr (z w : U ⊕ PUnit) (h : PairCollapseRel B z w) : F z = F w := by
      rcases h with rfl | ⟨hz, hw⟩
      · rfl
      · exact (hF z hz).trans (hF w hw).symm
    exact ⟨Quotient.lift F hr, (a.continuous.sumElim continuous_const).quotient_lift hr⟩
  let upperTube : C(Y × I, Q) := qa.comp (j.comp (mappingConeTube f))
  have hupper₀ (z : Y × I) (hz : z ∈ UnreducedSuspension.lowerEnd Y) : upperTube z = s := by
    rcases z with ⟨y, t⟩
    change t = 0 at hz
    subst t
    change qa (j (mappingConeTube f (y, 0))) = s
    rw [(mappingCone_tube_endpoints f y).1]
    exact (PointedQuotient.of_eq_basepoint_iff A _).2
      ⟨mappingConeIn idX (f y), rfl⟩
  let firstY : C(UnreducedSuspension.LowerCone Y, Q) :=
    liftY (UnreducedSuspension.lowerEnd Y) upperTube s hupper₀
  let northQ : Q := qa (j (mappingConeTip f))
  have hupper₁ (z : UnreducedSuspension.LowerCone Y)
      (hz : z ∈ UnreducedSuspension.upperEnd Y) : firstY z = northQ := by
    obtain ⟨y, rfl⟩ := hz
    change qa (j (mappingConeTube f (y, 1))) = qa (j (mappingConeTip f))
    rw [(mappingCone_tube_endpoints f y).2]
  let inv : C(UnreducedSuspension Y, Q) :=
    liftY (UnreducedSuspension.upperEnd Y) firstY northQ hupper₁
  have hleft : Function.LeftInverse inv g := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => rfl
      | inl z =>
        change inv (q z) = qa z
        refine doubleCases (fun w ↦ inv (q w) = qa w) ?_ ?_ ?_ z
        · refine originalCases (fun w ↦ inv (q (j w)) = qa (j w)) ?_ ?_ ?_
          · intro x
            exact ((PointedQuotient.of_eq_basepoint_iff A _).2
              ⟨mappingConeIn idX x, rfl⟩).symm
          · intro y t
            rfl
          · rfl
        · intro x t
          exact ((PointedQuotient.of_eq_basepoint_iff A _).2
            ⟨mappingConeTube idX (x, t), rfl⟩).symm
        · exact ((PointedQuotient.of_eq_basepoint_iff A _).2 ⟨tip, rfl⟩).symm
  have hright : Function.RightInverse inv g := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => rfl
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z => cases z <;> rfl
  let quotientEquiv : Q ≃ₜ UnreducedSuspension Y :=
    (Equiv.ofBijective g ⟨hleft.injective, hright.surjective⟩).toHomeomorphOfContinuousClosed
      g.continuous g.continuous.isClosedMap
  have hqg : g.comp qa = q := by
    ext z
    rfl
  have hinvq : inv.comp q = qa := by
    ext z
    exact hleft (qa z)
  have hginv : g.comp inv = ContinuousMap.id (UnreducedSuspension Y) := by
    ext z
    exact hright z
  let qStar : reducedComplexKZero UnreducedSuspension.south →+ reducedComplexKZero d₀ :=
    reducedComplexKZeroPullback d₀ UnreducedSuspension.south q rfl
  have hqStar : Function.Bijective qStar := by
    have hc := reducedComplexKZeroCollapse_bijective A hA d₀ hd₀
    have hfactor (a : reducedComplexKZero (UnreducedSuspension.south (X := Y))) :
        reducedComplexKZeroCollapse A hA d₀ hd₀
            (reducedComplexKZeroPullback s UnreducedSuspension.south g rfl a) = qStar a := by
      apply Subtype.ext
      change complexKZeroPullback qa (complexKZeroPullback g a.val) =
        complexKZeroPullback q a.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hqg]
    constructor
    · intro a b hab
      have h := hc.injective ((hfactor a).trans (hab.trans (hfactor b).symm))
      have hv := congrArg (complexKZeroPullback inv) (congrArg Subtype.val h)
      change complexKZeroPullback inv (complexKZeroPullback g a.val) =
        complexKZeroPullback inv (complexKZeroPullback g b.val) at hv
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hginv] at hv
      change kZeroMap (RingHom.id _) a.val =
        complexKZeroPullback inv (complexKZeroPullback g b.val) at hv
      rw [kZeroMap_id, AddMonoidHom.id_apply, ← AddMonoidHom.comp_apply,
        ← complexKZeroPullback_comp, hginv] at hv
      change a.val = kZeroMap (RingHom.id _) b.val at hv
      rw [kZeroMap_id, AddMonoidHom.id_apply] at hv
      exact Subtype.ext hv
    · intro b
      obtain ⟨a, ha⟩ := hc.surjective b
      refine ⟨reducedComplexKZeroPullback UnreducedSuspension.south s inv rfl a, ?_⟩
      apply Subtype.ext
      change complexKZeroPullback q (complexKZeroPullback inv a.val) = b.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hinvq]
      exact congrArg Subtype.val ha
  -- The doubled suspension consists of two full cones, with their common X equator.
  let i₀ : C(X, CX) := mappingConeIn idX
  let D₀ := MappingCone i₀
  let j₀ : C(CX, D₀) := mappingConeIn i₀
  let e₀ : D₀ := j₀ (i₀ x₀)
  have sphereCases (P : D₀ → Prop) (hbase : ∀ z, P (j₀ z))
      (htube : ∀ x t, P (mappingConeTube i₀ (x, t)))
      (htip : P (mappingConeTip i₀)) : ∀ z, P z := by
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inr u => exact htip
      | inl z =>
        induction z using Quotient.inductionOn with
        | h z =>
          cases z with
          | inl z => exact hbase z
          | inr xt => exact htube xt.1 xt.2
  let lower₀ : C(CX, D₀) := mappingConeLift idX (j₀.comp i₀) (mappingConeTube i₀)
    (mappingConeTip i₀) (fun x ↦ (mappingCone_tube_endpoints i₀ x).1)
    (fun x ↦ (mappingCone_tube_endpoints i₀ x).2)
  let swap : C(D₀, D₀) := mappingConeLift i₀ lower₀ (j₀.comp (mappingConeTube idX))
    (j₀ tip) (fun x ↦ congrArg j₀ (mappingCone_tube_endpoints idX x).1)
    (fun x ↦ congrArg j₀ (mappingCone_tube_endpoints idX x).2)
  have hswapLower : ∀ z : CX, swap (lower₀ z) = j₀ z := by
    apply coneCases
    · intro x
      rfl
    · intro x t
      rfl
    · rfl
  have hswap : swap.comp swap = ContinuousMap.id D₀ := by
    ext z
    refine sphereCases (fun w ↦ swap (swap w) = w) ?_ ?_ ?_ z
    · intro c
      exact hswapLower c
    · intro x t
      rfl
    · rfl
  let p : C(D₀, UnreducedSuspension X) := puppeConeCollapse i₀
  let t : C(D₀, UnreducedSuspension X) := p.comp swap
  -- The two half collapses are different maps. Their pullbacks both fill the doubled group.
  have hconeReduced (a : reducedComplexKZero (i₀ x₀)) : a = 0 := by
    let H := contraction.trans (contraction.evalAt (i₀ x₀)).symm.toHomotopyConst
    have heq := DFunLike.congr_fun (complexKZeroPullback_eq_of_homotopy
      (ContinuousMap.id CX) (ContinuousMap.const CX (i₀ x₀)) H) a.val
    have hconst : complexKZeroPullback (ContinuousMap.const CX (i₀ x₀)) a.val = 0 := by
      unfold complexKZeroPullback
      have hc : (ContinuousMap.compRightAlgHom ℂ ℂ
          (ContinuousMap.const CX (i₀ x₀))).toRingHom =
            (algebraMap ℂ C(CX, ℂ)).comp
              (ContinuousMap.evalAlgHom ℂ ℂ (i₀ x₀)).toRingHom := by
        ext b z
        rfl
      rw [hc, kZeroMap_comp, AddMonoidHom.comp_apply, a.property, map_zero]
    change kZeroMap (RingHom.id _) a.val = _ at heq
    rw [kZeroMap_id, AddMonoidHom.id_apply, hconst] at heq
    exact Subtype.ext heq
  let pStar : reducedComplexKZero UnreducedSuspension.south →+ reducedComplexKZero e₀ :=
    reducedComplexKZeroPullback e₀ UnreducedSuspension.south p rfl
  let tStar : reducedComplexKZero UnreducedSuspension.south →+ reducedComplexKZero e₀ :=
    reducedComplexKZeroPullback e₀ UnreducedSuspension.south t rfl
  have hpStar : Function.Surjective pStar := by
    intro b
    have hb : b ∈ (puppeConeRestriction i₀ (i₀ x₀)).ker :=
      hconeReduced (puppeConeRestriction i₀ (i₀ x₀) b)
    rw [← range_puppeConeCollapsePullback i₀ x₀ (i₀ x₀) rfl] at hb
    exact hb
  have htStar : Function.Surjective tStar := by
    intro b
    let b' := reducedComplexKZeroPullback e₀ e₀ swap rfl b
    obtain ⟨a, ha⟩ := hpStar b'
    refine ⟨a, ?_⟩
    apply Subtype.ext
    have hv := congrArg (complexKZeroPullback swap) (congrArg Subtype.val ha)
    change complexKZeroPullback swap (complexKZeroPullback p a.val) =
      complexKZeroPullback swap (complexKZeroPullback swap b.val) at hv
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
      ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hswap] at hv
    change complexKZeroPullback t a.val = kZeroMap (RingHom.id _) b.val at hv
    change complexKZeroPullback t a.val = b.val
    simpa only [kZeroMap_id, AddMonoidHom.id_apply] using hv
  -- Compare the original two-cone diagram without identifying its two collapse arrows.
  let r : C(D, D₀) := mappingConeLift i (j₀.comp coneF) (mappingConeTube i₀)
    (mappingConeTip i₀) (fun x ↦ (mappingCone_tube_endpoints i₀ x).1)
    (fun x ↦ (mappingCone_tube_endpoints i₀ x).2)
  have hp : p.comp r = puppeConeCollapse i := by
    ext z
    refine doubleCases (fun w ↦ p (r w) = puppeConeCollapse i w) ?_ ?_ ?_ z
    · intro c
      rfl
    · intro x s
      rfl
    · rfl
  have hupper : p.comp lower₀ = puppeConeCollapse idX := by
    ext z
    refine coneCases (fun w ↦ p (lower₀ w) = puppeConeCollapse idX w) ?_ ?_ ?_ z
    · intro x
      rfl
    · intro x s
      rfl
    · rfl
  have ht : t.comp r = (UnreducedSuspension.map f).comp q := by
    ext z
    refine doubleCases
      (fun w ↦ t (r w) = UnreducedSuspension.map f (q w)) ?_ ?_ ?_ z
    · intro c
      change p (lower₀ (coneF c)) = UnreducedSuspension.map f (puppeConeCollapse f c)
      rw [show p (lower₀ (coneF c)) = puppeConeCollapse idX (coneF c) from
        DFunLike.congr_fun hupper (coneF c)]
      refine originalCases
        (fun w ↦ puppeConeCollapse idX (coneF w) =
          UnreducedSuspension.map f (puppeConeCollapse f w)) ?_ ?_ ?_ c
      · intro x
        rfl
      · intro y s
        rfl
      · rfl
    · intro x s
      rfl
    · rfl
  let rStar : reducedComplexKZero e₀ →+ reducedComplexKZero d₀ :=
    reducedComplexKZeroPullback d₀ e₀ r rfl
  let gStar := puppeConeCollapsePullback i (i x₀)
  have hpFactor (a : reducedComplexKZero (UnreducedSuspension.south (X := X))) :
      rStar (pStar a) = gStar a := by
    apply Subtype.ext
    change complexKZeroPullback r (complexKZeroPullback p a.val) =
      complexKZeroPullback (puppeConeCollapse i) a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hp]
  have htFactor (a : reducedComplexKZero (UnreducedSuspension.south (X := X))) :
      rStar (tStar a) = qStar (puppeSuspensionPullback f a) := by
    apply Subtype.ext
    change complexKZeroPullback r (complexKZeroPullback t a.val) =
      complexKZeroPullback q (complexKZeroPullback (UnreducedSuspension.map f) a.val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, ht,
      complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  have hrestriction (a : reducedComplexKZero (UnreducedSuspension.south (X := Y))) :
      puppeConeRestriction i (i x₀) (qStar a) = puppeConeCollapsePullback f x₀ a := by
    apply Subtype.ext
    change complexKZeroPullback j (complexKZeroPullback q a.val) =
      complexKZeroPullback (puppeConeCollapse f) a.val
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    rfl
  have hseq : gStar.range = (puppeConeRestriction i (i x₀)).ker :=
    range_puppeConeCollapsePullback i x₀ (i x₀) rfl
  -- Transport the bottom exact row through q*, using only surjectivity of both half collapses.
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    change puppeConeCollapsePullback f x₀ (puppeSuspensionPullback f b) = 0
    obtain ⟨c, hc⟩ := hpStar (tStar b)
    have hzero : puppeConeRestriction i (i x₀) (gStar c) = 0 := by
      have hz : gStar c ∈ gStar.range := ⟨c, rfl⟩
      rw [hseq] at hz
      exact hz
    have hcompare : qStar (puppeSuspensionPullback f b) = gStar c := by
      calc
        qStar (puppeSuspensionPullback f b) = rStar (tStar b) := (htFactor b).symm
        _ = rStar (pStar c) := congrArg rStar hc.symm
        _ = gStar c := hpFactor c
    exact (hrestriction _).symm.trans
      ((congrArg (puppeConeRestriction i (i x₀)) hcompare).trans hzero)
  · intro a ha
    change puppeConeCollapsePullback f x₀ a = 0 at ha
    have hz : qStar a ∈ (puppeConeRestriction i (i x₀)).ker := by
      change puppeConeRestriction i (i x₀) (qStar a) = 0
      rw [hrestriction, ha]
    rw [← hseq] at hz
    obtain ⟨b, hb⟩ := hz
    obtain ⟨c, hc⟩ := htStar (pStar b)
    refine ⟨c, hqStar.injective ?_⟩
    calc
      qStar (puppeSuspensionPullback f c) = rStar (tStar c) := (htFactor c).symm
      _ = rStar (pStar b) := congrArg rStar hc
      _ = gStar b := hpFactor b
      _ = qStar a := hb

end AtiyahSinger
