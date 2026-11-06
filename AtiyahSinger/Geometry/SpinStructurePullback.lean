/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SpinFrame
public import AtiyahSinger.Topology.CoveringPullback
public import AtiyahSinger.Topology.PrincipalBundlePullback

/-!
# Pullback of the original topological spin structure

Public module ID: M1459.

The pullback retains the original principal fiber product, native vector-bundle
topology, fiber inner products and oriented frames. The frame covering is
transported through the same actual fiber product, and its original two-point
fibers are preserved. No compactness or separation of either base is required.

Source: the standard pullback of a spin structure in Spin Geometry II.1.
The explicit native-topology comparisons connect this construction to the
project's original principal and orthogonal-frame models.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ContinuousLinearMap Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Native pullback preserves the original fiber inner products and their continuity. -/
theorem isContinuousRiemannianBundle_pullback
    {B X : Type*} [TopologicalSpace B] [TopologicalSpace X]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (E : B → Type*) [hnorm : ∀ b, NormedAddCommGroup (E b)]
    [hinnerSpace : ∀ b, InnerProductSpace ℝ (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E]
    (f : C(X, B)) :
    letI : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hnorm (f x)
    letI : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hinnerSpace (f x)
    letI : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
    letI : FiberBundle F ((f : X → B) *ᵖ E) := FiberBundle.pullback (F := F) (E := E) f
    letI : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toAddCommMonoid
    letI : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hinnerSpace (f x)).toModule
    letI : VectorBundle ℝ F ((f : X → B) *ᵖ E) :=
      VectorBundle.pullback ℝ (F := F) (E := E) f
    IsContinuousRiemannianBundle F ((f : X → B) *ᵖ E) := by
  let : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hnorm (f x)
  let : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hinnerSpace (f x)
  let : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
  let : FiberBundle F ((f : X → B) *ᵖ E) := FiberBundle.pullback (F := F) (E := E) f
  let : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toAddCommMonoid
  let : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hinnerSpace (f x)).toModule
  let : VectorBundle ℝ F ((f : X → B) *ᵖ E) :=
    VectorBundle.pullback ℝ (F := F) (E := E) f
  obtain ⟨g, hg, hinner⟩ :=
    IsContinuousRiemannianBundle.exists_continuous (F := F) (E := E)
  refine ⟨fun x ↦ g (f x), ?_, fun x v w ↦ hinner (f x) v w⟩
  -- Native pullback charts use the original chart at f(x), with the same vectors.
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hcoord := (continuousAt_hom_bundle (RingHom.id ℝ)
    (fun x : X ↦ (⟨f x, g (f x)⟩ : TotalSpace (F →L[ℝ] F →L[ℝ] ℝ)
      (fun b ↦ E b →L[ℝ] E b →L[ℝ] ℝ)))).mp
        ((hg.comp f.continuous).continuousAt (x := x₀))
  have hU : ∀ᶠ x in 𝓝 x₀, f x ∈ (trivializationAt F E (f x₀)).baseSet :=
    f.continuous.continuousAt.eventually
      ((trivializationAt F E (f x₀)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f x₀)))
  apply hcoord.2.congr_of_eventuallyEq
  filter_upwards [hU] with x hx
  have hx' : x ∈ (trivializationAt F ((f : X → B) *ᵖ E) x₀).baseSet := hx
  ext v w
  -- The bilinear coordinate formula removes the nested native Hom charts.
  rw [inCoordinates_apply_eq₂ hx' hx' (by simp),
    inCoordinates_apply_eq₂ hx hx (by simp)]
  have hsym (a : F) : (trivializationAt F ((f : X → B) *ᵖ E) x₀).symm x a =
      (trivializationAt F E (f x₀)).symm (f x) a := by
    -- On the chart base, both inverse frames have the same original coordinate a.
    apply ((trivializationAt F E (f x₀)).linearEquivAt ℝ (f x) hx).injective
    change (trivializationAt F E (f x₀)
      ⟨f x, (trivializationAt F ((f : X → B) *ᵖ E) x₀).symm x a⟩).2 =
        (trivializationAt F E (f x₀)
          ⟨f x, (trivializationAt F E (f x₀)).symm (f x) a⟩).2
    exact (congrArg Prod.snd
      ((trivializationAt F ((f : X → B) *ᵖ E) x₀).apply_mk_symm hx' a)).trans
        (congrArg Prod.snd ((trivializationAt F E (f x₀)).apply_mk_symm hx a)).symm
  rw [hsym v, hsym w]
  change (Bundle.Trivial.trivialization X ℝ).linearMapAt ℝ x _ =
    (Bundle.Trivial.trivialization B ℝ).linearMapAt ℝ (f x) _
  simp only [Bundle.Trivial.linearMapAt_trivialization]
  rfl

attribute [local instance] spinGroupTopology spinGroup_isTopologicalGroup
  orthogonalFrameTopology orientedOrthogonalFrameTopology

variable {m : ℕ} {B P X : Type*} {E : B → Type*}
  [hnorm : ∀ b, NormedAddCommGroup (E b)] [hinnerSpace : ∀ b, InnerProductSpace ℝ (E b)]
  [TopologicalSpace B] [TopologicalSpace P] [TopologicalSpace X]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin (2 * m))) E)]
  {o : ∀ b, Orientation ℝ (E b) (Fin (2 * m))}
  [MulAction (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  [ContinuousSMul (spinGroup (realSpinorQuadraticForm m))ᵐᵒᵖ P]
  {projection : P → B}
  [FiberBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin (2 * m))) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (2 * m))) E]
  {hm : 0 < m}
  {hP : IsPrincipalBundle (spinGroup (realSpinorQuadraticForm m)) projection}

local notation "RealModel" => EuclideanSpace ℝ (Fin (2 * m))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Pull back the original spin lift, including its actual two-sheeted frame covering. -/
def TopologicalSpinStructure.pullback (S : TopologicalSpinStructure m E o hm hP)
    (f : C(X, B)) :
    letI := hP
    letI : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hnorm (f x)
    letI : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hinnerSpace (f x)
    letI : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
    letI : FiberBundle RealModel ((f : X → B) *ᵖ E) :=
      FiberBundle.pullback (F := RealModel) (E := E) f
    letI : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toAddCommMonoid
    letI : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hinnerSpace (f x)).toModule
    letI : VectorBundle ℝ RealModel ((f : X → B) *ᵖ E) :=
      VectorBundle.pullback ℝ (F := RealModel) (E := E) f
    letI := isContinuousRiemannianBundle_pullback RealModel E f
    TopologicalSpinStructure m ((f : X → B) *ᵖ E) (fun x ↦ o (f x)) hm
      (isPrincipalBundle_pullback (G := spinGroup (realSpinorQuadraticForm m))
        (projection := projection) f) := by
  classical
  letI := hP
  letI : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hnorm (f x)
  letI : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ hinnerSpace (f x)
  letI : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
  letI : FiberBundle RealModel ((f : X → B) *ᵖ E) :=
    FiberBundle.pullback (F := RealModel) (E := E) f
  letI : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hnorm (f x)).toAddCommMonoid
  letI : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
    fun x ↦ (hinnerSpace (f x)).toModule
  letI : VectorBundle ℝ RealModel ((f : X → B) *ᵖ E) :=
    VectorBundle.pullback ℝ (F := RealModel) (E := E) f
  letI := isContinuousRiemannianBundle_pullback RealModel E f
  let A := OrientedOrthogonalFrameBundle m ((f : X → B) *ᵖ E) (fun x ↦ o (f x))
  letI : TopologicalSpace A :=
    orientedOrthogonalFrameTopology m ((f : X → B) *ᵖ E) (fun x ↦ o (f x))
  let Q := PrincipalBundlePullback f projection
  -- Transport only the frame's base equality; each original vector remains fixed.
  have hframe (p : P) (b : B) (hp : projection p = b) (v : RealModel) :
      (⟨b, S.frame p b hp v⟩ : TotalSpace RealModel E) =
        ⟨(S.frameMap p).val.1, (S.frameMap p).val.2 v⟩ := by
    have hb : (S.frameMap p).val.1 = b := (S.frameMap_projection p).trans hp
    cases hb
    rfl
  have hpositive (p : P) (b : B) (hp : projection p = b) :
      Orientation.map (Fin (2 * m)) (S.frame p b hp).toLinearEquiv
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ).toBasis.orientation = o b := by
    have hb : (S.frameMap p).val.1 = b := (S.frameMap_projection p).trans hp
    cases hb
    exact (S.frameMap p).property
  have hfixed (p : P) (b : B) (hp : projection p = b) :
      (⟨⟨b, S.frame p b hp⟩, hpositive p b hp⟩ :
        OrientedOrthogonalFrameBundle m E o) = S.frameMap p := by
    have hb : (S.frameMap p).val.1 = b := (S.frameMap_projection p).trans hp
    cases hb
    rfl
  -- The pullback frame topology records the new base and the same lifted columns.
  have hcolumns : Continuous (fun a : A ↦
      (a.val.1, fun i : Fin (2 * m) ↦
        (⟨a.val.1, a.val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
          TotalSpace RealModel ((f : X → B) *ᵖ E)))) := by
    have hc : Continuous (fun a : OrthogonalFrameBundle (2 * m) ((f : X → B) *ᵖ E) ↦
        (a.1, fun i : Fin (2 * m) ↦
          (⟨a.1, a.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
            TotalSpace RealModel ((f : X → B) *ᵖ E)))) := continuous_induced_dom
    have hv : Continuous (fun a : A ↦ a.val) := continuous_induced_dom
    exact hc.comp hv
  let L : C(A, OrientedOrthogonalFrameBundle m E o) :=
    { toFun a := ⟨⟨f a.val.1, a.val.2⟩, a.property⟩
      continuous_toFun := by
        apply continuous_induced_rng.mpr
        apply continuous_induced_rng.mpr
        exact (f.continuous.comp hcolumns.fst).prodMk (continuous_pi fun i ↦
          (_root_.Pullback.continuous_lift RealModel E f).comp
            ((continuous_apply i).comp hcolumns.snd)) }
  let F (q : Q) : A :=
    ⟨⟨q.val.1, S.frame q.val.2 (f q.val.1) q.property.symm⟩,
      hpositive q.val.2 (f q.val.1) q.property.symm⟩
  have hL (q : Q) : L (F q) = S.frameMap q.val.2 :=
    hfixed q.val.2 (f q.val.1) q.property.symm
  have hF : Continuous F := by
    have hc : Continuous (fun p : P ↦
        ((S.frameMap p).val.1, fun i : Fin (2 * m) ↦
          (⟨(S.frameMap p).val.1,
            (S.frameMap p).val.2 (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ :
              TotalSpace RealModel E))) :=
      continuous_induced_dom.comp (continuous_induced_dom.comp S.frameMap.continuous)
    apply continuous_induced_rng.mpr
    apply continuous_induced_rng.mpr
    refine continuous_subtype_val.fst.prodMk (continuous_pi fun i ↦ ?_)
    rw [(inducing_pullbackTotalSpaceEmbedding RealModel E f).continuous_iff]
    change Continuous (fun q : Q ↦
      (q.val.1, (⟨f q.val.1,
        S.frame q.val.2 (f q.val.1) q.property.symm
          (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)⟩ : TotalSpace RealModel E)))
    refine continuous_subtype_val.fst.prodMk ?_
    exact (((continuous_apply i).comp hc.snd).comp continuous_subtype_val.snd).congr
      (fun q ↦ (hframe q.val.2 (f q.val.1) q.property.symm
        (EuclideanSpace.basisFun (Fin (2 * m)) ℝ i)).symm)
  -- Retaining the new base makes the lifted-frame comparison injective even when f is not.
  have hLI : Function.Injective (fun a : A ↦ (a.val.1, L a)) := by
    rintro ⟨⟨x, a⟩, ha⟩ ⟨⟨y, b⟩, hb⟩ h
    have hxy : x = y := congrArg Prod.fst h
    subst y
    have he : (⟨f x, a⟩ : OrthogonalFrameBundle (2 * m) E) = ⟨f x, b⟩ :=
      congrArg Subtype.val (congrArg Prod.snd h)
    have hab : a = b := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    subst b
    rfl
  -- This homeomorphism identifies the specified principal pullback with the frame pullback.
  let T := {z : A × P // L z.1 = S.frameMap z.2}
  let e : Q ≃ₜ T :=
    { toFun q := ⟨(F q, q.val.2), hL q⟩
      invFun z := ⟨(z.val.1.val.1, z.val.2),
        (congrArg (orientedOrthogonalFrameProjection m E o) z.property).trans
          (S.frameMap_projection z.val.2)⟩
      left_inv q := by
        apply Subtype.ext
        rfl
      right_inv z := by
        apply Subtype.ext
        apply Prod.ext
        · apply hLI
          apply Prod.ext
          · rfl
          · exact (hL _).trans z.property.symm
        · rfl
      continuous_toFun := (hF.prodMk continuous_subtype_val.snd).subtype_mk _
      continuous_invFun :=
        ((hcolumns.fst.comp continuous_subtype_val.fst).prodMk
          continuous_subtype_val.snd).subtype_mk _ }
  refine
    { frameMap := ⟨F, hF⟩
      frameMap_projection := fun _ ↦ rfl
      equivariant := ?_
      is_covering_map := ?_
      fiber_card := ?_ }
  · intro g q v
    -- Apply the original equivariance to the same p and then return to the new base x.
    let w := (realSpinorCoordinateIsometry m).symm
      (realSpinVectorRepresentation m g (realSpinorCoordinateIsometry m v))
    have htotal :
        (⟨f q.val.1,
          S.frame (MulOpposite.op g • q.val.2) (f q.val.1)
            (((hP.projection_smul g q.val.2).trans q.property.symm)) v⟩ :
              TotalSpace RealModel E) =
          ⟨f q.val.1, S.frame q.val.2 (f q.val.1) q.property.symm w⟩ :=
      (hframe _ _ _ v).trans ((S.equivariant g q.val.2 v).trans
        (hframe q.val.2 (f q.val.1) q.property.symm w).symm)
    exact congrArg (fun z : E (f q.val.1) ↦
      (⟨q.val.1, z⟩ : TotalSpace RealModel ((f : X → B) *ᵖ E)))
        (TotalSpace.mk_injective (f q.val.1) htotal)
  · -- The same covering pulls back, then the actual principal-frame homeomorphism transports it.
    exact (S.is_covering_map.pullback L).comp_homeomorph e
  · intro a
    -- The original two frame-fiber points are expressed with the new base coordinate.
    let c : {q : Q // F q = a} ≃ {p : P // S.frameMap p = L a} :=
      { toFun q := ⟨q.val.val.2, (hL q.val).symm.trans (congrArg L q.property)⟩
        invFun p := ⟨e.symm ⟨(a, p.val), p.property.symm⟩, by
          exact congrArg (fun z : T ↦ z.val.1) (e.apply_symm_apply
            (⟨(a, p.val), p.property.symm⟩ : T))⟩
        left_inv q := by
          apply Subtype.ext
          apply e.injective
          rw [e.apply_symm_apply]
          apply Subtype.ext
          exact Prod.ext q.property.symm rfl
        right_inv p := by
          apply Subtype.ext
          rfl }
    exact (Nat.card_congr c).trans (S.fiber_card (L a))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- At the specified pullback principal point, the frame is the original lifted frame. -/
theorem TopologicalSpinStructure.pullback_frame (S : TopologicalSpinStructure m E o hm hP)
    (f : C(X, B)) (q : PrincipalBundlePullback f projection) :
    letI := hP
    letI : ∀ x, NormedAddCommGroup (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hnorm (f x)
    letI : ∀ x, InnerProductSpace ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ hinnerSpace (f x)
    letI : ∀ x, TopologicalSpace (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toUniformSpace.toTopologicalSpace
    letI : FiberBundle RealModel ((f : X → B) *ᵖ E) :=
      FiberBundle.pullback (F := RealModel) (E := E) f
    letI : ∀ x, AddCommMonoid (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hnorm (f x)).toAddCommMonoid
    letI : ∀ x, Module ℝ (((f : X → B) *ᵖ E) x) :=
      fun x ↦ (hinnerSpace (f x)).toModule
    letI : VectorBundle ℝ RealModel ((f : X → B) *ᵖ E) :=
      VectorBundle.pullback ℝ (F := RealModel) (E := E) f
    letI := isContinuousRiemannianBundle_pullback RealModel E f
    (S.pullback f).frame q q.val.1 rfl =
      S.frame q.val.2 (f q.val.1) q.property.symm := by
  rfl

end AtiyahSinger
