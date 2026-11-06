/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BottDisk
public import AtiyahSinger.Topology.BottLoop
public import AtiyahSinger.Topology.LoopClutching
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# The actual idempotent Bott loop and its bundle symbol

Public module ID: M1563.

The positive loop `z * p + (1 - p)` splits on the two original image
bundles of the complementary idempotents. Its nontrivial summand is the
line symbol tensored with the image bundle of `p`. All comparisons retain
the actual boundary map, native tensor topology, and complementary projection.

Source: Karoubi, K-Theory, III.1.6--1.10. The tensor unit below is only the
standard bundle adapter used in that generator comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct Matrix

attribute [local instance] tensorTopology isFiniteRank_tensor sumTopology isFiniteRank_sum
  trivialTopology isFiniteRank_trivial isFiniteRank_pullback sectionModule
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber
  complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar tensor unit on the original finite bundle topology. -/
private theorem exists_tensor_unit_iso {X : Type*} [TopologicalSpace X]
    (E : FiniteBundle X) :
    ∃ e : Iso ((FiniteBundle.trivial X 1).tensor E).Fiber E.Fiber,
      ∀ (x : X) (u : Fin 1 → ℂ) (v : E.Fiber x),
        e.linearEquiv x (u ⊗ₜ[ℂ] v) = u 0 • v := by
  classical
  let c (x : X) : ((Fin 1 → ℂ) ⊗[ℂ] E.Fiber x) ≃ₗ[ℂ] E.Fiber x :=
    (TensorProduct.congr (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
      (LinearEquiv.refl ℂ (E.Fiber x))).trans (TensorProduct.lid ℂ (E.Fiber x))
  -- A finite tensor sum is sent to the corresponding finite sum of scalar multiples.
  have hc : Continuous (fun z : TotalSpace Unit
      ((FiniteBundle.trivial X 1).tensor E).Fiber ↦
        (⟨z.proj, c z.proj z.snd⟩ : TotalSpace Unit E.Fiber)) := by
    apply continuous_iSup_dom.mpr
    intro m
    apply continuous_coinduced_dom.mpr
    let D := TotalSpace Unit (fun x ↦
      (Fin m → Fin 1 → ℂ) × (Fin m → E.Fiber x))
    let : TopologicalSpace D := TopologicalSpace.induced
      (fun z : D ↦ (z.proj,
        (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
          TotalSpace Unit (FiniteBundle.trivial X 1).Fiber)),
        (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) inferInstance
    have hcoords : Continuous (fun z : D ↦ (z.proj,
        (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
          TotalSpace Unit (FiniteBundle.trivial X 1).Fiber)),
        (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) :=
      continuous_induced_dom
    let b : C(D, X) := ⟨fun z ↦ z.proj, hcoords.fst⟩
    let s (j : Fin m) : continuousSections ((b : D → X) *ᵖ E.Fiber) :=
      ⟨fun z ↦ z.snd.2 j, by
        change Continuous (fun z : D ↦
          (⟨z, z.snd.2 j⟩ : TotalSpace Unit ((b : D → X) *ᵖ E.Fiber)))
        rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber b).continuous_iff]
        exact continuous_id.prodMk ((continuous_apply j).comp hcoords.snd.snd)⟩
    have ht : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial X 1).Fiber ↦
        (z.proj, z.snd)) := continuous_induced_dom
    let a (j : Fin m) : C(D, ℂ) :=
      ⟨fun z ↦ z.snd.1 j 0, (continuous_apply 0).comp
        (ht.snd.comp ((continuous_apply j).comp hcoords.snd.fst))⟩
    let sum : continuousSections ((b : D → X) *ᵖ E.Fiber) := ∑ j : Fin m, a j • s j
    have hsum := (Pullback.continuous_lift Unit E.Fiber b).comp sum.property
    apply hsum.congr
    intro z
    apply congrArg (fun v : E.Fiber z.proj ↦ (⟨z.proj, v⟩ : TotalSpace Unit E.Fiber))
    simp only [sum, Submodule.coe_sum, Finset.sum_apply, SetLike.val_smul, Pi.smul_apply,
      map_sum]
    rfl
  -- Finite-rank inversion supplies the inverse on these same total spaces.
  let f : Hom ((FiniteBundle.trivial X 1).tensor E).Fiber E.Fiber :=
    { linearMap x := (c x).toLinearMap
      continuous_total := hc }
  exact ⟨f.toIso (fun x ↦ (c x).bijective), fun _ _ _ ↦ rfl⟩


set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The positive idempotent loop is the disk symbol on its original image bundle. -/
theorem bottMatrixLoop_diskRelativeClass {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : IdempotentMatrix C(X, ℂ)) :
    let E := FiniteBundle.ofFamily (fun x ↦ p.fiber x)
    let f : C(X × Complex.UnitClosedDisc, X) := ContinuousMap.fst
    let g : C(X × Complex.UnitClosedDisc, Complex.UnitClosedDisc) := ContinuousMap.snd
    let a := bottDiskTriple.pullback g
    (bottMatrixLoop p).diskRelativeClass =
      (BundleTriple.ofBoundary (a.source.tensor (E.pullback f))
        (a.target.tensor (E.pullback f))
        (a.boundary.tensorRight (E.pullback f).Fiber)).relativeClass
          (isClosed_complexDiskBoundaryProduct X) := by
  classical
  let Z := X × Complex.UnitClosedDisc
  let A := complexDiskBoundaryProduct X
  let E := FiniteBundle.ofFamily (fun x ↦ p.fiber x)
  let F := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let f : C(Z, X) := ContinuousMap.fst
  let g : C(Z, Complex.UnitClosedDisc) := ContinuousMap.snd
  let W := E.pullback f
  let V := F.pullback f
  let a := bottDiskTriple.pullback g
  let t : BundleTriple A := BundleTriple.ofBoundary
    (a.source.tensor W) (a.target.tensor W) (a.boundary.tensorRight W.Fiber)
  -- Remove the standard scalar tensor factor while retaining its action on vectors.
  obtain ⟨u, hu⟩ := exists_tensor_unit_iso W
  let q : Iso (a.source.tensor W).Fiber W.Fiber :=
    ((pullbackTrivialIso g 1).tensor (Iso.refl W.Fiber)).trans u
  have hq (z : Z) (v : Fin 1 → ℂ) (w : W.Fiber z) :
      q.linearEquiv z (v ⊗ₜ[ℂ] w) = v 0 • w := by
    change u.linearEquiv z
      ((TensorProduct.congr (pullbackTrivialIso g 1 |>.linearEquiv z)
        (LinearEquiv.refl ℂ (W.Fiber z))) (v ⊗ₜ[ℂ] w)) = _
    rw [TensorProduct.congr_tmul, pullbackTrivialIso_apply]
    exact hu z v w
  have hsymbol (z : A) (v : t.source.Fiber z.val) :
      q.linearEquiv z.val (t.boundary.linearEquiv z v) =
        (z.val.2 : ℂ) • q.linearEquiv z.val v := by
    induction v using TensorProduct.inductionOn with
    | tmul v w =>
      change q.linearEquiv z.val
        (TensorProduct.map (a.boundary.linearEquiv z).toLinearMap
          (LinearMap.id : W.Fiber z.val →ₗ[ℂ] W.Fiber z.val) (v ⊗ₜ[ℂ] w)) = _
      rw [TensorProduct.map_tmul, LinearMap.id_apply, hq, hq]
      have ha : a.boundary.linearEquiv z v = (z.val.2 : ℂ) • v := by
        change (bottDiskTriple.boundary.pullback g).linearEquiv z v = _
        rw [RelativeTriple.pullback_apply]
        rfl
      exact (congrArg (fun u : Fin 1 → ℂ ↦ u 0 • w) ha).trans (mul_smul _ _ _)
    | add v w hv hw => simpa only [map_add, smul_add] using congrArg₂ (· + ·) hv hw
  -- Addition in the two complementary image fibers is an actual global isomorphism.
  let add : Hom (W.sum V).Fiber (FiniteBundle.trivial Z p.size).Fiber :=
    { linearMap z := (p.complementIso.linearEquiv z.1).toLinearMap
      continuous_total := by
        have hE : Continuous (fun z : TotalSpace Unit W.Fiber ↦ z.snd.val) :=
          continuous_snd.comp (show Continuous (fun z : TotalSpace Unit W.Fiber ↦
            (f z.proj, z.snd.val)) from continuous_induced_dom.comp
              (Pullback.continuous_lift Unit E.Fiber f))
        have hF : Continuous (fun z : TotalSpace Unit V.Fiber ↦ z.snd.val) :=
          continuous_snd.comp (show Continuous (fun z : TotalSpace Unit V.Fiber ↦
            (f z.proj, z.snd.val)) from continuous_induced_dom.comp
              (Pullback.continuous_lift Unit F.Fiber f))
        apply continuous_induced_rng.mpr
        exact (continuous_proj (E := (W.sum V).Fiber)).prodMk
          ((hE.comp continuous_sum_fst).add (hF.comp continuous_sum_snd)) }
  let j := add.toIso (fun z ↦ (p.complementIso.linearEquiv z.1).bijective)
  let e : Iso (t.sum (BundleTriple.identity A V)).source.Fiber
      (bottMatrixLoop p).diskTriple.source.Fiber :=
    (q.sum (Iso.refl V.Fiber)).trans j
  have he (z : Z) (v : t.source.Fiber z) (w : V.Fiber z) :
      e.linearEquiv z (v, w) = (q.linearEquiv z v).val + w.val := rfl
  -- Every boundary point keeps the positive circle parameter used by the loop construction.
  have hcircle (z : Circle) : (bottMatrixLoop p).circleMap z = bottMatrixUnit p z := by
    let c := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
    have hz : c.symm z ∈ (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Set.Icc 0 (0 + 1) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ _
    obtain ⟨s, hs, hc⟩ := hz
    let s' : unitInterval := ⟨s, by simpa using hs⟩
    have hparameter : Circle.exp (2 * Real.pi * (s' : ℝ)) = z := by
      have hc' := congrArg c hc
      simpa [c, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] using hc'
    rw [← hparameter, FiniteMatrixLoop.circleMap_parameter]
    rfl
  let M (x : X) : Matrix (Fin p.size) (Fin p.size) ℂ := fun i j ↦ p.matrix i j x
  have hboundary (z : A) (v : Fin p.size → ℂ) :
      (bottMatrixLoop p).diskTriple.boundary.linearEquiv z v =
        ((z.val.2 : ℂ) • (M z.val.1) +
          (1 - (M z.val.1))) *ᵥ v := by
    change (fun i j ↦ ((bottMatrixLoop p).circleMap
      (complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩)).val i j z.val.1) *ᵥ v = _
    rw [hcircle]
    congr 1
    ext i j
    simp only [bottMatrixUnit, complexDiskBoundaryHomeomorph, M, Matrix.add_apply,
      Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, ContinuousMap.add_apply,
      ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul]
    split_ifs <;> rfl
  have hsquare (z : A) (v : t.source.Fiber z.val) (w : V.Fiber z.val) :
      e.linearEquiv z.val
        ((t.sum (BundleTriple.identity A V)).boundary.linearEquiv z (v, w)) =
      (bottMatrixLoop p).diskTriple.boundary.linearEquiv z
        (e.linearEquiv z.val (v, w)) := by
    rw [RelativeTriple.sum_apply]
    change e.linearEquiv z.val (t.boundary.linearEquiv z v, w) = _
    rw [he, hsymbol, he, hboundary]
    let P : Matrix (Fin p.size) (Fin p.size) ℂ := M z.val.1
    let Q : Matrix (Fin p.size) (Fin p.size) ℂ := 1 - P
    have hPP : P * P = P :=
      (p.map (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom).mul_self
    have hQQ : Q * Q = Q := by
      exact ((p.map (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom).complement).mul_self
    have hPQ : P + Q = 1 := by dsimp only [Q]; abel
    have hfix (u : p.fiber z.val.1) : P *ᵥ u.val = u.val := by
      obtain ⟨y, hy⟩ := u.property
      change P *ᵥ y = u.val at hy
      rw [← hy, Matrix.mulVec_mulVec, hPP]
    have hfixQ (u : p.complement.fiber z.val.1) : Q *ᵥ u.val = u.val := by
      obtain ⟨y, hy⟩ := u.property
      have hQ : (p.complement.map
          (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom).matrix = Q := by
        ext i j
        simp [IdempotentMatrix.map, IdempotentMatrix.complement, Q, P, M, Matrix.one_apply]
        split_ifs <;> rfl
      change (p.complement.map
        (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom).matrix *ᵥ y = u.val at hy
      rw [hQ] at hy
      rw [← hy, Matrix.mulVec_mulVec, hQQ]
    have hzeroQ (u : p.fiber z.val.1) : Q *ᵥ u.val = 0 := by
      have h := congrArg (fun M ↦ M *ᵥ u.val) hPQ
      rw [Matrix.add_mulVec, Matrix.one_mulVec, hfix] at h
      exact add_left_cancel (h.trans (add_zero _).symm)
    have hzeroP (u : p.complement.fiber z.val.1) : P *ᵥ u.val = 0 := by
      have h := congrArg (fun M ↦ M *ᵥ u.val) hPQ
      rw [Matrix.add_mulVec, Matrix.one_mulVec, hfixQ] at h
      exact add_right_cancel (h.trans (zero_add _).symm)
    calc
      _ = (z.val.2 : ℂ) • (q.linearEquiv z.val v).val + w.val :=
        congrArg (· + w.val)
          (map_smul (p.fiber z.val.1).subtype (z.val.2 : ℂ) (q.linearEquiv z.val v))
      _ = ((z.val.2 : ℂ) • P + Q) *ᵥ ((q.linearEquiv z.val v).val + w.val) := by
        rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
          hfix, hzeroP, hzeroQ, hfixQ, add_zero, zero_add]
      _ = _ := rfl
  -- The complementary summand has the identity boundary and contributes the zero relative class.
  have hiso : (t.sum (BundleTriple.identity A V)).IsIsomorphic
      (bottMatrixLoop p).diskTriple :=
    ⟨e, e, fun z v ↦ hsquare z v.1 v.2⟩
  have hclass := (t.sum (BundleTriple.identity A V)).relativeClass_eq_of_isIsomorphic
    (isClosed_complexDiskBoundaryProduct X) (bottMatrixLoop p).diskTriple hiso
  rw [BundleTriple.relativeClass_sum] at hclass
  have hz : (BundleTriple.identity A V).relativeClass
      (isClosed_complexDiskBoundaryProduct X) = 0 :=
    BundleTriple.relativeClass_identity (isClosed_complexDiskBoundaryProduct X) V
  rw [hz, add_zero] at hclass
  exact hclass.symm


set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in

/-- The specified disk comparison sends an idempotent Bott loop to its geometric product. -/
theorem complexDiskRelativeKZeroEquiv_bottMatrixLoop {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (p : IdempotentMatrix C(X, ℂ)) :
    complexDiskRelativeKZeroEquiv X (bottMatrixLoop p).diskRelativeClass =
      bottLineExternalProduct ((compactSupportKZeroCompactEquiv X).symm
        (AtiyahSinger.kZeroClass C(X, ℂ) p)) := by
  classical
  let Z := X × Complex.UnitClosedDisc
  let A := complexDiskBoundaryProduct X
  let hA := isClosed_complexDiskBoundaryProduct X
  let S := complexDiskBoundary
  let hS := isClosed_complexDiskBoundary
  let := hA.isOpen_compl.locallyCompactSpace
  let := hS.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space S hS
  let E := FiniteBundle.ofFamily (fun x ↦ p.fiber x)
  let f : C(Z, X) := ContinuousMap.fst
  let g : C(Z, Complex.UnitClosedDisc) := ContinuousMap.snd
  let a := bottDiskTriple.pullback g
  let fU : C((Aᶜ : Set Z), X) := f.comp ⟨Subtype.val, continuous_subtype_val⟩
  let e := complexDiskComplementHomeomorph X
  let eD := complexDiskInteriorHomeomorph
  let qA := PointedQuotient.onePointHomeomorph A hA
  let qS := PointedQuotient.onePointHomeomorph S hS
  let j : C(X × ℂ, (Aᶜ : Set Z)) := ⟨e.symm, e.symm.continuous⟩
  let proj : C(X × ℂ, ℂ) := ContinuousMap.snd
  have hπ : IsProperMap proj := isProperMap_snd_of_compactSpace
  let coeff := (compactSupportKZeroCompactEquiv X).symm E.kZeroClass
  let d := relativeKZeroToCompactSupport A hA (a.relativeClass hA)
  -- Tensoring is the original graph action of the image-bundle coefficient.
  have htensor := BundleTriple.relativeClass_tensorRight_pullback A hA a E f
  have hinput : E.kZeroClass = AtiyahSinger.kZeroClass C(X, ℂ) p :=
    kZeroClass_image p
  rw [bottMatrixLoop_diskRelativeClass]
  change compactSupportKZeroPullback j e.symm.isProperMap
    (relativeKZeroToCompactSupport A hA
      ((BundleTriple.ofBoundary (a.source.tensor (E.pullback f))
        (a.target.tensor (E.pullback f))
        (a.boundary.tensorRight (E.pullback f).Fiber)).relativeClass hA)) = _
  rw [htensor]
  change compactSupportKZeroPullback j e.symm.isProperMap
    (compactSupportKZeroAction fU coeff d) = _
  rw [compactSupportKZeroPullback_action]
  -- The same radial map and quotient projection commute with the second projection.
  have hd : compactSupportKZeroPullback j e.symm.isProperMap d =
      compactSupportKZeroPullback proj hπ bottLineClass := by
    have hrel : a.relativeClass hA =
        relativeKZeroPullback A hA S hS g (fun _ hx ↦ hx) bottDiskClass :=
      bottDiskTriple.relativeClass_pullback hS g
    let q := PointedQuotient.mapContinuous A S g (fun _ hx ↦ hx)
    let iA : C(OnePoint (Aᶜ : Set Z), PointedQuotient A) :=
      ⟨qA.symm, qA.symm.continuous⟩
    let iS : C(OnePoint (Sᶜ : Set Complex.UnitClosedDisc), PointedQuotient S) :=
      ⟨qS.symm, qS.symm.continuous⟩
    let J := properOnePointMap j e.symm.isProperMap
    let D := properOnePointMap ⟨eD.symm, eD.symm.continuous⟩ eD.symm.isProperMap
    let P := properOnePointMap proj hπ
    have hsquare : q.comp (iA.comp J) = iS.comp (D.comp P) := by
      ext z
      cases z using OnePoint.rec with
      | infty =>
        change q (qA.symm OnePoint.infty) = qS.symm OnePoint.infty
        rw [PointedQuotient.onePointHomeomorph_symm_infty,
          PointedQuotient.onePointHomeomorph_symm_infty]
        rfl
      | coe z =>
        have hleft : qA.symm (e.symm z : OnePoint (Aᶜ : Set Z)) =
            PointedQuotient.of A (e.symm z).val :=
          qA.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of A hA _).symm
        have hright : qS.symm (eD.symm z.2 : OnePoint (Sᶜ : Set Complex.UnitClosedDisc)) =
            PointedQuotient.of S (eD.symm z.2).val :=
          qS.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of S hS _).symm
        change q (qA.symm (e.symm z : OnePoint (Aᶜ : Set Z))) =
          qS.symm (eD.symm z.2 : OnePoint (Sᶜ : Set Complex.UnitClosedDisc))
        rw [hleft, hright]
        rfl
    have hline := bottDiskClass_toCompactSupport
    change compactSupportKZeroHomeomorph eD
        (relativeKZeroToCompactSupport S hS bottDiskClass) = bottLineClass at hline
    rw [← hline]
    apply Subtype.ext
    change complexKZeroPullback J (complexKZeroPullback iA (a.relativeClass hA).val) =
      complexKZeroPullback P (complexKZeroPullback D
        (complexKZeroPullback iS bottDiskClass.val))
    rw [hrel]
    change complexKZeroPullback J (complexKZeroPullback iA
      (complexKZeroPullback q bottDiskClass.val)) = _
    simp only [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp]
    have hsquare' : (q.comp iA).comp J = (iS.comp D).comp P := hsquare
    rw [hsquare']
    change complexKZeroPullback (iS.comp (D.comp P)) bottDiskClass.val = _
    rw [complexKZeroPullback_comp, AddMonoidHom.comp_apply]
  rw [hd]
  -- The two proper maps compose to the identity of the actual product coordinates.
  let graph : C(X × ℂ, X × (X × ℂ)) :=
    (fU.comp j).prodMk (ContinuousMap.id (X × ℂ))
  have hgraph : IsProperMap graph :=
    isProperMap_of_comp_of_t2 graph.continuous continuous_snd isProperMap_id
  let project : C(X × (X × ℂ), X × ℂ) := (ContinuousMap.id X).prodMap proj
  have hproject : IsProperMap project := isProperMap_id.prodMap hπ
  have hproduct := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id X) isProperMap_id proj hπ coeff bottLineClass
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
  change compactSupportKZeroPullback graph hgraph
    (compactSupportKZeroExternalProduct coeff
      (compactSupportKZeroPullback proj hπ bottLineClass)) = _
  rw [← hproduct, ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  have hid : project.comp graph = ContinuousMap.id (X × ℂ) := by
    apply ContinuousMap.ext
    intro z
    rfl
  change compactSupportKZeroPullback (project.comp graph) (hproject.comp hgraph)
    (compactSupportKZeroExternalProduct coeff bottLineClass) = _
  simp only [hid, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  change bottLineExternalProduct ((compactSupportKZeroCompactEquiv X).symm E.kZeroClass) = _
  rw [hinput]

end AtiyahSinger
