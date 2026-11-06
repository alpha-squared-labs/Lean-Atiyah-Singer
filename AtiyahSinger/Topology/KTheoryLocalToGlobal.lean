/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.KTheoryMayerVietoris
public import AtiyahSinger.Topology.SuspendedKModule

/-!
# The finite-family local-to-global theorem in complex K-theory

Public module ID: M1917.

Karoubi IV.1.3 uses a fixed finite family of degree-zero classes on Y over X.
Its fundamental homomorphism is the sum of multiplication by those same classes
in each nonpositive degree. The local hypothesis applies to every closed subset
of every member of a finite closed cover, not just to the cover members or points.
Restrictions of the classes are the actual proper pullbacks along closed inclusions.

The theorem is stated for locally compact Hausdorff spaces and arbitrary continuous
f, as in the source; compactness of X and properness of f are not assumed. This is
the complex K-theory case, with no claim to the real or other coefficient theories.
The proof uses the full suspended Mayer--Vietoris exact sequences and the compatibility
of the same graph action with their specified connecting maps. It descends simultaneously
over all closed subsets of finite partial unions, then removes the universal-set subtypes.
The empty cover and empty generator family require no additional hypotheses.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]

/-- Karoubi's fundamental map for a finite family of specified degree-zero classes. -/
def compactSupportKLerayHirschMap (n : ℕ) (f : C(Y, X)) {r : ℕ}
    (u : Fin r → CompactSupportKZero Y) :
    (Fin r → CompactSupportK n X) →+ CompactSupportK n Y where
  toFun a := ∑ i, compactSupportKAction n f (a i) (u i)
  map_zero' := by simp
  map_add' a b := by simp [Finset.sum_add_distrib]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3000000 in

/-- KA IV.1.3: the same family gives an isomorphism in every degree by finite closed descent. -/
theorem compactSupportKLerayHirschMap_bijective_of_closed_cover (f : C(Y, X)) {r N : ℕ}
    (u : Fin r → CompactSupportKZero Y) (W : Fin N → Set X)
    (hW : ∀ i, IsClosed (W i)) (hcover : ⋃ i, W i = Set.univ)
    (hloc : ∀ (i : Fin N) (C : Set X) (hC : IsClosed C), C ⊆ W i →
      letI := hC.locallyCompactSpace
      letI := (hC.preimage f.continuous).locallyCompactSpace
      ∀ n : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap n (preimageSubspaceMap C f)
          (fun j ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage f.continuous).isProperMap_subtypeVal (u j))))
    (n : ℕ) : Function.Bijective (compactSupportKLerayHirschMap n f u) := by
  /- Stage 1: for every closed C, its inverse image is closed in Y. Both subspaces
  are LCH, their inclusions are proper, and the restricted classes are exactly
  those in hloc. The fundamental map uses the same graph action and finite sum.
  Stage 2: use Karoubi II.4.18's full suspended Mayer--Vietoris sequences for a
  closed union A∪B and the corresponding inverse-image union in Y. Multiplication
  by the fixed degree-zero classes commutes with restriction, open extension and
  the connecting homomorphism, as established in IV.1.3 via II.4.9. Apply finite
  direct products to the source sequence. The established exactness and boundary compatibility
  supply the commuting five-term diagram in every required degree.
  Stage 3: induct on the number of cover members, simultaneously for every closed
  subset of the partial union. The intersection with the last cover member is
  among the closed subsets covered by hloc. For degree -n the five-term segment
  uses degrees -(n+1) and -n, both provided by the all-n induction hypothesis.
  Four vertical maps are isomorphisms, so the five lemma gives the central one.
  Stage 4: the total union is X by hcover. The resulting central map is precisely
  the displayed sum of graph actions. Empty covers and empty generator families
  are included by the zero-group cases, with no added nonemptiness hypothesis. -/
  classical
  -- First record the proper base-change squares for the original graph action.
  have action_precomp {P Q Z : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
      (k : ℕ) (g : C(P, Q)) (hg : IsProperMap g) (v : C(Z, P))
      (a : CompactSupportK k Q) (b : CompactSupportKZero Z) :
      compactSupportKAction k v (compactSupportKPullback k g hg a) b =
        compactSupportKAction k (g.comp v) a b := by
    let T := Fin k → ℝ
    let G := g.prodMap (ContinuousMap.id T)
    have hG : IsProperMap G := hg.prodMap isProperMap_id
    let H : C(Z × T, (P × T) × Z) :=
      (v.prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let K : C(Z × T, (Q × T) × Z) :=
      ((g.comp v).prodMap (ContinuousMap.id T)).prodMk ContinuousMap.fst
    let retract : C((P × T) × Z, Z × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    have hH : IsProperMap H :=
      isProperMap_of_comp_of_t2 H.continuous retract.continuous isProperMap_id
    let retract' : C((Q × T) × Z, Z × T) :=
      ContinuousMap.snd.prodMk (ContinuousMap.snd.comp ContinuousMap.fst)
    have hK : IsProperMap K :=
      isProperMap_of_comp_of_t2 K.continuous retract'.continuous isProperMap_id
    let L := G.prodMap (ContinuousMap.id Z)
    have hL : IsProperMap L := hG.prodMap isProperMap_id
    have hproduct := compactSupportKZeroExternalProduct_properPullback
      G hG (ContinuousMap.id Z) isProperMap_id a b
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hproduct
    change compactSupportKZeroPullback H hH
        (compactSupportKZeroExternalProduct (compactSupportKZeroPullback G hG a) b) =
      compactSupportKZeroPullback K hK (compactSupportKZeroExternalProduct a b)
    rw [← hproduct]
    have hcomp := compactSupportKZeroPullback_comp H L hH hL
    exact (DFunLike.congr_fun hcomp (compactSupportKZeroExternalProduct a b)).symm
  have natural {P Q P' Q' : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      [TopologicalSpace P'] [LocallyCompactSpace P'] [T2Space P']
      [TopologicalSpace Q'] [LocallyCompactSpace Q'] [T2Space Q']
      {s : ℕ} (k : ℕ) (v : C(Q, P)) (v' : C(Q', P'))
      (g : C(P', P)) (hg : IsProperMap g) (j : C(Q', Q)) (hj : IsProperMap j)
      (hcomm : v.comp j = g.comp v') (w : Fin s → CompactSupportKZero Q)
      (a : Fin s → CompactSupportK k P) :
      compactSupportKPullback k j hj (compactSupportKLerayHirschMap k v w a) =
        compactSupportKLerayHirschMap k v'
          (fun i ↦ compactSupportKZeroPullback j hj (w i))
          (fun i ↦ compactSupportKPullback k g hg (a i)) := by
    change compactSupportKPullback k j hj (∑ i, compactSupportKAction k v (a i) (w i)) =
      ∑ i, compactSupportKAction k v' (compactSupportKPullback k g hg (a i))
        (compactSupportKZeroPullback j hj (w i))
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [compactSupportKPullback_action, hcomm]
    exact (action_precomp k g hg v' (a i)
      (compactSupportKZeroPullback j hj (w i))).symm
  -- Homeomorphism comparisons are conjugations of this same fundamental map.
  have transport {P Q P' Q' : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      [TopologicalSpace P'] [LocallyCompactSpace P'] [T2Space P']
      [TopologicalSpace Q'] [LocallyCompactSpace Q'] [T2Space Q']
      {s : ℕ} (k : ℕ) (v : C(Q, P)) (v' : C(Q', P'))
      (e : P' ≃ₜ P) (d : Q' ≃ₜ Q)
      (hcomm : v.comp ⟨d, d.continuous⟩ = (⟨e, e.continuous⟩ : C(P', P)).comp v')
      (w : Fin s → CompactSupportKZero Q)
      (hv : Function.Bijective (compactSupportKLerayHirschMap k v w)) :
      Function.Bijective (compactSupportKLerayHirschMap k v'
        (fun i ↦ compactSupportKZeroPullback ⟨d, d.continuous⟩ d.isProperMap (w i))) := by
    let E := Equiv.piCongrRight
      (fun _ : Fin s ↦ (compactSupportKHomeomorphEquiv k e.symm).toEquiv)
    let D := compactSupportKHomeomorphEquiv k d.symm
    have hsquare (a : Fin s → CompactSupportK k P) :
        D (compactSupportKLerayHirschMap k v w a) =
          compactSupportKLerayHirschMap k v'
            (fun i ↦ compactSupportKZeroPullback ⟨d, d.continuous⟩ d.isProperMap (w i))
            (E a) := natural k v v' ⟨e, e.continuous⟩ e.isProperMap
              ⟨d, d.continuous⟩ d.isProperMap hcomm w a
    constructor
    · intro a b hab
      apply E.symm.injective
      apply hv.injective
      apply D.injective
      rw [hsquare, hsquare, E.apply_symm_apply, E.apply_symm_apply]
      exact hab
    · intro b
      obtain ⟨a, ha⟩ := hv.surjective (D.symm b)
      refine ⟨E a, ?_⟩
      rw [← hsquare, ha, D.apply_symm_apply]
  -- All closed subsets are retained in the induction, with their original restricted classes.
  let Good (C : Set X) (hC : IsClosed C) : Prop :=
    let := hC.locallyCompactSpace
    let := (hC.preimage f.continuous).locallyCompactSpace
    ∀ k : ℕ, Function.Bijective
      (compactSupportKLerayHirschMap k (preimageSubspaceMap C f)
        (fun j ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
          (hC.preimage f.continuous).isProperMap_subtypeVal (u j)))
  have nested (C : Set X) (hC : IsClosed C) (D : Set C) (hD : IsClosed D)
      (hgood : Good (Subtype.val '' D) (hC.isClosedMap_subtype_val D hD)) :
      letI := hC.locallyCompactSpace
      letI := (hC.preimage f.continuous).locallyCompactSpace
      let v := preimageSubspaceMap C f
      letI := hD.locallyCompactSpace
      letI := (hD.preimage v.continuous).locallyCompactSpace
      ∀ k : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap k (preimageSubspaceMap D v)
          (fun i ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hD.preimage v.continuous).isProperMap_subtypeVal
              (compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
                (hC.preimage f.continuous).isProperMap_subtypeVal (u i)))) := by
    let := hC.locallyCompactSpace
    let := (hC.preimage f.continuous).locallyCompactSpace
    let v := preimageSubspaceMap C f
    let := hD.locallyCompactSpace
    let := (hD.preimage v.continuous).locallyCompactSpace
    let E : Set X := Subtype.val '' D
    have hE : IsClosed E := hC.isClosedMap_subtype_val D hD
    let := hE.locallyCompactSpace
    let := (hE.preimage f.continuous).locallyCompactSpace
    have mem_image (x : X) : x ∈ E ↔ ∃ hx : x ∈ C, (⟨x, hx⟩ : C) ∈ D := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z.property, hz⟩
      · rintro ⟨hx, hz⟩
        exact ⟨⟨x, hx⟩, hz, rfl⟩
    let e : D ≃ₜ E :=
      { toFun z := ⟨z.val.val, ⟨z.val, z.property, rfl⟩⟩
        invFun z := ⟨⟨z.val, ((mem_image z.val).mp z.property).choose⟩,
          ((mem_image z.val).mp z.property).choose_spec⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let d : (v ⁻¹' D) ≃ₜ (f ⁻¹' E) :=
      { toFun z := ⟨z.val.val, ⟨v z.val, z.property, rfl⟩⟩
        invFun z := ⟨⟨z.val, ((mem_image (f z.val)).mp z.property).choose⟩,
          ((mem_image (f z.val)).mp z.property).choose_spec⟩
        left_inv _ := rfl
        right_inv _ := rfl
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    let iC : C(f ⁻¹' C, Y) := ⟨Subtype.val, continuous_subtype_val⟩
    let iD : C(v ⁻¹' D, f ⁻¹' C) := ⟨Subtype.val, continuous_subtype_val⟩
    let iE : C(f ⁻¹' E, Y) := ⟨Subtype.val, continuous_subtype_val⟩
    have hiC : IsProperMap iC := (hC.preimage f.continuous).isProperMap_subtypeVal
    have hiD : IsProperMap iD := (hD.preimage v.continuous).isProperMap_subtypeVal
    have hiE : IsProperMap iE := (hE.preimage f.continuous).isProperMap_subtypeVal
    have hw : (fun i ↦ compactSupportKZeroPullback ⟨d, d.continuous⟩ d.isProperMap
        (compactSupportKZeroPullback iE hiE (u i))) =
        (fun i ↦ compactSupportKZeroPullback iD hiD
          (compactSupportKZeroPullback iC hiC (u i))) := by
      funext i
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      rfl
    change ∀ k : ℕ, Function.Bijective
      (compactSupportKLerayHirschMap k (preimageSubspaceMap D v)
        (fun i ↦ compactSupportKZeroPullback iD hiD
          (compactSupportKZeroPullback iC hiC (u i))))
    intro k
    have h := transport k (preimageSubspaceMap E f) (preimageSubspaceMap D v)
      e d (by rfl) (fun i ↦ compactSupportKZeroPullback iE hiE (u i)) (hgood k)
    rw [hw] at h
    exact h
  -- The empty-cover case uses the actual reduced evaluation kernel on an empty space.
  have vanish {Z : Type _} [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
      [IsEmpty Z] (k : ℕ) (a : CompactSupportK k Z) : a = 0 := by
    let T := Z × (Fin k → ℝ)
    let ev : C(OnePoint T, ℂ) →+* ℂ :=
      (ContinuousMap.evalAlgHom ℂ ℂ (OnePoint.infty : OnePoint T)).toRingHom
    let c : ℂ →+* C(OnePoint T, ℂ) := algebraMap ℂ C(OnePoint T, ℂ)
    have hc : c.comp ev = RingHom.id C(OnePoint T, ℂ) := by
      ext b z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe z => exact isEmptyElim z
    have hid : (kZeroMap c).comp (kZeroMap ev) = AddMonoidHom.id _ := by
      rw [← kZeroMap_comp, hc, kZeroMap_id]
    have ha : kZeroMap ev a.val = 0 := a.property
    apply Subtype.ext
    change a.val = 0
    calc
      a.val = kZeroMap c (kZeroMap ev a.val) := (DFunLike.congr_fun hid a.val).symm
      _ = 0 := by rw [ha, map_zero]
  -- The two-piece step is the five-lemma chase on these actual Mayer--Vietoris maps.
  have glue {P Q : Type _}
      [TopologicalSpace P] [LocallyCompactSpace P] [T2Space P]
      [TopologicalSpace Q] [LocallyCompactSpace Q] [T2Space Q]
      {s : ℕ} (v : C(Q, P)) (w : Fin s → CompactSupportKZero Q)
      (A B : Set P) (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = Set.univ)
      (hpieces : ∀ (C : Set P) (hC : IsClosed C),
        C = A ∨ C = B ∨ C = A ∩ B →
        letI := hC.locallyCompactSpace
        letI := (hC.preimage v.continuous).locallyCompactSpace
        ∀ k : ℕ, Function.Bijective
          (compactSupportKLerayHirschMap k (preimageSubspaceMap C v)
            (fun i ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
              (hC.preimage v.continuous).isProperMap_subtypeVal (w i))))
      (k : ℕ) : Function.Bijective (compactSupportKLerayHirschMap k v w) := by
    let := hA.locallyCompactSpace
    let := hB.locallyCompactSpace
    let := (hA.inter hB).locallyCompactSpace
    let YA := v ⁻¹' A
    let YB := v ⁻¹' B
    have hYA : IsClosed YA := hA.preimage v.continuous
    have hYB : IsClosed YB := hB.preimage v.continuous
    have hYAB : YA ∪ YB = Set.univ := by
      rw [← Set.preimage_union, hAB, Set.preimage_univ]
    let := hYA.locallyCompactSpace
    let := hYB.locallyCompactSpace
    let := (hYA.inter hYB).locallyCompactSpace
    let vA : C(YA, A) := preimageSubspaceMap A v
    let vB : C(YB, B) := preimageSubspaceMap B v
    let vO : C((YA ∩ YB : Set Q), (A ∩ B : Set P)) :=
      preimageSubspaceMap (A ∩ B) v
    let jA : C(YA, Q) := ⟨Subtype.val, continuous_subtype_val⟩
    let jB : C(YB, Q) := ⟨Subtype.val, continuous_subtype_val⟩
    let jO : C((YA ∩ YB : Set Q), Q) := ⟨Subtype.val, continuous_subtype_val⟩
    let wA := fun i ↦ compactSupportKZeroPullback jA hYA.isProperMap_subtypeVal (w i)
    let wB := fun i ↦ compactSupportKZeroPullback jB hYB.isProperMap_subtypeVal (w i)
    let wO := fun i ↦ compactSupportKZeroPullback jO
      (hYA.inter hYB).isProperMap_subtypeVal (w i)
    let F (l : ℕ) := compactSupportKLerayHirschMap l v w
    let FA (l : ℕ) := compactSupportKLerayHirschMap l vA wA
    let FB (l : ℕ) := compactSupportKLerayHirschMap l vB wB
    let FO (l : ℕ) := compactSupportKLerayHirschMap l vO wO
    have hFA (l : ℕ) : Function.Bijective (FA l) := hpieces A hA (Or.inl rfl) l
    have hFB (l : ℕ) : Function.Bijective (FB l) := hpieces B hB (Or.inr (Or.inl rfl)) l
    have hFO (l : ℕ) : Function.Bijective (FO l) :=
      hpieces (A ∩ B) (hA.inter hB) (Or.inr (Or.inr rfl)) l
    let RX (l : ℕ) := compactSupportKMayerVietorisRestriction l A B hA hB
    let VX (l : ℕ) := compactSupportKMayerVietorisDifference l A B hA hB
    let DX (l : ℕ) := compactSupportKMayerVietorisBoundary l A B hA hB hAB
    let RY (l : ℕ) := compactSupportKMayerVietorisRestriction l YA YB hYA hYB
    let VY (l : ℕ) := compactSupportKMayerVietorisDifference l YA YB hYA hYB
    let DY (l : ℕ) := compactSupportKMayerVietorisBoundary l YA YB hYA hYB hYAB
    -- The diagonal restrictions use the identical proper pullbacks of the fixed family.
    have hR (l : ℕ) (a : Fin s → CompactSupportK l P) :
        RY l (F l a) =
          (FA l (fun i ↦ (RX l (a i)).1), FB l (fun i ↦ (RX l (a i)).2)) := by
      apply Prod.ext
      · change compactSupportKClosedRestriction l YA hYA
          (∑ i, compactSupportKAction l v (a i) (w i)) =
          ∑ i, compactSupportKAction l vA
            (compactSupportKClosedRestriction l A hA (a i)) (wA i)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact compactSupportKClosedRestriction_action l A hA v (a i) (w i)
      · change compactSupportKClosedRestriction l YB hYB
          (∑ i, compactSupportKAction l v (a i) (w i)) =
          ∑ i, compactSupportKAction l vB
            (compactSupportKClosedRestriction l B hB (a i)) (wB i)
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact compactSupportKClosedRestriction_action l B hB v (a i) (w i)
    let left : C((A ∩ B : Set P), A) :=
      ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩
    let right : C((A ∩ B : Set P), B) :=
      ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩
    let leftY : C((YA ∩ YB : Set Q), YA) :=
      ⟨fun x ↦ ⟨x.val, x.property.1⟩, continuous_subtype_val.subtype_mk _⟩
    let rightY : C((YA ∩ YB : Set Q), YB) :=
      ⟨fun x ↦ ⟨x.val, x.property.2⟩, continuous_subtype_val.subtype_mk _⟩
    have hleft : IsProperMap left := isProperMap_of_comp_of_t2 left.continuous
      continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
    have hright : IsProperMap right := isProperMap_of_comp_of_t2 right.continuous
      continuous_subtype_val (hA.inter hB).isProperMap_subtypeVal
    have hleftY : IsProperMap leftY := isProperMap_of_comp_of_t2 leftY.continuous
      continuous_subtype_val (hYA.inter hYB).isProperMap_subtypeVal
    have hrightY : IsProperMap rightY := isProperMap_of_comp_of_t2 rightY.continuous
      continuous_subtype_val (hYA.inter hYB).isProperMap_subtypeVal
    have hwleft : (fun i ↦ compactSupportKZeroPullback leftY hleftY (wA i)) = wO := by
      funext i
      change compactSupportKZeroPullback leftY hleftY
        (compactSupportKZeroPullback jA hYA.isProperMap_subtypeVal (w i)) = _
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      rfl
    have hwright : (fun i ↦ compactSupportKZeroPullback rightY hrightY (wB i)) = wO := by
      funext i
      change compactSupportKZeroPullback rightY hrightY
        (compactSupportKZeroPullback jB hYB.isProperMap_subtypeVal (w i)) = _
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      rfl
    have hleft_square (l : ℕ) (a : Fin s → CompactSupportK l A) :
        compactSupportKPullback l leftY hleftY (FA l a) =
          FO l (fun i ↦ compactSupportKPullback l left hleft (a i)) := by
      have h := natural l vA vO left hleft leftY hleftY (by rfl) wA a
      rw [hwleft] at h
      exact h
    have hright_square (l : ℕ) (a : Fin s → CompactSupportK l B) :
        compactSupportKPullback l rightY hrightY (FB l a) =
          FO l (fun i ↦ compactSupportKPullback l right hright (a i)) := by
      have h := natural l vB vO right hright rightY hrightY (by rfl) wB a
      rw [hwright] at h
      exact h
    -- Difference and connecting maps commute before any injectivity is used.
    have hV (l : ℕ) (a : Fin s → CompactSupportK l A) (b : Fin s → CompactSupportK l B) :
        VY l (FA l a, FB l b) = FO l (fun i ↦ VX l (a i, b i)) := by
      change compactSupportKPullback l leftY hleftY (FA l a) -
        compactSupportKPullback l rightY hrightY (FB l b) = _
      rw [hleft_square, hright_square]
      exact (map_sub (FO l) _ _).symm
    have hD (l : ℕ) (a : Fin s → CompactSupportK (l + 1) (A ∩ B : Set P)) :
        F l (fun i ↦ DX l (a i)) = DY l (FO (l + 1) a) := by
      change (∑ i, compactSupportKAction l v (DX l (a i)) (w i)) =
        DY l (∑ i, compactSupportKAction (l + 1) vO (a i) (wO i))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      exact compactSupportKAction_mayerVietorisBoundary l A B hA hB hAB v (a i) (w i)
    have xDV := range_compactSupportKMayerVietorisDifference_eq_ker_boundary k A B hA hB hAB
    have xDR := range_compactSupportKMayerVietorisBoundary_eq_ker_restriction k A B hA hB hAB
    have xRV := range_compactSupportKMayerVietorisRestriction_eq_ker_difference k A B hA hB hAB
    have yDV := range_compactSupportKMayerVietorisDifference_eq_ker_boundary k YA YB
      hYA hYB hYAB
    have yDR := range_compactSupportKMayerVietorisBoundary_eq_ker_restriction k YA YB
      hYA hYB hYAB
    have yRV := range_compactSupportKMayerVietorisRestriction_eq_ker_difference k YA YB
      hYA hYB hYAB
    change Function.Bijective (F k)
    constructor
    · -- Injectivity: correct a boundary lift by the same two piecewise lifts.
      apply (injective_iff_map_eq_zero _).mpr
      intro a ha
      have hr := hR k a
      rw [ha, map_zero] at hr
      have hza : (fun i ↦ (RX k (a i)).1) = 0 :=
        (hFA k).injective (by simpa using (congrArg Prod.fst hr).symm)
      have hzb : (fun i ↦ (RX k (a i)).2) = 0 :=
        (hFB k).injective (by simpa using (congrArg Prod.snd hr).symm)
      have hboundary (i : Fin s) : ∃ c, DX k c = a i := by
        have hker : a i ∈ (RX k).ker :=
          Prod.ext (congrFun hza i) (congrFun hzb i)
        rw [← xDR] at hker
        exact hker
      choose c hc using hboundary
      have hz : DY k (FO (k + 1) c) = 0 := by
        rw [← hD, show (fun i ↦ DX k (c i)) = a from funext hc, ha]
      have hker : FO (k + 1) c ∈ (DY k).ker := hz
      rw [← yDV] at hker
      obtain ⟨p, hp⟩ := hker
      obtain ⟨aA, haA⟩ := (hFA (k + 1)).surjective p.1
      obtain ⟨aB, haB⟩ := (hFB (k + 1)).surjective p.2
      have hv := hV (k + 1) aA aB
      rw [haA, haB] at hv
      have heq : (fun i ↦ VX (k + 1) (aA i, aB i)) = c :=
        (hFO (k + 1)).injective (hv.symm.trans hp)
      funext i
      change a i = 0
      rw [← hc i, ← congrFun heq i]
      have hmem : VX (k + 1) (aA i, aB i) ∈ (VX (k + 1)).range :=
        ⟨(aA i, aB i), rfl⟩
      rw [xDV] at hmem
      exact hmem
    · -- Surjectivity: glue the two lifts, then remove the remaining boundary error.
      intro b
      obtain ⟨aA, haA⟩ := (hFA k).surjective (RY k b).1
      obtain ⟨aB, haB⟩ := (hFB k).surjective (RY k b).2
      have hmem : RY k b ∈ (RY k).range := ⟨b, rfl⟩
      rw [yRV] at hmem
      have hz : FO k (fun i ↦ VX k (aA i, aB i)) = 0 := by
        rw [← hV, haA, haB]
        exact hmem
      have hzero : (fun i ↦ VX k (aA i, aB i)) = 0 :=
        (hFO k).injective (by simpa only [map_zero] using hz)
      have hlift (i : Fin s) : ∃ a, RX k a = (aA i, aB i) := by
        have hker : (aA i, aB i) ∈ (VX k).ker := congrFun hzero i
        rw [← xRV] at hker
        exact hker
      choose a ha using hlift
      have hrestA : (fun i ↦ (RX k (a i)).1) = aA :=
        funext (fun i ↦ congrArg Prod.fst (ha i))
      have hrestB : (fun i ↦ (RX k (a i)).2) = aB :=
        funext (fun i ↦ congrArg Prod.snd (ha i))
      have herr : b - F k a ∈ (RY k).ker := by
        change RY k (b - F k a) = 0
        rw [map_sub, hR, hrestA, hrestB, haA, haB]
        exact sub_self _
      rw [← yDR] at herr
      obtain ⟨d, hd⟩ := herr
      obtain ⟨c, hc⟩ := (hFO (k + 1)).surjective d
      refine ⟨a + (fun i ↦ DX k (c i)), ?_⟩
      rw [map_add, hD, hc, hd]
      abel
  -- Keep both independent universe roles in the empty-source and empty-target cases.
  have vanishTarget {Z : Type _}
      [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]
      [IsEmpty Z] (k : ℕ) (a : CompactSupportK k Z) : a = 0 := by
    let T := Z × (Fin k → ℝ)
    let ev : C(OnePoint T, ℂ) →+* ℂ :=
      (ContinuousMap.evalAlgHom ℂ ℂ (OnePoint.infty : OnePoint T)).toRingHom
    let c : ℂ →+* C(OnePoint T, ℂ) := algebraMap ℂ C(OnePoint T, ℂ)
    have hc : c.comp ev = RingHom.id C(OnePoint T, ℂ) := by
      ext b z
      cases z using OnePoint.rec with
      | infty => rfl
      | coe z => exact isEmptyElim z
    have hid : (kZeroMap c).comp (kZeroMap ev) = AddMonoidHom.id _ := by
      rw [← kZeroMap_comp, hc, kZeroMap_id]
    have ha : kZeroMap ev a.val = 0 := a.property
    apply Subtype.ext
    change a.val = 0
    calc
      a.val = kZeroMap c (kZeroMap ev a.val) := (DFunLike.congr_fun hid a.val).symm
      _ = 0 := by rw [ha, map_zero]
  -- Induct simultaneously on every closed subset of the partial finite union.
  have descent (s : Finset (Fin N)) :
      ∀ (C : Set X) (hC : IsClosed C), C ⊆ ⋃ i ∈ s, W i → Good C hC := by
    induction s using Finset.induction_on with
    | empty =>
      intro C hC hsub
      let := hC.locallyCompactSpace
      let := (hC.preimage f.continuous).locallyCompactSpace
      have hempty : C ⊆ ∅ := by simpa using hsub
      let : IsEmpty C := ⟨fun x ↦ hempty x.property⟩
      let : IsEmpty (f ⁻¹' C) := ⟨fun y ↦ hempty y.property⟩
      change ∀ k : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap k (preimageSubspaceMap C f)
          (fun i ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage f.continuous).isProperMap_subtypeVal (u i)))
      intro k
      constructor
      · intro a b _
        funext i
        exact (vanish k (a i)).trans (vanish k (b i)).symm
      · intro b
        refine ⟨0, ?_⟩
        exact (map_zero _).trans (vanishTarget k b).symm
    | @insert j s _ ih =>
      intro C hC hsub
      let := hC.locallyCompactSpace
      let := (hC.preimage f.continuous).locallyCompactSpace
      let U : Set X := ⋃ i ∈ s, W i
      have hU : IsClosed U := isClosed_biUnion_finset (fun i _ ↦ hW i)
      let A : Set C := Subtype.val ⁻¹' W j
      let B : Set C := Subtype.val ⁻¹' U
      have hA : IsClosed A := (hW j).preimage continuous_subtype_val
      have hB : IsClosed B := hU.preimage continuous_subtype_val
      have hcoverC : C ⊆ W j ∪ U := by
        intro x hx
        obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsub hx)
        obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
        rcases Finset.mem_insert.mp his with rfl | his
        · exact Or.inl hxi
        · exact Or.inr (Set.mem_iUnion.mpr
            ⟨i, Set.mem_iUnion.mpr ⟨his, hxi⟩⟩)
      have hAB : A ∪ B = Set.univ :=
        Set.eq_univ_of_forall (fun x ↦ hcoverC x.property)
      change ∀ k : ℕ, Function.Bijective
        (compactSupportKLerayHirschMap k (preimageSubspaceMap C f)
          (fun i ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
            (hC.preimage f.continuous).isProperMap_subtypeVal (u i)))
      intro k
      apply glue (preimageSubspaceMap C f)
        (fun i ↦ compactSupportKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩
          (hC.preimage f.continuous).isProperMap_subtypeVal (u i)) A B hA hB hAB ?_ k
      intro D hD hcase
      apply nested C hC D hD
      rcases hcase with rfl | rfl | rfl
      · apply hloc j _ (hC.isClosedMap_subtype_val A hA)
        rintro x ⟨z, hz, rfl⟩
        exact hz
      · apply ih _ (hC.isClosedMap_subtype_val B hB)
        rintro x ⟨z, hz, rfl⟩
        exact hz
      · apply ih _ (hC.isClosedMap_subtype_val (A ∩ B) (hA.inter hB))
        rintro x ⟨z, hz, rfl⟩
        exact hz.2
  -- Finally remove the two literal universal-set subtypes, preserving the family u.
  have hglobal : Good Set.univ isClosed_univ := by
    apply descent Finset.univ Set.univ isClosed_univ
    intro x _
    have hx : x ∈ ⋃ i, W i := hcover ▸ Set.mem_univ x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let := (isClosed_univ : IsClosed (Set.univ : Set X)).locallyCompactSpace
  let := ((isClosed_univ : IsClosed (Set.univ : Set X)).preimage
    f.continuous).locallyCompactSpace
  let e : X ≃ₜ (Set.univ : Set X) :=
    { toFun x := ⟨x, Set.mem_univ x⟩
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let d : Y ≃ₜ (f ⁻¹' (Set.univ : Set X)) :=
    { toFun y := ⟨y, Set.mem_univ (f y)⟩
      invFun := Subtype.val
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let j : C(f ⁻¹' (Set.univ : Set X), Y) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : IsProperMap j :=
    ((isClosed_univ : IsClosed (Set.univ : Set X)).preimage
      f.continuous).isProperMap_subtypeVal
  have hw : (fun i ↦ compactSupportKZeroPullback ⟨d, d.continuous⟩ d.isProperMap
      (compactSupportKZeroPullback j hj (u i))) = u := by
    funext i
    rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
    change compactSupportKZeroPullback (ContinuousMap.id Y) isProperMap_id (u i) = u i
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  have h := transport n (preimageSubspaceMap Set.univ f) f e d (by rfl)
    (fun i ↦ compactSupportKZeroPullback j hj (u i)) (hglobal n)
  rw [hw] at h
  exact h

end AtiyahSinger
