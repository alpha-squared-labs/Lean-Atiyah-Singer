/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKMinusOneSuspension
public import AtiyahSinger.Topology.GradedKProduct
public import AtiyahSinger.Topology.GradedKProductNaturality
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Associativity, graded symmetry and units of the suspended K-product

Public module ID: M1871.

The indices m and n denote degrees -m and -n. The product retains the ordered
real suspension blocks of `suspendedProductHomeomorph`: the m coordinates
precede the n coordinates. Reindexing equal natural-number degrees is separate
from changing the base factors. Neither operation silently permutes coordinates.

The symmetry sign is (-1)^(m*n), since interchanging those two real blocks
performs m*n one-dimensional suspension interchanges. The point unit is the
original positive rank-one class, inserted into degree zero through the existing
empty-coordinate comparison. No Bott class or periodicity choice defines a unit.

Sources: Spin Geometry, Appendix C.1 (graded product), and the suspension
definition of negative K-groups. The sign argument uses the existing real
reflection theorem from Karoubi II.4.10. Its properly homotopic coordinate
rotation and block-permutation application below are a project supplement.
These statements concern locally compact Hausdorff bases, allowing empty bases
and zero degrees; they impose no compactness, connectedness or CW hypothesis.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y Z : Type*}
  [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [LocallyCompactSpace Y] [T2Space Y]
  [TopologicalSpace Z] [LocallyCompactSpace Z] [T2Space Z]

/-- Associativity preserves the three suspension blocks and uses the actual base associator. -/
theorem compactSupportKExternalProduct_assoc (m n p : ℕ)
    (a : CompactSupportK m X) (b : CompactSupportK n Y) (c : CompactSupportK p Z) :
    compactSupportKDegreeCongr (X × (Y × Z)) (Nat.add_assoc m n p)
        (compactSupportKHomeomorphEquiv ((m + n) + p) (Homeomorph.prodAssoc X Y Z)
          (compactSupportKExternalProduct (m + n) p
            (compactSupportKExternalProduct m n a b) c)) =
      compactSupportKExternalProduct m (n + p) a
        (compactSupportKExternalProduct n p b c) := by
  /- Stage 1: expand both products as the original degree-zero products on the
  suspended spaces. Apply their existing associativity and homeomorphism
  naturality to reassociate the three base factors without exchanging them.
  Stage 2: the two coordinate composites retain (x,y,z) and concatenate the
  m, n and p real blocks in that order. After the displayed Nat.add_assoc
  transport their coordinate functions agree on each of the three index ranges.
  Proper-pullback functoriality identifies the resulting compact-support maps.
  No suspension block is interchanged, so no sign or periodicity map appears. -/
  let S := Fin m → ℝ
  let T := Fin n → ℝ
  let U := Fin p → ℝ
  let eF := suspendedProductHomeomorph m n X Y
  let eL := suspendedProductHomeomorph (m + n) p (X × Y) Z
  let eG := suspendedProductHomeomorph n p Y Z
  let eR := suspendedProductHomeomorph m (n + p) X (Y × Z)
  let jF : C((X × Y) × (Fin (m + n) → ℝ), (X × S) × (Y × T)) :=
    ⟨eF.symm, eF.symm.continuous⟩
  let jL : C(((X × Y) × Z) × (Fin ((m + n) + p) → ℝ),
      ((X × Y) × (Fin (m + n) → ℝ)) × (Z × U)) :=
    ⟨eL.symm, eL.symm.continuous⟩
  let jG : C((Y × Z) × (Fin (n + p) → ℝ), (Y × T) × (Z × U)) :=
    ⟨eG.symm, eG.symm.continuous⟩
  let jR : C((X × (Y × Z)) × (Fin (m + (n + p)) → ℝ),
      (X × S) × ((Y × Z) × (Fin (n + p) → ℝ))) :=
    ⟨eR.symm, eR.symm.continuous⟩
  -- Equality of degrees transports the same tuple; it does not permute any block.
  have hdegree (i j : ℕ) (h : i = j) (d : CompactSupportK i (X × (Y × Z))) :
      compactSupportKDegreeCongr (X × (Y × Z)) h d = compactSupportKZeroHomeomorph
        ((Homeomorph.refl (X × (Y × Z))).prodCongr
          (Homeomorph.piCongrLeft (Y := fun _ : Fin j ↦ ℝ) (finCongr h))) d := by
    subst j
    simp only [finCongr_refl, Homeomorph.piCongrLeft_refl]
    change d = compactSupportKZeroPullback (ContinuousMap.id _) isProperMap_id d
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  let e := (Homeomorph.refl (X × (Y × Z))).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (m + (n + p)) ↦ ℝ)
      (finCongr (Nat.add_assoc m n p)))
  let J : C((X × (Y × Z)) × (Fin (m + (n + p)) → ℝ),
      (X × (Y × Z)) × (Fin ((m + n) + p) → ℝ)) := ⟨e.symm, e.symm.continuous⟩
  let d := (Homeomorph.prodAssoc X Y Z).prodCongr
    (Homeomorph.refl (Fin ((m + n) + p) → ℝ))
  let D : C((X × (Y × Z)) × (Fin ((m + n) + p) → ℝ),
      ((X × Y) × Z) × (Fin ((m + n) + p) → ℝ)) := ⟨d.symm, d.symm.continuous⟩
  let L := jF.prodMap (ContinuousMap.id (Z × U))
  let R := (ContinuousMap.id (X × S)).prodMap jG
  let A : C((X × S) × ((Y × T) × (Z × U)), ((X × S) × (Y × T)) × (Z × U)) :=
    ⟨(Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm,
      (Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm.continuous⟩
  have hL : IsProperMap L := eF.symm.isProperMap.prodMap isProperMap_id
  have hR : IsProperMap R := isProperMap_id.prodMap eG.symm.isProperMap
  have hA : IsProperMap A :=
    (Homeomorph.prodAssoc (X × S) (Y × T) (Z × U)).symm.isProperMap
  -- Move each inner product through its actual inverse-coordinate pullback.
  have hLP := compactSupportKZeroExternalProduct_properPullback
    jF eF.symm.isProperMap (ContinuousMap.id (Z × U)) isProperMap_id
    (compactSupportKZeroExternalProduct a b) c
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hLP
  have hRP := compactSupportKZeroExternalProduct_properPullback
    (ContinuousMap.id (X × S)) isProperMap_id jG eG.symm.isProperMap a
    (compactSupportKZeroExternalProduct b c)
  rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply] at hRP
  rw [hdegree]
  change compactSupportKZeroPullback J e.symm.isProperMap
      (compactSupportKZeroPullback D d.symm.isProperMap
        (compactSupportKZeroPullback jL eL.symm.isProperMap
          (compactSupportKZeroExternalProduct
            (compactSupportKZeroPullback jF eF.symm.isProperMap
              (compactSupportKZeroExternalProduct a b)) c))) =
    compactSupportKZeroPullback jR eR.symm.isProperMap
      (compactSupportKZeroExternalProduct a
        (compactSupportKZeroPullback jG eG.symm.isProperMap
          (compactSupportKZeroExternalProduct b c)))
  rw [← hLP, ← hRP, ← compactSupportKZeroExternalProduct_assoc a b c]
  let t := compactSupportKZeroExternalProduct (compactSupportKZeroExternalProduct a b) c
  have hsquare : L.comp (jL.comp (D.comp J)) = A.comp (R.comp jR) := by
    apply ContinuousMap.ext
    rintro ⟨⟨x, y, z⟩, s⟩
    refine Prod.ext (Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)) (Prod.ext rfl ?_)
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.castAdd p (Fin.castAdd n i))) =
        s (Fin.castAdd (n + p) i)
      rfl
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.castAdd p (Fin.natAdd m i))) =
        s (Fin.natAdd m (Fin.castAdd p i))
      rfl
    · funext i
      change s (Fin.cast (Nat.add_assoc m n p) (Fin.natAdd (m + n) i)) =
        s (Fin.natAdd m (Fin.natAdd n i))
      congr 1
      exact Fin.ext (Nat.add_assoc m n i.val)
  -- Both composites retain (x,y,z) and the same m-, n- and p-coordinates.
  calc
    _ = compactSupportKZeroPullback (L.comp (jL.comp (D.comp J)))
        (hL.comp (eL.symm.isProperMap.comp (d.symm.isProperMap.comp e.symm.isProperMap)))
          t := by
      rw [compactSupportKZeroPullback_comp (jL.comp (D.comp J)) L
          (eL.symm.isProperMap.comp (d.symm.isProperMap.comp e.symm.isProperMap)) hL,
        AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp (D.comp J) jL
          (d.symm.isProperMap.comp e.symm.isProperMap) eL.symm.isProperMap,
        AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp J D e.symm.isProperMap d.symm.isProperMap,
        AddMonoidHom.comp_apply]
    _ = compactSupportKZeroPullback (A.comp (R.comp jR))
        (hA.comp (hR.comp eR.symm.isProperMap)) t := by
      simp only [hsquare]
    _ = _ := by
      rw [compactSupportKZeroPullback_comp (R.comp jR) A
          (hR.comp eR.symm.isProperMap) hA, AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp jR R eR.symm.isProperMap hR,
        AddMonoidHom.comp_apply]
      rfl

open scoped unitInterval in
/-- Swapping the base factors gives the Koszul sign from the two ordered suspension blocks. -/
theorem compactSupportKExternalProduct_swap (m n : ℕ)
    (a : CompactSupportK m X) (b : CompactSupportK n Y) :
    compactSupportKDegreeCongr (Y × X) (Nat.add_comm m n)
        (compactSupportKHomeomorphEquiv (m + n) (Homeomorph.prodComm X Y)
          (compactSupportKExternalProduct m n a b)) =
      ((-1 : ℤ) ^ (m * n)) • compactSupportKExternalProduct n m b a := by
  /- Symmetry of the degree-zero product exchanges both suspended factors.
  The displayed base swap exchanges only the base points, so their difference
  after the degree cast is the literal permutation of the two real blocks.
  For a single transposition, reflect its first output coordinate to obtain
  the quarter-plane rotation. Karoubi II.4.10 makes that reflection act by
  negation, while the rotation acts trivially: its time-preserving cylinder
  homeomorphism and compact time interval give joint properness.
  Finite permutation induction therefore gives the sign of the actual block
  permutation. Identifying this block flip with powers of the cyclic rotation
  computes its sign as (-1)^(m*n). Combining the same coordinate transports
  gives the displayed formula, including empty blocks and bases. -/
  classical
  -- First construct a proper plane rotation with every base coordinate fixed.
  have plane_rotation {B : Type _} [TopologicalSpace B]
        [LocallyCompactSpace B] [T2Space B] (r : ℕ) (i j : Fin r) (hij : i ≠ j) :
      let V := B × (Fin r → ℝ)
      ∃ (f : C(V, V)) (hf : IsProperMap f),
        (∀ p : V, f p = (p.1, fun k ↦
          if k = i then -p.2 j else if k = j then p.2 i else p.2 k)) ∧
        compactSupportKZeroPullback f hf =
          AddMonoidHom.id (CompactSupportKZero V) := by
    classical
    dsimp only
    let c (t : I) : ℝ := Real.cos (Real.pi / 2 * (t : ℝ))
    let s (t : I) : ℝ := Real.sin (Real.pi / 2 * (t : ℝ))
    let R (t : I) (v : Fin r → ℝ) (k : Fin r) : ℝ :=
      if k = i then c t * v i - s t * v j
      else if k = j then s t * v i + c t * v j else v k
    let S (t : I) (v : Fin r → ℝ) (k : Fin r) : ℝ :=
      if k = i then c t * v i + s t * v j
      else if k = j then -s t * v i + c t * v j else v k
    have hcircle (t : I) : c t ^ 2 + s t ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq _
    have hRS (t : I) (v : Fin r → ℝ) : R t (S t v) = v := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [R, S, hij.symm]
        linear_combination (v i) * hcircle t
      · by_cases hkj : k = j
        · subst k
          simp [R, S, hij.symm]
          linear_combination (v j) * hcircle t
        · simp [R, S, hki, hkj]
    have hSR (t : I) (v : Fin r → ℝ) : S t (R t v) = v := by
      funext k
      by_cases hki : k = i
      · subst k
        simp [R, S, hij.symm]
        linear_combination (v i) * hcircle t
      · by_cases hkj : k = j
        · subst k
          simp [R, S, hij.symm]
          linear_combination (v j) * hcircle t
        · simp [R, S, hki, hkj]
    -- A time-preserving homeomorphism gives properness of the entire cylinder.
    let E : (I × (B × (Fin r → ℝ))) ≃ₜ (I × (B × (Fin r → ℝ))) :=
      { toFun := fun p ↦ (p.1, p.2.1, R p.1 p.2.2)
        invFun := fun p ↦ (p.1, p.2.1, S p.1 p.2.2)
        left_inv := fun p ↦ by simp only [hSR, Prod.eta]
        right_inv := fun p ↦ by simp only [hRS, Prod.eta]
        continuous_toFun := by
          apply continuous_fst.prodMk
          apply continuous_snd.fst.prodMk
          apply continuous_pi
          intro k
          dsimp only [R, c, s]
          split_ifs <;> fun_prop
        continuous_invFun := by
          apply continuous_fst.prodMk
          apply continuous_snd.fst.prodMk
          apply continuous_pi
          intro k
          dsimp only [S, c, s]
          split_ifs <;> fun_prop }
    let f : C(B × (Fin r → ℝ), B × (Fin r → ℝ)) :=
      ⟨fun p ↦ (p.1, fun k ↦
        if k = i then -p.2 j else if k = j then p.2 i else p.2 k), by
          apply continuous_fst.prodMk
          apply continuous_pi
          intro k
          split_ifs <;> fun_prop⟩
    let H : ContinuousMap.Homotopy (ContinuousMap.id (B × (Fin r → ℝ))) f :=
      { toFun := fun p ↦ (p.2.1, R p.1 p.2.2)
        continuous_toFun := continuous_snd.comp E.continuous
        map_zero_left := by
          intro p
          change (p.1, R 0 p.2) = (p.1, p.2)
          refine Prod.ext rfl ?_
          funext k
          dsimp only [R]
          split_ifs <;> subst_vars <;> simp [c, s]
        map_one_left := by
          intro p
          change (p.1, R 1 p.2) = (p.1, fun k ↦
            if k = i then -p.2 j else if k = j then p.2 i else p.2 k)
          refine Prod.ext rfl ?_
          funext k
          simp [R, c, s] }
    have hH : IsProperMap H :=
      isProperMap_snd_of_compactSpace.comp E.isProperMap
    have hf : IsProperMap f := by
      have h := isProperMap_homotopy_eval H hH 1
      simpa only [H.apply_one] using h
    refine ⟨f, hf, (fun _ ↦ rfl), ?_⟩
    have h := compactSupportKZeroPullback_eq_of_proper_homotopy isProperMap_id hf H hH
    rw [compactSupportKZeroPullback_id] at h
    exact h.symm
  -- Conjugate the already-proved real reflection through an actual coordinate split.
  have coordinate_reflection {B : Type _} [TopologicalSpace B]
        [LocallyCompactSpace B] [T2Space B] (r : ℕ) (i : Fin r) :
      ∃ (f : C(B × (Fin r → ℝ), B × (Fin r → ℝ))) (hf : IsProperMap f),
        (∀ p, f p = (p.1, fun k ↦ if k = i then -p.2 k else p.2 k)) ∧
        ∀ a, compactSupportKZeroPullback f hf a = -a := by
    classical
    let q : (B × (Fin r → ℝ)) ≃ₜ ((B × ({k : Fin r // k ≠ i} → ℝ)) × ℝ) :=
      { toFun := fun p ↦ ((p.1, fun k ↦ p.2 k), p.2 i)
        invFun := fun p ↦ (p.1.1, fun k ↦ if h : k = i then p.2 else p.1.2 ⟨k, h⟩)
        left_inv := by
          intro p
          refine Prod.ext rfl ?_
          funext k
          dsimp only
          split_ifs with h
          · exact congrArg p.2 h.symm
          · rfl
        right_inv := by
          intro p
          refine Prod.ext (Prod.ext rfl ?_) ?_
          · funext k
            simp only [dite_eq_right k.property]
          · simp
        continuous_toFun := by fun_prop
        continuous_invFun := by
          apply continuous_fst.fst.prodMk
          apply continuous_pi
          intro k
          split_ifs <;> fun_prop }
    let e := (Homeomorph.refl (B × ({k : Fin r // k ≠ i} → ℝ))).prodCongr
      (Homeomorph.neg ℝ)
    let P : C(B × (Fin r → ℝ), (B × ({k : Fin r // k ≠ i} → ℝ)) × ℝ) :=
      ⟨q, q.continuous⟩
    let Q : C((B × ({k : Fin r // k ≠ i} → ℝ)) × ℝ, B × (Fin r → ℝ)) :=
      ⟨q.symm, q.symm.continuous⟩
    let N : C((B × ({k : Fin r // k ≠ i} → ℝ)) × ℝ,
        (B × ({k : Fin r // k ≠ i} → ℝ)) × ℝ) := ⟨e, e.continuous⟩
    let f := Q.comp (N.comp P)
    have hf : IsProperMap f := q.symm.isProperMap.comp (e.isProperMap.comp q.isProperMap)
    have hQP : Q.comp P = ContinuousMap.id (B × (Fin r → ℝ)) := by
      apply ContinuousMap.ext
      exact q.symm_apply_apply
    have hcancel (a : CompactSupportKZero (B × (Fin r → ℝ))) :
        compactSupportKZeroPullback P q.isProperMap
          (compactSupportKZeroPullback Q q.symm.isProperMap a) = a := by
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      simp only [hQP, compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
    refine ⟨f, hf, ?_, ?_⟩
    · intro p
      apply q.injective
      change q (q.symm (e (q p))) = q (p.1, fun k ↦ if k = i then -p.2 k else p.2 k)
      rw [q.apply_symm_apply]
      refine Prod.ext (Prod.ext rfl ?_) ?_
      · funext k
        exact (ite_eq_right k.property).symm
      · change -p.2 i = if i = i then -p.2 i else p.2 i
        simp
    · intro a
      change compactSupportKZeroPullback (Q.comp (N.comp P)) hf a = -a
      rw [compactSupportKZeroPullback_comp (N.comp P) Q
          (e.isProperMap.comp q.isProperMap) q.symm.isProperMap,
        AddMonoidHom.comp_apply, compactSupportKZeroPullback_comp P N
          q.isProperMap e.isProperMap, AddMonoidHom.comp_apply]
      have hN := compactSupportKZeroPullback_realReflection
        (B × ({k : Fin r // k ≠ i} → ℝ))
        (compactSupportKZeroPullback Q q.symm.isProperMap a)
      change compactSupportKZeroPullback N e.isProperMap
        (compactSupportKZeroPullback Q q.symm.isProperMap a) = _ at hN
      rw [hN, map_neg, hcancel]
  -- Reflecting the first output of a transposition gives the proper plane rotation.
  have swap_action {B : Type _} [TopologicalSpace B]
        [LocallyCompactSpace B] [T2Space B] (r : ℕ) (i j : Fin r) (hij : i ≠ j)
      (a : CompactSupportKZero (B × (Fin r → ℝ))) :
      let e := (Homeomorph.refl B).prodCongr
        (Homeomorph.piCongrLeft (Y := fun _ : Fin r ↦ ℝ) (Equiv.swap i j))
      compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap a = -a := by
    classical
    let e := (Homeomorph.refl B).prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : Fin r ↦ ℝ) (Equiv.swap i j))
    let G : C(B × (Fin r → ℝ), B × (Fin r → ℝ)) := ⟨e, e.continuous⟩
    obtain ⟨R, hR, hRformula, hRlaw⟩ := plane_rotation (B := B) r i j hij
    obtain ⟨N, hN, hNformula, hNlaw⟩ := coordinate_reflection (B := B) r i
    have hfactor : N.comp G = R := by
      apply ContinuousMap.ext
      intro p
      rw [ContinuousMap.comp_apply, hNformula, hRformula]
      refine Prod.ext rfl ?_
      funext k
      by_cases hki : k = i
      · subst k
        simp [G, e, Homeomorph.piCongrLeft, Equiv.piCongrLeft]
      · by_cases hkj : k = j
        · subst k
          simp [G, e, Homeomorph.piCongrLeft, Equiv.piCongrLeft, hki]
        · have hs : Equiv.swap i j k = k := Equiv.swap_apply_of_ne_of_ne hki hkj
          simp [G, e, Homeomorph.piCongrLeft, Equiv.piCongrLeft, hki, hkj, hs]
    have hid : compactSupportKZeroPullback G e.isProperMap
        (compactSupportKZeroPullback N hN a) = a := by
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      have h := DFunLike.congr_fun hRlaw a
      simpa only [hfactor, AddMonoidHom.id_apply] using h
    rw [hNlaw, map_neg] at hid
    exact neg_eq_iff_eq_neg.mp hid
  -- Finite permutation induction computes pullback on the original suspension.
  have permutation_action {B : Type _} [TopologicalSpace B]
        [LocallyCompactSpace B] [T2Space B] (r : ℕ) (p : Equiv.Perm (Fin r))
      (a : CompactSupportKZero (B × (Fin r → ℝ))) :
      let e := (Homeomorph.refl B).prodCongr
        (Homeomorph.piCongrLeft (Y := fun _ : Fin r ↦ ℝ) p.symm)
      compactSupportKZeroPullback ⟨e, e.continuous⟩ e.isProperMap a =
        ((p.sign : ℤˣ) : ℤ) • a := by
    classical
    let E (p : Equiv.Perm (Fin r)) := (Homeomorph.refl B).prodCongr
      (Homeomorph.piCongrLeft (Y := fun _ : Fin r ↦ ℝ) p.symm)
    let G (p : Equiv.Perm (Fin r)) : C(B × (Fin r → ℝ), B × (Fin r → ℝ)) :=
      ⟨E p, (E p).continuous⟩
    have law (p : Equiv.Perm (Fin r)) :
        ∀ a, compactSupportKZeroPullback (G p) (E p).isProperMap a =
          ((p.sign : ℤˣ) : ℤ) • a := by
      induction p using Equiv.Perm.swap_induction_on with
      | one =>
        intro a
        have hG : G 1 = ContinuousMap.id (B × (Fin r → ℝ)) := by
          apply ContinuousMap.ext
          intro z
          rfl
        simp only [hG, compactSupportKZeroPullback_id, AddMonoidHom.id_apply,
          map_one, Units.val_one, one_zsmul]
      | swap_mul p i j hij ih =>
        intro a
        have hsquare : G (Equiv.swap i j * p) = (G p).comp (G (Equiv.swap i j)) := by
          apply ContinuousMap.ext
          intro z
          refine Prod.ext rfl ?_
          funext k
          simp [G, E, Homeomorph.piCongrLeft, Equiv.piCongrLeft, Equiv.Perm.mul_apply]
        have hswap (b : CompactSupportKZero (B × (Fin r → ℝ))) :
            compactSupportKZeroPullback (G (Equiv.swap i j))
              (E (Equiv.swap i j)).isProperMap b = -b := by
          simpa only [G, E, Equiv.symm_swap] using swap_action (B := B) r i j hij b
        calc
          _ = compactSupportKZeroPullback (G (Equiv.swap i j))
              (E (Equiv.swap i j)).isProperMap
                (compactSupportKZeroPullback (G p) (E p).isProperMap a) := by
            simpa only [hsquare, AddMonoidHom.comp_apply] using congrArg (fun F ↦ F a)
              (compactSupportKZeroPullback_comp (G (Equiv.swap i j)) (G p)
                (E (Equiv.swap i j)).isProperMap (E p).isProperMap)
          _ = ((p.sign : ℤˣ) : ℤ) • (-a) := by rw [ih, map_zsmul, hswap]
          _ = _ := by
            simp only [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
              Units.val_neg, neg_one_mul, neg_zsmul, smul_neg]
    exact law p a
  -- Keep the block permutation literal, including empty blocks.
  have rotate_pow_val (N k : ℕ) (i : Fin N) :
      (((finRotate N) ^ k) i).val = (i.val + k) % N := by
    have := i.neZero
    induction k with
    | zero => simp [Nat.mod_eq_of_lt i.isLt]
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih]
      change (((i.val + k) % N + 1 % N) % N) = (i.val + (k + 1)) % N
      rw [← Nat.add_mod, Nat.add_assoc]
  -- Repeated rotation identifies the specified block permutation.
  have block_swap_eq_rotate_pow (m n : ℕ) :
      finAddFlip.trans (finCongr (Nat.add_comm n m)) = (finRotate (m + n)) ^ n := by
    ext ⟨i, hi⟩
    change (finAddFlip (⟨i, hi⟩ : Fin (m + n))).val =
      (((finRotate (m + n)) ^ n) ⟨i, hi⟩).val
    rw [rotate_pow_val]
    by_cases him : i < m
    · rw [finAddFlip_apply_mk_left him]
      change n + i = (i + n) % (m + n)
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [finAddFlip_apply_mk_right (by omega) hi]
      change i - m = (i + n) % (m + n)
      have heq : i + n = (i - m) + (m + n) := by omega
      rw [heq, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  -- Its sign counts the crossings of the two ordered real blocks.
  have sign_block_swap (m n : ℕ) :
      Equiv.Perm.sign (finAddFlip.trans (finCongr (Nat.add_comm n m))) =
        (-1 : ℤˣ) ^ (m * n) := by
    rw [block_swap_eq_rotate_pow, map_pow, sign_finRotate, ← pow_mul]
    cases n with
    | zero => simp
    | succ k =>
      have hlen : m + (k + 1) - 1 = m + k := by omega
      rw [hlen, Nat.add_mul, pow_add,
        (Nat.even_mul_succ_self k).neg_one_pow, mul_one]
  -- Finally compare the original degree cast, base swap and product transports.
  let S := Fin m → ℝ
  let T := Fin n → ℝ
  let eF := suspendedProductHomeomorph m n X Y
  let eN := suspendedProductHomeomorph n m Y X
  let jF : C((X × Y) × (Fin (m + n) → ℝ), (X × S) × (Y × T)) :=
    ⟨eF.symm, eF.symm.continuous⟩
  let jN : C((Y × X) × (Fin (n + m) → ℝ), (Y × T) × (X × S)) :=
    ⟨eN.symm, eN.symm.continuous⟩
  have hdegree (i j : ℕ) (h : i = j) (c : CompactSupportK i (Y × X)) :
      compactSupportKDegreeCongr (Y × X) h c = compactSupportKZeroHomeomorph
        ((Homeomorph.refl (Y × X)).prodCongr
          (Homeomorph.piCongrLeft (Y := fun _ : Fin j ↦ ℝ) (finCongr h))) c := by
    subst j
    simp only [finCongr_refl, Homeomorph.piCongrLeft_refl]
    change c = compactSupportKZeroPullback (ContinuousMap.id _) isProperMap_id c
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  let eD := (Homeomorph.refl (Y × X)).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n + m) ↦ ℝ)
      (finCongr (Nat.add_comm m n)))
  let J : C((Y × X) × (Fin (n + m) → ℝ), (Y × X) × (Fin (m + n) → ℝ)) :=
    ⟨eD.symm, eD.symm.continuous⟩
  let eB := (Homeomorph.prodComm X Y).prodCongr
    (Homeomorph.refl (Fin (m + n) → ℝ))
  let D : C((Y × X) × (Fin (m + n) → ℝ), (X × Y) × (Fin (m + n) → ℝ)) :=
    ⟨eB.symm, eB.symm.continuous⟩
  let p : Equiv.Perm (Fin (n + m)) :=
    finAddFlip.trans (finCongr (Nat.add_comm m n))
  let eG := (Homeomorph.refl (Y × X)).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ : Fin (n + m) ↦ ℝ) p.symm)
  let G : C((Y × X) × (Fin (n + m) → ℝ), (Y × X) × (Fin (n + m) → ℝ)) :=
    ⟨eG, eG.continuous⟩
  let eA := Homeomorph.prodComm (X × S) (Y × T)
  let A : C((Y × T) × (X × S), (X × S) × (Y × T)) :=
    ⟨eA.symm, eA.symm.continuous⟩
  have hswap := compactSupportKZeroExternalProduct_swap a b
  change compactSupportKZeroPullback A eA.symm.isProperMap
    (compactSupportKZeroExternalProduct a b) = compactSupportKZeroExternalProduct b a
      at hswap
  have hGformula (z : (Y × X) × (Fin (n + m) → ℝ)) :
      G z = (z.1, fun k ↦ z.2 (p k)) := by
    simp [G, eG, Homeomorph.piCongrLeft, Equiv.piCongrLeft]
    rfl
  have hsquare : jF.comp (D.comp J) = A.comp (jN.comp G) := by
    apply ContinuousMap.ext
    rintro ⟨⟨y, x⟩, s⟩
    change eF.symm (eB.symm (eD.symm ((y, x), s))) = eA.symm (eN.symm (G ((y, x), s)))
    rw [hGformula]
    refine Prod.ext (Prod.ext rfl ?_) (Prod.ext rfl ?_)
    · funext i
      change s (Fin.cast (Nat.add_comm m n) (Fin.castAdd n i)) =
        s (p (Fin.natAdd n i))
      simp only [p, Equiv.trans_apply, finAddFlip_apply_natAdd]
      rfl
    · funext i
      change s (Fin.cast (Nat.add_comm m n) (Fin.natAdd m i)) =
        s (p (Fin.castAdd m i))
      simp only [p, Equiv.trans_apply, finAddFlip_apply_castAdd]
      rfl
  have hsign : ((p.sign : ℤˣ) : ℤ) = (-1 : ℤ) ^ (m * n) := by
    have h := congrArg (fun z : ℤˣ ↦ (z : ℤ)) (sign_block_swap n m)
    simpa only [p, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Nat.mul_comm n m] using h
  rw [hdegree]
  change compactSupportKZeroPullback J eD.symm.isProperMap
      (compactSupportKZeroPullback D eB.symm.isProperMap
        (compactSupportKZeroPullback jF eF.symm.isProperMap
          (compactSupportKZeroExternalProduct a b))) = _
  calc
    _ = compactSupportKZeroPullback (jF.comp (D.comp J))
        (eF.symm.isProperMap.comp (eB.symm.isProperMap.comp eD.symm.isProperMap))
          (compactSupportKZeroExternalProduct a b) := by
      rw [compactSupportKZeroPullback_comp (D.comp J) jF
          (eB.symm.isProperMap.comp eD.symm.isProperMap) eF.symm.isProperMap,
        AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp J D eD.symm.isProperMap eB.symm.isProperMap,
        AddMonoidHom.comp_apply]
    _ = compactSupportKZeroPullback (A.comp (jN.comp G))
        (eA.symm.isProperMap.comp (eN.symm.isProperMap.comp eG.isProperMap))
          (compactSupportKZeroExternalProduct a b) := by
      simp only [hsquare]
    _ = compactSupportKZeroPullback G eG.isProperMap
        (compactSupportKZeroPullback jN eN.symm.isProperMap
          (compactSupportKZeroExternalProduct b a)) := by
      rw [compactSupportKZeroPullback_comp (jN.comp G) A
          (eN.symm.isProperMap.comp eG.isProperMap) eA.symm.isProperMap,
        AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp G jN eG.isProperMap eN.symm.isProperMap,
        AddMonoidHom.comp_apply, hswap]
    _ = _ := by
      rw [permutation_action (B := Y × X) (n + m) p, hsign]
      rfl

/-- Removing both empty coordinate blocks recovers exactly the original degree-zero product. -/
theorem compactSupportKZeroDegreeEquiv_externalProduct
    (a : CompactSupportK 0 X) (b : CompactSupportK 0 Y) :
    compactSupportKZeroDegreeEquiv (X × Y) (compactSupportKExternalProduct 0 0 a b) =
      compactSupportKZeroExternalProduct
        (compactSupportKZeroDegreeEquiv X a) (compactSupportKZeroDegreeEquiv Y b) := by
  /- Stage 1: both suspension factors are the unique empty real tuple. The
  product homeomorphism sends ((x,()),(y,())) to ((x,y),()), so deleting its
  empty coordinate is the product of the original two coordinate projections.
  Stage 2: apply homeomorphism naturality of the specified degree-zero product.
  Its three transports are exactly the existing degree-zero comparison maps. -/
  let eX := Homeomorph.prodUnique X (Fin 0 → ℝ)
  let eY := Homeomorph.prodUnique Y (Fin 0 → ℝ)
  let eXY := Homeomorph.prodUnique (X × Y) (Fin 0 → ℝ)
  let eP := suspendedProductHomeomorph 0 0 X Y
  let j : C((X × Y) × (Fin 0 → ℝ), (X × (Fin 0 → ℝ)) × (Y × (Fin 0 → ℝ))) :=
    ⟨eP.symm, eP.symm.continuous⟩
  let q : C(X × Y, (X × Y) × (Fin 0 → ℝ)) := ⟨eXY.symm, eXY.symm.continuous⟩
  let r : C(X × Y, (X × (Fin 0 → ℝ)) × (Y × (Fin 0 → ℝ))) :=
    ⟨(eX.prodCongr eY).symm, (eX.prodCongr eY).symm.continuous⟩
  have hp := compactSupportKZeroExternalProduct_homeomorph eX eY a b
  -- Both actual inverses insert only the two unique empty tuples.
  have hsquare : j.comp q = r := by
    apply ContinuousMap.ext
    rintro ⟨x, y⟩
    exact Prod.ext (Prod.ext rfl (Subsingleton.elim _ _))
      (Prod.ext rfl (Subsingleton.elim _ _))
  change _ = compactSupportKZeroExternalProduct (compactSupportKZeroHomeomorph eX a)
    (compactSupportKZeroHomeomorph eY b)
  rw [← hp]
  change compactSupportKZeroPullback q eXY.symm.isProperMap
      (compactSupportKZeroPullback j eP.symm.isProperMap
        (compactSupportKZeroExternalProduct a b)) =
    compactSupportKZeroPullback r (eX.prodCongr eY).symm.isProperMap
      (compactSupportKZeroExternalProduct a b)
  rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
  simp only [hsquare]

/-- The original positive point class is a left unit in every suspended degree. -/
theorem compactSupportKExternalProduct_one_left (n : ℕ) (a : CompactSupportK n X) :
    compactSupportKDegreeCongr X (Nat.zero_add n)
        (compactSupportKHomeomorphEquiv (0 + n) (Homeomorph.uniqueProd PUnit.{1} X)
          (compactSupportKExternalProduct 0 n
            ((compactSupportKZeroDegreeEquiv PUnit.{1}).symm compactSupportKZeroPointOne) a)) =
      a := by
  /- Stage 1: the degree-zero comparison inserts the unique empty coordinate
  into the original positive rank-one point class. The external product keeps
  that empty block before the original n coordinates of a.
  Stage 2: the actual projection from point times X, followed by the displayed
  degree identification, deletes only the point and the empty block. Apply
  the existing left unit law to X times its original real n-space. The same
  coordinates and compact supports remain, so the resulting class is a. -/
  let V := X × (Fin n → ℝ)
  let e0 := Homeomorph.prodUnique PUnit.{1} (Fin 0 → ℝ)
  let b := (compactSupportKZeroDegreeEquiv PUnit.{1}).symm compactSupportKZeroPointOne
  have hb : compactSupportKZeroHomeomorph e0 b = compactSupportKZeroPointOne :=
    (compactSupportKZeroDegreeEquiv PUnit.{1}).apply_symm_apply compactSupportKZeroPointOne
  have hid : compactSupportKZeroHomeomorph (Homeomorph.refl V) a = a := by
    change compactSupportKZeroPullback (ContinuousMap.id V) isProperMap_id a = a
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  have hp := compactSupportKZeroExternalProduct_homeomorph e0 (Homeomorph.refl V) b a
  rw [hb, hid] at hp
  -- Identify equality-of-degree transport with its actual unchanged-coordinate map.
  have hdegree (i j : ℕ) (h : i = j) (c : CompactSupportK i X) :
      compactSupportKDegreeCongr X h c = compactSupportKZeroHomeomorph
        ((Homeomorph.refl X).prodCongr
          (Homeomorph.piCongrLeft (Y := fun _ : Fin j ↦ ℝ) (finCongr h))) c := by
    subst j
    simp only [finCongr_refl, Homeomorph.piCongrLeft_refl]
    change c = compactSupportKZeroPullback (ContinuousMap.id _) isProperMap_id c
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  let e := (Homeomorph.refl X).prodCongr
    (Homeomorph.piCongrLeft (Y := fun _ : Fin n ↦ ℝ) (finCongr (Nat.zero_add n)))
  let J : C(V, X × (Fin (0 + n) → ℝ)) := ⟨e.symm, e.symm.continuous⟩
  let d := (Homeomorph.uniqueProd PUnit.{1} X).prodCongr
    (Homeomorph.refl (Fin (0 + n) → ℝ))
  let D : C(X × (Fin (0 + n) → ℝ), (PUnit.{1} × X) × (Fin (0 + n) → ℝ)) :=
    ⟨d.symm, d.symm.continuous⟩
  let eP := suspendedProductHomeomorph 0 n PUnit.{1} X
  let j : C((PUnit.{1} × X) × (Fin (0 + n) → ℝ), (PUnit.{1} × (Fin 0 → ℝ)) × V) :=
    ⟨eP.symm, eP.symm.continuous⟩
  let u := Homeomorph.uniqueProd PUnit.{1} V
  let q : C(V, PUnit.{1} × V) := ⟨u.symm, u.symm.continuous⟩
  let r : C(PUnit.{1} × V, (PUnit.{1} × (Fin 0 → ℝ)) × V) :=
    ⟨(e0.prodCongr (Homeomorph.refl V)).symm,
      (e0.prodCongr (Homeomorph.refl V)).symm.continuous⟩
  have hsquare : j.comp (D.comp J) = r.comp q := by
    apply ContinuousMap.ext
    rintro ⟨x, s⟩
    refine Prod.ext (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
      (Prod.ext rfl ?_)
    funext i
    change s (Fin.cast (Nat.zero_add n) (Fin.natAdd 0 i)) = s i
    congr 1
    exact Fin.ext (Nat.zero_add i.val)
  rw [hdegree]
  change compactSupportKZeroPullback J e.symm.isProperMap
      (compactSupportKZeroPullback D d.symm.isProperMap
        (compactSupportKZeroPullback j eP.symm.isProperMap
          (compactSupportKZeroExternalProduct b a))) = a
  -- The resulting map is the same point projection on the original suspended base V.
  calc
    _ = compactSupportKZeroPullback (j.comp (D.comp J))
        (eP.symm.isProperMap.comp (d.symm.isProperMap.comp e.symm.isProperMap))
          (compactSupportKZeroExternalProduct b a) := by
      rw [compactSupportKZeroPullback_comp (D.comp J) j
          (d.symm.isProperMap.comp e.symm.isProperMap) eP.symm.isProperMap,
        AddMonoidHom.comp_apply,
        compactSupportKZeroPullback_comp J D e.symm.isProperMap d.symm.isProperMap,
        AddMonoidHom.comp_apply]
    _ = compactSupportKZeroPullback (r.comp q)
        ((e0.prodCongr (Homeomorph.refl V)).symm.isProperMap.comp u.symm.isProperMap)
          (compactSupportKZeroExternalProduct b a) := by
      simp only [hsquare]
    _ = compactSupportKZeroPullback q u.symm.isProperMap
        (compactSupportKZeroHomeomorph (e0.prodCongr (Homeomorph.refl V))
          (compactSupportKZeroExternalProduct b a)) := by
      rw [compactSupportKZeroPullback_comp q r
        u.symm.isProperMap (e0.prodCongr (Homeomorph.refl V)).symm.isProperMap]
      rfl
    _ = a := by
      rw [hp]
      exact compactSupportKZeroExternalProduct_one_left a

/-- The original positive point class is a right unit in every suspended degree. -/
theorem compactSupportKExternalProduct_one_right (n : ℕ) (a : CompactSupportK n X) :
    compactSupportKDegreeCongr X (Nat.add_zero n)
        (compactSupportKHomeomorphEquiv (n + 0) (Homeomorph.prodUnique X PUnit.{1})
          (compactSupportKExternalProduct n 0 a
            ((compactSupportKZeroDegreeEquiv PUnit.{1}).symm compactSupportKZeroPointOne))) =
      a := by
  /- Stage 1: insert the empty suspension tuple into the same positive point
  class. The product appends this empty block after the n coordinates of a.
  Stage 2: the specified right projection removes the point, and Nat.add_zero
  retains each original real coordinate. The degree-zero right unit law on
  X times real n-space gives the claimed equality for this actual transport. -/
  let V := X × (Fin n → ℝ)
  let e0 := Homeomorph.prodUnique PUnit.{1} (Fin 0 → ℝ)
  let b := (compactSupportKZeroDegreeEquiv PUnit.{1}).symm compactSupportKZeroPointOne
  have hb : compactSupportKZeroHomeomorph e0 b = compactSupportKZeroPointOne :=
    (compactSupportKZeroDegreeEquiv PUnit.{1}).apply_symm_apply compactSupportKZeroPointOne
  have hid : compactSupportKZeroHomeomorph (Homeomorph.refl V) a = a := by
    change compactSupportKZeroPullback (ContinuousMap.id V) isProperMap_id a = a
    rw [compactSupportKZeroPullback_id, AddMonoidHom.id_apply]
  have hp := compactSupportKZeroExternalProduct_homeomorph (Homeomorph.refl V) e0 a b
  rw [hid, hb] at hp
  let d := (Homeomorph.prodUnique X PUnit.{1}).prodCongr
    (Homeomorph.refl (Fin n → ℝ))
  let D : C(V, (X × PUnit.{1}) × (Fin n → ℝ)) := ⟨d.symm, d.symm.continuous⟩
  let eP := suspendedProductHomeomorph n 0 X PUnit.{1}
  let j : C((X × PUnit.{1}) × (Fin n → ℝ), V × (PUnit.{1} × (Fin 0 → ℝ))) :=
    ⟨eP.symm, eP.symm.continuous⟩
  let u := Homeomorph.prodUnique V PUnit.{1}
  let q : C(V, V × PUnit.{1}) := ⟨u.symm, u.symm.continuous⟩
  let r : C(V × PUnit.{1}, V × (PUnit.{1} × (Fin 0 → ℝ))) :=
    ⟨((Homeomorph.refl V).prodCongr e0).symm,
      ((Homeomorph.refl V).prodCongr e0).symm.continuous⟩
  -- Right projection removes only the same point and the unique appended empty block.
  have hsquare : j.comp D = r.comp q := by
    apply ContinuousMap.ext
    rintro ⟨x, s⟩
    exact Prod.ext (Prod.ext rfl rfl)
      (Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _))
  change compactSupportKZeroPullback D d.symm.isProperMap
      (compactSupportKZeroPullback j eP.symm.isProperMap
        (compactSupportKZeroExternalProduct a b)) = a
  calc
    _ = compactSupportKZeroPullback (j.comp D)
        (eP.symm.isProperMap.comp d.symm.isProperMap)
          (compactSupportKZeroExternalProduct a b) := by
      rw [compactSupportKZeroPullback_comp D j d.symm.isProperMap eP.symm.isProperMap,
        AddMonoidHom.comp_apply]
    _ = compactSupportKZeroPullback (r.comp q)
        (((Homeomorph.refl V).prodCongr e0).symm.isProperMap.comp u.symm.isProperMap)
          (compactSupportKZeroExternalProduct a b) := by
      simp only [hsquare]
    _ = compactSupportKZeroPullback q u.symm.isProperMap
        (compactSupportKZeroHomeomorph ((Homeomorph.refl V).prodCongr e0)
          (compactSupportKZeroExternalProduct a b)) := by
      rw [compactSupportKZeroPullback_comp q r
        u.symm.isProperMap ((Homeomorph.refl V).prodCongr e0).symm.isProperMap]
      rfl
    _ = a := by
      rw [hp]
      exact compactSupportKZeroExternalProduct_one_right a

end AtiyahSinger
