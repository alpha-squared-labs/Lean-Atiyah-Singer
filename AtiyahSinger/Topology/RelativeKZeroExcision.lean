/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeKZero

/-!
# Relative homotopy, retractions and excision

Public module ID: M2081.

The maps here are the actual quotient-induced pullbacks already defined.
Compact Hausdorff closed pairs suffice for the stated excision and exactness
interfaces. We do not assert that the forgetful map is injective for all pairs.
Sources: SG I.9; Karoubi II.2.29–2.35 and its quotient proof. Triple comparison,
higher groups, products and the long exact sequence are outside this module.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

open scoped unitInterval

attribute [local instance] PointedQuotient.compactSpace

-- Local compactness of the interval suffices for homotopy descent through the quotient.
set_option linter.unusedVariables false in
/-- A homotopy through maps of compact pairs descends to their quotients. -/
theorem PointedQuotient.nonempty_map_homotopy [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (f g : C(X, Y))
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t : I, ∀ x ∈ A, H (t, x) ∈ B) :
    Nonempty (ContinuousMap.Homotopy (PointedQuotient.mapContinuous A B f hf)
      (PointedQuotient.mapContinuous A B g hg)) := by
  /- On the interval times the pointed sum use H on X and the constant base
  point on the added point. The pair condition makes this constant on each
  collapse class at each time. The product of the quotient map with the locally
  compact interval is a quotient map; descend the continuous cylinder map. -/
  let F (t : I) := PointedQuotient.mapContinuous A B (H.curry t) (hH t)
  refine ⟨{
    toFun := fun p ↦ F p.1 p.2
    continuous_toFun := ?_
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · -- On the pointed representatives the joint map is H followed by the original quotient.
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hc : Continuous (Sum.elim
        (fun p : I × X ↦ PointedQuotient.of B (H p))
        (fun _ : I × PUnit ↦ PointedQuotient.basepoint B)) :=
      ((PointedQuotient.continuous_of B).comp H.continuous).sumElim continuous_const
    convert hc.comp (Homeomorph.prodSumDistrib
      (X := I) (Y := X) (Z := PUnit)).continuous using 1
    funext p
    rcases p with ⟨t, z⟩
    cases z <;> rfl
  · -- The zero endpoint descends the given f, including at the added base point.
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => exact congrArg (PointedQuotient.of B) (H.apply_zero x)
      | inr p => rfl
  · -- The one endpoint descends the given g on those same representatives.
    intro z
    induction z using Quotient.inductionOn with
    | h z =>
      cases z with
      | inl x => exact congrArg (PointedQuotient.of B) (H.apply_one x)
      | inr p => rfl

/-- Homotopic maps of pairs induce equal relative pullbacks. -/
theorem relativeKZeroPullback_eq_of_homotopy [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (f g : C(X, Y))
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g A B)
    (H : ContinuousMap.Homotopy f g) (hH : ∀ t : I, ∀ x ∈ A, H (t, x) ∈ B) :
    relativeKZeroPullback A hA B hB f hf = relativeKZeroPullback A hA B hB g hg := by
  /- Apply absolute K⁰ homotopy invariance to the descended quotient homotopy.
  Both endpoint maps preserve the quotient base point, so their equal absolute
  pullbacks restrict to equal maps on the evaluation kernels. -/
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  obtain ⟨K⟩ := PointedQuotient.nonempty_map_homotopy A hA B hB f g hf hg H hH
  have heq := complexKZeroPullback_eq_of_homotopy
    (PointedQuotient.mapContinuous A B f hf) (PointedQuotient.mapContinuous A B g hg) K
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  exact DFunLike.congr_fun heq a.val

/-- Enlarging the relative subspace gives the canonical map of relative groups. -/
def relativeKZeroEnlarge [CompactSpace X] [T2Space X]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (h : A ⊆ B) :
    RelativeKZero B hB →+ RelativeKZero A hA :=
  relativeKZeroPullback A hA B hB (ContinuousMap.id X) h

/-- The change of relative subspace commutes with forgetting. -/
theorem relativeKZeroForget_enlarge [CompactSpace X] [T2Space X]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (h : A ⊆ B) :
    (relativeKZeroForget A hA).comp (relativeKZeroEnlarge A B hA hB h) =
      relativeKZeroForget B hB := by
  /- Use naturality of the forgetful map for the identity map of X viewed as
  a map from (X,A) to (X,B). Absolute pullback along the identity contributes no change. -/
  calc
    _ = (complexKZeroPullback (ContinuousMap.id X)).comp (relativeKZeroForget B hB) :=
      relativeKZeroForget_natural A hA B hB (ContinuousMap.id X) h
    _ = relativeKZeroForget B hB := by
      change (kZeroMap (RingHom.id _)).comp (relativeKZeroForget B hB) = _
      rw [kZeroMap_id]
      rfl

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix in
/-- If A is a retract, relative forgetting is injective. -/
theorem relativeKZeroForget_injective_of_retraction [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (r : C(X, A)) (hr : ∀ a : A, r a = a) :
    Function.Injective (relativeKZeroForget A hA) := by
  /- Represent a reduced quotient class as a bundle minus a trivial bundle,
  using a finite complement. If its pullback to X is zero, stabilize to obtain
  a trivialization there. Along A it differs from the fixed basepoint
  trivialization by a family of matrices. Pull that family back along r and
  correct the global trivialization, making it constant on A. It then descends
  to the pointed quotient, proving the original class zero. This direct descent
  argument does not use the later triple comparison; the retraction is essential. -/
  classical
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  let Z := PointedQuotient A
  let : CompactSpace Z := PointedQuotient.compactSpace A
  let : T2Space Z := PointedQuotient.t2Space A hA
  let ev := (ContinuousMap.evalAlgHom ℂ ℂ (PointedQuotient.basepoint A : Z)).toRingHom
  by_cases hX : Nonempty X
  · let x₀ : X := Classical.choice hX
    let a₀ : A := r x₀
    have hcollapse (x : A) : PointedQuotient.of A x = (PointedQuotient.basepoint A : Z) :=
      (PointedQuotient.of_eq_basepoint_iff A x).2 x.property
    have hsurj : Function.Surjective (PointedQuotient.of A : X → Z) := by
      intro z
      rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩
      · exact ⟨a₀.val, hcollapse a₀⟩
      · exact ⟨x, rfl⟩
    -- Stabilize the same pulled-back class, with one common free summand.
    obtain ⟨p, n, hp⟩ := ComplexBundle.exists_class_sub_trivial a.val
    rw [ComplexBundle.kZeroClass_image, ComplexBundle.kZeroClass_trivial] at hp
    let q := IdempotentMatrix.identity C(Z, ℂ) n
    let ψ := (ContinuousMap.compRightAlgHom ℂ ℂ
      (⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩ : C(X, Z))).toRingHom
    have hclass : kZeroClass C(X, ℂ) (p.map ψ) = kZeroClass C(X, ℂ) (q.map ψ) := by
      change kZeroMap ψ a.val = 0 at ha
      rw [hp, map_sub, kZeroMap_class, kZeroMap_class, sub_eq_zero] at ha
      exact ha
    obtain ⟨m, he⟩ :=
      IdempotentMatrix.exists_isEquivalent_stabilization_of_kZeroClass_eq
        (p.map ψ) (q.map ψ) hclass
    let P := p.blockSum (IdempotentMatrix.identity C(Z, ℂ) m)
    let Q := q.blockSum (IdempotentMatrix.identity C(Z, ℂ) m)
    have hmapblock (v w : IdempotentMatrix C(Z, ℂ)) :
        (v.blockSum w).map ψ = (v.map ψ).blockSum (w.map ψ) := by
      dsimp only [IdempotentMatrix.map, IdempotentMatrix.blockSum]
      congr 1
      ext i j
      simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
    have hmapid (k : ℕ) : (IdempotentMatrix.identity C(Z, ℂ) k).map ψ =
        IdempotentMatrix.identity C(X, ℂ) k := by
      dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
      congr 1
      exact map_one ψ.mapMatrix
    have he' : (P.map ψ).IsEquivalent (Q.map ψ) := by
      dsimp only [P, Q]
      rw [hmapblock, hmapblock, hmapid]
      exact he
    obtain ⟨B, L, hBL, hLB, hPB, hQL⟩ := he'
    dsimp only [IdempotentMatrix.map] at B L hBL hLB hPB hQL
    have hQmatrix : Q.matrix = 1 := by
      change Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(Z, ℂ)) 0 0
          (1 : Matrix (Fin m) (Fin m) C(Z, ℂ))) = 1
      rw [Matrix.fromBlocks_one]
      exact map_one (Matrix.reindexRingEquiv C(Z, ℂ) finSumFinEquiv)
    rw [hQmatrix, map_one] at hLB
    -- Compare the pulled-back frame with its value along the given retraction.
    let ρ := (ContinuousMap.compRightAlgHom ℂ ℂ
      (⟨fun x ↦ (r x).val, continuous_subtype_val.comp r.continuous⟩ : C(X, X))).toRingHom
    let θ : C(X, ℂ) →+* C(X, ℂ) :=
      (algebraMap ℂ C(X, ℂ)).comp (ContinuousMap.evalAlgHom ℂ ℂ a₀.val).toRingHom
    have hPconst : ρ.mapMatrix (ψ.mapMatrix P.matrix) = θ.mapMatrix (ψ.mapMatrix P.matrix) := by
      ext i j x
      change P.matrix i j (PointedQuotient.of A (r x).val) =
        P.matrix i j (PointedQuotient.of A a₀.val)
      rw [hcollapse, hcollapse]
    let Br : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ) := B.map ρ
    let Lr : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ) := L.map ρ
    let B₀ : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ) := B.map θ
    let L₀ : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ) := L.map θ
    have hBrLr : Br * Lr = ρ.mapMatrix (ψ.mapMatrix P.matrix) := by
      dsimp only [Br, Lr]
      rw [← Matrix.map_mul, hBL]
      rfl
    have hLrBr : Lr * Br = 1 := by
      dsimp only [Br, Lr]
      rw [← Matrix.map_mul, hLB]
      exact map_one ρ.mapMatrix
    have hB₀L₀ : B₀ * L₀ = θ.mapMatrix (ψ.mapMatrix P.matrix) := by
      dsimp only [B₀, L₀]
      rw [← Matrix.map_mul, hBL]
      rfl
    have hL₀B₀ : L₀ * B₀ = 1 := by
      dsimp only [B₀, L₀]
      rw [← Matrix.map_mul, hLB]
      exact map_one θ.mapMatrix
    -- The change of frame has a global inverse because both frames have the same image.
    have hboundary : Br * Lr = B₀ * L₀ := hBrLr.trans (hPconst.trans hB₀L₀.symm)
    let H := Lr * B₀
    let K := L₀ * Br
    have hHK : H * K = 1 := by
      change (Lr * B₀) * (L₀ * Br) = 1
      calc
        _ = Lr * (B₀ * L₀) * Br := by simp only [Matrix.mul_assoc]
        _ = Lr * (Br * Lr) * Br := by rw [hboundary]
        _ = (Lr * Br) * (Lr * Br) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLrBr, Matrix.one_mul]
    have hKH : K * H = 1 := by
      change (L₀ * Br) * (Lr * B₀) = 1
      calc
        _ = L₀ * (Br * Lr) * B₀ := by simp only [Matrix.mul_assoc]
        _ = L₀ * (B₀ * L₀) * B₀ := by rw [hboundary]
        _ = (L₀ * B₀) * (L₀ * B₀) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hL₀B₀, Matrix.one_mul]
    let C := B * H
    let D := K * L
    have hCD : C * D = ψ.mapMatrix P.matrix := by
      change (B * H) * (K * L) = _
      calc
        _ = B * (H * K) * L := by simp only [Matrix.mul_assoc]
        _ = ψ.mapMatrix P.matrix := by rw [hHK, Matrix.mul_one, hBL]
    have hDC : D * C = 1 := by
      change (K * L) * (B * H) = _
      calc
        _ = K * (L * B) * H := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hLB, Matrix.mul_one, hKH]
    -- Retraction correction makes the two inverse matrices constant on A.
    let ι := (ContinuousMap.compRightAlgHom ℂ ℂ
      (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X))).toRingHom
    have hBrA : Br.map ι = B.map ι := by
      ext i j x
      change B i j (r x.val).val = B i j x.val
      rw [hr x]
    have hLrA : Lr.map ι = L.map ι := by
      ext i j x
      change L i j (r x.val).val = L i j x.val
      rw [hr x]
    have hCB₀ : C.map ι = B₀.map ι := by
      calc
        _ = (B.map ι) * ((Lr.map ι) * (B₀.map ι)) := by
          dsimp only [C, H]
          rw [Matrix.map_mul, Matrix.map_mul]
        _ = ((Br * Lr) * B₀).map ι := by
          rw [Matrix.map_mul, Matrix.map_mul, hBrA, Matrix.mul_assoc]
        _ = ((B₀ * L₀) * B₀).map ι := by rw [hboundary]
        _ = B₀.map ι := by rw [Matrix.mul_assoc, hL₀B₀, Matrix.mul_one]
    have hDL₀ : D.map ι = L₀.map ι := by
      calc
        _ = ((L₀.map ι) * (Br.map ι)) * (L.map ι) := by
          dsimp only [D, K]
          rw [Matrix.map_mul, Matrix.map_mul]
        _ = (L₀ * (Br * Lr)).map ι := by
          rw [Matrix.map_mul, Matrix.map_mul, hLrA, Matrix.mul_assoc]
        _ = (L₀ * (B₀ * L₀)).map ι := by rw [hboundary]
        _ = L₀.map ι := by rw [← Matrix.mul_assoc, hL₀B₀, Matrix.one_mul]
    have hC (i j) (x : A) : C i j x = B i j a₀.val :=
      congrArg (fun M ↦ M i j x) hCB₀
    have hD (i j) (x : A) : D i j x = L i j a₀.val :=
      congrArg (fun M ↦ M i j x) hDL₀
    -- Descend those exact inverse matrices through the actual pointed quotient.
    have descend (f : C(X, ℂ)) (v : ℂ) (hf : ∀ x : A, f x = v) :
        ∃ g : C(Z, ℂ), ∀ x : X, g (PointedQuotient.of A x) = f x := by
      let F : X ⊕ PUnit → ℂ := Sum.elim f (fun _ ↦ v)
      have hF (z : X ⊕ PUnit) (hz : z ∈ pairCollapsedSet A) : F z = v := by
        cases z with
        | inl x =>
          have hx : x ∈ A := by simpa [pairCollapsedSet] using hz
          exact hf ⟨x, hx⟩
        | inr x => rfl
      let g : Z → ℂ := Quotient.lift F (by
        intro z w h
        rcases h with rfl | ⟨hz, hw⟩
        · rfl
        · exact (hF z hz).trans (hF w hw).symm)
      exact ⟨⟨g, continuous_quot_lift _ (f.continuous.sumElim continuous_const)⟩,
        fun _ ↦ rfl⟩
    choose Cq hCq using fun i j ↦ descend (C i j) (B i j a₀.val) (hC i j)
    choose Dq hDq using fun i j ↦ descend (D i j) (L i j a₀.val) (hD i j)
    let CqM : Matrix (Fin P.size) (Fin Q.size) C(Z, ℂ) := Cq
    let DqM : Matrix (Fin Q.size) (Fin P.size) C(Z, ℂ) := Dq
    change ∀ i j x, CqM i j (PointedQuotient.of A x) = C i j x at hCq
    change ∀ i j x, DqM i j (PointedQuotient.of A x) = D i j x at hDq
    have hCqDq : CqM * DqM = P.matrix := by
      ext i j z
      obtain ⟨x, rfl⟩ := hsurj z
      simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, hCq, hDq]
      have h := congrArg (fun M ↦ M i j x) hCD
      change (C * D) i j x = P.matrix i j (PointedQuotient.of A x) at h
      simpa only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply] using h
    have hDqCq : DqM * CqM = Q.matrix := by
      rw [hQmatrix]
      ext i j z
      obtain ⟨x, rfl⟩ := hsurj z
      simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, hCq, hDq]
      have h := congrArg (fun M ↦ M i j x) hDC
      simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply] at h
      by_cases hij : i = j
      · subst j
        simpa using h
      · simpa [Matrix.one_apply, hij] using h
    have hPQ : P.IsEquivalent Q := by
      refine ⟨CqM, DqM, hCqDq, hDqCq, ?_, ?_⟩
      · calc
          _ = (CqM * DqM) * CqM := by rw [hCqDq]
          _ = CqM * (DqM * CqM) := Matrix.mul_assoc _ _ _
          _ = CqM := by rw [hDqCq, hQmatrix, Matrix.mul_one]
      · rw [hQmatrix, Matrix.one_mul]
    -- Cancel the same free stabilizer to recover the original reduced class.
    have hclassPQ := kZeroClass_eq_of_isEquivalent P Q hPQ
    dsimp only [P, Q] at hclassPQ
    rw [kZeroClass_blockSum, kZeroClass_blockSum] at hclassPQ
    have hpq : kZeroClass _ p = kZeroClass _ q := add_right_cancel hclassPQ
    apply Subtype.ext
    change a.val = 0
    rw [hp, hpq, sub_self]
  · -- For empty X the original pointed quotient consists only of its base point.
    let : IsEmpty X := not_nonempty_iff.mp hX
    have hconst : (algebraMap ℂ C(Z, ℂ)).comp ev = RingHom.id C(Z, ℂ) := by
      ext f z
      rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩
      · rfl
      · exact isEmptyElim x
    apply Subtype.ext
    have hz : kZeroMap ev a.val = 0 := a.property
    have hid := congrArg (fun φ ↦ kZeroMap φ a.val) hconst
    rw [kZeroMap_comp, kZeroMap_id, AddMonoidHom.comp_apply, hz, map_zero] at hid
    exact hid.symm

/-- Retraction splits the actual absolute restriction map. -/
theorem complexKZeroRestriction_pullback_retraction [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (r : C(X, A)) (hr : ∀ a : A, r a = a) :
    letI := hA.isClosedEmbedding_subtypeVal.compactSpace
    (complexKZeroRestriction A hA).comp (complexKZeroPullback r) =
      AddMonoidHom.id (ComplexKZero A) := by
  /- The composite of the subtype inclusion with r is identity on A by hr.
  Contravariant functoriality identifies the two K₀ maps with pullback along that
  identity, so this is an explicit splitting of the restriction map. -/
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hcomp : r.comp i = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro a
    exact hr a
  change (complexKZeroPullback i).comp (complexKZeroPullback r) = _
  rw [← complexKZeroPullback_comp, hcomp]
  exact kZeroMap_id

/-- Restriction to a closed retract is surjective. -/
theorem complexKZeroRestriction_surjective_of_retraction [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (r : C(X, A)) (hr : ∀ a : A, r a = a) :
    Function.Surjective (complexKZeroRestriction A hA) := by
  /- For each class on A, pull it back along r. The splitting identity says
  that restriction of this class is the original one, supplying its preimage. -/
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  intro a
  refine ⟨complexKZeroPullback r a, ?_⟩
  exact DFunLike.congr_fun (complexKZeroRestriction_pullback_retraction A hA r hr) a

/-- Relative classes vanish when the base deforms into its relative subspace. -/
theorem relativeKZero_subsingleton_of_deformation [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (f : C(X, X)) (hf : ∀ x, f x ∈ A)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) f)
    (hH : ∀ t : I, ∀ x ∈ A, H (t, x) ∈ A) :
    Subsingleton (RelativeKZero A hA) := by
  /- The identity and f induce equal relative pullbacks by the pair homotopy.
  Since f maps all of X into A, its quotient map is constant at the base point
  and its reduced pullback is zero. Thus the identity endomorphism is zero. -/
  let hfA : Set.MapsTo f A A := fun x _ ↦ hf x
  let q := PointedQuotient.mapContinuous A A f hfA
  let b := PointedQuotient.basepoint A
  -- The given endpoint map collapses every original quotient representative to its base point.
  have hconstant (z : PointedQuotient A) : q z = b := by
    rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩
    · rfl
    · exact (PointedQuotient.of_eq_basepoint_iff A (f x)).2 (hf x)
  have heval : (ContinuousMap.compRightAlgHom ℂ ℂ q).toRingHom =
      (algebraMap ℂ C(PointedQuotient A, ℂ)).comp
        (ContinuousMap.evalAlgHom ℂ ℂ b).toRingHom := by
    ext g z
    change g (q z) = g b
    rw [hconstant]
  have heq := relativeKZeroPullback_eq_of_homotopy A hA A hA
    (ContinuousMap.id X) f (fun _ hx ↦ hx) hfA H hH
  rw [relativeKZeroPullback_id] at heq
  -- Homotopy makes the original identity equal to a pullback factoring through evaluation.
  have hzero (a : RelativeKZero A hA) : a = 0 := by
    apply Subtype.ext
    have ha : kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ b).toRingHom a.val = 0 := a.property
    have h := congrArg Subtype.val (DFunLike.congr_fun heq a)
    change a.val = kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ q).toRingHom a.val at h
    rw [heval, kZeroMap_comp, AddMonoidHom.comp_apply, ha, map_zero] at h
    exact h
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- Restriction of a closed set to a subspace is closed. -/
theorem isClosed_relative_subspace (A B : Set X) (hA : IsClosed A) :
    IsClosed {b : B | (b : X) ∈ A} := by
  /- The indicated set is the inverse image of A under the continuous subtype
  inclusion. Closedness is preserved by inverse image, with no compactness needed. -/
  exact hA.preimage continuous_subtype_val

/-- Restriction from a pair to a closed subspace pair. -/
def relativeKZeroClosedRestriction [CompactSpace X] [T2Space X]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) :
    letI := hB.isClosedEmbedding_subtypeVal.compactSpace
    RelativeKZero A hA →+
      RelativeKZero {b : B | (b : X) ∈ A} (isClosed_relative_subspace A B hA) :=
  letI := hB.isClosedEmbedding_subtypeVal.compactSpace
  relativeKZeroPullback {b : B | (b : X) ∈ A} (isClosed_relative_subspace A B hA)
    A hA ⟨Subtype.val, continuous_subtype_val⟩ (fun _ hx ↦ hx)

/-- Closed excision holds whenever the subspace contains the complement of A. -/
theorem relativeKZeroClosedRestriction_bijective [CompactSpace X] [T2Space X]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (h : A ∪ B = Set.univ) :
    Function.Bijective (relativeKZeroClosedRestriction A B hA hB) := by
  /- The induced map B/(A∩B) → X/A is bijective: points outside A all lie
  in B, and the distinguished classes match even if A∩B is empty. It is a
  continuous bijection from a compact space to a Hausdorff space, hence a pointed
  homeomorphism. Pullback by this actual homeomorphism is bijective on reduced K⁰. -/
  let := hB.isClosedEmbedding_subtypeVal.compactSpace
  let C : Set B := {b | (b : X) ∈ A}
  have hC : IsClosed C := isClosed_relative_subspace A B hA
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space C hC
  let i : C(B, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let k : C(PointedQuotient C, PointedQuotient A) :=
    PointedQuotient.mapContinuous C A i (fun _ hx ↦ hx)
  -- The actual subspace quotient map identifies exactly the same collapsed representatives.
  have hinj : Function.Injective k := by
    intro z w hzw
    rcases PointedQuotient.eq_basepoint_or_exists C z with rfl | ⟨x, rfl⟩ <;>
      rcases PointedQuotient.eq_basepoint_or_exists C w with rfl | ⟨y, rfl⟩
    · rfl
    · have hy : (y : X) ∈ A :=
        (PointedQuotient.of_eq_basepoint_iff A y).1 hzw.symm
      exact ((PointedQuotient.of_eq_basepoint_iff C y).2 hy).symm
    · have hx : (x : X) ∈ A :=
        (PointedQuotient.of_eq_basepoint_iff A x).1 hzw
      exact (PointedQuotient.of_eq_basepoint_iff C x).2 hx
    · rcases (PointedQuotient.of_eq_of_iff A x y).1 hzw with hxy | ⟨hx, hy⟩
      · exact congrArg (PointedQuotient.of C) (Subtype.ext hxy)
      · exact (PointedQuotient.of_eq_of_iff C x y).2 (Or.inr ⟨hx, hy⟩)
  have hsurj : Function.Surjective k := by
    intro z
    rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩
    · exact ⟨PointedQuotient.basepoint C, rfl⟩
    by_cases hx : x ∈ A
    · exact ⟨PointedQuotient.basepoint C,
        ((PointedQuotient.of_eq_basepoint_iff A x).2 hx).symm⟩
    · have hxB : x ∈ B := by
        have hxU : x ∈ A ∪ B := h.symm ▸ Set.mem_univ x
        exact hxU.resolve_left hx
      exact ⟨PointedQuotient.of C ⟨x, hxB⟩, rfl⟩
  -- Compactness and Hausdorffness turn this very map into a pointed homeomorphism.
  let e := (Equiv.ofBijective k ⟨hinj, hsurj⟩).toHomeomorphOfContinuousClosed
    k.continuous k.continuous.isClosedMap
  let g : C(PointedQuotient A, PointedQuotient C) := ⟨e.symm, e.symm.continuous⟩
  have hbase : g (PointedQuotient.basepoint A) = PointedQuotient.basepoint C :=
    e.symm_apply_eq.mpr rfl
  let inv : RelativeKZero C hC →+ RelativeKZero A hA :=
    reducedComplexKZeroPullback (PointedQuotient.basepoint A)
      (PointedQuotient.basepoint C) g hbase
  -- Its inverse pullback is inverse to the original relative restriction on both kernels.
  have hleft : Function.LeftInverse inv (relativeKZeroClosedRestriction A B hA hB) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback g (complexKZeroPullback k a.val) = a.val
    have hid : k.comp g = ContinuousMap.id _ := by
      ext z
      exact e.apply_symm_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hright : Function.RightInverse inv (relativeKZeroClosedRestriction A B hA hB) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback k (complexKZeroPullback g a.val) = a.val
    have hid : g.comp k = ContinuousMap.id _ := by
      ext z
      exact e.symm_apply_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

/-- The excision equivalence has the actual restriction as its forward map. -/
def relativeKZeroClosedExcisionEquiv [CompactSpace X] [T2Space X]
    (A B : Set X) (hA : IsClosed A) (hB : IsClosed B) (h : A ∪ B = Set.univ) :
    letI := hB.isClosedEmbedding_subtypeVal.compactSpace
    RelativeKZero A hA ≃+
      RelativeKZero {b : B | (b : X) ∈ A} (isClosed_relative_subspace A B hA) :=
  letI := hB.isClosedEmbedding_subtypeVal.compactSpace
  AddEquiv.ofBijective _ (relativeKZeroClosedRestriction_bijective A B hA hB h)

end AtiyahSinger
