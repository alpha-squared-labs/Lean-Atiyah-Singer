/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleKZero
public import AtiyahSinger.Topology.PointedQuotient

import Mathlib.Analysis.Complex.Tietze

/-!
# Relative K⁰ of compact Hausdorff pairs

Public module ID: M2080.

The group is the kernel of evaluation on the actual pointed quotient.
All maps are pullbacks along specified continuous maps. The forgetful map
from this relative group to K(X) need not be injective, even though its image
is the kernel of restriction K(X) → K(A).
Sources: SG I.9.16–9.26; Karoubi II.2.29–2.35. The comparison with geometric
triples and the difference-bundle construction are treated separately.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open OnePoint

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

attribute [local instance] PointedQuotient.compactSpace

/-- Reduced K⁰ of the pointed quotient, for a closed pair in a compact Hausdorff space. -/
abbrev RelativeKZero [CompactSpace X] [T2Space X] (A : Set X) (hA : IsClosed A) : Type _ :=
  letI := PointedQuotient.t2Space A hA
  reducedComplexKZero (PointedQuotient.basepoint A)

/-- Pull back relative classes along the induced map of pointed quotients. -/
def relativeKZeroPullback [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (f : C(X, Y)) (hf : Set.MapsTo f A B) : RelativeKZero B hB →+ RelativeKZero A hA :=
  letI := PointedQuotient.t2Space A hA
  letI := PointedQuotient.t2Space B hB
  reducedComplexKZeroPullback (PointedQuotient.basepoint A)
    (PointedQuotient.basepoint B) (PointedQuotient.mapContinuous A B f hf)
    (PointedQuotient.map_basepoint A B f hf)

/-- Relative pullback along the identity is identity. -/
theorem relativeKZeroPullback_id [CompactSpace X] [T2Space X] (A : Set X) (hA : IsClosed A) :
    relativeKZeroPullback A hA A hA (ContinuousMap.id X) (fun _ hx ↦ hx) =
      AddMonoidHom.id (RelativeKZero A hA) := by
  /- The quotient map induced by the identity fixes every representative. Its
  pullback on continuous functions and hence on K₀ is identity; restricting to
  the kernel of basepoint evaluation gives the asserted identity. -/
  let := PointedQuotient.t2Space A hA
  have hid : PointedQuotient.mapContinuous A A (ContinuousMap.id X) (fun _ hx ↦ hx) =
      ContinuousMap.id (PointedQuotient A) := by
    ext z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> rfl
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback (PointedQuotient.mapContinuous A A _ _) a.val = a.val
  rw [hid]
  change kZeroMap (RingHom.id _) a.val = a.val
  rw [kZeroMap_id]
  rfl

/-- Relative pullbacks compose contravariantly. -/
theorem relativeKZeroPullback_comp [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] [CompactSpace Z] [T2Space Z]
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (C : Set Z) (hC : IsClosed C) (f : C(X, Y)) (g : C(Y, Z))
    (hf : Set.MapsTo f A B) (hg : Set.MapsTo g B C) :
    relativeKZeroPullback A hA C hC (g.comp f) (hg.comp hf) =
      (relativeKZeroPullback A hA B hB f hf).comp (relativeKZeroPullback B hB C hC g hg) := by
  /- On representatives the quotient map of the composite is the composite of
  quotient maps. Apply contravariance of absolute K₀ pullback and use subtype
  extensionality to compare the restricted maps on reduced classes. -/
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  let := PointedQuotient.t2Space C hC
  have hcomp : PointedQuotient.mapContinuous A C (g.comp f) (hg.comp hf) =
      (PointedQuotient.mapContinuous B C g hg).comp
        (PointedQuotient.mapContinuous A B f hf) := by
    ext z
    induction z using Quotient.inductionOn with
    | h z => cases z <;> rfl
  apply AddMonoidHom.ext
  intro a
  apply Subtype.ext
  change complexKZeroPullback (PointedQuotient.mapContinuous A C _ _) a.val =
    complexKZeroPullback (PointedQuotient.mapContinuous A B f hf)
      (complexKZeroPullback (PointedQuotient.mapContinuous B C g hg) a.val)
  rw [hcomp, complexKZeroPullback_comp]
  rfl

/-- Forget the relative condition by pulling a reduced quotient class back to X. -/
def relativeKZeroForget [CompactSpace X] [T2Space X] (A : Set X) (hA : IsClosed A) :
    RelativeKZero A hA →+ ComplexKZero X :=
  letI := PointedQuotient.t2Space A hA
  (complexKZeroPullback ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩).comp
    (reducedComplexKZero (PointedQuotient.basepoint A)).subtype

/-- Restriction of absolute classes to a closed subspace. -/
def complexKZeroRestriction [CompactSpace X] [T2Space X] (A : Set X) (hA : IsClosed A) :
    letI := hA.isClosedEmbedding_subtypeVal.compactSpace
    ComplexKZero X →+ ComplexKZero A :=
  letI := hA.isClosedEmbedding_subtypeVal.compactSpace
  complexKZeroPullback ⟨Subtype.val, continuous_subtype_val⟩

/-- A forgotten relative class restricts to zero on A. -/
theorem complexKZeroRestriction_relativeKZeroForget [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (a : RelativeKZero A hA) :
    complexKZeroRestriction A hA (relativeKZeroForget A hA a) = 0 := by
  /- The composite from A into the quotient is constant at its base point.
  Pullback along that constant map factors through basepoint evaluation, and the
  defining reduced-class condition makes this evaluation zero. -/
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let q : C(X, PointedQuotient A) :=
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let i : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
  -- On A the quotient map is constant at the same distinguished base point.
  have heval : (ContinuousMap.compRightAlgHom ℂ ℂ i).toRingHom.comp
      (ContinuousMap.compRightAlgHom ℂ ℂ q).toRingHom =
      (algebraMap ℂ C(A, ℂ)).comp
        (ContinuousMap.evalAlgHom ℂ ℂ (PointedQuotient.basepoint A)).toRingHom := by
    ext f x
    change f (PointedQuotient.of A x) = f (PointedQuotient.basepoint A)
    rw [(PointedQuotient.of_eq_basepoint_iff A x).2 x.property]
  have ha : kZeroMap
      (ContinuousMap.evalAlgHom ℂ ℂ (PointedQuotient.basepoint A)).toRingHom a.val = 0 :=
    a.property
  change kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ i).toRingHom
    (kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ q).toRingHom a.val) = 0
  rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp, heval, kZeroMap_comp,
    AddMonoidHom.comp_apply, ha, map_zero]

section RelativeMatrixProofs

open scoped Matrix

namespace IdempotentMatrix

set_option backward.isDefEq.respectTransparency.types false in
/-- Equality in K-zero becomes rectangular equivalence after adding the same finite free
summand. This standard strengthening of the common-projective-summand criterion uses the
complement of that summand and is reused in relative exactness and retract injectivity. -/
theorem exists_isEquivalent_stabilization_of_kZeroClass_eq {R : Type*} [CommRing R]
    (p q : IdempotentMatrix R)
    (h : kZeroClass R p = kZeroClass R q) :
    ∃ n : ℕ, (p.blockSum (IdempotentMatrix.identity R n)).IsEquivalent
      (q.blockSum (IdempotentMatrix.identity R n)) := by
  classical
  have hblock (p q : IdempotentMatrix R) :
      Nonempty ((p.blockSum q).image ≃ₗ[R] p.image × q.image) := by
    -- Split the original columns using the same finite-index equivalence as blockSum.
    let c : (Fin (p.blockSum q).size → R) ≃ₗ[R]
        (Fin p.size → R) × (Fin q.size → R) :=
      (LinearEquiv.piCongrLeft' R (fun _ : Fin (p.blockSum q).size ↦ R)
        finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ R R)
    have hc_apply (x : Fin (p.blockSum q).size → R) :
        c x = (x ∘ Fin.castAdd q.size, x ∘ Fin.natAdd p.size) := rfl
    have hc (x : Fin (p.blockSum q).size → R) :
        c ((p.blockSum q).matrix.mulVecLin x) =
          (p.matrix.mulVecLin (c x).1, q.matrix.mulVecLin (c x).2) := by
      change c ((Matrix.fromBlocks p.matrix 0 0 q.matrix).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ x) = _
      rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
        Matrix.fromBlocks_mulVec]
      apply Prod.ext <;> ext i <;>
        simp [hc_apply, Function.comp_def]
    -- The block multiplication formula restricts these coordinates to the actual images.
    have hmem (x : (p.blockSum q).image) :
        (c x.val).1 ∈ p.image ∧ (c x.val).2 ∈ q.image := by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      rw [hc]
      exact ⟨⟨(c y).1, rfl⟩, ⟨(c y).2, rfl⟩⟩
    let f : (p.blockSum q).image →ₗ[R] p.image × q.image := {
      toFun := fun x ↦ (⟨(c x.val).1, (hmem x).1⟩, ⟨(c x.val).2, (hmem x).2⟩)
      map_add' := fun x y ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := fun r x ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp }
    -- Coordinate injectivity and explicit block-image preimages give the image equivalence.
    refine ⟨LinearEquiv.ofBijective f ⟨?_, ?_⟩⟩
    · intro x y hxy
      apply Subtype.ext
      apply c.injective
      exact Prod.ext (congrArg (fun z : p.image × q.image ↦ z.1.val) hxy)
        (congrArg (fun z : p.image × q.image ↦ z.2.val) hxy)
    · rintro ⟨x, y⟩
      obtain ⟨a, ha⟩ := x.property
      obtain ⟨b, hb⟩ := y.property
      refine ⟨(p.blockSum q).matrix.mulVecLin.rangeRestrict (c.symm (a, b)), ?_⟩
      apply Prod.ext <;> apply Subtype.ext
      · change (c ((p.blockSum q).matrix.mulVecLin (c.symm (a, b)))).1 = x.val
        rw [hc, c.apply_symm_apply]
        exact ha
      · change (c ((p.blockSum q).matrix.mulVecLin (c.symm (a, b)))).2 = y.val
        rw [hc, c.apply_symm_apply]
        exact hb
  obtain ⟨r, ⟨e⟩⟩ := (kZeroClass_eq_iff_exists_stable_image_equiv p q).mp h
  have hfix (s : IdempotentMatrix R) (x : s.image) : s.matrix *ᵥ x.val = x.val := by
    obtain ⟨v, hv⟩ := x.property
    change s.matrix *ᵥ v = x.val at hv
    rw [← hv, Matrix.mulVec_mulVec, s.mul_self]
  let c : (r.image × r.complement.image) ≃ₗ[R] (Fin r.size → R) :=
    { toFun := fun x ↦ x.1.val + x.2.val
      invFun := fun x ↦ (r.matrix.mulVecLin.rangeRestrict x,
        r.complement.matrix.mulVecLin.rangeRestrict x)
      map_add' := fun x y ↦ by ext i; simp; ring
      map_smul' := fun s x ↦ by ext i; simp [mul_add]
      left_inv := by
        rintro ⟨x, y⟩
        apply Prod.ext <;> apply Subtype.ext
        · change r.matrix *ᵥ (x.val + y.val) = x.val
          rw [Matrix.mulVec_add, hfix]
          obtain ⟨v, hv⟩ := y.property
          change r.complement.matrix *ᵥ v = y.val at hv
          rw [← hv, Matrix.mulVec_mulVec, r.matrix_mul_complement,
            Matrix.zero_mulVec, add_zero]
        · change r.complement.matrix *ᵥ (x.val + y.val) = y.val
          rw [Matrix.mulVec_add, hfix]
          obtain ⟨v, hv⟩ := x.property
          change r.matrix *ᵥ v = x.val at hv
          rw [← hv, Matrix.mulVec_mulVec, r.complement_mul_matrix,
            Matrix.zero_mulVec, zero_add]
      right_inv := by
        intro x
        change r.matrix *ᵥ x + (1 - r.matrix) *ᵥ x = x
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel }
  let a : (p.image × (Fin r.size → R)) ≃ₗ[R] (q.image × (Fin r.size → R)) :=
    ((LinearEquiv.refl R p.image).prodCongr c.symm).trans
      ((LinearEquiv.prodAssoc R p.image r.image r.complement.image).symm.trans
        ((e.prodCongr (LinearEquiv.refl R r.complement.image)).trans
          ((LinearEquiv.prodAssoc R q.image r.image r.complement.image).trans
            ((LinearEquiv.refl R q.image).prodCongr c))))
  let t := IdempotentMatrix.identity R r.size
  have ht : t.image = ⊤ := by
    change (Matrix.mulVecLin (1 : Matrix (Fin r.size) (Fin r.size) R)).range = ⊤
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  let ct : t.image ≃ₗ[R] (Fin r.size → R) := LinearEquiv.ofTop t.image ht
  obtain ⟨cp⟩ := hblock p t
  obtain ⟨cq⟩ := hblock q t
  refine ⟨r.size, (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr ?_⟩
  exact ⟨cp.trans (((LinearEquiv.refl R p.image).prodCongr ct).trans
    (a.trans (((LinearEquiv.refl R q.image).prodCongr ct.symm).trans cq.symm)))⟩

end IdempotentMatrix

set_option maxHeartbeats 1200000 in

set_option backward.isDefEq.respectTransparency false in
/-- Relative K⁰ is exact at absolute K⁰. -/
theorem range_relativeKZeroForget [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    (relativeKZeroForget A hA).range = (complexKZeroRestriction A hA).ker := by
  classical
  let := hA.isClosedEmbedding_subtypeVal.compactSpace
  let Z := PointedQuotient A
  let : CompactSpace Z := PointedQuotient.compactSpace A
  let : T2Space Z := PointedQuotient.t2Space A hA
  apply le_antisymm
  · rintro a ⟨b, rfl⟩
    exact complexKZeroRestriction_relativeKZeroForget A hA b
  intro a ha
  -- Write the original class as one image bundle minus a trivial bundle.
  obtain ⟨p, n, hp⟩ := ComplexBundle.exists_class_sub_trivial a
  rw [ComplexBundle.kZeroClass_image, ComplexBundle.kZeroClass_trivial] at hp
  let φ : C(X, ℂ) →+* C(A, ℂ) :=
    (ContinuousMap.compRightAlgHom ℂ ℂ ⟨Subtype.val, continuous_subtype_val⟩).toRingHom
  let q := IdempotentMatrix.identity C(X, ℂ) n
  have hclass : kZeroClass C(A, ℂ) (p.map φ) = kZeroClass C(A, ℂ) (q.map φ) := by
    change kZeroMap φ a = 0 at ha
    rw [hp, map_sub, kZeroMap_class, kZeroMap_class, sub_eq_zero] at ha
    exact ha
  obtain ⟨m, he⟩ := IdempotentMatrix.exists_isEquivalent_stabilization_of_kZeroClass_eq
    (p.map φ) (q.map φ) hclass
  let P := p.blockSum (IdempotentMatrix.identity C(X, ℂ) m)
  let Q := q.blockSum (IdempotentMatrix.identity C(X, ℂ) m)
  have hmapblock (v w : IdempotentMatrix C(X, ℂ)) :
      (v.blockSum w).map φ = (v.map φ).blockSum (w.map φ) := by
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.blockSum]
    congr 1
    ext i j
    simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
    cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
  have hmapid (k : ℕ) : (IdempotentMatrix.identity C(X, ℂ) k).map φ =
      IdempotentMatrix.identity C(A, ℂ) k := by
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.identity]
    congr 1
    exact map_one φ.mapMatrix
  have he' : (P.map φ).IsEquivalent (Q.map φ) := by
    dsimp only [P, Q]
    rw [hmapblock, hmapblock, hmapid]
    exact he
  obtain ⟨Ba, La, hBaLa, hLaBa, hPBa, hQLa⟩ := he'
  dsimp only [IdempotentMatrix.map] at Ba La hBaLa hLaBa hPBa hQLa
  -- Extend only rectangular matrix entries; invertibility is supplied by elementary shears.
  choose B hB using fun i j ↦ (Ba i j).exists_restrict_eq hA
  choose L hL using fun i j ↦ (La i j).exists_restrict_eq hA
  have hφB : Matrix.map B φ = Ba := by
    ext i j x
    exact congrArg (fun f : C(A, ℂ) ↦ f x) (hB i j)
  have hφL : Matrix.map L φ = La := by
    ext i j x
    exact congrArg (fun f : C(A, ℂ) ↦ f x) (hL i j)
  let S : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin P.size) (Fin P.size) C(X, ℂ)) (-B) 0 1
  let T : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin P.size) (Fin P.size) C(X, ℂ)) 0 L 1
  let S' : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin P.size) (Fin P.size) C(X, ℂ)) B 0 1
  let T' : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks (1 : Matrix (Fin P.size) (Fin P.size) C(X, ℂ)) 0 (-L) 1
  let U := S * T * S
  let V := S' * T' * S'
  have hSS : S * S' = 1 := by simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hS'S : S' * S = 1 := by simp [S, S', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hTT : T * T' = 1 := by simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hT'T : T' * T = 1 := by simp [T, T', Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  have hUV : U * V = 1 := by
    change (S * T * S) * (S' * T' * S') = 1
    calc
      _ = S * T * (S * S') * T' * S' := by noncomm_ring
      _ = 1 := by rw [hSS, mul_one, mul_assoc S T T', hTT, mul_one, hSS]
  have hVU : V * U = 1 := by
    change (S' * T' * S') * (S * T * S) = 1
    calc
      _ = S' * T' * (S' * S) * T * S := by noncomm_ring
      _ = 1 := by rw [hS'S, mul_one, mul_assoc S' T' T, hT'T, mul_one, hS'S]
  let P₀ : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks P.matrix (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) 0 0
  let Q₀ : Matrix (Fin P.size ⊕ Fin Q.size) (Fin P.size ⊕ Fin Q.size) C(X, ℂ) :=
    Matrix.fromBlocks (0 : Matrix (Fin P.size) (Fin P.size) C(X, ℂ)) 0 0 Q.matrix
  have hP₀ : P₀ * P₀ = P₀ := by simp [P₀, Matrix.fromBlocks_multiply, P.mul_self]
  have hQ₀ : Q₀ * Q₀ = Q₀ := by simp [Q₀, Matrix.fromBlocks_multiply, Q.mul_self]
  change Ba * La = P.matrix.map φ at hBaLa
  change La * Ba = Q.matrix.map φ at hLaBa
  change P.matrix.map φ * Ba = Ba at hPBa
  change Q.matrix.map φ * La = La at hQLa
  have hPφ : P.matrix.map φ * P.matrix.map φ = P.matrix.map φ :=
    (P.map φ).mul_self
  have hQφ : Q.matrix.map φ * Q.matrix.map φ = Q.matrix.map φ :=
    (Q.map φ).mul_self
  have hLaP : La * (P.matrix.map φ) = La := by
    calc
      La * (P.matrix.map φ) = La * (Ba * La) := congrArg (La * ·) hBaLa.symm
      _ = (La * Ba) * La := (Matrix.mul_assoc _ _ _).symm
      _ = La := by rw [hLaBa, hQLa]
  have hSmap : φ.mapMatrix S = Matrix.fromBlocks 1 (-Ba) 0 1 := by
    ext i j
    cases i <;> cases j <;> simp [S, RingHom.mapMatrix_apply, Matrix.fromBlocks,
      ← hφB, Matrix.map_apply, Matrix.one_apply]
  have hTmap : φ.mapMatrix T = Matrix.fromBlocks 1 0 La 1 := by
    ext i j
    cases i <;> cases j <;> simp [T, RingHom.mapMatrix_apply, Matrix.fromBlocks,
      ← hφL, Matrix.map_apply, Matrix.one_apply]
  have hPmap : φ.mapMatrix P₀ = Matrix.fromBlocks (P.matrix.map φ) 0 0 0 := by
    ext i j
    cases i <;> cases j <;> simp [P₀, RingHom.mapMatrix_apply, Matrix.fromBlocks]
  have hQmap : φ.mapMatrix Q₀ = Matrix.fromBlocks 0 0 0 (Q.matrix.map φ) := by
    ext i j
    cases i <;> cases j <;> simp [Q₀, RingHom.mapMatrix_apply, Matrix.fromBlocks]
  have hrestrict : φ.mapMatrix (U * P₀ * V) = φ.mapMatrix Q₀ := by
    have hUa : φ.mapMatrix U = Matrix.fromBlocks
        (1 - (P.matrix.map φ)) (-Ba) La (1 - (Q.matrix.map φ)) := by
      simp only [U, map_mul, hSmap, hTmap, Matrix.fromBlocks_multiply,
        Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul,
        Matrix.mul_neg, hBaLa, hLaBa]
      congr 1
      · simp [Matrix.add_mul, Matrix.neg_mul, hPBa]
      · abel
    have hi : φ.mapMatrix U * φ.mapMatrix P₀ = φ.mapMatrix Q₀ * φ.mapMatrix U := by
      rw [hUa, hPmap, hQmap]
      simp [Matrix.fromBlocks_multiply, Matrix.sub_mul, Matrix.mul_sub,
        hPφ, hQφ, hLaP, hQLa]
    rw [map_mul, map_mul, hi, mul_assoc, ← map_mul, hUV, map_one, mul_one]
  have hQmatrix : Q.matrix = 1 := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) C(X, ℂ)) 0 0
        (1 : Matrix (Fin m) (Fin m) C(X, ℂ))) = 1
    rw [Matrix.fromBlocks_one]
    exact map_one (Matrix.reindexRingEquiv C(X, ℂ) finSumFinEquiv)
  let reindex := Matrix.reindexRingEquiv C(X, ℂ)
    (finSumFinEquiv (m := P.size) (n := Q.size))
  let Rm := reindex (U * P₀ * V)
  let Cm := reindex Q₀
  have hRm : Rm * Rm = Rm := by
    dsimp only [Rm]
    rw [← map_mul]
    apply congrArg reindex
    calc
      _ = U * P₀ * (V * U) * P₀ * V := by noncomm_ring
      _ = U * P₀ * V := by rw [hVU, mul_one, mul_assoc U P₀ P₀, hP₀]
  have hCm : Cm * Cm = Cm := by dsimp only [Cm]; rw [← map_mul, hQ₀]
  let c : Matrix (Fin (P.size + Q.size)) (Fin (P.size + Q.size)) ℂ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (0 : Matrix (Fin P.size) (Fin P.size) ℂ) 0 0 1)
  have hCconst (i j) : Cm i j = ContinuousMap.const X (c i j) := by
    dsimp only [Cm, reindex, Q₀]
    rw [hQmatrix]
    ext x
    dsimp only [Matrix.reindexRingEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, c]
    cases hi : finSumFinEquiv.symm i <;> cases hj : finSumFinEquiv.symm j <;>
      simp [Matrix.fromBlocks, Matrix.one_apply, hi, hj]
    all_goals split_ifs <;> rfl
  have hseam (i j) (x : A) : Rm i j x = c i j := by
    have h := congrArg (fun M ↦ M (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) x)
      hrestrict
    change Rm i j x = Cm i j x at h
    rw [hCconst] at h
    exact h
  -- Descend the constant-on-A matrix to the original pointed quotient.
  have descend (f : C(X, ℂ)) (v : ℂ) (hf : ∀ x : A, f x = v) :
      ∃ g : C(Z, ℂ),
        (∀ x : X, g (PointedQuotient.of A x) = f x) ∧
        g (PointedQuotient.basepoint A) = v := by
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
      fun _ ↦ rfl, rfl⟩
  choose D hD hDb using fun i j ↦ descend (Rm i j) (c i j) (hseam i j)
  have hcc : c * c = c := by
    change Matrix.reindex finSumFinEquiv finSumFinEquiv _ *
      Matrix.reindex finSumFinEquiv finSumFinEquiv _ = _
    change (Matrix.reindexRingEquiv ℂ finSumFinEquiv) _ *
      (Matrix.reindexRingEquiv ℂ finSumFinEquiv) _ = _
    rw [← map_mul]
    simp [Matrix.fromBlocks_multiply, c]
  let d : IdempotentMatrix C(Z, ℂ) :=
    { size := P.size + Q.size
      matrix := D
      mul_self := by
        ext i j z
        rcases PointedQuotient.eq_basepoint_or_exists A z with rfl | ⟨x, rfl⟩
        · simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, hDb]
          exact congrFun (congrFun hcc i) j
        · simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply, hD]
          simpa only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply]
            using congrArg (fun M ↦ M i j x) hRm }
  let cQ : IdempotentMatrix C(Z, ℂ) :=
    { size := P.size + Q.size
      matrix i j := ContinuousMap.const _ (c i j)
      mul_self := by
        ext i j z
        simp only [Matrix.mul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
          ContinuousMap.const_apply]
        exact congrFun (congrFun hcc i) j }
  let ψ := (ContinuousMap.compRightAlgHom ℂ ℂ
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩).toRingHom
  have hdmat : (d.map ψ).matrix = Rm := by ext i j x; exact hD i j x
  have hcmat : (cQ.map ψ).matrix = Cm := by
    ext i j x
    exact congrArg (fun f ↦ f x) (hCconst i j).symm
  have hdeval : d.map (ContinuousMap.evalAlgHom ℂ ℂ (PointedQuotient.basepoint A)).toRingHom =
      cQ.map (ContinuousMap.evalAlgHom ℂ ℂ (PointedQuotient.basepoint A)).toRingHom := by
    dsimp only [IdempotentMatrix.map, d, cQ]
    congr 1
    ext i j
    exact hDb i j
  let b : RelativeKZero A hA := ⟨kZeroClass _ d - kZeroClass _ cQ, by
    change kZeroMap _ (kZeroClass _ d - kZeroClass _ cQ) = 0
    rw [map_sub, kZeroMap_class, kZeroMap_class, hdeval, sub_self]⟩
  -- Rectangular inverse products identify the original K-zero presentations.
  have equivalent (p q : IdempotentMatrix C(X, ℂ))
      (N : Matrix (Fin p.size) (Fin q.size) C(X, ℂ))
      (M : Matrix (Fin q.size) (Fin p.size) C(X, ℂ))
      (hNM : N * M = p.matrix) (hMN : M * N = q.matrix) : p.IsEquivalent q := by
    have hNQ : N * q.matrix = p.matrix * N := by
      rw [← hMN, ← Matrix.mul_assoc, hNM]
    have hMP : M * p.matrix = q.matrix * M := by
      rw [← hNM, ← Matrix.mul_assoc, hMN]
    refine ⟨p.matrix * N, q.matrix * M, ?_, ?_, ?_, ?_⟩
    · calc
        _ = p.matrix * (N * q.matrix) * M := by simp only [Matrix.mul_assoc]
        _ = p.matrix * (p.matrix * N) * M := by rw [hNQ]
        _ = (p.matrix * p.matrix) * (N * M) := by simp only [Matrix.mul_assoc]
        _ = p.matrix := by rw [p.mul_self, hNM, p.mul_self]
    · calc
        _ = q.matrix * (M * p.matrix) * N := by simp only [Matrix.mul_assoc]
        _ = q.matrix * (q.matrix * M) * N := by rw [hMP]
        _ = (q.matrix * q.matrix) * (M * N) := by simp only [Matrix.mul_assoc]
        _ = q.matrix := by rw [q.mul_self, hMN, q.mul_self]
    · rw [← Matrix.mul_assoc, p.mul_self]
    · rw [← Matrix.mul_assoc, q.mul_self]
  let ML : Matrix (Fin (P.size + Q.size)) (Fin P.size) C(X, ℂ) :=
    (U * Matrix.fromRows P.matrix (0 : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ))).submatrix
      finSumFinEquiv.symm id
  let NL : Matrix (Fin P.size) (Fin (P.size + Q.size)) C(X, ℂ) :=
    (Matrix.fromCols P.matrix (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) * V).submatrix
      id finSumFinEquiv.symm
  have hNLML : NL * ML = P.matrix := by
    dsimp only [NL, ML]
    rw [Matrix.submatrix_mul_equiv]
    have hc : (Matrix.fromCols P.matrix (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) * V) *
        (U * Matrix.fromRows P.matrix 0) = P.matrix := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc V, hVU, Matrix.one_mul,
        Matrix.fromCols_mul_fromRows, P.mul_self, Matrix.zero_mul, add_zero]
    rw [hc]
    rfl
  have hMLNL : ML * NL = (d.map ψ).matrix := by
    rw [hdmat]
    change (U * Matrix.fromRows P.matrix (0 : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ))).submatrix
      finSumFinEquiv.symm (Equiv.refl (Fin P.size)) *
      (Matrix.fromCols P.matrix (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) * V).submatrix
        (Equiv.refl (Fin P.size)) finSumFinEquiv.symm =
        (U * P₀ * V).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    rw [Matrix.submatrix_mul_equiv]
    congr 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.fromRows _ _),
      Matrix.fromRows_mul_fromCols, P.mul_self]
    simp [P₀, Matrix.mul_assoc]
  have hclassD : kZeroClass _ (d.map ψ) = kZeroClass _ P :=
    (kZeroClass_eq_of_isEquivalent P (d.map ψ) (equivalent P (d.map ψ) NL ML hNLML hMLNL)).symm
  let MR : Matrix (Fin (P.size + Q.size)) (Fin Q.size) C(X, ℂ) :=
    (Matrix.fromRows (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) Q.matrix).submatrix
      finSumFinEquiv.symm id
  let NR : Matrix (Fin Q.size) (Fin (P.size + Q.size)) C(X, ℂ) :=
    (Matrix.fromCols (0 : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ)) Q.matrix).submatrix
      id finSumFinEquiv.symm
  have hNRMR : NR * MR = Q.matrix := by
    dsimp only [NR, MR]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromRows,
      Matrix.zero_mul, zero_add, Q.mul_self]
    rfl
  have hMRNR : MR * NR = (cQ.map ψ).matrix := by
    rw [hcmat]
    change (Matrix.fromRows (0 : Matrix (Fin P.size) (Fin Q.size) C(X, ℂ)) Q.matrix).submatrix
      finSumFinEquiv.symm (Equiv.refl (Fin Q.size)) *
      (Matrix.fromCols (0 : Matrix (Fin Q.size) (Fin P.size) C(X, ℂ)) Q.matrix).submatrix
        (Equiv.refl (Fin Q.size)) finSumFinEquiv.symm =
        Q₀.submatrix finSumFinEquiv.symm finSumFinEquiv.symm
    rw [Matrix.submatrix_mul_equiv]
    congr 1
    rw [Matrix.fromRows_mul_fromCols]
    simp [Q₀, Q.mul_self]
  have hclassC : kZeroClass _ (cQ.map ψ) = kZeroClass _ Q :=
    (kZeroClass_eq_of_isEquivalent Q (cQ.map ψ) (equivalent Q (cQ.map ψ) NR MR hNRMR hMRNR)).symm
  refine ⟨b, ?_⟩
  change kZeroMap ψ (kZeroClass _ d - kZeroClass _ cQ) = a
  rw [map_sub, kZeroMap_class, kZeroMap_class, hclassD, hclassC]
  dsimp only [P, Q]
  rw [kZeroClass_blockSum, kZeroClass_blockSum]
  exact (add_sub_add_right_eq_sub _ _ _).trans hp.symm

end RelativeMatrixProofs

/-- Forgetting relative data is natural under maps of closed pairs. -/
theorem relativeKZeroForget_natural [CompactSpace X] [T2Space X]
    [CompactSpace Y] [T2Space Y] (A : Set X) (hA : IsClosed A)
    (B : Set Y) (hB : IsClosed B) (f : C(X, Y)) (hf : Set.MapsTo f A B) :
    (relativeKZeroForget A hA).comp (relativeKZeroPullback A hA B hB f hf) =
      (complexKZeroPullback f).comp (relativeKZeroForget B hB) := by
  /- The square of original spaces and their pointed quotients commutes on
  every point. Contravariant K₀ pullback turns it into the desired equality;
  the inclusion of reduced classes does not change their underlying classes. -/
  let := PointedQuotient.t2Space A hA
  let := PointedQuotient.t2Space B hB
  let qA : C(X, PointedQuotient A) :=
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  let qB : C(Y, PointedQuotient B) :=
    ⟨PointedQuotient.of B, PointedQuotient.continuous_of B⟩
  have hsquare : (PointedQuotient.mapContinuous A B f hf).comp qA = qB.comp f := by
    ext x
    rfl
  apply AddMonoidHom.ext
  intro a
  change complexKZeroPullback qA
      (complexKZeroPullback (PointedQuotient.mapContinuous A B f hf) a.val) =
    complexKZeroPullback f (complexKZeroPullback qB a.val)
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare,
    complexKZeroPullback_comp]
  rfl

/-- The empty relative subspace recovers absolute K⁰. -/
theorem relativeKZeroForget_empty_bijective [CompactSpace X] [T2Space X] :
    Function.Bijective (relativeKZeroForget (∅ : Set X) isClosed_empty) := by
  /- For empty A the quotient is the disjoint union of X and a point. A reduced
  class has zero component at that point, so restriction to X identifies it
  bijectively with absolute K⁰, including when X itself is empty. -/
  classical
  let := PointedQuotient.t2Space (∅ : Set X) isClosed_empty
  let ec : ((∅ : Set X)ᶜ : Set X) ≃ₜ X :=
    { toFun := Subtype.val
      invFun := fun x ↦ ⟨x, Set.notMem_empty x⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := continuous_subtype_val
      continuous_invFun := continuous_id.subtype_mk _ }
  let e := (PointedQuotient.onePointHomeomorph
    (∅ : Set X) isClosed_empty).trans ec.onePointCongr
  let b := PointedQuotient.basepoint (∅ : Set X)
  -- The specified quotient comparison keeps every original point and the added point.
  have hbase : e b = ∞ := by
    change ec.onePointCongr
      (PointedQuotient.onePointHomeomorph (∅ : Set X) isClosed_empty b) = ∞
    rw [PointedQuotient.onePointHomeomorph_basepoint]
    rfl
  have hfinite (x : X) : e (PointedQuotient.of (∅ : Set X) x) = (x : OnePoint X) := by
    have hx := PointedQuotient.onePointHomeomorph_of
      (∅ : Set X) isClosed_empty (ec.symm x)
    change ec.onePointCongr
      (PointedQuotient.onePointHomeomorph (∅ : Set X) isClosed_empty
        (PointedQuotient.of (∅ : Set X) (ec.symm x))) = (x : OnePoint X)
    rw [hx]
    rfl
  let f : C(PointedQuotient (∅ : Set X), OnePoint X) := ⟨e, e.continuous⟩
  let g : C(OnePoint X, PointedQuotient (∅ : Set X)) := ⟨e.symm, e.symm.continuous⟩
  have hbase' : g ∞ = b := e.symm_apply_eq.mpr hbase.symm
  let phi : RelativeKZero (∅ : Set X) isClosed_empty →+ CompactSupportKZero X :=
    reducedComplexKZeroPullback ∞ b g hbase'
  let inv : CompactSupportKZero X →+ RelativeKZero (∅ : Set X) isClosed_empty :=
    reducedComplexKZeroPullback b ∞ f hbase
  -- Inverse pointed homeomorphisms give inverse maps on the original evaluation kernels.
  have hleft : Function.LeftInverse inv phi := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback f (complexKZeroPullback g a.val) = a.val
    have hid : g.comp f = ContinuousMap.id _ := by
      ext z
      exact e.symm_apply_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hright : Function.RightInverse inv phi := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback g (complexKZeroPullback f a.val) = a.val
    have hid : f.comp g = ContinuousMap.id _ := by
      ext z
      exact e.apply_symm_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  -- Forgetting is this comparison followed by the established compact-base restriction.
  let i : C(X, OnePoint X) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let q : C(X, PointedQuotient (∅ : Set X)) :=
    ⟨PointedQuotient.of (∅ : Set X), PointedQuotient.continuous_of (∅ : Set X)⟩
  have hsquare : g.comp i = q := by
    ext x
    apply e.injective
    change e (e.symm (x : OnePoint X)) = e (PointedQuotient.of (∅ : Set X) x)
    rw [e.apply_symm_apply, hfinite]
  have hforget : relativeKZeroForget (∅ : Set X) isClosed_empty =
      compactSupportKZeroToAbsolute.comp phi := by
    apply AddMonoidHom.ext
    intro a
    change complexKZeroPullback q a.val =
      complexKZeroPullback i (complexKZeroPullback g a.val)
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
  rw [hforget]
  exact compactSupportKZeroToAbsolute_bijective.comp ⟨hleft.injective, hright.surjective⟩

/-- Canonical comparison for the empty relative subspace. -/
def relativeKZeroEmptyEquiv [CompactSpace X] [T2Space X] :
    RelativeKZero (∅ : Set X) isClosed_empty ≃+ ComplexKZero X :=
  AddEquiv.ofBijective _ relativeKZeroForget_empty_bijective

/-- The relative group of a space with itself is zero. -/
theorem relativeKZero_univ_subsingleton [CompactSpace X] [T2Space X] :
    Subsingleton (RelativeKZero (Set.univ : Set X) isClosed_univ) := by
  /- The quotient collapses every representative to its base point. Evaluation
  is then an isomorphism on K₀, whose kernel consists only of zero. -/
  let b := PointedQuotient.basepoint (Set.univ : Set X)
  have hall (z : PointedQuotient (Set.univ : Set X)) : z = b := by
    rcases PointedQuotient.eq_basepoint_or_exists Set.univ z with hz | ⟨x, rfl⟩
    · exact hz
    · exact (PointedQuotient.of_eq_basepoint_iff Set.univ x).2 (Set.mem_univ x)
  -- Evaluation at the sole quotient point has the constant-function map as inverse.
  let ev := (ContinuousMap.evalAlgHom ℂ ℂ b).toRingHom
  let c := algebraMap ℂ C(PointedQuotient (Set.univ : Set X), ℂ)
  have hcev : c.comp ev = RingHom.id _ := by
    ext f z
    change f b = f z
    rw [hall z]
  have hzero (a : RelativeKZero (Set.univ : Set X) isClosed_univ) : a = 0 := by
    apply Subtype.ext
    have ha : kZeroMap ev a.val = 0 := a.property
    have h := congrArg (kZeroMap c) ha
    rw [← AddMonoidHom.comp_apply, ← kZeroMap_comp, hcev, kZeroMap_id, map_zero] at h
    exact h
  exact ⟨fun a b ↦ (hzero a).trans (hzero b).symm⟩

/-- The complement comparison sends infinity back to the quotient base point. -/
theorem PointedQuotient.onePointHomeomorph_symm_infty [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    (PointedQuotient.onePointHomeomorph A hA).symm ∞ = PointedQuotient.basepoint A := by
  /- Apply the inverse of the homeomorphism to its basepoint equation. The
  inverse law identifies the image with the original distinguished quotient class. -/
  exact (PointedQuotient.onePointHomeomorph A hA).symm_apply_eq.mpr
    (PointedQuotient.onePointHomeomorph_basepoint A hA).symm

/-- Map relative classes to compactly supported classes on the open complement. -/
def relativeKZeroToCompactSupport [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    RelativeKZero A hA →+ CompactSupportKZero (Aᶜ : Set X) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  letI := PointedQuotient.t2Space A hA
  reducedComplexKZeroPullback ∞ (PointedQuotient.basepoint A)
    ⟨(PointedQuotient.onePointHomeomorph A hA).symm,
      (PointedQuotient.onePointHomeomorph A hA).symm.continuous⟩
    (PointedQuotient.onePointHomeomorph_symm_infty A hA)

/-- The actual complement pullback is bijective. -/
theorem relativeKZeroToCompactSupport_bijective [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    Function.Bijective (relativeKZeroToCompactSupport A hA) := by
  /- Pullback by the inverse pointed homeomorphism is inverse to pullback by
  the homeomorphism itself. Both preserve evaluation kernels by the basepoint
  equations, so they give mutually inverse homomorphisms on the reduced groups. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space A hA
  let e := PointedQuotient.onePointHomeomorph A hA
  let f : C(PointedQuotient A, OnePoint (Aᶜ : Set X)) := ⟨e, e.continuous⟩
  let g : C(OnePoint (Aᶜ : Set X), PointedQuotient A) := ⟨e.symm, e.symm.continuous⟩
  let inv := reducedComplexKZeroPullback (PointedQuotient.basepoint A) ∞ f
    (PointedQuotient.onePointHomeomorph_basepoint A hA)
  -- The actual pointed homeomorphism gives inverses on the original evaluation kernels.
  have hleft : Function.LeftInverse inv (relativeKZeroToCompactSupport A hA) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback f (complexKZeroPullback g a.val) = a.val
    have hid : g.comp f = ContinuousMap.id _ := by
      ext z
      exact e.symm_apply_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  have hright : Function.RightInverse inv (relativeKZeroToCompactSupport A hA) := by
    intro a
    apply Subtype.ext
    change complexKZeroPullback g (complexKZeroPullback f a.val) = a.val
    have hid : f.comp g = ContinuousMap.id _ := by
      ext z
      exact e.apply_symm_apply z
    rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hid]
    change kZeroMap (RingHom.id _) a.val = a.val
    rw [kZeroMap_id]
    rfl
  exact ⟨hleft.injective, hright.surjective⟩

/-- Relative K⁰ is canonically isomorphic to compactly supported K⁰ of the open complement. -/
def relativeKZeroCompactSupportEquiv [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) :
    letI := hA.isOpen_compl.locallyCompactSpace
    RelativeKZero A hA ≃+ CompactSupportKZero (Aᶜ : Set X) :=
  letI := hA.isOpen_compl.locallyCompactSpace
  AddEquiv.ofBijective _ (relativeKZeroToCompactSupport_bijective A hA)

/-- Open extension on the complement agrees with forgetting the relative class. -/
theorem relativeKZeroToCompactSupport_extension [CompactSpace X] [T2Space X]
    (A : Set X) (hA : IsClosed A) (a : RelativeKZero A hA) :
    compactSupportKZeroToAbsolute
      (compactSupportKZeroOpenExtension (Aᶜ : Set X) hA.isOpen_compl
        (relativeKZeroToCompactSupport A hA a)) = relativeKZeroForget A hA a := by
  /- The collapse from X⁺ to the compactified complement, followed by the
  inverse comparison with the quotient, restricts on X to the original quotient
  map. It sends infinity to the base point. Functoriality of reduced pullback
  therefore identifies open extension followed by restriction with forgetting. -/
  let := hA.isOpen_compl.locallyCompactSpace
  let := PointedQuotient.t2Space A hA
  let e := PointedQuotient.onePointHomeomorph A hA
  let f : C(OnePoint (Aᶜ : Set X), PointedQuotient A) := ⟨e.symm, e.symm.continuous⟩
  let c : C(OnePoint X, OnePoint (Aᶜ : Set X)) :=
    ⟨onePointCollapse Aᶜ, continuous_onePointCollapse Aᶜ hA.isOpen_compl⟩
  let i : C(X, OnePoint X) := ⟨OnePoint.some, OnePoint.continuous_coe⟩
  let q : C(X, PointedQuotient A) :=
    ⟨PointedQuotient.of A, PointedQuotient.continuous_of A⟩
  -- Check the specified square on A and on its actual complement separately.
  have hsquare : f.comp (c.comp i) = q := by
    ext x
    change e.symm (onePointCollapse Aᶜ (x : OnePoint X)) = PointedQuotient.of A x
    by_cases hx : x ∈ A
    · have hnot : x ∉ (Aᶜ : Set X) := by simpa using hx
      simp only [onePointCollapse, OnePoint.elim_some, dite_eq_right hnot]
      exact (PointedQuotient.onePointHomeomorph_symm_infty A hA).trans
        ((PointedQuotient.of_eq_basepoint_iff A x).2 hx).symm
    · have hcoe := PointedQuotient.onePointHomeomorph_of A hA (⟨x, hx⟩ : (Aᶜ : Set X))
      apply e.injective
      rw [e.apply_symm_apply]
      simpa [onePointCollapse, hx, e] using hcoe.symm
  change complexKZeroPullback i
      (complexKZeroPullback c (complexKZeroPullback f a.val)) = complexKZeroPullback q a.val
  rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
    ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]

end AtiyahSinger
