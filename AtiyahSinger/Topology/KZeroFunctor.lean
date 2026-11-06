/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.IdempotentHomotopy
public import AtiyahSinger.Topology.KZero
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Homotopy.Basic

/-!
# Functoriality and rank in the finite-projective model of K₀

Public module ID: M1922.

Ring maps act on actual idempotent matrices,
and the resulting maps descend through the existing presentation of K₀. The rank map
over a field is the dimension of the image, extended additively. None of these maps is
specified by an arbitrary isomorphism or by an index-theorem identity.

For compact Hausdorff spaces, pullback is induced by precomposition of continuous
functions. Homotopy invariance uses finite matrices over C(X, ℂ), with uniform rather
than merely pointwise control of a homotopy. See Karoubi I.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped BigOperators Matrix Matrix.Norms.Operator unitInterval

namespace IdempotentMatrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Extension of scalars in the idempotent model, by applying the ring map to each entry. -/
def map (φ : R →+* S) (p : IdempotentMatrix R) : IdempotentMatrix S where
  size := p.size
  matrix := φ.mapMatrix p.matrix
  mul_self := by
    rw [← map_mul, p.mul_self]

/-- The identity matrix presents a free module of the displayed rank. -/
def identity (R : Type*) [CommRing R] (n : ℕ) : IdempotentMatrix R where
  size := n
  matrix := 1
  mul_self := one_mul 1

/-- Extension of scalars respects the rectangular equivalence of presentations. -/
theorem isEquivalent_map (φ : R →+* S) (p q : IdempotentMatrix R)
    (h : p.IsEquivalent q) : (p.map φ).IsEquivalent (q.map φ) := by
  /- Apply φ entry by entry to the two rectangular witnesses. Ring homomorphisms
  preserve each finite sum and product in the four defining matrix identities. -/
  obtain ⟨a, b, hab, hba, hpa, hqb⟩ := h
  refine ⟨a.map φ, b.map φ, ?_, ?_, ?_, ?_⟩
  · change a.map φ * b.map φ = p.matrix.map φ
    rw [← Matrix.map_mul, hab]
  · change b.map φ * a.map φ = q.matrix.map φ
    rw [← Matrix.map_mul, hba]
  · change p.matrix.map φ * a.map φ = a.map φ
    rw [← Matrix.map_mul, hpa]
  · change q.matrix.map φ * b.map φ = b.map φ
    rw [← Matrix.map_mul, hqb]

end IdempotentMatrix

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- The generator map kills the defining relations needed for functoriality of K₀. -/
theorem kZeroRelations_le_ker_map (φ : R →+* S) :
    kZeroRelations R ≤
      (FreeAbelianGroup.lift (fun p : IdempotentMatrix R ↦
        kZeroClass S (p.map φ))).ker := by
  /- First handle the generators: rectangular equivalence survives entrywise φ,
  and entrywise φ commutes with the reindexed block sum. Their differences vanish
  in K₀(S). The kernel is a subgroup, so it contains the generated relation subgroup. -/
  apply (AddSubgroup.closure_le _).mpr
  rintro x (⟨p, q, hpq, rfl⟩ | ⟨p, q, rfl⟩)
  · change (FreeAbelianGroup.lift _) (_ - _) = 0
    simp only [map_sub, FreeAbelianGroup.lift_apply_of]
    exact sub_eq_zero.mpr (kZeroClass_eq_of_isEquivalent _ _
      (IdempotentMatrix.isEquivalent_map φ p q hpq))
  · have hblock : (p.blockSum q).map φ = (p.map φ).blockSum (q.map φ) := by
      dsimp only [IdempotentMatrix.map, IdempotentMatrix.blockSum]
      congr 1
      ext i j
      simp only [IdempotentMatrix.blockMatrix, Matrix.reindex_apply,
        RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply]
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> simp
    change (FreeAbelianGroup.lift _) (_ - _ - _) = 0
    simp only [map_sub, FreeAbelianGroup.lift_apply_of, hblock, kZeroClass_blockSum]
    abel

/-- The usual covariant map of algebraic K₀ induced by a unital ring homomorphism. -/
def kZeroMap (φ : R →+* S) : KZero R →+ KZero S :=
  QuotientAddGroup.lift (kZeroRelations R)
    (FreeAbelianGroup.lift (fun p : IdempotentMatrix R ↦ kZeroClass S (p.map φ)))
    (fun _ hx ↦ kZeroRelations_le_ker_map φ hx)

/-- The induced map sends a projective presentation to its extension of scalars. -/
theorem kZeroMap_class (φ : R →+* S) (p : IdempotentMatrix R) :
    kZeroMap φ (kZeroClass R p) = kZeroClass S (p.map φ) := by
  /- Evaluate the quotient lift on the free generator. This is its defining formula,
  so there is no choice of a projective representative hidden in the induced map. -/
  exact FreeAbelianGroup.lift_apply_of _ p

/-- Identity ring maps induce identity maps on K₀. -/
theorem kZeroMap_id : kZeroMap (RingHom.id R) = AddMonoidHom.id (KZero R) := by
  /- The two homomorphisms agree on every idempotent generator because entrywise
  application of the identity ring map preserves its matrix. Generators span K₀. -/
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change kZeroMap (RingHom.id R) (kZeroClass R p) = kZeroClass R p
  rw [kZeroMap_class]
  rfl

/-- Composition of ring maps induces composition of the specified K₀ maps. -/
theorem kZeroMap_comp (φ : R →+* S) (ψ : S →+* T) :
    kZeroMap (ψ.comp φ) = (kZeroMap ψ).comp (kZeroMap φ) := by
  /- On an idempotent generator both sides apply ψ(φ(-)) to each entry. Extend this
  equality from the generators through the additive presentation of K₀. -/
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change kZeroMap (ψ.comp φ) (kZeroClass R p) =
    kZeroMap ψ (kZeroMap φ (kZeroClass R p))
  rw [kZeroMap_class, kZeroMap_class, kZeroMap_class]
  rfl

variable (K : Type*) [Field K]

set_option backward.isDefEq.respectTransparency.types false in
/-- Dimension is additive and isomorphism invariant on finite projective presentations. -/
theorem kZeroRelations_le_ker_rank :
    kZeroRelations K ≤
      (FreeAbelianGroup.lift (fun p : IdempotentMatrix K ↦
        (Module.finrank K p.image : ℤ))).ker := by
  /- Every image is a subspace of a finite-dimensional free space. Rectangular
  equivalence identifies the image spaces, while block sum identifies their direct
  sum. Finite-dimensional rank is invariant under the former and additive under
  the latter. Thus both families of relation generators have dimension difference zero. -/
  have hblock (p q : IdempotentMatrix K) :
      Nonempty ((p.blockSum q).image ≃ₗ[K] p.image × q.image) := by
    let c : (Fin (p.blockSum q).size → K) ≃ₗ[K]
        (Fin p.size → K) × (Fin q.size → K) :=
      (LinearEquiv.piCongrLeft' K (fun _ : Fin (p.blockSum q).size ↦ K)
        finSumFinEquiv.symm).trans (LinearEquiv.sumArrowLequivProdArrow _ _ K K)
    have hc_apply (x : Fin (p.blockSum q).size → K) :
        c x = (x ∘ Fin.castAdd q.size, x ∘ Fin.natAdd p.size) := rfl
    have hc (x : Fin (p.blockSum q).size → K) :
        c ((p.blockSum q).matrix.mulVecLin x) =
          (p.matrix.mulVecLin (c x).1, q.matrix.mulVecLin (c x).2) := by
      change c ((Matrix.fromBlocks p.matrix 0 0 q.matrix).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm *ᵥ x) = _
      rw [Matrix.submatrix_mulVec_equiv _ _ _ finSumFinEquiv.symm,
        Matrix.fromBlocks_mulVec]
      apply Prod.ext <;> ext i <;>
        simp [hc_apply, Function.comp_def]
    have hmem (x : (p.blockSum q).image) :
        (c x.val).1 ∈ p.image ∧ (c x.val).2 ∈ q.image := by
      obtain ⟨y, hy⟩ := x.property
      rw [← hy]
      rw [hc]
      exact ⟨⟨(c y).1, rfl⟩, ⟨(c y).2, rfl⟩⟩
    let f : (p.blockSum q).image →ₗ[K] p.image × q.image := {
      toFun := fun x ↦ (⟨(c x.val).1, (hmem x).1⟩, ⟨(c x.val).2, (hmem x).2⟩)
      map_add' := fun x y ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp
      map_smul' := fun r x ↦ by apply Prod.ext <;> apply Subtype.ext <;> simp }
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
  -- Isomorphism invariance and the actual block-image decomposition kill the relations.
  apply (AddSubgroup.closure_le _).mpr
  rintro x (⟨p, q, hpq, rfl⟩ | ⟨p, q, rfl⟩)
  · obtain ⟨e⟩ := (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv p q).mp hpq
    change (FreeAbelianGroup.lift _) (_ - _) = 0
    simp [e.finrank_eq]
  · obtain ⟨e⟩ := hblock p q
    have hdim : Module.finrank K (p.blockSum q).image =
        Module.finrank K p.image + Module.finrank K q.image := by
      rw [e.finrank_eq, Module.finrank_prod]
    change (FreeAbelianGroup.lift _) (_ - _ - _) = 0
    simp [hdim, Nat.cast_add]


/-- The rank homomorphism over a field, defined by actual finite-dimensional images. -/
def kZeroRank : KZero K →+ ℤ :=
  QuotientAddGroup.lift (kZeroRelations K)
    (FreeAbelianGroup.lift (fun p : IdempotentMatrix K ↦ (Module.finrank K p.image : ℤ)))
    (fun _ hx ↦ kZeroRelations_le_ker_rank K hx)

/-- Rank on a generator is its image dimension, not its ambient matrix size. -/
theorem kZeroRank_class (p : IdempotentMatrix K) :
    kZeroRank K (kZeroClass K p) = (Module.finrank K p.image : ℤ) := by
  /- Evaluate the free-group and quotient lifts on the generator p. The image is
  finite-dimensional because it is a submodule of K raised to a finite power. -/
  exact FreeAbelianGroup.lift_apply_of _ p

/-- Over a field, rank identifies K₀ with the integers. -/
theorem kZeroRank_bijective : Function.Bijective (kZeroRank K) := by
  /- Choose a finite basis of the image of each idempotent. This identifies its class
  with that of an identity matrix of the image dimension. Direct sum then expresses
  that class as the dimension times the rank-one class. Hence rank determines every
  element. Rank-one classes and their negatives realize all integers. -/
  let c : KZero K := kZeroClass K (IdempotentMatrix.identity K 1)
  have hfull (n : ℕ) : (IdempotentMatrix.identity K n).image = ⊤ := by
    change (Matrix.mulVecLin (1 : Matrix (Fin n) (Fin n) K)).range = ⊤
    rw [Matrix.mulVecLin_one, LinearMap.range_id]
  have hdim (n : ℕ) : Module.finrank K (IdempotentMatrix.identity K n).image = n := by
    rw [hfull]
    change Module.finrank K (⊤ : Submodule K (Fin n → K)) = n
    exact (Submodule.topEquiv : (⊤ : Submodule K (Fin n → K)) ≃ₗ[K]
      (Fin n → K)).finrank_eq.trans (by simp)
  have hblock (m n : ℕ) : (IdempotentMatrix.identity K m).blockSum
      (IdempotentMatrix.identity K n) = IdempotentMatrix.identity K (m + n) := by
    dsimp only [IdempotentMatrix.blockSum, IdempotentMatrix.identity]
    congr 1
    simp [IdempotentMatrix.blockMatrix, Matrix.fromBlocks_one]
  -- Free presentations are sums of the same positive rank-one class, including rank zero.
  have hclass (n : ℕ) : kZeroClass K (IdempotentMatrix.identity K n) = n • c := by
    induction n with
    | zero =>
      have h := kZeroClass_blockSum (IdempotentMatrix.identity K 0)
        (IdempotentMatrix.identity K 0)
      rw [hblock] at h
      have hz : kZeroClass K (IdempotentMatrix.identity K 0) = 0 := by
        apply add_left_cancel
        simpa only [add_zero] using h.symm
      simpa using hz
    | succ n ih =>
      rw [← hblock n 1, kZeroClass_blockSum, ih]
      simp only [c, add_nsmul, one_nsmul]
  have hgen (p : IdempotentMatrix K) :
      kZeroClass K p = (Module.finrank K p.image) • c := by
    -- A basis identifies the actual image with the identity presentation of its dimension.
    let e : p.image ≃ₗ[K] (IdempotentMatrix.identity K (Module.finrank K p.image)).image :=
      (Module.finBasis K p.image).equivFun.trans (LinearEquiv.ofTop _ (hfull _)).symm
    calc
      kZeroClass K p = kZeroClass K
          (IdempotentMatrix.identity K (Module.finrank K p.image)) :=
        kZeroClass_eq_of_isEquivalent _ _
          ((IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr ⟨e⟩)
      _ = (Module.finrank K p.image) • c := hclass _
  let s : ℤ →+ KZero K := {
    toFun := fun z ↦ z • c
    map_zero' := zero_zsmul c
    map_add' := fun x y ↦ add_zsmul c x y }
  have hleft : s.comp (kZeroRank K) = AddMonoidHom.id _ := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change (kZeroRank K (kZeroClass K p)) • c = kZeroClass K p
    rw [kZeroRank_class]
    simpa using (hgen p).symm
  have hc : kZeroRank K c = 1 := by
    change kZeroRank K (kZeroClass K (IdempotentMatrix.identity K 1)) = 1
    rw [kZeroRank_class, hdim]
    rfl
  have hright : (kZeroRank K).comp s = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro z
    change kZeroRank K (z • c) = z
    rw [map_zsmul, hc]
    simp
  exact ⟨(show Function.LeftInverse s (kZeroRank K) from
      fun x ↦ DFunLike.congr_fun hleft x).injective,
    (show Function.RightInverse s (kZeroRank K) from
      fun x ↦ DFunLike.congr_fun hright x).surjective⟩

/-- The canonical rank isomorphism K₀(K) ≃ ℤ for a field K. -/
def kZeroRankEquiv : KZero K ≃+ ℤ :=
  AddEquiv.ofBijective (kZeroRank K) (kZeroRank_bijective K)

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]
  [CompactSpace Z] [T2Space Z]

/-- Pullback in absolute complex K⁰, induced by precomposition of continuous functions. -/
def complexKZeroPullback (f : C(X, Y)) : ComplexKZero Y →+ ComplexKZero X :=
  kZeroMap (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom

/-- Pullback reverses the order of composition. -/
theorem complexKZeroPullback_comp (f : C(X, Y)) (g : C(Y, Z)) :
    complexKZeroPullback (g.comp f) =
      (complexKZeroPullback f).comp (complexKZeroPullback g) := by
  /- Precomposition on functions reverses the order of the two base maps. Apply
  functoriality of kZeroMap to these explicit ring homomorphisms. -/
  change kZeroMap _ = (kZeroMap _).comp (kZeroMap _)
  rw [← kZeroMap_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Homotopic maps of compact Hausdorff spaces induce equal pullbacks on complex K⁰. -/
theorem complexKZeroPullback_eq_of_homotopy (f g : C(X, Y))
    (H : ContinuousMap.Homotopy f g) : complexKZeroPullback f = complexKZeroPullback g := by
  /- For an idempotent p over C(Y, ℂ), substitution along H gives a continuous
  idempotent matrix on I × X. Compactness of X turns this into a norm-continuous
  path in matrices over the Banach algebra C(X, ℂ). Nearby idempotents are conjugate;
  local conjugacy makes the conjugacy class locally constant, and connectedness
  of the interval identifies the endpoint classes. Thus the two pullbacks agree
  on every generator, and consequently on the entire Grothendieck group. -/
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro p
  change complexKZeroPullback f (kZeroClass C(Y, ℂ) p) =
    complexKZeroPullback g (kZeroClass C(Y, ℂ) p)
  simp only [complexKZeroPullback, kZeroMap_class]
  apply kZeroClass_eq_of_isEquivalent
  -- Currying the actual joint homotopy gives continuous functions in the uniform topology.
  let entry (i j : Fin p.size) : C(I, C(X, ℂ)) :=
    ((p.matrix i j).comp H.toContinuousMap).curry
  let P : C(I, Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) :=
    ⟨fun t i j ↦ entry i j t, continuous_pi fun i ↦
      continuous_pi fun j ↦ (entry i j).continuous⟩
  have hP (t : I) : P t * P t = P t := by
    exact (p.map (ContinuousMap.compRightAlgHom ℂ ℂ (H.curry t)).toRingHom).mul_self
  have hP₀ : P 0 = (p.map (ContinuousMap.compRightAlgHom ℂ ℂ f).toRingHom).matrix := by
    ext i j x
    change p.matrix i j (H (0, x)) = p.matrix i j (f x)
    rw [H.apply_zero]
  have hP₁ : P 1 = (p.map (ContinuousMap.compRightAlgHom ℂ ℂ g).toRingHom).matrix := by
    ext i j x
    change p.matrix i j (H (1, x)) = p.matrix i j (g x)
    rw [H.apply_one]
  -- The Banach-algebra homotopy theorem gives a unit conjugating the same endpoint matrices.
  have : CompleteSpace (Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) :=
    inferInstanceAs (CompleteSpace (Fin p.size → Fin p.size → C(X, ℂ)))
  obtain ⟨u, hu⟩ := exists_unit_conjugating_idempotent_path P hP
  refine ⟨P 0 * (↑(u⁻¹) : Matrix _ _ _), (u : Matrix _ _ _) * P 0, ?_, ?_, ?_, ?_⟩
  · rw [← hP₀]
    calc
      P 0 * ↑u⁻¹ * (↑u * P 0) = (P 0 * ↑u⁻¹ * ↑u) * P 0 := (mul_assoc _ _ _).symm
      _ = P 0 * P 0 := by rw [Units.inv_mul_cancel_right]
      _ = P 0 := hP 0
  · rw [← hP₁]
    calc
      ↑u * P 0 * (P 0 * ↑u⁻¹) = ↑u * (P 0 * P 0) * ↑u⁻¹ := by
        simp only [mul_assoc]
      _ = ↑u * P 0 * ↑u⁻¹ := by rw [hP 0]
      _ = P 1 := hu.symm
  · rw [← hP₀]
    change P 0 * (P 0 * (↑u⁻¹ : Matrix (Fin p.size) (Fin p.size) C(X, ℂ))) =
      P 0 * (↑u⁻¹ : Matrix (Fin p.size) (Fin p.size) C(X, ℂ))
    rw [← mul_assoc, hP 0]
  · rw [← hP₁]
    change P 1 * ((u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0) =
      (u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0
    calc
      P 1 * (↑u * P 0) = (↑u * P 0 * ↑u⁻¹) * (↑u * P 0) :=
        congrArg (fun a : Matrix (Fin p.size) (Fin p.size) C(X, ℂ) ↦
          a * ((u : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)) * P 0)) hu
      _ =
          (↑u * P 0 * ↑u⁻¹ * ↑u) * P 0 := (mul_assoc _ _ _).symm
      _ = ↑u * P 0 * P 0 := by rw [Units.inv_mul_cancel_right]
      _ = ↑u * P 0 := by rw [mul_assoc, hP 0]

/-- Rank at a point of a compact space, allowing different ranks on different components. -/
def complexKZeroRankAt (x : X) : ComplexKZero X →+ ℤ :=
  (kZeroRank ℂ).comp (kZeroMap (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)

/-- The point-space rank map is bijective; no connectedness hypothesis on other bases is used. -/
theorem complexKZeroRankAt_point_bijective :
    Function.Bijective (complexKZeroRankAt (X := PUnit) PUnit.unit) := by
  /- Evaluation identifies C(point, ℂ) with ℂ, with inverse the constant-function
  map. Functoriality transports this ring isomorphism to K₀, where the field rank
  map is bijective. The composite is exactly the displayed point-rank map. -/
  let ev : C(PUnit, ℂ) →+* ℂ := (ContinuousMap.evalAlgHom ℂ ℂ PUnit.unit).toRingHom
  let c : ℂ →+* C(PUnit, ℂ) := algebraMap ℂ C(PUnit, ℂ)
  have hcev : c.comp ev = RingHom.id C(PUnit, ℂ) := by
    ext a x
    cases x
    rfl
  have hevc : ev.comp c = RingHom.id ℂ := by
    ext z
    rfl
  -- Functoriality lifts the actual evaluation/constant inverse pair to K-zero.
  have hleft : (kZeroMap c).comp (kZeroMap ev) = AddMonoidHom.id _ := by
    rw [← kZeroMap_comp, hcev, kZeroMap_id]
  have hright : (kZeroMap ev).comp (kZeroMap c) = AddMonoidHom.id _ := by
    rw [← kZeroMap_comp, hevc, kZeroMap_id]
  have hev : Function.Bijective (kZeroMap ev) :=
    ⟨(show Function.LeftInverse (kZeroMap c) (kZeroMap ev) from
        fun x ↦ DFunLike.congr_fun hleft x).injective,
      (show Function.RightInverse (kZeroMap c) (kZeroMap ev) from
        fun x ↦ DFunLike.congr_fun hright x).surjective⟩
  exact (kZeroRank_bijective ℂ).comp hev

/-- The specified normalization K⁰(point) ≃ ℤ. -/
def complexKZeroPointEquivInt : ComplexKZero PUnit ≃+ ℤ :=
  AddEquiv.ofBijective (complexKZeroRankAt PUnit.unit) complexKZeroRankAt_point_bijective

/-- Point normalization on a virtual difference of trivial bundles of ranks m and n. -/
theorem complexKZeroPointEquivInt_sub_identity (m n : ℕ) :
    complexKZeroPointEquivInt
      (kZeroClass C(PUnit, ℂ) (IdempotentMatrix.identity C(PUnit, ℂ) m) -
        kZeroClass C(PUnit, ℂ) (IdempotentMatrix.identity C(PUnit, ℂ) n)) =
      (m : ℤ) - (n : ℤ) := by
  /- The identity matrices have full image of dimensions m and n. Evaluation at
  the point preserves them, and the rank homomorphism takes their difference to m−n.
  This fixes the positive rank-one generator used in the point index normalization. -/
  -- Evaluate the original identity matrices and compute their full image dimensions.
  rw [complexKZeroPointEquivInt, AddEquiv.ofBijective_apply, complexKZeroRankAt,
    AddMonoidHom.comp_apply, map_sub, map_sub, kZeroMap_class, kZeroMap_class,
    kZeroRank_class, kZeroRank_class]
  have hmap (k : ℕ) : Module.finrank ℂ
      ((IdempotentMatrix.identity C(PUnit, ℂ) k).map
        (ContinuousMap.evalAlgHom ℂ ℂ PUnit.unit).toRingHom).image = k := by
    change Module.finrank ℂ (Matrix.mulVecLin
      ((ContinuousMap.evalAlgHom ℂ ℂ PUnit.unit).toRingHom.mapMatrix
        (1 : Matrix (Fin k) (Fin k) C(PUnit, ℂ)))).range = k
    rw [map_one, Matrix.mulVecLin_one, LinearMap.range_id]
    simp
  rw [hmap m, hmap n]

end AtiyahSinger
