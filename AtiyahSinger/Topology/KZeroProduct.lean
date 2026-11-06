/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ProjectiveKZero
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.LinearAlgebra.TensorProduct.Matrix
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensor multiplication in the finite-projective model of K₀

Public module ID: M1923.

Tensor product of finite projective modules induces the usual
commutative, associative multiplication with the free rank-one class as unit.
The underlying matrix is the actual Kronecker product, with its product index
set reindexed by Fin. The product on K₀ is the unique biadditive map with this
specified value on every pair of idempotent generators. No unspecified ring
structure, arbitrary equivalence or index identity defines the multiplication.

Source: Hatcher, Vector Bundles and K-Theory, §2.1, p.40, Ring Structure.
That source states the geometric bundle construction. The concrete idempotent
and projective-module realization here is the algebraic form required by this
project's existing K₀ model; bundle comparison requires a separate Serre-Swan construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped Matrix TensorProduct

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

namespace IdempotentMatrix

/-- The Kronecker projection matrix, with its actual product indices reindexed by Fin. -/
def tensorMatrix (p q : IdempotentMatrix R) :
    Matrix (Fin (p.size * q.size)) (Fin (p.size * q.size)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Matrix.kronecker p.matrix q.matrix)

/-- The Kronecker projection is idempotent; this certifies the concrete construction. -/
theorem tensorMatrix_mul_self (p q : IdempotentMatrix R) :
    tensorMatrix p q * tensorMatrix p q = tensorMatrix p q := by
  /- Stage 1: matrix multiplication of two Kronecker products factors as
  the Kronecker product of the two matrix products. Commutativity of R permits
  interchanging the middle scalar entries in each finite sum.
  Stage 2: substitute p²=p and q²=q, then transport matrix multiplication
  through finProdFinEquiv. This also covers either ambient dimension zero. -/
  simp only [tensorMatrix, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.kronecker,
    ← Matrix.mul_kronecker_mul, p.mul_self, q.mul_self]

/-- The specified finite idempotent presenting the tensor product of two projective modules. -/
def tensor (p q : IdempotentMatrix R) : IdempotentMatrix R where
  size := p.size * q.size
  matrix := p.tensorMatrix q
  mul_self := p.tensorMatrix_mul_self q

/-- The image of the Kronecker projection is the tensor product of the original image modules. -/
theorem nonempty_tensor_image_linearEquiv (p q : IdempotentMatrix R) :
    Nonempty ((p.tensor q).image ≃ₗ[R] p.image ⊗[R] q.image) := by
  /- Stage 1: identify the tensor product of the two finite free ambient
  modules with functions on their product index set, then use finProdFinEquiv.
  TensorProduct.toMatrix_map identifies the displayed matrix with p ⊗ q.
  Stage 2: each projection splits through its image inclusion and retraction.
  Tensoring those two pairs gives inverse maps between the actual image of
  p ⊗ q and image(p) ⊗ image(q). No exactness assertion for an
  arbitrary tensor product, field assumption or rank equality is needed. -/
  -- Standard tensor coordinates preserve the specified Kronecker matrix and Fin reindexing.
  let bp := Pi.basisFun R (Fin p.size)
  let bq := Pi.basisFun R (Fin q.size)
  let b := (bp.tensorProduct bq).reindex finProdFinEquiv
  let e := b.equivFun
  have hmat : LinearMap.toMatrix b b (TensorProduct.map p.matrix.mulVecLin q.matrix.mulVecLin) =
      p.tensorMatrix q := by
    have h := TensorProduct.toMatrix_map bp bq bp bq p.matrix.mulVecLin q.matrix.mulVecLin
    have hp : LinearMap.toMatrix bp bp p.matrix.mulVecLin = p.matrix :=
      LinearMap.toMatrix'_toLin' p.matrix
    have hq : LinearMap.toMatrix bq bq q.matrix.mulVecLin = q.matrix :=
      LinearMap.toMatrix'_toLin' q.matrix
    rw [hp, hq] at h
    ext i j
    simpa [b, IdempotentMatrix.tensorMatrix, LinearMap.toMatrix_apply,
      Matrix.reindex_apply, Module.Basis.repr_reindex_apply] using
      congrFun (congrFun h (finProdFinEquiv.symm i)) (finProdFinEquiv.symm j)
  have hcoord (x : (Fin p.size → R) ⊗[R] (Fin q.size → R)) :
      (p.tensor q).matrix.mulVecLin (e x) =
        e (TensorProduct.map p.matrix.mulVecLin q.matrix.mulVecLin x) := by
    have h := LinearMap.toMatrix_mulVec_repr b b
      (TensorProduct.map p.matrix.mulVecLin q.matrix.mulVecLin) x
    rw [hmat] at h
    exact h
  -- Each original image is a retract; tensor the inclusion and the retraction.
  let proj (r : IdempotentMatrix R) : (Fin r.size → R) →ₗ[R] r.image :=
    r.matrix.mulVecLin.rangeRestrict
  have hrestrict (r : IdempotentMatrix R) (x : r.image) : proj r x = x := by
    apply Subtype.ext
    obtain ⟨y, hy⟩ := x.property
    change r.matrix.mulVecLin (x : Fin r.size → R) = x
    rw [← hy, ← LinearMap.comp_apply, ← Matrix.mulVecLin_mul, r.mul_self]
  let I : p.image ⊗[R] q.image →ₗ[R] (Fin (p.size * q.size) → R) :=
    e.toLinearMap.comp (TensorProduct.map p.image.subtype q.image.subtype)
  let F : (Fin (p.size * q.size) → R) →ₗ[R] p.image ⊗[R] q.image :=
    (TensorProduct.map (proj p) (proj q)).comp e.symm.toLinearMap
  have hFI : F.comp I = LinearMap.id := by
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change TensorProduct.map (proj p) (proj q) (e.symm (e
      (TensorProduct.map p.image.subtype q.image.subtype (x ⊗ₜ[R] y)))) = x ⊗ₜ[R] y
    rw [e.symm_apply_apply, TensorProduct.map_tmul, TensorProduct.map_tmul,
      Submodule.subtype_apply, Submodule.subtype_apply, hrestrict, hrestrict]
  have hIF : I.comp F = (p.tensor q).matrix.mulVecLin := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := e.surjective x
    change e (TensorProduct.map p.image.subtype q.image.subtype
      (TensorProduct.map (proj p) (proj q) (e.symm (e z)))) =
        (p.tensor q).matrix.mulVecLin (e z)
    rw [e.symm_apply_apply]
    have hc : (TensorProduct.map p.image.subtype q.image.subtype).comp
        (TensorProduct.map (proj p) (proj q)) =
          TensorProduct.map p.matrix.mulVecLin q.matrix.mulVecLin := by
      rw [← TensorProduct.map_comp]
      rfl
    rw [← LinearMap.comp_apply, hc]
    exact (hcoord z).symm
  have hfix (x : (p.tensor q).image) : I (F x.val) = x.val := by
    exact (DFunLike.congr_fun hIF x.val).trans
      (congrArg Subtype.val (hrestrict (p.tensor q) x))
  -- Restrict to the actual Kronecker image, where the split maps are inverse.
  refine ⟨LinearEquiv.ofBijective (F.comp (p.tensor q).image.subtype) ⟨?_, ?_⟩⟩
  · intro x y h
    apply Subtype.ext
    exact (hfix x).symm.trans ((congrArg I h).trans (hfix y))
  · intro x
    have hmem : I x ∈ (p.tensor q).image := by
      refine ⟨I x, ?_⟩
      rw [← hIF]
      change I (F (I x)) = I x
      exact congrArg I (DFunLike.congr_fun hFI x)
    refine ⟨⟨I x, hmem⟩, ?_⟩
    exact DFunLike.congr_fun hFI x

end IdempotentMatrix

attribute [local instance] IdempotentMatrix.finite_image IdempotentMatrix.projective_image

set_option backward.isDefEq.respectTransparency.types false in
/-- The tensor product on generators descends to one uniquely specified biadditive K₀ map. -/
theorem existsUnique_kZeroMul (R : Type u) [CommRing R] :
    ∃! μ : KZero R →+ KZero R →+ KZero R,
      ∀ p q : IdempotentMatrix R,
        μ (kZeroClass R p) (kZeroClass R q) = kZeroClass R (p.tensor q) := by
  /- Stage 1: tensoring rectangular equivalences gives rectangular
  equivalences of the displayed Kronecker projections. Tensor product of
  image modules distributes over the actual block sum in each variable,
  so both defining K₀ relations are killed in each argument separately.
  Stage 2: for a fixed generator in the first argument, use the existing
  Grothendieck universal property in the second argument. Its uniqueness
  shows that these resulting additive homomorphisms respect isomorphism
  and block-sum relations in the first argument as well.
  Stage 3: apply the same universal property with the additive group of
  homomorphisms as target. Two resulting biadditive maps agreeing on all
  generator pairs agree first on the second K₀ argument, then on the first.
  Thus the displayed characterization determines one actual product. -/
  -- Block coordinates identify the original direct-sum image before tensoring.
  have hblock (p q : IdempotentMatrix R) :
      Nonempty ((p.blockSum q).image ≃ₗ[R] p.image × q.image) := by
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
  -- Identify every generator product with the class of its actual tensor image.
  have hclass (p q : IdempotentMatrix R) : kZeroClass R (p.tensor q) =
      projectiveModuleKZeroClass R (p.image ⊗[R] q.image) := by
    obtain ⟨e⟩ := p.nonempty_tensor_image_linearEquiv q
    exact (projectiveModuleKZeroClass_image (p.tensor q)).symm.trans
      (projectiveModuleKZeroClass_eq_of_linearEquiv e)
  have hiso₁ (p p' q : IdempotentMatrix R) (h : p.IsEquivalent p') :
      kZeroClass R (p.tensor q) = kZeroClass R (p'.tensor q) := by
    obtain ⟨e⟩ := (p.isEquivalent_iff_nonempty_linearEquiv p').mp h
    rw [hclass, hclass]
    exact projectiveModuleKZeroClass_eq_of_linearEquiv
      (TensorProduct.congr e (LinearEquiv.refl R q.image))
  have hiso₂ (p q q' : IdempotentMatrix R) (h : q.IsEquivalent q') :
      kZeroClass R (p.tensor q) = kZeroClass R (p.tensor q') := by
    obtain ⟨e⟩ := (q.isEquivalent_iff_nonempty_linearEquiv q').mp h
    rw [hclass, hclass]
    exact projectiveModuleKZeroClass_eq_of_linearEquiv
      (TensorProduct.congr (LinearEquiv.refl R p.image) e)
  have hadd₁ (p p' q : IdempotentMatrix R) :
      kZeroClass R ((p.blockSum p').tensor q) =
        kZeroClass R (p.tensor q) + kZeroClass R (p'.tensor q) := by
    obtain ⟨e⟩ := hblock p p'
    rw [hclass, hclass, hclass]
    calc
      _ = projectiveModuleKZeroClass R
          ((p.image ⊗[R] q.image) × (p'.image ⊗[R] q.image)) :=
        projectiveModuleKZeroClass_eq_of_linearEquiv
          ((TensorProduct.congr e (LinearEquiv.refl R q.image)).trans
            (TensorProduct.prodLeft R R p.image p'.image q.image))
      _ = _ := projectiveModuleKZeroClass_prod _ _
  have hadd₂ (p q q' : IdempotentMatrix R) :
      kZeroClass R (p.tensor (q.blockSum q')) =
        kZeroClass R (p.tensor q) + kZeroClass R (p.tensor q') := by
    obtain ⟨e⟩ := hblock q q'
    rw [hclass, hclass, hclass]
    calc
      _ = projectiveModuleKZeroClass R
          ((p.image ⊗[R] q.image) × (p.image ⊗[R] q'.image)) :=
        projectiveModuleKZeroClass_eq_of_linearEquiv
          ((TensorProduct.congr (LinearEquiv.refl R p.image) e).trans
            (TensorProduct.prodRight R R p.image q.image q'.image))
      _ = _ := projectiveModuleKZeroClass_prod _ _
  have hext {A : Type u} [AddCommGroup A] (f g : KZero R →+ A)
      (h : ∀ p, f (kZeroClass R p) = g (kZeroClass R p)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Descend separately in the second variable, then in the first.
  let v (p : IdempotentMatrix R) : KZero R →+ KZero R :=
    (kZero_universal_property (fun q ↦ kZeroClass R (p.tensor q))
      (hiso₂ p) (hadd₂ p)).choose
  have hv (p q : IdempotentMatrix R) :
      v p (kZeroClass R q) = kZeroClass R (p.tensor q) :=
    (kZero_universal_property (fun q ↦ kZeroClass R (p.tensor q))
      (hiso₂ p) (hadd₂ p)).choose_spec.1 q
  have hviso (p p' : IdempotentMatrix R) (h : p.IsEquivalent p') : v p = v p' := by
    apply hext
    intro q
    rw [hv, hv]
    exact hiso₁ p p' q h
  have hvadd (p p' : IdempotentMatrix R) : v (p.blockSum p') = v p + v p' := by
    apply hext
    intro q
    simp only [AddMonoidHom.add_apply, hv, hadd₁]
  obtain ⟨μ, hμ, hμunique⟩ := kZero_universal_property v hviso hvadd
  refine ⟨μ, ?_, ?_⟩
  · intro p q
    rw [hμ]
    exact hv p q
  · intro ν hν
    apply hμunique
    intro p
    apply hext
    intro q
    exact (hν p q).trans (hv p q).symm

/-- Tensor multiplication on K₀, chosen by its unique value on every generator pair. -/
def kZeroMul (R : Type u) [CommRing R] : KZero R →+ KZero R →+ KZero R :=
  Classical.choose (existsUnique_kZeroMul R).exists

/-- Tensor multiplication of projective classes is represented by the actual Kronecker matrix. -/
theorem kZeroMul_class (p q : IdempotentMatrix R) :
    kZeroMul R (kZeroClass R p) (kZeroClass R q) = kZeroClass R (p.tensor q) := by
  /- Apply the specification of the uniquely characterized chosen product.
  Its value uses precisely p.tensor q, including the fixed index reindexing. -/
  exact (Classical.choose_spec (existsUnique_kZeroMul R).exists) p q

/-- Symmetry of tensor product gives commutativity of the specified multiplication on K₀. -/
theorem kZeroMul_comm (x y : KZero R) : kZeroMul R x y = kZeroMul R y x := by
  /- Stage 1: on generator pairs, switching the tensor factors permutes the
  finite product indices and identifies the two projective image modules.
  The corresponding K₀ classes are equal by isomorphism invariance.
  Stage 2: extend equality by additivity in each variable through the
  Grothendieck presentation. No multiplication structure is assumed on K₀. -/
  have hext {A : Type u} [AddCommGroup A] (f g : KZero R →+ A)
      (h : ∀ p, f (kZeroClass R p) = g (kZeroClass R p)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have h : kZeroMul R = (kZeroMul R).flip := by
    apply hext
    intro p
    apply hext
    intro q
    simp only [AddMonoidHom.flip_apply, kZeroMul_class]
    obtain ⟨epq⟩ := p.nonempty_tensor_image_linearEquiv q
    obtain ⟨eqp⟩ := q.nonempty_tensor_image_linearEquiv p
    apply kZeroClass_eq_of_isEquivalent
    apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
    exact ⟨epq.trans ((TensorProduct.comm R p.image q.image).trans eqp.symm)⟩
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

/-- Associativity of tensor product gives associativity of the specified K₀ multiplication. -/
theorem kZeroMul_assoc (x y z : KZero R) :
    kZeroMul R (kZeroMul R x y) z = kZeroMul R x (kZeroMul R y z) := by
  /- Stage 1: the two iterated Kronecker projections represent
  (image(p) ⊗ image(q)) ⊗ image(r) and image(p) ⊗ (image(q) ⊗ image(r)).
  The tensor associator identifies them despite different Fin index types.
  Stage 2: use kZeroMul_class and isomorphism invariance on generator
  triples, then extend by additivity successively in all three variables. -/
  have hext {A : Type u} [AddCommGroup A] (f g : KZero R →+ A)
      (h : ∀ p, f (kZeroClass R p) = g (kZeroClass R p)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Prove the tensor associator identity on triples of actual matrix images.
  have hgen (p q r : IdempotentMatrix R) :
      kZeroClass R ((p.tensor q).tensor r) = kZeroClass R (p.tensor (q.tensor r)) := by
    obtain ⟨epq⟩ := p.nonempty_tensor_image_linearEquiv q
    obtain ⟨eqr⟩ := q.nonempty_tensor_image_linearEquiv r
    obtain ⟨el⟩ := (p.tensor q).nonempty_tensor_image_linearEquiv r
    obtain ⟨er⟩ := p.nonempty_tensor_image_linearEquiv (q.tensor r)
    apply kZeroClass_eq_of_isEquivalent
    apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
    exact ⟨el.trans ((TensorProduct.congr epq (LinearEquiv.refl R r.image)).trans
      ((TensorProduct.assoc R p.image q.image r.image).trans
        ((TensorProduct.congr (LinearEquiv.refl R p.image) eqr.symm).trans er.symm)))⟩
  -- Additive-homomorphism extensionality extends the three variables in order.
  have h₃ (p q : IdempotentMatrix R) :
      kZeroMul R (kZeroMul R (kZeroClass R p) (kZeroClass R q)) =
        (kZeroMul R (kZeroClass R p)).comp (kZeroMul R (kZeroClass R q)) := by
    apply hext
    intro r
    simpa only [AddMonoidHom.comp_apply, kZeroMul_class] using hgen p q r
  have h₂ (p : IdempotentMatrix R) :
      ((kZeroMul R).flip z).comp (kZeroMul R (kZeroClass R p)) =
        (kZeroMul R (kZeroClass R p)).comp ((kZeroMul R).flip z) := by
    apply hext
    intro q
    exact DFunLike.congr_fun (h₃ p q) z
  have h₁ : ((kZeroMul R).flip z).comp ((kZeroMul R).flip y) =
      (kZeroMul R).flip (kZeroMul R y z) := by
    apply hext
    intro p
    exact DFunLike.congr_fun (h₂ p) y
  exact DFunLike.congr_fun h₁ x

/-- The class of the free rank-one module is the multiplicative unit. -/
theorem kZeroMul_one_left (x : KZero R) :
    kZeroMul R (kZeroClass R (IdempotentMatrix.identity R 1)) x = x := by
  /- The identity matrix of size one presents R. The tensor unit
  equivalence R ⊗ image(p) ≃ image(p) identifies generator classes.
  Extend through the additive presentation; commutativity gives the right
  unit law as well. No choice of a basis of image(p) or nontriviality of R
  is assumed. The zero ring is included. -/
  -- The one-by-one identity projection has its entire ambient module as image.
  let e : (IdempotentMatrix.identity R 1).image ≃ₗ[R] (Fin 1 → R) :=
    LinearEquiv.ofBijective (IdempotentMatrix.identity R 1).image.subtype
      ⟨Subtype.val_injective, by
        intro f
        refine ⟨⟨f, ?_⟩, rfl⟩
        refine ⟨f, ?_⟩
        exact Matrix.one_mulVec f⟩
  let eunit := e.trans (LinearEquiv.funUnique (Fin 1) R R)
  have h : kZeroMul R (kZeroClass R (IdempotentMatrix.identity R 1)) =
      AddMonoidHom.id (KZero R) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    change kZeroMul R (kZeroClass R (IdempotentMatrix.identity R 1))
      (kZeroClass R p) = kZeroClass R p
    rw [kZeroMul_class]
    obtain ⟨ep⟩ := (IdempotentMatrix.identity R 1).nonempty_tensor_image_linearEquiv p
    apply kZeroClass_eq_of_isEquivalent
    apply (IdempotentMatrix.isEquivalent_iff_nonempty_linearEquiv _ _).mpr
    exact ⟨ep.trans ((TensorProduct.congr eunit (LinearEquiv.refl R p.image)).trans
      (TensorProduct.lid R p.image))⟩
  exact DFunLike.congr_fun h x

/-- Extension of scalars preserves the specified tensor multiplication on K₀. -/
theorem kZeroMap_mul (φ : R →+* S) (x y : KZero R) :
    kZeroMap φ (kZeroMul R x y) = kZeroMul S (kZeroMap φ x) (kZeroMap φ y) := by
  /- Stage 1: applying φ entrywise to the reindexed Kronecker matrix gives
  the same matrix as taking the tensor product of p.map φ and q.map φ.
  Ring-homomorphism preservation of multiplication identifies all entries.
  Stage 2: evaluate both sides on generator pairs with kZeroMap_class and
  kZeroMul_class, then extend by additivity. This is compatibility with
  the already fixed scalar-extension map, not existence of some ring map. -/
  -- Entrywise scalar extension commutes with the same Fin-indexed Kronecker matrix.
  have htensor (p q : IdempotentMatrix R) :
      (p.tensor q).map φ = (p.map φ).tensor (q.map φ) := by
    dsimp only [IdempotentMatrix.map, IdempotentMatrix.tensor]
    congr 1
    ext i j
    simp only [IdempotentMatrix.tensorMatrix, Matrix.reindex_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, map_mul]
  -- Both sides are biadditive, so generator pairs determine their equality.
  have h : (kZeroMul R).compr₂ (kZeroMap φ) =
      ((kZeroMul S).compl₂ (kZeroMap φ)).comp (kZeroMap φ) := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro p
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    intro q
    change kZeroMap φ (kZeroMul R (kZeroClass R p) (kZeroClass R q)) =
      kZeroMul S (kZeroMap φ (kZeroClass R p)) (kZeroMap φ (kZeroClass R q))
    simp only [kZeroMul_class, kZeroMap_class, htensor]
  exact DFunLike.congr_fun (DFunLike.congr_fun h x) y

end AtiyahSinger
