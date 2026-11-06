/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationTensor
public import AtiyahSinger.Algebra.RepresentationGrothendieckGroup
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# The ring of finite continuous complex representations

Public module ID: M0055.

Tensor product descends to the existing split additive Grothendieck group.
The product is the unique biadditive map with the specified tensor value on
each pair of actual finite representations. The ring instance retains the
original quotient addition, negation and zero, and uses the one-dimensional
trivial representation as its unit. Dimension extends the already constructed
additive augmentation to a ring homomorphism.

Source: SG III.9, printed pp.211--212, especially the tensor-product ring
construction on p.212. No compactness, complete reducibility or injectivity
of dimension is asserted. In particular, this split Grothendieck presentation
does not silently replace direct-sum relations by nonsplit exact sequences.
The proofs retain the specified operations and their original quotient carriers.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct


set_option linter.unusedSectionVars false

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The genuine tensor product descends uniquely to a biadditive map on representation classes. -/
theorem existsUnique_representationMul :
    ∃! μ : RepresentationGrothendieckGroup G →+
        RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G,
      ∀ ρ σ : FiniteContinuousRepresentation G,
        μ (finiteRepresentationClass ρ) (finiteRepresentationClass σ) =
          finiteRepresentationClass (ρ.tensor σ) := by
  /- Stage 1: tensor actual equivariant linear equivalences and transport them
  into the specified finite product coordinates. Finite-dimensional linear
  equivalences are continuous. Tensor product distributes over the actual
  ordered direct sum in each argument, by the usual canonical intertwiners.
  Thus tensor classes respect exactly the original isomorphism and sum relations.
  Stage 2: fix the first representation and use the additive universal property
  in the second argument. Uniqueness then shows that these homomorphisms respect
  the first argument's isomorphism and direct-sum relations. Apply the universal
  property again with the additive group of additive homomorphisms as target.
  Stage 3: equality on all representation generators implies equality first
  in one argument and then in the other. This proves uniqueness of the same
  biadditive tensor product, with no cancellation or semisimplicity premise. -/
  classical
  -- It suffices to construct the actual finite-dimensional intertwiner on pure tensors.
  have htensor (ρ σ τ : FiniteContinuousRepresentation G)
      (e : ((Fin ρ.dimension → ℂ) ⊗[ℂ] (Fin σ.dimension → ℂ)) ≃ₗ[ℂ]
        (Fin τ.dimension → ℂ))
      (he : ∀ g x y, e (ρ.representation g x ⊗ₜ[ℂ] σ.representation g y) =
        τ.representation g (e (x ⊗ₜ[ℂ] y))) :
      finiteRepresentationClass (ρ.tensor σ) = finiteRepresentationClass τ := by
    apply finiteRepresentationClass_eq_of_isEquivalent
    let c := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    refine ⟨ContRepresentation.Equiv.mk (c.symm.trans e).toContinuousLinearEquiv ?_⟩
    intro g
    have hmap : e.toLinearMap.comp
        (TensorProduct.map (ρ.representation g).toLinearMap (σ.representation g).toLinearMap) =
        (τ.representation g).toLinearMap.comp e.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      exact he g x y
    apply ContinuousLinearMap.ext
    intro v
    change e (c.symm (c (TensorProduct.map (ρ.representation g).toLinearMap
      (σ.representation g).toLinearMap (c.symm v)))) = τ.representation g (e (c.symm v))
    rw [c.symm_apply_apply]
    exact DFunLike.congr_fun hmap (c.symm v)
  have hcomm (ρ σ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass (ρ.tensor σ) = finiteRepresentationClass (σ.tensor ρ) := by
    apply htensor ρ σ (σ.tensor ρ)
      ((TensorProduct.comm ℂ _ _).trans
        (FiniteContinuousRepresentation.tensorCoordinates σ.dimension ρ.dimension))
    intro g x y
    simpa only [FiniteContinuousRepresentation.tensor, LinearEquiv.trans_apply,
      TensorProduct.comm_tmul] using
      (FiniteContinuousRepresentation.tensor_tmul σ ρ g y x).symm
  have hiso₂ (ρ σ τ : FiniteContinuousRepresentation G) (h : σ.IsEquivalent τ) :
      finiteRepresentationClass (ρ.tensor σ) = finiteRepresentationClass (ρ.tensor τ) := by
    obtain ⟨e⟩ := h
    apply htensor ρ σ (ρ.tensor τ)
      ((TensorProduct.congr (LinearEquiv.refl ℂ _) e.toContinuousLinearEquiv.toLinearEquiv).trans
        (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension τ.dimension))
    intro g x y
    have he : e.toContinuousLinearEquiv (σ.representation g y) =
        τ.representation g (e.toContinuousLinearEquiv y) :=
      DFunLike.congr_fun (e.isIntertwining g) y
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply]
    change FiniteContinuousRepresentation.tensorCoordinates ρ.dimension τ.dimension
      (ρ.representation g x ⊗ₜ[ℂ] e.toContinuousLinearEquiv (σ.representation g y)) = _
    rw [he]
    exact (FiniteContinuousRepresentation.tensor_tmul ρ τ g x
      (e.toContinuousLinearEquiv y)).symm
  -- Use the exact ordered direct-sum coordinates from the original construction.
  let d (ρ σ : FiniteContinuousRepresentation G) :
      (Fin (ρ.dimension + σ.dimension) → ℂ) ≃ₗ[ℂ]
        (Fin ρ.dimension → ℂ) × (Fin σ.dimension → ℂ) :=
    ((ContinuousLinearEquiv.piCongrLeft ℂ
      (fun _ : Fin ρ.dimension ⊕ Fin σ.dimension ↦ ℂ) finSumFinEquiv.symm).trans
      (ContinuousLinearEquiv.sumPiEquivProdPi ℂ (Fin ρ.dimension) (Fin σ.dimension)
        (fun _ ↦ ℂ))).toLinearEquiv
  have hd (ρ σ : FiniteContinuousRepresentation G) (g : G)
      (v : Fin (ρ.dimension + σ.dimension) → ℂ) :
      d ρ σ ((ρ.directSum σ).representation g v) =
        (ρ.representation g (d ρ σ v).1, σ.representation g (d ρ σ v).2) := by
    change d ρ σ ((d ρ σ).symm _) = _
    exact (d ρ σ).apply_symm_apply _
  have hadd₂ (ρ σ τ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass (ρ.tensor (σ.directSum τ)) =
        finiteRepresentationClass (ρ.tensor σ) + finiteRepresentationClass (ρ.tensor τ) := by
    rw [← finiteRepresentationClass_directSum]
    let e := (TensorProduct.congr (LinearEquiv.refl ℂ _) (d σ τ)).trans
      ((TensorProduct.prodRight ℂ ℂ _ _ _).trans
        (((FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension).prodCongr
          (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension τ.dimension)).trans
          (d (ρ.tensor σ) (ρ.tensor τ)).symm))
    apply htensor ρ (σ.directSum τ) ((ρ.tensor σ).directSum (ρ.tensor τ)) e
    intro g x y
    have heval (a : Fin ρ.dimension → ℂ) (b : Fin (σ.dimension + τ.dimension) → ℂ) :
        d (ρ.tensor σ) (ρ.tensor τ) (e (a ⊗ₜ[ℂ] b)) =
          (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
            (a ⊗ₜ[ℂ] (d σ τ b).1),
            FiniteContinuousRepresentation.tensorCoordinates ρ.dimension τ.dimension
              (a ⊗ₜ[ℂ] (d σ τ b).2)) := by
      dsimp only [e]
      simp only [FiniteContinuousRepresentation.tensor, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, TensorProduct.prodRight_tmul,
        LinearEquiv.prodCongr_apply, LinearEquiv.apply_symm_apply]
    apply (d (ρ.tensor σ) (ρ.tensor τ)).injective
    rw [hd]
    erw [heval, heval, hd]
    apply Prod.ext
    · exact (FiniteContinuousRepresentation.tensor_tmul ρ σ g x (d σ τ y).1).symm
    · exact (FiniteContinuousRepresentation.tensor_tmul ρ τ g x (d σ τ y).2).symm
  have hiso₁ (ρ σ τ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ) :
      finiteRepresentationClass (ρ.tensor τ) = finiteRepresentationClass (σ.tensor τ) :=
    (hcomm ρ τ).trans ((hiso₂ τ ρ σ h).trans (hcomm σ τ).symm)
  have hadd₁ (ρ σ τ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass ((ρ.directSum σ).tensor τ) =
        finiteRepresentationClass (ρ.tensor τ) + finiteRepresentationClass (σ.tensor τ) := by
    rw [hcomm, hadd₂, hcomm τ ρ, hcomm τ σ]
  have hext
      (f g : RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G)
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = g (finiteRepresentationClass ρ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Descend in the second argument, then descend the resulting homomorphisms in the first.
  let v (ρ : FiniteContinuousRepresentation G) :
      RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G :=
    (representationGrothendieckGroup_universal_property
      (fun σ ↦ finiteRepresentationClass (ρ.tensor σ)) (hiso₂ ρ) (hadd₂ ρ)).choose
  have hv (ρ σ : FiniteContinuousRepresentation G) :
      v ρ (finiteRepresentationClass σ) = finiteRepresentationClass (ρ.tensor σ) :=
    (representationGrothendieckGroup_universal_property
      (fun σ ↦ finiteRepresentationClass (ρ.tensor σ)) (hiso₂ ρ) (hadd₂ ρ)).choose_spec.1 σ
  have hviso (ρ σ : FiniteContinuousRepresentation G) (h : ρ.IsEquivalent σ) : v ρ = v σ := by
    apply hext
    intro τ
    rw [hv, hv]
    exact hiso₁ ρ σ τ h
  have hvadd (ρ σ : FiniteContinuousRepresentation G) : v (ρ.directSum σ) = v ρ + v σ := by
    apply hext
    intro τ
    simp only [AddMonoidHom.add_apply, hv, hadd₁]
  obtain ⟨μ, hμ, hμunique⟩ := representationGrothendieckGroup_universal_property v hviso hvadd
  refine ⟨μ, ?_, ?_⟩
  · intro ρ σ
    rw [hμ]
    exact hv ρ σ
  · intro ν hν
    apply hμunique
    intro ρ
    apply hext
    intro σ
    exact (hν ρ σ).trans (hv ρ σ).symm

/-- Multiplication specified uniquely by the tensor class of every pair of generators. -/
def representationMul : RepresentationGrothendieckGroup G →+
    RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G :=
  Classical.choose (existsUnique_representationMul G).exists

/-- The specified product evaluates a pair of finite classes at their actual tensor product. -/
theorem representationMul_finiteClass (ρ σ : FiniteContinuousRepresentation G) :
    representationMul G (finiteRepresentationClass ρ) (finiteRepresentationClass σ) =
      finiteRepresentationClass (ρ.tensor σ) := by
  /- Evaluate the specification of the uniquely characterized chosen product.
  The tensor representation is precisely the actual action in the fixed ordered
  product coordinates, retaining the original two jointly continuous actions. -/
  exact (Classical.choose_spec (existsUnique_representationMul G).exists) ρ σ

/-- The class of the one-dimensional trivial action is the multiplicative unit. -/
def representationOne : RepresentationGrothendieckGroup G :=
  finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := G))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxRecDepth 2048 in
/-- The associator, symmetry and trivial-line unitor certify the specified ring operations. -/
theorem representationMul_laws :
    (∀ x y z : RepresentationGrothendieckGroup G,
      representationMul G (representationMul G x y) z =
        representationMul G x (representationMul G y z)) ∧
    (∀ x y : RepresentationGrothendieckGroup G,
      representationMul G x y = representationMul G y x) ∧
    (∀ x : RepresentationGrothendieckGroup G,
      representationMul G (representationOne G) x = x) := by
  /- Stage 1: on representation generators, the actual tensor associator and
  factor exchange are equivariant. The standard scalar unitor intertwines the
  tensor action exactly because the chosen one-dimensional action is trivial.
  Express these canonical maps in the finite coordinates; their continuity
  follows from finite dimension, and their classes agree by isomorphism invariance.
  Stage 2: use the specified generator product and extend each identity by
  additivity in all its arguments. The generator classes generate the existing
  quotient group, so the identities hold for virtual differences as well.
-/
  classical
  -- It suffices to construct the actual finite-dimensional intertwiner on pure tensors.
  have htensor (ρ σ τ : FiniteContinuousRepresentation G)
      (e : ((Fin ρ.dimension → ℂ) ⊗[ℂ] (Fin σ.dimension → ℂ)) ≃ₗ[ℂ]
        (Fin τ.dimension → ℂ))
      (he : ∀ g x y, e (ρ.representation g x ⊗ₜ[ℂ] σ.representation g y) =
        τ.representation g (e (x ⊗ₜ[ℂ] y))) :
      finiteRepresentationClass (ρ.tensor σ) = finiteRepresentationClass τ := by
    apply finiteRepresentationClass_eq_of_isEquivalent
    let c := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    refine ⟨ContRepresentation.Equiv.mk (c.symm.trans e).toContinuousLinearEquiv ?_⟩
    intro g
    have hmap : e.toLinearMap.comp
        (TensorProduct.map (ρ.representation g).toLinearMap (σ.representation g).toLinearMap) =
        (τ.representation g).toLinearMap.comp e.toLinearMap := by
      apply TensorProduct.ext'
      intro x y
      exact he g x y
    apply ContinuousLinearMap.ext
    intro v
    change e (c.symm (c (TensorProduct.map (ρ.representation g).toLinearMap
      (σ.representation g).toLinearMap (c.symm v)))) = τ.representation g (e (c.symm v))
    rw [c.symm_apply_apply]
    exact DFunLike.congr_fun hmap (c.symm v)
  -- Canonical tensor symmetry, associator and scalar unitor are actual intertwiners.
  have hcomm (ρ σ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass (ρ.tensor σ) = finiteRepresentationClass (σ.tensor ρ) := by
    apply htensor ρ σ (σ.tensor ρ)
      ((TensorProduct.comm ℂ _ _).trans
        (FiniteContinuousRepresentation.tensorCoordinates σ.dimension ρ.dimension))
    intro g x y
    simpa only [FiniteContinuousRepresentation.tensor, LinearEquiv.trans_apply,
      TensorProduct.comm_tmul] using
      (FiniteContinuousRepresentation.tensor_tmul σ ρ g y x).symm
  have hassoc (ρ σ τ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass ((ρ.tensor σ).tensor τ) =
        finiteRepresentationClass (ρ.tensor (σ.tensor τ)) := by
    let c := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension σ.dimension
    let d := FiniteContinuousRepresentation.tensorCoordinates σ.dimension τ.dimension
    let e := (TensorProduct.congr c.symm (LinearEquiv.refl ℂ _)).trans
      ((TensorProduct.assoc ℂ _ _ _).trans
        ((TensorProduct.congr (LinearEquiv.refl ℂ _) d).trans
          (FiniteContinuousRepresentation.tensorCoordinates ρ.dimension (σ.tensor τ).dimension)))
    have heval (a : Fin ρ.dimension → ℂ) (b : Fin σ.dimension → ℂ)
        (y : Fin τ.dimension → ℂ) :
        e (c (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] y) =
          FiniteContinuousRepresentation.tensorCoordinates ρ.dimension (σ.tensor τ).dimension
            (a ⊗ₜ[ℂ] d (b ⊗ₜ[ℂ] y)) := by
      dsimp only [e]
      simp only [FiniteContinuousRepresentation.tensor, LinearEquiv.trans_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply, LinearEquiv.symm_apply_apply,
        TensorProduct.assoc_tmul]
    apply htensor (ρ.tensor σ) τ (ρ.tensor (σ.tensor τ)) e
    intro g x y
    obtain ⟨w, rfl⟩ := c.surjective x
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      have hc := FiniteContinuousRepresentation.tensor_tmul ρ σ g a b
      change (ρ.tensor σ).representation g (c (a ⊗ₜ[ℂ] b)) = _ at hc
      rw [hc]
      change e (c (ρ.representation g a ⊗ₜ[ℂ] σ.representation g b) ⊗ₜ[ℂ]
        τ.representation g y) = (ρ.tensor (σ.tensor τ)).representation g
          (e (c (a ⊗ₜ[ℂ] b) ⊗ₜ[ℂ] y))
      rw [heval, heval]
      have hd := FiniteContinuousRepresentation.tensor_tmul σ τ g b y
      change (σ.tensor τ).representation g (d (b ⊗ₜ[ℂ] y)) =
        d (σ.representation g b ⊗ₜ[ℂ] τ.representation g y) at hd
      rw [← hd]
      exact (FiniteContinuousRepresentation.tensor_tmul ρ (σ.tensor τ) g a
        (d (b ⊗ₜ[ℂ] y))).symm
    | add w₁ w₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.add_tmul, h₁, h₂]
  have hone (ρ : FiniteContinuousRepresentation G) :
      finiteRepresentationClass ((FiniteContinuousRepresentation.trivial (G := G)).tensor ρ) =
        finiteRepresentationClass ρ := by
    apply htensor (FiniteContinuousRepresentation.trivial (G := G)) ρ ρ
      ((TensorProduct.congr (LinearEquiv.piUnique ℂ (fun _ : Fin 1 ↦ ℂ))
        (LinearEquiv.refl ℂ _)).trans (TensorProduct.lid ℂ _))
    intro g x y
    simp only [LinearEquiv.trans_apply, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
      TensorProduct.lid_tmul, FiniteContinuousRepresentation.trivial,
      ContRepresentation.trivial_apply, map_smul]
  have hext (f g : RepresentationGrothendieckGroup G →+
      RepresentationGrothendieckGroup G)
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = g (finiteRepresentationClass ρ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- Extend the generator identities by additivity, one argument at a time.
  refine ⟨?_, ?_, ?_⟩
  · intro x y z
    have h₃ (ρ σ : FiniteContinuousRepresentation G) :
        representationMul G (representationMul G (finiteRepresentationClass ρ)
          (finiteRepresentationClass σ)) =
        (representationMul G (finiteRepresentationClass ρ)).comp
          (representationMul G (finiteRepresentationClass σ)) := by
      apply hext
      intro τ
      simpa only [AddMonoidHom.comp_apply, representationMul_finiteClass] using hassoc ρ σ τ
    have h₂ (ρ : FiniteContinuousRepresentation G) :
        ((representationMul G).flip z).comp (representationMul G (finiteRepresentationClass ρ)) =
        (representationMul G (finiteRepresentationClass ρ)).comp
          ((representationMul G).flip z) := by
      apply hext
      intro σ
      exact DFunLike.congr_fun (h₃ ρ σ) z
    have h₁ : ((representationMul G).flip z).comp ((representationMul G).flip y) =
        (representationMul G).flip (representationMul G y z) := by
      apply hext
      intro ρ
      exact DFunLike.congr_fun (h₂ ρ) y
    exact DFunLike.congr_fun h₁ x
  · intro x y
    have hρ (ρ : FiniteContinuousRepresentation G) :
        representationMul G (finiteRepresentationClass ρ) =
          (representationMul G).flip (finiteRepresentationClass ρ) := by
      apply hext
      intro σ
      simpa only [AddMonoidHom.flip_apply, representationMul_finiteClass] using hcomm ρ σ
    have h : representationMul G y = (representationMul G).flip y := by
      apply hext
      intro ρ
      exact (DFunLike.congr_fun (hρ ρ) y).symm
    exact (DFunLike.congr_fun h x).symm
  · intro x
    have h : representationMul G (representationOne G) =
        AddMonoidHom.id (RepresentationGrothendieckGroup G) := by
      apply hext
      intro ρ
      simpa only [representationOne, representationMul_finiteClass, AddMonoidHom.id_apply] using
        hone ρ
    exact DFunLike.congr_fun h x

/-- The tensor representation ring, with the original quotient additive group unchanged. -/
instance commRingRepresentationGrothendieckGroup :
    CommRing (RepresentationGrothendieckGroup G) where
  __ := (inferInstance : AddCommGroup (RepresentationGrothendieckGroup G))
  mul := fun x y ↦ representationMul G x y
  one := representationOne G
  mul_assoc := (representationMul_laws G).1
  mul_comm := (representationMul_laws G).2.1
  one_mul := (representationMul_laws G).2.2
  mul_one x := ((representationMul_laws G).2.1 x (representationOne G)).trans
    ((representationMul_laws G).2.2 x)
  left_distrib x y z := (representationMul G x).map_add y z
  right_distrib x y z := congrArg
    (fun f : RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G ↦ f z)
    ((representationMul G).map_add x y)
  zero_mul x := congrArg
    (fun f : RepresentationGrothendieckGroup G →+ RepresentationGrothendieckGroup G ↦ f x)
    (representationMul G).map_zero
  mul_zero x := (representationMul G x).map_zero

/-- The existing dimension augmentation preserves the specified tensor product and trivial unit. -/
theorem representationDimension_multiplicative :
    (∀ x y : RepresentationGrothendieckGroup G,
      representationDimension G (x * y) =
        representationDimension G x * representationDimension G y) ∧
    representationDimension G 1 = 1 := by
  /- Stage 1: on a pair of representation classes the product is represented
  by the actual tensor model, whose dimension is definitionally the product
  of the two dimensions. Apply representationDimension_finiteClass and the
  integer cast of the natural-number product. Biadditivity extends this to
  arbitrary virtual representation classes in the existing quotient group.
  Stage 2: the specified multiplicative unit has dimension one. Evaluating
  the same dimension homomorphism on that generator proves preservation of one.
  No assertion that dimension distinguishes representations is used. -/
  have hext (f g : RepresentationGrothendieckGroup G →+ ℤ)
      (h : ∀ ρ, f (finiteRepresentationClass ρ) = g (finiteRepresentationClass ρ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- First fix a genuine representation, then extend the other argument to virtual classes.
  have hρ (ρ : FiniteContinuousRepresentation G) :
      (representationDimension G).comp (representationMul G (finiteRepresentationClass ρ)) =
        { toFun := fun y ↦ (ρ.dimension : ℤ) * representationDimension G y
          map_zero' := by simp
          map_add' := by intro y z; simp [mul_add] } := by
    apply hext
    intro σ
    simp only [AddMonoidHom.comp_apply, representationMul_finiteClass,
      representationDimension_finiteClass, FiniteContinuousRepresentation.tensor, Nat.cast_mul,
      AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  constructor
  · intro x y
    have h : (representationDimension G).comp ((representationMul G).flip y) =
        { toFun := fun z ↦ representationDimension G z * representationDimension G y
          map_zero' := by simp
          map_add' := by intro z w; simp [add_mul] } := by
      apply hext
      intro ρ
      simpa only [AddMonoidHom.comp_apply, AddMonoidHom.flip_apply,
        representationDimension_finiteClass, AddMonoidHom.coe_mk, ZeroHom.coe_mk] using
        DFunLike.congr_fun (hρ ρ) y
    exact DFunLike.congr_fun h x
  · change representationDimension G
      (finiteRepresentationClass (FiniteContinuousRepresentation.trivial (G := G))) = 1
    rw [representationDimension_finiteClass]
    rfl

/-- Dimension as a ring homomorphism, with exactly the previously constructed additive map. -/
def representationDimensionRingHom : RepresentationGrothendieckGroup G →+* ℤ where
  __ := representationDimension G
  map_one' := (representationDimension_multiplicative G).2
  map_mul' := (representationDimension_multiplicative G).1

end AtiyahSinger
