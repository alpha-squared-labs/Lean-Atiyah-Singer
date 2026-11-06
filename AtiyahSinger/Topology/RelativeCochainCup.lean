/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeSingularCohomology
public import AtiyahSinger.Topology.SingularCochainCup
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Ordinary cochains acting on the original relative cochains

Public module ID: M2059.

Hatcher, Algebraic Topology, section 3.2, pp.206--210. Relative
cochains are the dual of the original quotient chain complex C_*(X,A;R).
The canonical cokernel property identifies them with the kernel of
restriction to A. Restricting the actual front/back cochain cup product
therefore constructs C^p(X;R) × C^q(X,A;R) → C^(p+q)(X,A;R).

Every data map uses the original chain projection and its canonical
cokernel universal property. No arbitrary bilinear operation or replacement
cochain complex is supplied as an assumption. The ordinary factor is on
the left, as required by the Thom map a ↦ π*a cup U. The subset A is
arbitrary; no closedness, excision or manifold condition is imposed.
The coefficient ring retains the existing small commutative-ring scope.

The kernel/image adapters use the original relative cochain differential.
Leibniz and the coboundary ideal property provide the construction certificates
for descent to the same relative cohomology.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The original relative cochains are exactly the ordinary cochains restricting to zero on A. -/
def relativeSingularCochainEquiv (A : Set X) (n : ℕ) :
    (relativeSingularCochains R A).X n ≃ₗ[R]
      (((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f n).hom.ker := by
  -- Evaluation preserves the actual chain cokernel, so its original projection is universal.
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    (singularSubspaceChains R A)
  -- Extend each vanishing cochain uniquely through that same projection.
  let extend (φ :
      (((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f n).hom.ker) :=
    CokernelCofork.IsColimit.desc' Q φ.val (show (singularSubspaceChains R A).f n ≫ φ.val = 0
      from φ.property)
  exact
    { toFun := fun φ ↦ ⟨(relativeSingularChainsProjection R A).f n ≫ φ, by
        change (relativeSingularChains R A).X n ⟶ singularCoefficient R at φ
        change (singularSubspaceChains R A).f n ≫
            ((relativeSingularChainsProjection R A).f n ≫ φ) = 0
        have hz : (singularSubspaceChains R A).f n ≫
            (relativeSingularChainsProjection R A).f n = 0 :=
          congrArg (fun f ↦ f.f n) (cokernel.condition (singularSubspaceChains R A))
        rw [← Category.assoc, hz, zero_comp]⟩
      invFun := fun φ ↦ (extend φ).val
      left_inv := by
        -- Two relative cochains agree when their composites with the quotient projection agree.
        intro φ
        change (relativeSingularChains R A).X n ⟶ singularCoefficient R at φ
        apply Cofork.IsColimit.hom_ext Q
        exact (extend _).property
      right_inv := by
        -- The descended cochain pulls back to the prescribed ordinary cochain.
        intro φ
        apply Subtype.ext
        exact (extend φ).property
      map_add' := by
        intro φ ψ
        apply Subtype.ext
        rfl
      map_smul' := by
        intro a φ
        apply Subtype.ext
        rfl }

/-- The actual cup product vanishes on A when its right factor is a relative cochain. -/
theorem singularCochainCup_mem_relative (A : Set X) (p q : ℕ)
    (φ : (singularCochains R X).X p) (ψ : (relativeSingularCochains R A).X q) :
    ((singularCochainDualFunctor R).map (singularSubspaceChains R A).op).f (p + q)
      (singularCochainCup R X p q φ (relativeSingularCochainEquiv R A q ψ).val) = 0 := by
  /- Evaluate the restriction on each original simplex of A. Its back
  face is still a simplex of A, and the right cochain is the pullback
  of the given relative cochain along the original quotient projection.
  The subspace chain followed by this projection is zero, so that
  back-face evaluation vanishes. The actual cup formula then vanishes
  on every generator. Linearity gives the displayed restriction equality.
  No geometric property of A and no excision theorem is used. -/
  -- The same chain inclusion evaluates an ordinary cochain on the included simplex.
  let f := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
  let P := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
  have heval (k : ℕ) (χ : (singularCochains R X).X k)
      (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌)) :
      singularCochainEquiv R A k (P.f k χ) σ =
        singularCochainEquiv R X k χ (f.app (op ⦋k⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap f (singularCoefficient R)).f k) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  apply (singularCochainEquiv R A (p + q)).injective
  funext σ
  rw [heval]
  change singularCochainEquiv R X (p + q)
    ((singularCochainEquiv R X (p + q)).symm _) _ = _
  rw [LinearEquiv.apply_symm_apply]
  dsimp only
  have hvanish := congrArg
    (fun χ : (singularCochains R A).X q ↦ singularCochainEquiv R A q χ
      ((TopCat.toSSet.obj (TopCat.of A)).map (singularCupBackFace p q).op σ))
    (relativeSingularCochainEquiv R A q ψ).property
  rw [heval] at hvanish
  have hface := congrArg (fun g ↦ g σ) (f.naturality (singularCupBackFace p q).op)
  change f.app (op ⦋q⦌) ((TopCat.toSSet.obj (TopCat.of A)).map
    (singularCupBackFace p q).op σ) =
      (TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op
        (f.app (op ⦋p + q⦌) σ) at hface
  rw [← hface, hvanish]
  simp

/-- Ordinary cochains act on the same relative cochains by the actual front/back formula. -/
def relativeSingularCochainAction (A : Set X) (p q : ℕ) :
    (singularCochains R X).X p →ₗ[R]
      (relativeSingularCochains R A).X q →ₗ[R]
        (relativeSingularCochains R A).X (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ (relativeSingularCochainEquiv R A (p + q)).symm
        ⟨singularCochainCup R X p q φ (relativeSingularCochainEquiv R A q ψ).val,
          singularCochainCup_mem_relative R A p q φ ψ⟩
      map_add' := by
        intro ψ χ
        apply (relativeSingularCochainEquiv R A (p + q)).injective
        apply Subtype.ext
        simp [map_add]
      map_smul' := by
        intro a ψ
        apply (relativeSingularCochainEquiv R A (p + q)).injective
        apply Subtype.ext
        simp [map_smul] }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply (relativeSingularCochainEquiv R A (p + q)).injective
    apply Subtype.ext
    simp [map_add]
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply (relativeSingularCochainEquiv R A (p + q)).injective
    apply Subtype.ext
    simp [map_smul]

/-- Relative Leibniz uses the same unsuspended differential and the ordinary degree p sign. -/
theorem relativeSingularCochainAction_leibniz (A : Set X) (p q : ℕ)
    (φ : (singularCochains R X).X p) (ψ : (relativeSingularCochains R A).X q) :
    (relativeSingularCochains R A).d (p + q) (p + q + 1)
        (relativeSingularCochainAction R A p q φ ψ) =
      ((relativeSingularCochains R A).XIsoOfEq (Nat.add_right_comm p 1 q)).hom
          (relativeSingularCochainAction R A (p + 1) q
            ((singularCochains R X).d p (p + 1) φ) ψ) +
        (-1 : R) ^ p •
          ((relativeSingularCochains R A).XIsoOfEq (Nat.add_assoc p q 1).symm).hom
            (relativeSingularCochainAction R A p (q + 1) φ
              ((relativeSingularCochains R A).d q (q + 1) ψ)) := by
  /- Pull both sides back along the original chain quotient projection.
  This injective map is the underlying map of relativeSingularCochainEquiv
  and commutes with the original coboundaries. The desired equality is
  therefore the ordinary cochain Leibniz identity on the same two factors.
  Its sign is (-1)^p; the equality transports only reconcile degree sums.
  Injectivity returns the equality in the original relative complex. -/
  -- Pull back along the original quotient projection, whose dual is injective degreewise.
  let J := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  have haction (i j : ℕ) (a : (singularCochains R X).X i)
      (b : (relativeSingularCochains R A).X j) :
      J.f (i + j) (relativeSingularCochainAction R A i j a b) =
        singularCochainCup R X i j a (J.f j b) := by
    exact congrArg Subtype.val ((relativeSingularCochainEquiv R A (i + j)).apply_symm_apply _)
  have hd (i j : ℕ) (a : (relativeSingularCochains R A).X i) :
      J.f j ((relativeSingularCochains R A).d i j a) =
        (singularCochains R X).d i j (J.f i a) :=
    (congrArg (fun f ↦ f a) (J.comm i j)).symm
  have ht {i j : ℕ} (h : i = j) (a : (relativeSingularCochains R A).X i) :
      J.f j (((relativeSingularCochains R A).XIsoOfEq h).hom a) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i a) := by
    subst j
    rfl
  apply (relativeSingularCochainEquiv R A (p + q + 1)).injective
  apply Subtype.ext
  change J.f (p + q + 1) _ = J.f (p + q + 1) _
  rw [hd, haction, map_add, map_smul, ht, ht, haction, haction, hd]
  exact singularCochainCup_leibniz R X p q φ (J.f q ψ)

/-- The original relative cocycle kernel used in the existing homology quotient. -/
abbrev relativeSingularCocycles (A : Set X) (n : ℕ) : ModuleCat.{u} R :=
  ((relativeSingularCochains R A).sc n).moduleCatLeftHomologyData.K

/-- The image of the original relative incoming differential inside its cocycle kernel. -/
abbrev relativeSingularCoboundaries (A : Set X) (n : ℕ) :
    Submodule R (relativeSingularCocycles R A n) :=
  ((relativeSingularCochains R A).sc n).moduleCatToCycles.range

/-- The actual ordinary-relative product of cocycles is a relative cocycle. -/
theorem relativeSingularCochainAction_mem_cocycles (A : Set X) (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : relativeSingularCocycles R A q) :
    ((relativeSingularCochains R A).sc (p + q)).g
      (relativeSingularCochainAction R A p q φ.val ψ.val) = 0 := by
  /- The original outgoing differential is d(n,n+1). Apply relative
  Leibniz to the two specified kernel elements. Their differentiated
  factors vanish, so bilinearity makes both terms zero. The result is
  membership in the same relative kernel used by the homology quotient. -/
  -- Use the original next-degree isomorphisms rather than changing the kernel model.
  let φ₀ : (singularCochains R X).X p := φ.val
  let ψ₀ : (relativeSingularCochains R A).X q := ψ.val
  have hφ : (singularCochains R X).d p (p + 1) φ₀ = 0 := by
    have h : (singularCochains R X).dFrom p φ₀ = 0 := φ.property
    have h' := congrArg ((singularCochains R X).xNextIso
      (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hψ : (relativeSingularCochains R A).d q (q + 1) ψ₀ = 0 := by
    have h : (relativeSingularCochains R A).dFrom q ψ₀ = 0 := ψ.property
    have h' := congrArg ((relativeSingularCochains R A).xNextIso
      (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hproduct := relativeSingularCochainAction_leibniz R A p q φ₀ ψ₀
  rw [hφ, hψ] at hproduct
  simp only [map_zero, LinearMap.zero_apply, zero_add, smul_zero] at hproduct
  change (relativeSingularCochains R A).dFrom (p + q)
    (relativeSingularCochainAction R A p q φ₀ ψ₀) = 0
  rw [HomologicalComplex.dFrom_eq (r := show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1)
    from rfl), ModuleCat.comp_apply, hproduct, map_zero]

/-- The same ordinary-relative cup formula restricted to the original cocycle modules. -/
def relativeSingularCocycleAction (A : Set X) (p q : ℕ) :
    singularCocycles R X p →ₗ[R] relativeSingularCocycles R A q →ₗ[R]
      relativeSingularCocycles R A (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ ⟨relativeSingularCochainAction R A p q φ.val ψ.val,
        relativeSingularCochainAction_mem_cocycles R A p q φ ψ⟩
      map_add' := by
        intro ψ χ
        apply Subtype.ext
        exact (relativeSingularCochainAction R A p q φ.val).map_add ψ.val χ.val
      map_smul' := by
        intro a ψ
        apply Subtype.ext
        exact (relativeSingularCochainAction R A p q φ.val).map_smul a ψ.val }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply Subtype.ext
    exact congrArg (fun f ↦ f χ.val)
      ((relativeSingularCochainAction R A p q).map_add φ.val ψ.val)
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    exact congrArg (fun f ↦ f ψ.val)
      ((relativeSingularCochainAction R A p q).map_smul a φ.val)

/-- An ordinary or relative coboundary factor gives a relative coboundary product. -/
theorem relativeSingularCocycleAction_mem_coboundaries (A : Set X) (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : relativeSingularCocycles R A q)
    (h : φ ∈ singularCoboundaries R X p ∨ ψ ∈ relativeSingularCoboundaries R A q) :
    relativeSingularCocycleAction R A p q φ ψ ∈
      relativeSingularCoboundaries R A (p + q) := by
  /- If the coboundary factor has degree zero, its incoming differential
  in the original nonnegative complex is zero and the product vanishes.
  In positive degree choose its preimage under the original differential.
  For a left coboundary, act with that primitive on the closed relative
  factor. For a right coboundary, act with the closed ordinary factor on
  its relative primitive and multiply by (-1)^p. Relative Leibniz shows
  these are actual relative primitives for the required product.
  Thus the product lies in the displayed original image submodule,
  rather than merely becoming zero after forgetting the relative condition. -/
  -- Use the actual incoming and outgoing maps of both original complexes.
  let O : CochainComplex (ModuleCat.{u} R) ℕ := singularCochains R X
  let C : CochainComplex (ModuleCat.{u} R) ℕ := relativeSingularCochains R A
  have hclosed (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (χ : (D.sc k).moduleCatLeftHomologyData.K) : D.d k (k + 1) χ.val = 0 := by
    let v : D.X k := χ.val
    have hχ : D.dFrom k v = 0 := χ.property
    have hχ' := congrArg (D.xNextIso
      (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)).hom hχ
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at hχ'
    exact hχ'
  have hzero (D : CochainComplex (ModuleCat.{u} R) ℕ)
      (χ : (D.sc 0).moduleCatLeftHomologyData.K) (hχ : χ ∈ (D.sc 0).moduleCatToCycles.range) :
      χ = 0 := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change D.dTo 0 β = χ.val at hval
    have hd : D.dTo 0 = 0 := D.shape _ _ (by
      change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
      omega)
    rw [hd] at hval
    apply Subtype.ext
    exact hval.symm
  have hprimitive (D : CochainComplex (ModuleCat.{u} R) ℕ) (k : ℕ)
      (χ : (D.sc (k + 1)).moduleCatLeftHomologyData.K)
      (hχ : χ ∈ (D.sc (k + 1)).moduleCatToCycles.range) :
      ∃ β : D.X k, D.d k (k + 1) β = χ.val := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change D.dTo (k + 1) β = χ.val at hval
    have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
    refine ⟨(D.xPrevIso hrel).hom β, ?_⟩
    have hcomp := congrArg (fun f : D.xPrev (k + 1) ⟶ D.X (k + 1) ↦ f β)
      (D.dTo_eq hrel)
    exact hcomp.symm.trans hval
  have hboundary (D : CochainComplex (ModuleCat.{u} R) ℕ) (i j : ℕ)
      (hij : (ComplexShape.up ℕ).Rel i j)
      (χ : (D.sc j).moduleCatLeftHomologyData.K) (β : D.X i) (hβ : D.d i j β = χ.val) :
      χ ∈ (D.sc j).moduleCatToCycles.range := by
    refine ⟨(D.xPrevIso hij).inv β, ?_⟩
    apply Subtype.ext
    change D.dTo j ((D.xPrevIso hij).inv β) = χ.val
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    exact hβ
  rcases h with hφ | hψ
  · cases p with
    | zero =>
      -- Degree zero has no incoming boundary, so the left factor itself vanishes.
      rw [hzero O φ hφ]
      simp
    | succ k =>
      obtain ⟨α, hα⟩ := hprimitive O k φ hφ
      let φ₀ : O.X (k + 1) := φ.val
      let ψ₀ : C.X q := ψ.val
      change O.d k (k + 1) α = φ₀ at hα
      have hψ₀ : C.d q (q + 1) ψ₀ = 0 := hclosed C q ψ
      have hleib := relativeSingularCochainAction_leibniz R A k q α ψ₀
      change C.d (k + q) (k + q + 1) (relativeSingularCochainAction R A k q α ψ₀) = _ at hleib
      rw [hα, hψ₀] at hleib
      simp only [map_zero, smul_zero, add_zero] at hleib
      -- The cup of the actual primitive with the closed right factor is a primitive.
      apply hboundary C (k + q) ((k + 1) + q) (by change k + q + 1 = (k + 1) + q; omega)
        (relativeSingularCocycleAction R A (k + 1) q φ ψ)
        (relativeSingularCochainAction R A k q α ψ₀)
      change C.d (k + q) ((k + 1) + q) (relativeSingularCochainAction R A k q α ψ₀) =
        relativeSingularCochainAction R A (k + 1) q φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (C.XIsoOfEq (Nat.add_right_comm k 1 q)).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
      exact hleib
  · cases q with
    | zero =>
      -- The same incoming-degree-zero argument applies to the right factor.
      rw [hzero C ψ hψ]
      simp
    | succ k =>
      obtain ⟨β, hβ⟩ := hprimitive C k ψ hψ
      let φ₀ : O.X p := φ.val
      let ψ₀ : C.X (k + 1) := ψ.val
      change C.d k (k + 1) β = ψ₀ at hβ
      have hφ₀ : O.d p (p + 1) φ₀ = 0 := hclosed O p φ
      have hleib := relativeSingularCochainAction_leibniz R A p k φ₀ β
      change C.d (p + k) (p + k + 1) (relativeSingularCochainAction R A p k φ₀ β) = _ at hleib
      rw [hφ₀, hβ] at hleib
      simp only [map_zero, LinearMap.zero_apply, zero_add] at hleib
      -- The Leibniz sign is its own inverse, so it corrects this actual right primitive.
      apply hboundary C (p + k) (p + (k + 1)) (by change p + k + 1 = p + (k + 1); omega)
        (relativeSingularCocycleAction R A p (k + 1) φ ψ)
        ((-1 : R) ^ p • relativeSingularCochainAction R A p k φ₀ β)
      change C.d (p + k) (p + (k + 1)) ((-1 : R) ^ p • relativeSingularCochainAction R A p k φ₀ β) =
        relativeSingularCochainAction R A p (k + 1) φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (C.XIsoOfEq (Nat.add_assoc p k 1).symm).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom,
        map_smul, hleib, smul_smul, ← pow_add]
      have hsign : (-1 : R) ^ (p + p) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hsign, one_smul]

end AtiyahSinger
