/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportedThomAction

/-!
# Associativity of the genuine relative union cup product

Public module ID: M2073.

The three factors retain their original relative conditions. A common quotient
by chains small in the three open subspaces compares both binary union products.
The original Alexander--Whitney product is associative on that quotient, and
the original small-chain homotopy equivalence detects equality of its classes.

Source: Hatcher, Algebraic Topology, Section 3.2, the relative cup product.
The auxiliary quotient adapters implement the common small-chain comparison;
they do not introduce an additional cohomology theory or change any cup factor.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory HomologicalComplex Limits Opposite
open scoped Simplicial

universe u

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

private theorem smallSubspace_comp_zero (Z : Set X) (𝒰 : Set (Set X)) (n : ℕ)
    (N : ModuleCat.{u} R) (φ : (singularChains R X).X n ⟶ N)
    (hφ : ∀ U ∈ 𝒰, (singularSubspaceChains R U).f n ≫ φ = 0) :
    ((smallSingularChainsInclusion R
      ((fun U : Set X ↦ (Subtype.val : Z → X) ⁻¹' U) '' 𝒰) ≫
        singularSubspaceChains R Z).f n) ≫ φ = 0 := by
  -- Every small simplex lifts to its actual member of the specified cover.
  let V := (fun U : Set X ↦ (Subtype.val : Z → X) ⁻¹' U) '' 𝒰
  let inc (U : Set X) := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(U, X)))
  apply SSet.chainComplex_hom_ext
  intro σ
  obtain ⟨W, ⟨U, hU, rfl⟩, hσ⟩ := σ.property
  let τX := (inc Z).app (op ⦋n⦌) σ.val
  have hτX : Set.range ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τX) ⊆ U := by
    rintro _ ⟨t, rfl⟩
    exact hσ ⟨t, rfl⟩
  let τ : C(Convexity.StdSimplex ℝ (Fin (n + 1)), U) :=
    ⟨fun t ↦ ⟨(TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τX t, hτX ⟨t, rfl⟩⟩,
      ((TopCat.of X).toSSetObjEquiv (op ⦋n⦌) τX).continuous.subtype_mk _⟩
  let η := ((TopCat.of U).toSSetObjEquiv (op ⦋n⦌)).symm τ
  have hη : (inc U).app (op ⦋n⦌) η = τX := rfl
  change (smallSingularSet V).toSSet.ιChainComplex σ ≫
    (((SSet.chainComplexMap (smallSingularSet V).ι (singularCoefficient R)).f n ≫
      (SSet.chainComplexMap (inc Z) (singularCoefficient R)).f n) ≫ φ) = _
  rw [← Category.assoc, ← Category.assoc, SSet.ι_chainComplexMap_f,
    SSet.ι_chainComplexMap_f]
  change (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex τX ≫ φ = _
  rw [← hη, ← SSet.ι_chainComplexMap_f]
  rw [Category.assoc]
  change (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex η ≫
    ((singularSubspaceChains R U).f n ≫ φ) = _
  rw [hφ U hU, comp_zero, comp_zero]

/-- The actual dual of a chain cokernel, viewed in the original cochains.
This private adapter is used only to factor products through the common small quotient. -/
private def quotientCochainEquiv {C D : ChainComplex (ModuleCat.{u} R) ℕ}
    (f : C ⟶ D) (n : ℕ) :
    ((singularCochainDualFunctor R).obj (op (cokernel f))).X n ≃ₗ[R]
      (((singularCochainDualFunctor R).map f.op).f n).hom.ker := by
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n) f
  let extend (φ : (((singularCochainDualFunctor R).map f.op).f n).hom.ker) :=
    CokernelCofork.IsColimit.desc' Q φ.val
      (show f.f n ≫ φ.val = 0 from φ.property)
  exact
    { toFun := fun φ ↦ ⟨(cokernel.π f).f n ≫ φ, by
        change f.f n ≫ ((cokernel.π f).f n ≫ φ) = 0
        have hz : f.f n ≫ (cokernel.π f).f n = 0 :=
          congrArg (fun g ↦ g.f n) (cokernel.condition f)
        rw [← Category.assoc, hz, zero_comp]⟩
      invFun := fun φ ↦ (extend φ).val
      left_inv := by
        intro φ
        apply Cofork.IsColimit.hom_ext Q
        exact (extend _).property
      right_inv := by
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

section QuotientCup

variable {S : ChainComplex (ModuleCat.{u} R) ℕ}
  {C D : CochainComplex (ModuleCat.{u} R) ℕ}
  (f : S ⟶ singularChains R X) (P : C ⟶ singularCochains R X)
  (Q : D ⟶ singularCochains R X)
  (hvanish : ∀ (p q : ℕ) (a : C.X p) (b : D.X q),
    f.f (p + q) ≫ singularCochainCup R X p q (P.f p a) (Q.f q b) = 0)

/-- Factor the specified cochain product through a chain quotient that it annihilates. -/
private def quotientCochainCup (p q : ℕ) :
    C.X p →ₗ[R] D.X q →ₗ[R]
      ((singularCochainDualFunctor R).obj (op (cokernel f))).X (p + q) := by
  let J := (singularCochainDualFunctor R).map (cokernel.π f).op
  let μ := ((singularCochainCup R X p q).compl₂ (Q.f q).hom).comp (P.f p).hom
  have hJ : Function.Injective (J.f (p + q)) := by
    intro a b h
    apply (quotientCochainEquiv R f (p + q)).injective
    exact Subtype.ext h
  apply μ.codRestrict₂ (J.f (p + q)).hom hJ
  intro a b
  refine ⟨(quotientCochainEquiv R f (p + q)).symm ⟨μ a b, hvanish p q a b⟩, ?_⟩
  exact congrArg Subtype.val ((quotientCochainEquiv R f (p + q)).apply_symm_apply _)

private theorem quotientCochainCup_to_ordinary (p q : ℕ) (a : C.X p) (b : D.X q) :
    (((singularCochainDualFunctor R).map (cokernel.π f).op).f (p + q))
      (quotientCochainCup R f P Q hvanish p q a b) =
        singularCochainCup R X p q (P.f p a) (Q.f q b) := by
  exact LinearMap.codRestrict₂_apply _ _ _ _ a b

private theorem quotientCochainCup_leibniz (p q : ℕ) (a : C.X p) (b : D.X q) :
    let T := (singularCochainDualFunctor R).obj (op (cokernel f))
    T.d (p + q) (p + q + 1) (quotientCochainCup R f P Q hvanish p q a b) =
      (T.XIsoOfEq (Nat.add_right_comm p 1 q)).hom
          (quotientCochainCup R f P Q hvanish (p + 1) q (C.d p (p + 1) a) b) +
        (-1 : R) ^ p • (T.XIsoOfEq (Nat.add_assoc p q 1).symm).hom
          (quotientCochainCup R f P Q hvanish p (q + 1) a (D.d q (q + 1) b)) := by
  let T := (singularCochainDualFunctor R).obj (op (cokernel f))
  let J := (singularCochainDualFunctor R).map (cokernel.π f).op
  have hd {U V : CochainComplex (ModuleCat.{u} R) ℕ} (G : U ⟶ V)
      (i j : ℕ) (c : U.X i) : G.f j (U.d i j c) = V.d i j (G.f i c) :=
    (congrArg (fun g ↦ g c) (G.comm i j)).symm
  have ht {i j : ℕ} (h : i = j) (c : T.X i) :
      J.f j ((T.XIsoOfEq h).hom c) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i c) := by
    subst j
    rfl
  apply (quotientCochainEquiv R f (p + q + 1)).injective
  apply Subtype.ext
  change J.f (p + q + 1) _ = J.f (p + q + 1) _
  rw [hd, quotientCochainCup_to_ordinary, map_add, map_smul, ht, ht,
    quotientCochainCup_to_ordinary, quotientCochainCup_to_ordinary, hd, hd]
  exact singularCochainCup_leibniz R X p q (P.f p a) (Q.f q b)

end QuotientCup

section CocycleProducts

private def cochainClass (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (C.sc n).moduleCatLeftHomologyData.K →ₗ[R] C.homology n :=
  ((C.sc n).moduleCatHomologyIso.inv.hom).comp (C.sc n).moduleCatToCycles.range.mkQ

private theorem cochainCocycle_closed (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ)
    (a : (C.sc n).moduleCatLeftHomologyData.K) : C.d n (n + 1) a.val = 0 := by
  have ha : C.dFrom n a.val = 0 := a.property
  have h := congrArg
    (C.xNextIso (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)).hom ha
  rw [← ModuleCat.comp_apply, dFrom_comp_xNextIso, map_zero] at h
  exact h

private theorem cochainClass_surjective (C : CochainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Function.Surjective (cochainClass R C n) := by
  intro x
  obtain ⟨a, ha⟩ := (C.sc n).moduleCatToCycles.range.mkQ_surjective
    ((C.sc n).moduleCatHomologyIso.hom x)
  refine ⟨a, ?_⟩
  change (C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a) = x
  rw [ha, Iso.hom_inv_id_apply]

private theorem cochainClass_map {C D : CochainComplex (ModuleCat.{u} R) ℕ}
    (F : C ⟶ D) (n : ℕ) (a : (C.sc n).moduleCatLeftHomologyData.K)
    (b : (D.sc n).moduleCatLeftHomologyData.K) (h : F.f n a.val = b.val) :
    homologyMap F n (cochainClass R C n a) = cochainClass R D n b := by
  let S := (shortComplexFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).map F
  let G := ShortComplex.leftHomologyMapData S
    (C.sc n).moduleCatLeftHomologyData (D.sc n).moduleCatLeftHomologyData
  have hcycles : G.φK a = b := by
    apply Subtype.ext
    exact (congrArg (fun f ↦ f a) G.commi).trans h
  have hquot := congrArg (fun f ↦ f a) G.commπ
  change G.φH ((C.sc n).moduleCatToCycles.range.mkQ a) =
    (D.sc n).moduleCatToCycles.range.mkQ (G.φK a) at hquot
  rw [hcycles] at hquot
  have hmap := G.homologyMap_eq
  change homologyMap F n = _ at hmap
  rw [hmap]
  change (D.sc n).moduleCatHomologyIso.inv
    (G.φH ((C.sc n).moduleCatHomologyIso.hom
      ((C.sc n).moduleCatHomologyIso.inv ((C.sc n).moduleCatToCycles.range.mkQ a)))) = _
  rw [Iso.inv_hom_id_apply, hquot]
  rfl

private theorem cochainClass_transport (C : CochainComplex (ModuleCat.{u} R) ℕ)
    (n m : ℕ) (h : n = m) (a : (C.sc n).moduleCatLeftHomologyData.K)
    (b : (C.sc m).moduleCatLeftHomologyData.K) (hab : (C.XIsoOfEq h).hom a.val = b.val) :
    (eqToIso (congrArg (fun k ↦ C.homology k) h)).hom (cochainClass R C n a) =
      cochainClass R C m b := by
  subst m
  change a.val = b.val at hab
  have heq : a = b := Subtype.ext hab
  subst b
  rfl

variable {C D T : CochainComplex (ModuleCat.{u} R) ℕ}
  (μ : ∀ p q : ℕ, C.X p →ₗ[R] D.X q →ₗ[R] T.X (p + q))
  (hleibniz : ∀ (p q : ℕ) (a : C.X p) (b : D.X q),
    T.d (p + q) (p + q + 1) (μ p q a b) =
      (T.XIsoOfEq (Nat.add_right_comm p 1 q)).hom (μ (p + 1) q (C.d p (p + 1) a) b) +
        (-1 : R) ^ p • (T.XIsoOfEq (Nat.add_assoc p q 1).symm).hom
          (μ p (q + 1) a (D.d q (q + 1) b)))

private def cochainCupCycles (p q : ℕ) :
    (C.sc p).moduleCatLeftHomologyData.K →ₗ[R]
      (D.sc q).moduleCatLeftHomologyData.K →ₗ[R]
        (T.sc (p + q)).moduleCatLeftHomologyData.K := by
  have hclosed (a : (C.sc p).moduleCatLeftHomologyData.K)
      (b : (D.sc q).moduleCatLeftHomologyData.K) : T.dFrom (p + q) (μ p q a.val b.val) = 0 := by
    have h := hleibniz p q a.val b.val
    rw [cochainCocycle_closed R C p a, cochainCocycle_closed R D q b] at h
    simp only [map_zero, LinearMap.zero_apply, zero_add, smul_zero] at h
    rw [dFrom_eq (r := show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1) from rfl),
      ModuleCat.comp_apply, h, map_zero]
  exact
    { toFun := fun a ↦
        { toFun := fun b ↦ ⟨μ p q a.val b.val, hclosed a b⟩
          map_add' := by
            intro b c
            apply Subtype.ext
            exact (μ p q a.val).map_add b.val c.val
          map_smul' := by
            intro t b
            apply Subtype.ext
            exact (μ p q a.val).map_smul t b.val }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        apply Subtype.ext
        exact congrArg (fun f ↦ f c.val) ((μ p q).map_add a.val b.val)
      map_smul' := by
        intro t a
        apply LinearMap.ext
        intro b
        apply Subtype.ext
        exact congrArg (fun f ↦ f b.val) ((μ p q).map_smul t a.val) }

private theorem cochainCupCycles_mem_boundaries (p q : ℕ)
    (φ : (C.sc p).moduleCatLeftHomologyData.K)
    (ψ : (D.sc q).moduleCatLeftHomologyData.K)
    (h : φ ∈ (C.sc p).moduleCatToCycles.range ∨ ψ ∈ (D.sc q).moduleCatToCycles.range) :
    cochainCupCycles R μ hleibniz p q φ ψ ∈ (T.sc (p + q)).moduleCatToCycles.range := by
  -- The primitive remains in this precise target complex; the right primitive has the Leibniz sign.
  let O := C
  let C := D
  let U := T
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
      -- Degree zero has no incoming coboundary, so the left factor itself vanishes.
      rw [hzero O φ hφ, map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
    | succ k =>
      obtain ⟨α, hα⟩ := hprimitive O k φ hφ
      let φ₀ : O.X (k + 1) := φ.val
      let ψ₀ : C.X q := ψ.val
      change O.d k (k + 1) α = φ₀ at hα
      have hψ₀ : C.d q (q + 1) ψ₀ = 0 := cochainCocycle_closed R C q ψ
      have hleib := hleibniz k q α ψ₀
      rw [hα, hψ₀] at hleib
      simp only [map_zero, smul_zero, add_zero] at hleib
      -- The cup of the actual primitive with the closed right factor is a primitive.
      apply hboundary U (k + q) ((k + 1) + q) (by change k + q + 1 = (k + 1) + q; omega)
        (cochainCupCycles R μ hleibniz (k + 1) q φ ψ)
        (μ k q α ψ₀)
      change U.d (k + q) ((k + 1) + q) (μ k q α ψ₀) =
        μ (k + 1) q φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (U.XIsoOfEq (Nat.add_right_comm k 1 q)).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
      exact hleib
  · cases q with
    | zero =>
      -- The same incoming-degree-zero argument applies to the right factor.
      rw [hzero C ψ hψ, map_zero]
      exact Submodule.zero_mem _
    | succ k =>
      obtain ⟨β, hβ⟩ := hprimitive C k ψ hψ
      let φ₀ : O.X p := φ.val
      let ψ₀ : C.X (k + 1) := ψ.val
      change C.d k (k + 1) β = ψ₀ at hβ
      have hφ₀ : O.d p (p + 1) φ₀ = 0 := cochainCocycle_closed R O p φ
      have hleib := hleibniz p k φ₀ β
      rw [hφ₀, hβ] at hleib
      simp only [map_zero, LinearMap.zero_apply, zero_add] at hleib
      -- The Leibniz sign is its own inverse, so it corrects this actual right primitive.
      apply hboundary U (p + k) (p + (k + 1)) (by change p + k + 1 = p + (k + 1); omega)
        (cochainCupCycles R μ hleibniz p (k + 1) φ ψ)
        ((-1 : R) ^ p • μ p k φ₀ β)
      change U.d (p + k) (p + (k + 1))
        ((-1 : R) ^ p • μ p k φ₀ β) =
        μ p (k + 1) φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (U.XIsoOfEq (Nat.add_assoc p k 1).symm).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom,
        map_smul, hleib, smul_smul, ← pow_add]
      have hsign : (-1 : R) ^ (p + p) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hsign, one_smul]

private theorem cochainCupClass_congr (p q : ℕ)
    (a a' : (C.sc p).moduleCatLeftHomologyData.K)
    (b b' : (D.sc q).moduleCatLeftHomologyData.K)
    (ha : cochainClass R C p a = cochainClass R C p a')
    (hb : cochainClass R D q b = cochainClass R D q b') :
    cochainClass R T (p + q) (cochainCupCycles R μ hleibniz p q a b) =
      cochainClass R T (p + q) (cochainCupCycles R μ hleibniz p q a' b') := by
  let product := (cochainCupCycles R μ hleibniz p q).compr₂ (cochainClass R T (p + q))
  have hleft : (C.sc p).moduleCatToCycles.range ≤ product.ker := by
    intro α hα
    apply LinearMap.ext
    intro β
    change (T.sc (p + q)).moduleCatHomologyIso.inv
      ((T.sc (p + q)).moduleCatToCycles.range.mkQ
        (cochainCupCycles R μ hleibniz p q α β)) = 0
    have hz : (T.sc (p + q)).moduleCatToCycles.range.mkQ
        (cochainCupCycles R μ hleibniz p q α β) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        (cochainCupCycles_mem_boundaries R μ hleibniz p q α β (Or.inl hα))
    rw [hz, map_zero]
  have hright : (D.sc q).moduleCatToCycles.range ≤ product.flip.ker := by
    intro β hβ
    apply LinearMap.ext
    intro α
    change (T.sc (p + q)).moduleCatHomologyIso.inv
      ((T.sc (p + q)).moduleCatToCycles.range.mkQ
        (cochainCupCycles R μ hleibniz p q α β)) = 0
    have hz : (T.sc (p + q)).moduleCatToCycles.range.mkQ
        (cochainCupCycles R μ hleibniz p q α β) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr
        (cochainCupCycles_mem_boundaries R μ hleibniz p q α β (Or.inr hβ))
    rw [hz, map_zero]
  let descended := product.liftQ₂ (C.sc p).moduleCatToCycles.range
    (D.sc q).moduleCatToCycles.range hleft hright
  let onHomology := (descended.compl₂ (D.sc q).moduleCatHomologyIso.hom.hom).comp
    (C.sc p).moduleCatHomologyIso.hom.hom
  have heval (α : (C.sc p).moduleCatLeftHomologyData.K)
      (β : (D.sc q).moduleCatLeftHomologyData.K) :
      onHomology (cochainClass R C p α) (cochainClass R D q β) =
        cochainClass R T (p + q) (cochainCupCycles R μ hleibniz p q α β) := by
    change descended ((C.sc p).moduleCatHomologyIso.hom
      ((C.sc p).moduleCatHomologyIso.inv ((C.sc p).moduleCatToCycles.range.mkQ α)))
        ((D.sc q).moduleCatHomologyIso.hom
          ((D.sc q).moduleCatHomologyIso.inv ((D.sc q).moduleCatToCycles.range.mkQ β))) = _
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
    rfl
  rw [← heval, ← heval, ha, hb]

end CocycleProducts

private theorem cochainCup_restriction (A : Set X) (p q : ℕ)
    (a : (singularCochains R X).X p) (b : (singularCochains R X).X q) :
    let P := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
    P.f (p + q) (singularCochainCup R X p q a b) =
      singularCochainCup R A p q (P.f p a) (P.f q b) := by
  let P := (singularCochainDualFunctor R).map (singularSubspaceChains R A).op
  let g := TopCat.toSSet.map
    (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(A, X)))
  have heval (k : ℕ) (χ : (singularCochains R X).X k)
      (σ : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌)) :
      singularCochainEquiv R A k (P.f k χ) σ =
        singularCochainEquiv R X k χ (g.app (op ⦋k⦌) σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X k ⟶ singularCoefficient R from χ)
      (((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex σ ≫
        (SSet.chainComplexMap g (singularCoefficient R)).f k) (ULift.up 1)) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  apply (singularCochainEquiv R A (p + q)).injective
  funext σ
  rw [heval]
  change singularCochainEquiv R X (p + q)
    ((singularCochainEquiv R X (p + q)).symm _) _ =
      singularCochainEquiv R A (p + q) ((singularCochainEquiv R A (p + q)).symm _) _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  dsimp only
  rw [heval, heval]
  have hfront := congrArg (fun t ↦ t σ) (g.naturality (singularCupFrontFace p q).op)
  have hback := congrArg (fun t ↦ t σ) (g.naturality (singularCupBackFace p q).op)
  exact congrArg₂ (fun u v ↦ singularCochainEquiv R X p a u *
    singularCochainEquiv R X q b v) hfront.symm hback.symm

private theorem subspace_comp_zero_of_subset (A B : Set X) (hAB : A ⊆ B)
    {D : ChainComplex (ModuleCat.{u} R) ℕ} (f : singularChains R X ⟶ D)
    (hB : singularSubspaceChains R B ≫ f = 0) : singularSubspaceChains R A ≫ f = 0 := by
  let i : C(A, B) := ⟨fun x ↦ ⟨x.val, hAB x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have h : (singularChainsFunctor R).map (TopCat.ofHom i) ≫ singularSubspaceChains R B =
      singularSubspaceChains R A := by
    simp only [singularSubspaceChains, ← Functor.map_comp]
    rfl
  rw [← h, Category.assoc, hB, comp_zero]

private theorem jointProjection_kills (A B C : Set X) (h : C ⊆ A ∨ C ⊆ B) :
    singularSubspaceChains R C ≫ relativeUnionSingularChainsProjection R A B = 0 := by
  rcases h with h | h
  · apply subspace_comp_zero_of_subset R C A h
    have hz := congrArg
      (fun f ↦ (biprod.inl : singularChains R A ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    dsimp only [singularSubspaceSumChains] at hz
    simp only [biprod.inl_desc_assoc, comp_zero] at hz
    exact hz
  · apply subspace_comp_zero_of_subset R C B h
    have hz := congrArg
      (fun f ↦ (biprod.inr : singularChains R B ⟶
        singularChains R A ⊞ singularChains R B) ≫ f)
      (cokernel.condition (singularSubspaceSumChains R A B))
    dsimp only [singularSubspaceSumChains] at hz
    simp only [biprod.inr_desc_assoc, comp_zero] at hz
    exact hz

set_option maxHeartbeats 2400000 in

/-- Three genuine relative factors associate, with only the actual support and degree casts. -/
theorem relativeSingularCohomologyUnionCup_assoc (A B C : Set X)
    (hA : IsOpen A) (hB : IsOpen B) (hC : IsOpen C) (p q r : ℕ)
    (a : relativeSingularCohomology R A p) (b : relativeSingularCohomology R B q)
    (c : relativeSingularCohomology R C r) :
    (eqToIso (by rw [Set.union_assoc, Nat.add_assoc]) :
      relativeSingularCohomology R ((A ∪ B) ∪ C) ((p + q) + r) ≅
        relativeSingularCohomology R (A ∪ (B ∪ C)) (p + (q + r))).hom
      (relativeSingularCohomologyUnionCup R (A ∪ B) C (hA.union hB) hC (p + q) r
        (relativeSingularCohomologyUnionCup R A B hA hB p q a b) c) =
      relativeSingularCohomologyUnionCup R A (B ∪ C) hA (hB.union hC) p (q + r) a
        (relativeSingularCohomologyUnionCup R B C hB hC q r b c) := by
  /- Compare both bracketings in the same quotient by three-member small chains.
  The canonical map from this quotient to the relative chains of the full union
  is a chain homotopy equivalence. Inner binary products give the original AW
  classes there; their possible differences of representatives are coboundaries
  in the same quotient. Associativity then follows from the same three faces. -/
  let Z := A ∪ (B ∪ C)
  let 𝒰 : Set (Set X) := {A, B, C}
  let 𝒱 := (fun U : Set X ↦ (Subtype.val : Z → X) ⁻¹' U) '' 𝒰
  let i := smallSingularChainsInclusion R 𝒱
  let j := singularSubspaceChains R Z
  let f := i ≫ j
  let T := (singularCochainDualFunctor R).obj (op (cokernel f))
  let J := (singularCochainDualFunctor R).map (cokernel.π f).op
  let P (U : Set X) := (singularCochainDualFunctor R).map
    (relativeSingularChainsProjection R U).op
  let Q (U V : Set X) := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsProjection R U V).op
  have hJ (n : ℕ) : Function.Injective (J.f n) := by
    intro x y h
    apply (quotientCochainEquiv R f n).injective
    exact Subtype.ext h
  have hkill (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :
      f ≫ relativeUnionSingularChainsProjection R U V = 0 := by
    ext n : 1
    change f.f n ≫ (relativeUnionSingularChainsProjection R U V).f n = 0
    apply smallSubspace_comp_zero R Z 𝒰 n
    intro W hW
    exact congrArg (fun g ↦ g.f n) (jointProjection_kills R U V W (hUV W hW))
  let factor (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :=
    cokernel.desc f (relativeUnionSingularChainsProjection R U V) (hkill U V hUV)
  let F (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :=
    (singularCochainDualFunctor R).map (factor U V hUV).op
  let G (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :=
    (singularCochainDualFunctor R).map (relativeUnionSingularChainsToRelative R U V).op ≫
      F U V hUV
  have hFJ (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :
      F U V hUV ≫ J = Q U V := by
    change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp]
    congr 1
    exact congrArg Quiver.Hom.op (cokernel.π_desc _ _ _)
  have hGJ (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) :
      G U V hUV ≫ J = P (U ∪ V) := by
    change (_ ≫ F U V hUV) ≫ J = _
    rw [Category.assoc, hFJ U V hUV]
    change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp]
    congr 1
    exact congrArg Quiver.Hom.op (cokernel.π_desc _ _ _)
  have hleft : ∀ W ∈ 𝒰, W ⊆ A ∪ B ∨ W ⊆ C := by
    intro W hW
    have h : W = A ∨ W = B ∨ W = C := by simpa [𝒰] using hW
    rcases h with rfl | rfl | rfl
    · exact Or.inl Set.subset_union_left
    · exact Or.inl Set.subset_union_right
    · exact Or.inr Set.Subset.rfl
  have hright : ∀ W ∈ 𝒰, W ⊆ A ∨ W ⊆ B ∪ C := by
    intro W hW
    have h : W = A ∨ W = B ∨ W = C := by simpa [𝒰] using hW
    rcases h with rfl | rfl | rfl
    · exact Or.inl Set.Subset.rfl
    · exact Or.inr Set.subset_union_left
    · exact Or.inr Set.subset_union_right
  -- Small-chain excision supplies injectivity on cohomology, not forgetting relative support.
  have hOpen : ∀ U ∈ 𝒱, IsOpen U := by
    rintro U ⟨W, hW, rfl⟩
    have h : W = A ∨ W = B ∨ W = C := by simpa [𝒰] using hW
    rcases h with rfl | rfl | rfl
    · exact hA.preimage continuous_subtype_val
    · exact hB.preimage continuous_subtype_val
    · exact hC.preimage continuous_subtype_val
  have hCover : ⋃₀ 𝒱 = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rcases x.property with hx | hx | hx
    · exact ⟨_, ⟨A, by simp [𝒰], rfl⟩, hx⟩
    · exact ⟨_, ⟨B, by simp [𝒰], rfl⟩, hx⟩
    · exact ⟨_, ⟨C, by simp [𝒰], rfl⟩, hx⟩
  obtain ⟨hcontract⟩ := contractible_cokernel_smallSingularChains R 𝒱 hOpen hCover
  have hj (n : ℕ) : IsSplitMono (j.f n) :=
    isSplitMono_singularChainsMap_of_injective R
      (⟨Subtype.val, continuous_subtype_val⟩ : C(Z, X)) Subtype.val_injective n
  let g := cokernel.desc f (relativeSingularChainsProjection R Z) (by
    change (i ≫ j) ≫ cokernel.π j = 0
    simp)
  have hg : HomologicalComplex.homotopyEquivalences
      (ModuleCat.{u} R) (ComplexShape.down ℕ) g :=
    homotopyEquivalences_cokernel_desc_of_contractible i j hj hcontract
  have hG : G A (B ∪ C) hright = (singularCochainDualFunctor R).map g.op := by
    have hcomp : factor A (B ∪ C) hright ≫
        relativeUnionSingularChainsToRelative R A (B ∪ C) = g := by
      apply (cancel_epi (cokernel.π f)).mp
      rw [← Category.assoc, cokernel.π_desc, cokernel.π_desc]
      exact cokernel.π_desc _ _ _
    change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp, hcomp]
  have hInjective (n : ℕ) : Function.Injective (homologyMap (G A (B ∪ C) hright) n) := by
    rw [hG]
    have := isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences R g hg n
    exact (ConcreteCategory.bijective_of_isIso _).injective
  -- Every auxiliary product is the original ordinary AW formula in this common quotient.
  have hvanishCup {D E : CochainComplex (ModuleCat.{u} R) ℕ}
      (PD : D ⟶ singularCochains R X) (PE : E ⟶ singularCochains R X)
      (hDE : ∀ (W : Set X), W ∈ 𝒰 →
        (∀ (k : ℕ) (α : D.X k), (singularSubspaceChains R W).f k ≫ PD.f k α = 0) ∨
        (∀ (k : ℕ) (β : E.X k), (singularSubspaceChains R W).f k ≫ PE.f k β = 0))
      (k l : ℕ) (α : D.X k) (β : E.X l) :
      f.f (k + l) ≫ singularCochainCup R X k l (PD.f k α) (PE.f l β) = 0 := by
    apply smallSubspace_comp_zero R Z 𝒰 (k + l)
    intro W hW
    change (((singularCochainDualFunctor R).map (singularSubspaceChains R W).op).f (k + l))
      (singularCochainCup R X k l (PD.f k α) (PE.f l β)) = 0
    rw [cochainCup_restriction]
    rcases hDE W hW with hD | hE
    · change (singularCochainCup R W k l
        ((singularSubspaceChains R W).f k ≫ PD.f k α)) _ = 0
      rw [hD k α, map_zero, LinearMap.zero_apply]
    · change (singularCochainCup R W k l _)
        ((singularSubspaceChains R W).f l ≫ PE.f l β) = 0
      rw [hE l β, map_zero]
  have hPrel (U : Set X) (k : ℕ) (α : (relativeSingularCochains R U).X k) :
      (singularSubspaceChains R U).f k ≫ (P U).f k α = 0 := by
    change (singularSubspaceChains R U).f k ≫
      ((relativeSingularChainsProjection R U).f k ≫ α) = 0
    rw [← Category.assoc]
    have h := congrArg (fun g ↦ g.f k) (cokernel.condition (singularSubspaceChains R U))
    change (singularSubspaceChains R U).f k ≫ (relativeSingularChainsProjection R U).f k = 0 at h
    rw [h, zero_comp]
  have hQrel (U V W : Set X) (hW : W ⊆ U ∨ W ⊆ V) (k : ℕ)
      (α : (relativeUnionSingularCochains R U V).X k) :
      (singularSubspaceChains R W).f k ≫ (Q U V).f k α = 0 := by
    change (singularSubspaceChains R W).f k ≫
      ((relativeUnionSingularChainsProjection R U V).f k ≫ α) = 0
    rw [← Category.assoc]
    have h := congrArg (fun g ↦ g.f k) (jointProjection_kills R U V W hW)
    change (singularSubspaceChains R W).f k ≫
      (relativeUnionSingularChainsProjection R U V).f k = 0 at h
    rw [h, zero_comp]
  have hL := hvanishCup (Q A B) (P C) (by
    intro W hW
    have h : W = A ∨ W = B ∨ W = C := by simpa [𝒰] using hW
    rcases h with h | h | h
    · subst W
      exact Or.inl (hQrel A B A (Or.inl Set.Subset.rfl))
    · subst W
      exact Or.inl (hQrel A B B (Or.inr Set.Subset.rfl))
    · subst W
      exact Or.inr (hPrel C))
  have hR := hvanishCup (P A) (Q B C) (by
    intro W hW
    have h : W = A ∨ W = B ∨ W = C := by simpa [𝒰] using hW
    rcases h with h | h | h
    · subst W
      exact Or.inl (hPrel A)
    · subst W
      exact Or.inr (hQrel B C B (Or.inl Set.Subset.rfl))
    · subst W
      exact Or.inr (hQrel B C C (Or.inr Set.Subset.rfl)))
  let μL := quotientCochainCup R f (Q A B) (P C) hL
  let μR := quotientCochainCup R f (P A) (Q B C) hR
  let cL := cochainCupCycles R μL (quotientCochainCup_leibniz R f (Q A B) (P C) hL)
  let cR := cochainCupCycles R μR (quotientCochainCup_leibniz R f (P A) (Q B C) hR)
  -- The remaining comparison uses the original two binary cocycle-class formulas.
  let mapCycle {D E : CochainComplex (ModuleCat.{u} R) ℕ} (H : D ⟶ E) (k : ℕ)
      (α : (D.sc k).moduleCatLeftHomologyData.K) : (E.sc k).moduleCatLeftHomologyData.K :=
    ⟨H.f k α.val, by
      change E.dFrom k (H.f k α.val) = 0
      have h := congrArg (fun g ↦ g α.val) (H.comm_from k)
      change E.dFrom k (H.f k α.val) = H.next k (D.dFrom k α.val) at h
      rw [h, show D.dFrom k α.val = 0 from α.property, map_zero]⟩
  let binary (U V : Set X) := (singularCochainDualFunctor R).map
    (relativeUnionSingularChainsToRelative R U V).op
  have hbinary (U V : Set X) : binary U V ≫ Q U V = P (U ∪ V) := by
    change (singularCochainDualFunctor R).map _ ≫
      (singularCochainDualFunctor R).map _ = _
    rw [← Functor.map_comp, ← op_comp]
    congr 1
    exact congrArg Quiver.Hom.op (cokernel.π_desc _ _ _)
  have hFeval (U V : Set X) (hUV : ∀ W ∈ 𝒰, W ⊆ U ∨ W ⊆ V) (k : ℕ)
      (α : (relativeUnionSingularCochains R U V).X k) :
      J.f k ((F U V hUV).f k α) = (Q U V).f k α :=
    congrArg (fun g ↦ g.f k α) (hFJ U V hUV)
  have hBeval (U V : Set X) (k : ℕ) (α : (relativeSingularCochains R (U ∪ V)).X k) :
      (Q U V).f k ((binary U V).f k α) = (P (U ∪ V)).f k α :=
    congrArg (fun g ↦ g.f k α) (hbinary U V)
  have hjoint (U V : Set X) (k l : ℕ) (α : (relativeSingularCochains R U).X k)
      (β : (relativeSingularCochains R V).X l) :
      (Q U V).f (k + l) (relativeUnionSingularCochainCup R U V k l α β) =
        singularCochainCup R X k l ((P U).f k α) ((P V).f l β) :=
    congrArg Subtype.val ((relativeUnionSingularCochainEquiv R U V (k + l)).apply_symm_apply _)
  obtain ⟨α, hα⟩ := cochainClass_surjective R (relativeSingularCochains R A) p a
  obtain ⟨β, hβ⟩ := cochainClass_surjective R (relativeSingularCochains R B) q b
  obtain ⟨γ, hγ⟩ := cochainClass_surjective R (relativeSingularCochains R C) r c
  change relativeSingularCocycleClass R A p α = a at hα
  change relativeSingularCocycleClass R B q β = b at hβ
  change relativeSingularCocycleClass R C r γ = c at hγ
  rw [← hα, ← hβ, ← hγ]
  obtain ⟨δ, hδ⟩ := cochainClass_surjective R (relativeSingularCochains R (A ∪ B)) (p + q)
    (relativeSingularCohomologyUnionCup R A B hA hB p q
      (relativeSingularCocycleClass R A p α) (relativeSingularCocycleClass R B q β))
  obtain ⟨ε, hε⟩ := cochainClass_surjective R (relativeSingularCochains R (B ∪ C)) (q + r)
    (relativeSingularCohomologyUnionCup R B C hB hC q r
      (relativeSingularCocycleClass R B q β) (relativeSingularCocycleClass R C r γ))
  let δJ := mapCycle (binary A B) (p + q) δ
  let εJ := mapCycle (binary B C) (q + r) ε
  let αβ := relativeUnionSingularCocycleCup R A B p q α β
  let βγ := relativeUnionSingularCocycleCup R B C q r β γ
  have hδJ : cochainClass R (relativeUnionSingularCochains R A B) (p + q) δJ =
      cochainClass R (relativeUnionSingularCochains R A B) (p + q) αβ := by
    rw [← cochainClass_map R (binary A B) (p + q) δ δJ rfl, hδ]
    exact relativeSingularCohomologyUnionCup_cocycleClass R A B hA hB p q α β
  have hεJ : cochainClass R (relativeUnionSingularCochains R B C) (q + r) εJ =
      cochainClass R (relativeUnionSingularCochains R B C) (q + r) βγ := by
    rw [← cochainClass_map R (binary B C) (q + r) ε εJ rfl, hε]
    exact relativeSingularCohomologyUnionCup_cocycleClass R B C hB hC q r β γ
  have hOuterL : homologyMap (G (A ∪ B) C hleft) ((p + q) + r)
      (relativeSingularCohomologyUnionCup R (A ∪ B) C (hA.union hB) hC (p + q) r
        (cochainClass R (relativeSingularCochains R (A ∪ B)) (p + q) δ)
        (relativeSingularCocycleClass R C r γ)) =
      cochainClass R T ((p + q) + r) (cL (p + q) r δJ γ) := by
    change homologyMap (binary (A ∪ B) C ≫ F (A ∪ B) C hleft) ((p + q) + r)
      (relativeSingularCohomologyUnionCup R (A ∪ B) C (hA.union hB) hC (p + q) r
        (relativeSingularCocycleClass R (A ∪ B) (p + q) δ)
        (relativeSingularCocycleClass R C r γ)) = _
    rw [homologyMap_comp, ModuleCat.comp_apply]
    change homologyMap (F (A ∪ B) C hleft) ((p + q) + r)
      (relativeUnionCohomologyComparison R (A ∪ B) C ((p + q) + r) _) = _
    rw [relativeSingularCohomologyUnionCup_cocycleClass]
    apply cochainClass_map R (F (A ∪ B) C hleft)
    apply hJ ((p + q) + r)
    change J.f ((p + q) + r) ((F (A ∪ B) C hleft).f ((p + q) + r)
      (relativeUnionSingularCochainCup R (A ∪ B) C (p + q) r δ.val γ.val)) =
      J.f ((p + q) + r) (μL (p + q) r ((binary A B).f (p + q) δ.val) γ.val)
    rw [hFeval (A ∪ B) C hleft, hjoint, quotientCochainCup_to_ordinary]
    exact congrArg (fun z ↦ singularCochainCup R X (p + q) r z ((P C).f r γ.val))
      (hBeval A B (p + q) δ.val).symm
  have hOuterR : homologyMap (G A (B ∪ C) hright) (p + (q + r))
      (relativeSingularCohomologyUnionCup R A (B ∪ C) hA (hB.union hC) p (q + r)
        (relativeSingularCocycleClass R A p α)
        (cochainClass R (relativeSingularCochains R (B ∪ C)) (q + r) ε)) =
      cochainClass R T (p + (q + r)) (cR p (q + r) α εJ) := by
    change homologyMap (binary A (B ∪ C) ≫ F A (B ∪ C) hright) (p + (q + r))
      (relativeSingularCohomologyUnionCup R A (B ∪ C) hA (hB.union hC) p (q + r)
        (relativeSingularCocycleClass R A p α)
        (relativeSingularCocycleClass R (B ∪ C) (q + r) ε)) = _
    rw [homologyMap_comp, ModuleCat.comp_apply]
    change homologyMap (F A (B ∪ C) hright) (p + (q + r))
      (relativeUnionCohomologyComparison R A (B ∪ C) (p + (q + r)) _) = _
    rw [relativeSingularCohomologyUnionCup_cocycleClass]
    apply cochainClass_map R (F A (B ∪ C) hright)
    apply hJ (p + (q + r))
    change J.f (p + (q + r)) ((F A (B ∪ C) hright).f (p + (q + r))
      (relativeUnionSingularCochainCup R A (B ∪ C) p (q + r) α.val ε.val)) =
      J.f (p + (q + r)) (μR p (q + r) α.val ((binary B C).f (q + r) ε.val))
    rw [hFeval A (B ∪ C) hright, hjoint, quotientCochainCup_to_ordinary]
    exact congrArg (singularCochainCup R X p (q + r) ((P A).f p α.val))
      (hBeval B C (q + r) ε.val).symm
  -- The support equality transports the canonical comparison itself.
  have hPcast (U V : Set X) (h : U = V) :
      eqToHom (congrArg (relativeSingularCochains R) h) ≫ P V = P U := by
    subst V
    simp
  have hmono : Mono J := HomologicalComplex.mono_of_mono_f J
    (fun n ↦ (ModuleCat.mono_iff_injective _).mpr (hJ n))
  have hsupport : eqToHom (congrArg (relativeSingularCochains R) (Set.union_assoc A B C)) ≫
      G A (B ∪ C) hright = G (A ∪ B) C hleft := by
    apply (cancel_mono J).mp
    rw [Category.assoc, hGJ A (B ∪ C) hright, hGJ (A ∪ B) C hleft]
    exact hPcast _ _ (Set.union_assoc A B C)
  have htransport {D E : CochainComplex (ModuleCat.{u} R) ℕ} (h : D = E)
      (HD : D ⟶ T) (HE : E ⟶ T) (hH : eqToHom h ≫ HE = HD)
      (k l : ℕ) (hkl : k = l) (x : D.homology k) :
      homologyMap HE l
          ((eqToIso (by subst E; subst l; rfl) : D.homology k ≅ E.homology l).hom x) =
        (eqToIso (congrArg (fun n ↦ T.homology n) hkl)).hom (homologyMap HD k x) := by
    subst E
    subst l
    simp only [eqToHom_refl, Category.id_comp] at hH
    subst HD
    rfl
  have hcast (x : relativeSingularCohomology R ((A ∪ B) ∪ C) ((p + q) + r)) :
      homologyMap (G A (B ∪ C) hright) (p + (q + r))
          ((eqToIso (by rw [Set.union_assoc, Nat.add_assoc]) :
            relativeSingularCohomology R ((A ∪ B) ∪ C) ((p + q) + r) ≅
              relativeSingularCohomology R (A ∪ (B ∪ C)) (p + (q + r))).hom x) =
        (eqToIso (congrArg (fun n ↦ T.homology n) (Nat.add_assoc p q r))).hom
          (homologyMap (G (A ∪ B) C hleft) ((p + q) + r) x) :=
    htransport (congrArg (relativeSingularCochains R) (Set.union_assoc A B C))
      (G (A ∪ B) C hleft) (G A (B ∪ C) hright) hsupport
      ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r) x
  apply hInjective (p + (q + r))
  rw [← hδ, ← hε, hcast, hOuterL, hOuterR]
  have hLclass := cochainCupClass_congr R μL
    (quotientCochainCup_leibniz R f (Q A B) (P C) hL) (p + q) r δJ αβ γ γ hδJ rfl
  have hRclass := cochainCupClass_congr R μR
    (quotientCochainCup_leibniz R f (P A) (Q B C) hR) p (q + r) α α εJ βγ rfl hεJ
  rw [hLclass, hRclass]
  apply cochainClass_transport R T ((p + q) + r) (p + (q + r)) (Nat.add_assoc p q r)
    (cL (p + q) r αβ γ) (cR p (q + r) α βγ)
  -- Both expressions now evaluate on exactly the same front, middle, and back faces.
  have ht {k l : ℕ} (h : k = l) (x : T.X k) :
      J.f l ((T.XIsoOfEq h).hom x) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f k x) := by
    subst l
    rfl
  apply hJ (p + (q + r))
  change J.f (p + (q + r)) ((T.XIsoOfEq (Nat.add_assoc p q r)).hom
      (μL (p + q) r (relativeUnionSingularCochainCup R A B p q α.val β.val) γ.val)) =
    J.f (p + (q + r))
      (μR p (q + r) α.val (relativeUnionSingularCochainCup R B C q r β.val γ.val))
  rw [ht, quotientCochainCup_to_ordinary, quotientCochainCup_to_ordinary]
  calc
    _ = ((singularCochains R X).XIsoOfEq (Nat.add_assoc p q r)).hom
        (singularCochainCup R X (p + q) r
          (singularCochainCup R X p q ((P A).f p α.val) ((P B).f q β.val))
          ((P C).f r γ.val)) :=
      congrArg (fun z ↦ ((singularCochains R X).XIsoOfEq (Nat.add_assoc p q r)).hom
        (singularCochainCup R X (p + q) r z ((P C).f r γ.val)))
        (hjoint A B p q α.val β.val)
    _ = singularCochainCup R X p (q + r) ((P A).f p α.val)
        (singularCochainCup R X q r ((P B).f q β.val) ((P C).f r γ.val)) :=
      singularCochainCup_assoc R p q r ((P A).f p α.val) ((P B).f q β.val) ((P C).f r γ.val)
    _ = _ := congrArg (singularCochainCup R X p (q + r) ((P A).f p α.val))
      (hjoint B C q r β.val γ.val).symm

end AtiyahSinger
