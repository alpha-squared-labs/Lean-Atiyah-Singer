/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RelativeCochainCup
public import AtiyahSinger.Topology.SingularSmallChainsHomotopy

/-!
# Relative cup cochains and the actual quotient by two subspace chain complexes

Public module ID: M2099.

Hatcher, Algebraic Topology, Section 3.2, p.209. The ordinary
Alexander--Whitney product of an A-relative cochain and a B-relative cochain
vanishes separately on C_*(A) and C_*(B). It therefore factors through the
actual quotient C_*(X)/(C_*(A)+C_*(B)), represented by the cokernel of the
sum of their two original chain inclusions.

It need not vanish on every simplex of A union B. The canonical quotient
map to C_*(X,A union B) instead induces a cohomology isomorphism when A and
B are open, by the small-chain subdivision comparison. Its precise inverse
transports the joint cup to union-relative cohomology. Cochain
construction itself requires no openness, and all coefficients are in the
original arbitrary commutative ring. The joint-quotient cup, Leibniz identity
and coboundary ideal property are proved below. The open-union comparison uses
the actual small-chain contraction and the canonical nested quotient map.

The product and its differential always use the original front/back
faces and their unsuspended Leibniz sign.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]

/-- The sum of the original two chain inclusions, whose image is C_*(A)+C_*(B). -/
def singularSubspaceSumChains (A B : Set X) :
    singularChains R A ⊞ singularChains R B ⟶ singularChains R X :=
  biprod.desc (singularSubspaceChains R A) (singularSubspaceChains R B)

/-- The actual quotient by the sum of the two subspace chain images. -/
abbrev relativeUnionSingularChains (A B : Set X) : ChainComplex (ModuleCat.{u} R) ℕ :=
  cokernel (singularSubspaceSumChains R A B)

/-- The original projection to the quotient by C_*(A)+C_*(B). -/
abbrev relativeUnionSingularChainsProjection (A B : Set X) :
    singularChains R X ⟶ relativeUnionSingularChains R A B :=
  cokernel.π (singularSubspaceSumChains R A B)

/-- Cochains vanishing separately on both subspace chain images, using the actual quotient dual. -/
abbrev relativeUnionSingularCochains (A B : Set X) : CochainComplex (ModuleCat.{u} R) ℕ :=
  (singularCochainDualFunctor R).obj (op (relativeUnionSingularChains R A B))

/-- Cohomology of the original quotient dual, prior to the open-union comparison. -/
abbrev relativeUnionSingularCohomology (A B : Set X) (n : ℕ) : ModuleCat.{u} R :=
  (relativeUnionSingularCochains R A B).homology n

/-- The canonical chain quotient map to the original relative chains of the union. -/
def relativeUnionSingularChainsToRelative (A B : Set X) :
    relativeUnionSingularChains R A B ⟶ relativeSingularChains R (A ∪ B) := by
  -- Each original subspace inclusion factors through the same actual union inclusion.
  let iA : C(A, ↥(A ∪ B)) :=
    ⟨fun x ↦ ⟨x.val, Or.inl x.property⟩, continuous_subtype_val.subtype_mk _⟩
  let iB : C(B, ↥(A ∪ B)) :=
    ⟨fun x ↦ ⟨x.val, Or.inr x.property⟩, continuous_subtype_val.subtype_mk _⟩
  have hA : (singularChainsFunctor R).map (TopCat.ofHom iA) ≫
      singularSubspaceChains R (A ∪ B) = singularSubspaceChains R A := by
    simp only [singularSubspaceChains, ← Functor.map_comp]
    rfl
  have hB : (singularChainsFunctor R).map (TopCat.ofHom iB) ≫
      singularSubspaceChains R (A ∪ B) = singularSubspaceChains R B := by
    simp only [singularSubspaceChains, ← Functor.map_comp]
    rfl
  -- The relative projection kills both summands, hence factors through their sum cokernel.
  exact cokernel.desc (singularSubspaceSumChains R A B)
    (relativeSingularChainsProjection R (A ∪ B)) (by
      apply biprod.hom_ext'
      · simp only [singularSubspaceSumChains, biprod.inl_desc_assoc, comp_zero]
        rw [← hA, Category.assoc]
        simp [relativeSingularChainsProjection]
      · simp only [singularSubspaceSumChains, biprod.inr_desc_assoc, comp_zero]
        rw [← hB, Category.assoc]
        simp [relativeSingularChainsProjection])

/-- The cohomology comparison induced by dualizing that specified chain quotient map. -/
def relativeUnionCohomologyComparison (A B : Set X) (n : ℕ) :
    relativeSingularCohomology R (A ∪ B) n ⟶ relativeUnionSingularCohomology R A B n :=
  HomologicalComplex.homologyMap
    ((singularCochainDualFunctor R).map (relativeUnionSingularChainsToRelative R A B).op) n

/-- Open-union small-chain excision makes the specified comparison bijective. -/
theorem relativeUnionCohomologyComparison_bijective
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    Function.Bijective (relativeUnionCohomologyComparison R A B n) := by
  /- Stage 1: in A union B, subdivide each actual singular simplex until
  every resulting simplex lies entirely in A or entirely in B. The open
  cover and compactness of the standard simplex supply a finite stage.
  The subdivision and prism operators give the usual small-chain chain
  homotopy comparison with C_*(A union B), preserving the original inclusions.
  Stage 2: the quotient of C_*(A union B) by C_*(A)+C_*(B) is therefore
  contractible. The inclusion and quotient sequences are degreewise split
  on the actual free simplex modules. The induced comparison between
  C_*(X)/(C_*(A)+C_*(B)) and C_*(X,A union B) is consequently a chain
  homotopy equivalence with this very canonical quotient as forward map.
  Stage 3: dualize the comparison and its chain homotopies over R and
  take degree-n cohomology. Dualizing a mere quasi-isomorphism would not
  suffice over an arbitrary ring; the small-chain homotopy comparison
  supplies what is needed. This gives bijectivity of the displayed map,
  including degree zero and the zero coefficient ring. -/
  have hChains : HomologicalComplex.homotopyEquivalences
      (ModuleCat.{u} R) (ComplexShape.down ℕ) (relativeUnionSingularChainsToRelative R A B) := by
    let Z := ↥(A ∪ B)
    let UA : Set Z := (Subtype.val : Z → X) ⁻¹' A
    let UB : Set Z := (Subtype.val : Z → X) ⁻¹' B
    have hOpen : ∀ U ∈ ({UA, UB} : Set (Set Z)), IsOpen U := by
      intro U hU
      have hc : U = UA ∨ U = UB := by simpa using hU
      rcases hc with hU | hU
      · rw [hU]
        exact hA.preimage continuous_subtype_val
      · rw [hU]
        exact hB.preimage continuous_subtype_val
    have hCover : ⋃₀ ({UA, UB} : Set (Set Z)) = Set.univ := by
      rw [Set.sUnion_pair]
      ext x
      exact iff_true_intro x.property
    obtain ⟨hSmall⟩ := contractible_cokernel_smallSingularChains R {UA, UB} hOpen hCover
    let eA : A ≃ₜ UA :=
      { toFun := fun x ↦ ⟨⟨x.val, Or.inl x.property⟩, x.property⟩
        invFun := fun x ↦ ⟨x.val.val, x.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
        continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
    let eB : B ≃ₜ UB :=
      { toFun := fun x ↦ ⟨⟨x.val, Or.inr x.property⟩, x.property⟩
        invFun := fun x ↦ ⟨x.val.val, x.property⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
        continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ }
    let EA := (singularChainsFunctor R).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of A) (Y := TopCat.of UA) eA)
    let EB := (singularChainsFunctor R).mapIso
      (TopCat.isoOfHomeo (X := TopCat.of B) (Y := TopCat.of UB) eB)
    let E := biprod.mapIso EA EB
    let i₀ := biprod.desc (singularSubspaceChains R UA) (singularSubspaceChains R UB)
    let i := E.hom ≫ i₀
    let j := singularSubspaceChains R (A ∪ B)
    have hAmap : EA.hom ≫ singularSubspaceChains R UA ≫ j = singularSubspaceChains R A := by
      change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ ≫
        (singularChainsFunctor R).map _ = (singularChainsFunctor R).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    have hBmap : EB.hom ≫ singularSubspaceChains R UB ≫ j = singularSubspaceChains R B := by
      change (singularChainsFunctor R).map _ ≫ (singularChainsFunctor R).map _ ≫
        (singularChainsFunctor R).map _ = (singularChainsFunctor R).map _
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    have hfactor : i ≫ j = singularSubspaceSumChains R A B := by
      apply biprod.hom_ext'
      · simpa [i, E, i₀, singularSubspaceSumChains] using hAmap
      · simpa [i, E, i₀, singularSubspaceSumChains] using hBmap
    -- Both changes of source preserve the actual quotient of the union's singular chains.
    let e₀ := cokernelIsoOfDegreewiseRangeEq (smallSingularChainsInclusion R {UA, UB}) i₀
      (range_smallSingularChainsInclusion_pair R UA UB)
    have h₀ : Homotopy (𝟙 (cokernel i₀)) 0 := by
      have H := (hSmall.compLeft e₀.inv).compRight e₀.hom
      simpa only [Category.comp_id, e₀.inv_hom_id, comp_zero, zero_comp] using H
    let e₁ := cokernelEpiComp E.hom i₀
    have h₁ : Homotopy (𝟙 (cokernel i)) 0 := by
      have H := (h₀.compLeft e₁.hom).compRight e₁.inv
      simpa only [Category.comp_id, e₁.hom_inv_id, comp_zero, zero_comp] using H
    have hj (n : ℕ) : IsSplitMono (j.f n) :=
      isSplitMono_singularChainsMap_of_injective R
        (⟨Subtype.val, continuous_subtype_val⟩ : C(↥(A ∪ B), X)) Subtype.val_injective n
    obtain ⟨T, hT⟩ := homotopyEquivalences_cokernel_desc_of_contractible i j hj h₁
    let Q := cokernelIsoOfEq hfactor
    have hforward : Q.hom ≫ relativeUnionSingularChainsToRelative R A B = T.hom := by
      rw [hT]
      apply (cancel_epi (cokernel.π (i ≫ j))).mp
      rw [← Category.assoc, π_comp_cokernelIsoOfEq_hom, cokernel.π_desc]
      simp [relativeUnionSingularChainsToRelative, j]
    let S := (HomotopyEquiv.ofIso Q.symm).trans T
    refine ⟨S, ?_⟩
    change Q.inv ≫ T.hom = relativeUnionSingularChainsToRelative R A B
    rw [← hforward, ← Category.assoc, Q.inv_hom_id, Category.id_comp]
  -- The actual inverse homotopies remain inverse homotopies after algebraic dualization.
  have hiso : IsIso (relativeUnionCohomologyComparison R A B n) :=
    isIso_homologyMap_singularCochainDualFunctor_of_homotopyEquivalences
      R (relativeUnionSingularChainsToRelative R A B) hChains n
  exact (ConcreteCategory.isIso_iff_bijective _).mp hiso

/-- The open-union equivalence with the actual dual quotient comparison as forward map. -/
def relativeUnionCohomologyEquiv
    (A B : Set X) (hA : IsOpen A) (hB : IsOpen B) (n : ℕ) :
    relativeSingularCohomology R (A ∪ B) n ≃ₗ[R]
      relativeUnionSingularCohomology R A B n :=
  LinearEquiv.ofBijective (relativeUnionCohomologyComparison R A B n).hom
    (relativeUnionCohomologyComparison_bijective R A B hA hB n)

/-- The quotient dual is exactly the kernel of restriction to the sum of the subspace chains. -/
def relativeUnionSingularCochainEquiv (A B : Set X) (n : ℕ) :
    (relativeUnionSingularCochains R A B).X n ≃ₗ[R]
      (((singularCochainDualFunctor R).map (singularSubspaceSumChains R A B).op).f n).hom.ker := by
  -- Degree evaluation retains the original cokernel's universal property.
  let Q := isColimitOfHasCokernelOfPreservesColimit
    (HomologicalComplex.eval (ModuleCat.{u} R) (ComplexShape.down ℕ) n)
    (singularSubspaceSumChains R A B)
  let extend (φ :
      (((singularCochainDualFunctor R).map (singularSubspaceSumChains R A B).op).f n).hom.ker) :=
    CokernelCofork.IsColimit.desc' Q φ.val
      (show (singularSubspaceSumChains R A B).f n ≫ φ.val = 0 from φ.property)
  exact
    { toFun := fun φ ↦ ⟨(relativeUnionSingularChainsProjection R A B).f n ≫ φ, by
        change (relativeUnionSingularChains R A B).X n ⟶ singularCoefficient R at φ
        change (singularSubspaceSumChains R A B).f n ≫
            ((relativeUnionSingularChainsProjection R A B).f n ≫ φ) = 0
        have hz : (singularSubspaceSumChains R A B).f n ≫
            (relativeUnionSingularChainsProjection R A B).f n = 0 :=
          congrArg (fun f ↦ f.f n) (cokernel.condition (singularSubspaceSumChains R A B))
        rw [← Category.assoc, hz, zero_comp]⟩
      invFun := fun φ ↦ (extend φ).val
      left_inv := by
        intro φ
        change (relativeUnionSingularChains R A B).X n ⟶ singularCoefficient R at φ
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

/-- The actual cup of the two relative cochains vanishes on the sum of their subspace chains. -/
theorem singularCochainCup_mem_relativeUnion (A B : Set X) (p q : ℕ)
    (φ : (relativeSingularCochains R A).X p) (ψ : (relativeSingularCochains R B).X q) :
    ((singularCochainDualFunctor R).map (singularSubspaceSumChains R A B).op).f (p + q)
      (singularCochainCup R X p q (relativeSingularCochainEquiv R A p φ).val
        (relativeSingularCochainEquiv R B q ψ).val) = 0 := by
  /- On a simplex lying in A the front face also lies in A, so the left
  relative factor vanishes. On a simplex lying in B the back face lies
  in B, so the right factor vanishes. The actual product therefore kills
  both chain inclusions, hence their biproduct sum. Linearity gives exactly
  the displayed kernel condition. This argument does not say that a
  simplex whose image merely lies in A union B lies in either member. -/
  -- Vanishing of the left factor on A applies to the original front face.
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
  let cup : (singularChains R X).X (p + q) ⟶ singularCoefficient R :=
    singularCochainCup R X p q (relativeSingularCochainEquiv R A p φ).val
      (relativeSingularCochainEquiv R B q ψ).val
  have hA : P.f (p + q) cup = 0 := by
    apply (singularCochainEquiv R A (p + q)).injective
    funext σ
    rw [heval]
    change singularCochainEquiv R X (p + q)
      ((singularCochainEquiv R X (p + q)).symm _) _ = _
    rw [LinearEquiv.apply_symm_apply]
    dsimp only
    have hvanish := congrArg
      (fun χ : (singularCochains R A).X p ↦ singularCochainEquiv R A p χ
        ((TopCat.toSSet.obj (TopCat.of A)).map (singularCupFrontFace p q).op σ))
      (relativeSingularCochainEquiv R A p φ).property
    rw [heval] at hvanish
    have hface := congrArg (fun g ↦ g σ) (f.naturality (singularCupFrontFace p q).op)
    change f.app (op ⦋p⦌) ((TopCat.toSSet.obj (TopCat.of A)).map
      (singularCupFrontFace p q).op σ) =
        (TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op
          (f.app (op ⦋p + q⦌) σ) at hface
    rw [← hface, hvanish]
    simp
  -- The already established right-relative formula kills the original B inclusion.
  have hB := singularCochainCup_mem_relative R B p q
    (relativeSingularCochainEquiv R A p φ).val ψ
  -- Evaluate the original chain-level biproduct sum; no new degreewise model is needed.
  have hA' : (singularSubspaceChains R A).f (p + q) ≫ cup = 0 := hA
  have hB' : (singularSubspaceChains R B).f (p + q) ≫ cup = 0 := hB
  change (biprod.desc (singularSubspaceChains R A)
    (singularSubspaceChains R B)).f (p + q) ≫ cup = 0
  rw [biprod.desc_eq, HomologicalComplex.add_f_apply,
    HomologicalComplex.comp_f, HomologicalComplex.comp_f, Preadditive.add_comp,
    Category.assoc, Category.assoc, hA', hB', comp_zero, comp_zero, add_zero]

/-- The original front/back product, factored through the actual joint quotient dual. -/
def relativeUnionSingularCochainCup (A B : Set X) (p q : ℕ) :
    (relativeSingularCochains R A).X p →ₗ[R]
      (relativeSingularCochains R B).X q →ₗ[R]
        (relativeUnionSingularCochains R A B).X (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ (relativeUnionSingularCochainEquiv R A B (p + q)).symm
        ⟨singularCochainCup R X p q (relativeSingularCochainEquiv R A p φ).val
            (relativeSingularCochainEquiv R B q ψ).val,
          singularCochainCup_mem_relativeUnion R A B p q φ ψ⟩
      map_add' := by
        intro ψ χ
        apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
        apply Subtype.ext
        simp [map_add]
      map_smul' := by
        intro a ψ
        apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
        apply Subtype.ext
        simp [map_smul] }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
    apply Subtype.ext
    simp [map_add]
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply (relativeUnionSingularCochainEquiv R A B (p + q)).injective
    apply Subtype.ext
    simp [map_smul]

/-- Leibniz holds in the joint quotient dual with the original degree-p sign. -/
theorem relativeUnionSingularCochainCup_leibniz (A B : Set X) (p q : ℕ)
    (φ : (relativeSingularCochains R A).X p) (ψ : (relativeSingularCochains R B).X q) :
    (relativeUnionSingularCochains R A B).d (p + q) (p + q + 1)
        (relativeUnionSingularCochainCup R A B p q φ ψ) =
      ((relativeUnionSingularCochains R A B).XIsoOfEq (Nat.add_right_comm p 1 q)).hom
          (relativeUnionSingularCochainCup R A B (p + 1) q
            ((relativeSingularCochains R A).d p (p + 1) φ) ψ) +
        (-1 : R) ^ p •
          ((relativeUnionSingularCochains R A B).XIsoOfEq (Nat.add_assoc p q 1).symm).hom
            (relativeUnionSingularCochainCup R A B p (q + 1) φ
              ((relativeSingularCochains R B).d q (q + 1) ψ)) := by
  /- Pull both sides back along the original joint quotient projection.
  Its injective dual is the underlying map of relativeUnionSingularCochainEquiv
  and commutes with coboundary. Both factor pullbacks are the original
  relative-to-ordinary cochain inclusions. Apply singularCochainCup_leibniz
  to these same ordinary cochains, then return by injectivity. Only degree
  reassociations occur; no subdivision or cochain commutativity is used. -/
  -- Pull back all three original quotient complexes to the same ordinary cochains.
  let JA := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R A).op
  let JB := (singularCochainDualFunctor R).map (relativeSingularChainsProjection R B).op
  let J := (singularCochainDualFunctor R).map (relativeUnionSingularChainsProjection R A B).op
  have hcup (i j : ℕ) (a : (relativeSingularCochains R A).X i)
      (b : (relativeSingularCochains R B).X j) :
      J.f (i + j) (relativeUnionSingularCochainCup R A B i j a b) =
        singularCochainCup R X i j (JA.f i a) (JB.f j b) := by
    exact congrArg Subtype.val
      ((relativeUnionSingularCochainEquiv R A B (i + j)).apply_symm_apply _)
  have hd (i j : ℕ) (a : (relativeUnionSingularCochains R A B).X i) :
      J.f j ((relativeUnionSingularCochains R A B).d i j a) =
        (singularCochains R X).d i j (J.f i a) :=
    (congrArg (fun f ↦ f a) (J.comm i j)).symm
  have hdA (i j : ℕ) (a : (relativeSingularCochains R A).X i) :
      JA.f j ((relativeSingularCochains R A).d i j a) =
        (singularCochains R X).d i j (JA.f i a) :=
    (congrArg (fun f ↦ f a) (JA.comm i j)).symm
  have hdB (i j : ℕ) (a : (relativeSingularCochains R B).X i) :
      JB.f j ((relativeSingularCochains R B).d i j a) =
        (singularCochains R X).d i j (JB.f i a) :=
    (congrArg (fun f ↦ f a) (JB.comm i j)).symm
  have ht {i j : ℕ} (h : i = j) (a : (relativeUnionSingularCochains R A B).X i) :
      J.f j (((relativeUnionSingularCochains R A B).XIsoOfEq h).hom a) =
        ((singularCochains R X).XIsoOfEq h).hom (J.f i a) := by
    subst j
    rfl
  -- Injectivity and compatibility of the specified pullbacks reduce to ordinary Leibniz.
  apply (relativeUnionSingularCochainEquiv R A B (p + q + 1)).injective
  apply Subtype.ext
  change J.f (p + q + 1) _ = J.f (p + q + 1) _
  rw [hd, hcup, map_add, map_smul, ht, ht, hcup, hcup, hdA, hdB]
  exact singularCochainCup_leibniz R X p q (JA.f p φ) (JB.f q ψ)

/-- The cocycle kernel in the actual joint quotient dual. -/
abbrev relativeUnionSingularCocycles (A B : Set X) (n : ℕ) : ModuleCat.{u} R :=
  ((relativeUnionSingularCochains R A B).sc n).moduleCatLeftHomologyData.K

/-- The incoming differential image inside the same joint cocycle kernel. -/
abbrev relativeUnionSingularCoboundaries (A B : Set X) (n : ℕ) :
    Submodule R (relativeUnionSingularCocycles R A B n) :=
  ((relativeUnionSingularCochains R A B).sc n).moduleCatToCycles.range

/-- The original product of two relative cocycles lies in the joint cocycle kernel. -/
theorem relativeUnionSingularCochainCup_mem_cocycles (A B : Set X) (p q : ℕ)
    (φ : relativeSingularCocycles R A p) (ψ : relativeSingularCocycles R B q) :
    ((relativeUnionSingularCochains R A B).sc (p + q)).g
      (relativeUnionSingularCochainCup R A B p q φ.val ψ.val) = 0 := by
  /- Both factors have zero original outgoing differential. Their Leibniz
  formula in the joint complex therefore has two zero terms. The outgoing
  map of this short complex is that original differential, giving precisely
  membership in its actual kernel, including zero degrees. -/
  -- Use the original next-degree isomorphisms rather than changing the kernel model.
  let φ₀ : (relativeSingularCochains R A).X p := φ.val
  let ψ₀ : (relativeSingularCochains R B).X q := ψ.val
  have hφ : (relativeSingularCochains R A).d p (p + 1) φ₀ = 0 := by
    have h : (relativeSingularCochains R A).dFrom p φ₀ = 0 := φ.property
    have h' := congrArg ((relativeSingularCochains R A).xNextIso
      (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hψ : (relativeSingularCochains R B).d q (q + 1) ψ₀ = 0 := by
    have h : (relativeSingularCochains R B).dFrom q ψ₀ = 0 := ψ.property
    have h' := congrArg ((relativeSingularCochains R B).xNextIso
      (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hproduct := relativeUnionSingularCochainCup_leibniz R A B p q φ₀ ψ₀
  rw [hφ, hψ] at hproduct
  simp only [map_zero, LinearMap.zero_apply, zero_add, smul_zero] at hproduct
  change (relativeUnionSingularCochains R A B).dFrom (p + q)
    (relativeUnionSingularCochainCup R A B p q φ₀ ψ₀) = 0
  rw [HomologicalComplex.dFrom_eq (r := show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1)
    from rfl), ModuleCat.comp_apply, hproduct, map_zero]

/-- The same front/back product restricted to the two original relative cocycle modules. -/
def relativeUnionSingularCocycleCup (A B : Set X) (p q : ℕ) :
    relativeSingularCocycles R A p →ₗ[R] relativeSingularCocycles R B q →ₗ[R]
      relativeUnionSingularCocycles R A B (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ ⟨relativeUnionSingularCochainCup R A B p q φ.val ψ.val,
        relativeUnionSingularCochainCup_mem_cocycles R A B p q φ ψ⟩
      map_add' := by
        intro ψ χ
        apply Subtype.ext
        exact (relativeUnionSingularCochainCup R A B p q φ.val).map_add ψ.val χ.val
      map_smul' := by
        intro a ψ
        apply Subtype.ext
        exact (relativeUnionSingularCochainCup R A B p q φ.val).map_smul a ψ.val }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply Subtype.ext
    exact congrArg (fun f ↦ f χ.val)
      ((relativeUnionSingularCochainCup R A B p q).map_add φ.val ψ.val)
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    exact congrArg (fun f ↦ f ψ.val)
      ((relativeUnionSingularCochainCup R A B p q).map_smul a φ.val)

/-- A coboundary in either original factor gives a coboundary in the joint quotient dual. -/
theorem relativeUnionSingularCocycleCup_mem_coboundaries (A B : Set X) (p q : ℕ)
    (φ : relativeSingularCocycles R A p) (ψ : relativeSingularCocycles R B q)
    (h : φ ∈ relativeSingularCoboundaries R A p ∨
      ψ ∈ relativeSingularCoboundaries R B q) :
    relativeUnionSingularCocycleCup R A B p q φ ψ ∈
      relativeUnionSingularCoboundaries R A B (p + q) := by
  /- Choose an actual relative primitive for the coboundary factor. Its
  product with the other closed relative factor is a joint cochain, by
  the same separate A/B vanishing certificate. Leibniz makes it a primitive
  of the displayed product; for a right coboundary multiply by (-1)^p.
  A degree-zero coboundary is already zero in the nonnegative complex.
  Thus the primitive lives in this exact joint complex, not merely in
  ordinary cochains or in a separately chosen cohomology representative. -/
  -- Use the actual incoming and outgoing maps of both original complexes.
  let O : CochainComplex (ModuleCat.{u} R) ℕ := relativeSingularCochains R A
  let C : CochainComplex (ModuleCat.{u} R) ℕ := relativeSingularCochains R B
  let U : CochainComplex (ModuleCat.{u} R) ℕ := relativeUnionSingularCochains R A B
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
      -- In degree zero every coboundary is zero, so the left factor itself vanishes.
      rw [hzero O φ hφ]
      simp
    | succ k =>
      obtain ⟨α, hα⟩ := hprimitive O k φ hφ
      let φ₀ : O.X (k + 1) := φ.val
      let ψ₀ : C.X q := ψ.val
      change O.d k (k + 1) α = φ₀ at hα
      have hψ₀ : C.d q (q + 1) ψ₀ = 0 := hclosed C q ψ
      have hleib := relativeUnionSingularCochainCup_leibniz R A B k q α ψ₀
      change U.d (k + q) (k + q + 1) (relativeUnionSingularCochainCup R A B k q α ψ₀) = _ at hleib
      rw [hα, hψ₀] at hleib
      simp only [map_zero, smul_zero, add_zero] at hleib
      -- The cup of the actual primitive with the closed right factor is a primitive.
      apply hboundary U (k + q) ((k + 1) + q) (by change k + q + 1 = (k + 1) + q; omega)
        (relativeUnionSingularCocycleCup R A B (k + 1) q φ ψ)
        (relativeUnionSingularCochainCup R A B k q α ψ₀)
      change U.d (k + q) ((k + 1) + q) (relativeUnionSingularCochainCup R A B k q α ψ₀) =
        relativeUnionSingularCochainCup R A B (k + 1) q φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (U.XIsoOfEq (Nat.add_right_comm k 1 q)).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
      exact hleib
  · cases q with
    | zero =>
      -- The right factor also has only the zero coboundary in degree zero.
      rw [hzero C ψ hψ]
      simp
    | succ k =>
      obtain ⟨β, hβ⟩ := hprimitive C k ψ hψ
      let φ₀ : O.X p := φ.val
      let ψ₀ : C.X (k + 1) := ψ.val
      change C.d k (k + 1) β = ψ₀ at hβ
      have hφ₀ : O.d p (p + 1) φ₀ = 0 := hclosed O p φ
      have hleib := relativeUnionSingularCochainCup_leibniz R A B p k φ₀ β
      change U.d (p + k) (p + k + 1) (relativeUnionSingularCochainCup R A B p k φ₀ β) = _ at hleib
      rw [hφ₀, hβ] at hleib
      simp only [map_zero, LinearMap.zero_apply, zero_add] at hleib
      -- The Leibniz sign is its own inverse, so it corrects this actual right primitive.
      apply hboundary U (p + k) (p + (k + 1)) (by change p + k + 1 = p + (k + 1); omega)
        (relativeUnionSingularCocycleCup R A B p (k + 1) φ ψ)
        ((-1 : R) ^ p • relativeUnionSingularCochainCup R A B p k φ₀ β)
      change U.d (p + k) (p + (k + 1))
        ((-1 : R) ^ p • relativeUnionSingularCochainCup R A B p k φ₀ β) =
        relativeUnionSingularCochainCup R A B p (k + 1) φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (U.XIsoOfEq (Nat.add_assoc p k 1).symm).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom,
        map_smul, hleib, smul_smul, ← pow_add]
      have hsign : (-1 : R) ^ (p + p) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hsign, one_smul]

end AtiyahSinger
