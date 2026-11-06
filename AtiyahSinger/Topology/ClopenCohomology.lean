/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.CochainProduct
public import AtiyahSinger.Topology.SingularCochainCup
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Singular cohomology of a clopen decomposition

Public module ID: M1616.

A locally constant map partitions the original space into its actual fibers.
Every singular simplex lies in one fiber, because its standard simplex is
nonempty and connected. The free chain modules therefore decompose as direct
sums on precisely these simplices. Dualizing those original free modules gives
the unrestricted product of the fiber cochains, with the original differential.

The resulting cohomology comparison is the family of actual inclusion
pullbacks. It is bijective in every degree over any commutative coefficient
ring. Neither a finite family, bounded ranks, compactness, separation nor local
contractibility is assumed. The small indexing type is lifted internally to
the base universe, without changing the fibers or the public comparison.

This is the standard disjoint-union property of singular cohomology, written
on the project's existing singular complexes for clopen rank-stratum assembly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Convexity Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] {X : Type u} [TopologicalSpace X]
  {ι : Type} (p : X → ι)

private def locallyConstantSimplexSumEquiv (hp : IsLocallyConstant p) (n : ℕ) :
    ((i : ι) × (TopCat.toSSet.obj (TopCat.of {x : X // p x = i})).obj (op ⦋n⦌)) ≃
      (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) := by
  classical
  let e := fun (i : ι) ↦ (TopCat.of {x : X // p x = i}).toSSetObjEquiv (op ⦋n⦌)
  let eX := (TopCat.of X).toSSetObjEquiv (op ⦋n⦌)
  let f := fun s : (i : ι) ×
      (TopCat.toSSet.obj (TopCat.of {x : X // p x = i})).obj (op ⦋n⦌) ↦
    (TopCat.toSSet.map (TopCat.ofHom
      (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = s.1}, X)))).app
        (op ⦋n⦌) s.2
  apply Equiv.ofBijective f
  constructor
  · rintro ⟨i, σ⟩ ⟨j, τ⟩ h
    -- One vertex identifies the fiber; inclusion is then injective on the entire simplex.
    have hij : i = j := by
      let t := Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))
      have ht := congrArg (fun z ↦ p (eX z t)) h
      exact (e i σ t).property.symm.trans (ht.trans (e j τ t).property)
    subst j
    have hστ : σ = τ := by
      apply (e i).injective
      ext t
      exact congrArg (fun z ↦ eX z t) h
    exact congrArg (Sigma.mk i) hστ
  · intro σ
    -- Connectedness makes this original simplex factor through one actual fiber.
    let t := Classical.arbitrary (StdSimplex ℝ (Fin (n + 1)))
    let i := p (eX σ t)
    have hconstant (s : StdSimplex ℝ (Fin (n + 1))) : p (eX σ s) = i :=
      (hp.comp_continuous (eX σ).continuous).apply_eq_of_preconnectedSpace s t
    let τ : C(StdSimplex ℝ (Fin (n + 1)), {x : X // p x = i}) :=
      ⟨fun s ↦ ⟨eX σ s, hconstant s⟩, (eX σ).continuous.subtype_mk _⟩
    refine ⟨⟨i, (e i).symm τ⟩, ?_⟩
    apply eX.injective
    ext s
    rfl

/-- Restriction of the original cochains to all actual fibers of the given map. -/
def singularCochainsFiberRestriction :
    singularCochains R X ⟶ cochainFamilyProduct R
      (fun i : ULift.{u} ι ↦ singularCochains R {x : X // p x = i.down}) where
  f n := ModuleCat.ofHom
    { toFun := fun φ i ↦
        ((singularCochainsFunctor R).map (TopCat.ofHom
          (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i.down}, X))).op).f n φ
      map_add' := by intros; ext; exact map_add _ _ _
      map_smul' := by intros; ext; exact map_smul _ _ _ }
  comm' n k _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro φ
    funext i
    exact congrArg (fun f ↦ f φ)
      (((singularCochainsFunctor R).map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i.down}, X))).op).comm n k)

private theorem singularCochainsFiberRestriction_bijective
    (hp : IsLocallyConstant p) (n : ℕ) :
    Function.Bijective ((singularCochainsFiberRestriction R p).f n) := by
  classical
  let e := locallyConstantSimplexSumEquiv p hp n
  let ev := singularCochainEquiv R X n
  let evFiber := fun i : ι ↦ singularCochainEquiv R {x : X // p x = i} n
  -- The dual of each original inclusion evaluates on the same free chain generator.
  have hrestriction (φ : (singularCochains R X).X n) (i : ι)
      (σ : (TopCat.toSSet.obj (TopCat.of {x : X // p x = i})).obj (op ⦋n⦌)) :
      evFiber i (((singularCochainsFiberRestriction R p).f n φ) ⟨i⟩) σ =
        ev φ (e ⟨i, σ⟩) := by
    change (((TopCat.toSSet.obj (TopCat.of {x : X // p x = i})).ιChainComplex σ ≫
      (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i}, X))))
          (singularCoefficient R)).f n) ≫ φ) (ULift.up 1) = _
    rw [SSet.ι_chainComplexMap_f]
    rfl
  constructor
  · intro φ ψ h
    -- All original generators occur in one fiber, so restrictions detect cochains.
    apply ev.injective
    funext σ
    obtain ⟨⟨i, τ⟩, rfl⟩ := e.surjective σ
    rw [← hrestriction, ← hrestriction, h]
  · intro ψ
    -- An unrestricted family assigns a value to each generator in its unique fiber.
    let φ := ev.symm fun σ ↦ evFiber (e.symm σ).1 (ψ ⟨(e.symm σ).1⟩) (e.symm σ).2
    refine ⟨φ, ?_⟩
    funext i
    apply (evFiber i.down).injective
    funext σ
    rw [hrestriction]
    change ev (ev.symm _) (e ⟨i.down, σ⟩) = _
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The original cochains are the unrestricted product of cochains on the clopen fibers. -/
private def singularCochainsLocallyConstantFiberIso (hp : IsLocallyConstant p) :
    singularCochains R X ≅ cochainFamilyProduct R
      (fun i : ULift.{u} ι ↦ singularCochains R {x : X // p x = i.down}) := by
  let f := singularCochainsFiberRestriction R p
  letI (n : ℕ) : IsIso (f.f n) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (singularCochainsFiberRestriction_bijective R p hp n)
  letI : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

/-- The actual inclusion pullbacks identify cohomology with the product over clopen fibers. -/
theorem singularCohomologyPullback_fibers_bijective (hp : IsLocallyConstant p) (n : ℕ) :
    Function.Bijective (fun c : singularCohomology R X n ↦ fun i : ι ↦
      singularCohomologyPullback R
        (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i}, X)) n c) := by
  -- The genuine cochain isomorphism and the existing product theorem give bijectivity.
  let C := fun i : ULift.{u} ι ↦ singularCochains R {x : X // p x = i.down}
  let e := singularCochainsLocallyConstantFiberIso R p hp
  have h := (bijective_homologyMap_cochainFamilyProductProjection R C n).comp
    (ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap e.hom n))
  -- Identify every projection with the specified original inclusion pullback.
  have hmap (i : ULift.{u} ι) : e.hom ≫ cochainFamilyProductProjection R C i =
      (singularCochainsFunctor R).map (TopCat.ofHom
        (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i.down}, X))).op := by
    rfl
  have hcomparison (c : singularCohomology R X n) (i : ULift.{u} ι) :
      HomologicalComplex.homologyMap (cochainFamilyProductProjection R C i) n
        (HomologicalComplex.homologyMap e.hom n c) =
      singularCohomologyPullback R
        (⟨Subtype.val, continuous_subtype_val⟩ : C({x : X // p x = i.down}, X)) n c := by
    change (HomologicalComplex.homologyMap e.hom n ≫
      HomologicalComplex.homologyMap (cochainFamilyProductProjection R C i) n) c = _
    rw [← HomologicalComplex.homologyMap_comp, hmap]
    rfl
  -- Remove only the universe lift of the index, preserving all original fiber classes.
  constructor
  · intro a b hab
    apply h.injective
    funext i
    exact (hcomparison a i).trans ((congrFun hab i.down).trans (hcomparison b i).symm)
  · intro c
    obtain ⟨a, ha⟩ := h.surjective (fun i ↦ c i.down)
    refine ⟨a, ?_⟩
    funext i
    exact (hcomparison a ⟨i⟩).symm.trans (congrFun ha ⟨i⟩)

end AtiyahSinger
