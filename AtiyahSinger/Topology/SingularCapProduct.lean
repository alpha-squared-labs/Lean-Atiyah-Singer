/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomologyCup
public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The Alexander--Whitney cap product on the original singular chains

Public module ID: M2122.

D11: Hatcher, Algebraic Topology, section 3.3, pp.239--240, the cap-product
formula preceding Poincare duality. A degree-p cochain evaluates the front face
of an original (p+q)-simplex; its value is the coefficient of the back
q-face. The chain extension uses the original free coproduct, not a
replacement chain model or an unspecified pairing.

We write the cochain argument first. With the existing unsuspended dual
differential the boundary identity is
`d (cap phi c) = (-1)^p (cap phi (d c) - cap (d phi) c)`.
The original singular chains are nonnegative, including degree zero.
All coefficients are the same small commutative ring R; ULift changes
only universes. Both the generator formula and boundary identity are proved
for these original objects. The boundary proof evaluates against coefficient
cochains and uses the already established cup Leibniz identity; the original
free coproduct's coordinate projections separate chains over every such ring.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Evaluate the original front face and retain the original back face, extended linearly. -/
def singularCochainCap (p q : ℕ) :
    (singularCochains R X).X p →ₗ[R]
      (singularChains R X).X (p + q) →ₗ[R] (singularChains R X).X q := by
  -- Expose the original free chain objects before their coproduct universal property.
  let C (k : ℕ) : ModuleCat.{u} R :=
    ∐ fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌) ↦ singularCoefficient R
  change (singularCochains R X).X p →ₗ[R] C (p + q) →ₗ[R] C q
  -- Extend the prescribed front/back value along the original free chain coproduct.
  let T (φ : (singularCochains R X).X p) : C (p + q) ⟶ C q :=
    Sigma.desc fun σ ↦ ConcreteCategory.ofHom (C := ModuleCat R)
      (X := singularCoefficient R) (Y := C q)
      ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight
        ((Sigma.ι (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋q⦌) ↦
          singularCoefficient R)
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ))
            (singularCochainEquiv R X p φ
              ((TopCat.toSSet.obj (TopCat.of X)).map
                (singularCupFrontFace p q).op σ))))
  -- Linearity in the cochain is checked on those same coproduct summands.
  exact
    { toFun := fun φ ↦ (T φ).hom
      map_add' := by
        intro φ ψ
        change (T (φ + ψ)).hom = (T φ + T ψ).hom
        apply congrArg ModuleCat.Hom.hom
        apply Sigma.hom_ext
        intro σ
        change Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ T (φ + ψ) =
          Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ (T φ + T ψ)
        dsimp only [T, C]
        rw [Preadditive.comp_add, Sigma.ι_comp_desc, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro a
        simp [map_add, smul_add]
      map_smul' := by
        intro a φ
        change (T (a • φ)).hom = (a • T φ).hom
        apply congrArg ModuleCat.Hom.hom
        apply Sigma.hom_ext
        intro σ
        change Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ T (a • φ) =
          Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ (a • T φ)
        dsimp only [T, C]
        rw [Linear.comp_smul, Sigma.ι_comp_desc, Sigma.ι_comp_desc]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        simp [map_smul, smul_smul, mul_comm] }

/-- On a generator, cap is precisely front-face evaluation times the back-face generator. -/
theorem singularCochainCap_simplex (p q : ℕ)
    (φ : (singularCochains R X).X p)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋p + q⦌)) :
    singularCochainCap R X p q φ
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ (ULift.up 1)) =
      (singularCochainEquiv R X p φ
        ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ)).down •
          (TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
            (R := singularCoefficient R)
            ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ)
            (ULift.up 1) := by
  -- Evaluate the original coproduct extension on its specified coefficient-one generator.
  change (Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ Sigma.desc _) (ULift.up 1) = _
  rw [Sigma.ι_comp_desc]
  change (1 : R) •
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R)
      ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ)) _ = _
  rw [one_smul]
  rw [← map_smul]
  congr 1
  apply ULift.ext
  simp

/-- The cap boundary formula with the sign of the original dual differential. -/
theorem singularCochainCap_boundary (p q : ℕ)
    (φ : (singularCochains R X).X p)
    (c : (singularChains R X).X (p + (q + 1))) :
    (singularChains R X).d (q + 1) q (singularCochainCap R X p (q + 1) φ c) =
      (-1 : R) ^ p •
        (singularCochainCap R X p q φ
            ((singularChains R X).d (p + (q + 1)) (p + q) c) -
          singularCochainCap R X (p + 1) q
            ((singularCochains R X).d p (p + 1) φ)
            (((singularChains R X).XIsoOfEq
              ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1))).hom c)) := by
  /- The standard alternating-face argument is already captured by the cup Leibniz identity.
  The front/back cup--cap pairing transfers that identity to these original chains. Coordinate
  cochains separate the free chain module over arbitrary commutative rings, so no field or
  nontriviality assumption is needed. The only scalar cancellation uses ((-1)^p)^2 = 1. -/
  classical
  -- Evaluate using the given dual complex; the differential is precomposition with boundary.
  let ev (k : ℕ) (χ : (singularCochains R X).X k) :
      (singularChains R X).X k →ₗ[R] ULift.{u} R :=
    (show (singularChains R X).X k ⟶ singularCoefficient R from χ).hom
  have hdiff (i j : ℕ) (χ : (singularCochains R X).X i)
      (z : (singularChains R X).X j) :
      ev j ((singularCochains R X).d i j χ) z =
        ev i χ ((singularChains R X).d j i z) := by rfl
  have htransport {i j : ℕ} (h : i = j) (χ : (singularCochains R X).X i)
      (z : (singularChains R X).X j) :
      ev j (((singularCochains R X).XIsoOfEq h).hom χ) z =
        ev i χ (((singularChains R X).XIsoOfEq h.symm).hom z) := by
    subst j
    rfl
  -- On each original simplex, cup evaluates the same front and back faces as cap.
  have hcap (i j : ℕ) (α : (singularCochains R X).X i)
      (β : (singularCochains R X).X j) (z : (singularChains R X).X (i + j)) :
      ev j β (singularCochainCap R X i j α z) =
        ev (i + j) (singularCochainCup R X i j α β) z := by
    change ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X j ⟶ singularCoefficient R at β
    have h : ModuleCat.ofHom (β.hom.comp (singularCochainCap R X i j α)) =
        singularCochainCup R X i j α β := by
      apply (singularCochainEquiv R X (i + j)).injective
      funext σ
      change β (singularCochainCap R X i j α
        ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
          (R := singularCoefficient R) σ (ULift.up 1))) = _
      rw [singularCochainCap_simplex]
      change β.hom (_ • _) = _
      rw [map_smul]
      have hcup := congrFun ((singularCochainEquiv R X (i + j)).apply_symm_apply
        (fun σ ↦ singularCochainEquiv R X i α
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace i j).op σ) *
          singularCochainEquiv R X j β
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace i j).op σ))) σ
      rw [show singularCochainEquiv R X (i + j) (singularCochainCup R X i j α β) σ = _
        from hcup]
      apply ULift.ext
      rfl
    exact congrArg (fun f : (singularChains R X).X (i + j) ⟶ singularCoefficient R ↦ f z) h
  -- The original chain coproduct is separated by its coefficient projections over any ring.
  have hsep (x y : (singularChains R X).X q)
      (h : ∀ ψ : (singularCochains R X).X q, ev q ψ x = ev q ψ y) : x = y := by
    let e := ModuleCat.coprodIsoDirectSum
      (fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋q⦌) ↦ singularCoefficient R)
    apply e.toLinearEquiv.injective
    apply DirectSum.ext
    intro σ
    exact h (ModuleCat.ofHom ((DirectSum.component R _ _ σ).comp e.hom.hom))
  apply hsep
  intro ψ
  rw [map_smul, map_sub, ← hdiff, hcap, hcap, hcap]
  -- Evaluate the already proved cup Leibniz identity on the same chain, with its degree casts.
  have h := congrArg (fun χ ↦ ev (p + q + 1) χ
    (((singularChains R X).XIsoOfEq (Nat.add_assoc p q 1).symm).hom c))
    (singularCochainCup_leibniz R X p q φ ψ)
  change ev (p + q + 1) ((singularCochains R X).d (p + q) (p + q + 1)
      (singularCochainCup R X p q φ ψ)) _ =
    ev (p + q + 1) (((singularCochains R X).XIsoOfEq
      (Nat.add_right_comm p 1 q)).hom (singularCochainCup R X (p + 1) q
        ((singularCochains R X).d p (p + 1) φ) ψ)) _ +
    (-1 : R) ^ p • ev (p + q + 1) (((singularCochains R X).XIsoOfEq
      (Nat.add_assoc p q 1).symm).hom (singularCochainCup R X p (q + 1) φ
        ((singularCochains R X).d q (q + 1) ψ))) _ at h
  rw [hdiff, htransport, htransport] at h
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, ModuleCat.id_apply] at h
  change ev (p + q) (singularCochainCup R X p q φ ψ)
    ((singularChains R X).d (p + (q + 1)) (p + q) c) =
      ev (p + 1 + q) (singularCochainCup R X (p + 1) q
        ((singularCochains R X).d p (p + 1) φ) ψ)
        (((singularChains R X).XIsoOfEq
          ((Nat.add_assoc p q 1).symm.trans (Nat.add_right_comm p q 1))).hom c) +
      (-1 : R) ^ p • ev (p + (q + 1)) (singularCochainCup R X p (q + 1) φ
        ((singularCochains R X).d q (q + 1) ψ)) c at h
  -- Solve the evaluated Leibniz identity for boundary(cap); the parity sign squares to one.
  rw [h, add_sub_cancel_left, smul_smul]
  rw [← pow_add, ← two_mul, pow_mul]
  simp

/-- The original singular-cycle kernel, using the same short-complex homology model. -/
abbrev singularCycles (n : ℕ) : ModuleCat.{u} R :=
  ((singularChains R X).sc n).moduleCatLeftHomologyData.K

/-- The original incoming-boundary image inside the original singular-cycle kernel. -/
abbrev singularBoundaries (n : ℕ) : Submodule R (singularCycles R X n) :=
  ((singularChains R X).sc n).moduleCatToCycles.range

/-- The class of an original cycle in the already defined singular homology. -/
def singularCycleClass (n : ℕ) : singularCycles R X n →ₗ[R] singularHomology R X n :=
  (((singularChains R X).sc n).moduleCatHomologyIso.inv.hom).comp
    (singularBoundaries R X n).mkQ

end AtiyahSinger
