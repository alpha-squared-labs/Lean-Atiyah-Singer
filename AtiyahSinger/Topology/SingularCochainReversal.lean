/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCochainCup
public import AtiyahSinger.Topology.SingularReversal

/-!
# Signed reversal on the original singular cochains

Public module ID: M2125.

The actual vertex reversal is dualized on the original chain complex. Its
geometric homotopy identifies its action on cohomology with the identity.
Reversal exchanges the Alexander--Whitney front and back faces, and the
three reversal signs give the graded commutativity sign. This is the
cochain argument of Hatcher, Algebraic Topology, Theorem 3.11.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Opposite Convexity
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- The dual of the signed reversal of the original singular chains. -/
def singularCochainReversal : singularCochains R X ⟶ singularCochains R X :=
  (singularCochainDualFunctor R).map (singularReversal R X).op

/-- Signed reversal acts as the identity on the original singular cohomology. -/
theorem homologyMap_singularCochainReversal (n : ℕ) :
    HomologicalComplex.homologyMap (singularCochainReversal R X) n = 𝟙 _ := by
  -- Dualize the specified geometric homotopy, with the original unsuspended differential.
  let dual := ((linearYoneda R (ModuleCat.{u} R)).obj (singularCoefficient R)).rightOp
  have H := (dual.mapHomotopy (singularReversalHomotopy R X)).unop
  change Homotopy ((singularCochainDualFunctor R).map (𝟙 (singularChains R X)).op)
    (singularCochainReversal R X) at H
  have h := H.homologyMap_eq n
  rw [show (𝟙 (singularChains R X)).op = 𝟙 (op (singularChains R X)) from rfl,
    CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id] at h
  exact h.symm

/-- Evaluation of the actual dual reversal on an original singular generator. -/
theorem singularCochainReversal_apply (n : ℕ) (φ : (singularCochains R X).X n)
    (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌)) :
    singularCochainEquiv R X n ((singularCochainReversal R X).f n φ) σ =
      vertexReversalSign R (n + 1) •
        singularCochainEquiv R X n φ (singularSimplexReversal σ) := by
  change (show (singularChains R X).X n ⟶ singularCoefficient R from φ)
    (singularReversalComponent R X n
    ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
      (R := singularCoefficient R) σ (ULift.up 1))) = _
  rw [singularReversalComponent_generator_signed]
  exact (show (singularChains R X).X n ⟶ singularCoefficient R from φ).hom.map_smul _ _

/-- The original Alexander--Whitney cup changes order under signed vertex reversal. -/
theorem singularCochainReversal_cup (p q : ℕ)
    (φ : (singularCochains R X).X p) (ψ : (singularCochains R X).X q) :
    ((singularCochains R X).XIsoOfEq (Nat.add_comm p q)).hom
        ((singularCochainReversal R X).f (p + q) (singularCochainCup R X p q φ ψ)) =
      (-1 : R) ^ (p * q) • singularCochainCup R X q p
        ((singularCochainReversal R X).f q ψ)
        ((singularCochainReversal R X).f p φ) := by
  -- Degree transport is the ordinary equality map on the same singular generators.
  have htransport {n m : ℕ} (h : n = m) (χ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋m⦌)) :
      singularCochainEquiv R X m (((singularCochains R X).XIsoOfEq h).hom χ) σ =
        singularCochainEquiv R X n χ
          ((TopCat.toSSet.obj (TopCat.of X)).map
            (eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).op σ) := by
    subst m
    simp [HomologicalComplex.XIsoOfEq]
  have hcup (i j : ℕ) (χ : (singularCochains R X).X i)
      (η : (singularCochains R X).X j)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋i + j⦌)) :
      singularCochainEquiv R X (i + j) (singularCochainCup R X i j χ η) σ =
        singularCochainEquiv R X i χ
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace i j).op σ) *
        singularCochainEquiv R X j η
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace i j).op σ) :=
    congrFun ((singularCochainEquiv R X (i + j)).apply_symm_apply _) σ
  let S := TopCat.toSSet.obj (TopCat.of X)
  let e : ⦋p + q⦌ ⟶ ⦋q + p⦌ :=
    eqToHom (congrArg (fun k ↦ ⦋k⦌) (Nat.add_comm p q))
  have hcast {i j : ℕ} (h : i = j) (v : Fin (i + 1)) :
      ((eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).toOrderHom v).val = v.val := by
    subst j
    rfl
  -- Both reversed faces have exactly the opposite consecutive list of original vertices.
  have hface {k : ℕ} (f : ⦋k⦌ ⟶ ⦋p + q⦌) (g : ⦋k⦌ ⟶ ⦋q + p⦌)
      (h : ∀ i, e.toOrderHom (Fin.rev (f.toOrderHom i)) = g.toOrderHom (Fin.rev i))
      (σ : S.obj (op ⦋q + p⦌)) :
      S.map f.op (singularSimplexReversal (S.map e.op σ)) =
        singularSimplexReversal (S.map g.op σ) := by
    apply ((TopCat.of X).toSSetObjEquiv (op ⦋k⦌)).injective
    apply ContinuousMap.ext
    intro s
    let τ := (TopCat.of X).toSSetObjEquiv (op ⦋q + p⦌) σ
    change τ (((StdSimplex.affineMap e.toOrderHom).comp
      ((StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single ∘ Fin.rev)).comp
        (StdSimplex.affineMap f.toOrderHom))) s) =
      τ (((StdSimplex.affineMap g.toOrderHom).comp
        (StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single ∘ Fin.rev))) s)
    have heq : (StdSimplex.affineMap e.toOrderHom).comp
        ((StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single ∘ Fin.rev)).comp
          (StdSimplex.affineMap f.toOrderHom)) =
        (StdSimplex.affineMap g.toOrderHom).comp
          (StdSimplex.affineMapMk (R := ℝ) (StdSimplex.single ∘ Fin.rev)) := by
      apply StdSimplex.affineMap_ext
      intro i
      simp [h i]
    exact congrArg τ (congrArg (fun F ↦ F s) heq)
  have hfront (σ : S.obj (op ⦋q + p⦌)) :
      S.map (singularCupFrontFace p q).op (singularSimplexReversal (S.map e.op σ)) =
        singularSimplexReversal (S.map (singularCupBackFace q p).op σ) := by
    apply hface _ _ _ σ
    intro i
    apply Fin.ext
    rw [hcast (Nat.add_comm p q)]
    simp only [Fin.val_rev]
    change p + q + 1 - (i.val + 1) = q + (p + 1 - (i.val + 1))
    have hi : i.val < p + 1 := i.isLt
    omega
  have hback (σ : S.obj (op ⦋q + p⦌)) :
      S.map (singularCupBackFace p q).op (singularSimplexReversal (S.map e.op σ)) =
        singularSimplexReversal (S.map (singularCupFrontFace q p).op σ) := by
    apply hface _ _ _ σ
    intro i
    apply Fin.ext
    rw [hcast (Nat.add_comm p q)]
    simp only [Fin.val_rev]
    change p + q + 1 - (p + i.val + 1) = q + 1 - (i.val + 1)
    omega
  -- The total sign is the product of the two face signs and the Koszul sign.
  apply (singularCochainEquiv R X (q + p)).injective
  funext σ
  rw [htransport, singularCochainReversal_apply, hcup]
  change vertexReversalSign R (p + q + 1) •
      (singularCochainEquiv R X p φ
        (S.map (singularCupFrontFace p q).op (singularSimplexReversal (S.map e.op σ))) *
      singularCochainEquiv R X q ψ
        (S.map (singularCupBackFace p q).op (singularSimplexReversal (S.map e.op σ)))) = _
  rw [hfront, hback, map_smul]
  change _ = (-1 : R) ^ (p * q) •
    singularCochainEquiv R X (q + p)
      (singularCochainCup R X q p _ _) σ
  rw [hcup, singularCochainReversal_apply, singularCochainReversal_apply,
    vertexReversalSign_add_degree]
  simp only [mul_smul, smul_mul_assoc, mul_smul_comm]
  simp only [smul_smul]
  congr 1
  ring

end AtiyahSinger
