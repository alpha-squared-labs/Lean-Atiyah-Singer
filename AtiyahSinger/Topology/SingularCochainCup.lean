/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularCohomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# The original singular cochain cup product

Public module ID: M2124.

D11: Hatcher, Algebraic Topology, section 3.2, pp.206--213, especially
Lemma 3.6. The Alexander--Whitney front/back formula is implemented on
the actual singular simplices of the existing singular chain complex.
Evaluation at the original free generators identifies its linear dual
with simplex functions. The inverse uses the same free coproduct, not
another cochain complex. The cup product is their genuine pointwise
front/back evaluation followed by that inverse linear equivalence.

The kernel and image adapters below are exactly the existing short-complex
homology API. The cocycle product therefore descends to the original
singular cohomology quotient. No replacement cohomology theory or product
supplied as an assumption is introduced. Degrees zero, arbitrary small
commutative coefficient rings and arbitrary topological spaces are included.

The differential is the original unsuspended dual differential, φ ↦ φ ∘ ∂,
so its Leibniz sign is (-1) ^ p. This cochain product is associative and
unital but is not asserted graded commutative before passing to cohomology.
The Leibniz identity, cocycle closure, coboundary ideal property and unit closure
are proved below for these original cochains.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

/-- Generator evaluation identifies the original cochains with all singular-simplex functions. -/
def singularCochainEquiv (n : ℕ) :
    (singularCochains R X).X n ≃ₗ[R]
      ((TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) → ULift.{u} R) where
  toFun φ σ :=
    (show (singularChains R X).X n ⟶ singularCoefficient R from φ)
      ((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex
        (R := singularCoefficient R) σ (ULift.up 1))
  invFun F := Sigma.desc fun σ ↦ ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight (F σ))
  left_inv φ := by
    -- Equality on the original coproduct summands is equality of cochains.
    change (∐ fun _ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n⦌) ↦
      singularCoefficient R) ⟶ singularCoefficient R at φ
    apply Sigma.hom_ext
    intro σ
    dsimp only [SSet.ιChainComplex]
    rw [Sigma.ι_comp_desc]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change r.down • φ ((Sigma.ι (fun _ ↦ singularCoefficient R) σ) (ULift.up 1)) =
      (Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫ φ) r
    rw [ModuleCat.comp_apply]
    have hr : r = r.down • (ULift.up (1 : R) : ULift.{u} R) := by
      apply ULift.ext
      simp
    conv_rhs => rw [hr]
    rw [map_smul, map_smul]
  right_inv F := by
    -- The linear extension has the prescribed value on each generator with coefficient one.
    funext σ
    change (Sigma.ι (fun _ ↦ singularCoefficient R) σ ≫
      Sigma.desc (fun τ ↦ ModuleCat.ofHom
        ((ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap.smulRight (F τ))))
      (ULift.up 1) = F σ
    rw [Sigma.ι_comp_desc]
    change (1 : R) • F σ = F σ
    exact one_smul R (F σ)
  map_add' φ ψ := by
    funext σ
    rfl
  map_smul' a φ := by
    funext σ
    rfl

/-- The ordered front face consists of vertices 0 through p of the original (p + q)-simplex. -/
def singularCupFrontFace (p q : ℕ) : ⦋p⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ ⟨i.val,
        Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_add_right p q))⟩
      monotone' := fun _ _ h ↦ h }

/-- The ordered back face consists of vertices p through p + q, sharing vertex p with the front. -/
def singularCupBackFace (p q : ℕ) : ⦋q⦌ ⟶ ⦋p + q⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i ↦ ⟨p + i.val, Nat.add_lt_add_left i.isLt p⟩
      monotone' := fun _ _ h ↦ Nat.add_le_add_left h p }

/-- The actual Alexander--Whitney cup formula, as a bilinear map on the original cochains. -/
def singularCochainCup (p q : ℕ) :
    (singularCochains R X).X p →ₗ[R]
      (singularCochains R X).X q →ₗ[R] (singularCochains R X).X (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ (singularCochainEquiv R X (p + q)).symm fun σ ↦
        singularCochainEquiv R X p φ
            ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ) *
          singularCochainEquiv R X q ψ
            ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ)
      map_add' := by
        intro ψ χ
        apply (singularCochainEquiv R X (p + q)).injective
        funext σ
        simp [map_add, mul_add]
      map_smul' := by
        intro a ψ
        apply (singularCochainEquiv R X (p + q)).injective
        funext σ
        simp [map_smul] }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply (singularCochainEquiv R X (p + q)).injective
    funext σ
    simp [map_add, add_mul]
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply (singularCochainEquiv R X (p + q)).injective
    funext σ
    simp [map_smul]

/-- Hatcher Lemma 3.6 with the signs of the original dual singular differential. -/
theorem singularCochainCup_leibniz (p q : ℕ)
    (φ : (singularCochains R X).X p) (ψ : (singularCochains R X).X q) :
    (singularCochains R X).d (p + q) (p + q + 1) (singularCochainCup R X p q φ ψ) =
      ((singularCochains R X).XIsoOfEq (Nat.add_right_comm p 1 q)).hom
          (singularCochainCup R X (p + 1) q ((singularCochains R X).d p (p + 1) φ) ψ) +
        (-1 : R) ^ p •
          ((singularCochains R X).XIsoOfEq (Nat.add_assoc p q 1).symm).hom
            (singularCochainCup R X p (q + 1) φ ((singularCochains R X).d q (q + 1) ψ)) := by
  /- Evaluate on an arbitrary original (p + q + 1)-simplex using
  SSet.ιChainComplex_d. Split its alternating face sum at the shared
  vertex p. Removing a vertex in the front block gives δφ cup ψ;
  removing one in the back block gives (-1) ^ p φ cup δψ. The two
  occurrences of the middle face cancel with opposite signs. The
  displayed XIsoOfEq maps only reconcile equal natural-number degree
  expressions; they do not change a simplex, coefficient or differential.
  Generator extensionality proves the cochain equality, including p=0
  and q=0. No commutativity of cup on cochains is used. -/
  classical
  -- Evaluate the unchanged dual differential on the original free generators.
  have hdiffLift (n : ℕ) (φ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n + 1⦌)) :
      singularCochainEquiv R X (n + 1) ((singularCochains R X).d n (n + 1) φ) σ =
        ∑ i : Fin (n + 2), (-1 : R) ^ i.val • singularCochainEquiv R X n φ
          ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X n ⟶ singularCoefficient R from φ)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (singularCoefficient R)).d (n + 1) n) (ULift.up 1)) = _
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℤ) ^ i.val) •
      singularCochainEquiv R X n φ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = _
    rw [← Int.cast_smul_eq_zsmul R]
    simp
  have htransport {n m : ℕ} (h : n = m) (φ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋m⦌)) :
      singularCochainEquiv R X m (((singularCochains R X).XIsoOfEq h).hom φ) σ =
        singularCochainEquiv R X n φ
          ((TopCat.toSSet.obj (TopCat.of X)).map
            (eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).op σ) := by
    subst m
    simp [HomologicalComplex.XIsoOfEq]
  have hcup (p q : ℕ) (φ : (singularCochains R X).X p)
      (ψ : (singularCochains R X).X q)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋p + q⦌)) :
      singularCochainEquiv R X (p + q) (singularCochainCup R X p q φ ψ) σ =
        singularCochainEquiv R X p φ
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace p q).op σ) *
        singularCochainEquiv R X q ψ
          ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace p q).op σ) := by
    exact congrFun ((singularCochainEquiv R X (p + q)).apply_symm_apply _) σ
  let ev (k : ℕ) (χ : (singularCochains R X).X k)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k⦌)) : R :=
    (singularCochainEquiv R X k χ τ).down
  have hdiff (k : ℕ) (χ : (singularCochains R X).X k)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋k + 1⦌)) :
      ev (k + 1) ((singularCochains R X).d k (k + 1) χ) τ =
        ∑ i : Fin (k + 2), (-1 : R) ^ i.val *
          ev k χ ((TopCat.toSSet.obj (TopCat.of X)).δ i τ) := by
    have h := congrArg (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R) (hdiffLift k χ τ)
    simp only [map_sum, map_smul, smul_eq_mul] at h
    exact h
  have hcupDown (i j : ℕ) (χ : (singularCochains R X).X i)
      (η : (singularCochains R X).X j)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋i + j⦌)) :
      ev (i + j) (singularCochainCup R X i j χ η) τ =
        ev i χ ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupFrontFace i j).op τ) *
          ev j η ((TopCat.toSSet.obj (TopCat.of X)).map (singularCupBackFace i j).op τ) :=
    congrArg ULift.down (hcup i j χ η τ)
  have htransportDown {i j : ℕ} (h : i = j) (χ : (singularCochains R X).X i)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋j⦌)) :
      ev j (((singularCochains R X).XIsoOfEq h).hom χ) τ =
        ev i χ ((TopCat.toSSet.obj (TopCat.of X)).map
          (eqToHom (congrArg (fun k ↦ ⦋k⦌) h)).op τ) :=
    congrArg ULift.down (htransport h χ τ)
  have hmap {i j k : SimplexCategory} (f : i ⟶ j) (g : j ⟶ k)
      (τ : (TopCat.toSSet.obj (TopCat.of X)).obj (op k)) :
      (TopCat.toSSet.obj (TopCat.of X)).map f.op
          ((TopCat.toSSet.obj (TopCat.of X)).map g.op τ) =
        (TopCat.toSSet.obj (TopCat.of X)).map (f ≫ g).op τ := by
    rw [op_comp, Functor.map_comp]
    rfl
  apply (singularCochainEquiv R X (p + q + 1)).injective
  funext σ
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply]
  apply ULift.ext
  change ev (p + q + 1) ((singularCochains R X).d (p + q) (p + q + 1)
      (singularCochainCup R X p q φ ψ)) σ =
    ev (p + q + 1) (((singularCochains R X).XIsoOfEq (Nat.add_right_comm p 1 q)).hom
      (singularCochainCup R X (p + 1) q ((singularCochains R X).d p (p + 1) φ) ψ)) σ +
    (-1 : R) ^ p * ev (p + q + 1)
      (((singularCochains R X).XIsoOfEq (Nat.add_assoc p q 1).symm).hom
        (singularCochainCup R X p (q + 1) φ ((singularCochains R X).d q (q + 1) ψ))) σ
  rw [hdiff, htransportDown, htransportDown, hcupDown, hcupDown, hdiff, hdiff]
  simp_rw [hcupDown]
  simp only [SimplicialObject.δ, hmap]
  -- Identify the same ordered faces, retaining both canonical degree transports.
  have hfront (k l : ℕ) (i : Fin (k + 1)) :
      ((singularCupFrontFace k l).toOrderHom i).val = i.val := rfl
  have hback (k l : ℕ) (i : Fin (l + 1)) :
      ((singularCupBackFace k l).toOrderHom i).val = k + i.val := rfl
  have hδ (k : ℕ) (i : Fin (k + 2)) (j : Fin (k + 1)) :
      ((SimplexCategory.δ i).toOrderHom j).val =
        if j.val < i.val then j.val else j.val + 1 := by
    change (if j.val < i.val then j.castSucc else j.succ).val = _
    split_ifs <;> rfl
  have hcast {s t : SimplexCategory} (h : s = t) (i : Fin (s.len + 1)) :
      ((eqToHom h).toOrderHom i).val = i.val := by
    subst t
    rfl
  let N : ℕ := p + q + 1
  let t₁ : ⦋(p + 1) + q⦌ ⟶ ⦋N⦌ :=
    eqToHom (congrArg (fun n ↦ ⦋n⦌) (Nat.add_right_comm p 1 q))
  let t₂ : ⦋p + (q + 1)⦌ ⟶ ⦋N⦌ :=
    eqToHom (congrArg (fun n ↦ ⦋n⦌) (Nat.add_assoc p q 1).symm)
  -- The pair a,b belongs to dφ cup ψ; the pair c,d belongs to φ cup dψ.
  let a : ⦋p + 1⦌ ⟶ ⦋N⦌ := singularCupFrontFace (p + 1) q ≫ t₁
  let b : ⦋q⦌ ⟶ ⦋N⦌ := singularCupBackFace (p + 1) q ≫ t₁
  let c : ⦋p⦌ ⟶ ⦋N⦌ := singularCupFrontFace p (q + 1) ≫ t₂
  let d : ⦋q + 1⦌ ⟶ ⦋N⦌ := singularCupBackFace p (q + 1) ≫ t₂
  let left (i : Fin (p + 1)) : Fin (p + q + 2) := ⟨i.val, by omega⟩
  let right (j : Fin (q + 1)) : Fin (p + q + 2) := ⟨p + 1 + j.val, by omega⟩
  have ha (i : Fin (p + 1)) :
      singularCupFrontFace p q ≫ SimplexCategory.δ (left i) =
        SimplexCategory.δ i.castSucc ≫ a := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [a, t₁, left, hcast, hfront, hδ, Fin.val_castSucc,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
  have hb (i : Fin (p + 1)) :
      singularCupBackFace p q ≫ SimplexCategory.δ (left i) = b := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [b, t₁, left, hcast, hback, hδ,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    split_ifs <;> omega
  have hc (j : Fin (q + 1)) :
      singularCupFrontFace p q ≫ SimplexCategory.δ (right j) = c := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [c, t₂, right, hcast, hfront, hδ,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    split_ifs <;> omega
  have hd (j : Fin (q + 1)) :
      singularCupBackFace p q ≫ SimplexCategory.δ (right j) =
        SimplexCategory.δ j.succ ≫ d := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [d, t₂, right, hcast, hback, hδ, Fin.val_succ,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    split_ifs <;> omega
  -- These two exceptional middle faces coincide, with opposite Leibniz signs.
  have hlast : SimplexCategory.δ (Fin.last (p + 1)) ≫ a = c := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [a, c, t₁, t₂, hcast, hfront, hδ, Fin.val_last,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    split_ifs <;> omega
  have hzero : SimplexCategory.δ (0 : Fin (q + 2)) ≫ d = b := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    apply Fin.ext
    simp only [b, d, t₁, t₂, hcast, hback, hδ, Fin.val_zero, Nat.not_lt_zero, ite_false,
      SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply]
    omega
  let F (f : ⦋p⦌ ⟶ ⦋N⦌) : R :=
    ev p φ ((TopCat.toSSet.obj (TopCat.of X)).map f.op σ)
  let G (g : ⦋q⦌ ⟶ ⦋N⦌) : R :=
    ev q ψ ((TopCat.toSSet.obj (TopCat.of X)).map g.op σ)
  change (∑ i : Fin (p + q + 2), (-1 : R) ^ i.val *
    (F (singularCupFrontFace p q ≫ SimplexCategory.δ i) *
      G (singularCupBackFace p q ≫ SimplexCategory.δ i))) =
    (∑ i : Fin (p + 2), (-1 : R) ^ i.val * F (SimplexCategory.δ i ≫ a)) * G b +
      (-1 : R) ^ p * (F c * ∑ j : Fin (q + 2), (-1 : R) ^ j.val * G (SimplexCategory.δ j ≫ d))
  -- Split the alternating boundary at the common front/back vertex.
  have hsplit (f : Fin (p + q + 2) → R) :
      ∑ i, f i = (∑ i : Fin (p + 1), f (left i)) +
        ∑ j : Fin (q + 1), f (right j) := by
    let e : Fin ((p + 1) + (q + 1)) ≃ Fin (p + q + 2) := finCongr (by omega)
    rw [← Equiv.sum_comp e f, Fin.sum_univ_add]
    rfl
  rw [hsplit,
    Fin.sum_univ_castSucc (fun i : Fin (p + 2) ↦ (-1 : R) ^ i.val * F (SimplexCategory.δ i ≫ a)),
    Fin.sum_univ_succ (fun j : Fin (q + 2) ↦ (-1 : R) ^ j.val * G (SimplexCategory.δ j ≫ d))]
  simp only [ha, hb, hc, hd, hlast, hzero, left, right,
    Fin.val_castSucc, Fin.val_last, Fin.val_succ, Fin.val_zero, pow_zero, one_mul]
  -- The two middle terms cancel; all other terms retain their original signs.
  simp only [pow_add, pow_succ, neg_mul, mul_neg,
    Finset.sum_mul, Finset.mul_sum, mul_add, add_mul]
  ring_nf
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The actual cocycle kernel used by the existing ModuleCat homology quotient. -/
abbrev singularCocycles (n : ℕ) : ModuleCat.{u} R :=
  ((singularCochains R X).sc n).moduleCatLeftHomologyData.K

/-- The actual image of the original incoming differential, inside that same cocycle kernel. -/
abbrev singularCoboundaries (n : ℕ) : Submodule R (singularCocycles R X n) :=
  ((singularCochains R X).sc n).moduleCatToCycles.range

/-- The original cup product of two cocycles lies in the original cocycle kernel. -/
theorem singularCochainCup_mem_cocycles (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : singularCocycles R X q) :
    ((singularCochains R X).sc (p + q)).g
      (singularCochainCup R X p q φ.val ψ.val) = 0 := by
  /- In the up-shaped complex the outgoing differential at n is the
  original d(n,n + 1). Apply the Leibniz formula to the two kernel elements.
  Both differentiated inputs are zero, and bilinearity makes both terms
  zero. The original short-complex kernel, rather than a separately chosen
  space of closed cochains, is the target used here. -/
  -- Use the original next-degree isomorphisms rather than changing the kernel model.
  let φ₀ : (singularCochains R X).X p := φ.val
  let ψ₀ : (singularCochains R X).X q := ψ.val
  have hφ : (singularCochains R X).d p (p + 1) φ₀ = 0 := by
    have h : (singularCochains R X).dFrom p φ₀ = 0 := φ.property
    have h' := congrArg ((singularCochains R X).xNextIso
      (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hψ : (singularCochains R X).d q (q + 1) ψ₀ = 0 := by
    have h : (singularCochains R X).dFrom q ψ₀ = 0 := ψ.property
    have h' := congrArg ((singularCochains R X).xNextIso
      (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)).hom h
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at h'
    exact h'
  have hproduct := singularCochainCup_leibniz R X p q φ₀ ψ₀
  rw [hφ, hψ] at hproduct
  simp only [map_zero, LinearMap.zero_apply, zero_add, smul_zero] at hproduct
  change (singularCochains R X).dFrom (p + q) (singularCochainCup R X p q φ₀ ψ₀) = 0
  rw [HomologicalComplex.dFrom_eq (r := show (ComplexShape.up ℕ).Rel (p + q) (p + q + 1)
    from rfl), ModuleCat.comp_apply, hproduct, map_zero]

/-- The same cup formula restricted to the original cocycle modules. -/
def singularCocycleCup (p q : ℕ) :
    singularCocycles R X p →ₗ[R] singularCocycles R X q →ₗ[R]
      singularCocycles R X (p + q) where
  toFun φ :=
    { toFun := fun ψ ↦ ⟨singularCochainCup R X p q φ.val ψ.val,
        singularCochainCup_mem_cocycles R X p q φ ψ⟩
      map_add' := by
        intro ψ χ
        apply Subtype.ext
        exact (singularCochainCup R X p q φ.val).map_add ψ.val χ.val
      map_smul' := by
        intro a ψ
        apply Subtype.ext
        exact (singularCochainCup R X p q φ.val).map_smul a ψ.val }
  map_add' := by
    intro φ ψ
    apply LinearMap.ext
    intro χ
    apply Subtype.ext
    exact congrArg (fun f ↦ f χ.val) ((singularCochainCup R X p q).map_add φ.val ψ.val)
  map_smul' := by
    intro a φ
    apply LinearMap.ext
    intro ψ
    apply Subtype.ext
    exact congrArg (fun f ↦ f ψ.val) ((singularCochainCup R X p q).map_smul a φ.val)

/-- Multiplying a cocycle by a coboundary on either side gives an actual coboundary. -/
theorem singularCocycleCup_mem_coboundaries (p q : ℕ)
    (φ : singularCocycles R X p) (ψ : singularCocycles R X q)
    (h : φ ∈ singularCoboundaries R X p ∨ ψ ∈ singularCoboundaries R X q) :
    singularCocycleCup R X p q φ ψ ∈ singularCoboundaries R X (p + q) := by
  /- Split the two sides of the supplied image-membership hypothesis.
  If the corresponding degree is zero, the incoming differential in
  the original nonnegative cochain complex is zero, so that factor is
  zero. Otherwise take its actual preimage under moduleCatToCycles.
  Leibniz expresses the cup with the other closed factor as the
  differential of the cup with that preimage. For a right coboundary,
  multiply this primitive by (-1) ^ p; this scalar is its own inverse.
  These are preimages under the target's original incoming differential,
  so the conclusion is in precisely the original range submodule.
  No quotient representative or coefficient ring is replaced. -/
  -- Relate the actual short-complex image to primitives in the preceding degree.
  let C : CochainComplex (ModuleCat.{u} R) ℕ := singularCochains R X
  have hclosed (k : ℕ) (χ : singularCocycles R X k) : C.d k (k + 1) χ.val = 0 := by
    let v : C.X k := χ.val
    have hχ : C.dFrom k v = 0 := χ.property
    have hχ' := congrArg (C.xNextIso
      (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl)).hom hχ
    rw [← ModuleCat.comp_apply, HomologicalComplex.dFrom_comp_xNextIso, map_zero] at hχ'
    exact hχ'
  have hzero (χ : singularCocycles R X 0) (hχ : χ ∈ singularCoboundaries R X 0) :
      χ = 0 := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change C.dTo 0 β = χ.val at hval
    have hd : C.dTo 0 = 0 := C.shape _ _ (by
      change ¬ (ComplexShape.up ℕ).prev 0 + 1 = 0
      omega)
    rw [hd] at hval
    apply Subtype.ext
    exact hval.symm
  have hprimitive (k : ℕ) (χ : singularCocycles R X (k + 1))
      (hχ : χ ∈ singularCoboundaries R X (k + 1)) :
      ∃ β : C.X k, C.d k (k + 1) β = χ.val := by
    obtain ⟨β, hβ⟩ := hχ
    have hval := congrArg Subtype.val hβ
    change C.dTo (k + 1) β = χ.val at hval
    have hrel : (ComplexShape.up ℕ).Rel k (k + 1) := rfl
    refine ⟨(C.xPrevIso hrel).hom β, ?_⟩
    have hcomp := congrArg (fun f : C.xPrev (k + 1) ⟶ C.X (k + 1) ↦ f β)
      (C.dTo_eq hrel)
    exact hcomp.symm.trans hval
  have hboundary (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j)
      (χ : singularCocycles R X j) (β : C.X i) (hβ : C.d i j β = χ.val) :
      χ ∈ singularCoboundaries R X j := by
    refine ⟨(C.xPrevIso hij).inv β, ?_⟩
    apply Subtype.ext
    change C.dTo j ((C.xPrevIso hij).inv β) = χ.val
    rw [← ModuleCat.comp_apply, HomologicalComplex.xPrevIso_comp_dTo]
    exact hβ
  rcases h with hφ | hψ
  · cases p with
    | zero =>
      -- Degree zero has no incoming boundary, so the left factor itself vanishes.
      rw [hzero φ hφ]
      simp
    | succ k =>
      obtain ⟨α, hα⟩ := hprimitive k φ hφ
      let φ₀ : C.X (k + 1) := φ.val
      let ψ₀ : C.X q := ψ.val
      change C.d k (k + 1) α = φ₀ at hα
      have hψ₀ : C.d q (q + 1) ψ₀ = 0 := hclosed q ψ
      have hleib := singularCochainCup_leibniz R X k q α ψ₀
      change C.d (k + q) (k + q + 1) (singularCochainCup R X k q α ψ₀) = _ at hleib
      rw [hα, hψ₀] at hleib
      simp only [map_zero, smul_zero, add_zero] at hleib
      -- The cup of the actual primitive with the closed right factor is a primitive.
      apply hboundary (k + q) ((k + 1) + q) (by change k + q + 1 = (k + 1) + q; omega)
        (singularCocycleCup R X (k + 1) q φ ψ) (singularCochainCup R X k q α ψ₀)
      change C.d (k + q) ((k + 1) + q) (singularCochainCup R X k q α ψ₀) =
        singularCochainCup R X (k + 1) q φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (C.XIsoOfEq (Nat.add_right_comm k 1 q)).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom]
      exact hleib
  · cases q with
    | zero =>
      -- The same incoming-degree-zero argument applies to the right factor.
      rw [hzero ψ hψ]
      simp
    | succ k =>
      obtain ⟨β, hβ⟩ := hprimitive k ψ hψ
      let φ₀ : C.X p := φ.val
      let ψ₀ : C.X (k + 1) := ψ.val
      change C.d k (k + 1) β = ψ₀ at hβ
      have hφ₀ : C.d p (p + 1) φ₀ = 0 := hclosed p φ
      have hleib := singularCochainCup_leibniz R X p k φ₀ β
      change C.d (p + k) (p + k + 1) (singularCochainCup R X p k φ₀ β) = _ at hleib
      rw [hφ₀, hβ] at hleib
      simp only [map_zero, LinearMap.zero_apply, zero_add] at hleib
      -- The Leibniz sign is its own inverse, so it corrects this actual right primitive.
      apply hboundary (p + k) (p + (k + 1)) (by change p + k + 1 = p + (k + 1); omega)
        (singularCocycleCup R X p (k + 1) φ ψ)
        ((-1 : R) ^ p • singularCochainCup R X p k φ₀ β)
      change C.d (p + k) (p + (k + 1)) ((-1 : R) ^ p • singularCochainCup R X p k φ₀ β) =
        singularCochainCup R X p (k + 1) φ₀ ψ₀
      apply (ModuleCat.mono_iff_injective
        (C.XIsoOfEq (Nat.add_assoc p k 1).symm).hom).mp inferInstance
      rw [← ModuleCat.comp_apply, HomologicalComplex.d_comp_XIsoOfEq_hom,
        map_smul, hleib, smul_smul, ← pow_add]
      have hsign : (-1 : R) ^ (p + p) = 1 := by
        rw [← two_mul, pow_mul]
        norm_num
      rw [hsign, one_smul]

/-- The actual degree-zero cochain which evaluates to one on every original vertex simplex. -/
def singularCochainOne : (singularCochains R X).X 0 :=
  (singularCochainEquiv R X 0).symm fun _ ↦ 1

/-- The constant-one cochain is closed for the original alternating-face differential. -/
theorem singularCochainOne_mem_cocycles :
    ((singularCochains R X).sc 0).g (singularCochainOne R X) = 0 := by
  /- Evaluate on each actual singular edge. Its two endpoint evaluations
  are one and one, and the original alternating boundary subtracts them.
  Generator extensionality then gives the zero cochain. This also applies
  to the empty space, whose degree-zero cochain module is zero. -/
  -- Evaluate on each original edge; the two constant endpoint values cancel.
  have hdiff (n : ℕ) (φ : (singularCochains R X).X n)
      (σ : (TopCat.toSSet.obj (TopCat.of X)).obj (op ⦋n + 1⦌)) :
      singularCochainEquiv R X (n + 1) ((singularCochains R X).d n (n + 1) φ) σ =
        ∑ i : Fin (n + 2), (-1 : R) ^ i.val • singularCochainEquiv R X n φ
          ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) := by
    change (show ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
      (singularCoefficient R)).X n ⟶ singularCoefficient R from φ)
      (((TopCat.toSSet.obj (TopCat.of X)).ιChainComplex σ ≫
      ((TopCat.toSSet.obj (TopCat.of X)).chainComplex
        (singularCoefficient R)).d (n + 1) n) (ULift.up 1)) = _
    rw [SSet.ιChainComplex_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro i _
    change ((-1 : ℤ) ^ i.val) •
      singularCochainEquiv R X n φ ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) = _
    rw [← Int.cast_smul_eq_zsmul R]
    simp
  have hnext : (ComplexShape.up ℕ).next 0 = 1 :=
    (ComplexShape.up ℕ).next_eq' rfl
  change (singularCochains R X).d 0 ((ComplexShape.up ℕ).next 0) (singularCochainOne R X) = 0
  rw [hnext]
  apply (singularCochainEquiv R X 1).injective
  funext σ
  change singularCochainEquiv R X 1
    ((singularCochains R X).d 0 1 (singularCochainOne R X)) σ = 0
  rw [hdiff]
  simp only [singularCochainOne, LinearEquiv.apply_symm_apply]
  change (∑ i : Fin 2, (-1 : R) ^ i.val • (1 : ULift.{u} R)) = 0
  rw [Fin.sum_univ_two]
  norm_num

/-- The same constant-one cochain as an element of the original degree-zero cocycle kernel. -/
def singularCocycleOne : singularCocycles R X 0 :=
  ⟨singularCochainOne R X, singularCochainOne_mem_cocycles R X⟩

end AtiyahSinger
