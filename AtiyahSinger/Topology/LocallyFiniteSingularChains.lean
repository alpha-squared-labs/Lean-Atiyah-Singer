/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SingularHomology
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Topology.Compactness.LocallyFinite
public import Mathlib.Topology.Sets.Compacts

/-!
# Locally finite chains on the original singular simplices

Public module ID: M1952.

A locally finite singular chain is a coefficient function on the original
singular simplices whose nonzero simplex images form a locally finite family
in the original space. This is not locally finite support in a topology on
the set of simplices. The boundary is the actual alternating face formula.
Each coefficient sum is finite: every parent of a fixed face contains any
chosen point of that face, and the original active image family is point-finite.

For a compact subset K, retain the finitely many active simplices meeting K
and apply the original quotient projection to C_*(X,X minus K). Truncation
need not commute with the boundary as an absolute finite chain. It does
commute after this prescribed quotient, because discarded faces lie outside K.
All coefficients, simplex faces and relative quotient maps remain unchanged.

Sources: the standard locally finite singular-chain definition of Borel--Moore
homology; Hatcher, Algebraic Topology, sections 2.1 and 3.3, for the underlying
singular boundary and compact-relative constructions. The explicit extension
to locally finite coefficients and these quotient comparisons are project
supplements. No inverse-limit definition of homology or triangulation of an
arbitrary topological manifold is assumed. Finite native singular chains control
the boundary-squared identity and the compact-relative restriction comparisons.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Limits Opposite TopologicalSpace Convexity
open scoped Simplicial

universe u

variable (R : Type) [CommRing R] (X : Type u) [TopologicalSpace X]

local notation "S" => TopCat.toSSet.obj (TopCat.of X)

/-- Local finiteness of the actual images of the nonzero original singular simplices. -/
def IsLocallyFiniteSingularChain (n : ℕ) (c : (S).obj (op ⦋n⦌) → R) : Prop :=
  LocallyFinite fun σ : {σ : (S).obj (op ⦋n⦌) // c σ ≠ 0} ↦
    Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ.val)

/-- The standard local-finiteness condition is closed under the original coefficient operations. -/
theorem isLocallyFiniteSingularChain_submodule (n : ℕ) :
    IsLocallyFiniteSingularChain R X n 0 ∧
      (∀ c d : (S).obj (op ⦋n⦌) → R,
        IsLocallyFiniteSingularChain R X n c → IsLocallyFiniteSingularChain R X n d →
          IsLocallyFiniteSingularChain R X n (c + d)) ∧
      (∀ (a : R) (c : (S).obj (op ⦋n⦌) → R),
        IsLocallyFiniteSingularChain R X n c →
          IsLocallyFiniteSingularChain R X n (a • c)) := by
  /- The zero coefficient function has no active simplex. A nonzero
  coefficient in a sum occurs in the union of the two original supports;
  intersect their local neighborhoods and use the union of their finite
  active index sets. Scalar multiplication only removes active simplices.
  These arguments use actual image families and require no separation axiom. -/
  classical
  -- Restricting the active coefficients preserves the original image family.
  have hmono (c d : (S).obj (op ⦋n⦌) → R)
      (h : ∀ σ, d σ ≠ 0 → c σ ≠ 0)
      (hc : IsLocallyFiniteSingularChain R X n c) :
      IsLocallyFiniteSingularChain R X n d := by
    intro x
    obtain ⟨U, hU, hfin⟩ := hc x
    refine ⟨U, hU, ((hfin.image Subtype.val).preimage
      Subtype.val_injective.injOn).subset ?_⟩
    intro σ hσ
    exact ⟨⟨σ.val, h σ.val σ.property⟩, hσ, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro x
    refine ⟨Set.univ, Filter.univ_mem, ?_⟩
    have hempty : IsEmpty {σ : (S).obj (op ⦋n⦌) // (0 : (S).obj (op ⦋n⦌) → R) σ ≠ 0} :=
      ⟨fun σ ↦ σ.property rfl⟩
    exact Set.toFinite _
  · intro c d hc hd x
    obtain ⟨U, hU, hfinU⟩ := hc x
    obtain ⟨V, hV, hfinV⟩ := hd x
    have hfin := (hfinU.image Subtype.val).union (hfinV.image Subtype.val)
    refine ⟨U ∩ V, Filter.inter_mem hU hV,
      (hfin.preimage Subtype.val_injective.injOn).subset ?_⟩
    intro σ hσ
    obtain ⟨y, hy, hyU, hyV⟩ := hσ
    by_cases hcs : c σ.val ≠ 0
    · exact Or.inl ⟨⟨σ.val, hcs⟩, ⟨y, hy, hyU⟩, rfl⟩
    · have hds : d σ.val ≠ 0 := by
        intro hd0
        apply σ.property
        simp [not_not.mp hcs, hd0]
      exact Or.inr ⟨⟨σ.val, hds⟩, ⟨y, hy, hyV⟩, rfl⟩
  · intro a c hc
    apply hmono c (a • c) _ hc
    intro σ h hc0
    apply h
    simp [hc0]

/-- The module of locally finite coefficient functions on the original singular n-simplices. -/
def locallyFiniteSingularChainModule (n : ℕ) : Submodule R ((S).obj (op ⦋n⦌) → R) where
  carrier := IsLocallyFiniteSingularChain R X n
  zero_mem' := (isLocallyFiniteSingularChain_submodule R X n).1
  add_mem' := (isLocallyFiniteSingularChain_submodule R X n).2.1 _ _
  smul_mem' := (isLocallyFiniteSingularChain_submodule R X n).2.2

/-- The original alternating-face boundary, with finite sums for every target coefficient. -/
def locallyFiniteSingularBoundaryFunction (n : ℕ)
    (c : (S).obj (op ⦋n + 1⦌) → R) : (S).obj (op ⦋n⦌) → R := by
  classical
  exact fun τ ↦ ∑ i : Fin (n + 2), ∑ᶠ σ : (S).obj (op ⦋n + 1⦌),
    if (S).map (SimplexCategory.δ i).op σ = τ then (-1 : R) ^ i.val * c σ else 0

open Classical in
/-- Local finiteness makes every coefficient sum in the displayed boundary genuinely finite. -/
theorem locallyFiniteSingularBoundaryFunction_finite_support (n : ℕ)
    (c : locallyFiniteSingularChainModule R X (n + 1))
    (i : Fin (n + 2)) (τ : (S).obj (op ⦋n⦌)) :
    (Function.support fun σ : (S).obj (op ⦋n + 1⦌) ↦
      if (S).map (SimplexCategory.δ i).op σ = τ then (-1 : R) ^ i.val * c.val σ else 0).Finite := by
  classical
  /- The standard simplex of τ is nonempty, also in degree zero. Choose
  one of its points. Every active parent with this i-th face equal to τ
  contains its image point. Local finiteness of the original image family
  gives finitely many such parents, by LocallyFinite.point_finite.
  The displayed summand support is a subset of that finite parent set.
  Thus finsum is an actual finite sum here, not its infinite-support default. -/
  let z : StdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  let x : X := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) τ z
  have hfin := c.property.point_finite x
  refine (hfin.image Subtype.val).subset ?_
  intro σ hσ
  simp only [Function.mem_support] at hσ
  split_ifs at hσ with hface
  · have hc : c.val σ ≠ 0 := by
      intro hc0
      simp [hc0] at hσ
    refine ⟨⟨σ, hc⟩, ?_, rfl⟩
    change x ∈ Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 1⦌) σ)
    refine ⟨StdSimplex.map (SimplexCategory.δ i) z, ?_⟩
    change TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)
      ((S).map (SimplexCategory.δ i).op σ) z = x
    rw [hface]
  · exact (hσ rfl).elim

/-- The actual boundary preserves local finiteness and the original module operations. -/
theorem locallyFiniteSingularBoundaryFunction_properties (n : ℕ) :
    (∀ c : locallyFiniteSingularChainModule R X (n + 1),
      IsLocallyFiniteSingularChain R X n
        (locallyFiniteSingularBoundaryFunction R X n c.val)) ∧
      (∀ c d : locallyFiniteSingularChainModule R X (n + 1),
        locallyFiniteSingularBoundaryFunction R X n (c + d).val =
          locallyFiniteSingularBoundaryFunction R X n c.val +
            locallyFiniteSingularBoundaryFunction R X n d.val) ∧
      (∀ (a : R) (c : locallyFiniteSingularChainModule R X (n + 1)),
        locallyFiniteSingularBoundaryFunction R X n (a • c).val =
          a • locallyFiniteSingularBoundaryFunction R X n c.val) := by
  /- Stage 1: a nonzero boundary coefficient has an active parent with
  that face. Each neighborhood meeting only finitely many original active
  simplices therefore meets only finitely many of their finitely many faces.
  This proves local finiteness of the actual output, including cancellations.
  Stage 2: the preceding finite-support certificate applies to each original
  parent sum. Finite union of these supports justifies distributivity and
  scalar multiplication in the displayed formula over the given CommRing.
  No domain, field, convergence or coefficient-topology assumption is used. -/
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c
    -- A nonzero boundary coefficient comes from an active original parent.
    have hparent (τ : (S).obj (op ⦋n⦌))
        (hτ : locallyFiniteSingularBoundaryFunction R X n c.val τ ≠ 0) :
        ∃ (i : Fin (n + 2)) (σ : (S).obj (op ⦋n + 1⦌)),
          c.val σ ≠ 0 ∧ (S).map (SimplexCategory.δ i).op σ = τ := by
      by_contra h
      push Not at h
      apply hτ
      unfold locallyFiniteSingularBoundaryFunction
      apply Finset.sum_eq_zero
      intro i _
      apply finsum_eq_zero_of_forall_eq_zero
      intro σ
      split_ifs with hface
      · have hc : c.val σ = 0 := by
          by_contra hc
          exact h i σ hc hface
        simp [hc]
      · rfl
    -- A neighborhood meets only faces of its finite family of active parents.
    intro x
    obtain ⟨U, hU, hfin⟩ := c.property x
    let parents : Set ((S).obj (op ⦋n + 1⦌)) :=
      Subtype.val '' Set.ofPred (fun σ : {σ : (S).obj (op ⦋n + 1⦌) // c.val σ ≠ 0} ↦
        (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 1⦌) σ.val) ∩ U).Nonempty)
    have hpfin : parents.Finite := hfin.image Subtype.val
    have hfaces : (⋃ i : Fin (n + 2), (S).map (SimplexCategory.δ i).op '' parents).Finite :=
      Set.finite_iUnion fun i ↦ hpfin.image _
    refine ⟨U, hU, (hfaces.preimage Subtype.val_injective.injOn).subset ?_⟩
    intro τ hτ
    obtain ⟨i, σ, hc, hface⟩ := hparent τ.val τ.property
    apply Set.mem_iUnion.mpr
    refine ⟨i, σ, ?_, hface⟩
    refine ⟨⟨σ, hc⟩, ?_, rfl⟩
    obtain ⟨y, ⟨z, hz⟩, hy⟩ := hτ
    refine ⟨y, ⟨StdSimplex.map (SimplexCategory.δ i) z, ?_⟩, hy⟩
    change TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌)
      ((S).map (SimplexCategory.δ i).op σ) z = y
    rw [hface]
    exact hz
  · intro c d
    -- Finite coefficient supports justify distributing the actual finsums.
    funext τ
    change (∑ i : Fin (n + 2), ∑ᶠ σ,
      if (S).map (SimplexCategory.δ i).op σ = τ then
        (-1 : R) ^ i.val * (c.val σ + d.val σ) else 0) = _
    unfold locallyFiniteSingularBoundaryFunction
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_add, ite_add_zero]
    exact finsum_add_distrib
      (locallyFiniteSingularBoundaryFunction_finite_support R X n c i τ)
      (locallyFiniteSingularBoundaryFunction_finite_support R X n d i τ)
  · intro a c
    -- The finite-support formula works over a general commutative ring.
    funext τ
    change (∑ i : Fin (n + 2), ∑ᶠ σ,
      if (S).map (SimplexCategory.δ i).op σ = τ then
        (-1 : R) ^ i.val * (a * c.val σ) else 0) =
      a * ∑ i : Fin (n + 2), ∑ᶠ σ,
        if (S).map (SimplexCategory.δ i).op σ = τ then
          (-1 : R) ^ i.val * c.val σ else 0
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_finsum' _ a
      (locallyFiniteSingularBoundaryFunction_finite_support R X n c i τ)]
    congr 1
    funext σ
    split_ifs <;> ring

/-- The genuine linear differential between locally finite singular-chain modules. -/
def locallyFiniteSingularBoundary (n : ℕ) :
    locallyFiniteSingularChainModule R X (n + 1) →ₗ[R]
      locallyFiniteSingularChainModule R X n where
  toFun c := ⟨locallyFiniteSingularBoundaryFunction R X n c.val,
    (locallyFiniteSingularBoundaryFunction_properties R X n).1 c⟩
  map_add' c d := Subtype.ext
    ((locallyFiniteSingularBoundaryFunction_properties R X n).2.1 c d)
  map_smul' a c := Subtype.ext
    ((locallyFiniteSingularBoundaryFunction_properties R X n).2.2 a c)

/-- The two alternating-face boundaries cancel on every original locally finite chain. -/
theorem locallyFiniteSingularBoundary_comp (n : ℕ) :
    ModuleCat.ofHom (locallyFiniteSingularBoundary R X (n + 1)) ≫
        ModuleCat.ofHom (locallyFiniteSingularBoundary R X n) = 0 := by
  /- Fix a target simplex and a point in its image. All nonzero double-face
  contributions come from original active simplices containing that point,
  a finite set. Compare with the ordinary finite singular chain on these
  parents. The native differential has the same alternating-face formula;
  its already-proved square-zero identity performs the simplicial sign
  cancellation. Boundary locality twice transfers that identity back to
  the original target coefficient, without interchanging infinite sums. -/
  classical
  -- Single original simplices define locally finite coefficient functions.
  have hsingle (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : R) :
      IsLocallyFiniteSingularChain R X k (Pi.single (M := fun _ ↦ R) σ a) := by
    have hsupport : (Function.support (Pi.single (M := fun _ ↦ R) σ a)).Finite := by
      refine (Set.finite_singleton σ).subset ?_
      intro τ hτ
      by_contra h
      have hne : τ ≠ σ := h
      exact hτ (by simp [hne])
    let : Fintype {τ : (S).obj (op ⦋k⦌) // Pi.single (M := fun _ ↦ R) σ a τ ≠ 0} := hsupport.fintype
    exact locallyFinite_of_finite _
  let single (k : ℕ) (σ : (S).obj (op ⦋k⦌)) :
      R →ₗ[R] locallyFiniteSingularChainModule R X k :=
    { toFun := fun a ↦ ⟨Pi.single (M := fun _ ↦ R) σ a, hsingle k σ a⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext τ
        by_cases h : τ = σ <;> simp [h, Pi.single_eq_of_ne]
      map_smul' := by
        intro a b
        apply Subtype.ext
        funext τ
        by_cases h : τ = σ <;> simp [h, Pi.single_eq_of_ne] }
  let coeff (k : ℕ) :
      ((S).chainComplex (singularCoefficient R)).X k ⟶
        ModuleCat.of R (locallyFiniteSingularChainModule R X k) :=
    Sigma.desc fun σ ↦ ModuleCat.ofHom
      ((single k σ).comp (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap)
  have hcoeff (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : ULift.{u} R) :
      coeff k ((S).ιChainComplex (R := singularCoefficient R) σ a) =
        single k σ a.down := by
    change ((S).ιChainComplex (R := singularCoefficient R) σ ≫ coeff k) a = _
    dsimp only [SSet.ιChainComplex, coeff]
    rw [Sigma.ι_comp_desc]
    rfl
  have hsingle_d (k : ℕ) (σ : (S).obj (op ⦋k + 1⦌)) (a : R) :
      locallyFiniteSingularBoundary R X k (single (k + 1) σ a) =
        ∑ i : Fin (k + 2), single k ((S).δ i σ) ((-1 : R) ^ i.val * a) := by
    apply Subtype.ext
    funext τ
    change (∑ i : Fin (k + 2), ∑ᶠ ρ,
      if (S).δ i ρ = τ then (-1 : R) ^ i.val * Pi.single (M := fun _ ↦ R) σ a ρ else 0) = _
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [finsum_eq_single _ σ (fun ρ hρ ↦ by simp [Pi.single_eq_of_ne hρ])]
    change (if (S).δ i σ = τ then (-1 : R) ^ i.val * Pi.single (M := fun _ ↦ R) σ a σ else 0) =
      Pi.single (M := fun _ ↦ R) ((S).δ i σ) ((-1 : R) ^ i.val * a) τ
    simp only [Pi.single_eq_same]
    by_cases h : (S).δ i σ = τ
    · simp [h]
    · simp [h]
  -- The coefficient map intertwines the native and locally finite differentials.
  have hcomm (k : ℕ) :
      ((S).chainComplex (singularCoefficient R)).d (k + 1) k ≫ coeff k =
        coeff (k + 1) ≫ ModuleCat.ofHom (locallyFiniteSingularBoundary R X k) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change coeff k (((S).ιChainComplex (R := singularCoefficient R) σ ≫
      ((S).chainComplex (singularCoefficient R)).d (k + 1) k) a) =
      locallyFiniteSingularBoundary R X k
        (coeff (k + 1) ((S).ιChainComplex (R := singularCoefficient R) σ a))
    rw [SSet.ιChainComplex_d, hcoeff, hsingle_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, hcoeff, ← map_zsmul]
    congr 1
    simp [zsmul_eq_mul]
  have hsq (z : ((S).chainComplex (singularCoefficient R)).X (n + 2)) :
      locallyFiniteSingularBoundary R X n
        (locallyFiniteSingularBoundary R X (n + 1) (coeff (n + 2) z)) = 0 := by
    have hz : coeff (n + 2) ≫ ModuleCat.ofHom
        (locallyFiniteSingularBoundary R X (n + 1)) ≫
          ModuleCat.ofHom (locallyFiniteSingularBoundary R X n) = 0 := by
      rw [← Category.assoc, ← hcomm (n + 1), Category.assoc, ← hcomm n,
        ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
    exact congrArg (fun f ↦ f z) hz
  -- A coefficient of the boundary depends only on parents containing its image point.
  have hlocal (k : ℕ) (x : X) (f g : (S).obj (op ⦋k + 1⦌) → R)
      (hfg : ∀ σ, x ∈ Set.range
        (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k + 1⦌) σ) → f σ = g σ)
      (τ : (S).obj (op ⦋k⦌))
      (hτ : x ∈ Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) τ)) :
      locallyFiniteSingularBoundaryFunction R X k f τ =
        locallyFiniteSingularBoundaryFunction R X k g τ := by
    unfold locallyFiniteSingularBoundaryFunction
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext σ
    split_ifs with hface
    · congr 1
      apply hfg σ
      obtain ⟨z, hz⟩ := hτ
      refine ⟨StdSimplex.map (SimplexCategory.δ i) z, ?_⟩
      change TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌)
        ((S).map (SimplexCategory.δ i).op σ) z = x
      rw [hface]
      exact hz
    · rfl
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  apply Subtype.ext
  funext τ
  let z : StdSimplex ℝ (Fin (n + 1)) := Classical.choice inferInstance
  let x : X := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) τ z
  have hfinite := (c.property.point_finite x).image Subtype.val
  let parents := hfinite.toFinset
  let finiteChain : ((S).chainComplex (singularCoefficient R)).X (n + 2) :=
    ∑ σ ∈ parents, (S).ιChainComplex (R := singularCoefficient R) σ (ULift.up (c.val σ))
  have hagree (σ : (S).obj (op ⦋n + 2⦌))
      (hσ : x ∈ Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 2⦌) σ)) :
      (coeff (n + 2) finiteChain).val σ = c.val σ := by
    simp only [finiteChain, map_sum, hcoeff, Submodule.coe_sum, Finset.sum_apply]
    change (∑ ρ ∈ parents, Pi.single (M := fun _ ↦ R) ρ (c.val ρ) σ) = c.val σ
    rw [Finset.sum_eq_single σ]
    · exact Pi.single_eq_same _ _
    · intro ρ _ hρ
      exact Pi.single_eq_of_ne (Ne.symm hρ) _
    · intro hnot
      have hc : c.val σ = 0 := by
        by_contra hc
        apply hnot
        exact hfinite.mem_toFinset.mpr ⟨⟨σ, hc⟩, hσ, rfl⟩
      simp [hc]
  have hfirst (ρ : (S).obj (op ⦋n + 1⦌))
      (hρ : x ∈ Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n + 1⦌) ρ)) :
      locallyFiniteSingularBoundaryFunction R X (n + 1) c.val ρ =
        locallyFiniteSingularBoundaryFunction R X (n + 1)
          (coeff (n + 2) finiteChain).val ρ :=
    hlocal (n + 1) x _ _ (fun σ hσ ↦ (hagree σ hσ).symm) ρ hρ
  change locallyFiniteSingularBoundaryFunction R X n
    (locallyFiniteSingularBoundaryFunction R X (n + 1) c.val) τ = 0
  rw [hlocal n x _ _ hfirst τ ⟨z, rfl⟩]
  exact congrArg (fun b : locallyFiniteSingularChainModule R X n ↦ b.val τ)
    (hsq finiteChain)

/-- The actual locally finite singular complex, with zero outgoing boundary in degree zero. -/
def locallyFiniteSingularChains : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (fun n ↦ ModuleCat.of R (locallyFiniteSingularChainModule R X n))
    (fun n ↦ ModuleCat.ofHom (locallyFiniteSingularBoundary R X n))
    (locallyFiniteSingularBoundary_comp R X)

/-- Only finitely many active original simplices meet a compact subset. -/
theorem locallyFiniteSingularChainModule_finite_meeting (K : Compacts X) (n : ℕ)
    (c : locallyFiniteSingularChainModule R X n) :
    Set.Finite (Set.ofPred fun σ : (S).obj (op ⦋n⦌) ↦ c.val σ ≠ 0 ∧
      (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ) ∩
        (K : Set X)).Nonempty) := by
  /- Apply LocallyFinite.finite_nonempty_inter_compact to the original
  nonzero simplex-image family and K.isCompact. The injective subtype-value
  map identifies its finite active index set with precisely the displayed
  set of original simplices. No compactness of X is needed. -/
  have hfin := c.property.finite_nonempty_inter_compact K.isCompact
  refine (hfin.image Subtype.val).subset ?_
  intro σ hσ
  exact ⟨⟨σ, hσ.1⟩, hσ.2, rfl⟩

/-- The finite sum of the actual original relative simplex classes which meet K. -/
def locallyFiniteSingularChainRestrictionValue (K : Compacts X) (n : ℕ)
    (c : locallyFiniteSingularChainModule R X n) :
    (relativeSingularChains R ((K : Set X)ᶜ)).X n := by
  classical
  exact ∑ᶠ σ : (S).obj (op ⦋n⦌),
    if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ) ∩
        (K : Set X)).Nonempty then
      (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f n
        ((S).ιChainComplex (R := singularCoefficient R) σ (ULift.up (c.val σ)))
    else 0

/-- The finite compact truncation into the original relative quotient is linear. -/
theorem locallyFiniteSingularChainRestrictionValue_linear (K : Compacts X) (n : ℕ) :
    (∀ c d : locallyFiniteSingularChainModule R X n,
      locallyFiniteSingularChainRestrictionValue R X K n (c + d) =
        locallyFiniteSingularChainRestrictionValue R X K n c +
          locallyFiniteSingularChainRestrictionValue R X K n d) ∧
      (∀ (a : R) (c : locallyFiniteSingularChainModule R X n),
        locallyFiniteSingularChainRestrictionValue R X K n (a • c) =
          a • locallyFiniteSingularChainRestrictionValue R X K n c) := by
  /- The preceding compact-finiteness theorem bounds the support of every
  summand by a finite set: a zero coefficient gives the zero original
  generator and hence the zero relative class. Use the union of the finite
  controls for addition. Finite-sum linearity and the original generator and
  quotient linearity prove both assertions, without using an infinite finsum. -/
  classical
  -- Package the prescribed generator and quotient as one linear coefficient map.
  let generator (σ : (S).obj (op ⦋n⦌)) :
      R →ₗ[R] (relativeSingularChains R ((K : Set X)ᶜ)).X n :=
    ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).f n).hom.comp
      (((S).ιChainComplex (R := singularCoefficient R) σ).hom.comp
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap)
  let term (c : locallyFiniteSingularChainModule R X n) (σ : (S).obj (op ⦋n⦌)) :
      (relativeSingularChains R ((K : Set X)ᶜ)).X n :=
    if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋n⦌) σ) ∩
        (K : Set X)).Nonempty then
      generator σ (c.val σ)
    else 0
  -- Compact local finiteness controls every summand, including zero coefficients.
  have hfinite (c : locallyFiniteSingularChainModule R X n) :
      (Function.support (term c)).Finite := by
    apply (locallyFiniteSingularChainModule_finite_meeting R X K n c).subset
    intro σ hσ
    change term c σ ≠ 0 at hσ
    simp only [term] at hσ
    split_ifs at hσ with hmeet
    · refine ⟨?_, hmeet⟩
      intro hc0
      simp [hc0] at hσ
    · exact (hσ rfl).elim
  -- Distribute only finite-support sums; no coefficient topology is needed.
  constructor
  · intro c d
    change (∑ᶠ σ, term (c + d) σ) = (∑ᶠ σ, term c σ) + ∑ᶠ σ, term d σ
    rw [← finsum_add_distrib (hfinite c) (hfinite d)]
    congr 1
    funext σ
    simp only [term]
    split_ifs
    · simp only [Submodule.coe_add, Pi.add_apply, map_add]
    · exact (zero_add 0).symm
  · intro a c
    change (∑ᶠ σ, term (a • c) σ) = a • ∑ᶠ σ, term c σ
    rw [smul_finsum' a (hfinite c)]
    congr 1
    funext σ
    simp only [term]
    split_ifs
    · simp only [Submodule.coe_smul, Pi.smul_apply, map_smul]
    · exact (smul_zero a).symm

/-- The actual degreewise restriction from locally finite chains to the original compact pair. -/
def locallyFiniteSingularChainRestriction (K : Compacts X) (n : ℕ) :
    locallyFiniteSingularChainModule R X n →ₗ[R]
      (relativeSingularChains R ((K : Set X)ᶜ)).X n where
  toFun := locallyFiniteSingularChainRestrictionValue R X K n
  map_add' := (locallyFiniteSingularChainRestrictionValue_linear R X K n).1
  map_smul' := (locallyFiniteSingularChainRestrictionValue_linear R X K n).2

/-- Compact truncation commutes with the actual boundary after the specified relative quotient. -/
theorem locallyFiniteSingularChainRestriction_comm (K : Compacts X) (i j : ℕ) :
    ModuleCat.ofHom (locallyFiniteSingularChainRestriction R X K i) ≫
        (relativeSingularChains R ((K : Set X)ᶜ)).d i j =
      (locallyFiniteSingularChains R X).d i j ≫
        ModuleCat.ofHom (locallyFiniteSingularChainRestriction R X K j) := by
  /- Outside adjacent chain degrees both differentials vanish. In adjacent
  degrees use the finite set of active original parent simplices meeting K.
  A parent disjoint from K has all its faces disjoint from K. For a retained
  parent, discard only faces lying wholly in X minus K; their images under
  the original relative projection are zero. The remaining alternating
  face sums are exactly both displayed composites. Absolute truncation is
  not asserted to be a chain map; the original quotient is essential. -/
  classical
  -- Single original simplices define locally finite coefficient functions.
  have hsingle (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : R) :
      IsLocallyFiniteSingularChain R X k (Pi.single (M := fun _ ↦ R) σ a) := by
    have hsupport : (Function.support (Pi.single (M := fun _ ↦ R) σ a)).Finite := by
      refine (Set.finite_singleton σ).subset ?_
      intro τ hτ
      by_contra h
      have hne : τ ≠ σ := h
      exact hτ (by simp [hne])
    let : Fintype {τ : (S).obj (op ⦋k⦌) // Pi.single (M := fun _ ↦ R) σ a τ ≠ 0} := hsupport.fintype
    exact locallyFinite_of_finite _
  let single (k : ℕ) (σ : (S).obj (op ⦋k⦌)) :
      R →ₗ[R] locallyFiniteSingularChainModule R X k :=
    { toFun := fun a ↦ ⟨Pi.single (M := fun _ ↦ R) σ a, hsingle k σ a⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext τ
        by_cases h : τ = σ <;> simp [h, Pi.single_eq_of_ne]
      map_smul' := by
        intro a b
        apply Subtype.ext
        funext τ
        by_cases h : τ = σ <;> simp [h, Pi.single_eq_of_ne] }
  let coeff (k : ℕ) :
      ((S).chainComplex (singularCoefficient R)).X k ⟶
        ModuleCat.of R (locallyFiniteSingularChainModule R X k) :=
    Sigma.desc fun σ ↦ ModuleCat.ofHom
      ((single k σ).comp (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).toLinearMap)
  have hcoeff (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : ULift.{u} R) :
      coeff k ((S).ιChainComplex (R := singularCoefficient R) σ a) =
        single k σ a.down := by
    change ((S).ιChainComplex (R := singularCoefficient R) σ ≫ coeff k) a = _
    dsimp only [SSet.ιChainComplex, coeff]
    rw [Sigma.ι_comp_desc]
    rfl
  have hsingle_d (k : ℕ) (σ : (S).obj (op ⦋k + 1⦌)) (a : R) :
      locallyFiniteSingularBoundary R X k (single (k + 1) σ a) =
        ∑ i : Fin (k + 2), single k ((S).δ i σ) ((-1 : R) ^ i.val * a) := by
    apply Subtype.ext
    funext τ
    change (∑ i : Fin (k + 2), ∑ᶠ ρ,
      if (S).δ i ρ = τ then (-1 : R) ^ i.val * Pi.single (M := fun _ ↦ R) σ a ρ else 0) = _
    simp only [Submodule.coe_sum, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [finsum_eq_single _ σ (fun ρ hρ ↦ by simp [Pi.single_eq_of_ne hρ])]
    change (if (S).δ i σ = τ then (-1 : R) ^ i.val * Pi.single (M := fun _ ↦ R) σ a σ else 0) =
      Pi.single (M := fun _ ↦ R) ((S).δ i σ) ((-1 : R) ^ i.val * a) τ
    simp only [Pi.single_eq_same]
    by_cases h : (S).δ i σ = τ
    · simp [h]
    · simp [h]
  -- The coefficient map intertwines the native and locally finite differentials.
  have hcomm (k : ℕ) :
      ((S).chainComplex (singularCoefficient R)).d (k + 1) k ≫ coeff k =
        coeff (k + 1) ≫ ModuleCat.ofHom (locallyFiniteSingularBoundary R X k) := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change coeff k (((S).ιChainComplex (R := singularCoefficient R) σ ≫
      ((S).chainComplex (singularCoefficient R)).d (k + 1) k) a) =
      locallyFiniteSingularBoundary R X k
        (coeff (k + 1) ((S).ιChainComplex (R := singularCoefficient R) σ a))
    rw [SSet.ιChainComplex_d, hcoeff, hsingle_d]
    simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul,
      LinearMap.sum_apply, LinearMap.smul_apply]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul, hcoeff, ← map_zsmul]
    congr 1
    simp [zsmul_eq_mul]
  -- A discarded simplex factors through X minus K, so its original quotient class is zero.
  have hdisjoint (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : ULift.{u} R)
      (hdisj : ¬ (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
        (K : Set X)).Nonempty) :
      (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f k
        ((S).ιChainComplex (R := singularCoefficient R) σ a) = 0 := by
    let A := (K : Set X)ᶜ
    let σmap := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ
    have hmap (z : StdSimplex ℝ (Fin (k + 1))) : σmap z ∈ A := by
      intro hz
      exact hdisj ⟨σmap z, ⟨z, rfl⟩, hz⟩
    let σA : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌) :=
      (TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋k⦌)).symm
        ⟨fun z ↦ ⟨σmap z, hmap z⟩, σmap.continuous.subtype_mk _⟩
    let inc : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hσ : (TopCat.toSSet.map (TopCat.ofHom inc)).app (op ⦋k⦌) σA = σ := by
      apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌)).injective
      ext z
      rfl
    have hgen : (singularSubspaceChains R A).f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a) =
        (S).ιChainComplex (R := singularCoefficient R) σ a := by
      change ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient R) σA ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom inc))
            (singularCoefficient R)).f k) a = _
      rw [SSet.ι_chainComplexMap_f, hσ]
    have hzero := congrArg (fun f ↦ f.f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a))
      (cokernel.condition (singularSubspaceChains R A))
    change (relativeSingularChainsProjection R A).f k
      ((singularSubspaceChains R A).f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a)) = 0 at hzero
    rw [hgen] at hzero
    exact hzero
  let generator (k : ℕ) (σ : (S).obj (op ⦋k⦌)) :
      R →ₗ[R] (relativeSingularChains R ((K : Set X)ᶜ)).X k :=
    ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).f k).hom.comp
      (((S).ιChainComplex (R := singularCoefficient R) σ).hom.comp
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap)
  -- On finite chains, the prescribed truncation is exactly the original quotient projection.
  have hrestrict_coeff (k : ℕ) :
      coeff k ≫ ModuleCat.ofHom (locallyFiniteSingularChainRestriction R X K k) =
        (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f k := by
    apply SSet.chainComplex_hom_ext
    intro σ
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change locallyFiniteSingularChainRestriction R X K k
      (coeff k ((S).ιChainComplex (R := singularCoefficient R) σ a)) = _
    rw [hcoeff]
    change (∑ᶠ ρ : (S).obj (op ⦋k⦌),
      if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) ρ) ∩
          (K : Set X)).Nonempty then
        generator k ρ (Pi.single (M := fun _ ↦ R) σ a.down ρ) else 0) =
      generator k σ a.down
    rw [finsum_eq_single _ σ (fun ρ hρ ↦ by simp [Pi.single_eq_of_ne hρ])]
    by_cases hmeet : (Set.range
      (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩ (K : Set X)).Nonempty
    · simp [hmeet]
    · simp only [hmeet, ↓reduceIte]
      exact (hdisjoint k σ a hmeet).symm
  -- Truncation only sees coefficients of simplices meeting the given compact set.
  have hrestrict_local (k : ℕ) (c d : locallyFiniteSingularChainModule R X k)
      (hcd : ∀ σ, (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
        (K : Set X)).Nonempty → c.val σ = d.val σ) :
      locallyFiniteSingularChainRestriction R X K k c =
        locallyFiniteSingularChainRestriction R X K k d := by
    change (∑ᶠ σ : (S).obj (op ⦋k⦌),
      if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
          (K : Set X)).Nonempty then generator k σ (c.val σ) else 0) =
      ∑ᶠ σ : (S).obj (op ⦋k⦌),
        if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
            (K : Set X)).Nonempty then generator k σ (d.val σ) else 0
    congr 1
    funext σ
    split_ifs with hmeet
    · rw [hcd σ hmeet]
    · rfl
  -- Every face meeting K has a parent meeting K; this gives boundary locality.
  have hboundary_local (k : ℕ) (c d : locallyFiniteSingularChainModule R X (k + 1))
      (hcd : ∀ σ, (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k + 1⦌) σ) ∩
        (K : Set X)).Nonempty → c.val σ = d.val σ)
      (τ : (S).obj (op ⦋k⦌))
      (hτ : (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) τ) ∩
        (K : Set X)).Nonempty) :
      (locallyFiniteSingularBoundary R X k c).val τ =
        (locallyFiniteSingularBoundary R X k d).val τ := by
    change locallyFiniteSingularBoundaryFunction R X k c.val τ =
      locallyFiniteSingularBoundaryFunction R X k d.val τ
    unfold locallyFiniteSingularBoundaryFunction
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    funext σ
    split_ifs with hface
    · congr 1
      apply hcd σ
      obtain ⟨x, ⟨z, hz⟩, hx⟩ := hτ
      refine ⟨x, ⟨StdSimplex.map (SimplexCategory.δ i) z, ?_⟩, hx⟩
      change TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌)
        ((S).map (SimplexCategory.δ i).op σ) z = x
      rw [hface]
      exact hz
    · rfl
  -- Local finiteness on K supplies a native finite chain controlling both sides.
  by_cases hij : j + 1 = i
  · subst i
    simp only [locallyFiniteSingularChains, ChainComplex.of_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    have hfinite := locallyFiniteSingularChainModule_finite_meeting R X K (j + 1) c
    let parents := hfinite.toFinset
    let finiteChain : ((S).chainComplex (singularCoefficient R)).X (j + 1) :=
      ∑ σ ∈ parents, (S).ιChainComplex (R := singularCoefficient R) σ (ULift.up (c.val σ))
    have hagree (σ : (S).obj (op ⦋j + 1⦌))
        (hσ : (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋j + 1⦌) σ) ∩
          (K : Set X)).Nonempty) :
        (coeff (j + 1) finiteChain).val σ = c.val σ := by
      simp only [finiteChain, map_sum, hcoeff, Submodule.coe_sum, Finset.sum_apply]
      change (∑ ρ ∈ parents, Pi.single (M := fun _ ↦ R) ρ (c.val ρ) σ) = c.val σ
      rw [Finset.sum_eq_single σ]
      · exact Pi.single_eq_same _ _
      · intro ρ _ hρ
        exact Pi.single_eq_of_ne (Ne.symm hρ) _
      · intro hnot
        have hc : c.val σ = 0 := by
          by_contra hc
          exact hnot (hfinite.mem_toFinset.mpr ⟨hc, hσ⟩)
        simp [hc]
    have hrest := hrestrict_local (j + 1) c (coeff (j + 1) finiteChain)
      (fun σ hσ ↦ (hagree σ hσ).symm)
    have hrest_d := hrestrict_local j
      (locallyFiniteSingularBoundary R X j c)
      (locallyFiniteSingularBoundary R X j (coeff (j + 1) finiteChain))
      (hboundary_local j c (coeff (j + 1) finiteChain)
        (fun σ hσ ↦ (hagree σ hσ).symm))
    change (relativeSingularChains R ((K : Set X)ᶜ)).d (j + 1) j
      (locallyFiniteSingularChainRestriction R X K (j + 1) c) =
        locallyFiniteSingularChainRestriction R X K j
          (locallyFiniteSingularBoundary R X j c)
    rw [hrest, hrest_d]
    -- Move the finite chain through its original projection and its native differential.
    calc
      _ = (relativeSingularChains R ((K : Set X)ᶜ)).d (j + 1) j
          ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).f (j + 1) finiteChain) := by
        exact congrArg ((relativeSingularChains R ((K : Set X)ᶜ)).d (j + 1) j)
          (congrArg (fun f ↦ f finiteChain) (hrestrict_coeff (j + 1)))
      _ = (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f j
          (((S).chainComplex (singularCoefficient R)).d (j + 1) j finiteChain) :=
        congrArg (fun f ↦ f finiteChain)
          ((relativeSingularChainsProjection R ((K : Set X)ᶜ)).comm (j + 1) j)
      _ = locallyFiniteSingularChainRestriction R X K j
          (coeff j (((S).chainComplex (singularCoefficient R)).d (j + 1) j finiteChain)) :=
        (congrArg (fun f ↦ f (((S).chainComplex (singularCoefficient R)).d
          (j + 1) j finiteChain)) (hrestrict_coeff j)).symm
      _ = _ := congrArg (locallyFiniteSingularChainRestriction R X K j)
        (congrArg (fun f ↦ f finiteChain) (hcomm j))
  · have hshape : ¬ (ComplexShape.down ℕ).Rel i j := hij
    rw [(relativeSingularChains R ((K : Set X)ᶜ)).shape i j hshape,
      (locallyFiniteSingularChains R X).shape i j hshape, comp_zero]
    exact zero_comp.symm

/-- The actual restriction chain map to the original compact-relative singular complex. -/
def locallyFiniteSingularChainsRestriction (K : Compacts X) :
    locallyFiniteSingularChains R X ⟶ relativeSingularChains R ((K : Set X)ᶜ) where
  f n := ModuleCat.ofHom (locallyFiniteSingularChainRestriction R X K n)
  comm' i j _ := locallyFiniteSingularChainRestriction_comm R X K i j

/-- Restriction at a larger compact control followed by the original pair inclusion agrees. -/
theorem locallyFiniteSingularChainsRestriction_inclusion {K L : Compacts X} (h : K ≤ L) :
    locallyFiniteSingularChainsRestriction R X L ≫
        relativeSingularChainsMap R (ContinuousMap.id X)
          (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ) ((K : Set X)ᶜ)
            from fun _ hx ↦ (Set.compl_subset_compl.mpr h) hx) =
      locallyFiniteSingularChainsRestriction R X K := by
  /- Work degreewise on the finite original set of active simplices meeting L.
  Those meeting K have exactly the same coefficient and original relative
  simplex image on both sides. Every other retained simplex is disjoint
  from K, so its image under the original quotient for X minus K is zero.
  This proves the square for the actual restriction maps, not a selected
  equivalence or an assumed inverse-limit model. -/
  classical
  -- Simplices missing K factor through its complement and vanish in its quotient.
  have hdisjoint (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : ULift.{u} R)
      (hdisj : ¬ (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
        (K : Set X)).Nonempty) :
      (relativeSingularChainsProjection R ((K : Set X)ᶜ)).f k
        ((S).ιChainComplex (R := singularCoefficient R) σ a) = 0 := by
    let A := (K : Set X)ᶜ
    let σmap := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ
    have hmap (z : StdSimplex ℝ (Fin (k + 1))) : σmap z ∈ A := by
      intro hz
      exact hdisj ⟨σmap z, ⟨z, rfl⟩, hz⟩
    let σA : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋k⦌) :=
      (TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋k⦌)).symm
        ⟨fun z ↦ ⟨σmap z, hmap z⟩, σmap.continuous.subtype_mk _⟩
    let inc : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hσ : (TopCat.toSSet.map (TopCat.ofHom inc)).app (op ⦋k⦌) σA = σ := by
      apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌)).injective
      ext z
      rfl
    have hgen : (singularSubspaceChains R A).f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a) =
        (S).ιChainComplex (R := singularCoefficient R) σ a := by
      change ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient R) σA ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom inc))
            (singularCoefficient R)).f k) a = _
      rw [SSet.ι_chainComplexMap_f, hσ]
    have hzero := congrArg (fun f ↦ f.f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a))
      (cokernel.condition (singularSubspaceChains R A))
    change (relativeSingularChainsProjection R A).f k
      ((singularSubspaceChains R A).f k
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient R) σA a)) = 0 at hzero
    rw [hgen] at hzero
    exact hzero
  -- The original pair map intertwines the two original quotient projections.
  let inclusion := relativeSingularChainsMap R (ContinuousMap.id X)
    (show Set.MapsTo (ContinuousMap.id X) ((L : Set X)ᶜ) ((K : Set X)ᶜ)
      from fun _ hx ↦ (Set.compl_subset_compl.mpr h) hx)
  have hprojection : relativeSingularChainsProjection R ((L : Set X)ᶜ) ≫ inclusion =
      relativeSingularChainsProjection R ((K : Set X)ᶜ) := by
    simp [inclusion, relativeSingularChainsMap, relativeSingularChainsProjection]
  let generator (H : Compacts X) (k : ℕ) (σ : (S).obj (op ⦋k⦌)) :
      R →ₗ[R] (relativeSingularChains R ((H : Set X)ᶜ)).X k :=
    ((relativeSingularChainsProjection R ((H : Set X)ᶜ)).f k).hom.comp
      (((S).ιChainComplex (R := singularCoefficient R) σ).hom.comp
        (ULift.moduleEquiv : ULift.{u} R ≃ₗ[R] R).symm.toLinearMap)
  let term (H : Compacts X) (k : ℕ) (c : locallyFiniteSingularChainModule R X k)
      (σ : (S).obj (op ⦋k⦌)) : (relativeSingularChains R ((H : Set X)ᶜ)).X k :=
    if (Set.range (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩
        (H : Set X)).Nonempty then generator H k σ (c.val σ) else 0
  -- Compactness supplies the support certificate before mapping a finsum.
  have hfinite (k : ℕ) (c : locallyFiniteSingularChainModule R X k) :
      (Function.support (term L k c)).Finite := by
    apply (locallyFiniteSingularChainModule_finite_meeting R X L k c).subset
    intro σ hσ
    change term L k c σ ≠ 0 at hσ
    simp only [term] at hσ
    split_ifs at hσ with hmeet
    · refine ⟨?_, hmeet⟩
      intro hc0
      simp [hc0] at hσ
    · exact (hσ rfl).elim
  have hgen (k : ℕ) (σ : (S).obj (op ⦋k⦌)) (a : R) :
      inclusion.f k (generator L k σ a) = generator K k σ a :=
    congrArg (fun f ↦ f.f k ((S).ιChainComplex
      (R := singularCoefficient R) σ (ULift.up a))) hprojection
  -- Compare each original simplex: classes outside K vanish after the pair map.
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  change inclusion.f k (∑ᶠ σ, term L k c σ) = ∑ᶠ σ, term K k c σ
  rw [map_finsum _ (hfinite k c)]
  congr 1
  funext σ
  by_cases hK : (Set.range
    (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩ (K : Set X)).Nonempty
  · have hL : (Set.range
        (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩ (L : Set X)).Nonempty :=
      hK.mono (Set.inter_subset_inter_right _ h)
    simp only [term, hK, hL, ↓reduceIte]
    exact hgen k σ (c.val σ)
  · by_cases hL : (Set.range
        (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋k⦌) σ) ∩ (L : Set X)).Nonempty
    · simp only [term, hK, hL, ↓reduceIte]
      rw [hgen]
      exact hdisjoint k σ (ULift.up (c.val σ)) hK
    · simp only [term, hK, hL, ↓reduceIte, map_zero]

end AtiyahSinger
