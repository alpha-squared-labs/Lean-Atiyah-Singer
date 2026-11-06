/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The universal polynomials of a multiplicative sequence

Public module ID: M0040.

SL04: SG III.11, printed pp.228--230, especially Lemma 11.9; MS section 19,
printed pp.219--222, especially Lemma 19.1. The finite root product is an
actual formal power series with polynomial coefficients. The inverse of
mathlib's elementary-symmetric algebra equivalence then constructs its
universal polynomials. Their values on arbitrary coefficients construct the
sequence transformation; multiplicativity is a theorem, not an input field.

The power-series variable records degree. Coefficients are evaluated in an
ordinary commutative rational algebra. For a graded algebra, the weighted
homogeneity theorem keeps the degree-k output in its original degree-k
submodule. SG uses even or fourfold cohomological degrees for this reason;
the entire signed graded-commutative cohomology ring is not assumed to be
an ordinary commutative ring.

No Chern class, geometric Chern root, splitting space, or Chern character
is assumed or constructed here. The root variables are the actual free
polynomial variables used in the source's algebraic proof. Symmetry, weighted homogeneity,
root-count stability, multiplicativity, normalization, and graded membership
are proved below for these original algebraic constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.MultiplicativeSequence

open scoped BigOperators

/-- The genuine product of the given series at n free roots, with degree recorded formally. -/
def rootProduct (f : PowerSeries ℚ) (n : ℕ) :
    PowerSeries (MvPolynomial (Fin n) ℚ) :=
  ∏ i : Fin n, PowerSeries.mk fun k : ℕ ↦
    MvPolynomial.C (PowerSeries.coeff k f) * MvPolynomial.X i ^ k

/-- Every coefficient of the free-root product is a symmetric polynomial. -/
theorem isSymmetric_coeff_rootProduct (f : PowerSeries ℚ) (n k : ℕ) :
    (PowerSeries.coeff k (rootProduct f n)).IsSymmetric := by
  /- A permutation of the original n free variables permutes exactly the
  n factors. Apply coefficientwise polynomial renaming and reindex the
  finite product by that permutation. Coefficient extraction commutes
  with this ring homomorphism. The empty product covers n=0, and the
  coefficient statement also covers k=0. No normalization of f is needed. -/
  classical
  intro σ
  -- Renaming sends each factor to the factor indexed by the permuted root.
  have hfactor (i : Fin n) :
      PowerSeries.map (MvPolynomial.rename σ).toRingHom
          (PowerSeries.mk fun j : ℕ ↦
            MvPolynomial.C (PowerSeries.coeff j f) * MvPolynomial.X i ^ j) =
        PowerSeries.mk (fun j : ℕ ↦
          MvPolynomial.C (PowerSeries.coeff j f) * MvPolynomial.X (σ i) ^ j) := by
    ext j
    simp
  -- The permutation reindexes the whole product, including the empty product.
  have hproduct :
      PowerSeries.map (MvPolynomial.rename σ).toRingHom (rootProduct f n) =
        rootProduct f n := by
    simp only [rootProduct, map_prod, hfactor]
    exact Equiv.prod_comp σ (fun i : Fin n ↦ PowerSeries.mk fun j : ℕ ↦
      MvPolynomial.C (PowerSeries.coeff j f) * MvPolynomial.X i ^ j)
  -- Extracting a coefficient commutes with the coefficient-ring homomorphism.
  exact (PowerSeries.coeff_map (MvPolynomial.rename σ).toRingHom k
    (rootProduct f n)).symm.trans (congrArg (PowerSeries.coeff k) hproduct)

/-- The k-th universal polynomial, obtained from the actual elementary-symmetric inverse. -/
def polynomial (f : PowerSeries ℚ) (k : ℕ) : MvPolynomial (Fin k) ℚ :=
  (MvPolynomial.esymmAlgEquiv (Fin k) ℚ (Fintype.card_fin k)).symm
    ⟨PowerSeries.coeff k (rootProduct f k), isSymmetric_coeff_rootProduct f k k⟩

/-- The series degree equals total root degree; used for homogeneity and root-count stability. -/
private theorem isWeightedHomogeneous_coeff_rootProduct (f : PowerSeries ℚ) (n k : ℕ) :
    (PowerSeries.coeff k (rootProduct f n)).IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) k := by
  classical
  have hprod (s : Finset (Fin n)) (j : ℕ) :
      (PowerSeries.coeff j (∏ i ∈ s, PowerSeries.mk fun d : ℕ ↦
        MvPolynomial.C (PowerSeries.coeff d f) * MvPolynomial.X i ^ d)).IsWeightedHomogeneous
          (fun _ ↦ (1 : ℕ)) j := by
    induction s using Finset.induction_on generalizing j with
    | empty =>
      simp only [Finset.prod_empty, PowerSeries.coeff_one]
      split_ifs with hj
      · subst j
        exact MvPolynomial.isWeightedHomogeneous_one _ _
      · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
    | @insert i s hi ih =>
      rw [Finset.prod_insert hi, PowerSeries.coeff_mul]
      apply MvPolynomial.IsWeightedHomogeneous.sum
      intro p hp
      rw [PowerSeries.coeff_mk]
      have hdegree : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
      rw [← hdegree]
      have hfactor :
          (MvPolynomial.C (PowerSeries.coeff p.1 f) * MvPolynomial.X i ^ p.1).IsWeightedHomogeneous
            (fun _ ↦ (1 : ℕ)) p.1 := by
        simpa using ((MvPolynomial.isWeightedHomogeneous_X ℚ
          (fun _ : Fin n ↦ (1 : ℕ)) i).pow p.1).C_mul (PowerSeries.coeff p.1 f)
      exact hfactor.mul (ih p.2)
  exact hprod Finset.univ k

/-- Algebraically independent elementary symmetric polynomials reflect the weighted grading. -/
private theorem isWeightedHomogeneous_of_esymm (n k : ℕ) (p : MvPolynomial (Fin n) ℚ)
    (hp : (MvPolynomial.aeval
      (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℚ (i.val + 1)) p).IsWeightedHomogeneous
        (fun _ ↦ (1 : ℕ)) k) :
    p.IsWeightedHomogeneous (fun i : Fin n ↦ i.val + 1) k := by
  classical
  let w : Fin n → ℕ := fun i ↦ i.val + 1
  let e : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
    MvPolynomial.aeval (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℚ (i.val + 1))
  -- Elementary symmetric substitution sends a monomial's weight to its root degree.
  have hesymm (j : ℕ) :
      (MvPolynomial.esymm (Fin n) ℚ j).IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) j := by
    rw [MvPolynomial.esymm]
    apply MvPolynomial.IsWeightedHomogeneous.sum
    intro s hs
    have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
    simpa [hcard] using MvPolynomial.IsWeightedHomogeneous.prod s
      (fun i : Fin n ↦ (MvPolynomial.X i : MvPolynomial (Fin n) ℚ))
      (fun _ ↦ (1 : ℕ))
      (fun i _ ↦ MvPolynomial.isWeightedHomogeneous_X ℚ (fun _ ↦ (1 : ℕ)) i)
  have hmonomial (d : Fin n →₀ ℕ) (r : ℚ) :
      (e (MvPolynomial.monomial d r)).IsWeightedHomogeneous
        (fun _ ↦ (1 : ℕ)) (Finsupp.weight w d) := by
    dsimp only [e]
    rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
    apply MvPolynomial.IsWeightedHomogeneous.C_mul
    simpa [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, w] using
      MvPolynomial.IsWeightedHomogeneous.prod d.support
        (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℚ (i.val + 1) ^ d i)
        (fun i : Fin n ↦ d i • (i.val + 1))
        (fun i _ ↦ (hesymm (i.val + 1)).pow (d i))
  -- Consequently, projecting onto degree k commutes with this substitution.
  have hcomm (q : MvPolynomial (Fin n) ℚ) :
      MvPolynomial.weightedHomogeneousComponent (fun _ ↦ (1 : ℕ)) k (e q) =
        e (MvPolynomial.weightedHomogeneousComponent w k q) := by
    induction q using MvPolynomial.induction_on' with
    | monomial d r =>
      rw [MvPolynomial.weightedHomogeneousComponent_of_mem (hmonomial d r),
        MvPolynomial.weightedHomogeneousComponent_of_mem
          (MvPolynomial.isWeightedHomogeneous_monomial w d r rfl)]
      split_ifs <;> simp [e]
    | add q r hq hr => simp only [map_add, hq, hr]
  -- Algebraic independence reflects equality with the degree-k component.
  have heinj : Function.Injective e := by
    intro q r hqr
    apply MvPolynomial.esymmAlgHom_fin_injective ℚ (n := n) (m := n) le_rfl
    apply Subtype.ext
    simpa only [MvPolynomial.esymmAlgHom_apply] using hqr
  have heq : MvPolynomial.weightedHomogeneousComponent w k p = p := by
    apply heinj
    rw [← hcomm, hp.weightedHomogeneousComponent_same]
  rw [← heq]
  exact MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous k p

/-- The i-th coefficient variable has weight i+1, and the k-th polynomial has weight k. -/
theorem polynomial_isWeightedHomogeneous (f : PowerSeries ℚ) (k : ℕ) :
    (polynomial f k).IsWeightedHomogeneous (fun i : Fin k ↦ (i : ℕ) + 1) k := by
  /- Stage 1: every monomial in the coefficient of degree k in rootProduct
  has total root degree k, by the finite Cauchy-product formula.
  Stage 2: elementary symmetric polynomial number i+1 is homogeneous
  of root degree i+1. Decompose the actual inverse polynomial into its
  weighted homogeneous components. Their elementary-symmetric images
  lie in distinct ordinary homogeneous degrees. Algebraic independence,
  equivalently injectivity of esymmAlgHom, makes every weight except k
  vanish. This includes the empty-variable polynomial at k=0. -/
  apply isWeightedHomogeneous_of_esymm k k
  -- The defining inverse identifies the image with the actual root coefficient.
  have heval :
      MvPolynomial.aeval (fun i : Fin k ↦ MvPolynomial.esymm (Fin k) ℚ (i.val + 1))
        (polynomial f k) = PowerSeries.coeff k (rootProduct f k) := by
    rw [← MvPolynomial.esymmAlgHom_apply]
    exact congrArg Subtype.val
      ((MvPolynomial.esymmAlgEquiv (Fin k) ℚ (Fintype.card_fin k)).apply_symm_apply
        ⟨PowerSeries.coeff k (rootProduct f k), isSymmetric_coeff_rootProduct f k k⟩)
  rw [heval]
  exact isWeightedHomogeneous_coeff_rootProduct f k k

/-- The same universal polynomial gives the degree-k coefficient for any number of roots. -/
theorem polynomial_esymm (f : PowerSeries ℚ) (hf : f.constantCoeff = 1) (n k : ℕ) :
    MvPolynomial.aeval (fun i : Fin k ↦ MvPolynomial.esymm (Fin n) ℚ ((i : ℕ) + 1))
        (polynomial f k) =
      PowerSeries.coeff k (rootProduct f n) := by
  /- First establish that setting surplus roots to zero preserves both
  the root product and the elementary symmetric polynomials. For n ≤ k,
  specialize the defining k-root inverse identity directly. For k ≤ n,
  the inverse polynomial for the n-root coefficient has weight k, so
  it uses only the first k coefficient variables. Specializing to k roots
  and using algebraic independence identifies it with polynomial f k.
  These arguments include n=0 and k=0 without a geometric splitting assumption. -/
  classical
  let ρ (m n : ℕ) : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
    MvPolynomial.aeval (fun i : Fin n ↦
      if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m) else 0)
  let e (n t : ℕ) : MvPolynomial (Fin t) ℚ →ₐ[ℚ] MvPolynomial (Fin n) ℚ :=
    MvPolynomial.aeval (fun i : Fin t ↦ MvPolynomial.esymm (Fin n) ℚ (i.val + 1))
  -- Removing a root replaces its series factor by the unit because f(0) = 1.
  have hroot (m n j : ℕ) (hmn : m ≤ n) :
      ρ m n (PowerSeries.coeff j (rootProduct f n)) =
        PowerSeries.coeff j (rootProduct f m) := by
    let E : MvPolynomial (Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin m) ℚ :=
      MvPolynomial.aeval (fun i : Fin n ↦
        if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m) else 0)
    have hfactor (i : Fin n) :
        PowerSeries.map E.toRingHom (PowerSeries.mk fun d : ℕ ↦
          MvPolynomial.C (PowerSeries.coeff d f) * MvPolynomial.X i ^ d) =
        PowerSeries.mk (fun d : ℕ ↦
          MvPolynomial.C (PowerSeries.coeff d f) *
            (if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m) else 0) ^ d) := by
      ext d
      simp [E]
    have hproduct : PowerSeries.map E.toRingHom (rootProduct f n) = rootProduct f m := by
      simp only [rootProduct, map_prod, hfactor]
      symm
      apply Fintype.prod_of_injective (Fin.castLE hmn) (Fin.castLE_injective hmn)
      · intro i hi
        have hi' : ¬ i.val < m := by simpa only [Fin.range_castLE, Set.mem_ofPred_eq] using hi
        ext d
        by_cases hd : d = 0
        · subst d
          simp [hi', PowerSeries.coeff_zero_eq_constantCoeff, hf]
        · simp [hi', hd]
      · intro i
        ext d
        simp [i.isLt]
    exact (PowerSeries.coeff_map E.toRingHom j (rootProduct f n)).symm.trans
      (congrArg (PowerSeries.coeff j) hproduct)
  -- Adjoining zero leaves all elementary symmetric polynomials unchanged.
  have hesymm (m n : ℕ) (hmn : m ≤ n) (j : ℕ) :
      ρ m n (MvPolynomial.esymm (Fin n) ℚ j) = MvPolynomial.esymm (Fin m) ℚ j := by
    dsimp only [ρ]
    have hstep (r : ℕ) (g : Fin r → MvPolynomial (Fin m) ℚ) :
        MvPolynomial.aeval (Fin.lastCases 0 g) (MvPolynomial.esymm (Fin (r + 1)) ℚ j) =
          MvPolynomial.aeval g (MvPolynomial.esymm (Fin r) ℚ j) := by
      have hzero (s : Multiset (MvPolynomial (Fin m) ℚ)) (d : ℕ) :
          (0 ::ₘ s).esymm d = s.esymm d := by
        cases d with
        | zero => simp
        | succ d => simp [Multiset.esymm, Multiset.map_map]
      simp only [MvPolynomial.aeval_esymm_eq_multiset_esymm]
      rw [Fin.univ_castSuccEmb, Finset.cons_val, Multiset.map_cons, Finset.map_val,
        Multiset.map_map]
      simpa only [Fin.lastCases_last, Function.comp_def, Fin.castSuccEmb_apply,
        Fin.lastCases_castSucc] using hzero (Finset.univ.val.map g) j
    induction n, hmn using Nat.le_induction with
    | base =>
      have hvars : (fun i : Fin m ↦
          if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m)
          else (0 : MvPolynomial (Fin m) ℚ)) =
            (MvPolynomial.X : Fin m → MvPolynomial (Fin m) ℚ) := by
        funext i
        simp [i.isLt]
      rw [hvars]
      simp only [MvPolynomial.aeval_X_left, AlgHom.id_apply]
    | succ n hmn ih =>
      have hvars : (fun i : Fin (n + 1) ↦
          if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m)
          else (0 : MvPolynomial (Fin m) ℚ)) =
            Fin.lastCases 0 (fun i : Fin n ↦
              if h : i.val < m then MvPolynomial.X (⟨i.val, h⟩ : Fin m)
              else (0 : MvPolynomial (Fin m) ℚ)) := by
        funext i
        refine Fin.lastCases ?_ (fun i ↦ ?_) i
        · simp [Nat.not_lt.mpr hmn]
        · simp
      rw [hvars, hstep, ih]
  -- Elementary substitution commutes with removing surplus zero roots.
  have hcomp (m n t : ℕ) (hmn : m ≤ n) (p : MvPolynomial (Fin t) ℚ) :
      ρ m n (e n t p) = e m t p := by
    dsimp only [e]
    rw [MvPolynomial.comp_aeval_apply]
    simp only [hesymm m n hmn]
  have hbase (m : ℕ) : e m m (polynomial f m) =
      PowerSeries.coeff m (rootProduct f m) := by
    dsimp only [e]
    rw [← MvPolynomial.esymmAlgHom_apply]
    exact congrArg Subtype.val
      ((MvPolynomial.esymmAlgEquiv (Fin m) ℚ (Fintype.card_fin m)).apply_symm_apply
        ⟨PowerSeries.coeff m (rootProduct f m), isSymmetric_coeff_rootProduct f m m⟩)
  rcases le_total n k with hnk | hkn
  · -- With fewer than k roots, specialize the defining k-root identity directly.
    calc
      e n k (polynomial f k) = ρ n k (e k k (polynomial f k)) := (hcomp n k k hnk _).symm
      _ = PowerSeries.coeff k (rootProduct f n) := by rw [hbase]; exact hroot n k k hnk
  · -- With at least k roots, the weighted inverse uses only the first k variables.
    let q : MvPolynomial (Fin n) ℚ :=
      (MvPolynomial.esymmAlgEquiv (Fin n) ℚ (Fintype.card_fin n)).symm
        ⟨PowerSeries.coeff k (rootProduct f n), isSymmetric_coeff_rootProduct f n k⟩
    have hq : e n n q = PowerSeries.coeff k (rootProduct f n) := by
      dsimp only [e]
      rw [← MvPolynomial.esymmAlgHom_apply]
      exact congrArg Subtype.val
        ((MvPolynomial.esymmAlgEquiv (Fin n) ℚ (Fintype.card_fin n)).apply_symm_apply
          ⟨PowerSeries.coeff k (rootProduct f n), isSymmetric_coeff_rootProduct f n k⟩)
    have hweight : q.IsWeightedHomogeneous (fun i : Fin n ↦ i.val + 1) k := by
      apply isWeightedHomogeneous_of_esymm n k
      change (e n n q).IsWeightedHomogeneous (fun _ ↦ (1 : ℕ)) k
      rw [hq]
      exact isWeightedHomogeneous_coeff_rootProduct f n k
    have hvars : (q.vars : Set (Fin n)) ⊆ Set.range (Fin.castLE hkn) := by
      intro i hi
      obtain ⟨d, hd, hi⟩ := (MvPolynomial.mem_vars_iff_mem_support _).mp hi
      have hdweight := hweight (MvPolynomial.mem_support_iff.mp hd)
      have hiweight := Finsupp.le_weight_of_ne_zero' (fun i : Fin n ↦ i.val + 1)
        (Finsupp.mem_support_iff.mp hi)
      rw [hdweight] at hiweight
      exact ⟨⟨i.val, hiweight⟩, rfl⟩
    obtain ⟨p, hp⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range q
      (Fin.castLE hkn) (Fin.castLE_injective hkn) hvars
    have hpimage : e n k p = PowerSeries.coeff k (rootProduct f n) := by
      calc
        e n k p = e n n (MvPolynomial.rename (Fin.castLE hkn) p) := by
          simp [e, MvPolynomial.aeval_rename, Function.comp_def]
        _ = PowerSeries.coeff k (rootProduct f n) := by rw [hp, hq]
    -- Specialization to k roots identifies that polynomial by algebraic independence.
    have hpbase : e k k p = e k k (polynomial f k) := by
      calc
        e k k p = ρ k n (e n k p) := (hcomp k n k hkn p).symm
        _ = PowerSeries.coeff k (rootProduct f k) := by
          rw [hpimage]
          exact hroot k n k hkn
        _ = e k k (polynomial f k) := (hbase k).symm
    have hpeq : p = polynomial f k := by
      apply MvPolynomial.esymmAlgHom_fin_injective ℚ (n := k) (m := k) le_rfl
      apply Subtype.ext
      simpa only [MvPolynomial.esymmAlgHom_apply] using hpbase
    rw [hpeq] at hpimage
    exact hpimage

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- Evaluate the actual universal polynomials on the positive coefficients of b. -/
def transform (f : PowerSeries ℚ) (b : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k : ℕ ↦
    MvPolynomial.aeval (fun i : Fin k ↦ PowerSeries.coeff ((i : ℕ) + 1) b)
      (polynomial f k)

/-- The transformed formal sum has constant coefficient one. -/
theorem constantCoeff_transform (f : PowerSeries ℚ) (b : PowerSeries R) :
    (transform f b).constantCoeff = 1 := by
  /- The degree-zero root product is the empty product, whose constant
  coefficient is one. The elementary-symmetric algebra equivalence and
  evaluation both preserve one. The input constant coefficient is not
  read by transform. -/
  -- With no root variables the root product is the multiplicative identity.
  have hzero : polynomial f 0 = 1 := by
    unfold polynomial
    have hroot : (⟨PowerSeries.coeff 0 (rootProduct f 0),
        isSymmetric_coeff_rootProduct f 0 0⟩ :
        MvPolynomial.symmetricSubalgebra (Fin 0) ℚ) = 1 := by
      apply Subtype.ext
      simp [rootProduct]
    rw [hroot, map_one]
  -- Both the inverse elementary-symmetric map and evaluation preserve one.
  simp [transform, hzero]

/-- The multiplicative sequence preserves the identity formal sum. -/
theorem transform_one (f : PowerSeries ℚ) : transform f (1 : PowerSeries R) = 1 := by
  /- The constant coefficient is the preceding normalization. For k>0,
  weighted homogeneity of positive weight forces the universal polynomial
  to vanish when all its variables are zero. These are exactly the positive
  coefficients of the original identity series. Compare all coefficients. -/
  ext k
  by_cases hk : k = 0
  · subst k
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff, map_one] using
      constantCoeff_transform f (1 : PowerSeries R)
  · -- A positive-weight homogeneous polynomial has no constant monomial.
    have hconstant : MvPolynomial.constantCoeff (polynomial f k) = 0 := by
      exact (polynomial_isWeightedHomogeneous f k).coeff_eq_zero 0 (by simpa using Ne.symm hk)
    -- All positive coefficients of the input unit are zero.
    simp [transform, PowerSeries.coeff_one, MvPolynomial.aeval_zero', hconstant, hk]

/-- The elementary root product has the elementary symmetric polynomials as coefficients. -/
private theorem coeff_rootProduct_one_add_X (n j : ℕ) :
    PowerSeries.coeff j (rootProduct (1 + PowerSeries.X) n) =
      MvPolynomial.esymm (Fin n) ℚ j := by
  classical
  -- Each root contributes a linear factor; choosing its nonconstant term records that root.
  have hfactor (i : Fin n) :
      (PowerSeries.mk fun k : ℕ ↦
        MvPolynomial.C (PowerSeries.coeff k (1 + (PowerSeries.X : PowerSeries ℚ))) *
          MvPolynomial.X i ^ k) =
        1 + PowerSeries.C (MvPolynomial.X i) * PowerSeries.X := by
    ext k
    simp only [PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, PowerSeries.coeff_X,
      PowerSeries.coeff_C_mul]
    by_cases hk0 : k = 0
    · subst k
      simp
    · by_cases hk1 : k = 1
      · subst k
        simp
      · simp [hk0, hk1]
  -- Expanding the product indexes its degree-j coefficient by subsets of cardinality j.
  have hprod (s : Finset (Fin n)) :
      (∏ i ∈ s, (PowerSeries.C (MvPolynomial.X i) * PowerSeries.X)) =
        PowerSeries.C (∏ i ∈ s, (MvPolynomial.X i : MvPolynomial (Fin n) ℚ)) *
          PowerSeries.X ^ s.card := by
    simp only [Finset.prod_mul_distrib, map_prod, Finset.prod_const]
  simp only [rootProduct, hfactor, Finset.prod_one_add, map_sum, hprod,
    PowerSeries.coeff_C_mul_X_pow, MvPolynomial.esymm, Finset.powersetCard_eq_filter,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  simp [eq_comm]

/-- The transformation is natural under homomorphisms of rational coefficient algebras. -/
private theorem map_transform {S T : Type*} [CommRing S] [Algebra ℚ S]
    [CommRing T] [Algebra ℚ T] (φ : S →ₐ[ℚ] T) (f : PowerSeries ℚ) (b : PowerSeries S) :
    PowerSeries.map φ.toRingHom (transform f b) =
      transform f (PowerSeries.map φ.toRingHom b) := by
  ext k
  simp only [transform, PowerSeries.coeff_map, PowerSeries.coeff_mk]
  exact MvPolynomial.comp_aeval_apply _ φ _

/-- SG Lemma 11.9: the constructed transformation preserves the actual Cauchy product. -/
theorem transform_mul (f : PowerSeries ℚ) (hf : f.constantCoeff = 1)
    (b c : PowerSeries R) (hb : b.constantCoeff = 1) (hc : c.constantCoeff = 1) :
    transform f (b * c) = transform f b * transform f c := by
  /- Stage 1: fix degree k and take two separate sets of k independent
  free roots. Their elementary products have coefficient sequences b'
  and c'. Concatenating these original root sets gives the coefficients
  of their actual Cauchy product. The arbitrary-root-count formula above
  identifies transform with the product of the same f(root) factors.
  Stage 2: split that finite product into its two original blocks. Its
  degree-k coefficient is the Cauchy coefficient of the two transformed
  elementary products. The two sets of elementary symmetric polynomials
  are algebraically independent, so this is an identity of universal
  polynomials in the two groups of coefficient variables.
  Stage 3: evaluate that polynomial identity in the given ordinary
  commutative rational algebra R at the first k coefficients of the
  actual b and c. The hypotheses hb and hc supply precisely their
  constant terms in the convolution. Degreewise equality gives the
  displayed series equality; there is no analytic convergence claim. -/
  classical
  -- Concatenating the two root blocks multiplies their actual formal series.
  have hsplit (f : PowerSeries ℚ) (n m : ℕ) :
      PowerSeries.map
          (MvPolynomial.rename (finSumFinEquiv.symm : Fin (n + m) → Fin n ⊕ Fin m)).toRingHom
          (rootProduct f (n + m)) =
        PowerSeries.map (MvPolynomial.rename (Sum.inl : Fin n → Fin n ⊕ Fin m)).toRingHom
            (rootProduct f n) *
          PowerSeries.map (MvPolynomial.rename (Sum.inr : Fin m → Fin n ⊕ Fin m)).toRingHom
            (rootProduct f m) := by
    classical
    have hmap {a : ℕ} (g : Fin a → Fin n ⊕ Fin m) (i : Fin a) :
        PowerSeries.map (MvPolynomial.rename g).toRingHom
            (PowerSeries.mk fun d : ℕ ↦
              MvPolynomial.C (PowerSeries.coeff d f) * MvPolynomial.X i ^ d) =
          PowerSeries.mk (fun d : ℕ ↦
            MvPolynomial.C (PowerSeries.coeff d f) * MvPolynomial.X (g i) ^ d) := by
      ext d
      simp
    simp only [rootProduct, map_prod, hmap]
    rw [← Equiv.prod_comp (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m))]
    simp only [Equiv.symm_apply_apply, Fintype.prod_sum_type]
  -- Separate algebraic independence in each coefficient block gives joint injectivity.
  have hinj (n : ℕ) :
      Function.Injective (MvPolynomial.aeval (R := ℚ) (Sum.elim
        (fun j : Fin n ↦ MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin n) ℚ (j.val + 1)))
        (fun j : Fin n ↦ MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm (Fin n) ℚ (j.val + 1))))) := by
    have hesymm (S : Type) [CommRing S] :
        Function.Injective
          (MvPolynomial.aeval (R := S)
            (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) S (i.val + 1))) := by
      intro p q h
      apply MvPolynomial.esymmAlgHom_fin_injective S (n := n) (m := n) le_rfl
      apply Subtype.ext
      simpa only [MvPolynomial.esymmAlgHom_apply] using h
    let B : Type := MvPolynomial (Fin n) ℚ
    let e : B →ₐ[ℚ] B :=
      MvPolynomial.aeval (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) ℚ (i.val + 1))
    let E : MvPolynomial (Fin n) B →ₐ[B] MvPolynomial (Fin n) B :=
      MvPolynomial.aeval (fun i : Fin n ↦ MvPolynomial.esymm (Fin n) B (i.val + 1))
    let s : MvPolynomial (Fin n ⊕ Fin n) ℚ ≃ₐ[ℚ] MvPolynomial (Fin n) B :=
      MvPolynomial.sumAlgEquiv ℚ (Fin n) (Fin n)
    let b : MvPolynomial (Fin n ⊕ Fin n) ℚ →ₐ[ℚ] MvPolynomial (Fin n ⊕ Fin n) ℚ :=
      MvPolynomial.aeval (Sum.elim
        (fun j : Fin n ↦ MvPolynomial.rename Sum.inl (MvPolynomial.esymm (Fin n) ℚ (j.val + 1)))
        (fun j : Fin n ↦ MvPolynomial.rename Sum.inr (MvPolynomial.esymm (Fin n) ℚ (j.val + 1))))
    have he : Function.Injective e := hesymm ℚ
    have hE : Function.Injective E := hesymm B
    have hconj : s.toAlgHom.comp b =
        (MvPolynomial.mapAlgHom e).comp ((E.restrictScalars ℚ).comp s.toAlgHom) := by
      apply MvPolynomial.algHom_ext
      intro i
      cases i with
      | inl j =>
        simp [b, s, e, E, B, MvPolynomial.esymm, map_sum, map_prod]
      | inr j =>
        simp [b, s, e, E, B, MvPolynomial.esymm, map_sum, map_prod]
    intro p q hpq
    apply s.injective
    apply hE
    apply MvPolynomial.map_injective e.toRingHom he
    have hpq' := congrArg s hpq
    exact (DFunLike.congr_fun hconj p).symm.trans
      (hpq'.trans (DFunLike.congr_fun hconj q))
  -- Prove the identity first for the universal normalized polynomials of degree k.
  have hU (k : ℕ) :
      let B : PowerSeries (MvPolynomial (Fin k ⊕ Fin k) ℚ) :=
        PowerSeries.mk fun j ↦ match j with
          | 0 => 1
          | j + 1 => if hj : j < k then MvPolynomial.X (Sum.inl ⟨j, hj⟩) else 0
      let C : PowerSeries (MvPolynomial (Fin k ⊕ Fin k) ℚ) :=
        PowerSeries.mk fun j ↦ match j with
          | 0 => 1
          | j + 1 => if hj : j < k then MvPolynomial.X (Sum.inr ⟨j, hj⟩) else 0
      transform f (B * C) = transform f B * transform f C := by
    let blockSeries (g : Fin k → Fin k ⊕ Fin k) :
        PowerSeries (MvPolynomial (Fin k ⊕ Fin k) ℚ) :=
      PowerSeries.mk fun j ↦ match j with
        | 0 => 1
        | j + 1 => if hj : j < k then MvPolynomial.X (g ⟨j, hj⟩) else 0
    change transform f (blockSeries Sum.inl * blockSeries Sum.inr) =
      transform f (blockSeries Sum.inl) * transform f (blockSeries Sum.inr)
    let E : MvPolynomial (Fin k ⊕ Fin k) ℚ →ₐ[ℚ] MvPolynomial (Fin k ⊕ Fin k) ℚ :=
      MvPolynomial.aeval (Sum.elim
        (fun i : Fin k ↦ MvPolynomial.rename Sum.inl
          (MvPolynomial.esymm (Fin k) ℚ (i.val + 1)))
        (fun i : Fin k ↦ MvPolynomial.rename Sum.inr
          (MvPolynomial.esymm (Fin k) ℚ (i.val + 1))))
    have hroot (n : ℕ) :
        transform f (rootProduct (1 + PowerSeries.X) n) = rootProduct f n := by
      apply PowerSeries.ext
      intro j
      simp only [transform, PowerSeries.coeff_mk, coeff_rootProduct_one_add_X]
      exact polynomial_esymm f hf n j
    have hblock (g : Fin k → Fin k ⊕ Fin k)
        (hg : ∀ i, E (MvPolynomial.X (g i)) =
          MvPolynomial.rename g (MvPolynomial.esymm (Fin k) ℚ (i.val + 1))) :
        PowerSeries.map E.toRingHom (blockSeries g) =
          PowerSeries.map (MvPolynomial.rename g).toRingHom
            (rootProduct (1 + PowerSeries.X) k) := by
      apply PowerSeries.ext
      intro j
      simp only [PowerSeries.coeff_map, blockSeries, PowerSeries.coeff_mk,
        coeff_rootProduct_one_add_X]
      cases j with
      | zero => simp
      | succ j =>
        by_cases hj : j < k
        · simp only [hj, dite_true]
          exact hg ⟨j, hj⟩
        · have hlarge : (Finset.univ : Finset (Fin k)).card < j + 1 := by
            simp only [Finset.card_univ, Fintype.card_fin]
            omega
          simp [hj, MvPolynomial.esymm, Finset.powersetCard_eq_empty.mpr hlarge]
    have hB := hblock Sum.inl (by intro i; simp [E])
    have hC := hblock Sum.inr (by intro i; simp [E])
    apply PowerSeries.map_injective E.toRingHom (hinj k)
    rw [map_transform, map_mul, hB, hC]
    rw [← hsplit]
    rw [← map_transform, hroot]
    rw [map_mul, map_transform, map_transform, hB, hC]
    rw [← map_transform, ← map_transform, hroot]
    exact hsplit f k k
  -- Evaluate the universal identity and compare only coefficients needed in degree k.
  ext k
  let B : PowerSeries (MvPolynomial (Fin k ⊕ Fin k) ℚ) :=
    PowerSeries.mk fun j ↦ match j with
      | 0 => 1
      | j + 1 => if hj : j < k then MvPolynomial.X (Sum.inl ⟨j, hj⟩) else 0
  let C : PowerSeries (MvPolynomial (Fin k ⊕ Fin k) ℚ) :=
    PowerSeries.mk fun j ↦ match j with
      | 0 => 1
      | j + 1 => if hj : j < k then MvPolynomial.X (Sum.inr ⟨j, hj⟩) else 0
  let φ : MvPolynomial (Fin k ⊕ Fin k) ℚ →ₐ[ℚ] R :=
    MvPolynomial.aeval (Sum.elim
      (fun i : Fin k ↦ PowerSeries.coeff (i.val + 1) b)
      (fun i : Fin k ↦ PowerSeries.coeff (i.val + 1) c))
  let B' : PowerSeries R := PowerSeries.map φ.toRingHom B
  let C' : PowerSeries R := PowerSeries.map φ.toRingHom C
  -- Evaluation recovers the given normalized input coefficients through degree k.
  have hB (j : ℕ) (hj : j ≤ k) : PowerSeries.coeff j B' = PowerSeries.coeff j b := by
    cases j with
    | zero => simp [B', B, PowerSeries.coeff_zero_eq_constantCoeff, hb]
    | succ j =>
      have hj' : j < k := hj
      simp [B', B, φ, hj']
  have hC (j : ℕ) (hj : j ≤ k) : PowerSeries.coeff j C' = PowerSeries.coeff j c := by
    cases j with
    | zero => simp [C', C, PowerSeries.coeff_zero_eq_constantCoeff, hc]
    | succ j =>
      have hj' : j < k := hj
      simp [C', C, φ, hj']
  have hproduct (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (B' * C') = PowerSeries.coeff j (b * c) := by
    rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hpj : p.1 + p.2 = j := Finset.mem_antidiagonal.mp hp
    rw [hB p.1 ((Nat.le_add_right _ _).trans (hpj.trans_le hj)),
      hC p.2 ((Nat.le_add_left _ _).trans (hpj.trans_le hj))]
  -- The degree-j output reads only the first j input coefficients.
  have hlocal (u v : PowerSeries R) (j : ℕ)
      (h : ∀ t : ℕ, t ≤ j → PowerSeries.coeff t u = PowerSeries.coeff t v) :
      PowerSeries.coeff j (transform f u) = PowerSeries.coeff j (transform f v) := by
    simp only [transform, PowerSeries.coeff_mk]
    apply congrArg (fun a : Fin j → R ↦ MvPolynomial.aeval a (polynomial f j))
    funext i
    exact h (i.val + 1) (Nat.succ_le_of_lt i.isLt)
  have htransB (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (transform f B') = PowerSeries.coeff j (transform f b) :=
    hlocal B' b j (fun t ht ↦ hB t (ht.trans hj))
  have htransC (j : ℕ) (hj : j ≤ k) :
      PowerSeries.coeff j (transform f C') = PowerSeries.coeff j (transform f c) :=
    hlocal C' c j (fun t ht ↦ hC t (ht.trans hj))
  have hU' : transform f (B * C) = transform f B * transform f C := hU k
  have hmapped : transform f (B' * C') = transform f B' * transform f C' := by
    have h := congrArg (PowerSeries.map φ.toRingHom) hU'
    simpa only [map_transform, map_mul] using h
  calc
    PowerSeries.coeff k (transform f (b * c)) =
        PowerSeries.coeff k (transform f (B' * C')) := (hlocal _ _ k hproduct).symm
    _ = PowerSeries.coeff k (transform f B' * transform f C') := by rw [hmapped]
    _ = PowerSeries.coeff k (transform f b * transform f c) := by
      rw [PowerSeries.coeff_mul, PowerSeries.coeff_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hpk : p.1 + p.2 = k := Finset.mem_antidiagonal.mp hp
      rw [htransB p.1 ((Nat.le_add_right _ _).trans hpk.le),
        htransC p.2 ((Nat.le_add_left _ _).trans hpk.le)]

/-- The original characteristic series is recovered on the one-root elementary product. -/
theorem transform_one_add_X (f : PowerSeries ℚ) (hf : f.constantCoeff = 1) :
    transform f (1 + PowerSeries.X) = f := by
  /- Apply the arbitrary-root-count coefficient identity with one root,
  then evaluate that root at one. The elementary coefficients are one
  in degree one and zero in higher degrees, exactly those of 1+X.
  The right-hand coefficients are the coefficients of the given f.
  The constant coefficient comparison uses hf. This recovers the source's
  defining series rather than an unspecified multiplicative operation. -/
  let e : MvPolynomial (Fin 1) ℚ →ₐ[ℚ] ℚ := MvPolynomial.aeval (fun _ ↦ (1 : ℚ))
  -- Evaluating the sole root at one recovers any characteristic series.
  have hroot (g : PowerSeries ℚ) :
      PowerSeries.map e.toRingHom (rootProduct g 1) = g := by
    ext k
    simp [rootProduct, e]
  -- The arbitrary-root formula identifies the transform of the elementary product.
  have htransform : transform f (rootProduct (1 + PowerSeries.X) 1) =
      rootProduct f 1 := by
    apply PowerSeries.ext
    intro k
    simp only [transform, PowerSeries.coeff_mk, coeff_rootProduct_one_add_X]
    exact polynomial_esymm f hf 1 k
  calc
    transform f (1 + PowerSeries.X) =
        transform f (PowerSeries.map e.toRingHom (rootProduct (1 + PowerSeries.X) 1)) := by
      rw [hroot]
    _ = PowerSeries.map e.toRingHom (transform f (rootProduct (1 + PowerSeries.X) 1)) :=
      (map_transform e f _).symm
    _ = PowerSeries.map e.toRingHom (rootProduct f 1) := by rw [htransform]
    _ = f := hroot f

/-- Weighted homogeneity preserves each original homogeneous coefficient submodule. -/
theorem coeff_transform_mem (𝒜 : ℕ → Submodule ℚ R) [GradedAlgebra 𝒜]
    (f : PowerSeries ℚ) (b : PowerSeries R)
    (hb : ∀ k : ℕ, PowerSeries.coeff k b ∈ 𝒜 k) (k : ℕ) :
    PowerSeries.coeff k (transform f b) ∈ 𝒜 k := by
  /- Expand the actual universal polynomial into its finitely many
  monomials. A variable of index i is replaced by the original coefficient
  b_(i+1), which lies in 𝒜 (i+1) by hb. Graded multiplication puts a
  monomial in the sum of these weighted degrees. The weighted-homogeneous
  theorem makes that sum k for every nonzero term. Rational scalar
  multiplication and finite addition preserve the original submodule
  𝒜 k. In degree zero the empty monomial is the original unit in 𝒜 0. -/
  classical
  -- Every nonzero monomial has total weight k before evaluation.
  rw [transform, PowerSeries.coeff_mk, (polynomial f k).as_sum, map_sum]
  apply Submodule.sum_mem
  intro d hd
  have hweight := polynomial_isWeightedHomogeneous f k (MvPolynomial.mem_support_iff.mp hd)
  -- Graded powers and products add exactly the weights of the substituted coefficients.
  have hmonomial :
      (d.prod fun i m ↦ PowerSeries.coeff (i.val + 1) b ^ m) ∈ 𝒜 k := by
    have hgraded := SetLike.prod_pow_mem_graded 𝒜 (F := d.support)
      (fun i : Fin k ↦ i.val + 1) (fun i : Fin k ↦ PowerSeries.coeff (i.val + 1) b) d
      (fun i _ ↦ hb (i.val + 1))
    have hdegree : (∑ i ∈ d.support, d i • (i.val + 1)) = k := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hweight
    simpa only [Finsupp.prod, hdegree] using hgraded
  -- Rational scalar multiplication and finite addition preserve the same submodule.
  rw [MvPolynomial.aeval_monomial, ← Algebra.smul_def]
  exact (𝒜 k).smul_mem _ hmonomial

end AtiyahSinger.MultiplicativeSequence
