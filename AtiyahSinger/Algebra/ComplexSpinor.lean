/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorSymbol
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The even-dimensional complex Clifford representation

Public module ID: M0010.

The E07 model is the actual exterior algebra of complex Euclidean m-space. Its
complex Clifford generators are the complex-linear extension of the real-linear
symbol already used by the Bott construction. In coordinates (x,y), the quadratic
form is -sum x_j^2-sum y_j^2 and the action is
sum x_j (wedge e_j-contract e_j)+i y_j (wedge e_j+contract e_j).

The representation is constructed using mathlib's Clifford algebra universal
property. Its isomorphism with the full endomorphism algebra gives the standard
irreducible complex Clifford module. This is irreducibility for the full Clifford
algebra, not for its even subalgebra or the spin group. No spin group or associated
bundle is introduced here.

Sources: Lawson--Michelsohn, Spin Geometry, I.5, especially pp. 34--38 and
equations (5.25)--(5.27). The real vector is embedded by its real and imaginary
coordinates; it is essential not to treat Hermitian contraction as complex-linear
in the contracted vector. The zero-dimensional model is included.
The specified Clifford relation, spinor dimension and real-symbol identification are proved below.
The specified representation is an algebra isomorphism, and its full Clifford action is irreducible.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped ComplexConjugate

/-- The standard complex spinor space in real dimension `2 * m`. -/
abbrev ComplexSpinor (m : ℕ) : Type := ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin m))

/-- The complex extension of the negative Euclidean quadratic form. -/
def complexSpinorQuadraticForm (m : ℕ) :
    QuadraticForm ℂ (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  -(∑ j : Fin m, (QuadraticMap.sq (R := ℂ) (A := ℂ)).comp
    ((EuclideanSpace.projₗ j).comp
      (LinearMap.fst ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin m))))) -
    ∑ j : Fin m, (QuadraticMap.sq (R := ℂ) (A := ℂ)).comp
      ((EuclideanSpace.projₗ j).comp
        (LinearMap.snd ℂ (EuclideanSpace ℂ (Fin m)) (EuclideanSpace ℂ (Fin m))))

/-- The complex-linear extension of wedge minus Hermitian contraction. -/
def complexSpinorGenerator (m : ℕ) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) →ₗ[ℂ]
      Module.End ℂ (ComplexSpinor m) :=
  ∑ j : Fin m,
    (((EuclideanSpace.projₗ j).comp (LinearMap.fst ℂ _ _)).smulRight
      (exteriorMultiplication (EuclideanSpace.single j (1 : ℂ)) -
        contraction (EuclideanSpace.single j (1 : ℂ))) +
      Complex.I • (((EuclideanSpace.projₗ j).comp (LinearMap.snd ℂ _ _)).smulRight
        (exteriorMultiplication (EuclideanSpace.single j (1 : ℂ)) +
          contraction (EuclideanSpace.single j (1 : ℂ)))))

/-- The defining Clifford relation for the specified complex-linear generators. -/
theorem complexSpinorGenerator_sq (m : ℕ)
    (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    complexSpinorGenerator m v * complexSpinorGenerator m v =
      algebraMap ℂ (Module.End ℂ (ComplexSpinor m)) (complexSpinorQuadraticForm m v) := by
  /- Stage 1: collect the specified coordinate generators into exterior
  multiplication by the vector u with coefficients x_j + i*y_j and
  contraction by the functional phi with coefficients -x_j + i*y_j.
  This is an equality of the original endomorphisms, not a new spinor model.
  Stage 2: evaluate phi on u using the original orthonormal coordinate
  vectors. The mixed scalar terms cancel and i^2 = -1, giving exactly
  the prescribed negative sum of coordinate squares.
  Stage 3: exterior multiplication and contraction each square to zero.
  The native contraction rule on u wedge s makes their two mixed terms
  sum to phi(u) times s. This proves the Clifford relation for the
  same original complex-linear generator, including dimension zero. -/
  let u : EuclideanSpace ℂ (Fin m) :=
    ∑ j : Fin m, (v.1 j + Complex.I * v.2 j) • EuclideanSpace.single j (1 : ℂ)
  let φ : Module.Dual ℂ (EuclideanSpace ℂ (Fin m)) :=
    ∑ j : Fin m, (-v.1 j + Complex.I * v.2 j) • innerₛₗ ℂ (EuclideanSpace.single j 1)
  have hgen : complexSpinorGenerator m v = exteriorMultiplication u +
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ _)) φ := by
    simp only [complexSpinorGenerator, LinearMap.sum_apply, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply]
    simp only [u, φ, exteriorMultiplication, map_sum, map_smul, Finset.sum_add_distrib]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [contraction, smul_sub, smul_add, add_smul, neg_smul, smul_smul]
    simp only [EuclideanSpace.projₗ, PiLp.projₗ, LinearMap.comp_apply,
      LinearMap.proj_apply, LinearEquiv.coe_coe, WithLp.coe_linearEquiv]
    module
  have hpair : φ u = complexSpinorQuadraticForm m v := by
    simp [φ, u, EuclideanSpace.inner_single_left, complexSpinorQuadraticForm,
      sub_eq_add_neg]
    ring_nf
    simp [Complex.I_sq, Finset.sum_add_distrib, Finset.sum_neg_distrib, sub_eq_add_neg]
  -- The arbitrary creation/contraction pair squares to its scalar pairing.
  rw [hgen]
  apply LinearMap.ext
  intro s
  change ExteriorAlgebra.ι ℂ u *
      (ExteriorAlgebra.ι ℂ u * s + CliffordAlgebra.contractLeft φ s) +
      CliffordAlgebra.contractLeft φ
        (ExteriorAlgebra.ι ℂ u * s + CliffordAlgebra.contractLeft φ s) =
    complexSpinorQuadraticForm m v • s
  rw [mul_add, map_add, CliffordAlgebra.contractLeft_ι_mul,
    CliffordAlgebra.contractLeft_contractLeft, ← mul_assoc, ExteriorAlgebra.ι_sq_zero]
  simp [hpair]

/-- The complex Clifford algebra acts on the specified exterior spinor space. -/
def complexSpinorRepresentation (m : ℕ) :
    CliffordAlgebra (complexSpinorQuadraticForm m) →ₐ[ℂ]
      Module.End ℂ (ComplexSpinor m) :=
  CliffordAlgebra.lift (complexSpinorQuadraticForm m)
    ⟨complexSpinorGenerator m, complexSpinorGenerator_sq m⟩

/-- The complex dimension of the standard exterior spinor module. -/
theorem finrank_complexSpinor (m : ℕ) :
    Module.finrank ℂ (ComplexSpinor m) = 2 ^ m := by
  /- Stage 1: ordered exterior monomials in the m coordinate vectors form a
  basis, indexed by subsets of Fin m. This basis is the actual exterior basis,
  rather than a separately chosen space of the same dimension.
  Stage 2: count its indices; there are 2^m subsets. The empty subset also
  accounts for the one-dimensional spinor module when m=0. -/
  -- Count the actual exterior basis indexed by finite subsets of the original coordinate basis.
  simpa using Module.finrank_eq_card_basis
    (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra

/-- The standard spinor representation identifies the full even-dimensional algebra. -/
theorem complexSpinorRepresentation_bijective (m : ℕ) :
    Function.Bijective (complexSpinorRepresentation m) := by
  /- Stage 1: linear combinations of the two Clifford generators for each
  coordinate recover creation and contraction separately. Products of their
  occupation projections isolate every exterior basis vector; creation and
  contraction then give every matrix unit. The representation is surjective.
  Stage 2: the ordered Clifford monomial basis has 2^(2m) elements, while the
  endomorphism space of the exterior basis has (2^m)^2 elements. Equal finite
  dimensions turn surjectivity into injectivity. For m=0 both algebras are ℂ
  and the same construction is the scalar action. -/
  classical
  -- Use the same orthonormal coordinate vectors as the original Clifford generators.
  let e (i : Fin m) : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single i (1 : ℂ)
  let w (i : Fin m) : Module.End ℂ (ComplexSpinor m) := exteriorMultiplication (e i)
  let c (i : Fin m) : Module.End ℂ (ComplexSpinor m) := contraction (e i)
  let z (i : Fin m) : ComplexSpinor m := ExteriorAlgebra.ι ℂ (e i)
  let mon (l : List (Fin m)) : ComplexSpinor m := (l.map z).prod
  -- The contraction rule and anticommutation determine occupation on every monomial.
  have hc (i j : Fin m) (x : ComplexSpinor m) :
      c i (z j * x) = (if i = j then x else 0) - z j * c i x := by
    change CliffordAlgebra.contractLeft (innerₛₗ ℂ (e i))
      (CliffordAlgebra.ι (0 : QuadraticForm ℂ _) (e j) * x) = _
    rw [CliffordAlgebra.contractLeft_ι_mul]
    congr 1
    change (inner ℂ (e i) (e j)) • x = _
    rw [EuclideanSpace.inner_single_left]
    by_cases hij : i = j
    · subst j
      simp [e]
    · simp [e, hij]
  have hz (i j : Fin m) : z i * z j = -(z j * z i) := by
    exact eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap (e i) (e j))
  have hcmon (i : Fin m) (l : List (Fin m)) (hi : i ∉ l) : c i (mon l) = 0 := by
    induction l with
    | nil => exact CliffordAlgebra.contractLeft_one _ _
    | cons j l ih =>
      have hij : i ≠ j := fun h ↦ hi (List.mem_cons.mpr (Or.inl h))
      change c i (z j * mon l) = 0
      rw [hc, ite_eq_right hij, ih (fun h ↦ hi (List.mem_cons_of_mem _ h))]
      simp
  have hn (i : Fin m) (l : List (Fin m)) :
      (w i * c i) (mon l) = if i ∈ l then mon l else 0 := by
    change z i * c i (mon l) = _
    induction l with
    | nil => simp [mon, c, contraction]
    | cons j l ih =>
      change z i * c i (z j * mon l) = _
      rw [hc, mul_sub]
      by_cases hij : i = j
      · subst j
        simp [mon, ← mul_assoc (z i) (z i), z]
      · rw [ite_eq_right hij, mul_zero, ← mul_assoc, hz, neg_mul, zero_sub, neg_neg,
          mul_assoc, ih]
        simp [mon, hij]
  -- Identify these monomials with mathlib’s actual ordered exterior basis.
  let b : Module.Basis (Finset (Fin m)) ℂ (ComplexSpinor m) :=
    (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  let seq (s : Finset (Fin m)) : List (Fin m) :=
    List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))
  have hseq (s : Finset (Fin m)) (i : Fin m) : i ∈ seq s ↔ i ∈ s := by
    exact (List.mem_ofFn' _ _).trans
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _)
  have hb (s : Finset (Fin m)) : b s = mon (seq s) := by
    rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
    simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      Function.comp_def, mon, seq, List.map_ofFn]
    congr 2
    funext i
    simp [z, e]
  have hnb (i : Fin m) (s : Finset (Fin m)) :
      (w i * c i) (b s) = if i ∈ s then b s else 0 := by
    simp only [hb, hn, hseq]
  -- Recover creation and contraction from the two original coordinate generators.
  let R : Subalgebra ℂ (Module.End ℂ (ComplexSpinor m)) := (complexSpinorRepresentation m).range
  have hgen₁ (i : Fin m) : w i - c i ∈ R := by
    refine ⟨CliffordAlgebra.ι _ (e i, 0), ?_⟩
    change complexSpinorRepresentation m (CliffordAlgebra.ι _ (e i, 0)) = _
    rw [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply]
    simp [complexSpinorGenerator, EuclideanSpace.projₗ, PiLp.projₗ, e, w, c,
      Finset.sum_ite_eq']
  have hgen₂ (i : Fin m) : Complex.I • (w i + c i) ∈ R := by
    refine ⟨CliffordAlgebra.ι _ (0, e i), ?_⟩
    change complexSpinorRepresentation m (CliffordAlgebra.ι _ (0, e i)) = _
    rw [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply]
    simp [complexSpinorGenerator, EuclideanSpace.projₗ, PiLp.projₗ, e, w, c,
      Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hw (i : Fin m) : w i ∈ R := by
    have h := R.toSubmodule.smul_mem (1 / 2 : ℂ)
      (R.sub_mem (hgen₁ i) (R.toSubmodule.smul_mem Complex.I (hgen₂ i)))
    have heq : (1 / 2 : ℂ) • ((w i - c i) - Complex.I • (Complex.I • (w i + c i))) =
        w i := by
      rw [smul_smul, Complex.I_mul_I, neg_one_smul]
      module
    rwa [heq] at h
  have hcR (i : Fin m) : c i ∈ R := by
    have h := R.sub_mem (hw i) (hgen₁ i)
    simpa using h
  -- Occupied and empty coordinate projections isolate a single exterior basis vector.
  let p (s : Finset (Fin m)) (i : Fin m) : Module.End ℂ (ComplexSpinor m) :=
    if i ∈ s then w i * c i else 1 - w i * c i
  let q (s : Finset (Fin m)) (l : List (Fin m)) : Module.End ℂ (ComplexSpinor m) :=
    (l.map (p s)).prod
  have hp (s t : Finset (Fin m)) (i : Fin m) :
      p s i (b t) = if (i ∈ s ↔ i ∈ t) then b t else 0 := by
    by_cases hs : i ∈ s
    · by_cases ht : i ∈ t
      · simp [p, hs, ht, hnb]
      · simp [p, hs, ht, hnb]
    · by_cases ht : i ∈ t
      · simp [p, hs, ht, LinearMap.sub_apply, hnb]
      · simp [p, hs, ht, LinearMap.sub_apply, hnb]
  have hq (s t : Finset (Fin m)) (l : List (Fin m)) :
      q s l (b t) = if (∀ i ∈ l, i ∈ s ↔ i ∈ t) then b t else 0 := by
    induction l with
    | nil => simp [q]
    | cons i l ih =>
      change p s i (q s l (b t)) = _
      rw [ih]
      by_cases h : ∀ j ∈ l, j ∈ s ↔ j ∈ t
      · rw [ite_eq_left h, hp]
        simp only [List.forall_mem_cons, and_iff_left h]
      · rw [ite_eq_right h, map_zero]
        simp only [List.forall_mem_cons, h, and_false, ite_false]
  have hqR (s : Finset (Fin m)) (l : List (Fin m)) : q s l ∈ R := by
    induction l with
    | nil => exact R.one_mem
    | cons i l ih =>
      apply R.mul_mem _ ih
      dsimp [p]
      split_ifs
      · exact R.mul_mem (hw i) (hcR i)
      · exact R.sub_mem R.one_mem (R.mul_mem (hw i) (hcR i))
  let P (s : Finset (Fin m)) : Module.End ℂ (ComplexSpinor m) :=
    q s (List.ofFn (fun i : Fin m ↦ i))
  have hP (s t : Finset (Fin m)) : P s (b t) = if s = t then b t else 0 := by
    simp only [P, hq, List.mem_ofFn, exists_eq, forall_const]
    have heq : (∀ i, i ∈ s ↔ i ∈ t) ↔ s = t := Finset.ext_iff.symm
    simp only [heq]
  -- Involutive creation-plus-contraction products carry the vacuum to each basis vector.
  -- Their reversed products give inverses without a separate choice of permutation signs.
  let J (i : Fin m) : Module.End ℂ (ComplexSpinor m) := w i + c i
  let U (l : List (Fin m)) : Module.End ℂ (ComplexSpinor m) := (l.map J).prod
  have hJJ (i : Fin m) : J i * J i = 1 := by
    apply LinearMap.ext
    intro x
    change z i * (z i * x + c i x) + c i (z i * x + c i x) = x
    rw [mul_add, map_add, hc, ite_eq_left rfl]
    have hcc : c i (c i x) = 0 := CliffordAlgebra.contractLeft_contractLeft _ _
    rw [hcc, ← mul_assoc]
    have hzz : z i * z i = 0 := ExteriorAlgebra.ι_sq_zero (e i)
    rw [hzz]
    simp
  have hUR (l : List (Fin m)) : U l ∈ R := by
    induction l with
    | nil => exact R.one_mem
    | cons i l ih => exact R.mul_mem (R.add_mem (hw i) (hcR i)) ih
  have hUinv (l : List (Fin m)) : U l.reverse * U l = 1 := by
    induction l with
    | nil => simp [U]
    | cons i l ih =>
      simp only [U, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.prod_append, List.prod_cons, List.prod_nil, mul_one] at ⊢
      rw [mul_assoc, ← mul_assoc (J i) (J i), hJJ, one_mul]
      exact ih
  have hUvac (l : List (Fin m)) (hl : l.Nodup) : U l 1 = mon l := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      have hi : i ∉ l := (List.nodup_cons.mp hl).1
      change (w i + c i) (U l 1) = z i * mon l
      rw [ih (List.nodup_cons.mp hl).2, LinearMap.add_apply, hcmon i l hi, add_zero]
      rfl
  have hseqnodup (s : Finset (Fin m)) : (seq s).Nodup :=
    List.nodup_ofFn.mpr (Set.powersetCard.ofFinEmbEquiv.symm _).injective
  have hUb (s : Finset (Fin m)) : U (seq s) 1 = b s := by
    rw [hUvac _ (hseqnodup s), hb]
  have hUback (s : Finset (Fin m)) : U (seq s).reverse (b s) = 1 := by
    rw [← hUb]
    change (U (seq s).reverse * U (seq s)) 1 = 1
    rw [hUinv]
    rfl
  -- Compose the selected projection with these products to obtain every matrix unit.
  let E (s t : Finset (Fin m)) : Module.End ℂ (ComplexSpinor m) :=
    U (seq s) * U (seq t).reverse * P t
  have hE (s t a : Finset (Fin m)) : E s t (b a) = if t = a then b s else 0 := by
    change U (seq s) (U (seq t).reverse (P t (b a))) = _
    rw [hP]
    by_cases h : t = a
    · subst a
      rw [ite_eq_left rfl, hUback, hUb, ite_eq_left rfl]
    · simp [h]
  have hER (s t : Finset (Fin m)) : E s t ∈ R :=
    R.mul_mem (R.mul_mem (hUR _) (hUR _)) (hqR _ _)
  -- Matrix units span all endomorphisms, inside the image of the specified representation.
  have hsurj : Function.Surjective (complexSpinorRepresentation m) := by
    intro f
    have hf : f = ∑ t : Finset (Fin m), ∑ s : Finset (Fin m),
        (b.repr (f (b t)) s) • E s t := by
      apply b.ext
      intro a
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, hE]
      simp only [smul_ite, smul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, b.sum_repr]
    change f ∈ R
    rw [hf]
    apply R.sum_mem
    intro t _
    apply R.sum_mem
    intro s _
    exact R.toSubmodule.smul_mem _ (hER s t)
  -- Compare the actual Clifford and endomorphism dimensions to obtain injectivity.
  let : Invertible (2 : ℂ) := invertibleOfNonzero (two_ne_zero : (2 : ℂ) ≠ 0)
  let : FiniteDimensional ℂ (ComplexSpinor m) :=
    Module.Finite.of_basis b
  let bExterior := (((EuclideanSpace.basisFun (Fin m) ℂ).toBasis.prod
    (EuclideanSpace.basisFun (Fin m) ℂ).toBasis).reindex finSumFinEquiv).ExteriorAlgebra
  let bCl := bExterior.map (CliffordAlgebra.equivExterior (complexSpinorQuadraticForm m)).symm
  let : FiniteDimensional ℂ (CliffordAlgebra (complexSpinorQuadraticForm m)) :=
    Module.Finite.of_basis bCl
  have hsource : Module.finrank ℂ (CliffordAlgebra (complexSpinorQuadraticForm m)) =
      2 ^ (m + m) := by
    simpa using Module.finrank_eq_card_basis bCl
  have hdim : Module.finrank ℂ (CliffordAlgebra (complexSpinorQuadraticForm m)) =
      Module.finrank ℂ (Module.End ℂ (ComplexSpinor m)) := by
    rw [hsource, Module.finrank_linearMap, finrank_complexSpinor, pow_add]
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (complexSpinorRepresentation m).toLinearMap) hdim).mpr hsurj, hsurj⟩

/-- The algebra isomorphism whose forward map is the specified spinor representation. -/
def complexSpinorEquiv (m : ℕ) :
    CliffordAlgebra (complexSpinorQuadraticForm m) ≃ₐ[ℂ]
      Module.End ℂ (ComplexSpinor m) :=
  AlgEquiv.ofBijective (complexSpinorRepresentation m)
    (complexSpinorRepresentation_bijective m)

/-- The full complex Clifford action has no proper nonzero invariant complex subspace. -/
theorem complexSpinor_irreducible (m : ℕ) (W : Submodule ℂ (ComplexSpinor m))
    (hW : ∀ a : CliffordAlgebra (complexSpinorQuadraticForm m),
      ∀ s : ComplexSpinor m, s ∈ W → complexSpinorRepresentation m a s ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  /- Stage 1: surjectivity of the specified representation implies that W is
  invariant under every complex-linear endomorphism of the exterior space.
  Stage 2: if W contains a nonzero vector, choose a linear functional taking
  value 1 on it. The rank-one endomorphism obtained by multiplying that
  functional by any desired vector shows that every vector belongs to W.
  Otherwise W is zero. This argument concerns the full Clifford algebra;
  it makes no irreducibility claim about its even part. -/
  classical
  -- A nonzero invariant subspace contains a vector detected by a dual functional.
  by_cases hzero : W = ⊥
  · exact Or.inl hzero
  · right
    obtain ⟨s, hs, hsne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hzero
    obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one ℂ hsne
    -- Every rank-one endomorphism is realized by this same full Clifford action.
    apply Submodule.eq_top_iff'.mpr
    intro t
    obtain ⟨a, ha⟩ := (complexSpinorRepresentation_bijective m).surjective (φ.smulRight t)
    have ht := hW a s hs
    rw [ha, LinearMap.smulRight_apply, hφ, one_smul] at ht
    exact ht

/-- Real and imaginary coordinates embed the underlying real space in its complexification. -/
def complexSpinorRealEmbedding (m : ℕ) :
    EuclideanSpace ℂ (Fin m) →ₗ[ℝ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  let re : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm.toLinearMap.comp
      (LinearMap.pi fun j ↦ Complex.ofRealAm.toLinearMap.comp
        (Complex.reLm.comp ((EuclideanSpace.projₗ j).restrictScalars ℝ)))
  let im : EuclideanSpace ℂ (Fin m) →ₗ[ℝ] EuclideanSpace ℂ (Fin m) :=
    (WithLp.linearEquiv 2 ℝ (Fin m → ℂ)).symm.toLinearMap.comp
      (LinearMap.pi fun j ↦ Complex.ofRealAm.toLinearMap.comp
        (Complex.imLm.comp ((EuclideanSpace.projₗ j).restrictScalars ℝ)))
  re.prod im

/-- The real embedding preserves the negative Euclidean quadratic form. -/
theorem complexSpinorQuadraticForm_real (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    complexSpinorQuadraticForm m (complexSpinorRealEmbedding m v) = -(‖v‖ ^ 2 : ℂ) := by
  /- Stage 1: evaluate the coordinate quadratic form on the real and imaginary
  parts of each coordinate. The two contributions are -Re(v_j)^2-Im(v_j)^2.
  Stage 2: identify their sum with the negative sum of the complex coordinate
  norm squares. The Euclidean norm formula gives -‖v‖², embedded in ℂ. This
  compatibility uses a real-linear embedding, not a complex-linear one. -/
  -- Evaluate the same real/imaginary embedding in the specified coordinate quadratic form.
  simp only [complexSpinorQuadraticForm, complexSpinorRealEmbedding,
    sub_apply, neg_apply, sum_apply, QuadraticMap.comp_apply, QuadraticMap.sq_apply]
  change -(∑ j : Fin m, ((v j).re : ℂ) * ((v j).re : ℂ)) -
      ∑ j : Fin m, ((v j).im : ℂ) * ((v j).im : ℂ) = -(‖v‖ ^ 2 : ℂ)
  -- Each coordinate contributes its real square plus its imaginary square.
  rw [← Complex.ofReal_pow, EuclideanSpace.norm_sq_eq]
  simp only [Complex.sq_norm, Complex.normSq_apply]
  push_cast
  simp only [Finset.sum_add_distrib]
  ring

/-- On the underlying real space this representation is exactly the existing Bott symbol. -/
theorem complexSpinorRepresentation_real (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) :
    complexSpinorRepresentation m
        (CliffordAlgebra.ι (complexSpinorQuadraticForm m)
          (complexSpinorRealEmbedding m v)) = cliffordSymbol v := by
  /- Stage 1: the Clifford lift evaluates on a generating vector as the
  specified complexSpinorGenerator. Write each coordinate of v as x_j+i y_j
  with real x_j and y_j and expand the finite sum.
  Stage 2: exterior multiplication is complex-linear in v, whereas Hermitian
  contraction is conjugate-linear in v. Thus the coefficient of creation is
  x_j+i y_j and the coefficient of contraction is -x_j+i y_j. These are exactly
  the two terms in wedge(v)-contraction(v), with no independent symbol choice. -/
  -- Evaluate the universal lift at this very real vector.
  rw [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply]
  have hv : (∑ j : Fin m, (v j) • EuclideanSpace.single j (1 : ℂ)) = v := by
    ext j
    simp [Pi.single_apply]
  have hw : exteriorMultiplication v =
      ∑ j : Fin m, (v j) • exteriorMultiplication (EuclideanSpace.single j (1 : ℂ)) := by
    conv_lhs => rw [← hv]
    simp only [exteriorMultiplication, map_sum, map_smul]
  have hc : contraction v =
      ∑ j : Fin m, conj (v j) • contraction (EuclideanSpace.single j (1 : ℂ)) := by
    conv_lhs => rw [← hv]
    simp only [contraction, map_sum, map_smulₛₗ]
    rfl
  -- Creation is complex linear, while contraction conjugates the same coordinate coefficients.
  rw [cliffordSymbol, hw, hc, ← Finset.sum_sub_distrib]
  simp only [complexSpinorGenerator, LinearMap.sum_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  apply Finset.sum_congr rfl
  intro j _
  change ((v j).re : ℂ) •
      (exteriorMultiplication (EuclideanSpace.single j 1) -
        contraction (EuclideanSpace.single j 1)) +
    Complex.I • ((v j).im : ℂ) •
      (exteriorMultiplication (EuclideanSpace.single j 1) +
        contraction (EuclideanSpace.single j 1)) =
    v j • exteriorMultiplication (EuclideanSpace.single j 1) -
      conj (v j) • contraction (EuclideanSpace.single j 1)
  conv_rhs => rw [← Complex.re_add_im (v j)]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  module

end AtiyahSinger
