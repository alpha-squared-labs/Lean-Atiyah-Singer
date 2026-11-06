/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.SpinTorus
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# The actual exterior spinor weight basis

Public module ID: M0070.

The standard coordinate basis of complex Euclidean m-space determines an ordered
exterior basis indexed by subsets of Fin m. Its even and odd subfamilies are bases
of the original exterior parity submodules, hence of the half-spin spaces under
the chirality identification already fixed in SpinorChirality.

For the ordered spin element built from cos(theta_j)+sin(theta_j)e_j(i e_j), an
occupied coordinate has eigenvalue exp(i theta_j) and an unoccupied coordinate
has eigenvalue exp(-i theta_j). These are the actual weights of the existing
complexSpinRepresentation, with its unchanged creation-minus-contraction action.
The same spin element rotates real vectors by twice the parameter angle. No
maximality theorem, quotient torus, or new representation carrier is introduced.

Sources: Lawson--Michelsohn, Spin Geometry, I.5 pp. 37--38 and I.6 pp. 43--44.
The interleaved real/imaginary orientation is retained. In rank zero the unique
empty exterior monomial is positive and has weight one; the odd basis is empty.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The standard ordered exterior basis of the original complex spinor space. -/
def complexSpinorBasis (m : ℕ) : Module.Basis (Finset (Fin m)) ℂ (ComplexSpinor m) :=
  (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra

/-- The spin weight of an exterior monomial for the specified half-angle parameters. -/
def spinorWeight (m : ℕ) (s : Finset (Fin m)) (theta : Fin m → ℝ) : ℂ :=
  Complex.exp (Complex.I * ∑ j : Fin m, if j ∈ s then (theta j : ℂ) else -(theta j : ℂ))

/-- The parity of a standard spinor monomial is exactly its subset cardinality modulo two. -/
theorem complexSpinorBasis_mem_evenOdd (m : ℕ) (s : Finset (Fin m)) (i : ZMod 2) :
    complexSpinorBasis m s ∈
        CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i ↔
      (s.card : ZMod 2) = i := by
  /- Stage 1: the standard exterior basis element is the ordered product of
  precisely the coordinate vectors indexed by s. Each factor has Clifford
  parity one, so this product lies in parity card(s) modulo two.
  Stage 2: the two exterior parity submodules form a direct sum. A basis vector
  is nonzero, hence cannot lie in both parity summands. This proves the reverse
  implication as well, including the empty monomial in even parity. -/
  classical
  -- The ordered exterior monomial has the degree of its number of vector factors.
  let b := complexSpinorBasis m
  let z : Fin m → ComplexSpinor m := fun j ↦
    CliffordAlgebra.ι (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m)))
      (EuclideanSpace.single j (1 : ℂ))
  have hprod (l : List (Fin m)) :
      (l.map z).prod ∈ CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) (l.length : ZMod 2) := by
    induction l with
    | nil =>
      change (1 : ComplexSpinor m) ∈ CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) 0
      exact SetLike.one_mem_graded _
    | cons j l ih =>
      simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add,
        Nat.cast_one, add_comm] using SetLike.mul_mem_graded
          (CliffordAlgebra.ι_mem_evenOdd_one _ (EuclideanSpace.single j (1 : ℂ))) ih
  let seq : List (Fin m) :=
    List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))
  have hb : b s = (seq.map z).prod := by
    change (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra s = _
    rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
    simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      Function.comp_def, seq, List.map_ofFn]
    congr 2
    funext j
    simp [z]
  have hdegree : b s ∈ CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) (s.card : ZMod 2) := by
    rw [hb]
    simpa only [seq, List.length_ofFn] using hprod seq
  -- Distinct homogeneous components intersect only at zero, and basis vectors are nonzero.
  constructor
  · intro h
    exact DirectSum.degree_eq_of_mem_mem _ hdegree h (b.ne_zero s)
  · intro h
    simpa only [h] using hdegree

/-- Monomials of the indicated parity span exactly the original parity submodule. -/
theorem complexSpinorBasis_parity_span (m : ℕ) (i : ZMod 2) :
    Submodule.span ℂ
        (Set.range (fun s : {s : Finset (Fin m) // (s.card : ZMod 2) = i} ↦
          complexSpinorBasis m s.val)) =
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i := by
  /- The parity membership criterion puts each selected basis monomial in
  the indicated submodule. For the reverse inclusion, project the full
  basis expansion onto that same homogeneous component. This projection
  fixes a vector of the submodule, fixes selected monomials, and kills
  monomials of the other parity. Its finite sum therefore belongs to
  the span of exactly the selected monomials. -/
  classical
  let b := complexSpinorBasis m
  let G := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m)))
  let S := Submodule.span ℂ
    (Set.range (fun s : {s : Finset (Fin m) // (s.card : ZMod 2) = i} ↦ b s.val))
  -- Each selected monomial belongs to the original parity summand.
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨s, rfl⟩
    exact (complexSpinorBasis_mem_evenOdd m s.val i).mpr s.property
  · intro x hx
    -- Project the full basis expansion onto this same homogeneous component.
    let P : ComplexSpinor m →ₗ[ℂ] ComplexSpinor m :=
      (G i).subtype ∘ₗ (DirectSum.component ℂ (ZMod 2) (fun j ↦ G j) i) ∘ₗ
        (DirectSum.decomposeLinearEquiv G).toLinearMap
    have hPx : P x = x := DirectSum.decompose_of_mem_same G hx
    have hPb (s : Finset (Fin m)) : P (b s) ∈ S := by
      have hs := (complexSpinorBasis_mem_evenOdd m s (s.card : ZMod 2)).mpr rfl
      by_cases h : (s.card : ZMod 2) = i
      · have hp : P (b s) = b s :=
          DirectSum.decompose_of_mem_same G
            ((complexSpinorBasis_mem_evenOdd m s i).mpr h)
        rw [hp]
        exact Submodule.subset_span ⟨⟨s, h⟩, rfl⟩
      · have hp : P (b s) = 0 := DirectSum.decompose_of_mem_ne G hs h
        rw [hp]
        exact S.zero_mem
    have hexpand := congrArg P (b.sum_repr x)
    rw [map_sum] at hexpand
    rw [← hPx, ← hexpand]
    apply S.sum_mem
    intro s _
    rw [map_smul]
    exact S.smul_mem _ (hPb s)

/-- The actual half-spin basis obtained by restricting the original exterior monomials. -/
def complexSpinorParityBasis (m : ℕ) (i : ZMod 2) :
    Module.Basis {s : Finset (Fin m) // (s.card : ZMod 2) = i} ℂ
      (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i) :=
  (Module.Basis.span
    ((complexSpinorBasis m).linearIndependent.comp
      (fun s : {s : Finset (Fin m) // (s.card : ZMod 2) = i} ↦ s.val)
      Subtype.val_injective)).map
    (LinearEquiv.ofEq _ _ (complexSpinorBasis_parity_span m i))

/-- SG I.6: the original complex spin action is diagonal in the actual exterior basis. -/
theorem complexSpinRepresentation_spinTorusElement_basis (m : ℕ) (theta : Fin m → ℝ)
    (s : Finset (Fin m)) :
    complexSpinRepresentation m (spinTorusElement m theta) (complexSpinorBasis m s) =
      spinorWeight m s theta • complexSpinorBasis m s := by
  /- Stage 1: realSpinorRepresentation_ι identifies each coordinate vector
  with its original wedge-minus-contraction operator. The ordered bivector
  e_j*(i*e_j) consequently acts as i*(2*N_j-1), where N_j is the occupation
  projection for coordinate j in the actual exterior basis.
  Stage 2: N_j has eigenvalue one when j belongs to s and zero otherwise.
  The j-th rotation factor therefore has eigenvalue cos(theta_j)+i*sin(theta_j)
  in the occupied case and cos(theta_j)-i*sin(theta_j) in the unoccupied case.
  Stage 3: multiply these eigenvalues in the specified order and use Euler's
  identity and the exponential sum law. This is precisely spinorWeight m s
  theta, on the same basis vector and the same original spin representation.
  In rank zero both the product and the empty-sum exponential are one. -/
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
  let b := complexSpinorBasis m
  let seq (s : Finset (Fin m)) : List (Fin m) :=
    List.ofFn (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.ofCard (s := s) rfl))
  have hseq (s : Finset (Fin m)) (i : Fin m) : i ∈ seq s ↔ i ∈ s := by
    exact (List.mem_ofFn' _ _).trans
      (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem _ _)
  have hb (s : Finset (Fin m)) : b s = mon (seq s) := by
    change (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra s = _
    rw [ExteriorAlgebra.basis_apply_ofCard _ (s := s) rfl]
    simp only [ExteriorAlgebra.ιMulti_family, ExteriorAlgebra.ιMulti_apply,
      Function.comp_def, mon, seq, List.map_ofFn]
    congr 2
    funext i
    simp [z, e]
  have hnb (i : Fin m) (s : Finset (Fin m)) :
      (w i * c i) (b s) = if i ∈ s then b s else 0 := by
    simp only [hb, hn, hseq]
  -- One ordered real/imaginary pair acts by i times the signed occupation operator.
  have hI (j : Fin m) :
      cliffordSymbol (EuclideanSpace.single j Complex.I) = Complex.I • (w j + c j) := by
    have hv : EuclideanSpace.single j Complex.I = Complex.I • e j := by
      ext k
      simp [e]
    rw [hv, cliffordSymbol]
    simp only [exteriorMultiplication, contraction, map_smul, map_smulₛₗ,
      Complex.conj_I, neg_smul, smul_add, w, c]
    simp only [map_neg, map_smul, sub_neg_eq_add]
  have hpair (j : Fin m) :
      realSpinorRepresentation m (spinPlaneBivector m j) =
        Complex.I • (w j * c j + w j * c j - 1) := by
    rw [spinPlaneBivector, map_mul, realSpinorRepresentation_ι,
      realSpinorRepresentation_ι, hI]
    change (w j - c j) * (Complex.I • (w j + c j)) = _
    rw [mul_smul_comm]
    congr 1
    have hww : w j * w j = 0 := by
      simpa only [pow_two] using exteriorMultiplication_sq (e j)
    have hcc : c j * c j = 0 := by
      simpa only [pow_two] using contraction_sq (e j)
    have hsum : w j * c j + c j * w j = 1 := by
      simpa [w, c, e] using exteriorMultiplication_contraction_add (e j)
    rw [sub_mul, mul_add, mul_add, hww, hcc, zero_add, add_zero]
    rw [eq_sub_of_add_eq hsum]
    abel
  let F (j : Fin m) : CliffordAlgebra (realSpinorQuadraticForm m) :=
    algebraMap ℝ _ (Real.cos (theta j)) + Real.sin (theta j) • spinPlaneBivector m j
  let a (j : Fin m) : ℂ :=
    Complex.I * (if j ∈ s then (theta j : ℂ) else -(theta j : ℂ))
  have hfactor (j : Fin m) :
      realSpinorRepresentation m (F j) (b s) = Complex.exp (a j) • b s := by
    simp only [F, map_add, map_smul, AlgHom.commutes, hpair, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hnb]
    -- Convert real scalar multiplication before collecting the complex eigenvalue.
    simp only [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply,
      Module.End.one_apply]
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    by_cases h : j ∈ s
    · simp only [h, ite_true, add_sub_cancel_right, a]
      rw [mul_comm Complex.I, Complex.exp_mul_I]
      simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin, smul_smul, ← add_smul]
      congr 1
    · simp only [h, ite_false, add_zero, zero_sub, a]
      rw [mul_comm Complex.I, Complex.exp_mul_I]
      simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos,
        ← Complex.ofReal_sin, smul_neg, smul_smul, ← neg_smul, ← add_smul]
      congr 1
      simp [mul_comm]
  -- Multiply the eigenvalues in the same order as the original Clifford product.
  have hprod (l : List (Fin m)) :
      realSpinorRepresentation m ((l.map F).prod) (b s) =
        Complex.exp ((l.map a).sum) • b s := by
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, map_mul,
        Module.End.mul_apply, ih, map_smul, hfactor, smul_smul, Complex.exp_add]
      rw [mul_comm]
  change realSpinorRepresentation m (spinTorusProduct m theta) (b s) = _
  have h := hprod (List.ofFn (fun j : Fin m ↦ j))
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def, b, a, F,
    spinTorusProduct, spinorWeight,
    ← Finset.mul_sum] using h

/-- The original half-spin action has the same weights on its actual parity basis. -/
theorem complexSpinParityRepresentation_spinTorusElement_basis (m : ℕ) (i : ZMod 2)
    (theta : Fin m → ℝ) (s : {s : Finset (Fin m) // (s.card : ZMod 2) = i}) :
    complexSpinParityRepresentation m i (spinTorusElement m theta)
        (complexSpinorParityBasis m i s) =
      spinorWeight m s.val theta • complexSpinorParityBasis m i s := by
  /- Stage 1: the actual half-spin representation is the restriction of the
  original full spin action to the original exterior parity submodule. Its
  basis vector coerces to exactly complexSpinorBasis m s.val, by the specified
  span-basis construction, without an independent choice of eigenvectors.
  Stage 2: apply the preceding full-spin weight formula and use subtype
  extensionality. The result is a diagonalization on a complete basis of the
  original half-spin space, which directly computes its trace. -/
  -- The restricted span basis has exactly the original exterior vectors as its values.
  apply Subtype.ext
  have hb : ∀ t : {s : Finset (Fin m) // (s.card : ZMod 2) = i},
      (complexSpinorParityBasis m i t : ComplexSpinor m) = complexSpinorBasis m t.val := by
    intro t
    simp [complexSpinorParityBasis]
  change complexSpinRepresentation m (spinTorusElement m theta)
      (complexSpinorParityBasis m i s : ComplexSpinor m) =
    spinorWeight m s.val theta • (complexSpinorParityBasis m i s : ComplexSpinor m)
  rw [hb]
  exact complexSpinRepresentation_spinTorusElement_basis m theta s.val

end AtiyahSinger
