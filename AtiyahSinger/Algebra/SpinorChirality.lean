/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ComplexSpinor
public import AtiyahSinger.Algebra.ExteriorParity
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.Eigenspace.Basic

import Mathlib.Tactic.Module

/-!
# The normalized complex volume and its actual half-spin spaces

Public module ID: M0064.

E07, Spin Geometry I.5, especially pp.34--38. The ordered real orthonormal
basis is interleaved: e1, i*e1, e2, i*e2, and so on. For the negative-square
Clifford convention the complex volume is i^m times that ordered product.
Its action on the original exterior spinor module is the exterior grading
involution. Thus the positive and negative half-spin spaces are literally
the existing even and odd exterior subspaces, not independently chosen
isomorphic spaces.

Putting all real-coordinate vectors before all imaginary-coordinate vectors
changes the volume by (-1)^(m*(m-1)/2). We retain the interleaved complex
orientation throughout. No identification of these local representation
spaces with the associated bundles of a general spin manifold is asserted.
The zero-dimensional spinor is entirely positive; equal half-dimensions
are asserted only in positive even real dimension.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- SG's normalized complex volume for the interleaved real and imaginary basis. -/
def complexSpinorVolume (m : ℕ) : CliffordAlgebra (complexSpinorQuadraticForm m) :=
  (Complex.I ^ m) •
    (List.ofFn (fun j : Fin m ↦
      CliffordAlgebra.ι (complexSpinorQuadraticForm m)
          (EuclideanSpace.single j (1 : ℂ), 0) *
        CliffordAlgebra.ι (complexSpinorQuadraticForm m)
          (0, EuclideanSpace.single j (1 : ℂ)))).prod

/-- The chirality operator is the action of the specified normalized volume. -/
def complexSpinorChirality (m : ℕ) : Module.End ℂ (ComplexSpinor m) :=
  complexSpinorRepresentation m (complexSpinorVolume m)

/-- The two half-spin spaces are the actual positive and negative chirality eigenspaces. -/
def complexHalfSpinor (m : ℕ) (i : ZMod 2) : Submodule ℂ (ComplexSpinor m) :=
  (complexSpinorChirality m).eigenspace ((-1 : ℂ) ^ i.val)

/-- The normalized volume acts by the original exterior-algebra grading involution. -/
theorem complexSpinorChirality_eq_involute (m : ℕ) :
    complexSpinorChirality m =
      (CliffordAlgebra.involute
        (Q := (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))))).toLinearMap := by
  /- Stage 1: apply the specified Clifford representation to the ordered
  product. For each coordinate, its two real generators act as epsilon-iota
  and i*(epsilon+iota). Their product is i*(2*N_j-1), where N_j is the
  occupation projection for that exterior coordinate.
  Stage 2: the leading i^m turns the product into the commuting product of
  1-2*N_j. On the actual ordered wedge basis this is multiplication by
  (-1)^degree. No permutation to a different real basis is made.
  Stage 3: the original exterior involution has exactly this action on the
  same wedge basis. Linear extension identifies the two endomorphisms.
  For m=0 the empty product and the grading involution both act as identity. -/
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
  -- Compute each original interleaved real/imaginary generator pair before taking products.
  let A (i : Fin m) : Module.End ℂ (ComplexSpinor m) :=
    complexSpinorRepresentation m
      (CliffordAlgebra.ι _ (e i, 0) * CliffordAlgebra.ι _ (0, e i))
  have hgen₁ (i : Fin m) :
      complexSpinorRepresentation m (CliffordAlgebra.ι _ (e i, 0)) = w i - c i := by
    rw [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply]
    simp [complexSpinorGenerator, EuclideanSpace.projₗ, PiLp.projₗ, e, w, c,
      Finset.sum_ite_eq']
  have hgen₂ (i : Fin m) :
      complexSpinorRepresentation m (CliffordAlgebra.ι _ (0, e i)) =
        Complex.I • (w i + c i) := by
    rw [complexSpinorRepresentation, CliffordAlgebra.lift_ι_apply]
    simp [complexSpinorGenerator, EuclideanSpace.projₗ, PiLp.projₗ, e, w, c,
      Finset.sum_add_distrib, Finset.sum_ite_eq']
  have hpair (i : Fin m) :
      Complex.I • A i = 1 - (2 : ℂ) • (w i * c i) := by
    have hww : w i * w i = 0 := by
      simpa only [pow_two] using exteriorMultiplication_sq (e i)
    have hcc : c i * c i = 0 := by
      simpa only [pow_two] using contraction_sq (e i)
    have hcw : w i * c i + c i * w i = 1 := by
      simpa [e] using exteriorMultiplication_contraction_add (e i)
    dsimp only [A]
    rw [map_mul, hgen₁, hgen₂, mul_smul_comm, smul_smul, Complex.I_mul_I,
      neg_one_smul, sub_mul, mul_add, mul_add, hww, hcc, zero_add, add_zero]
    calc
      -(w i * c i - c i * w i) =
          (w i * c i + c i * w i) - (2 : ℂ) • (w i * c i) := by module
      _ = 1 - (2 : ℂ) • (w i * c i) := by rw [hcw]
  have hpairb (i : Fin m) (s : Finset (Fin m)) :
      (Complex.I • A i) (b s) = (if i ∈ s then (-1 : ℂ) else 1) • b s := by
    rw [hpair]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, hnb]
    by_cases hi : i ∈ s
    · simp only [hi, ite_true]
      module
    · simp [hi]
  -- Multiplying in the specified order gives one minus sign for each occupied coordinate.
  have hprod (s : Finset (Fin m)) (l : List (Fin m)) :
      (l.map (fun i ↦ Complex.I • A i)).prod (b s) =
        (l.map (fun i ↦ if i ∈ s then (-1 : ℂ) else 1)).prod • b s := by
    induction l with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih,
        map_smul, hpairb, mul_smul]
      module
  have hvolume : complexSpinorChirality m =
      (List.ofFn (fun i : Fin m ↦ Complex.I • A i)).prod := by
    simp only [complexSpinorChirality, complexSpinorVolume, map_smul, map_list_prod,
      List.map_ofFn]
    change Complex.I ^ m • (List.ofFn A).prod = _
    simpa only [List.length_ofFn, List.map_ofFn, Function.comp_def]
      using List.smul_prod (List.ofFn A) Complex.I
  have haction (s : Finset (Fin m)) :
      complexSpinorChirality m (b s) = (-1 : ℂ) ^ s.card • b s := by
    rw [hvolume]
    simpa only [List.map_ofFn, Function.comp_def, List.prod_ofFn,
      Finset.prod_ite_mem_eq, Finset.prod_const]
      using hprod s (List.ofFn (fun i : Fin m ↦ i))
  -- The native grade involution has the identical sign on those same exterior monomials.
  have hinvmon (l : List (Fin m)) :
      CliffordAlgebra.involute (mon l) = (-1 : ℂ) ^ l.length • mon l := by
    induction l with
    | nil => simp [mon]
    | cons i l ih =>
      change CliffordAlgebra.involute (z i * mon l) = _
      rw [map_mul, CliffordAlgebra.involute_ι, ih]
      simp [mon, z, pow_succ]
  apply b.ext
  intro s
  rw [haction]
  change (-1 : ℂ) ^ s.card • b s = CliffordAlgebra.involute (b s)
  rw [hb, hinvmon]
  simp only [seq, List.length_ofFn]

/-- SG's two chirality eigenspaces are exactly the original exterior parity submodules. -/
theorem complexHalfSpinor_eq_evenOdd (m : ℕ) (i : ZMod 2) :
    complexHalfSpinor m i =
      CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m))) i := by
  /- Stage 1: replace the chirality action by the preceding exterior
  involution identity. The original even/odd direct sum has eigenvalues
  +1 and -1, respectively, by the involution action on wedge monomials.
  Stage 2: decompose any eigenspace vector using that same direct sum.
  Since 2 is nonzero in C, the component with the opposite eigenvalue
  vanishes. The reverse inclusion follows from the action on each parity.
  This proves equality of submodules, not just equality of their dimensions. -/
  classical
  let Q : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m)) := 0
  have hcompl := CliffordAlgebra.evenOdd_isCompl Q
  ext x
  rw [complexHalfSpinor, complexSpinorChirality_eq_involute,
    Module.End.mem_eigenspace_iff]
  -- Split into the original complementary parity submodules before comparing eigenvalues.
  have hsplit : x ∈ CliffordAlgebra.evenOdd Q 0 ⊔ CliffordAlgebra.evenOdd Q 1 := by
    rw [hcompl.codisjoint.eq_top]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsplit
  have haInv := CliffordAlgebra.involute_eq_of_mem_even ha
  have hbInv := CliffordAlgebra.involute_eq_of_mem_odd hb
  -- Characteristic zero makes the opposite-eigenvalue component vanish.
  have htwo (a : ComplexSpinor m) (h : -a = a) : a = 0 := by
    have hs : (2 : ℂ) • a = 0 := by
      calc
        (2 : ℂ) • a = a + a := two_smul _ _
        _ = a + -a := congrArg (a + ·) h.symm
        _ = 0 := add_neg_cancel _
    exact (smul_eq_zero.mp hs).resolve_left (by norm_num)
  fin_cases i
  · change (CliffordAlgebra.involute (Q := Q) x = (-1 : ℂ) ^ (0 : ZMod 2).val • x) ↔
      x ∈ CliffordAlgebra.evenOdd Q 0
    simp only [ZMod.val_zero, pow_zero, one_smul]
    constructor
    · intro hx
      change CliffordAlgebra.involute x = x at hx
      have hEq : a - b = a + b := by
        simpa only [← hab, map_add, haInv, hbInv, sub_eq_add_neg] using hx
      have hbzero : b = 0 := by
        have hneg : -b = b := add_left_cancel (by
          simpa only [sub_eq_add_neg] using hEq)
        exact htwo b hneg
      simpa [← hab, hbzero, Q] using ha
    · intro hx
      exact CliffordAlgebra.involute_eq_of_mem_even hx
  · change (CliffordAlgebra.involute (Q := Q) x = (-1 : ℂ) ^ (1 : ZMod 2).val • x) ↔
      x ∈ CliffordAlgebra.evenOdd Q 1
    simp only [ZMod.val_one, pow_one, neg_one_smul]
    constructor
    · intro hx
      change CliffordAlgebra.involute x = -x at hx
      have hEq : a - b = -(a + b) := by
        simpa only [← hab, map_add, haInv, hbInv, sub_eq_add_neg] using hx
      have hazero : a = 0 := by
        have hneg : a = -a := by
          apply add_right_cancel (b := -b)
          simpa only [sub_eq_add_neg, neg_add] using hEq
        exact htwo a hneg.symm
      simpa [← hab, hazero, Q] using hb
    · intro hx
      exact CliffordAlgebra.involute_eq_of_mem_odd hx

/-- In positive even real dimension, each actual half-spin space has dimension 2^(m-1). -/
theorem finrank_complexHalfSpinor (m : ℕ) (hm : 0 < m) (i : ZMod 2) :
    Module.finrank ℂ (complexHalfSpinor m i) = 2 ^ (m - 1) := by
  /- Stage 1: identify the actual eigenspace with its exterior parity
  submodule by complexHalfSpinor_eq_evenOdd. The standard wedge basis is
  indexed by subsets of Fin m, with parity given by subset cardinality.
  Stage 2: choose one nonzero coordinate using hm. The existing invertible
  Clifford symbol exchanges the actual even and odd subspaces, so their
  dimensions agree. Their direct sum has dimension 2^m, giving 2^(m-1).
  The positivity premise excludes m=0, where the positive
  space has dimension one and the negative space has dimension zero. -/
  classical
  let Q : QuadraticForm ℂ (EuclideanSpace ℂ (Fin m)) := 0
  let : FiniteDimensional ℂ (ComplexSpinor m) :=
    Module.Finite.of_basis (EuclideanSpace.basisFun (Fin m) ℂ).toBasis.ExteriorAlgebra
  -- A nonzero coordinate vector gives an isomorphism between the actual parity spaces.
  let j : Fin m := ⟨0, hm⟩
  let v : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single j 1
  have hv : v ≠ 0 := by
    intro h
    have hcoord := congrArg (fun x : EuclideanSpace ℂ (Fin m) ↦ x j) h
    simp [v] at hcoord
  have hequal : Module.finrank ℂ (CliffordAlgebra.evenOdd Q 0) =
      Module.finrank ℂ (CliffordAlgebra.evenOdd Q 1) := by
    let E : CliffordAlgebra.evenOdd Q 0 ≃ₗ[ℂ] CliffordAlgebra.evenOdd Q 1 :=
      (cliffordSymbolParityEquiv v hv 0).trans
        (LinearEquiv.ofEq _ _ (by congr 1))
    exact E.finrank_eq
  -- Equal summand dimensions and the full spinor dimension determine each half.
  have hsum : Module.finrank ℂ (CliffordAlgebra.evenOdd Q 0) +
      Module.finrank ℂ (CliffordAlgebra.evenOdd Q 1) = 2 ^ m := by
    rw [Submodule.finrank_add_eq_of_isCompl (CliffordAlgebra.evenOdd_isCompl Q)]
    exact finrank_complexSpinor m
  have hpow : 2 ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hm]
    rw [pow_succ]
  have heven : Module.finrank ℂ (CliffordAlgebra.evenOdd Q 0) = 2 ^ (m - 1) := by
    omega
  rw [complexHalfSpinor_eq_evenOdd]
  fin_cases i
  · exact heven
  · exact hequal ▸ heven

end AtiyahSinger
