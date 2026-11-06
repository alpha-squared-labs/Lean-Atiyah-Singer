/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RealSpinor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The coordinate angle family in the actual spin group

Public module ID: M0061.

For the original negative real quadratic form, each ordered coordinate pair
e_j, i*e_j gives a bivector B_j with square -1. The displayed ordered product
of cos(theta_j)+sin(theta_j)*B_j lies in mathlib's native spinGroup and is
additive in the angle parameters. Its original vector representation rotates
the j-th complex coordinate by twice theta_j, fixing the half-angle convention
used by the complex spinor weights.

Source: Lawson--Michelsohn, Spin Geometry, I.6, the displayed standard torus
and equations (6.11)--(6.15), printed pp. 43--44. The precise angle kernel is
an elementary project supplement: it is pi times the integer vectors with
even coordinate sum, rather than the product of the individual 2*pi periods.
We construct a parameterized family; no maximality or quotient-torus topology
is claimed. When m=0 the product is empty and equals one, without identifying
the native rank-zero spin group with a separate geometric convention.
Proofs use the original real Clifford algebra and native spin subgroup throughout.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- The ordered real coordinate bivector in the original negative Clifford algebra. -/
def spinPlaneBivector (m : ℕ) (j : Fin m) :
    CliffordAlgebra (realSpinorQuadraticForm m) :=
  CliffordAlgebra.ι (realSpinorQuadraticForm m) (EuclideanSpace.single j (1 : ℂ)) *
    CliffordAlgebra.ι (realSpinorQuadraticForm m) (EuclideanSpace.single j Complex.I)

/-- The actual Clifford product in increasing coordinate order, before subgroup restriction. -/
def spinTorusProduct (m : ℕ) (theta : Fin m → ℝ) :
    CliffordAlgebra (realSpinorQuadraticForm m) :=
  (List.ofFn (fun j : Fin m ↦
    algebraMap ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) (Real.cos (theta j)) +
      Real.sin (theta j) • spinPlaneBivector m j)).prod

private theorem spinTorusFactor_mem_spinGroup (m : ℕ) (j : Fin m) (t : ℝ) :
    algebraMap ℝ (CliffordAlgebra (realSpinorQuadraticForm m)) (Real.cos t) +
      Real.sin t • (CliffordAlgebra.ι (realSpinorQuadraticForm m)
        (EuclideanSpace.single j (1 : ℂ)) *
        CliffordAlgebra.ι (realSpinorQuadraticForm m) (EuclideanSpace.single j Complex.I)) ∈
      spinGroup (realSpinorQuadraticForm m) := by
  -- Unit vectors are native Lipschitz generators and are Clifford-unitary.
  have hunit (v : EuclideanSpace ℂ (Fin m))
      (hq : realSpinorQuadraticForm m v = -1) :
      CliffordAlgebra.ι (realSpinorQuadraticForm m) v ∈
        pinGroup (realSpinorQuadraticForm m) := by
    let Q := realSpinorQuadraticForm m
    let a := CliffordAlgebra.ι Q v
    have haa : a * a = -1 := by
      simpa only [a, Q, hq, map_neg, map_one] using CliffordAlgebra.ι_sq_scalar Q v
    let u : (CliffordAlgebra Q)ˣ := ⟨a, -a, by simp [haa], by simp [haa]⟩
    have hu : u ∈ lipschitzGroup Q := Subgroup.subset_closure ⟨v, rfl⟩
    change (u : CliffordAlgebra Q) ∈ pinGroup Q
    apply pinGroup.units_mem_iff.mpr
    refine ⟨hu, ?_⟩
    change star a * a = 1 ∧ a * star a = 1
    have hstar : star a = -a := CliffordAlgebra.star_ι v
    simp [hstar, haa]
  -- Express the trigonometric factor as the ordered product of two unit vectors.
  let Q := realSpinorQuadraticForm m
  let e : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single j 1
  let f : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single j Complex.I
  let w := Real.cos t • e - Real.sin t • f
  have hform (v : EuclideanSpace ℂ (Fin m)) : Q v = -‖v‖ ^ 2 := by
    let := InnerProductSpace.complexToReal (G := EuclideanSpace ℂ (Fin m))
    change -(inner ℝ v v) = -‖v‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  have he : Q e = -1 := by simp [hform, e, PiLp.norm_single]
  have hwcoord : w = EuclideanSpace.single j ((Real.cos t : ℂ) - Real.sin t * Complex.I) := by
    ext k
    by_cases h : j = k
    · subst k
      simp [w, e, f, Complex.real_smul]
    · simp [w, e, f, Ne.symm h]
  have hw : Q w = -1 := by
    rw [hform, hwcoord, PiLp.norm_single, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im]
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hexpr : algebraMap ℝ (CliffordAlgebra Q) (Real.cos t) +
      Real.sin t • (CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q f) =
      CliffordAlgebra.ι Q (-e) * CliffordAlgebra.ι Q w := by
    rw [map_neg]
    simp only [w, map_sub, map_smul, mul_sub, mul_smul_comm, neg_mul,
      CliffordAlgebra.ι_sq_scalar, he, map_neg, map_one, smul_neg, Algebra.algebraMap_eq_smul_one]
    simp
  rw [hexpr]
  refine spinGroup.mem_iff.mpr ⟨?_, ?_⟩
  · apply (pinGroup Q).mul_mem
    · exact hunit (-e) (by change Q (-e) = -1; simpa only [QuadraticMap.map_neg] using he)
    · exact hunit w hw
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q (-e) w

/-- Each coordinate rotation product belongs to the actual native spin subgroup. -/
theorem spinTorusProduct_mem_spinGroup (m : ℕ) (theta : Fin m → ℝ) :
    spinTorusProduct m theta ∈ spinGroup (realSpinorQuadraticForm m) := by
  -- The ordered finite product remains in the native spin submonoid, including rank zero.
  apply (spinGroup (realSpinorQuadraticForm m)).list_prod_mem
  intro a ha
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
  exact spinTorusFactor_mem_spinGroup m j (theta j)

/-- SG's specified coordinate angle family, as elements of the original real spin group. -/
def spinTorusElement (m : ℕ) (theta : Fin m → ℝ) :
    spinGroup (realSpinorQuadraticForm m) :=
  ⟨spinTorusProduct m theta, spinTorusProduct_mem_spinGroup m theta⟩

private theorem realSpinor_polar (m : ℕ) (v w : EuclideanSpace ℂ (Fin m)) :
    QuadraticMap.polar (realSpinorQuadraticForm m) v w =
      -2 * (inner ℂ v w).re := by
  let := InnerProductSpace.complexToReal (G := EuclideanSpace ℂ (Fin m))
  change QuadraticMap.polar (-⇑(LinearMap.BilinMap.toQuadraticMap
    (innerₗ (EuclideanSpace ℂ (Fin m))))) v w = _
  rw [QuadraticMap.polar_neg, LinearMap.BilinMap.polar_toQuadraticMap]
  change -(inner ℝ v w + inner ℝ w v) = _
  rw [real_inner_comm v w]
  change -( (inner ℂ v w).re + (inner ℂ v w).re) = _
  ring

/-- Addition of angle parameters is multiplication of the specified spin elements. -/
theorem spinTorusElement_add (m : ℕ) (theta phi : Fin m → ℝ) :
    spinTorusElement m (theta + phi) = spinTorusElement m theta * spinTorusElement m phi := by
  -- The original Clifford relations give square minus one and commuting coordinate bivectors.
  let Q := realSpinorQuadraticForm m
  let a (j : Fin m) := CliffordAlgebra.ι Q (EuclideanSpace.single j (1 : ℂ))
  let b (j : Fin m) := CliffordAlgebra.ι Q (EuclideanSpace.single j Complex.I)
  have hform (v : EuclideanSpace ℂ (Fin m)) : Q v = -‖v‖ ^ 2 := by
    let := InnerProductSpace.complexToReal (G := EuclideanSpace ℂ (Fin m))
    change -(inner ℝ v v) = -‖v‖ ^ 2
    rw [real_inner_self_eq_norm_sq]
  have hsquare (j : Fin m) : spinPlaneBivector m j * spinPlaneBivector m j = -1 := by
    have he : Q (EuclideanSpace.single j (1 : ℂ)) = -1 := by
      simp [hform, PiLp.norm_single]
    have hf : Q (EuclideanSpace.single j Complex.I) = -1 := by
      simp [hform, PiLp.norm_single]
    have hp : QuadraticMap.polar Q (EuclideanSpace.single j (1 : ℂ))
        (EuclideanSpace.single j Complex.I) = 0 := by
      simp [Q, realSpinor_polar, EuclideanSpace.inner_single_left]
    change (a j * b j) * (a j * b j) = -1
    rw [← mul_assoc, show a j * b j * a j = b j from by
      simpa [a, b, he, hp] using CliffordAlgebra.ι_mul_ι_mul_ι (Q := Q)
        (EuclideanSpace.single j (1 : ℂ)) (EuclideanSpace.single j Complex.I)]
    simp [b, hf]
  have hcomm (i j : Fin m) : Commute (spinPlaneBivector m i) (spinPlaneBivector m j) := by
    by_cases hij : i = j
    · subst j
      exact Commute.refl _
    have hanti (z w : ℂ) :
        CliffordAlgebra.ι Q (EuclideanSpace.single i z) *
          CliffordAlgebra.ι Q (EuclideanSpace.single j w) =
        -(CliffordAlgebra.ι Q (EuclideanSpace.single j w) *
          CliffordAlgebra.ι Q (EuclideanSpace.single i z)) := by
      apply CliffordAlgebra.ι_mul_ι_comm_of_isOrtho
      apply QuadraticMap.isOrtho_polarBilin.mp
      change QuadraticMap.polar Q _ _ = 0
      simp [Q, realSpinor_polar, EuclideanSpace.inner_single_left, hij]
    have hp (w : ℂ) : Commute (a i * b i)
        (CliffordAlgebra.ι Q (EuclideanSpace.single j w)) := by
      let c := CliffordAlgebra.ι Q (EuclideanSpace.single j w)
      change a i * b i * c = c * (a i * b i)
      calc
        a i * b i * c = a i * (b i * c) := mul_assoc _ _ _
        _ = a i * -(c * b i) := by rw [show b i * c = -(c * b i) from hanti Complex.I w]
        _ = -(a i * c) * b i := by noncomm_ring
        _ = -(-(c * a i)) * b i := by rw [show a i * c = -(c * a i) from hanti 1 w]
        _ = c * (a i * b i) := by noncomm_ring
    exact (hp 1).mul_right (hp Complex.I)
  -- Pair the factors using angle addition, and commute only the justified coordinate terms.
  let f (t : Fin m → ℝ) (j : Fin m) : CliffordAlgebra Q :=
    algebraMap ℝ (CliffordAlgebra Q) (Real.cos (t j)) +
      Real.sin (t j) • spinPlaneBivector m j
  have hfcomm (t s : Fin m → ℝ) (i j : Fin m) : Commute (f t i) (f s j) := by
    exact (Algebra.commute_algebraMap_left _ _).add_left
      ((Algebra.commute_algebraMap_right _ _).add_right
        ((hcomm i j).smul_left _ |>.smul_right _))
  have hfadd (j : Fin m) : f (theta + phi) j = f theta j * f phi j := by
    dsimp [f]
    rw [Real.cos_add, Real.sin_add]
    simp only [map_mul, map_add, add_smul, mul_add, add_mul,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
      one_mul, mul_one, hsquare, smul_neg, sub_eq_add_neg]
    module
  have hprod (l : List (Fin m)) :
      (l.map (f (theta + phi))).prod = (l.map (f theta)).prod * (l.map (f phi)).prod := by
    induction l with
    | nil => simp
    | cons j l ih =>
      simp only [List.map_cons, List.prod_cons, hfadd, ih]
      have hmove : Commute (f phi j) (l.map (f theta)).prod := by
        apply Commute.list_prod_right
        intro x hx
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
        exact hfcomm phi theta j i
      calc
        (f theta j * f phi j) * ((l.map (f theta)).prod * (l.map (f phi)).prod) =
            f theta j * (f phi j * (l.map (f theta)).prod) * (l.map (f phi)).prod := by
          simp only [mul_assoc]
        _ = (f theta j * (l.map (f theta)).prod) *
            (f phi j * (l.map (f phi)).prod) := by
          rw [hmove.eq]
          simp only [mul_assoc]
  apply Subtype.ext
  change spinTorusProduct m (theta + phi) = spinTorusProduct m theta * spinTorusProduct m phi
  simpa only [spinTorusProduct, List.ofFn_eq_map] using hprod (List.finRange m)

/-- The original real vector action rotates each complex coordinate through twice its angle. -/
theorem realSpinVectorRepresentation_spinTorusElement (m : ℕ) (theta : Fin m → ℝ)
    (v : EuclideanSpace ℂ (Fin m)) (j : Fin m) :
    realSpinVectorRepresentation m (spinTorusElement m theta) v j =
      Complex.exp (2 * Complex.I * (theta j : ℂ)) * v j := by
  -- Construct the original one-coordinate spin factors, with native subgroup membership.
  let Q := realSpinorQuadraticForm m
  let f (i : Fin m) : spinGroup Q :=
    ⟨algebraMap ℝ (CliffordAlgebra Q) (Real.cos (theta i)) +
      Real.sin (theta i) • spinPlaneBivector m i,
      spinTorusFactor_mem_spinGroup m i (theta i)⟩
  have hfactor (i : Fin m) (v : EuclideanSpace ℂ (Fin m)) (j : Fin m) :
      realSpinVectorRepresentation m (f i) v j =
        (if i = j then Complex.exp (2 * Complex.I * (theta i : ℂ)) else 1) * v j := by
    let e : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single i 1
    let w : EuclideanSpace ℂ (Fin m) := EuclideanSpace.single i
      ((Real.cos (theta i) : ℂ) - Real.sin (theta i) * Complex.I)
    have hform (v : EuclideanSpace ℂ (Fin m)) : Q v = -‖v‖ ^ 2 := by
      let := InnerProductSpace.complexToReal (G := EuclideanSpace ℂ (Fin m))
      change -(inner ℝ v v) = -‖v‖ ^ 2
      rw [real_inner_self_eq_norm_sq]
    have he : Q e = -1 := by simp [hform, e, PiLp.norm_single]
    have hw : Q w = -1 := by
      rw [hform, PiLp.norm_single, Complex.sq_norm]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.mul_im]
      nlinarith [Real.sin_sq_add_cos_sq (theta i)]
    have hwexpr : w = Real.cos (theta i) • e -
        Real.sin (theta i) • EuclideanSpace.single i Complex.I := by
      ext k
      by_cases h : i = k
      · subst k
        simp [w, e, Complex.real_smul]
      · simp [w, e, Ne.symm h]
    have hfexpr : (f i : CliffordAlgebra Q) =
        -(CliffordAlgebra.ι Q e) * CliffordAlgebra.ι Q w := by
      change algebraMap ℝ (CliffordAlgebra Q) (Real.cos (theta i)) +
        Real.sin (theta i) • (CliffordAlgebra.ι Q e *
          CliffordAlgebra.ι Q (EuclideanSpace.single i Complex.I)) = _
      rw [hwexpr]
      simp only [map_sub, map_smul, mul_sub, mul_smul_comm, neg_mul,
        CliffordAlgebra.ι_sq_scalar, he, map_neg, map_one, smul_neg,
        Algebra.algebraMap_eq_smul_one]
      simp
    -- Apply the Clifford triple-product identity twice to compute the actual conjugation.
    let u := QuadraticMap.polar Q w v • w + v
    have haction : realSpinVectorRepresentation m (f i) v =
        QuadraticMap.polar Q e u • e + u := by
      apply (realSpinorVectorEmbeddingEquiv m).injective
      apply Subtype.ext
      change CliffordAlgebra.ι Q (realSpinVectorRepresentation m (f i) v) = _
      rw [(realSpinVectorRepresentation_properties m (f i) v).1]
      change (f i : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
        star (f i : CliffordAlgebra Q) = _
      rw [hfexpr]
      simp only [star_mul, star_neg, CliffordAlgebra.star_ι, neg_neg]
      calc
        (-CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q w) * CliffordAlgebra.ι Q v *
            (-CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q e) =
            CliffordAlgebra.ι Q e *
              (CliffordAlgebra.ι Q w * CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q w) *
                CliffordAlgebra.ι Q e := by noncomm_ring
        _ = CliffordAlgebra.ι Q e * CliffordAlgebra.ι Q u * CliffordAlgebra.ι Q e := by
          rw [CliffordAlgebra.ι_mul_ι_mul_ι]
          simp only [hw, neg_smul, one_smul, sub_neg_eq_add, u]
        _ = CliffordAlgebra.ι Q (QuadraticMap.polar Q e u • e + u) := by
          rw [CliffordAlgebra.ι_mul_ι_mul_ι]
          simp only [he, neg_smul, one_smul, sub_neg_eq_add]
    -- Read the same conjugation on complex coordinates and identify the doubled angle.
    rw [haction]
    by_cases hij : i = j
    · subst j
      simp only [ite_true]
      have hp : QuadraticMap.polar Q w v =
          -2 * (Real.cos (theta i) * (v i).re - Real.sin (theta i) * (v i).im) := by
        rw [show QuadraticMap.polar Q w v =
          -2 * (inner ℂ w v).re from realSpinor_polar m w v]
        simp only [w, EuclideanSpace.inner_single_left, Complex.mul_re,
          Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
        ring
      have hpu : QuadraticMap.polar Q e u = -2 * (u i).re := by
        simp [Q, realSpinor_polar, e, EuclideanSpace.inner_single_left]
      rw [hpu]
      have hexp : Complex.exp (2 * Complex.I * (theta i : ℂ)) =
          (Real.cos (2 * theta i) : ℂ) + Real.sin (2 * theta i) * Complex.I := by
        rw [show 2 * Complex.I * (theta i : ℂ) = ((2 * theta i : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_ofReal_mul_I]
      rw [hexp]
      apply Complex.ext
      · simp only [u, hp, e, w, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
          ite_true, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.real_smul, Complex.one_re,
          Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.add_im,
          Real.cos_two_mul, Real.sin_two_mul]
        ring
      · simp only [u, hp, e, w, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply,
          ite_true, Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
          Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.real_smul, Complex.one_re,
          Complex.one_im, Complex.sub_im, Complex.mul_im, Complex.add_im,
          Real.cos_two_mul, Real.sin_two_mul]
        nlinarith [congrArg (fun x : ℝ ↦ x * (v i).im)
          (Real.sin_sq_add_cos_sq (theta i))]
    · simp [hij, u, e, w, Ne.symm hij]
  -- The representation is multiplicative; the ordered list contains each coordinate once.
  have hprod : spinTorusElement m theta = ((List.finRange m).map f).prod := by
    apply Subtype.ext
    simp only [Submonoid.coe_list_prod, List.map_map, spinTorusElement, spinTorusProduct,
      List.ofFn_eq_map]
    rfl
  rw [hprod]
  have hlist (l : List (Fin m)) (v : EuclideanSpace ℂ (Fin m)) :
      realSpinVectorRepresentation m (l.map f).prod v j =
        (l.map (fun i ↦ if i = j then
          Complex.exp (2 * Complex.I * (theta i : ℂ)) else 1)).prod * v j := by
    induction l generalizing v with
    | nil => simp
    | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, LinearEquiv.mul_apply]
      rw [hfactor, ih]
      simp only [mul_assoc]
  rw [hlist]
  congr 1
  rw [← List.ofFn_eq_map, Fin.prod_ofFn]
  simp

/-- The exact period lattice of this angle family is pi times the even-sum integer lattice. -/
theorem spinTorusElement_eq_one_iff (m : ℕ) (theta : Fin m → ℝ) :
    spinTorusElement m theta = 1 ↔
      ∃ k : Fin m → ℤ, (∀ j, theta j = (k j : ℝ) * Real.pi) ∧ Even (∑ j, k j) := by
  -- Integer multiples of pi reduce the ordered product to a scalar parity sign.
  let Q := realSpinorQuadraticForm m
  have hscalar (k : Fin m → ℤ) :
      spinTorusProduct m (fun j ↦ (k j : ℝ) * Real.pi) =
        algebraMap ℝ (CliffordAlgebra Q) ((-1 : ℝ) ^ (∑ j, k j)) := by
    have hlist (l : List (Fin m)) :
        (l.map (fun j ↦ algebraMap ℝ (CliffordAlgebra Q) ((-1 : ℝ) ^ k j))).prod =
          algebraMap ℝ (CliffordAlgebra Q) ((-1 : ℝ) ^ (l.map k).sum) := by
      induction l with
      | nil => simp
      | cons j l ih =>
        simp only [List.map_cons, List.prod_cons, List.sum_cons, ih,
          zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), map_mul]
    simpa only [spinTorusProduct, Real.sin_int_mul_pi, Real.cos_int_mul_pi,
      zero_smul, add_zero, List.ofFn_eq_map, ← Fin.sum_univ_def] using
      hlist (List.finRange m)
  -- The actual vector representation forces every coordinate angle to be integral in pi.
  constructor
  · intro h
    have hinteger (j : Fin m) : ∃ k : ℤ, theta j = (k : ℝ) * Real.pi := by
      have hcoord := realSpinVectorRepresentation_spinTorusElement m theta
        (EuclideanSpace.single j 1) j
      rw [h, map_one] at hcoord
      have hexp : Complex.exp (2 * Complex.I * (theta j : ℂ)) = 1 := by
        simpa using hcoord.symm
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
      refine ⟨k, ?_⟩
      have him := congrArg Complex.im hk
      norm_num [Complex.mul_im, Complex.mul_re] at him
      nlinarith
    choose k hk using hinteger
    refine ⟨k, hk, ?_⟩
    -- Faithfulness of real scalar inclusion identifies the remaining even-sum condition.
    have htheta : theta = fun j ↦ (k j : ℝ) * Real.pi := funext hk
    have hval : spinTorusProduct m theta = 1 := congrArg Subtype.val h
    rw [htheta, hscalar] at hval
    have hs : (-1 : ℝ) ^ (∑ j, k j) = 1 := by
      apply (algebraMap ℝ (CliffordAlgebra Q)).injective
      simpa only [map_one] using hval
    by_contra hn
    simp only [neg_one_zpow_eq_ite, hn, ite_false] at hs
    norm_num at hs
  · rintro ⟨k, hk, heven⟩
    apply Subtype.ext
    change spinTorusProduct m theta = 1
    rw [show theta = fun j ↦ (k j : ℝ) * Real.pi from funext hk, hscalar,
      heven.neg_one_zpow, map_one]
end AtiyahSinger
