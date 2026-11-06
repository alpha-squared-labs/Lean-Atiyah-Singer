/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.FiniteRepresentationCoefficients
public import AtiyahSinger.Algebra.RepresentationRing
public import AtiyahSinger.Analysis.SphereHarmonicCoordinates
public import AtiyahSinger.Geometry.SphereFormCoefficients
public import AtiyahSinger.Geometry.SphereHodge
public import Mathlib.Topology.Algebra.Group.Matrix

/-!
# The actual equivariant de Rham index of the sphere

Public module ID: M1008.

The index is the difference of the actual smooth kernel and quotient-cokernel
representations of the round even-to-odd de Rham operator. Each finite coordinate
presentation is required to intertwine the original inverse-pullback action on
that same kernel and that same smooth range quotient. It includes joint continuity.
The index is not defined to be the cohomological Euler sum; Hodge theory proves
that equality and then computes it as one plus the signed determinant class.

SG III.9 Definition 9.3 and the de Rham example on p.212 specify this intrinsic
analytic index. SG III.13.7 p.253 uses the sphere but incorrectly describes the
top action in even dimensions and makes an invalid cancellation in R(O(r)).
Here the top action is det in every positive dimension, and no cancellation is
used. ASI p.524 independently states the complex-cohomology index and its O(1)
example. The rank-zero sphere has two independent points and index two.

This is the smooth differential operator's analytic index in the source sense.
Comparison with the separately presented PDO or K-symbol index requires
identifying the same operator and actions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped DirectSum Manifold ContDiff

set_option maxSynthPendingDepth 25

/-- The determinant character, as an actual jointly continuous one-dimensional representation. -/
def orthogonalDeterminantRepresentation (r : ℕ) :
    FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ) where
  dimension := 1
  representation := ContRepresentation.ofMonoidHom
    { toFun A := (A.val.det : ℂ) • ContinuousLinearMap.id ℂ (Fin 1 → ℂ)
      map_one' := by
        ext v i
        simp
      map_mul' A B := by
        ext v i
        simp [Matrix.det_mul, mul_assoc, mul_left_comm] }
  continuous_action := by
    apply continuous_pi
    intro i
    change Continuous (fun p : Matrix.orthogonalGroup (Fin r) ℝ × (Fin 1 → ℂ) ↦
      (p.1.val.det : ℂ) * p.2 i)
    exact (Complex.continuous_ofReal.comp
      (continuous_subtype_val.comp continuous_fst).matrix_det).mul
        ((continuous_apply i).comp continuous_snd)

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates instance synthesis for the actual harmonic and quotient
-- representations.
set_option maxHeartbeats 1500000 in
-- Compare all specified original carriers and coefficient maps in one finite presentation.
/-- Finite coordinates represent the actual positive de Rham kernel and smooth quotient-cokernel. -/
theorem exists_orthogonalSphereHodgeRepresentations (r : ℕ) :
    ∃ ρ τ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ),
      ∃ e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ]
          LinearMap.ker (positiveHodgeDirac (orthogonalSphereRoundMetric r)),
        ∃ f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ]
            PositiveHodgeCokernel (orthogonalSphereRoundMetric r),
          (∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (v : Fin ρ.dimension → ℂ),
            (e (ρ.representation A v)).val =
              orthogonalSphereEvenFormRepresentation r A (e v).val) ∧
          (∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
              (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)),
            f (τ.representation A
                (f.symm ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ v))) =
              (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ
                (orthogonalSphereOddFormRepresentation r A v)) := by
  /- Stage 1: the genuine positive de Rham operator is equivariant for the
  specified round action. Its actual kernel and smooth range are invariant.
  The canonical same-form harmonic kernel and quotient maps identify these
  two carriers with even and odd harmonic forms, and Hodge finiteness applies.
  Stage 2: joint continuity in finite coordinates follows from the actual
  sphere matrix action. In native charts its inverse-pullback coefficients
  depend continuously on the matrix. On the finite harmonic spaces, finitely
  many pointwise tensor evaluations separate vectors and supply continuous
  finite coordinates; integrate or evaluate these same transformed forms.
  The canonical quotient map transfers this action to the actual cokernel.
  Stage 3: choose finite coordinates for these two spaces and conjugate the
  actions. The displayed equations retain both original maps on every vector
  and quotient representative. No norm on all smooth forms, closure of the
  range, abstract Euler representation or Lie-group atlas is substituted. -/
  classical
  let g := orthogonalSphereRoundMetric r
  let D := positiveHodgeDirac g
  let RE := orthogonalSphereEvenFormRepresentation r
  let RF := orthogonalSphereOddFormRepresentation r
  let K := LinearMap.ker D
  let H := oddHarmonicForms g
  let F := SmoothDifferentialForm (n := r) (OrthogonalSphere r)
  let I := Σ p : ℕ, OrthogonalSphere r × (Fin p → EuclideanSpace ℝ (Fin r))
  -- Pointwise tensor evaluation separates the actual total smooth forms.
  let J : TotalSmoothDifferentialForm (n := r) (OrthogonalSphere r) →ₗ[ℂ] (I → ℂ) := {
    toFun u i := (u i.1).val i.2.1 i.2.2
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hJ : Function.Injective J := by
    intro u v h
    apply DFinsupp.ext
    intro p
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro w
    exact congrFun h ⟨p, x, w⟩
  have hcoeff (i : I) (u : TotalSmoothDifferentialForm (n := r) (OrthogonalSphere r)) :
      Continuous (fun A : Matrix.orthogonalGroup (Fin r) ℝ ↦
        J (orthogonalSphereTotalFormAction r A u) i) :=
    continuous_orthogonalSphere_smoothFormPullback_eval r i.1 (u i.1) i.2.1 i.2.2
  -- Equivariance preserves the actual kernel and the actual smooth range.
  have hK : ∀ A, K ≤ K.comap (RE A) := by
    intro A u hu
    change D (RE A u) = 0
    have heq := LinearMap.congr_fun (positiveHodgeDirac_orthogonalSphere_equivariant r A) u
    change D (RE A u) = RF A (D u) at heq
    exact heq.trans ((congrArg (RF A) hu).trans (map_zero (RF A)))
  have hRange : ∀ A, D.range ≤ D.range.comap (RF A) := by
    intro A u hu
    obtain ⟨v, rfl⟩ := hu
    refine ⟨RE A v, ?_⟩
    exact LinearMap.congr_fun (positiveHodgeDirac_orthogonalSphere_equivariant r A) v
  let RK := RE.subrepresentation K hK
  let RC := RF.quotient D.range hRange
  let JK := J.comp ((evenSmoothDifferentialForms (n := r)
    (M := OrthogonalSphere r)).subtype.comp K.subtype)
  have hJK : Function.Injective JK := hJ.comp (Subtype.val_injective.comp Subtype.val_injective)
  have : FiniteDimensional ℂ K := finiteDimensional_positiveHodgeDirac_ker g
  obtain ⟨ρ, e, he⟩ := exists_finiteContinuousRepresentation_of_coefficients RK JK hJK
    (fun i u ↦ hcoeff i u.val.val)
  -- Degreewise metric naturality preserves the same odd harmonic subspace.
  have hΔ (A : Matrix.orthogonalGroup (Fin r) ℝ) :
      (totalFormHodgeLaplacian g).comp (orthogonalSphereTotalFormAction r A) =
        (orthogonalSphereTotalFormAction r A).comp (totalFormHodgeLaplacian g) := by
    apply DirectSum.linearMap_ext
    intro p
    apply LinearMap.ext
    intro u
    simp only [LinearMap.comp_apply, orthogonalSphereTotalFormAction, DirectSum.lmap_lof,
      totalFormHodgeLaplacian, DirectSum.toModule_lof]
    exact congrArg (DirectSum.lof ℂ ℕ F p)
      (LinearMap.congr_fun (smoothFormHodgeLaplacian_pullback g g
        (orthogonalSphereDiffeomorph r A⁻¹)
        (orthogonalSphereRoundMetric_invariant r A⁻¹) p) u)
  have hH : ∀ A, H ≤ H.comap (RF A) := by
    intro A u hu
    change totalFormHodgeLaplacian g
      (orthogonalSphereTotalFormAction r A u.val) = 0
    have heq := LinearMap.congr_fun (hΔ A) u.val
    change totalFormHodgeLaplacian g (orthogonalSphereTotalFormAction r A u.val) =
      orthogonalSphereTotalFormAction r A (totalFormHodgeLaplacian g u.val) at heq
    exact heq.trans ((congrArg (orthogonalSphereTotalFormAction r A) hu).trans (map_zero _))
  let RH := RF.subrepresentation H hH
  let JH := J.comp ((oddSmoothDifferentialForms (n := r)
    (M := OrthogonalSphere r)).subtype.comp H.subtype)
  have hJH : Function.Injective JH := hJ.comp (Subtype.val_injective.comp Subtype.val_injective)
  let c : H ≃ₗ[ℂ] PositiveHodgeCokernel g := oddHarmonicCokernelEquiv g
  have : FiniteDimensional ℂ (PositiveHodgeCokernel g) :=
    finiteDimensional_positiveHodgeDirac_coker g
  have : FiniteDimensional ℂ H := c.symm.finiteDimensional
  obtain ⟨τ, fH, hfH⟩ := exists_finiteContinuousRepresentation_of_coefficients RH JH hJH
    (fun i u ↦ hcoeff i u.val.val)
  -- The harmonic equivalence uses precisely the original quotient map on each form.
  have hc (A : Matrix.orthogonalGroup (Fin r) ℝ) (u : H) :
      c (RH A u) = RC A (c u) := rfl
  let f := fH.trans c
  have hf (A : Matrix.orthogonalGroup (Fin r) ℝ) (v : Fin τ.dimension → ℂ) :
      f (τ.representation A v) = RC A (f v) :=
    (congrArg c (hfH A v)).trans (hc A (fH v))
  refine ⟨ρ, τ, e, f, ?_, ?_⟩
  · intro A v
    exact congrArg Subtype.val (he A v)
  · intro A v
    exact (hf A (f.symm (D.range.mkQ v))).trans
      (congrArg (RC A) (f.apply_symm_apply (D.range.mkQ v)))

/-- The intrinsic analytic index of the actual round even-to-odd de Rham operator. -/
def orthogonalSphereDeRhamIndex (r : ℕ) :
    RepresentationGrothendieckGroup (Matrix.orthogonalGroup (Fin r) ℝ) :=
  let h := exists_orthogonalSphereHodgeRepresentations r
  finiteRepresentationClass h.choose - finiteRepresentationClass h.choose_spec.choose

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates instance synthesis for the actual harmonic and quotient
-- representations.
/-- Any equivariant finite coordinates on the same kernel and range quotient compute the index. -/
theorem orthogonalSphereDeRhamIndex_eq (r : ℕ)
    (ρ τ : FiniteContinuousRepresentation (Matrix.orthogonalGroup (Fin r) ℝ))
    (e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ]
      LinearMap.ker (positiveHodgeDirac (orthogonalSphereRoundMetric r)))
    (f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ]
      PositiveHodgeCokernel (orthogonalSphereRoundMetric r))
    (he : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (v : Fin ρ.dimension → ℂ),
      (e (ρ.representation A v)).val =
        orthogonalSphereEvenFormRepresentation r A (e v).val)
    (hf : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
        (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)),
      f (τ.representation A
          (f.symm ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ v))) =
        (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ
          (orthogonalSphereOddFormRepresentation r A v)) :
    orthogonalSphereDeRhamIndex r = finiteRepresentationClass ρ - finiteRepresentationClass τ := by
  /- Compare the chosen kernel coordinates with e: their composite intertwines
  the same even inverse-pullback action. Compare the chosen cokernel coordinates
  with f using surjectivity of the original smooth range quotient. Each finite
  linear intertwiner is continuous, so its representation classes agree.
  Subtract the two class equalities. Dimension alone is not used to compare
  representations, and no choice of a different operator is allowed. -/
  classical
  let hex := exists_orthogonalSphereHodgeRepresentations r
  let ρ₀ := hex.choose
  let τ₀ := hex.choose_spec.choose
  obtain ⟨e₀, f₀, he₀, hf₀⟩ := hex.choose_spec.choose_spec
  -- Both coordinate systems intertwine the same original even-form action.
  have hρ : ρ₀.IsEquivalent ρ := by
    refine ⟨ContRepresentation.Equiv.mk (e₀.trans e.symm).toContinuousLinearEquiv ?_⟩
    intro A
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    apply Subtype.val_injective
    change (e (e.symm (e₀ (ρ₀.representation A v)))).val =
      (e (ρ.representation A (e.symm (e₀ v)))).val
    exact (congrArg Subtype.val (e.apply_symm_apply _)).trans
      ((he₀ A v).trans
        (((he A (e.symm (e₀ v))).trans
          (congrArg (fun w : LinearMap.ker
              (positiveHodgeDirac (orthogonalSphereRoundMetric r)) ↦
            orthogonalSphereEvenFormRepresentation r A w.val)
              (e.apply_symm_apply (e₀ v)))).symm))
  -- Compare the two quotient actions on one actual representative of each class.
  have quotientCompare (τ₀ : FiniteContinuousRepresentation
        (Matrix.orthogonalGroup (Fin r) ℝ))
      (f₀ : (Fin τ₀.dimension → ℂ) ≃ₗ[ℂ]
        PositiveHodgeCokernel (orthogonalSphereRoundMetric r))
      (hf₀ : ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ)
          (v : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r)),
        f₀ (τ₀.representation A
          (f₀.symm ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ v))) =
            (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ
              (orthogonalSphereOddFormRepresentation r A v)) : τ₀.IsEquivalent τ := by
    refine ⟨ContRepresentation.Equiv.mk (f₀.trans f.symm).toContinuousLinearEquiv ?_⟩
    intro A
    apply ContinuousLinearMap.ext
    intro v
    apply f.injective
    change f (f.symm (f₀ (τ₀.representation A v))) =
      f (τ.representation A (f.symm (f₀ v)))
    refine (f.apply_symm_apply _).trans ?_
    obtain ⟨w, hw⟩ := (positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ_surjective
      (f₀ v)
    have h₀ := hf₀ A w
    have h₁ := hf A w
    have hc : f₀.symm
        ((positiveHodgeDirac (orthogonalSphereRoundMetric r)).range.mkQ w) = v :=
      (congrArg f₀.symm hw).trans (f₀.symm_apply_apply v)
    have h₀' := (congrArg (fun z ↦ f₀ (τ₀.representation A z)) hc).symm.trans h₀
    have h₁' := (congrArg (fun z ↦ f (τ.representation A (f.symm z))) hw).symm.trans h₁
    exact h₀'.trans h₁'.symm
  have hτ := quotientCompare τ₀ f₀ hf₀
  change finiteRepresentationClass ρ₀ - finiteRepresentationClass τ₀ = _
  rw [finiteRepresentationClass_eq_of_isEquivalent ρ₀ ρ hρ,
    finiteRepresentationClass_eq_of_isEquivalent τ₀ τ hτ]

set_option maxHeartbeats 2500000 in
-- Compare the actual parity harmonic spaces through the same total-form coordinates.
set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates instance synthesis for the actual harmonic and quotient
-- representations.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full orthogonal de Rham index in positive dimension is one plus signed determinant. -/
theorem orthogonalSphereDeRhamIndex_eq_one_add_det (r : ℕ) (hr : 0 < r) :
    orthogonalSphereDeRhamIndex r =
      1 + (-1) ^ r * finiteRepresentationClass (orthogonalDeterminantRepresentation r) := by
  classical
  let S := OrthogonalSphere r
  let g := orthogonalSphereRoundMetric r
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let K := LinearMap.ker (totalFormHodgeLaplacian g)
  obtain ⟨T, hEven, hOdd, hAction⟩ := exists_sphereTotalHarmonicCoordinates r hr
  let iE : evenHarmonicForms g →ₗ[ℂ] K := {
    toFun u := ⟨u.val.val, u.property⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let iO : oddHarmonicForms g →ₗ[ℂ] K := {
    toFun u := ⟨u.val.val, u.property⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  let TE := T.toLinearMap.comp iE
  let TO := T.toLinearMap.comp iO
  have hEi : Function.Injective TE := by
    intro u v h
    have h' : iE u = iE v := T.injective h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : K ↦ w.val) h'
  have hOi : Function.Injective TO := by
    intro u v h
    have h' : iO u = iO v := T.injective h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : K ↦ w.val) h'
  -- A coordinate identity determines the same actual inverse-pulled-back harmonic form.
  have hEaction (A : G) (u v : evenHarmonicForms g)
      (h : TE v = ((TE u).1, (A.val.det : ℂ) * (TE u).2)) :
      v.val = orthogonalSphereEvenFormRepresentation r A u.val := by
    obtain ⟨w, hw, hTw⟩ := hAction A (iE u)
    have heq : iE v = w := T.injective (h.trans hTw.symm)
    apply Subtype.ext
    exact (congrArg Subtype.val heq).trans hw
  have hOaction (A : G) (u v : oddHarmonicForms g)
      (h : TO v = ((TO u).1, (A.val.det : ℂ) * (TO u).2)) :
      v.val = orthogonalSphereOddFormRepresentation r A u.val := by
    obtain ⟨w, hw, hTw⟩ := hAction A (iO u)
    have heq : iO v = w := T.injective (h.trans hTw.symm)
    apply Subtype.ext
    exact (congrArg Subtype.val heq).trans hw
  let oneRep := FiniteContinuousRepresentation.trivial (G := G)
  let detRep := orthogonalDeterminantRepresentation r
  let oneCoordinate := LinearEquiv.funUnique (Fin 1) ℂ ℂ
  by_cases hrEven : Even r
  · -- In even dimension both lines lie in the original positive kernel; the odd quotient is zero.
    have hTE : Function.Surjective TE := by
      intro z
      let u := T.symm z
      have he : u.val ∈ evenSmoothDifferentialForms (n := r) (M := S) :=
        (hEven u).mpr (fun ho ↦ False.elim ((Nat.not_odd_iff_even.mpr hrEven) ho))
      exact ⟨⟨⟨u.val, he⟩, u.property⟩, T.apply_symm_apply z⟩
    let E := LinearEquiv.ofBijective TE ⟨hEi, hTE⟩
    have hOzero (u : oddHarmonicForms g) : TO u = 0 := by
      have h := (hOdd (iO u)).mp u.val.property
      exact Prod.ext h.1 (h.2 hrEven)
    let : Subsingleton (oddHarmonicForms g) :=
      ⟨fun u v ↦ hOi ((hOzero u).trans (hOzero v).symm)⟩
    let : Subsingleton (PositiveHodgeCokernel g) :=
      ⟨fun u v ↦ (oddHarmonicCokernelEquiv g).symm.injective (Subsingleton.elim _ _)⟩
    let ρ := oneRep.directSum detRep
    let τ : FiniteContinuousRepresentation G := {
      dimension := 0
      representation := ContRepresentation.trivial ℂ G (Fin 0 → ℂ)
      continuous_action := continuous_snd }
    let pairCoordinate := LinearEquiv.finTwoArrow ℂ ℂ
    let e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] LinearMap.ker (positiveHodgeDirac g) :=
      pairCoordinate.trans (E.symm.trans (evenHarmonicKernelEquiv g))
    let f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ] PositiveHodgeCokernel g :=
      LinearEquiv.ofSubsingleton (R := ℂ) _ _
    have hρ (A : G) (v : Fin ρ.dimension → ℂ) :
        pairCoordinate (ρ.representation A v) =
          ((pairCoordinate v).1, (A.val.det : ℂ) * (pairCoordinate v).2) := by
      rfl
    have hindex := orthogonalSphereDeRhamIndex_eq r ρ τ e f (by
      intro A v
      change (E.symm (pairCoordinate (ρ.representation A v))).val =
        orthogonalSphereEvenFormRepresentation r A (E.symm (pairCoordinate v)).val
      apply hEaction
      change E (E.symm _) = ((E (E.symm _)).1, (A.val.det : ℂ) * (E (E.symm _)).2)
      rw [E.apply_symm_apply, E.apply_symm_apply, hρ]) (by
      intro A v
      exact Subsingleton.elim _ _)
    have hzero : finiteRepresentationClass τ = 0 := by
      have heq : (τ.directSum τ).IsEquivalent τ := by
        have : Subsingleton (Fin (τ.directSum τ).dimension → ℂ) := by
          change Subsingleton (Fin 0 → ℂ)
          infer_instance
        refine ⟨ContRepresentation.Equiv.mk
          ((LinearEquiv.ofSubsingleton (R := ℂ) _ _).toContinuousLinearEquiv) ?_⟩
        intro A
        exact Subsingleton.elim _ _
      have hsum := finiteRepresentationClass_directSum τ τ
      rw [finiteRepresentationClass_eq_of_isEquivalent _ _ heq] at hsum
      exact add_eq_left.mp hsum.symm
    rw [hindex, hzero, sub_zero, finiteRepresentationClass_directSum,
      hrEven.neg_one_pow, one_mul]
    rfl
  · -- In odd dimension degree zero lies in the kernel and top degree in the actual quotient.
    have hrOdd : Odd r := Nat.not_even_iff_odd.mp hrEven
    have hEtop (u : evenHarmonicForms g) : (TE u).2 = 0 :=
      (hEven (iE u)).mp u.val.property hrOdd
    have hOzero (u : oddHarmonicForms g) : (TO u).1 = 0 :=
      ((hOdd (iO u)).mp u.val.property).1
    let PE := (LinearMap.fst ℂ ℂ ℂ).comp TE
    let PO := (LinearMap.snd ℂ ℂ ℂ).comp TO
    have hPE : Function.Bijective PE := by
      constructor
      · intro u v h
        exact hEi (Prod.ext h ((hEtop u).trans (hEtop v).symm))
      · intro z
        let u := T.symm (z, 0)
        have he : u.val ∈ evenSmoothDifferentialForms (n := r) (M := S) := by
          apply (hEven u).mpr
          intro _
          exact congrArg Prod.snd (T.apply_symm_apply (z, 0))
        refine ⟨⟨⟨u.val, he⟩, u.property⟩, ?_⟩
        exact congrArg Prod.fst (T.apply_symm_apply (z, 0))
    have hPO : Function.Bijective PO := by
      constructor
      · intro u v h
        exact hOi (Prod.ext ((hOzero u).trans (hOzero v).symm) h)
      · intro z
        let u := T.symm (0, z)
        have ho : u.val ∈ oddSmoothDifferentialForms (n := r) (M := S) :=
          (hOdd u).mpr ⟨congrArg Prod.fst (T.apply_symm_apply (0, z)),
            fun he ↦ False.elim (hrEven he)⟩
        refine ⟨⟨⟨u.val, ho⟩, u.property⟩, ?_⟩
        exact congrArg Prod.snd (T.apply_symm_apply (0, z))
    let E := LinearEquiv.ofBijective PE hPE
    let O := LinearEquiv.ofBijective PO hPO
    let e : (Fin oneRep.dimension → ℂ) ≃ₗ[ℂ] LinearMap.ker (positiveHodgeDirac g) :=
      oneCoordinate.trans (E.symm.trans (evenHarmonicKernelEquiv g))
    let f : (Fin detRep.dimension → ℂ) ≃ₗ[ℂ] PositiveHodgeCokernel g :=
      oneCoordinate.trans (O.symm.trans (oddHarmonicCokernelEquiv g))
    have he (A : G) (v : Fin oneRep.dimension → ℂ) :
        (e (oneRep.representation A v)).val =
          orthogonalSphereEvenFormRepresentation r A (e v).val := by
      change (E.symm (oneCoordinate v)).val =
        orthogonalSphereEvenFormRepresentation r A (E.symm (oneCoordinate v)).val
      apply hEaction
      apply Prod.ext
      · rfl
      · rw [hEtop, mul_zero]
    have hodd (A : G) (v : Fin detRep.dimension → ℂ) :
        (O.symm (oneCoordinate (detRep.representation A v))).val =
          orthogonalSphereOddFormRepresentation r A (O.symm (oneCoordinate v)).val := by
      apply hOaction
      apply Prod.ext
      · rw [hOzero, hOzero]
      · change O (O.symm (oneCoordinate (detRep.representation A v))) =
          (A.val.det : ℂ) * O (O.symm (oneCoordinate v))
        rw [O.apply_symm_apply, O.apply_symm_apply]
        rfl
    have hf (A : G) (v : oddSmoothDifferentialForms (n := r) (M := S)) :
        f (detRep.representation A
          (f.symm ((positiveHodgeDirac g).range.mkQ v))) =
        (positiveHodgeDirac g).range.mkQ (orthogonalSphereOddFormRepresentation r A v) := by
      let w := f.symm ((positiveHodgeDirac g).range.mkQ v)
      have hrep : (positiveHodgeDirac g).range.mkQ (O.symm (oneCoordinate w)).val =
          (positiveHodgeDirac g).range.mkQ v := f.apply_symm_apply _
      -- The original range is invariant, so its quotient action uses these same representatives.
      have hRange : (positiveHodgeDirac g).range ≤
          (positiveHodgeDirac g).range.comap (orthogonalSphereOddFormRepresentation r A) := by
        intro a ha
        obtain ⟨b, rfl⟩ := ha
        exact ⟨orthogonalSphereEvenFormRepresentation r A b,
          LinearMap.congr_fun (positiveHodgeDirac_orthogonalSphere_equivariant r A) b⟩
      let qmap := Submodule.mapQ (positiveHodgeDirac g).range (positiveHodgeDirac g).range
        (orthogonalSphereOddFormRepresentation r A) hRange
      change (positiveHodgeDirac g).range.mkQ
        (O.symm (oneCoordinate (detRep.representation A w))).val = _
      rw [hodd]
      exact congrArg qmap hrep
    have hindex := orthogonalSphereDeRhamIndex_eq r oneRep detRep e f he hf
    rw [hindex, hrOdd.neg_one_pow, neg_one_mul]
    rfl

set_option synthInstance.maxHeartbeats 200000 in
-- The extended limit accommodates instance synthesis for the actual harmonic and quotient
-- representations.
set_option maxHeartbeats 1500000 in
-- The extended limit accommodates instance synthesis for the actual harmonic and quotient
-- representations.
/-- The zero-sphere has two actual degree-zero classes and de Rham index two. -/
theorem orthogonalSphereDeRhamIndex_zero : orthogonalSphereDeRhamIndex 0 = 2 := by
  /- The original S0 is the disjoint pair of north and south points. All
  positive-degree forms vanish, so the positive operator has the two-dimensional
  space of zero-forms as kernel and the zero space as quotient-cokernel.
  O(0) fixes each point separately. Evaluation on the two points gives two
  trivial lines; the representation direct-sum relation yields two units.
  No connectedness assumption identifies these two independent values. -/
  classical
  let X := OrthogonalSphere 0
  let g := orthogonalSphereRoundMetric 0
  let G := Matrix.orthogonalGroup (Fin 0) ℝ
  let F := SmoothDifferentialForm (n := 0) X
  let L (p : ℕ) := DirectSum.lof ℂ ℕ F p
  -- Every positive-degree tensor is zero on the actual zero-dimensional tangent space.
  have hhigh (p : ℕ) (hp : p ≠ 0) (u : F p) : u = 0 := by
    let i : Fin p := ⟨0, Nat.pos_of_ne_zero hp⟩
    apply Subtype.ext
    funext x
    apply ContinuousAlternatingMap.ext
    intro v
    apply (u.val x).map_coord_zero i
    exact Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) (v i) 0
  have hcomponent (u : evenHarmonicForms g) :
      smoothFormHodgeLaplacian g 0 (u.val.val 0) = 0 := by
    let proj := DirectSum.component ℂ ℕ F 0
    have hmap : proj.comp (totalFormHodgeLaplacian g) =
        (smoothFormHodgeLaplacian g 0).comp proj := by
      apply DirectSum.linearMap_ext
      intro q
      apply LinearMap.ext
      intro v
      by_cases hq : q = 0
      · subst q
        simp [proj, F, totalFormHodgeLaplacian]
      · simp [proj, F, totalFormHodgeLaplacian, DirectSum.component.of, hq]
    have h := LinearMap.congr_fun hmap u.val.val
    have hu : totalFormHodgeLaplacian g u.val.val = 0 := u.property
    rw [LinearMap.comp_apply, hu, map_zero] at h
    exact h.symm
  -- Projection onto degree zero is a genuine equivalence, without replacing the total carrier.
  let T : evenHarmonicForms g →ₗ[ℂ] harmonicForms g 0 := {
    toFun u := ⟨u.val.val 0, hcomponent u⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  have hT : Function.Bijective T := by
    constructor
    · intro u v h
      apply Subtype.ext
      apply Subtype.ext
      apply DFinsupp.ext
      intro p
      by_cases hp : p = 0
      · subst p
        exact congrArg (fun a : harmonicForms g 0 ↦ a.val) h
      · rw [hhigh p hp (u.val.val p), hhigh p hp (v.val.val p)]
    · intro u
      have heven : L 0 u.val ∈ evenSmoothDifferentialForms (n := 0) (M := X) := by
        intro p hp
        have hp0 : p ≠ 0 := by
          intro h
          subst p
          simp at hp
        simp [L, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne, hp0]
      have hharmonic : totalFormHodgeLaplacian g (L 0 u.val) = 0 := by
        simp [L, F, X, totalFormHodgeLaplacian,
          show smoothFormHodgeLaplacian g 0 u.val = 0 from u.property]
      refine ⟨⟨⟨L 0 u.val, heven⟩, hharmonic⟩, ?_⟩
      apply Subtype.ext
      change (L 0 u.val) 0 = u.val
      simp [L]
  obtain ⟨e₀⟩ := nonempty_deRhamCohomology_zeroSphere_equiv
  let eK : LinearMap.ker (positiveHodgeDirac g) ≃ₗ[ℂ] ℂ × ℂ :=
    (evenHarmonicKernelEquiv g).symm.trans
      ((LinearEquiv.ofBijective T hT).trans ((harmonicDeRhamEquiv g 0).trans e₀))
  -- All odd components vanish, so the exact smooth-range quotient is the zero space.
  have : Subsingleton (oddSmoothDifferentialForms (n := 0) (M := X)) := by
    constructor
    intro u v
    apply Subtype.ext
    apply DFinsupp.ext
    intro p
    by_cases hp : p = 0
    · subst p
      rw [u.property 0 (by decide), v.property 0 (by decide)]
    · rw [hhigh p hp (u.val p), hhigh p hp (v.val p)]
  have : Subsingleton (PositiveHodgeCokernel g) := inferInstance
  let oneRep := FiniteContinuousRepresentation.trivial (G := G)
  let ρ := oneRep.directSum oneRep
  let τ : FiniteContinuousRepresentation G := {
    dimension := 0
    representation := ContRepresentation.trivial ℂ G (Fin 0 → ℂ)
    continuous_action := continuous_snd }
  let e : (Fin ρ.dimension → ℂ) ≃ₗ[ℂ] LinearMap.ker (positiveHodgeDirac g) :=
    (LinearEquiv.finTwoArrow ℂ ℂ).trans eK.symm
  let f : (Fin τ.dimension → ℂ) ≃ₗ[ℂ] PositiveHodgeCokernel g :=
    LinearEquiv.ofSubsingleton (R := ℂ) _ _
  have hgroup (A : G) : A = 1 := by
    apply Subtype.ext
    exact Subsingleton.elim _ _
  have hindex : orthogonalSphereDeRhamIndex 0 =
      finiteRepresentationClass ρ - finiteRepresentationClass τ := by
    apply orthogonalSphereDeRhamIndex_eq 0 ρ τ e f
    · intro A v
      rw [hgroup A]
      simp
    · intro A v
      rw [hgroup A]
      simp
  -- The zero representation has class zero by the original direct-sum relation.
  have hzero : finiteRepresentationClass τ = 0 := by
    have heq : (τ.directSum τ).IsEquivalent τ := by
      have : Subsingleton (Fin (τ.directSum τ).dimension → ℂ) := by
        change Subsingleton (Fin 0 → ℂ)
        infer_instance
      refine ⟨ContRepresentation.Equiv.mk
        ((LinearEquiv.ofSubsingleton (R := ℂ) _ _).toContinuousLinearEquiv) ?_⟩
      intro A
      exact Subsingleton.elim _ _
    have hsum := finiteRepresentationClass_directSum τ τ
    rw [finiteRepresentationClass_eq_of_isEquivalent _ _ heq] at hsum
    exact (add_eq_left.mp hsum.symm)
  rw [hindex, hzero, sub_zero]
  change finiteRepresentationClass (oneRep.directSum oneRep) = 2
  rw [finiteRepresentationClass_directSum]
  change (1 : RepresentationGrothendieckGroup G) + 1 = 2
  norm_num

end AtiyahSinger
