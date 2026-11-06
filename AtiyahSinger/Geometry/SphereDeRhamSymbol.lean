/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ExteriorTopology
public import AtiyahSinger.Algebra.OrthogonalComplexification
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-!
# The two hemisphere Koszul homotopy for the sphere de Rham symbol

Public module ID: M1429.

AL02. Atiyah--Singer I, Lemma (3.2), pp.499--500, describes the tangent bundle
using two closed unit balls with transition `(x,v) ↦ (x,hₓ v)` on the equator.
Here `hₓ` is reflection in the real hyperplane perpendicular to `x`. Its complex
extension induces the actual exterior transition. On the two balls the
deformed Koszul differentials are left wedge multiplication by `v - I*s*x`
and `v + I*s*x`. The equatorial base point stays `x`; only the tangent and
exterior fibers are reflected. The formulas below extend to all coordinate
vectors, but the source geometry restricts the base to the closed unit ball,
the transition to its unit sphere, and the homotopy parameter to `[0,1]`.

The complex carrier is the same native `EuclideanSpace ℂ (Fin r)` used by
`orthogonalComplexificationRepresentation`, with coordinatewise inclusion of
the real vectors. Exterior powers are the actual submodules of its exterior
algebra. The range/kernel equality is exactness of this degree-one complex;
it implies exactness at each of its original degrees. At `s=0` the formula is
the real tangent Koszul differential. At `s=1` each ball has precisely one
nonexact fiber, namely `(x,v)=(0,0)`. The reflection family is continuous on
the equator, not across the origin of the ball.

This file supplies the original local complex homotopy and its gluing equation.
The native tangent comparison, global equivariant compact-support K-class,
pole pushforwards and fiber-reversal pullback are separate constructions.
In particular the sphere Hodge index is not used as a
definition of its de Rham symbol. Source footnote 15 omits the differential-
operator factor `I`; our wedge differential follows precisely that convention.
The proofs retain these precise vectors, transitions, actions, and failure loci.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

attribute [local instance] exteriorAlgebraNormedAddCommGroup exteriorAlgebraNormedSpace

set_option maxSynthPendingDepth 25

/-- The two vectors `v - I*s*x` and `v + I*s*x` in the specified complexification.
`atInfinity = false` denotes the zero-pole ball and `true` the infinity-pole ball. -/
def sphereHemisphereKoszulVector (r : ℕ) (atInfinity : Bool) (s : ℝ)
    (x v : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℂ (Fin r) :=
  WithLp.toLp 2 (fun i ↦ (v i : ℂ) +
    (if atInfinity then Complex.I else -Complex.I) * (s : ℂ) * (x i : ℂ))

/-- The actual left-wedge differential in either source hemisphere complex. -/
def sphereHemisphereDifferential (r : ℕ) (atInfinity : Bool) (s : ℝ)
    (x v : EuclideanSpace ℝ (Fin r)) :
    Module.End ℂ (ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r))) :=
  exteriorMultiplication (sphereHemisphereKoszulVector r atInfinity s x v)

/-- The exterior extension of reflection in the complexified equatorial hyperplane.
The construction has an actual inverse given by the same reflection. -/
def sphereEquatorExteriorTransition (r : ℕ) (x : EuclideanSpace ℝ (Fin r)) :
    ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r)) ≃ₐ[ℂ]
      ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r)) :=
  let h := (ℂ ∙ (WithLp.toLp 2 (fun i ↦ (x i : ℂ)) :
    EuclideanSpace ℂ (Fin r)))ᗮ.reflection
  { ExteriorAlgebra.map h.toLinearEquiv.toLinearMap with
    invFun := ExteriorAlgebra.map h.symm.toLinearEquiv.toLinearMap
    left_inv := ExteriorAlgebra.leftInverse_map_iff.mpr h.left_inv
    right_inv := ExteriorAlgebra.leftInverse_map_iff.mpr h.right_inv }

/-- The prescribed family is a continuous complex of the original exterior powers. -/
theorem sphereHemisphereDifferential_properties (r : ℕ) (atInfinity : Bool) :
    (∀ (s : ℝ) (x v : EuclideanSpace ℝ (Fin r)),
      sphereHemisphereDifferential r atInfinity s x v ^ 2 = 0) ∧
    (∀ (s : ℝ) (x v : EuclideanSpace ℝ (Fin r)) (p : ℕ)
        (w : ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r))),
      w ∈ ExteriorAlgebra.exteriorPower ℂ p (EuclideanSpace ℂ (Fin r)) →
      sphereHemisphereDifferential r atInfinity s x v w ∈
        ExteriorAlgebra.exteriorPower ℂ (p + 1) (EuclideanSpace ℂ (Fin r))) ∧
    Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin r) ×
        EuclideanSpace ℝ (Fin r) × ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r)) ↦
      sphereHemisphereDifferential r atInfinity z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let C := EuclideanSpace ℂ (Fin r)
  let B := ExteriorAlgebra ℂ C
  refine ⟨?_, ?_, ?_⟩
  · -- The original exterior generator has square zero, including at rank zero.
    intro s x v
    exact exteriorMultiplication_sq (sphereHemisphereKoszulVector r atInfinity s x v)
  · -- Left wedge multiplication adds exactly one original vector factor.
    intro s x v p w hw
    change ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r atInfinity s x v) * w ∈
      (LinearMap.range (ExteriorAlgebra.ι ℂ)) ^ (p + 1)
    rw [pow_succ']
    exact Submodule.mul_mem_mul ⟨sphereHemisphereKoszulVector r atInfinity s x v, rfl⟩ hw
  · -- Evaluate the continuous linear family of wedge operators on the same exterior algebra.
    let wedge : C →ₗ[ℂ] B →L[ℂ] B :=
      LinearMap.toContinuousLinearMap.toLinearMap.comp
        ((Algebra.lmul ℂ B).toLinearMap.comp (ExteriorAlgebra.ι ℂ))
    have hvector : Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin r) ×
        EuclideanSpace ℝ (Fin r) × B ↦
        sphereHemisphereKoszulVector r atInfinity z.1 z.2.1 z.2.2.1) := by
      apply (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
      apply continuous_pi
      intro j
      change Continuous (fun z : ℝ × EuclideanSpace ℝ (Fin r) ×
        EuclideanSpace ℝ (Fin r) × B ↦
        (z.2.2.1 j : ℂ) + (if atInfinity then Complex.I else -Complex.I) *
          (z.1 : ℂ) * (z.2.1 j : ℂ))
      fun_prop
    exact (wedge.continuous_of_finiteDimensional.comp hvector).clm_apply
      continuous_snd.snd.snd

/-- The source homotopy is equivariant for the original real orthogonal action. -/
theorem sphereHemisphereDifferential_equivariant (r : ℕ) (atInfinity : Bool)
    (s : ℝ) (x v : EuclideanSpace ℝ (Fin r))
    (A : Matrix.orthogonalGroup (Fin r) ℝ) :
    let exteriorA :=
      (ExteriorAlgebra.map (orthogonalComplexificationRepresentation r A).toLinearMap).toLinearMap
    (sphereHemisphereDifferential r atInfinity s
      (orthogonalEuclideanIsometry r A x) (orthogonalEuclideanIsometry r A v)).comp exteriorA =
      exteriorA.comp (sphereHemisphereDifferential r atInfinity s x v) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let inc (w : V) : C := WithLp.toLp 2 (fun j ↦ (w j : ℂ))
  let L := orthogonalComplexificationRepresentation r A
  -- The complexified action has the same real matrix entries on the included real space.
  have hinc (w : V) : L (inc w) = inc (orthogonalEuclideanIsometry r A w) := by
    ext j
    change (∑ k, (A.val j k : ℂ) * (w k : ℂ)) = (∑ k, A.val j k * w k : ℝ)
    simp
  have hformula (x v : V) : sphereHemisphereKoszulVector r atInfinity s x v =
      inc v + ((if atInfinity then Complex.I else -Complex.I) * (s : ℂ)) • inc x := by
    ext j
    rfl
  -- Complex linearity preserves the actual deformation parameter and its hemisphere sign.
  have hvector : sphereHemisphereKoszulVector r atInfinity s
      (orthogonalEuclideanIsometry r A x) (orthogonalEuclideanIsometry r A v) =
      L (sphereHemisphereKoszulVector r atInfinity s x v) := by
    rw [hformula, hformula, map_add, map_smul, hinc, hinc]
  -- Exterior functoriality gives the equality for every original exterior vector.
  apply LinearMap.ext
  intro a
  change ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r atInfinity s
      (orthogonalEuclideanIsometry r A x) (orthogonalEuclideanIsometry r A v)) *
      ExteriorAlgebra.map L.toLinearMap a =
    ExteriorAlgebra.map L.toLinearMap
      (ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r atInfinity s x v) * a)
  rw [map_mul, ExteriorAlgebra.map_apply_ι, hvector]
  rfl

/-- The actual real-reflection transition is continuous on the equator and O(r)-covariant. -/
theorem sphereEquatorExteriorTransition_properties (r : ℕ) :
    (∀ x v : EuclideanSpace ℝ (Fin r),
      sphereEquatorExteriorTransition r x
          (ExteriorAlgebra.ι ℂ (WithLp.toLp 2 (fun i ↦ (v i : ℂ)) :
            EuclideanSpace ℂ (Fin r))) =
        ExteriorAlgebra.ι ℂ
          (WithLp.toLp 2 (fun i ↦ (((ℝ ∙ x)ᗮ.reflection v) i : ℂ)) :
            EuclideanSpace ℂ (Fin r))) ∧
    (Continuous (fun z : Metric.sphere (0 : EuclideanSpace ℝ (Fin r)) 1 ×
        ExteriorAlgebra ℂ (EuclideanSpace ℂ (Fin r)) ↦
      sphereEquatorExteriorTransition r z.1.val z.2)) ∧
    ∀ (x : EuclideanSpace ℝ (Fin r)) (A : Matrix.orthogonalGroup (Fin r) ℝ),
      let exteriorA :=
        (ExteriorAlgebra.map (orthogonalComplexificationRepresentation r A).toLinearMap).toLinearMap
      (sphereEquatorExteriorTransition r (orthogonalEuclideanIsometry r A x)).toLinearMap.comp
          exteriorA =
        exteriorA.comp (sphereEquatorExteriorTransition r x).toLinearMap := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let inc : V →ₗ[ℝ] C :=
    { toFun := fun w ↦ WithLp.toLp 2 (fun j ↦ (w j : ℂ))
      map_add' := by
        intro a b
        ext j
        change ((a j + b j : ℝ) : ℂ) = (a j : ℂ) + (b j : ℂ)
        exact Complex.ofReal_add _ _
      map_smul' := by
        intro t a
        ext j
        change ((t * a j : ℝ) : ℂ) = t • (a j : ℂ)
        simp [Complex.real_smul] }
  have hinner (a b : V) : inner ℂ (inc a) (inc b) = (inner ℝ a b : ℂ) := by
    have hreal : inner ℝ a b = ∑ j : Fin r, b j * a j := PiLp.inner_apply a b
    have hcomplex : inner ℂ (inc a) (inc b) =
        ∑ j : Fin r, inc b j * star (inc a j) := PiLp.inner_apply (inc a) (inc b)
    rw [hreal, hcomplex]
    simp [inc]
  have hnorm (a : V) : (‖inc a‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 := by
    calc
      _ = inner ℂ (inc a) (inc a) := (inner_self_eq_norm_sq_to_K (inc a)).symm
      _ = (inner ℝ a a : ℂ) := hinner a a
      _ = (‖a‖ : ℂ) ^ 2 := by rw [real_inner_self_eq_norm_sq, Complex.ofReal_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro x v
    change ExteriorAlgebra.map (ℂ ∙ inc x)ᗮ.reflection.toLinearEquiv.toLinearMap
      (ExteriorAlgebra.ι ℂ (inc v)) = ExteriorAlgebra.ι ℂ (inc ((ℝ ∙ x)ᗮ.reflection v))
    rw [ExteriorAlgebra.map_apply_ι]
    congr 1
    change (ℂ ∙ inc x)ᗮ.reflection (inc v) = inc ((ℝ ∙ x)ᗮ.reflection v)
    rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
      Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
    simp only [map_neg, map_sub, map_smul, map_nsmul]
    rw [hinner]
    erw [hnorm]
    simp only [two_smul]
    congr 2
    ext j
    change ((inner ℝ x v : ℂ) / (‖x‖ : ℂ) ^ 2) * (x j : ℂ) +
        ((inner ℝ x v : ℂ) / (‖x‖ : ℂ) ^ 2) * (x j : ℂ) =
      ((inner ℝ x v / ‖x‖ ^ 2) • (x j : ℂ)) +
        ((inner ℝ x v / ‖x‖ ^ 2) • (x j : ℂ))
    simp [Complex.real_smul]
  · let S := Metric.sphere (0 : V) 1
    let B := ExteriorAlgebra ℂ C
    let R (x : S) := (ℂ ∙ inc x.val)ᗮ.reflection
    let F (x : S) : B →ₐ[ℂ] B := ExteriorAlgebra.map (R x).toLinearEquiv.toLinearMap
    have hinc : Continuous inc := (PiLp.continuous_toLp 2 (fun _ : Fin r ↦ ℂ)).comp
      (continuous_pi fun j ↦ Complex.continuous_ofReal.comp
        (PiLp.continuous_apply 2 (fun _ : Fin r ↦ ℝ) j))
    have hn (x : S) : (‖inc x.val‖ : ℂ) ^ 2 = 1 := by
      rw [hnorm]
      have hx : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
      rw [hx]
      norm_num
    -- On the equator the reflection denominator is one; no continuity at the origin is claimed.
    have hRcont (a : C) : Continuous (fun x : S ↦ R x a) := by
      have hformula (x : S) : R x a =
          -(2 • (inner ℂ (inc x.val) a) • inc x.val - a) := by
        rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
        erw [hn x]
        rw [div_one]
      simp_rw [hformula]
      fun_prop
    -- Algebra induction gives each orbit, then finite dimensionality gives joint evaluation.
    let : IsModuleTopology ℂ B := isModuleTopologyOfFiniteDimensional
    let : IsTopologicalRing B := IsModuleTopology.isTopologicalRing ℂ B
    have horbit (a : B) : Continuous (fun x : S ↦ F x a) := by
      induction a using ExteriorAlgebra.induction with
      | algebraMap c =>
        convert continuous_const (y := algebraMap ℂ B c) using 1
        ext x
        exact (F x).commutes c
      | ι v =>
        convert (ExteriorAlgebra.ι ℂ (M := C)).continuous_of_finiteDimensional.comp
          (hRcont v) using 1
        ext x
        exact ExteriorAlgebra.map_apply_ι (R x).toLinearEquiv.toLinearMap v
      | mul a b ha hb => simpa only [map_mul] using ha.fun_mul hb
      | add a b ha hb => simpa only [map_add] using ha.fun_add hb
    have hfamily : Continuous (fun x : S ↦ (F x).toLinearMap.toContinuousLinearMap) := by
      apply continuous_clm_apply.mpr
      exact horbit
    exact (hfamily.comp continuous_fst).clm_apply continuous_snd
  · intro x A
    let f := (orthogonalComplexificationRepresentation r A).toLinearMap
    let j (v : EuclideanSpace ℝ (Fin r)) : EuclideanSpace ℂ (Fin r) :=
      WithLp.toLp 2 (fun i ↦ (v i : ℂ))
    have hreal (v : EuclideanSpace ℝ (Fin r)) :
        f (j v) = j (orthogonalEuclideanIsometry r A v) := by
      ext i
      change (∑ k, (A.val i k : ℂ) * (v k : ℂ)) = ((∑ k, A.val i k * v k : ℝ) : ℂ)
      simp
    have hinner (v w : EuclideanSpace ℂ (Fin r)) :
        inner ℂ (f v) (f w) = inner ℂ v w := orthogonalComplexification_unitary r A v w
    have hnorm (v : EuclideanSpace ℂ (Fin r)) : ‖f v‖ = ‖v‖ :=
      (f.isometryOfInner hinner).norm_map v
    -- The actual unitary map carries the explicit hyperplane reflection formula.
    have hreflect (v w : EuclideanSpace ℂ (Fin r)) :
        (ℂ ∙ f v)ᗮ.reflection (f w) = f ((ℂ ∙ v)ᗮ.reflection w) := by
      simp only [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply,
        hinner, hnorm, map_neg, map_sub]
      simp only [map_nsmul, f.map_smul]
    let hx := (ℂ ∙ j x)ᗮ.reflection.toLinearEquiv.toLinearMap
    let hy := (ℂ ∙ j (orthogonalEuclideanIsometry r A x))ᗮ.reflection.toLinearEquiv.toLinearMap
    have hlinear : hy.comp f = f.comp hx := by
      apply LinearMap.ext
      intro w
      change (ℂ ∙ j (orthogonalEuclideanIsometry r A x))ᗮ.reflection (f w) =
        f ((ℂ ∙ j x)ᗮ.reflection w)
      rw [← hreal]
      exact hreflect (j x) w
    -- Exterior functoriality retains the same real-matrix action and transition.
    have h := congrArg (fun g ↦ ExteriorAlgebra.map g) hlinear
    rw [← ExteriorAlgebra.map_comp_map, ← ExteriorAlgebra.map_comp_map] at h
    apply LinearMap.ext
    intro w
    exact congrArg (fun g ↦ g w) h

/-- The two actual Koszul differentials agree under the source equatorial transition. -/
theorem sphereHemisphereDifferential_gluing (r : ℕ) (s : ℝ)
    (x v : EuclideanSpace ℝ (Fin r)) (hx : ‖x‖ = 1) :
    (sphereEquatorExteriorTransition r x).toLinearMap.comp
        (sphereHemisphereDifferential r false s x v) =
      (sphereHemisphereDifferential r true s x ((ℝ ∙ x)ᗮ.reflection v)).comp
        (sphereEquatorExteriorTransition r x).toLinearMap := by
  -- The source equator excludes the origin, where no gluing chart is being asserted.
  by_cases hzero : x = 0
  · rw [hzero, norm_zero] at hx
    norm_num at hx
  · let V := EuclideanSpace ℝ (Fin r)
    let C := EuclideanSpace ℂ (Fin r)
    let inc (w : V) : C := WithLp.toLp 2 (fun j ↦ (w j : ℂ))
    let F := sphereEquatorExteriorTransition r x
    have hformula (b : Bool) (w : V) : sphereHemisphereKoszulVector r b s x w =
        inc w + ((if b then Complex.I else -Complex.I) * (s : ℂ)) • inc x := by
      ext j
      rfl
    have hF (w : V) : F (ExteriorAlgebra.ι ℂ (inc w)) =
        ExteriorAlgebra.ι ℂ (inc ((ℝ ∙ x)ᗮ.reflection w)) :=
      (sphereEquatorExteriorTransition_properties r).1 x w
    -- The same reflection negates its defining real vector.
    have hxF : F (ExteriorAlgebra.ι ℂ (inc x)) = -ExteriorAlgebra.ι ℂ (inc x) := by
      rw [hF, Submodule.reflection_orthogonalComplement_singleton_eq_neg]
      have hneg : inc (-x) = -inc x := by
        ext j
        change ((-x j : ℝ) : ℂ) = -(x j : ℂ)
        exact Complex.ofReal_neg _
      rw [hneg, map_neg]
    have hvector : F (ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r false s x v)) =
        ExteriorAlgebra.ι ℂ
          (sphereHemisphereKoszulVector r true s x ((ℝ ∙ x)ᗮ.reflection v)) := by
      rw [hformula, hformula]
      simp only [Bool.false_eq_true, ↓reduceIte, map_add, map_smul]
      rw [hF, hxF]
      simp
    -- Intertwine left wedge multiplication, retaining the original equatorial base.
    apply LinearMap.ext
    intro a
    change F (ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r false s x v) * a) =
      ExteriorAlgebra.ι ℂ (sphereHemisphereKoszulVector r true s x ((ℝ ∙ x)ᗮ.reflection v)) * F a
    rw [map_mul, hvector]

/-- Exactness of the prescribed complex, with its precise parameter-dependent failure locus. -/
theorem sphereHemisphereDifferential_exact_iff (r : ℕ) (atInfinity : Bool)
    (s : ℝ) (x v : EuclideanSpace ℝ (Fin r)) :
    LinearMap.range (sphereHemisphereDifferential r atInfinity s x v) =
        LinearMap.ker (sphereHemisphereDifferential r atInfinity s x v) ↔
      v ≠ 0 ∨ (s ≠ 0 ∧ x ≠ 0) := by
  let V := EuclideanSpace ℝ (Fin r)
  let C := EuclideanSpace ℂ (Fin r)
  let B := ExteriorAlgebra ℂ C
  -- A nonzero vector gives the contraction homotopy; at zero the scalar unit obstructs exactness.
  have hexact (w : C) : LinearMap.range (exteriorMultiplication w) =
      LinearMap.ker (exteriorMultiplication w) ↔ w ≠ 0 := by
    constructor
    · intro h hw
      subst w
      have hOne : (1 : B) ∈ LinearMap.range (exteriorMultiplication (0 : C)) := by
        rw [h]
        change exteriorMultiplication (0 : C) 1 = 0
        simp [exteriorMultiplication]
      obtain ⟨a, ha⟩ := hOne
      simp [exteriorMultiplication] at ha
    · intro hw
      have hnorm : (‖w‖ ^ 2 : ℂ) ≠ 0 :=
        pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw))
      apply le_antisymm
      · rintro a ⟨b, rfl⟩
        change exteriorMultiplication w (exteriorMultiplication w b) = 0
        have h := congrArg (fun f : Module.End ℂ B ↦ f b) (exteriorMultiplication_sq w)
        exact h
      · intro a ha
        have h := congrArg (fun f : Module.End ℂ B ↦ f a)
          (exteriorMultiplication_contraction_add w)
        change exteriorMultiplication w (contraction w a) +
          contraction w (exteriorMultiplication w a) = (‖w‖ ^ 2 : ℂ) • a at h
        have hz : exteriorMultiplication w a = 0 := ha
        rw [hz, map_zero, add_zero] at h
        refine ⟨(‖w‖ ^ 2 : ℂ)⁻¹ • contraction w a, ?_⟩
        rw [map_smul, h, smul_smul, inv_mul_cancel₀ hnorm, one_smul]
  -- Real and imaginary coordinates identify the precise parameter-dependent zero locus.
  have hzero : sphereHemisphereKoszulVector r atInfinity s x v = 0 ↔
      v = 0 ∧ s • x = 0 := by
    constructor
    · intro h
      constructor
      · ext j
        have hj := congrArg (fun w : C ↦ (w j).re) h
        cases atInfinity <;> simpa [sphereHemisphereKoszulVector] using hj
      · ext j
        have hj := congrArg (fun w : C ↦ (w j).im) h
        cases atInfinity <;> simpa [sphereHemisphereKoszulVector] using hj
    · rintro ⟨rfl, hs⟩
      ext j
      have hj : s * x j = 0 := congrArg (fun w : V ↦ w j) hs
      apply Complex.ext
      · cases atInfinity <;> simp [sphereHemisphereKoszulVector]
      · cases atInfinity <;> simp [sphereHemisphereKoszulVector, hj]
  change LinearMap.range (exteriorMultiplication
    (sphereHemisphereKoszulVector r atInfinity s x v)) =
    LinearMap.ker (exteriorMultiplication
      (sphereHemisphereKoszulVector r atInfinity s x v)) ↔ _
  rw [hexact]
  rw [ne_eq, hzero, smul_eq_zero]
  tauto

end AtiyahSinger
