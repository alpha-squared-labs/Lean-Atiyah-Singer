/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.RealOrientationClass
public import AtiyahSinger.Topology.RelativeCapProduct
public import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.RingTheory.Complex
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# The geometrically normalized integral orientation of the complex line

Public module ID: M1716.

C02 / C03. A complex line has its canonical real orientation, with ordered
real basis (1,I). The affine triangle with vertices -1-I, 1, I contains zero
in its interior and has positive determinant 3. Its boundary avoids zero,
so its actual singular chain determines a relative fundamental class.
Evaluation means the existing relative cap product followed by mathlib's
ordinary degree-zero augmentation. Requiring evaluation to equal 1 fixes
the integral cohomological orientation, including its sign.

Milnor--Stasheff, Characteristic Classes, p.96, specifies a positive simplex
class and the cohomology generator pairing with it to give +1. Lemma 14.1,
p.155, uses the canonical complex orientation (1,i). The explicit affine
triangle below realizes these conventions; its coordinate computation is a
project implementation of the source normalization. Hatcher, Algebraic
Topology, section 3.3, supplies the local-orientation and cap background.
Complex-linear equivalences preserve it; arbitrary real-linear equivalences
are deliberately not asserted to do so.

The type ULift ℂ carries precisely the lifted usual topology and complex
vector-space structure. This allows the original same-universe singular
pullbacks to restrict classes to fibers in arbitrary universes. No new
cohomology theory, unspecified generator, or scalar normalization is chosen.
The original triangle cycle is proved below. Its generator normalization and
complex-linear invariance are proved below with the same native classes.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory Convexity Opposite
open scoped Simplicial

universe u

/-- The actual positively oriented affine triangle with vertices -1-I, 1, I. -/
def complexOrientationTriangle :
    (TopCat.toSSet.obj (TopCat.of (ULift.{u} ℂ))).obj (op ⦋2⦌) :=
  ((TopCat.of (ULift.{u} ℂ)).toSSetObjEquiv (op ⦋2⦌)).symm
    ⟨fun t ↦ ULift.up
      (((t.weights 1 : ℝ) : ℂ) - ((t.weights 0 : ℝ) : ℂ) +
        Complex.I * (((t.weights 2 : ℝ) : ℂ) - ((t.weights 0 : ℝ) : ℂ))),
      by fun_prop⟩

/-- The projected singular chain of the fixed positive triangle with coefficient one. -/
def complexOrientationRelativeChain :
    (relativeSingularChains ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0))).X 2 :=
  (relativeSingularChainsProjection ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0))).f 2
    ((TopCat.toSSet.obj (TopCat.of (ULift.{u} ℂ))).ιChainComplex
      (R := singularCoefficient ℤ) complexOrientationTriangle (ULift.up 1))

open CategoryTheory.Limits in
/-- All three boundary edges of the chosen triangle lie in the punctured complex line. -/
theorem complexOrientationRelativeChain_mem_cycles :
    ((relativeSingularChains ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0))).sc 2).g
      complexOrientationRelativeChain = 0 := by
  /- Stage 1: the affine formula takes the three standard vertices to
  -1-I, 1, I. A zero value has barycentric coordinates (1/3,1/3,1/3),
  since its real and imaginary parts force all three coordinates equal.
  Thus no boundary face meets zero, because a face has a zero coordinate.
  Stage 2: the alternating-face differential is a sum of the three
  actual singular edge chains in the punctured line. The original
  relative cokernel projection kills each such edge chain. Its chain
  map identity gives the asserted vanishing in the actual quotient. -/
  classical
  let X := ULift.{u} ℂ
  let A : Set X := Set.ofPred (fun z : X ↦ z ≠ 0)
  let S := TopCat.toSSet.obj (TopCat.of X)
  let σ := complexOrientationTriangle.{u}
  let ρ : (S.chainComplex (singularCoefficient ℤ)).X 1 ⟶
      (relativeSingularChains ℤ A).X 1 := (relativeSingularChainsProjection ℤ A).f 1
  -- A zero affine value has three equal barycentric coordinates, unlike every face.
  have hface (j : Fin 3) (t : StdSimplex ℝ (Fin 2)) :
      (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋1⦌) (S.δ j σ)) t ∈ A := by
    let s : StdSimplex ℝ (Fin 3) := StdSimplex.map j.succAbove t
    have hweight : s.weights j = 0 := by
      exact Finsupp.mapDomain_of_notMem_range t.weights j
        (by rintro ⟨k, hk⟩; exact Fin.succAbove_ne j k hk)
    intro hz
    have hz' : ((s.weights 1 : ℝ) : ℂ) - ((s.weights 0 : ℝ) : ℂ) +
        Complex.I * (((s.weights 2 : ℝ) : ℂ) - ((s.weights 0 : ℝ) : ℂ)) = 0 := by
      exact congrArg ULift.down hz
    have hre := congrArg Complex.re hz'
    have him := congrArg Complex.im hz'
    simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.sub_im, Complex.ofReal_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at hre
    simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.sub_re, Complex.ofReal_re,
      mul_zero, one_mul, sub_zero, zero_add, Complex.zero_im] at him
    have hsum := s.total_of_fintype
    rw [Fin.sum_univ_three] at hsum
    fin_cases j <;> simp only [Fin.reduceFinMk] at hweight <;> linarith
  -- Each actual edge generator factors through the punctured-line subspace.
  have hface_zero (j : Fin 3) :
      ρ
        (S.ιChainComplex (R := singularCoefficient ℤ) (S.δ j σ) (ULift.up 1)) = 0 := by
    let f := TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋1⦌) (S.δ j σ)
    let σA : (TopCat.toSSet.obj (TopCat.of A)).obj (op ⦋1⦌) :=
      (TopCat.toSSetObjEquiv (TopCat.of A) (op ⦋1⦌)).symm
        ⟨fun z ↦ ⟨f z, hface j z⟩, f.continuous.subtype_mk _⟩
    let inc : C(A, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hσ : (TopCat.toSSet.map (TopCat.ofHom inc)).app (op ⦋1⦌) σA = S.δ j σ := by
      apply (TopCat.toSSetObjEquiv (TopCat.of X) (op ⦋1⦌)).injective
      ext z
      rfl
    have hgen : (singularSubspaceChains ℤ A).f 1
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient ℤ) σA (ULift.up 1)) =
        S.ιChainComplex (R := singularCoefficient ℤ) (S.δ j σ) (ULift.up 1) := by
      change ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
        (R := singularCoefficient ℤ) σA ≫
          (SSet.chainComplexMap (TopCat.toSSet.map (TopCat.ofHom inc))
            (singularCoefficient ℤ)).f 1) (ULift.up 1) = _
      rw [SSet.ι_chainComplexMap_f, hσ]
    have hzero := congrArg (fun f ↦ f.f 1
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient ℤ) σA (ULift.up 1)))
      (cokernel.condition (singularSubspaceChains ℤ A))
    change (relativeSingularChainsProjection ℤ A).f 1
      ((singularSubspaceChains ℤ A).f 1
        ((TopCat.toSSet.obj (TopCat.of A)).ιChainComplex
          (R := singularCoefficient ℤ) σA (ULift.up 1))) = 0 at hzero
    rw [hgen] at hzero
    exact hzero
  -- The original chain-map differential is the alternating sum of these same edges.
  have hd : (relativeSingularChains ℤ A).d 2 1
    ((relativeSingularChainsProjection ℤ A).f 2
      (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1))) = 0 := by
    have hcomm := congrArg (fun f ↦ f
      (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1)))
      ((relativeSingularChainsProjection ℤ A).comm 2 1)
    refine hcomm.trans ?_
    change ((S.ιChainComplex (R := singularCoefficient ℤ) σ ≫
      (S.chainComplex (singularCoefficient ℤ)).d 2 1) ≫
        ρ) (ULift.up 1) = 0
    rw [SSet.ιChainComplex_d]
    simp only [Preadditive.sum_comp, Preadditive.zsmul_comp,
      ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply]
    apply Finset.sum_eq_zero
    intro j _
    change ((-1 : ℤ) ^ j.val) •
      ρ (S.ιChainComplex (R := singularCoefficient ℤ) (S.δ j σ) (ULift.up 1)) = 0
    rw [hface_zero]
    exact zsmul_zero ((-1 : ℤ) ^ j.val)
  change (relativeSingularChains ℤ A).dFrom 2 _ = 0
  rw [HomologicalComplex.dFrom_eq (r := show (ComplexShape.down ℕ).Rel 2 1 from rfl),
    ModuleCat.comp_apply]
  change (HomologicalComplex.xNextIso (relativeSingularChains ℤ A) _).inv
    ((relativeSingularChains ℤ A).d 2 1
      ((relativeSingularChainsProjection ℤ A).f 2
        (S.ιChainComplex (R := singularCoefficient ℤ) σ (ULift.up 1)))) = 0
  rw [hd, map_zero]

/-- The relative homology class represented by the specified positive triangle. -/
def complexOrientationCycle :
    relativeSingularHomology ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2 :=
  relativeSingularCycleClass ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2
    ⟨complexOrientationRelativeChain, complexOrientationRelativeChain_mem_cycles⟩

/-- Integral evaluation on the fixed triangle, via the original cap and augmentation maps. -/
def complexOrientationEvaluation
    (a : relativeSingularCohomology ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2) : ℤ :=
  (((TopCat.of (ULift.{u} ℂ)).singularHomology₀ε (singularCoefficient ℤ))
    (relativeSingularCapProduct ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2 0
      a complexOrientationCycle)).down

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The specified complex triangle is precisely the positive real simplex in the basis `(1,I)`. -/
theorem complexOrientationCycle_eq_realOrientationCycle :
    let b := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
    complexOrientationCycle.{u} = realOrientationCycle b b.orientation := by
  let b := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
  have htriangle : complexOrientationTriangle.{u} = realOrientationSimplex b := by
    apply ((TopCat.of (ULift.{u} ℂ)).toSSetObjEquiv (op ⦋2⦌)).injective
    apply ContinuousMap.ext
    intro t
    apply ULift.ext
    simp [complexOrientationTriangle, realOrientationSimplex, b,
      Fin.sum_univ_two, Module.Basis.map_apply, Complex.coe_basisOneI,
      Complex.real_smul, mul_comm]
  change relativeSingularCycleClass ℤ _ 2 _ = relativeSingularCycleClass ℤ _ 2 _
  congr 1
  apply Subtype.ext
  simp [complexOrientationRelativeChain, realOrientationRelativeChain, htriangle]
  rfl


/-- The positive triangle specifies a unique integral local cohomology generator. -/
theorem existsUnique_complexOrientationClass :
    ∃! a : relativeSingularCohomology ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2,
      complexOrientationEvaluation a = 1 := by
  /- The explicit triangle is the actual real simplex in the lifted ordered
  basis `(1,I)`. Its sign is positive. The real integral normalization therefore
  applies to exactly the same relative cycle and the same cap augmentation. -/
  let b := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
  have hcycle : complexOrientationCycle.{u} = realOrientationCycle b b.orientation :=
    complexOrientationCycle_eq_realOrientationCycle
  have heval (a : relativeSingularCohomology ℤ
      (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2) :
      complexOrientationEvaluation a = realOrientationEvaluation b b.orientation a := by
    unfold complexOrientationEvaluation realOrientationEvaluation
    rw [hcycle]
  simpa only [heval] using existsUnique_realOrientationClass b b.orientation

/-- The canonical integral local orientation of the usual complex line, with its positive sign. -/
def complexOrientationClass :
    relativeSingularCohomology ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2 :=
  Classical.choose existsUnique_complexOrientationClass.exists

/-- The canonical orientation evaluates to one on the chosen positive triangle. -/
theorem complexOrientationClass_evaluation :
    complexOrientationEvaluation complexOrientationClass.{u} = 1 := by
  /- The chosen class is the witness of the existence-and-uniqueness
  theorem for precisely this evaluation functional. Its specification
  is the asserted equality with the integer 1. This transports no
  separately chosen orientation or coefficient normalization. -/
  exact (existsUnique_complexOrientationClass).exists.choose_spec

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The normalized integral class freely generates the top relative fiber cohomology. -/
theorem complexOrientationClass_is_generator :
    Function.Bijective (fun a : ℤ ↦ a • complexOrientationClass.{u}) := by
  let E : relativeSingularCohomology ℤ (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)) 2 →+ ℤ :=
    { toFun := complexOrientationEvaluation
      map_zero' := by
        unfold complexOrientationEvaluation
        erw [map_zero, LinearMap.zero_apply, map_zero]
        rfl
      map_add' := by
        intro a a'
        unfold complexOrientationEvaluation
        erw [map_add, LinearMap.add_apply, map_add]
        rfl }
  have hnorm : E (complexOrientationClass) = 1 :=
    complexOrientationClass_evaluation
  -- The unique fiber over one forces the kernel to vanish: translate a kernel element
  -- by the specified class, then apply uniqueness to this same evaluation functional.
  have hinj : Function.Injective E := by
    intro a a' haa'
    have heval : E (a - a' + complexOrientationClass) = 1 := by
      rw [map_add, map_sub, haa', sub_self, zero_add, hnorm]
    have heq := (existsUnique_complexOrientationClass).unique heval hnorm
    exact sub_eq_zero.mp (add_right_cancel (heq.trans (zero_add _).symm))
  constructor
  · -- Evaluation of an integral multiple is its coefficient.
    intro a a' haa'
    have h := congrArg E haa'
    simpa only [map_zsmul, hnorm, smul_eq_mul, mul_one] using h
  · -- Injectivity identifies every class with the multiple given by its evaluation.
    intro a
    refine ⟨E a, hinj ?_⟩
    rw [map_zsmul, hnorm, smul_eq_mul, mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
set_option linter.unusedVariables false in

/-- Every complex-linear equivalence preserves the geometrically normalized local orientation. -/
theorem complexOrientationClass_pullback
    (e : ULift.{u} ℂ ≃L[ℂ] ULift.{u} ℂ) :
    relativeSingularCohomologyPullback ℤ (⟨e, e.continuous⟩ : C(ULift.{u} ℂ, ULift.{u} ℂ))
      (A := (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)))
      (B := (Set.ofPred (fun z : ULift.{u} ℂ ↦ z ≠ 0)))
      (fun z hz he ↦ hz (e.injective (he.trans e.map_zero.symm))) 2
      complexOrientationClass = complexOrientationClass := by
  /- In the lifted ordered basis (1,I), the real determinant of this
  complex-linear automorphism is the squared absolute value of its
  nonzero complex determinant. Positivity preserves the basis orientation.
  Identify complexOrientationClass with realOrientationClass in that
  orientation by evaluating both on the same positive triangle cycle:
  both evaluations are 1, so normalized real-class uniqueness applies.
  Rewrite by this identification and apply realOrientationClass_pullback
  to the same underlying real equivalence and preserved orientation. -/
  let b := Complex.basisOneI.map (ULift.moduleEquiv : ULift.{u} ℂ ≃ₗ[ℝ] ℂ).symm
  let eR := e.restrictScalars ℝ
  have hdet : 0 < LinearMap.det eR.toLinearMap := by
    change 0 < (e.toLinearMap.restrictScalars ℝ).det
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
    exact Complex.normSq_pos.mpr e.toLinearEquiv.isUnit_det'.ne_zero
  have ho : Orientation.map (Fin 2) eR.toLinearEquiv b.orientation = b.orientation := by
    rw [← Module.Basis.orientation_map]
    exact (b.orientation_comp_linearEquiv_eq_iff_det_pos eR.toLinearEquiv).mpr hdet
  have hclass : complexOrientationClass.{u} = realOrientationClass b b.orientation := by
    apply (existsUnique_realOrientationClass b b.orientation).unique
    · have h := complexOrientationClass_evaluation.{u}
      unfold complexOrientationEvaluation at h
      rw [complexOrientationCycle_eq_realOrientationCycle] at h
      exact h
    · exact realOrientationClass_evaluation b b.orientation
  rw [hclass]
  exact realOrientationClass_pullback b b.orientation b b.orientation eR ho

end AtiyahSinger
