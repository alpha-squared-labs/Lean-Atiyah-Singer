/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.RepresentationRing
public import AtiyahSinger.Analysis.EquivariantFredholmIndex
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Tensoring equivariant Fredholm operators with finite representations

Public module ID: M0531.

For a finite representation on Fin n → ℂ and a normed representation on E,
the native normed space Fin n → E models their genuine algebraic tensor
product. Its action mixes coordinates using the original finite representation
matrix, while applying the original E action in each summand. Thus the action
retains the representation itself, not merely its dimension.

The operator 1 ⊗ T is the actual coordinatewise continuous linear map. Its
kernel and quotient-cokernel are tensors of the original kernel and quotient,
which gives multiplication of the full representation-valued index. No unitary
action, inner product on a supremum norm, group compactness or completeness is
required. The finite product includes n = 0 and independent source and target
universes. The tensor action, intertwiner identities, and representation-valued index formula below
are proved for these original objects and native norms.

Source boundary: the tensor representation ring and equivariant Fredholm index
are from SG III.9, printed pp.211--213. The coordinate construction and tensor
index compatibility below spell out the standard interaction of these objects;
no additional numbered tensor lemma is attributed to that passage.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option linter.unusedSectionVars false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open ContinuousLinearMap
open scoped TensorProduct

/-- Actual scalar tensor coordinates, with the finite representation factor on the left. -/
def finiteTensorCoordinates (n : ℕ) (E : Type*) [AddCommMonoid E] [Module ℂ E] :
    ((Fin n → ℂ) ⊗[ℂ] E) ≃ₗ[ℂ] (Fin n → E) :=
  (TensorProduct.comm ℂ (Fin n → ℂ) E).trans
    (TensorProduct.piScalarRight ℂ ℂ E (Fin n))

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The actual matrix-mixed tensor action operator on the native finite normed product. -/
def finiteTensorActionOperator (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) (g : G) :
    (Fin ρ.dimension → E) →L[ℂ] (Fin ρ.dimension → E) :=
  ContinuousLinearMap.pi fun i ↦
    ∑ j : Fin ρ.dimension,
      (ρ.representation g (Pi.single j 1) i) •
        ((σ g).comp (ContinuousLinearMap.proj j))

/-- The matrix-mixed operators satisfy the group-action identities on the same finite product. -/
theorem finiteTensorAction_laws (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) :
    finiteTensorActionOperator ρ σ 1 = 1 ∧
      ∀ g h : G, finiteTensorActionOperator ρ σ (g * h) =
        finiteTensorActionOperator ρ σ g * finiteTensorActionOperator ρ σ h := by
  /- Stage 1: at the identity, the finite representation matrix is the identity
  and σ(1) is the identity operator, so each output coordinate is its input.
  Stage 2: compose the displayed finite sums. Linearity moves scalar coefficients
  through σ(g); the matrix multiplication formula for ρ(gh) and the action law
  σ(gh)=σ(g)σ(h) identify the result with the displayed operator at gh.
  Finite empty sums also give the unique operator on the zero product.
-/
  classical
  -- Expand each finite vector in the original standard basis.
  have hmatrix (g : G) (v : Fin ρ.dimension → ℂ) (i : Fin ρ.dimension) :
      ρ.representation g v i =
        ∑ j : Fin ρ.dimension, ρ.representation g (Pi.single j 1) i * v j := by
    have hv : v = ∑ j : Fin ρ.dimension, v j • Pi.single j 1 := by
      ext k
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  constructor
  · -- Identity matrix coefficients collapse the same finite coordinate sum.
    ext x i
    simp [finiteTensorActionOperator, Pi.single_apply]
  · -- Matrix multiplication and the original action law give the composite action.
    intro g h
    ext x i
    simp only [finiteTensorActionOperator, ContinuousLinearMap.pi_apply,
      sum_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      mul_apply_eq_comp]
    rw [map_mul, map_mul]
    change (∑ j, ρ.representation g (ρ.representation h (Pi.single j 1)) i •
      σ g (σ h (x j))) =
      ∑ j, ρ.representation g (Pi.single j 1) i •
        σ g (∑ k, ρ.representation h (Pi.single k 1) j • σ h (x k))
    have hcoeff (j : Fin ρ.dimension) :
        ρ.representation g (ρ.representation h (Pi.single j 1)) i =
          ∑ k, ρ.representation g (Pi.single k 1) i *
            ρ.representation h (Pi.single j 1) k :=
      hmatrix g (ρ.representation h (Pi.single j 1)) i
    simp_rw [hcoeff, Finset.sum_smul, map_sum, map_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]

/-- The tensor representation using the actual finite matrix coefficients and original action. -/
def finiteTensorRepresentation (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) : ContRepresentation ℂ G (Fin ρ.dimension → E) :=
  .ofMonoidHom
    { toFun := finiteTensorActionOperator ρ σ
      map_one' := (finiteTensorAction_laws ρ σ).1
      map_mul' := (finiteTensorAction_laws ρ σ).2 }

/-- Joint continuity of the genuine tensor action follows from both original joint actions. -/
theorem continuous_finiteTensorRepresentation (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E)
    (hσ : Continuous (fun p : G × E ↦ σ p.1 p.2)) :
    Continuous (fun p : G × (Fin ρ.dimension → E) ↦
      finiteTensorRepresentation ρ σ p.1 p.2) := by
  /- Stage 1: evaluating ρ's jointly continuous action on each fixed coordinate
  vector makes every matrix coefficient continuous in g. For each j the map
  (g,x) ↦ σ(g)(x j) is continuous by hσ and continuity of coordinate projection.
  Stage 2: multiply these functions by the same scalar coefficients, sum over
  the finite index set and assemble the output coordinates. The native finite
  product topology is the topology of its supremum norm; no operator-norm
  continuity of σ as a function of the group element is needed. -/
  -- Each matrix coefficient is continuous in the same group parameter.
  apply continuous_pi
  intro i
  change Continuous (fun p : G × (Fin ρ.dimension → E) ↦
    finiteTensorActionOperator ρ σ p.1 p.2 i)
  simp only [finiteTensorActionOperator, ContinuousLinearMap.pi_apply, sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  apply continuous_finsetSum
  intro j _
  apply Continuous.smul
  · exact (continuous_apply i).comp
      (ρ.continuous_action.comp (continuous_fst.prodMk continuous_const))
  · exact hσ.comp (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))

/-- The mixed-coordinate action is precisely the tensor action on every genuine pure tensor. -/
theorem finiteTensorRepresentation_tmul (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) (g : G) (v : Fin ρ.dimension → ℂ) (x : E) :
    finiteTensorRepresentation ρ σ g
        (finiteTensorCoordinates ρ.dimension E (v ⊗ₜ[ℂ] x)) =
      finiteTensorCoordinates ρ.dimension E (ρ.representation g v ⊗ₜ[ℂ] σ g x) := by
  /- The actual scalar tensor coordinates send v ⊗ x to (i ↦ v i • x).
  Substitute this vector in the displayed finite sum. Complex linearity of
  σ(g) and expansion of v in the standard basis show that coordinate i is
  (ρ(g)v)i • σ(g)x. These are exactly the coordinates on the right. -/
  classical
  -- Pure tensors use precisely the scalar coordinates of the original equivalence.
  ext i
  change finiteTensorActionOperator ρ σ g
    (finiteTensorCoordinates ρ.dimension E (v ⊗ₜ[ℂ] x)) i = _
  simp only [
    finiteTensorActionOperator, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    finiteTensorCoordinates, LinearEquiv.trans_apply, TensorProduct.comm_tmul,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    map_smul, smul_smul]
  -- Expand the finite representation input in the same standard basis.
  have hv : v = ∑ j : Fin ρ.dimension, v j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  conv_rhs => rw [hv]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm]

/-- The genuine operator 1 ⊗ T in finite tensor coordinates is coordinatewise application of T. -/
def finiteTensorOperator (n : ℕ) (T : E →L[ℂ] F) :
    (Fin n → E) →L[ℂ] (Fin n → F) :=
  ContinuousLinearMap.piMap (fun _ : Fin n ↦ T)

/-- The coordinatewise operator agrees with the actual algebraic tensor operator on pure tensors. -/
theorem finiteTensorOperator_tmul (n : ℕ) (T : E →L[ℂ] F)
    (v : Fin n → ℂ) (x : E) :
    finiteTensorOperator n T (finiteTensorCoordinates n E (v ⊗ₜ[ℂ] x)) =
      finiteTensorCoordinates n F (v ⊗ₜ[ℂ] T x) := by
  /- In the same scalar tensor coordinates, the input has coordinate v i • x.
  Apply T coordinatewise and use complex linearity to obtain v i • T x,
  precisely the forward coordinates of v ⊗ T x. No unrelated tensor map or
  change of norm is inserted between the displayed source and target spaces. -/
  -- The original tensor coordinates and the same continuous map give the formula.
  ext i
  simp [finiteTensorOperator, finiteTensorCoordinates, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]

/-- Tensoring an actual intertwiner with the identity preserves its full equivariance. -/
theorem finiteTensorOperator_intertwines (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) (τ : ContRepresentation ℂ G F)
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (σ g) = (τ g).comp T) :
    ∀ g : G, (finiteTensorOperator ρ.dimension T).comp (finiteTensorRepresentation ρ σ g) =
      (finiteTensorRepresentation ρ τ g).comp (finiteTensorOperator ρ.dimension T) := by
  /- In each output coordinate, linearity moves T through the finite scalar
  sum. The original intertwining equation changes T(σ(g)(x j)) into
  τ(g)(T(x j)). The same matrix coefficient of ρ(g) appears on both sides,
  so the resulting coordinates agree. No diagonalization or invariant metric
  is needed for either the finite representation or the normed representations. -/
  -- Move the actual intertwiner through each finite scalar-weighted sum.
  intro g
  ext x i
  have hintertwine (y : E) : T (σ g y) = τ g (T y) :=
    congrArg (fun A : E →L[ℂ] F ↦ A y) (hTg g)
  change T (finiteTensorActionOperator ρ σ g x i) =
    finiteTensorActionOperator ρ τ g (fun j ↦ T (x j)) i
  simp [finiteTensorActionOperator, hintertwine]

/-- Tensoring a Fredholm operator multiplies its full index by the finite representation class. -/
theorem equivariantFredholmIndex_finiteTensor (ρ : FiniteContinuousRepresentation G)
    (σ : ContRepresentation ℂ G E) (τ : ContRepresentation ℂ G F)
    (hσ : Continuous (fun p : G × E ↦ σ p.1 p.2))
    (hτ : Continuous (fun p : G × F ↦ τ p.1 p.2))
    (T : E →L[ℂ] F) (hTg : ∀ g : G, T.comp (σ g) = (τ g).comp T)
    (hT : T.IsFredholm) :
    ∃ hTensor : (finiteTensorOperator ρ.dimension T).IsFredholm,
      equivariantFredholmIndex (finiteTensorRepresentation ρ σ)
          (finiteTensorRepresentation ρ τ)
          (continuous_finiteTensorRepresentation ρ σ hσ)
          (continuous_finiteTensorRepresentation ρ τ hτ)
          (finiteTensorOperator ρ.dimension T)
          (finiteTensorOperator_intertwines ρ σ τ T hTg) hTensor =
        finiteRepresentationClass ρ * equivariantFredholmIndex σ τ hσ hτ T hTg hT := by
  /- Stage 1: tensor an original continuous quasi-inverse coordinatewise. Each
  of its two errors factors through a finite product of the corresponding
  original finite-dimensional error range. The continuous quasi-inverse criterion
  gives Fredholmness of this very operator in the native norm, without completeness
  of either carrier. Its finite kernel and quotient-cokernel then identify with
  Fin n → ker(T) and Fin n → (F/range(T)), using the original quotient maps.
  Stage 2: the kernel and quotient identifications intertwine the matrix-mixed
  actions, since the scalar coefficients are exactly those of the same ρ(g).
  By the pure-tensor formulas these are the actual tensor representations
  ρ ⊗ ker(T) and ρ ⊗ coker(T), not just spaces of the corresponding dimensions.
  Choose finite coordinates on the original kernel and quotient, and compare
  their tensor coordinates with the ring's fixed finite product coordinates.
  The resulting actual equivariant continuous equivalences identify their
  classes with finiteRepresentationClass ρ times the original respective classes.
  Stage 3: substitute these two equalities in the actual kernel-minus-quotient
  definition and distribute the same representation-ring product over subtraction.
  No invariant splitting of a nonsplit exact sequence is used. If n=0, the
  products are zero spaces and both sides are the zero representation class. -/
  classical
  -- Tensor a continuous quasi-inverse; each defect factors through a finite product of ranges.
  have hTensor : (finiteTensorOperator ρ.dimension T).IsFredholm := by
    obtain ⟨S, hS⟩ := hT.exists_isQuasiInverse
    apply ContinuousLinearMap.IsFredholm.of_isQuasiInverse
      (v := finiteTensorOperator ρ.dimension S)
    constructor
    · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
      have hd := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.1
      let d := S.toLinearMap.comp T.toLinearMap - LinearMap.id
      let : FiniteDimensional ℂ d.range := Module.Finite.of_fg hd
      let a := LinearMap.piMap (fun _ : Fin ρ.dimension ↦ d.rangeRestrict)
      let b := LinearMap.piMap (fun _ : Fin ρ.dimension ↦ d.range.subtype)
      have hf : (b.comp a).HasFiniteRange :=
        (LinearMap.HasFiniteRange.of_finite_dom (f := b)).comp_right a
      exact hf
    · apply LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mpr
      have hd := LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange.mp hS.2
      let d := T.toLinearMap.comp S.toLinearMap - LinearMap.id
      let : FiniteDimensional ℂ d.range := Module.Finite.of_fg hd
      let a := LinearMap.piMap (fun _ : Fin ρ.dimension ↦ d.rangeRestrict)
      let b := LinearMap.piMap (fun _ : Fin ρ.dimension ↦ d.range.subtype)
      have hf : (b.comp a).HasFiniteRange :=
        (LinearMap.HasFiniteRange.of_finite_dom (f := b)).comp_right a
      exact hf
  refine ⟨hTensor, ?_⟩
  -- Use the native finite-dimensional kernel and quotient norms of these same operators.
  let U := finiteTensorOperator ρ.dimension T
  let σ' := finiteTensorRepresentation ρ σ
  let τ' := finiteTensorRepresentation ρ τ
  let hUg := finiteTensorOperator_intertwines ρ σ τ T hTg
  let : FiniteDimensional ℂ T.ker := hT.finite_ker
  let : FiniteDimensional ℂ (F ⧸ T.range) := hT.finite_coker
  let : IsClosed (T.range : Set F) := hT.isClosed_range
  let : FiniteDimensional ℂ U.ker := hTensor.finite_ker
  let : FiniteDimensional ℂ ((Fin ρ.dimension → F) ⧸ U.range) := hTensor.finite_coker
  let : IsClosed (U.range : Set (Fin ρ.dimension → F)) := hTensor.isClosed_range
  let κ := equivariantKernelRepresentation σ τ T hTg
  let χ := equivariantCokernelRepresentation σ τ T hTg
  let hκ := continuous_equivariantKernelRepresentation σ τ T hTg hσ
  let hχ := continuous_equivariantCokernelRepresentation σ τ T hTg hτ
  -- Restrict each coordinate to the original kernel, retaining the same matrix coefficients.
  let k : U.ker ≃ₗ[ℂ] (Fin ρ.dimension → T.ker) :=
    { toFun := fun x i ↦ ⟨x.val i, congrFun x.property i⟩
      invFun := fun x ↦ ⟨fun i ↦ (x i).val, funext (fun i ↦ (x i).property)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hk : ContRepresentation.Equiv
      (equivariantKernelRepresentation σ' τ' U hUg)
      (finiteTensorRepresentation ρ κ) := by
    refine ContRepresentation.Equiv.mk k.toContinuousLinearEquiv ?_
    intro g
    ext x i
    change finiteTensorActionOperator ρ σ g x.val i =
      (finiteTensorActionOperator ρ κ g (k x) i).val
    simp [finiteTensorActionOperator, κ, equivariantKernelRepresentation, k]
    rfl
  -- The quotient map on each coordinate has kernel exactly the original product range.
  let q : (Fin ρ.dimension → F) →ₗ[ℂ] (Fin ρ.dimension → F ⧸ T.range) :=
    LinearMap.piMap (fun _ ↦ T.range.mkQ)
  have hq : Function.Surjective q := by
    intro x
    choose y hy using fun i ↦ T.range.mkQ_surjective (x i)
    exact ⟨y, funext hy⟩
  have hqker : q.ker = U.range := by
    ext y
    constructor
    · intro hy
      have hy' (i : Fin ρ.dimension) : y i ∈ T.range :=
        (Submodule.Quotient.mk_eq_zero T.range).mp (congrFun hy i)
      choose x hx using hy'
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩
      ext i
      exact (Submodule.Quotient.mk_eq_zero T.range).mpr ⟨x i, rfl⟩
  let c : ((Fin ρ.dimension → F) ⧸ U.range) ≃ₗ[ℂ]
      (Fin ρ.dimension → F ⧸ T.range) :=
    (Submodule.quotEquivOfEq _ _ hqker.symm).trans (q.quotKerEquivOfSurjective hq)
  have hc_apply (y : Fin ρ.dimension → F) : c (U.range.mkQ y) = q y := rfl
  have hc : ContRepresentation.Equiv
      (equivariantCokernelRepresentation σ' τ' U hUg)
      (finiteTensorRepresentation ρ χ) := by
    refine ContRepresentation.Equiv.mk c.toContinuousLinearEquiv ?_
    intro g
    apply ContinuousLinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | _ y =>
      change c (U.range.mkQ (τ' g y)) = finiteTensorRepresentation ρ χ g (c (U.range.mkQ y))
      rw [hc_apply, hc_apply]
      ext i
      change T.range.mkQ (finiteTensorActionOperator ρ τ g y i) =
        finiteTensorActionOperator ρ χ g (q y) i
      simp only [finiteTensorActionOperator, ContinuousLinearMap.pi_apply,
        sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.proj_apply, map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro j _
      rfl
  -- Compare genuine tensor coordinates with the ring's specified finite tensor coordinates.
  have hclassK : representationClass (finiteTensorRepresentation ρ κ)
      (continuous_finiteTensorRepresentation ρ κ hκ) =
        finiteRepresentationClass ρ * representationClass κ hκ := by
    let e : T.ker ≃L[ℂ] (Fin (Module.finrank ℂ T.ker) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let ν := FiniteContinuousRepresentation.ofEquiv κ hκ e
    let a := finiteTensorCoordinates ρ.dimension T.ker
    let b := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension ν.dimension
    let d := a.symm.trans
      ((TensorProduct.congr (LinearEquiv.refl ℂ _) e.toLinearEquiv).trans b)
    have he (g : G) (x : T.ker) : ν.representation g (e x) = e (κ g x) := by
      change e (κ g (e.symm (e x))) = e (κ g x)
      rw [e.symm_apply_apply]
    have hd (v : Fin ρ.dimension → ℂ) (x : T.ker) :
        d (a (v ⊗ₜ[ℂ] x)) = b (v ⊗ₜ[ℂ] e x) := by
      simp only [d, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rfl
    have hintertwine (g : G) (z : Fin ρ.dimension → T.ker) :
        d (finiteTensorRepresentation ρ κ g z) =
          (ρ.tensor ν).representation g (d z) := by
      obtain ⟨w, rfl⟩ := a.surjective z
      induction w using TensorProduct.inductionOn with
      | tmul v x =>
        change d (finiteTensorRepresentation ρ κ g
          (finiteTensorCoordinates ρ.dimension T.ker (v ⊗ₜ[ℂ] x))) = _
        rw [finiteTensorRepresentation_tmul]
        change d (a (ρ.representation g v ⊗ₜ[ℂ] κ g x)) = _
        rw [hd, hd, ← he]
        exact (FiniteContinuousRepresentation.tensor_tmul ρ ν g v (e x)).symm
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    rw [representationClass_ofEquiv (finiteTensorRepresentation ρ κ)
      (continuous_finiteTensorRepresentation ρ κ hκ) d.toContinuousLinearEquiv,
      representationClass_ofEquiv κ hκ e]
    change finiteRepresentationClass _ = representationMul G
      (finiteRepresentationClass ρ) (finiteRepresentationClass ν)
    rw [representationMul_finiteClass]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro z
    change d (finiteTensorRepresentation ρ κ g (d.symm z)) =
      (ρ.tensor ν).representation g z
    rw [hintertwine, d.apply_symm_apply]
  -- Use the same tensor comparison for the actual quotient-cokernel representation.
  have hclassQ : representationClass (finiteTensorRepresentation ρ χ)
      (continuous_finiteTensorRepresentation ρ χ hχ) =
        finiteRepresentationClass ρ * representationClass χ hχ := by
    let e : (F ⧸ T.range) ≃L[ℂ] (Fin (Module.finrank ℂ (F ⧸ T.range)) → ℂ) :=
      ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℂ).symm
    let ν := FiniteContinuousRepresentation.ofEquiv χ hχ e
    let a := finiteTensorCoordinates ρ.dimension (F ⧸ T.range)
    let b := FiniteContinuousRepresentation.tensorCoordinates ρ.dimension ν.dimension
    let d := a.symm.trans
      ((TensorProduct.congr (LinearEquiv.refl ℂ _) e.toLinearEquiv).trans b)
    have he (g : G) (x : (F ⧸ T.range)) : ν.representation g (e x) = e (χ g x) := by
      change e (χ g (e.symm (e x))) = e (χ g x)
      rw [e.symm_apply_apply]
    have hd (v : Fin ρ.dimension → ℂ) (x : (F ⧸ T.range)) :
        d (a (v ⊗ₜ[ℂ] x)) = b (v ⊗ₜ[ℂ] e x) := by
      simp only [d, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
        TensorProduct.congr_tmul, LinearEquiv.refl_apply]
      rfl
    have hintertwine (g : G) (z : Fin ρ.dimension → (F ⧸ T.range)) :
        d (finiteTensorRepresentation ρ χ g z) =
          (ρ.tensor ν).representation g (d z) := by
      obtain ⟨w, rfl⟩ := a.surjective z
      induction w using TensorProduct.inductionOn with
      | tmul v x =>
        change d (finiteTensorRepresentation ρ χ g
          (finiteTensorCoordinates ρ.dimension (F ⧸ T.range) (v ⊗ₜ[ℂ] x))) = _
        rw [finiteTensorRepresentation_tmul]
        change d (a (ρ.representation g v ⊗ₜ[ℂ] χ g x)) = _
        rw [hd, hd, ← he]
        exact (FiniteContinuousRepresentation.tensor_tmul ρ ν g v (e x)).symm
      | add x y hx hy =>
        simp only [map_add, hx, hy]
    rw [representationClass_ofEquiv (finiteTensorRepresentation ρ χ)
      (continuous_finiteTensorRepresentation ρ χ hχ) d.toContinuousLinearEquiv,
      representationClass_ofEquiv χ hχ e]
    change finiteRepresentationClass _ = representationMul G
      (finiteRepresentationClass ρ) (finiteRepresentationClass ν)
    rw [representationMul_finiteClass]
    apply finiteRepresentationClass_eq_of_isEquivalent
    refine ⟨ContRepresentation.Equiv.mk (ContinuousLinearEquiv.refl ℂ _) ?_⟩
    intro g
    apply ContinuousLinearMap.ext
    intro z
    change d (finiteTensorRepresentation ρ χ g (d.symm z)) =
      (ρ.tensor ν).representation g z
    rw [hintertwine, d.apply_symm_apply]
  -- Substitute the two actual representation comparisons into the same index difference.
  have hkernel := representationClass_eq_of_equiv
    (equivariantKernelRepresentation σ' τ' U hUg) (finiteTensorRepresentation ρ κ)
    (continuous_equivariantKernelRepresentation σ' τ' U hUg
      (continuous_finiteTensorRepresentation ρ σ hσ))
    (continuous_finiteTensorRepresentation ρ κ hκ) hk
  have hcokernel := representationClass_eq_of_equiv
    (equivariantCokernelRepresentation σ' τ' U hUg) (finiteTensorRepresentation ρ χ)
    (continuous_equivariantCokernelRepresentation σ' τ' U hUg
      (continuous_finiteTensorRepresentation ρ τ hτ))
    (continuous_finiteTensorRepresentation ρ χ hχ) hc
  unfold equivariantFredholmIndex
  rw [hkernel, hcokernel, hclassK, hclassQ, mul_sub]

end AtiyahSinger
