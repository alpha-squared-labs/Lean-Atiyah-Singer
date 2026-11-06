/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexConnection
public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Geometry.CovariantHomConnection
public import AtiyahSinger.Geometry.HermitianMetric
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# Actual iterated covariant derivatives and their tensor metric

Public module ID: M1286.

A01. The k-th derivative takes values in the original iterated Hom bundle
T^0(E)=E, T^(k+1)(E)=Hom_R(TM,T^k(E)). Its connection is recursively induced
from the given connections on TM and E. Complex compatibility on E is an
explicit hypothesis of the complex-linearity results. The derivative is the
literal recursion nabla^0 u=u and
nabla^(k+1)u=nabla_k(nabla^k u), not a supplied family of differential maps.

The small bundled record below exists only to recurse simultaneously on a
fiber, its model and their native algebraic/topological/smooth instances.
It supplies no unspecified connection, derivative, pairing or norm. Each
successor uses mathlib's original Hom-bundle topology and smooth structure.
The initial adapter retains the original E topology and scalar restriction.

The supplied cotangent metric and Hermitian metric define the tensor pairing
by repeated inverse-tangent-metric contraction. The raw tangent coordinate
basis is only an implementation choice; invariance allows all smoothness
arguments to use genuine smooth local frames. These are full covariant
tensors, so there is no exterior-power factor 1/k!. The data retain arbitrary
smooth connections; torsion freedom and metric compatibility are not needed
for the integer Sobolev comparison on a compact base.

Sources: SG III.2, p.170, (2.1), and p.176, Proposition 2.14, for the
integer derivative norm. The induced Hom connection and full inverse-metric
contraction explicitly expand its standard tensor-product construction.
The original tensor contraction is conjugate symmetric and positive definite.
Its proofs use real tensor inner products without replacing any production
fiber topology. Complex homogeneity of the actual iterates is independent of
the regularity of the Hom tower. The weaker-hypothesis regularity, additivity
and contraction-continuity statements below are inactive documentation.
Hausdorff-base smooth iteration is supplied by SeparatedCovariantDerivatives.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 40

universe u v

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)
local notation "TModel" => EuclideanSpace ℝ (Fin n)

/-- Implementation data for recursion through the same native smooth Hom bundles.
All fields are inherited bundle instances, never higher-derivative hypotheses. -/
structure CovariantTensorBundleData where
  /-- The original finite-dimensional real normed model at this stage. -/
  model : Type
  /-- The existing normed additive structure on the model. -/
  [modelNormedAddCommGroup : NormedAddCommGroup model]
  /-- The existing real normed module structure on the model. -/
  [modelNormedSpace : NormedSpace ℝ model]
  /-- The model is finite dimensional. -/
  [modelFiniteDimensional : FiniteDimensional ℝ model]
  /-- The actual fibers at this stage. -/
  fiber : M → Type v
  /-- The original additive operations in those fibers. -/
  [fiberAddCommGroup : ∀ x, AddCommGroup (fiber x)]
  /-- The original real scalar action in those fibers. -/
  [fiberRealModule : ∀ x, Module ℝ (fiber x)]
  /-- Complex scalars act in the original value slot. -/
  [fiberComplexModule : ∀ x, Module ℂ (fiber x)]
  /-- The real action is the restriction of the complex action. -/
  [fiberScalarTower : ∀ x, IsScalarTower ℝ ℂ (fiber x)]
  /-- Real and complex value scalars commute. -/
  [fiberSmulComm : ∀ x, SMulCommClass ℝ ℂ (fiber x)]
  /-- The original fiber topology. -/
  [fiberTopology : ∀ x, TopologicalSpace (fiber x)]
  /-- Addition is continuous for that topology. -/
  [fiberTopologicalAddGroup : ∀ x, IsTopologicalAddGroup (fiber x)]
  /-- Real scalar multiplication is continuous. -/
  [fiberContinuousRealSMul : ∀ x, ContinuousSMul ℝ (fiber x)]
  /-- Each constant complex scalar acts continuously in the value slot. -/
  [fiberContinuousComplexConstSMul : ∀ x, ContinuousConstSMul ℂ (fiber x)]
  /-- The original total-space topology. -/
  [totalTopology : TopologicalSpace (TotalSpace model fiber)]
  /-- The native local trivializations for that total-space topology. -/
  [fiberBundle : FiberBundle model fiber]
  /-- Those trivializations are real linear. -/
  [vectorBundle : VectorBundle ℝ model fiber]
  /-- The same original transitions are smooth. -/
  [smoothBundle : ContMDiffVectorBundle ∞ model fiber I]

attribute [instance] CovariantTensorBundleData.modelNormedAddCommGroup
  CovariantTensorBundleData.modelNormedSpace CovariantTensorBundleData.modelFiniteDimensional
  CovariantTensorBundleData.fiberAddCommGroup CovariantTensorBundleData.fiberRealModule
  CovariantTensorBundleData.fiberComplexModule CovariantTensorBundleData.fiberScalarTower
  CovariantTensorBundleData.fiberSmulComm CovariantTensorBundleData.fiberTopology
  CovariantTensorBundleData.fiberTopologicalAddGroup
  CovariantTensorBundleData.fiberContinuousRealSMul
  CovariantTensorBundleData.fiberContinuousComplexConstSMul CovariantTensorBundleData.totalTopology
  CovariantTensorBundleData.fiberBundle CovariantTensorBundleData.vectorBundle
  CovariantTensorBundleData.smoothBundle

/-- One actual native Hom-bundle step; all instances are the existing mathlib constructions. -/
def CovariantTensorBundleData.hom (B : CovariantTensorBundleData (n := n) (M := M)) :
    CovariantTensorBundleData (n := n) (M := M) where
  model := TModel →L[ℝ] B.model
  modelNormedAddCommGroup := inferInstance
  modelNormedSpace := inferInstance
  modelFiniteDimensional := inferInstance
  fiber := fun x ↦ TM x →L[ℝ] B.fiber x
  fiberAddCommGroup := fun _ ↦ inferInstance
  fiberRealModule := fun _ ↦ inferInstance
  fiberComplexModule := fun _ ↦ inferInstance
  fiberScalarTower := fun _ ↦ inferInstance
  fiberSmulComm := fun _ ↦ inferInstance
  fiberTopology := fun _ ↦ inferInstance
  fiberTopologicalAddGroup := fun _ ↦ inferInstance
  fiberContinuousRealSMul := fun _ ↦ inferInstance
  fiberContinuousComplexConstSMul := fun _ ↦ inferInstance
  totalTopology := inferInstance
  fiberBundle := inferInstance
  vectorBundle := inferInstance
  smoothBundle := inferInstance

attribute [local instance] complexBundleRealNormedSpace vectorBundle_real_of_complex
  contMDiffVectorBundle_real_of_complex

variable {r : ℕ} (E : M → Type v)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [IsSmoothComplexBundle (n := n) (r := r) E]

/-- The actual Hom tower beginning at the original real-restricted complex bundle. -/
def covariantTensorBundle : ℕ → CovariantTensorBundleData (n := n) (M := M)
  | 0 =>
    { model := EuclideanSpace ℂ (Fin r)
      modelNormedAddCommGroup := inferInstance
      modelNormedSpace := inferInstance
      modelFiniteDimensional := inferInstance
      fiber := E
      fiberAddCommGroup := fun _ ↦ inferInstance
      fiberRealModule := fun _ ↦ inferInstance
      fiberComplexModule := fun _ ↦ inferInstance
      fiberScalarTower := fun _ ↦ inferInstance
      fiberSmulComm := fun _ ↦ inferInstance
      fiberTopology := fun _ ↦ inferInstance
      fiberTopologicalAddGroup := fun _ ↦ inferInstance
      fiberContinuousRealSMul := fun _ ↦ inferInstance
      fiberContinuousComplexConstSMul := fun _ ↦ inferInstance
      totalTopology := inferInstance
      fiberBundle := inferInstance
      vectorBundle := inferInstance
      smoothBundle := inferInstance }
  | k + 1 => (covariantTensorBundle k).hom

/-- The native model of the k-fold covariant tensor bundle. -/
abbrev CovariantTensorModel (k : ℕ) : Type := (covariantTensorBundle (n := n) (r := r) E k).model

/-- The original k-fold continuous real Hom fiber with values in the original complex fiber. -/
abbrev CovariantTensorFiber (k : ℕ) (x : M) : Type v :=
  (covariantTensorBundle (n := n) (r := r) E k).fiber x

variable {E}
  (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (covE : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℂ (Fin r)) E)

/-- The actual induced connection at each stage of the native Hom tower. -/
def covariantTensorConnection : (k : ℕ) →
    CovariantDerivative I (CovariantTensorModel (n := n) (r := r) E k)
      (CovariantTensorFiber (n := n) (r := r) E k)
  | 0 => covE
  | k + 1 => covariantHomConnection covT (covariantTensorConnection k)

/-- The genuine iterated covariant derivative, recursively applying the induced connections. -/
def iteratedCovariantDerivative : (k : ℕ) → (∀ x : M, E x) →
    ∀ x : M, CovariantTensorFiber (n := n) (r := r) E k x
  | 0, u => u
  | k + 1, u => covariantTensorConnection covT covE k
      (iteratedCovariantDerivative k u)

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use the proved Hausdorff connection and derivative interfaces.
The historical outline below was not verified under the original weaker hypotheses.
This block defines no Lean constant.

/-- Each recursively induced connection is smooth when the two original connections are smooth. -/
theorem contMDiff_covariantTensorConnection
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞) (k : ℕ) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (covariantTensorConnection covT covE k) ∞ 
  /- Induct on k. At zero this is the supplied smoothness of covE.
  At a successor use contMDiff_covariantHomConnection with exactly covT
  and the already constructed preceding connection. Thus no independently
  supplied connection family or smoothness family is being assumed. -/
-/

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use the proved Hausdorff connection and derivative interfaces.
The historical outline below was not verified under the original weaker hypotheses.
This block defines no Lean constant.

/-- Iteration of the actual connections sends an original smooth section to a smooth tensor. -/
theorem contMDiff_iteratedCovariantDerivative
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (k : ℕ) (u : smoothSections (n := n) (r := r) E) :
    ContMDiff I ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E k)) ∞
      (fun x ↦ (⟨x, iteratedCovariantDerivative covT covE k u.val x⟩ :
        TotalSpace (CovariantTensorModel (n := n) (r := r) E k)
          (CovariantTensorFiber (n := n) (r := r) E k))) 
  /- Start with the original smoothness certificate of u, viewed over
  the same real-restricted bundle. At each successor apply the native
  smooth-connection property just constructed to the preceding smooth
  derivative section. Infinity plus one is infinity, so iteration loses
  no smoothness. All target topologies are the same recursive Hom topologies. -/
-/

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use the proved Hausdorff connection and derivative interfaces.
The historical outline below was not verified under the original weaker hypotheses.
This block defines no Lean constant.

/-- Iteration is additive on the original smooth sections. -/
theorem iteratedCovariantDerivative_add
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (k : ℕ) (u v : smoothSections (n := n) (r := r) E) (x : M) :
    iteratedCovariantDerivative covT covE k (u + v).val x =
      iteratedCovariantDerivative covT covE k u.val x +
        iteratedCovariantDerivative covT covE k v.val x 
  /- The zero stage is ordinary addition of the same original sections.
  Inductively the two preceding derivative sections are smooth, hence
  differentiable at x. The native additive connection axiom therefore
  applies to their sum. Use the recursion and the induction identity. -/
-/

/-- Constant complex scalars preserve differentiability in every native tensor-Hom bundle.
The complex action is only in the original value slot; tangent arguments remain real. -/
theorem mdifferentiableAt_covariantTensor_smul (k : ℕ) :
    ∀ (c : ℂ) (σ : ∀ x : M, CovariantTensorFiber (n := n) (r := r) E k x) (x : M),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E k))
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace (CovariantTensorModel (n := n) (r := r) E k)
          (CovariantTensorFiber (n := n) (r := r) E k))) x →
      MDifferentiableAt I ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E k))
        (fun y ↦ (⟨y, c • σ y⟩ : TotalSpace (CovariantTensorModel (n := n) (r := r) E k)
          (CovariantTensorFiber (n := n) (r := r) E k))) x := by
  induction k with
  | zero =>
    -- The original complex-linear frame maps commute with the same scalar.
    intro c σ x hσ
    let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
    have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
    have hcoord := (e.mdifferentiableAt_section_iff I _ he).mp hσ
    apply (e.mdifferentiableAt_section_iff I _ he).mpr
    have hs := ((c • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin r))).restrictScalars
      ℝ).mdifferentiableAt.comp x hcoord
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact (e.linearEquivAt ℂ y hy).map_smul c (σ y)
  | succ k ih =>
    -- Test the Hom section in a local tangent basis, then apply the preceding value result.
    intro c σ x hσ
    let A : ∀ y : M, TM y →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k y := σ
    apply mdifferentiableAt_tangentHom_of_localFrame
    intro a
    let t := trivializationAt TModel TM x
    have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt TModel TM x
    let X (y : M) : TM y := t.symmL ℝ y (EuclideanSpace.single a 1)
    have hX : MDifferentiableAt I (I).tangent
        (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x := by
      apply (t.mdifferentiableAt_section_iff I _ ht).mpr
      apply (mdifferentiableAt_const (c := EuclideanSpace.single a (1 : ℝ))).congr_of_eventuallyEq
      filter_upwards [t.open_baseSet.mem_nhds ht] with y hy
      simp only [X, t.symmL_apply hy, t.apply_mk_symm hy]
    have hd : MDifferentiableAt I
        ((I).prod 𝓘(ℝ, TModel →L[ℝ] CovariantTensorModel (n := n) (r := r) E k))
        (fun y ↦ (⟨y, A y⟩ : TotalSpace
          (TModel →L[ℝ] CovariantTensorModel (n := n) (r := r) E k)
          (fun y ↦ TM y →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k y))) x := hσ
    exact ih c (fun y ↦ A y (X y)) x (hd.clm_bundle_apply hX)

/-- The actual induced tensor connections are complex linear on differentiable inputs.
This follows from the original complex connection and the two-term Hom formula. -/
theorem covariantTensorConnection_const_smul
    (covT : CovariantDerivative I TModel TM)
    (covE : CovariantDerivative I (EuclideanSpace ℂ (Fin r)) E)
    (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E covE) (k : ℕ) :
    ∀ (c : ℂ) (σ : ∀ x : M, CovariantTensorFiber (n := n) (r := r) E k x) (x : M),
      MDifferentiableAt I ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E k))
        (fun y ↦ (⟨y, σ y⟩ : TotalSpace (CovariantTensorModel (n := n) (r := r) E k)
          (CovariantTensorFiber (n := n) (r := r) E k))) x →
      covariantTensorConnection covT covE k (fun y ↦ c • σ y) x =
        c • covariantTensorConnection covT covE k σ x := by
  induction k with
  | zero =>
    intro c σ x hσ
    ext v
    exact hcomplex σ x hσ (Set.mem_univ x) c v
  | succ k ih =>
    intro c σ x hσ
    let A : ∀ y : M, TM y →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k y := σ
    have hA : MDifferentiableAt I
        ((I).prod 𝓘(ℝ, TModel →L[ℝ] CovariantTensorModel (n := n) (r := r) E k))
        (fun y ↦ (⟨y, A y⟩ : TotalSpace
          (TModel →L[ℝ] CovariantTensorModel (n := n) (r := r) E k)
          (fun y ↦ TM y →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k y))) x := hσ
    have hscale := mdifferentiableAt_covariantTensor_smul (k + 1) c σ x hσ
    change covariantHomConnection covT (covariantTensorConnection covT covE k)
        (fun y ↦ c • A y) x =
      c • covariantHomConnection covT (covariantTensorConnection covT covE k) A x
    -- Use the same local representatives in both evaluations of the Hom formula.
    ext v w
    let X := FiberBundle.extend TModel v
    let Y := FiberBundle.extend TModel w
    have hX := FiberBundle.mdifferentiableAt_extend I TModel v
    have hY := FiberBundle.mdifferentiableAt_extend I TModel w
    have hXval : X x = v := by simp [X]
    have hYval : Y x = w := by simp [Y]
    change covariantHomConnection covT (covariantTensorConnection covT covE k)
        (fun y ↦ c • A y) x v w =
      c • covariantHomConnection covT (covariantTensorConnection covT covE k) A x v w
    rw [← hXval, ← hYval,
      covariantHomConnection_apply covT (covariantTensorConnection covT covE k)
        (fun y ↦ c • A y) X Y x hscale hX hY,
      covariantHomConnection_apply covT (covariantTensorConnection covT covE k)
        A X Y x hA hX hY]
    change covariantTensorConnection covT covE k (fun y ↦ c • A y (Y y)) x (X x) -
        c • A x (covT Y x (X x)) =
      c • (covariantTensorConnection covT covE k (fun y ↦ A y (Y y)) x (X x) -
        A x (covT Y x (X x)))
    rw [ih c (fun y ↦ A y (Y y)) x (hA.clm_bundle_apply hY)]
    simp only [smul_apply, smul_sub]

/-- The given complex connection makes every actual iterate complex linear on smooth inputs. -/
theorem iteratedCovariantDerivative_smul
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (hcomplex : IsComplexLinearConnectionOn (n := n) (r := r) E covE)
    (k : ℕ) (c : ℂ) (u : smoothSections (n := n) (r := r) E) (x : M) :
    iteratedCovariantDerivative covT covE k (c • u).val x =
      c • iteratedCovariantDerivative covT covE k u.val x := by
  /- Induct through the actual recursion. On differentiable tensor inputs,
  complex compatibility of the induced connection gives the desired identity.
  A nonzero constant scalar preserves and reflects differentiability, so the
  two nondifferentiable inputs both receive the prescribed zero Hom derivative.
  This argument does not require the smoothness of the Hom tower. -/
  classical
  let := hcovT
  let := hcovE
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have heq : iteratedCovariantDerivative covT covE k (c • u).val =
        fun y ↦ c • iteratedCovariantDerivative covT covE k u.val y := funext ih
    change covariantTensorConnection covT covE k
        (iteratedCovariantDerivative covT covE k (c • u).val) x =
      c • covariantTensorConnection covT covE k
        (iteratedCovariantDerivative covT covE k u.val) x
    rw [heq]
    -- Zero scalars use the native zero-section identity at every tensor stage.
    by_cases hc : c = 0
    · subst c
      simp only [zero_smul]
      exact congrFun (CovariantDerivative.zero (covariantTensorConnection covT covE k)) x
    cases k with
    | zero =>
      apply covariantTensorConnection_const_smul covT covE hcomplex 0 c u.val x
      let e := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
      have he : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ x
      have hu : ContMDiffAt I ((I).prod 𝓘(ℝ, EuclideanSpace ℂ (Fin r))) ∞
          (fun y ↦ (⟨y, u.val y⟩ : TotalSpace (EuclideanSpace ℂ (Fin r)) E)) x :=
        (e.contMDiffAt_section_iff he).mpr
          ((u.property e inferInstance).contMDiffAt (e.open_baseSet.mem_nhds he))
      exact hu.mdifferentiableAt (by simp)
    | succ k =>
      -- Nonzero scalars preserve the original differentiable/nondifferentiable branch.
      let σ := iteratedCovariantDerivative covT covE (k + 1) u.val
      by_cases hσ : MDifferentiableAt I
          ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E (k + 1)))
          (fun y ↦ (⟨y, σ y⟩ : TotalSpace
            (CovariantTensorModel (n := n) (r := r) E (k + 1))
            (CovariantTensorFiber (n := n) (r := r) E (k + 1)))) x
      · exact covariantTensorConnection_const_smul covT covE hcomplex (k + 1) c σ x hσ
      · have hscaled : ¬ MDifferentiableAt I
            ((I).prod 𝓘(ℝ, CovariantTensorModel (n := n) (r := r) E (k + 1)))
            (fun y ↦ (⟨y, c • σ y⟩ : TotalSpace
              (CovariantTensorModel (n := n) (r := r) E (k + 1))
              (CovariantTensorFiber (n := n) (r := r) E (k + 1)))) x := by
          intro hs
          have hback := mdifferentiableAt_covariantTensor_smul (k + 1) c⁻¹
            (fun y ↦ c • σ y) x hs
          apply hσ
          simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hback
        change covariantHomDerivative covT (covariantTensorConnection covT covE k)
            (fun y ↦ c • σ y) x =
          c • covariantHomDerivative covT (covariantTensorConnection covT covE k) σ x
        unfold covariantHomDerivative
        split
        · rename_i hs
          exact (hscaled hs).elim
        · split
          · rename_i hs
            exact (hσ hs).elim
          · exact (smul_zero c).symm

variable (g : SmoothCotangentMetric (n := n) (M := M))
  (h : SmoothHermitianMetric (n := n) (r := r) E)

/-- Contract every covariant slot using the supplied cotangent metric and original fiber form. -/
def iteratedCovariantPairing : (k : ℕ) → (x : M) →
    CovariantTensorFiber (n := n) (r := r) E k x → CovariantTensorFiber (n := n) (r := r) E k x → ℂ
  | 0, x, a, b => h.pairing x a b
  | k + 1, x, a, b =>
    let a' : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x := a
    let b' : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x := b
    ∑ i : Fin n, ∑ j : Fin n,
      (g.inner x (EuclideanSpace.proj i) (EuclideanSpace.proj j) : ℂ) *
        iteratedCovariantPairing k x (a' (EuclideanSpace.single i 1))
          (b' (EuclideanSpace.single j 1))

/-- The induced full-tensor metric is conjugate symmetric. -/
theorem iteratedCovariantPairing_conj_symm (k : ℕ) (x : M)
    (a b : CovariantTensorFiber (n := n) (r := r) E k x) :
    conj (iteratedCovariantPairing g h k x b a) =
      iteratedCovariantPairing g h k x a b := by
  /- Induct on k. At zero use the original Hermitian pairing.
  At each successor conjugate the finite contraction, use symmetry and
  reality of the cotangent Gram coefficients, apply the preceding
  conjugate symmetry and exchange the two finite indices. -/
  classical
  -- Conjugation reverses the value pairing and fixes the real Gram coefficients.
  induction k with
  | zero => exact (h.toCore x).conj_inner_symm a b
  | succ k ih =>
    let a' : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x := a
    let b' : TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E k x := b
    let p : Fin n → CotangentFiber (n := n) x := fun i ↦ EuclideanSpace.proj i
    change conj (∑ i : Fin n, ∑ j : Fin n, (g.inner x (p i) (p j) : ℂ) *
      iteratedCovariantPairing g h k x (b' (EuclideanSpace.single i 1))
        (a' (EuclideanSpace.single j 1))) =
      ∑ i : Fin n, ∑ j : Fin n, (g.inner x (p i) (p j) : ℂ) *
        iteratedCovariantPairing g h k x (a' (EuclideanSpace.single i 1))
          (b' (EuclideanSpace.single j 1))
    simp only [map_sum, map_mul, Complex.conj_ofReal, ih]
    -- Exchange the two tangent indices using symmetry of the same cotangent metric.
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun z : ℝ ↦ (z : ℂ) *
      iteratedCovariantPairing g h k x (a' (EuclideanSpace.single i 1))
        (b' (EuclideanSpace.single j 1))) (g.symm x (p j) (p i))

/-- The tensor metric is nonnegative on its diagonal. -/
theorem iteratedCovariantPairing_self_nonneg (k : ℕ) (x : M)
    (a : CovariantTensorFiber (n := n) (r := r) E k x) :
    0 ≤ (iteratedCovariantPairing g h k x a a).re := by
  /- Construct a real positive core realizing the real part of the contraction,
  inductively through the tensor degree. At a successor, embed the actual Hom
  fiber into the algebraic cotangent tensor product using the original basis
  and its dual. Evaluation recovers the Hom coefficients, proving injectivity.
  The tensor inner-product formula is exactly the displayed contraction,
  so its pullback core gives nonnegativity. Auxiliary value norms stay local
  to this proof and do not alter the stored original Hom maps. -/
  classical
  -- Real tensor inner products realize the same orthonormal tensor metric in the raw basis.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) := ⟨g.toRiemannianMetric⟩
  have cores (j : ℕ) :
      ∃ c : InnerProductSpace.Core ℝ (CovariantTensorFiber (n := n) (r := r) E j x),
        ∀ u v, c.inner u v = (iteratedCovariantPairing g h j x u v).re := by
    induction j with
    | zero =>
      change ∃ c : InnerProductSpace.Core ℝ (E x),
        ∀ u v, c.inner u v = (h.pairing x u v).re
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      refine ⟨{
        inner := fun u v ↦ (h.pairing x u v).re
        conj_inner_symm := ?_
        re_inner_nonneg := (h.toCore x).re_inner_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }, fun _ _ ↦ rfl⟩
      · intro u v
        change (h.pairing x v u).re = (h.pairing x u v).re
        simpa only [SmoothHermitianMetric.pairing, Complex.conj_re] using
          congrArg Complex.re ((h.toCore x).conj_inner_symm u v)
      · intro u v w
        change ((h.toCore x).inner (u + v) w).re = _
        rw [(h.toCore x).add_left, Complex.add_re]
        rfl
      · intro u v c
        change ((h.toCore x).inner ((c : ℂ) • u) v).re = c * ((h.toCore x).inner u v).re
        simpa only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero] using
          congrArg Complex.re ((h.toCore x).smul_left u v (c : ℂ))
      · intro u hu
        exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hu
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      -- Keep the original Hom topology until the algebraic embedding is fixed.
      let view (u : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          TM x →ₗ[ℝ] CovariantTensorFiber (n := n) (r := r) E j x :=
        (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from u).toLinearMap
      let p : Fin n → CotangentFiber (n := n) x := fun i ↦ EuclideanSpace.proj i
      let b : Fin n → TM x := fun i ↦ EuclideanSpace.single i 1
      let embed : CovariantTensorFiber (n := n) (r := r) E (j + 1) x →ₗ[ℝ]
          TensorProduct ℝ (CotangentFiber (n := n) x)
            (CovariantTensorFiber (n := n) (r := r) E j x) := {
        toFun := fun u ↦ ∑ i : Fin n, TensorProduct.tmul ℝ (p i) (view u (b i))
        map_add' := by
          intro u v
          have hval (i : Fin n) :
              view (u + v) (b i) = view u (b i) + view v (b i) := rfl
          simp only [hval, TensorProduct.tmul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c u
          have hval (i : Fin n) : view (c • u) (b i) = c • view u (b i) := rfl
          simp only [hval, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply] }
      -- Evaluation on each original tangent basis vector recovers every tensor coefficient.
      let recover (i : Fin n) :
          TensorProduct ℝ (CotangentFiber (n := n) x)
            (CovariantTensorFiber (n := n) (r := r) E j x) →ₗ[ℝ]
              CovariantTensorFiber (n := n) (r := r) E j x :=
        (TensorProduct.lid ℝ _).toLinearMap.comp
          (TensorProduct.map {
            toFun := fun ξ ↦ ξ (b i)
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
            (LinearMap.id : CovariantTensorFiber (n := n) (r := r) E j x →ₗ[ℝ] _))
      have hrecover (i : Fin n) (u : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          recover i (embed u) = view u (b i) := by
        have hterm (l : Fin n) :
            recover i (TensorProduct.tmul ℝ (p l) (view u (b l))) =
              (p l) (b i) • view u (b l) := rfl
        have hcoord (l : Fin n) : (p l) (b i) = if l = i then 1 else 0 := by
          change (EuclideanSpace.single i (1 : ℝ)) l = _
          simp [EuclideanSpace.single, eq_comm]
        change recover i (∑ l : Fin n, TensorProduct.tmul ℝ (p l) (view u (b l))) = _
        rw [map_sum]
        simp only [hterm, hcoord]
        simp
      have hinj : Function.Injective embed := by
        intro u v huv
        change (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from u) =
          (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from v)
        apply ContinuousLinearMap.ext
        intro w
        change view u w = view v w
        let w' : TModel := w
        have hw : (∑ i : Fin n, w' i • b i) = w := by
          change (∑ i : Fin n, w' i • EuclideanSpace.single i 1) = w'
          ext l
          simp [EuclideanSpace.single, Pi.single_apply]
        rw [← hw, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, map_smul]
        exact congrArg (fun z ↦ w' i • z)
          ((hrecover i u).symm.trans ((congrArg (recover i) huv).trans (hrecover i v)))
      -- Auxiliary norms are confined to this proof; the stored original Hom maps stay fixed.
      let : InnerProductSpace.Core ℝ (CovariantTensorFiber (n := n) (r := r) E j x) := c
      let : NormedAddCommGroup (CovariantTensorFiber (n := n) (r := r) E j x) :=
        c.toNormedAddCommGroup
      let : InnerProductSpace ℝ (CovariantTensorFiber (n := n) (r := r) E j x) :=
        InnerProductSpace.ofCore c.toCore
      have hformula (u v : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          inner ℝ (embed u) (embed v) = (iteratedCovariantPairing g h (j + 1) x u v).re := by
        simp only [embed, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
          TensorProduct.inner_tmul]
        rw [Finset.sum_comm]
        change (∑ i : Fin n, ∑ l : Fin n,
          g.inner x (p i) (p l) * c.inner (view u (b i)) (view v (b l))) = _
        simp only [hc, iteratedCovariantPairing, Complex.re_sum, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rfl
      refine ⟨{
        inner := fun u v ↦ inner ℝ (embed u) (embed v)
        conj_inner_symm := by
          intro u v
          change inner ℝ (embed v) (embed u) = inner ℝ (embed u) (embed v)
          exact real_inner_comm _ _
        re_inner_nonneg := by
          intro u
          change 0 ≤ inner ℝ (embed u) (embed u)
          exact real_inner_self_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }, hformula⟩
      · intro u v w
        rw [embed.map_add, inner_add_left]
      · intro u v a
        rw [embed.map_smul, real_inner_smul_left]
        rfl
      · intro u hu
        apply hinj
        rw [embed.map_zero]
        exact (inner_self_eq_zero (𝕜 := ℝ)).mp hu
  obtain ⟨c, hc⟩ := cores k
  rw [← hc a a]
  exact c.re_inner_nonneg a

/-- Only the zero tensor has zero squared length for the original induced metric. -/
theorem iteratedCovariantPairing_self_eq_zero_iff (k : ℕ) (x : M)
    (a : CovariantTensorFiber (n := n) (r := r) E k x) :
    (iteratedCovariantPairing g h k x a a).re = 0 ↔ a = 0 := by
  /- Realize the real contraction by a positive core, as in the nonnegativity
  argument. The original Hom-to-tensor embedding is injective because its
  coefficients are recovered by tangent-basis evaluation. Pulling back the
  tensor inner product therefore gives a definite core. Its definiteness
  proves the forward implication, and the zero inner-product identity proves
  the reverse. Empty tangent bases require no separate rank hypothesis. -/
  classical
  -- Reconstruct the real tensor metric through an injective algebraic Hom embedding.
  let : RiemannianBundle (CotangentFiber (n := n) (M := M)) := ⟨g.toRiemannianMetric⟩
  have cores (j : ℕ) :
      ∃ c : InnerProductSpace.Core ℝ (CovariantTensorFiber (n := n) (r := r) E j x),
        ∀ u v, c.inner u v = (iteratedCovariantPairing g h j x u v).re := by
    induction j with
    | zero =>
      change ∃ c : InnerProductSpace.Core ℝ (E x),
        ∀ u v, c.inner u v = (h.pairing x u v).re
      let : InnerProductSpace.Core ℂ (E x) := h.toCore x
      refine ⟨{
        inner := fun u v ↦ (h.pairing x u v).re
        conj_inner_symm := ?_
        re_inner_nonneg := (h.toCore x).re_inner_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }, fun _ _ ↦ rfl⟩
      · intro u v
        change (h.pairing x v u).re = (h.pairing x u v).re
        simpa only [SmoothHermitianMetric.pairing, Complex.conj_re] using
          congrArg Complex.re ((h.toCore x).conj_inner_symm u v)
      · intro u v w
        change ((h.toCore x).inner (u + v) w).re = _
        rw [(h.toCore x).add_left, Complex.add_re]
        rfl
      · intro u v c
        change ((h.toCore x).inner ((c : ℂ) • u) v).re = c * ((h.toCore x).inner u v).re
        simpa only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, sub_zero] using
          congrArg Complex.re ((h.toCore x).smul_left u v (c : ℂ))
      · intro u hu
        exact (InnerProductSpace.Core.normSq_eq_zero (𝕜 := ℂ)).mp hu
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      -- Keep the original Hom topology until the algebraic embedding is fixed.
      let view (u : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          TM x →ₗ[ℝ] CovariantTensorFiber (n := n) (r := r) E j x :=
        (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from u).toLinearMap
      let p : Fin n → CotangentFiber (n := n) x := fun i ↦ EuclideanSpace.proj i
      let b : Fin n → TM x := fun i ↦ EuclideanSpace.single i 1
      let embed : CovariantTensorFiber (n := n) (r := r) E (j + 1) x →ₗ[ℝ]
          TensorProduct ℝ (CotangentFiber (n := n) x)
            (CovariantTensorFiber (n := n) (r := r) E j x) := {
        toFun := fun u ↦ ∑ i : Fin n, TensorProduct.tmul ℝ (p i) (view u (b i))
        map_add' := by
          intro u v
          have hval (i : Fin n) :
              view (u + v) (b i) = view u (b i) + view v (b i) := rfl
          simp only [hval, TensorProduct.tmul_add, Finset.sum_add_distrib]
        map_smul' := by
          intro c u
          have hval (i : Fin n) : view (c • u) (b i) = c • view u (b i) := rfl
          simp only [hval, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply] }
      -- Evaluation on each original tangent basis vector recovers every tensor coefficient.
      let recover (i : Fin n) :
          TensorProduct ℝ (CotangentFiber (n := n) x)
            (CovariantTensorFiber (n := n) (r := r) E j x) →ₗ[ℝ]
              CovariantTensorFiber (n := n) (r := r) E j x :=
        (TensorProduct.lid ℝ _).toLinearMap.comp
          (TensorProduct.map {
            toFun := fun ξ ↦ ξ (b i)
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl }
            (LinearMap.id : CovariantTensorFiber (n := n) (r := r) E j x →ₗ[ℝ] _))
      have hrecover (i : Fin n) (u : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          recover i (embed u) = view u (b i) := by
        have hterm (l : Fin n) :
            recover i (TensorProduct.tmul ℝ (p l) (view u (b l))) =
              (p l) (b i) • view u (b l) := rfl
        have hcoord (l : Fin n) : (p l) (b i) = if l = i then 1 else 0 := by
          change (EuclideanSpace.single i (1 : ℝ)) l = _
          simp [EuclideanSpace.single, eq_comm]
        change recover i (∑ l : Fin n, TensorProduct.tmul ℝ (p l) (view u (b l))) = _
        rw [map_sum]
        simp only [hterm, hcoord]
        simp
      have hinj : Function.Injective embed := by
        intro u v huv
        change (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from u) =
          (show TM x →L[ℝ] CovariantTensorFiber (n := n) (r := r) E j x from v)
        apply ContinuousLinearMap.ext
        intro w
        change view u w = view v w
        let w' : TModel := w
        have hw : (∑ i : Fin n, w' i • b i) = w := by
          change (∑ i : Fin n, w' i • EuclideanSpace.single i 1) = w'
          ext l
          simp [EuclideanSpace.single, Pi.single_apply]
        rw [← hw, map_sum, map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, map_smul]
        exact congrArg (fun z ↦ w' i • z)
          ((hrecover i u).symm.trans ((congrArg (recover i) huv).trans (hrecover i v)))
      -- Auxiliary norms are confined to this proof; the stored original Hom maps stay fixed.
      let : InnerProductSpace.Core ℝ (CovariantTensorFiber (n := n) (r := r) E j x) := c
      let : NormedAddCommGroup (CovariantTensorFiber (n := n) (r := r) E j x) :=
        c.toNormedAddCommGroup
      let : InnerProductSpace ℝ (CovariantTensorFiber (n := n) (r := r) E j x) :=
        InnerProductSpace.ofCore c.toCore
      have hformula (u v : CovariantTensorFiber (n := n) (r := r) E (j + 1) x) :
          inner ℝ (embed u) (embed v) = (iteratedCovariantPairing g h (j + 1) x u v).re := by
        simp only [embed, LinearMap.coe_mk, AddHom.coe_mk, sum_inner, inner_sum,
          TensorProduct.inner_tmul]
        rw [Finset.sum_comm]
        change (∑ i : Fin n, ∑ l : Fin n,
          g.inner x (p i) (p l) * c.inner (view u (b i)) (view v (b l))) = _
        simp only [hc, iteratedCovariantPairing, Complex.re_sum, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
        rfl
      refine ⟨{
        inner := fun u v ↦ inner ℝ (embed u) (embed v)
        conj_inner_symm := by
          intro u v
          change inner ℝ (embed v) (embed u) = inner ℝ (embed u) (embed v)
          exact real_inner_comm _ _
        re_inner_nonneg := by
          intro u
          change 0 ≤ inner ℝ (embed u) (embed u)
          exact real_inner_self_nonneg
        add_left := ?_
        smul_left := ?_
        definite := ?_ }, hformula⟩
      · intro u v w
        rw [embed.map_add, inner_add_left]
      · intro u v a
        rw [embed.map_smul, real_inner_smul_left]
        rfl
      · intro u hu
        apply hinj
        rw [embed.map_zero]
        exact (inner_self_eq_zero (𝕜 := ℝ)).mp hu
  obtain ⟨c, hc⟩ := cores k
  rw [← hc a a]
  constructor
  · exact c.definite a
  · rintro rfl
    let : InnerProductSpace.Core ℝ (CovariantTensorFiber (n := n) (r := r) E k x) := c
    exact InnerProductSpace.Core.inner_zero_left 0

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use the proved Hausdorff connection and derivative interfaces.
The historical outline below was not verified under the original weaker hypotheses.
This block defines no Lean constant.

/-- Smooth derivative tensors have a continuous original scalar contraction. -/
theorem continuous_iteratedCovariantPairing
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovE : CovariantDerivative.ContMDiffCovariantDerivative covE ∞)
    (k : ℕ) (u v : smoothSections (n := n) (r := r) E) :
    Continuous (fun x ↦ iteratedCovariantPairing g h k x
      (iteratedCovariantDerivative covT covE k u.val x)
      (iteratedCovariantDerivative covT covE k v.val x)) 
  /- Stage 1: the same basis-change cancellation as for positivity
  allows evaluation of the contraction in genuine smooth local tangent
  and complex value frames. No global smoothness of the raw coordinate
  basis is asserted.
  Stage 2: the actual iterated derivative sections are smooth, as are
  the coefficients of g and h. The finite sum of products of their
  coefficients is smooth locally, hence continuous globally. No compactness
  is needed for this continuity statement; integrability comes later. -/
-/

end AtiyahSinger
