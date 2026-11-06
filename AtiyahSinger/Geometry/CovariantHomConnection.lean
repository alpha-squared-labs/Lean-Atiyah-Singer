/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# The induced connection on the original tangent Hom bundle

Public module ID: M1157.

A01. Two actual connections, on TM and V, induce the usual connection on
Hom(TM,V). Its defining formula is
(nabla A)(X)(Y) = nabla_V(A(Y))(X) - A(nabla_TM(Y)(X)).
The cancellation of derivatives of a scalar multiplying Y makes this
operation tensorial in both X and Y. Mathlib's TensorialAt.mkHom₂ turns
that very operation into the continuous bilinear map on the original fibers.

The total-space topology and smooth bundle structure are the native Hom
bundle constructions. Non-differentiable input sections receive zero at
that point, following mathlib's convention for Levi-Civita construction;
all mathematical identities below concern differentiable sections there.
No family of higher derivative operators is an input. This is the standard
induced Hom connection needed to iterate the derivative in the integer
Sobolev norm of SG III.2, p.170, (2.1), and p.176, Proposition 2.14.
The displayed Hom formula is a standard explicit expansion of its
tensor-product connection, not an additional numbered lemma in the source.
The active smoothness theorem assumes a Hausdorff base and globalizes local
tangent frames. The statement without separation hypotheses is retained below
as an inactive, unverified mathematical outline.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped BigOperators Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EuclideanSpace ℝ (Fin n))]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "TM" => TangentSpace I (M := M)
local notation "TModel" => EuclideanSpace ℝ (Fin n)

variable (covT : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin n))
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : M → Type _))
  (covV : CovariantDerivative 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) F V)

/-- The standard Hom-connection formula before tensorial descent to the actual tangent fibers.
This implementation formula retains both supplied connections. -/
def covariantHomOperation (A : ∀ x : M, TM x →L[ℝ] V x) (x : M)
    (X Y : ∀ y : M, TM y) : V x :=
  covV (fun y ↦ A y (Y y)) x (X x) - A x (covT Y x (X x))

set_option linter.unusedSectionVars false in
/-- The displayed Hom formula is tensorial in the two tangent-field inputs.
This is the certificate used by the native tensoriality constructor. -/
theorem covariantHomOperation_tensorial
    (A : ∀ x : M, TM x →L[ℝ] V x) (x : M)
    (hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F))
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) x) :
    (∀ (Y : ∀ y : M, TM y),
      MDifferentiableAt I (I).tangent (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) x →
      TensorialAt I TModel (fun X ↦ covariantHomOperation covT covV A x X Y) x) ∧
    (∀ (X : ∀ y : M, TM y),
      MDifferentiableAt I (I).tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x →
      TensorialAt I TModel (covariantHomOperation covT covV A x X) x) := by
  /- Stage 1: dependence on X is through X(x) in two continuous linear
  maps, so the expression is pointwise real-linear in X.
  Stage 2: smooth evaluation in the original Hom bundle makes A(Y)
  differentiable when A and Y are. Apply the two real Leibniz rules
  to Y multiplied by a differentiable scalar f. The derivative-of-f
  terms are identical A(x)(Y(x)) contributions and cancel. Additivity
  follows from the two original connections and linearity of A.
  This proves tensoriality for the exact operation above, without
  choosing a new connection or extending an arbitrary tensor value. -/
  constructor
  · -- The first tangent argument is used only through its value at the base point.
    intro Y hY
    constructor
    · intro f X hf hX
      change covV (fun y ↦ A y (Y y)) x (f x • X x) -
          A x (covT Y x (f x • X x)) =
        f x • (covV (fun y ↦ A y (Y y)) x (X x) - A x (covT Y x (X x)))
      rw [map_smul, map_smul, map_smul, smul_sub]
    · intro X Z hX hZ
      simp only [covariantHomOperation, Pi.add_apply, map_add]
      abel
  · -- In the second argument, the two scalar-derivative terms cancel exactly.
    intro X hX
    constructor
    · intro f Y hf hY
      have hAY := hA.clm_bundle_apply hY
      have hmul : (fun y ↦ A y ((f • Y) y)) = f • (fun y ↦ A y (Y y)) := by
        funext y
        change A y (f y • Y y) = f y • A y (Y y)
        exact (A y).map_smul (f y) (Y y)
      simp only [covariantHomOperation, hmul,
        covV.isCovariantDerivativeOnUniv.leibniz hAY hf,
        covT.isCovariantDerivativeOnUniv.leibniz hY hf,
        add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      module
    · intro Y Z hY hZ
      have hAY := hA.clm_bundle_apply hY
      have hAZ := hA.clm_bundle_apply hZ
      have hadd : (fun y ↦ A y ((Y + Z) y)) =
          (fun y ↦ A y (Y y)) + (fun y ↦ A y (Z y)) := by
        funext y
        simp only [Pi.add_apply, map_add]
      simp only [covariantHomOperation, hadd,
        covV.isCovariantDerivativeOnUniv.add hAY hAZ,
        covT.isCovariantDerivativeOnUniv.add hY hZ,
        add_apply, map_add]
      abel

open Classical in
/-- The actual induced derivative on Hom sections, with zero as its nonsmooth junk value. -/
def covariantHomDerivative (A : ∀ x : M, TM x →L[ℝ] V x) (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] V x :=
  if hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F))
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) x then
    TensorialAt.mkHom₂ (covariantHomOperation covT covV A x) x
      (covariantHomOperation_tensorial covT covV A x hA).1
      (covariantHomOperation_tensorial covT covV A x hA).2
  else 0

/-- The explicit Hom derivative satisfies the native connection axioms. -/
theorem isCovariantDerivativeOn_covariantHomDerivative :
    IsCovariantDerivativeOn (TModel →L[ℝ] F) (covariantHomDerivative covT covV) := by
  /- Evaluate both sides of each connection axiom on values of smooth
  local tangent fields. The actual mkHom₂ specification returns the
  defining operation, independently of the chosen extensions.
  Additivity in the Hom section follows from covV and linearity.
  Multiplying A by a scalar f produces exactly df(X) times A(Y),
  in addition to f times the old expression. This is the Hom-bundle
  Leibniz rule. Every section appearing in these axioms is differentiable
  at the point, so the zero junk branch is never used. -/
  -- Evaluate the descended operation on differentiable representatives of each tangent value.
  have heval (A : ∀ y : M, TM y →L[ℝ] V y) (x : M)
      (hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F))
        (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
          (fun y ↦ TM y →L[ℝ] V y))) x)
      (X Y : ∀ y : M, TM y)
      (hX : MDifferentiableAt I (I).tangent
        (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
      (hY : MDifferentiableAt I (I).tangent
        (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
      covariantHomDerivative covT covV A x (X x) (Y x) =
        covariantHomOperation covT covV A x X Y := by
    simp only [covariantHomDerivative, dite_eq_left hA]
    exact TensorialAt.mkHom₂_apply _ _ hX hY
  constructor
  · intro A B x hA hB hx
    ext v w
    let X := FiberBundle.extend TModel v
    let Y := FiberBundle.extend TModel w
    have hXd := FiberBundle.mdifferentiableAt_extend I TModel v
    have hYd := FiberBundle.mdifferentiableAt_extend I TModel w
    have hsum := mdifferentiableAt_add_section hA hB
    have hAY := hA.clm_bundle_apply hYd
    have hBY := hB.clm_bundle_apply hYd
    have hsumY : (fun y ↦ (A + B) y (Y y)) =
        (fun y ↦ A y (Y y)) + (fun y ↦ B y (Y y)) := by
      funext y
      rfl
    -- All three evaluations use the same two representatives and the same two connections.
    change covariantHomDerivative covT covV (A + B) x v w =
      covariantHomDerivative covT covV A x v w + covariantHomDerivative covT covV B x v w
    have hXval : X x = v := by simp [X]
    have hYval : Y x = w := by simp [Y]
    rw [← hXval, ← hYval, heval _ _ hsum X Y hXd hYd,
      heval _ _ hA X Y hXd hYd, heval _ _ hB X Y hXd hYd]
    unfold covariantHomOperation
    rw [hsumY, covV.isCovariantDerivativeOnUniv.add hAY hBY]
    simp only [Pi.add_apply, add_apply]
    abel
  · intro A f x hA hf hx
    ext v w
    let X := FiberBundle.extend TModel v
    let Y := FiberBundle.extend TModel w
    have hXd := FiberBundle.mdifferentiableAt_extend I TModel v
    have hYd := FiberBundle.mdifferentiableAt_extend I TModel w
    have hmul := hf.smul_section hA
    have hAY := hA.clm_bundle_apply hYd
    have hmulY : (fun y ↦ (f • A) y (Y y)) = f • (fun y ↦ A y (Y y)) := by
      funext y
      rfl
    have hXval : X x = v := by simp [X]
    have hYval : Y x = w := by simp [Y]
    change covariantHomDerivative covT covV (f • A) x v w =
      f x • covariantHomDerivative covT covV A x v w +
        (mvfderiv I f x v) • (A x w)
    rw [← hXval, ← hYval, heval _ _ hmul X Y hXd hYd,
      heval _ _ hA X Y hXd hYd]
    -- Differentiating the Hom coefficient leaves precisely df(X) times the original A(Y).
    unfold covariantHomOperation
    rw [hmulY, covV.isCovariantDerivativeOnUniv.leibniz hAY hf]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    change f x • covV (fun y ↦ A y (Y y)) x (X x) +
        (mvfderiv I f x (X x)) • A x (Y x) - f x • A x (covT Y x (X x)) = _
    module

/-- The standard connection induced by the given tangent and value-bundle connections. -/
def covariantHomConnection :
    CovariantDerivative I (TModel →L[ℝ] F) (fun x ↦ TM x →L[ℝ] V x) where
  toFun := covariantHomDerivative covT covV
  isCovariantDerivativeOnUniv := isCovariantDerivativeOn_covariantHomDerivative covT covV

/-- On differentiable fields the induced connection has its original evaluation formula. -/
theorem covariantHomConnection_apply
    (A : ∀ x : M, TM x →L[ℝ] V x) (X Y : ∀ x : M, TM x) (x : M)
    (hA : MDifferentiableAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F))
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) x)
    (hX : MDifferentiableAt I (I).tangent (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)) x)
    (hY : MDifferentiableAt I (I).tangent (fun y ↦ (⟨y, Y y⟩ : TangentBundle I M)) x) :
    covariantHomConnection covT covV A x (X x) (Y x) =
      covV (fun y ↦ A y (Y y)) x (X x) - A x (covT Y x (X x)) := by
  /- The differentiability assumption selects the actual mkHom₂ branch.
  Its apply theorem identifies evaluation on X(x), Y(x) with the
  original two-field operation. Unfold that operation, preserving
  both connections and the same three original sections. -/
  change covariantHomDerivative covT covV A x (X x) (Y x) = _
  simp only [covariantHomDerivative, dite_eq_left hA]
  exact TensorialAt.mkHom₂_apply _ _ hX hY

/-
Inactive original statement, retained as documentation (2026-10-31).
Current consumers use the proved Hausdorff connection and derivative interfaces.
The historical outline below was not verified under the original weaker hypotheses.
This block defines no Lean constant.

/-- Smooth input connections give a smooth connection on the same native Hom bundle. -/
theorem contMDiff_covariantHomConnection
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovV : CovariantDerivative.ContMDiffCovariantDerivative covV ∞) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (covariantHomConnection covT covV) ∞ 
  /- Stage 1: work in original smooth local tangent and value frames.
  Evaluate the Hom formula on the smooth tangent frame fields. Native
  smoothness of covV and covT, together with smooth Hom evaluation,
  makes every resulting coefficient smooth.
  Stage 2: these are precisely the coefficients of the mkHom₂ map by
  its evaluation identity. The native Hom-bundle chart criterion turns
  smooth coefficients into smoothness of the induced derivative section.
  This outline does not justify applying the smooth-connection class, which
  tests globally smooth inputs, to tangent fields known to be smooth only
  locally. The active Hausdorff proof below uses bump functions to globalize
  those fields. Metric compatibility is not used. -/
-/

/-- A tangent-Hom section is smooth when its evaluations on one native local frame are smooth.
This finite-dimensional criterion also applies to successive Hom value bundles. -/
theorem contMDiffAt_tangentHom_of_localFrame
    (A : ∀ x : M, TM x →L[ℝ] V x) (x : M)
    (hA : ∀ a : Fin n,
      ContMDiffAt I ((I).prod 𝓘(ℝ, F)) ∞
        (fun y ↦ (⟨y, A y ((trivializationAt TModel TM x).symmL ℝ y
          (EuclideanSpace.single a 1))⟩ : TotalSpace F V)) x) :
    ContMDiffAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F)) ∞
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) x := by
  classical
  -- Trivialize the value bundle and retain the same local tangent basis in each coefficient.
  let t := trivializationAt TModel TM x
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hcoord (a : Fin n) : ContMDiffAt I 𝓘(ℝ, F) ∞
      (fun y ↦ e.continuousLinearMapAt ℝ y
        (A y (t.symmL ℝ y (EuclideanSpace.single a 1)))) x := by
    have hs := (e.contMDiffAt_section_iff he).mp (hA a)
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy _
  apply (contMDiffAt_hom_bundle _).mpr
  refine ⟨contMDiffAt_id, ?_⟩
  -- Reconstruct the full continuous linear map by its finitely many basis evaluations.
  have hsum : ContMDiffAt I 𝓘(ℝ, TModel →L[ℝ] F) ∞
      (fun y ↦ ∑ a : Fin n, (EuclideanSpace.proj a : TModel →L[ℝ] ℝ).smulRight
        (e.continuousLinearMapAt ℝ y
          (A y (t.symmL ℝ y (EuclideanSpace.single a 1))))) x := by
    apply ContMDiffAt.sum
    intro a _
    exact (ContinuousLinearMap.smulRightL ℝ TModel F
      (EuclideanSpace.proj a : TModel →L[ℝ] ℝ)).contMDiff
      |>.contMDiffAt.comp x (hcoord a)
  convert hsum using 1
  funext y
  ext v
  change e.continuousLinearMapAt ℝ y (A y (t.symmL ℝ y v)) = _
  have hv := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl

/-- On a Hausdorff base, smooth original connections induce a smooth native Hom connection.
The separation assumption globalizes local tangent fields before applying the smooth-connection
classes. -/
theorem contMDiff_covariantHomConnection_of_t2Space [T2Space M]
    (covT : CovariantDerivative I TModel TM)
    (covV : CovariantDerivative I F V)
    (hcovT : CovariantDerivative.ContMDiffCovariantDerivative covT ∞)
    (hcovV : CovariantDerivative.ContMDiffCovariantDerivative covV ∞) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (covariantHomConnection covT covV) ∞ := by
  classical
  refine ⟨⟨?_⟩⟩
  intro A hA
  have hAs : ContMDiff I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F)) ∞
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) := by
    apply contMDiffOn_univ.mp
    simpa using hA
  apply contMDiffOn_univ.mpr
  intro x
  let t := trivializationAt TModel TM x
  have ht : x ∈ t.baseSet := mem_baseSet_trivializationAt TModel TM x
  let X (a : Fin n) (y : M) : TM y := t.symmL ℝ y (EuclideanSpace.single a 1)
  have hX (a : Fin n) (y : M) (hy : y ∈ t.baseSet) :
      ContMDiffAt I (I).tangent ∞
        (fun z ↦ (⟨z, X a z⟩ : TangentBundle I M)) y := by
    apply (t.contMDiffAt_section_iff hy).mpr
    apply (contMDiffAt_const (c := EuclideanSpace.single a (1 : ℝ))).congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds hy] with z hz
    simp only [X, t.symmL_apply hz, t.apply_mk_symm hz]
  -- A single bump globalizes all coordinate directions on a common neighborhood.
  obtain ⟨ψ, _, hψ⟩ := (SmoothBumpFunction.nhds_basis_tsupport («I» := I) x).mem_iff.mp
    (t.open_baseSet.mem_nhds ht)
  let Y (a : Fin n) := (ψ : M → ℝ) • X a
  have hY (a : Fin n) : ContMDiff I (I).tangent ∞
      (fun y ↦ (⟨y, Y a y⟩ : TangentBundle I M)) := by
    exact ContMDiffOn.smul_section_of_tsupport ψ.contMDiff.contMDiffOn
      t.open_baseSet hψ (fun y hy ↦ (hX a y hy).contMDiffWithinAt)
  have hAY (a : Fin n) := hAs.clm_bundle_apply (hY a)
  have hTY (a : Fin n) := contMDiffOn_univ.mp
    (hcovT.contMDiff.contMDiff (by simpa using (hY a).contMDiffOn))
  have hVAY (a : Fin n) := contMDiffOn_univ.mp
    (hcovV.contMDiff.contMDiff (by simpa using (hAY a).contMDiffOn))
  -- Evaluation in both tangent slots determines the smooth Hom coordinates.
  apply contMDiffAt_tangentHom_of_localFrame
  intro a
  apply contMDiffAt_tangentHom_of_localFrame
  intro b
  have hs := ((hVAY b).contMDiffAt.clm_bundle_apply (hX a x ht)).sub_section
    (hAs.contMDiffAt.clm_bundle_apply
      ((hTY b).contMDiffAt.clm_bundle_apply (hX a x ht)))
  apply hs.congr_of_eventuallyEq
  filter_upwards [ψ.eventuallyEq_one.eventually_nhds, t.open_baseSet.mem_nhds ht]
    with y hψy hy
  have hYX : Y b y = X b y := by
    change ψ y • X b y = X b y
    rw [show ψ y = 1 from hψy.self_of_nhds, one_smul]
  congr 1
  change covariantHomConnection covT covV A y (X a y) (X b y) = _
  rw [← hYX, covariantHomConnection_apply covT covV A (X a) (Y b) y
    (hAs.mdifferentiableAt (by simp)) ((hX a y hy).mdifferentiableAt (by simp))
    ((hY b).mdifferentiableAt (by simp))]
  rfl

/-- Differentiability of a tangent-Hom section is detected on one native local tangent frame.
This version does not assume continuity of the derivative of the coefficients. -/
theorem mdifferentiableAt_tangentHom_of_localFrame
    (A : ∀ x : M, TM x →L[ℝ] V x) (x : M)
    (hA : ∀ a : Fin n,
      MDifferentiableAt I ((I).prod 𝓘(ℝ, F))
        (fun y ↦ (⟨y, A y ((trivializationAt TModel TM x).symmL ℝ y
          (EuclideanSpace.single a 1))⟩ : TotalSpace F V)) x) :
    MDifferentiableAt I ((I).prod 𝓘(ℝ, TModel →L[ℝ] F))
      (fun y ↦ (⟨y, A y⟩ : TotalSpace (TModel →L[ℝ] F)
        (fun y ↦ TM y →L[ℝ] V y))) x := by
  classical
  -- Read the finitely many evaluations in the same value trivialization.
  let t := trivializationAt TModel TM x
  let e := trivializationAt F V x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt F V x
  have hcoord (a : Fin n) : MDifferentiableAt I 𝓘(ℝ, F)
      (fun y ↦ e.continuousLinearMapAt ℝ y
        (A y (t.symmL ℝ y (EuclideanSpace.single a 1)))) x := by
    have hs := (e.mdifferentiableAt_section_iff I _ he).mp (hA a)
    apply hs.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds he] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy _
  apply (mdifferentiableAt_hom_bundle _).mpr
  refine ⟨mdifferentiableAt_id, ?_⟩
  -- The basis reconstruction is linear in these coefficients and preserves differentiability.
  have hsum : MDifferentiableAt I 𝓘(ℝ, TModel →L[ℝ] F)
      (fun y ↦ ∑ a : Fin n, (EuclideanSpace.proj a : TModel →L[ℝ] ℝ).smulRight
        (e.continuousLinearMapAt ℝ y
          (A y (t.symmL ℝ y (EuclideanSpace.single a 1))))) x := by
    have hh (a : Fin n) : MDifferentiableAt I 𝓘(ℝ, TModel →L[ℝ] F)
        (fun y ↦ (EuclideanSpace.proj a : TModel →L[ℝ] ℝ).smulRight
          (e.continuousLinearMapAt ℝ y
            (A y (t.symmL ℝ y (EuclideanSpace.single a 1))))) x :=
      (ContinuousLinearMap.smulRightL ℝ TModel F
        (EuclideanSpace.proj a : TModel →L[ℝ] ℝ)).mdifferentiableAt.comp x (hcoord a)
    convert (MDifferentiableAt.sum (t := Finset.univ) (fun a _ ↦ hh a)) using 1
    funext y
    simp only [Finset.sum_apply]
  convert hsum using 1
  funext y
  ext v
  change e.continuousLinearMapAt ℝ y (A y (t.symmL ℝ y v)) = _
  have hv := (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v
  conv_lhs => rw [← hv]
  simp only [map_sum, map_smul, EuclideanSpace.basisFun_apply,
    EuclideanSpace.basisFun_repr, sum_apply,
    ContinuousLinearMap.smulRight_apply]
  rfl


end AtiyahSinger
