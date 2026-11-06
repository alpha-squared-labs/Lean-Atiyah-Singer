/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorHorizontalFamily
public import AtiyahSinger.Analysis.AssociatedTensorLocalizedFiber

/-!
# Exact horizontal coordinates for controlled regularization

Public module ID: M0161.

The same compact whole-sphere family in the original principal chart supplies
Schwartz inputs for every finite coefficient contraction. Applying the original
base PDO to those exact inputs gives the coordinates of its actual horizontal
family, including the original output cutoff and complete left symbol. This is
the coordinate identity needed before the product-frequency cutoff estimate.

Source: the local operator construction in SG III.13.5--13.6. No joint symbol
estimate is imposed on the unregularized horizontal lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap Topology

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r a : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  (A : SmoothComplexBundleAtlas (n := r) F)
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space B]

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

set_option maxSynthPendingDepth 30 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full original horizontal family has its exact Fourier action in the supplied frames. -/
theorem exists_associatedSphereTensorHorizontalCutoffCoordinates {m : ℝ}
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' m)
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hσ).smoothSections,
      ∃ u : Xp → Fin a → A.smoothSections,
        (∀ (z : Xp) (i : Fin a), u z i =
          (L.input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
            associatedSphereTensorLocalFiberCoordinates S E A b L.input.frame
              L.input.frame_mem_atlas i
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
              (L.chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z))) ∧
        (∀ (i : Fin a) (j : A.Index),
          ContMDiffOn ((𝓘(ℝ, Xp)).prod (𝓡 r)) 𝓘(ℝ, Fin (A.rank j) → ℂ) ∞
            (fun z : Xp × OrthogonalSphere r ↦ (A.chart j ⟨z.2, (u z.1 i).val z.2⟩).2)
            (Set.univ ×ˢ (A.chart j).baseSet)) ∧
        (∀ z ∉ (EuclideanSpace.equiv (Fin n) ℝ) '' tsupport L.input.cutoff,
          ∀ i, u z i = 0) ∧
        ∀ (y : OrthogonalSphere r) (l : F y →ₗ[ℂ] ℂ),
          ∃ f : 𝓢(X, EuclideanSpace ℂ (Fin a)),
            (∀ (z : X) (i : Fin a), f z i =
              l ((u ((EuclideanSpace.equiv (Fin n) ℝ) z) i).val y)) ∧
            ∀ (x : B) (_hx : x ∈ L.chart.source) (_hf : x ∈ L.output.frame.baseSet),
              (L.output.frame ⟨x, TensorProduct.lid ℂ (E' x)
                (TensorProduct.map l LinearMap.id
                  ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
                    hχ hχsupport y w).val x))⟩).2 =
                (L.output.cutoff (L.chart x) : ℂ) • quantize L.symbol f (L.chart x) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  intro w
  -- Reuse the same normalized whole-fiber family, including every original support witness.
  obtain ⟨u, hu, huSmooth, huSupport, huDual⟩ :=
    exists_associatedSphereTensorLocalizedFiberFamily (a := a)
      S E A σ hσ b L.input L.chart_mem_atlas hinput χ hχ hχsupport hχone w
  refine ⟨u, hu, huSmooth, huSupport, ?_⟩
  intro y l
  let R := associatedSphereTensorCutoffBaseRestriction (a := a)
    S E A σ hσ b χ hχ hχsupport y w
  let s : smoothSections (n := n) (r := a) E :=
    ⟨fun x ↦ TensorProduct.lid ℂ (E x)
      (TensorProduct.map l LinearMap.id (R.val x)), R.property l⟩
  refine ⟨L.input.localize L.chart_mem_atlas s, ?_, ?_⟩
  · intro z i
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using
      huDual y l ((EuclideanSpace.equiv (Fin n) ℝ) z) i
  · intro x hx hf
    -- Dual contraction commutes with the base section operator.
    let e := A.frameLinearEquiv (A.covers y).choose y (A.covers y).choose_spec
    let : FiniteDimensional ℂ (F y) := .of_injective e.toLinearMap e.injective
    have hcontract :
        TensorProduct.lid ℂ (E' x) (TensorProduct.map l LinearMap.id
          ((associatedSphereTensorHorizontalFamily (a := a) S E A σ E' L hσ b χ
            hχ hχsupport y w).val x)) = (L.toLinearMap s).val x := by
      exact congrFun (tensorSectionOperator_contract (F y)
        (smoothSections E) (smoothSections E') L.toLinearMap R l) x
    rw [hcontract]
    -- The actual piece already fixes the Fourier normalization and the output frame.
    exact L.toLinearMap_in_frame s x hx hf

end AtiyahSinger
