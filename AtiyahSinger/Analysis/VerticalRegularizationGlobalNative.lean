/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.VerticalRegularizationNativeSource
public import AtiyahSinger.Analysis.AssociatedChartExtensionSupport
public import AtiyahSinger.Analysis.AssociatedTensorVerticalRegularization
public import AtiyahSinger.Analysis.AssociatedTensorSupportedReturnBound
public import AtiyahSinger.Analysis.AssociatedTensorVerticalCoordinateEnergy
public import AtiyahSinger.Analysis.NativePresentationChartCutoff

import Mathlib.Algebra.Order.Chebyshev

/-!
# The actual vertical regularization is bounded by its original native fiber family

Public module ID: M1049.

The given I/O/U maps retain their original product coordinates. Spatial estimates
control the actual right cutoff, arbitrary original sphere cutoffs are bounded in
the fixed native fiber norm, and the actual output chart is returned at order zero.
No unregularized vertical map is declared to be a joint pseudodifferential operator.
-/

@[expose] public noncomputable section

set_option Elab.async false


open Lean Elab Tactic Meta in
local elab "as_aux_global_native_zeta" " => " seq:tacticSeq : tactic => withMainContext do
  let goal ← getMainGoal
  let remaining ← Tactic.run goal (evalTactic seq)
  unless remaining.isEmpty do
    throwError "Cannot abstract an unfinished native bound"
  let value ← instantiateMVars (mkMVar goal)
  if value.hasSorry then
    throwError "Native bound contains an error-recovery admission"
  let value ← mkAuxTheorem (← goal.getType) value (zetaDelta := true)
  goal.assign value

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

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
  (F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  [T2Space B]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D" => AssociatedEquivariantFiber (E := F.Fiber) S.toIsPrincipalBundle σ
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable (F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))

local notation "D'" => AssociatedEquivariantFiber (E := F'.Fiber) S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Yc" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

omit [T2Space B] in
set_option maxSynthPendingDepth 40 in
set_option cleanup.letToHave false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2400000 in
-- The finite sum uses the prescribed output maps and the same native row families.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual finite vertical regularization is bounded by the original native row families. -/
theorem vertical_regularization_global_native_bound
    (N₀ : ℕ) (J : SmoothBundlePresentation (n := n) (r := a) E)
    (b : Fin J.size → B)
    (hJ : ∀ k, tsupport (J.cutoff k) ⊆ (S.trivialization (b k)).baseSet)
    (Co : ∀ k : Fin J.size, Fin N₀ → BundleChartCutoff (r := a) E (J.chart k))
    (hCo : ∀ k j, (J.chart k).symm '' tsupport (Co k j).cutoff ⊆
      (S.trivialization (b k)).baseSet)
    (N : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      Fin N₀ → AtlasPseudodifferentialPiece
        (nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber)
        (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber) 1)
    (Ko : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      Fin J.size → ∀ j : Fin N₀,
        AtlasChartCutoff (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber)
          (L j).chart) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native 𝓘(ℝ, OrthogonalGroupModel r) hσ
    let hA' := σ'.isSmoothAtlas_native 𝓘(ℝ, OrthogonalGroupModel r) hσ'
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    let AT' := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
    let Din (k : Fin J.size) (j : Fin N₀) :=
      associatedSphereTensorChartCutoff S E A σ hA (b k) (J.chart k) (J.chartCutoff E k)
        (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) (L j).chart (L j).input
    let Dout (k : Fin J.size) (j : Fin N₀) :=
      associatedSphereTensorChartCutoff S E A' σ' hA' (b k) (J.chart k) (Co k j)
        (hCo k j) (L j).chart (Ko k j)
    let β (j : Fin N₀) : SymbolFunction r (F.rank * a) (F'.rank * a) :=
      fun y η ↦ tensorIdentitySymbolMap F.rank F'.rank a
        (zeroExtendedSymbol Set.univ (L j).output.cutoff (L j).symbol y η)
    ∀ (I : Fin J.size → Fin N₀ → AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
      (O : Fin J.size → Fin N₀ →
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))) →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT')
        (ε : ℝ), 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
          ∀ U : Fin J.size → Fin N₀ →
              𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
                𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))),
            (∀ k j v z, U k j v z = quantize
              (rightProductCutoffSymbol (n := n) (m := r) (r := a)
                (s := F.rank) (t := F'.rank) (β j) (Co k j).cutoff ε) v z) →
            ∀ (w : AT.smoothSections)
              (u : Fin J.size → Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber),
              (∀ k x i, u k x i = nativeSmoothSectionLinearEquiv (n := r) (r := F.rank) F.Fiber
                (((J.chartCutoff E k).cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
                  associatedSphereTensorLocalFiberCoordinates S E A (b k) (J.frame k)
                    (J.frame_mem_atlas k) i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                    ((J.chart k).symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x)))) →
              ∀ hu : ∀ k : Fin J.size, ∀ i : Fin a,
                  MemLp (fun x ↦ N.smoothToSobolev 1 (u k x i)) 2 (volume : Measure Xp),
                ‖Lo.smoothToSobolev 0 (∑ k, ∑ j, O k j (U k j (I k j w)))‖ ^ 2 ≤
                  K * ∑ k : Fin J.size, ∑ i : Fin a,
                    ‖(hu k i).toLp (fun x ↦ N.smoothToSobolev 1 (u k x i))‖ ^ 2 := by
  as_aux_global_native_zeta =>
    classical
    -- Bound the norm of the finite sum by the summed row energies.
    have hfinite {𝓔 : Type} [NormedAddCommGroup 𝓔] {q₁ q₂ : ℕ}
        (v : Fin q₁ → Fin q₂ → 𝓔) (c : Fin q₁ → Fin q₂ → ℝ)
        (en : Fin q₁ → ℝ) (hc : ∀ k j, 0 ≤ c k j) (hen : ∀ k, 0 ≤ en k)
        (hb : ∀ k j, ‖v k j‖ ^ 2 ≤ c k j * en k) :
        ‖∑ k, ∑ j, v k j‖ ^ 2 ≤
          ((q₁ * q₂ : ℝ) * (∑ k, ∑ j, c k j)) * ∑ k, en k := by
      let v₀ (i : Fin q₁ × Fin q₂) := v i.1 i.2
      have ht := norm_sum_le Finset.univ v₀
      have hs := pow_le_pow_left₀ (norm_nonneg (∑ i, v₀ i)) ht 2
      have hcard := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
        (f := fun i : Fin q₁ × Fin q₂ ↦ ‖v₀ i‖)
      simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hcard
      have hsum := Finset.sum_le_sum (s := Finset.univ)
        (fun (i : Fin q₁ × Fin q₂) _ ↦ (hb i.1 i.2).trans (mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (fun k _ ↦ hen k) (Finset.mem_univ i.1)) (hc i.1 i.2)))
      have hscaled := mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (Nat.cast_nonneg q₁) (Nat.cast_nonneg q₂))
      have hresult := (hs.trans hcard).trans hscaled
      simpa only [v₀, Fintype.sum_prod_type, ← Finset.sum_mul, mul_assoc] using hresult
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    intro A A' hA hA'
    have hlocal (k : Fin J.size) (j : Fin N₀) := vertical_regularization_native_source_bound
      (n := n) (r := r) (a := a) (P := P) (B := B) (projection := projection)
      S E F σ hσ F' σ' hσ' (b k) (J.chart k) (J.chart_mem_atlas k)
      (J.chartCutoff E k) (Co k j)
      (fun _ hx ↦ hJ k (J.chartCutoff_support_subset E k hx)) (hCo k j) N (L j) (Ko k j)
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    let := associatedSphereChartedSpace S
    let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let := linearModelChartedSpace e.symm Z
    let := isManifold_linearModelChartedSpace e.symm Z
    intro AT AT' Din Dout β I O hI hO Lo ε hε
    change AtlasBundlePresentation AT' at Lo
    have hdata (k : Fin J.size) (j : Fin N₀) :=
      hlocal k j (I k j) (O k j) (hI k j) (hO k j) Lo ε hε
    let K (k : Fin J.size) (j : Fin N₀) : ℝ := (hdata k j).choose
    have hK (k : Fin J.size) (j : Fin N₀) : 0 ≤ K k j := (hdata k j).choose_spec.1
    have hbound (k : Fin J.size) (j : Fin N₀) := (hdata k j).choose_spec.2
    refine ⟨(J.size * N₀ : ℝ) * (∑ k, ∑ j, K k j),
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Finset.sum_nonneg (fun k _ ↦ Finset.sum_nonneg (fun j _ ↦ hK k j))), ?_⟩
    intro U hU w u hvalue hu
    let v (k : Fin J.size) (j : Fin N₀) : Lo.SobolevSpace 0 :=
      Lo.smoothToSobolev 0 (O k j (U k j (I k j w)))
    let en (k : Fin J.size) : ℝ :=
      ∑ i : Fin a, ‖(hu k i).toLp (fun x ↦ N.smoothToSobolev 1 (u k x i))‖ ^ 2
    have hen (k : Fin J.size) : 0 ≤ en k := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
    have hb (k : Fin J.size) (j : Fin N₀) : ‖v k j‖ ^ 2 ≤ K k j * en k :=
      hbound k j (U k j) (hU k j) w (u k) (hvalue k) (hu k)
    have hsum : Lo.smoothToSobolev 0 (∑ k, ∑ j, O k j (U k j (I k j w))) =
        ∑ k, ∑ j, v k j := by simp only [map_sum, v]
    have hnorm := congrArg (fun z : Lo.SobolevSpace 0 ↦ ‖z‖ ^ 2) hsum
    exact hnorm.trans_le (hfinite (𝓔 := Lo.SobolevSpace 0) v K en hK hen hb)

end AtiyahSinger
