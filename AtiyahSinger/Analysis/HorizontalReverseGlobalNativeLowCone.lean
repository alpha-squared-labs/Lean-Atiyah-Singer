/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HorizontalReverseNativeLowCone
public import AtiyahSinger.Analysis.AssociatedTensorHorizontalLift

import Mathlib.Algebra.Order.Chebyshev

/-!
# Native vertical control of the original complete horizontal cutoff error

Public module ID: M0753.

Assemble the reverse low-cone estimate. The original principal pieces,
centers and base cutoffs form exactly the supplied global horizontal lift. The
finite error sum is bounded by the same native whole-fiber families at those
centers. All intermediate finite norm estimates stay local to this actual bound.
-/

@[expose] public noncomputable section

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

variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z
local notation "Yc" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual complete horizontal cutoff error has the original native vertical energy bound. -/
theorem horizontal_reverse_low_cone_global_native_bound
    (L : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (J : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (Co : ∀ k : Fin L.size, BundleChartCutoff (r := a') E' (L.piece k).chart)
    (hCoFrame : ∀ k, (Co k).frame = (L.piece k).output.frame)
    (hCo : ∀ k, (L.piece k).chart.symm '' tsupport (Co k).cutoff ⊆
      (S.trivialization (L.center k)).baseSet)
    (hCoOne : ∀ k x, x ∈ tsupport (L.piece k).output.cutoff → (Co k).cutoff x = 1)
    (κ : Fin L.size → Fin J.size → Yc → ℝ)
    (hκ : ∀ k j, ContDiff ℝ ∞ (κ k j)) (hκK : ∀ k j, HasCompactSupport (κ k j))
    (hκsupport : ∀ k j, tsupport (κ k j) ⊆ (J.chart j).target ∩
      (J.chart j).symm ⁻¹' (J.frame j).baseSet)
    (hκone : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ k j y, y ∈ tsupport (J.toAtlasBundlePresentation.chartCutoff j).cutoff →
        κ k j y = 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
    let J₀ := J.toAtlasBundlePresentation
    let Kout (k : Fin L.size) (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
      ⟨J₀.frameIndex j, κ k j, hκ k j, hκK k j, hκsupport k j⟩
    let Din (k : Fin L.size) (j : Fin J.size) :=
      associatedSphereTensorChartCutoff S E A σ hA (L.center k) (L.piece k).chart
        (L.piece k).input (fun _ ⟨x, hx, hxy⟩ ↦
          L.piece_support k ⟨x, Or.inr hx, hxy⟩) (J.chart j) (J₀.chartCutoff j)
    let Dout (k : Fin L.size) (j : Fin J.size) :=
      associatedSphereTensorChartCutoff S E' A σ hA (L.center k) (L.piece k).chart
        (Co k) (hCo k) (J.chart j) (Kout k j)
    let α (k : Fin L.size) :=
      zeroExtendedSymbol Set.univ (L.piece k).output.cutoff (L.piece k).symbol
    ∀ (I : Fin L.size → Fin J.size → AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
      (O : Fin L.size → Fin J.size →
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))) →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
          ∀ U : Fin L.size → Fin J.size →
            𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))),
            (∀ k j v z, U k j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
                (productCutoffSymbol (α k) (κ k j) ε x ξ)) v z) →
            ∀ (w : AT.smoothSections)
              (u : Fin L.size → Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber),
              (∀ k x i, u k x i = nativeSmoothSectionLinearEquiv F.Fiber
                (((L.piece k).input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
                  associatedSphereTensorLocalFiberCoordinates S E A (L.center k)
                    (L.piece k).input.frame (L.piece k).input.frame_mem_atlas i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                    ((L.piece k).chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x)))) →
              ∀ hu : ∀ (k : Fin L.size) (i : Fin a),
                  MemLp (fun x ↦ J.smoothToSobolev 1 (u k x i)) 2 (volume : Measure Xp),
                ‖Lo.smoothToSobolev 0
                  (L.horizontalLift S E A σ E' hA w -
                    ∑ k, ∑ j, O k j (U k j (I k j w)))‖ ^ 2 ≤
                  C * ∑ k, ∑ i : Fin a,
                    ‖(hu k i).toLp (fun x ↦ J.smoothToSobolev 1 (u k x i))‖ ^ 2 := by
  classical
  have hinput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).input.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inr hx, hxy⟩
  have houtput (k : Fin L.size) :
      (L.piece k).chart.symm '' tsupport (L.piece k).output.cutoff ⊆
        (S.trivialization (L.center k)).baseSet :=
    fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inl hx, hxy⟩
  -- Apply the native vertical estimate to each localized principal piece.
  have hlocal (k : Fin L.size) := horizontal_reverse_low_cone_native_bound
    (n := n) (r := r) (a := a) (a' := a') (P := P) (B := B)
    (projection := projection) S E F σ hσ E' (L.piece k) (L.center k)
    (hinput k) (houtput k) (L.inputCutoff k) (L.smooth_inputCutoff k)
    (L.inputCutoff_support k) (L.inputCutoff_eq_one k)
    J (Co k) (hCoFrame k) (hCo k) (hCoOne k) (κ k) (hκ k) (hκK k)
    (hκsupport k) (hκone k)
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
  let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
  let H (k : Fin L.size) : AT.smoothSections →ₗ[ℂ] AT'.smoothSections :=
    associatedSphereTensorLocalHorizontalLift (a := a) S E A σ E' (L.piece k)
      hA (L.center k) (L.inputCutoff k) (L.smooth_inputCutoff k)
      (L.inputCutoff_support k) (houtput k)
  dsimp only
  intro I O hI hO Lo ε hε
  change AtlasBundlePresentation AT' at Lo
  have hdata (k : Fin L.size) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : Fin J.size →
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))),
        (∀ j v z, U j v z = quantize
          (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
            (productCutoffSymbol
              (zeroExtendedSymbol Set.univ (L.piece k).output.cutoff (L.piece k).symbol)
              (κ k j) ε x ξ)) v z) →
        ∀ (w : AT.smoothSections)
          (u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber),
          (∀ x i, u x i = nativeSmoothSectionLinearEquiv F.Fiber
            (((L.piece k).input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
              associatedSphereTensorLocalFiberCoordinates S E A (L.center k)
                (L.piece k).input.frame (L.piece k).input.frame_mem_atlas i
                (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                ((L.piece k).chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x)))) →
          ∀ hu : ∀ i : Fin a,
              MemLp (fun x ↦ J.smoothToSobolev 1 (u x i)) 2 (volume : Measure Xp),
            ‖Lo.smoothToSobolev 0 (H k w - ∑ j, O k j (U j (I k j w)))‖ ^ 2 ≤
              C * ∑ i : Fin a,
                ‖(hu i).toLp (fun x ↦ J.smoothToSobolev 1 (u x i))‖ ^ 2 :=
    hlocal k (I k) (O k) (hI k) (hO k) Lo ε hε
  let Ck (k : Fin L.size) : ℝ := (hdata k).choose
  have hCk (k : Fin L.size) : 0 ≤ Ck k := (hdata k).choose_spec.1
  have hbound (k : Fin L.size) := (hdata k).choose_spec.2
  let total : ℝ := ∑ k, Ck k
  have htotal : 0 ≤ total := Finset.sum_nonneg (fun k _ ↦ hCk k)
  refine ⟨L.size * total, mul_nonneg (Nat.cast_nonneg _) htotal, ?_⟩
  intro U hU w u hvalue hu
  let energy (k : Fin L.size) : ℝ :=
    ∑ i : Fin a, ‖(hu k i).toLp (fun x ↦ J.smoothToSobolev 1 (u k x i))‖ ^ 2
  have henergy (k : Fin L.size) : 0 ≤ energy k :=
    Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  let err (k : Fin L.size) : AT'.smoothSections :=
    H k w - ∑ j, O k j (U k j (I k j w))
  have herrbound (k : Fin L.size) :
      ‖Lo.smoothToSobolev 0 (err k)‖ ^ 2 ≤ Ck k * energy k :=
    hbound k (U k) (hU k) w (u k) (hvalue k) (hu k)
  -- The exact global lift and the specified regularization share this finite error sum.
  have hglobal : L.horizontalLift S E A σ E' hA w = ∑ k, H k w := by
    change (∑ k, H k) w = ∑ k, H k w
    exact LinearMap.sum_apply Finset.univ H w
  have herrsum : L.horizontalLift S E A σ E' hA w -
      ∑ k, ∑ j, O k j (U k j (I k j w)) = ∑ k, err k := by
    rw [hglobal, ← Finset.sum_sub_distrib]
  have hmapped := congrArg (Lo.smoothToSobolev 0) herrsum
  have hmapSum := map_sum (Lo.smoothToSobolev 0) err Finset.univ
  have hnorm := congrArg (fun v : Lo.SobolevSpace 0 ↦ ‖v‖ ^ 2) (hmapped.trans hmapSum)
  -- Nonnegative local constants and the finite Hilbert norm inequality give one global constant.
  have htriangle := norm_sum_le Finset.univ (fun k ↦ Lo.smoothToSobolev 0 (err k))
  have hsquare := pow_le_pow_left₀
    (norm_nonneg (∑ k, Lo.smoothToSobolev 0 (err k))) htriangle 2
  have hcard := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
    (f := fun k : Fin L.size ↦ ‖Lo.smoothToSobolev 0 (err k)‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  have hsumBound := hsquare.trans hcard
  have hCk_le (k : Fin L.size) : Ck k ≤ total :=
    Finset.single_le_sum (fun j _ ↦ hCk j) (Finset.mem_univ k)
  have hsum₁ := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ herrbound k)
  have hsum₂ := Finset.sum_le_sum (s := Finset.univ)
    (fun k _ ↦ mul_le_mul_of_nonneg_right (hCk_le k) (henergy k))
  have hscaled := mul_le_mul_of_nonneg_left (hsum₁.trans hsum₂) (Nat.cast_nonneg L.size)
  have hscalar : (L.size : ℝ) * (∑ k, total * energy k) =
      (L.size * total) * ∑ k, energy k := by
    rw [← Finset.mul_sum, mul_assoc]
  exact hnorm.trans_le ((hsumBound.trans hscaled).trans_eq hscalar)

end AtiyahSinger
