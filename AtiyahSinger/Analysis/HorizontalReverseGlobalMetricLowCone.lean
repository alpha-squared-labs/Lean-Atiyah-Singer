/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalEstimate
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.NativePresentationChartCutoff
public import AtiyahSinger.Analysis.HorizontalReverseGlobalNativeLowCone

/-!
# The original horizontal regularization error is controlled by the metric vertical graph

Public module ID: M0752.

The unchanged principal input cutoff determines each native whole-fiber row.
The actual global vertical operator controls these rows by the same specified
metric inclusions. Their finite squared-norm sum controls the original complete
horizontal regularization error in the supplied output Sobolev model.
-/

@[expose] public noncomputable section

set_option Elab.async false

/- After completing the tactic proof, expand free local let values when
packaging it as an auxiliary theorem. -/
open Lean Elab Tactic Meta in
local elab "as_aux_horizontal_metric_zeta" " => " seq:tacticSeq : tactic => withMainContext do
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
local notation "Tv" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Yc" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

variable {a' : ℕ}
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']

local notation "T'" => fun z : Z ↦ E' (πS z) ⊗[ℂ] D z

variable [SecondCountableTopology B] [CompactSpace B] [MeasurableSpace B] [BorelSpace B]
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

set_option maxSynthPendingDepth 40 in
set_option cleanup.letToHave false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- The extended limit accommodates the global metric graph and low-cone cutoff estimates.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original metric vertical graph controls the full horizontal cutoff error. -/
theorem horizontal_reverse_low_cone_global_metric_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (kFiber : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (kFiber' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic)
    (N' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
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
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    let hQA := (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit Tv) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hA
    let ATv := associatedSphereTensorBundleAtlas (a := a) S E A' σ' hA'
    let AT' := associatedSphereTensorBundleAtlas (a := a') S E' A σ hA
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
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
      ∀ (_Li : AtlasBundlePresentation AT) (_Lv : AtlasBundlePresentation ATv)
        (Lo : AtlasBundlePresentation AT')
        (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
        (l' : ContinuousHermitianMetric Tv) (_hl' : ATv.IsSmoothHermitianMetric l')
        (Ng Ng' : SmoothFiniteComplexBundle (n := n + r) Z)
        (kGlobal : SmoothHermitianMetric (n := n + r) (r := Ng.rank) Ng.Fiber)
        (kGlobal' : SmoothHermitianMetric (n := n + r) (r := Ng'.rank) Ng'.Fiber)
        (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
        letI := modelTopology (EuclideanSpace ℂ (Fin Ng.rank)) Ng.Fiber
        letI := modelTopology (EuclideanSpace ℂ (Fin Ng'.rank)) Ng'.Fiber
        ∀ (e : Iso T Ng.Fiber)
          (he : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas Ng.Fiber)
            e.toHom.linearMap)
          (hi : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas Ng.Fiber) AT
            e.symm.toHom.linearMap)
          (e' : Iso Tv Ng'.Fiber)
          (he' : IsSmoothAtlasBundleMap ATv (nativeSmoothComplexBundleAtlas Ng'.Fiber)
            e'.toHom.linearMap)
          (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas Ng'.Fiber) ATv
            e'.symm.toHom.linearMap),
          (∀ (z : Z) (v w : T z),
            kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
              (l.toCore z).inner v w) →
          (∀ (z : Z) (v w : Tv z),
            kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
              (l'.toCore z).inner v w) →
          let sectionEquiv :=
            (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas Ng.Fiber) e he hi).trans
              (nativeSmoothSectionLinearEquiv Ng.Fiber)
          let sectionEquiv' :=
            (atlasSmoothSectionEquiv ATv (nativeSmoothComplexBundleAtlas Ng'.Fiber)
              e' he' hi').trans (nativeSmoothSectionLinearEquiv Ng'.Fiber)
          let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
          let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
            ∀ U : Fin L.size → Fin J.size →
                𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
                  𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))),
              (∀ k j v z, U k j v z = quantize
                (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
                  (productCutoffSymbol (α k) (κ k j) ε x ξ)) v z) →
              ∀ w : AT.smoothSections,
                ‖Lo.smoothToSobolev 0
                  (L.horizontalLift S E A σ E' hA w -
                    ∑ k, ∑ j, O k j (U k j (I k j w)))‖ ≤
                  C * (‖inclusion w‖ + ‖inclusion' (V w)‖) := by
  as_aux_horizontal_metric_zeta =>
    classical
    have hsqrt (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
        (h : x ^ 2 ≤ c * y ^ 2) : x ≤ Real.sqrt c * y := by
      apply (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) hy)).mp
      simpa only [mul_pow, Real.sq_sqrt hc] using h
    have hinput (k : Fin L.size) :
        (L.piece k).chart.symm '' tsupport (L.piece k).input.cutoff ⊆
          (S.trivialization (L.center k)).baseSet :=
      fun _ ⟨x, hx, hxy⟩ ↦ L.piece_support k ⟨x, Or.inr hx, hxy⟩
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    -- The original principal plateau and original input determine each whole-fiber family.
    have hfamily (k : Fin L.size) :=
      exists_associatedSphereTensorLocalizedVertical_global_sobolev_bound (a := a)
        S E F F' σ σ' hσ hσ' kFiber kFiber' ν Q hQ hQell J N' (L.center k)
        (L.piece k).input (L.piece k).chart_mem_atlas (hinput k)
        (L.inputCutoff k) (L.smooth_inputCutoff k)
        (L.inputCutoff_support k) (L.inputCutoff_eq_one k)
    have hnative := horizontal_reverse_low_cone_global_native_bound
      (n := n) (r := r) (a := a) (a' := a') (P := P) (B := B) (projection := projection)
      S E F σ hσ E' L J Co hCoFrame hCo hCoOne κ hκ hκK hκsupport hκone
    intro A A' hA hA' QA hQA
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let := modelTopology (EuclideanSpace ℂ (Fin a')) E'
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    let : TopologicalSpace (TotalSpace Unit Tv) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E') (F := D)
    let := associatedSphereChartedSpace S
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let := linearModelChartedSpace split.symm Z
    let := isManifold_linearModelChartedSpace split.symm Z
    intro AT ATv AT' V J₀ Kout Din Dout α I O hI hO Li Lv Lo l hl l' hl'
      Ng Ng' kGlobal kGlobal' η hη
    let := modelTopology (EuclideanSpace ℂ (Fin Ng.rank)) Ng.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin Ng'.rank)) Ng'.Fiber
    intro e he hi e' he' hi' hpair hpair' sectionEquiv sectionEquiv' inclusion inclusion' ε hε
    have hmetricData (k : Fin L.size) := (hfamily k).choose_spec
      Li Lv l hl l' hl' Ng Ng' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
    let Ck (k : Fin L.size) : ℝ := (hmetricData k).choose
    have hCk (k : Fin L.size) : 0 ≤ Ck k := (hmetricData k).choose_spec.1
    have hf (k : Fin L.size) := (hmetricData k).choose_spec.2
    have hnativeData := hnative I O hI hO Lo ε hε
    let cN : ℝ := hnativeData.choose
    have hcN : 0 ≤ cN := hnativeData.choose_spec.1
    have hn := hnativeData.choose_spec.2
    let total : ℝ := (a : ℝ) * ∑ k : Fin L.size, Ck k ^ 2
    have htotal : 0 ≤ total := mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun k _ ↦ sq_nonneg _))
    refine ⟨Real.sqrt (cN * total), Real.sqrt_nonneg _, ?_⟩
    intro U hU w
    -- Both estimates receive precisely the same native rows and their MemLp witnesses.
    let u (k : Fin L.size) : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
      (hf k w).choose
    have hvalue (k : Fin L.size) := (hf k w).choose_spec.1
    let hu (k : Fin L.size) := (hf k w).choose_spec.2.choose
    have hb (k : Fin L.size) := (hf k w).choose_spec.2.choose_spec
    have hnorm := hn U hU w u hvalue hu
    let v : ℝ := ‖inclusion w‖ + ‖inclusion' (V w)‖
    have hv : 0 ≤ v := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hrow (k : Fin L.size) (i : Fin a) :
        ‖(hu k i).toLp (fun x ↦ J.smoothToSobolev 1 (u k x i))‖ ^ 2 ≤ Ck k ^ 2 * v ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (hb k i) 2).trans_eq (mul_pow _ _ 2)
    have hsum : (∑ k, ∑ i : Fin a,
        ‖(hu k i).toLp (fun x ↦ J.smoothToSobolev 1 (u k x i))‖ ^ 2) ≤ total * v ^ 2 := by
      calc
        _ ≤ ∑ k : Fin L.size, ∑ i : Fin a, Ck k ^ 2 * v ^ 2 :=
          Finset.sum_le_sum (fun k _ ↦ Finset.sum_le_sum (fun i _ ↦ hrow k i))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.sum_mul, total, mul_assoc]
    have hsq := hnorm.trans (mul_le_mul_of_nonneg_left hsum hcN)
    have hsq' := hsq.trans_eq (mul_assoc cN total (v ^ 2)).symm
    exact hsqrt _ v (cN * total) (norm_nonneg _) hv (mul_nonneg hcN htotal) hsq'

end AtiyahSinger
