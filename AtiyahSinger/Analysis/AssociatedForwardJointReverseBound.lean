/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasBundleIsoSobolev
public import AtiyahSinger.Analysis.GradedLeftColumnEllipticBound
public import AtiyahSinger.Analysis.HorizontalReverseGlobalMetricLowCone
public import AtiyahSinger.Analysis.VerticalRegularizationGlobalMetric

/-!
# The original forward joint graph controls H1 through its specified elliptic graded column

Public module ID: M0091.

Both original O/U/I regularizations enter the actual supplied native K through
full smooth conjugation identities. The fixed-Q vertical graph bounds for the
vertical regularization and the full horizontal error are used directly.
The resulting native first-column elliptic estimate is transported through the
same fiber isomorphisms and the original metric inclusions. Ellipticity of K
is an explicit hypothesis.
-/

@[expose] public noncomputable section

set_option Elab.async false

/- Abstract the solved goal as an auxiliary theorem, expanding free local let values. -/
open Lean Elab Tactic Meta in
local elab "as_aux_forward_joint_zeta" " => " seq:tacticSeq : tactic => withMainContext do
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
set_option maxHeartbeats 8000000 in
-- The extended limit accommodates the elliptic column and forward metric joint graph estimates.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified elliptic graded first column controls the original forward metric joint graph. -/
theorem associated_forward_joint_reverse_bound
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
        κ k j y = 1)
    (N₀ : ℕ) (Jbase : SmoothBundlePresentation (n := n) (r := a) E)
    (bv : Fin Jbase.size → B)
    (hJbase : ∀ k, tsupport (Jbase.cutoff k) ⊆ (S.trivialization (bv k)).baseSet)
    (Cov : ∀ k : Fin Jbase.size, Fin N₀ → BundleChartCutoff (r := a) E (Jbase.chart k))
    (hCov : ∀ k j, (Jbase.chart k).symm '' tsupport (Cov k j).cutoff ⊆
      (S.trivialization (bv k)).baseSet)
    (Ls : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      Fin N₀ → AtlasPseudodifferentialPiece
        (nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber)
        (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber) 1)
    (Kov : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
      Fin Jbase.size → ∀ j : Fin N₀,
        AtlasChartCutoff (nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber)
          (Ls j).chart) :
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
    let Dinv (k : Fin Jbase.size) (j : Fin N₀) :=
      associatedSphereTensorChartCutoff S E A σ hA (bv k) (Jbase.chart k) (Jbase.chartCutoff E k)
        (fun _ hx ↦ hJbase k (Jbase.chartCutoff_support_subset E k hx)) (Ls j).chart (Ls j).input
    let Doutv (k : Fin Jbase.size) (j : Fin N₀) :=
      associatedSphereTensorChartCutoff S E A' σ' hA' (bv k) (Jbase.chart k) (Cov k j)
        (hCov k j) (Ls j).chart (Kov k j)
    let β (j : Fin N₀) : SymbolFunction r (F.rank * a) (F'.rank * a) :=
      fun y η ↦ tensorIdentitySymbolMap F.rank F'.rank a
        (zeroExtendedSymbol Set.univ (Ls j).output.cutoff (Ls j).symbol y η)
    ∀ (I : Fin L.size → Fin J.size → AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
      (O : Fin L.size → Fin J.size →
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))) →ₗ[ℂ] AT'.smoothSections),
      (∀ k j w z, I k j w z = (Din k j).localizedFunction w z) →
      (∀ k j v z, (O k j v).val z = (Dout k j).extendedFunction v z) →
      ∀ (Iv : Fin Jbase.size → Fin N₀ → AT.smoothSections →ₗ[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
        (Ov : Fin Jbase.size → Fin N₀ →
          𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))) →ₗ[ℂ] ATv.smoothSections),
        (∀ k j w z, Iv k j w z = (Dinv k j).localizedFunction w z) →
        (∀ k j u z, (Ov k j u).val z = (Doutv k j).extendedFunction u z) →
        ∀ (Li : AtlasBundlePresentation AT) (_Lv : AtlasBundlePresentation ATv)
          (_Lh : AtlasBundlePresentation AT')
          (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
          (lv : ContinuousHermitianMetric Tv) (_hlv : ATv.IsSmoothHermitianMetric lv)
          (lh : ContinuousHermitianMetric T') (_hlh : AT'.IsSmoothHermitianMetric lh)
          (AS BS : Fin 2 → SmoothFiniteComplexBundle (n := n + r) Z)
          (kI : SmoothHermitianMetric (n := n + r) (r := (AS 0).rank) (AS 0).Fiber)
          (kV : SmoothHermitianMetric (n := n + r) (r := (BS 1).rank) (BS 1).Fiber)
          (kH : SmoothHermitianMetric (n := n + r) (r := (BS 0).rank) (BS 0).Fiber)
          (η : Measure Z) [IsSmoothPositiveMeasure (n := n + r) η],
          letI := modelTopology (EuclideanSpace ℂ (Fin (AS 0).rank)) (AS 0).Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin (BS 1).rank)) (BS 1).Fiber
          letI := modelTopology (EuclideanSpace ℂ (Fin (BS 0).rank)) (BS 0).Fiber
          ∀ (eI : Iso T (AS 0).Fiber)
            (heI : IsSmoothAtlasBundleMap AT (nativeSmoothComplexBundleAtlas (AS 0).Fiber)
              eI.toHom.linearMap)
            (hiI : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas (AS 0).Fiber) AT
              eI.symm.toHom.linearMap)
            (eV : Iso Tv (BS 1).Fiber)
            (heV : IsSmoothAtlasBundleMap ATv (nativeSmoothComplexBundleAtlas (BS 1).Fiber)
              eV.toHom.linearMap)
            (hiV : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas (BS 1).Fiber) ATv
              eV.symm.toHom.linearMap)
            (eH : Iso T' (BS 0).Fiber)
            (heH : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas (BS 0).Fiber)
              eH.toHom.linearMap)
            (hiH : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas (BS 0).Fiber) AT'
              eH.symm.toHom.linearMap),
            (∀ z v w, kI.pairing z (eI.linearEquiv z v) (eI.linearEquiv z w) =
              (l.toCore z).inner v w) →
            (∀ z v w, kV.pairing z (eV.linearEquiv z v) (eV.linearEquiv z w) =
              (lv.toCore z).inner v w) →
            (∀ z v w, kH.pairing z (eH.linearEquiv z v) (eH.linearEquiv z w) =
              (lh.toCore z).inner v w) →
            let SI := (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas (AS 0).Fiber)
              eI heI hiI).trans (nativeSmoothSectionLinearEquiv (AS 0).Fiber)
            let SV := (atlasSmoothSectionEquiv ATv (nativeSmoothComplexBundleAtlas (BS 1).Fiber)
              eV heV hiV).trans (nativeSmoothSectionLinearEquiv (BS 1).Fiber)
            let SH := (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas (BS 0).Fiber)
              eH heH hiH).trans (nativeSmoothSectionLinearEquiv (BS 0).Fiber)
            let i := (kI.smoothToL2 η).comp SI.toLinearMap
            let iv := (kV.smoothToL2 η).comp SV.toLinearMap
            let ih := (kH.smoothToL2 η).comp SH.toLinearMap
            ∀ (ε : ℝ), 0 < ε →
              ∀ (Uh : Fin L.size → Fin J.size →
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
                    𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))))
                (Uv : Fin Jbase.size → Fin N₀ →
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
                    𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank)))),
                (∀ k j u z, Uh k j u z = quantize
                  (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
                    (productCutoffSymbol (α k) (κ k j) ε x ξ)) u z) →
                (∀ k j u z, Uv k j u z = quantize
                  (rightProductCutoffSymbol (n := n) (m := r) (r := a)
                    (s := F.rank) (t := F'.rank) (β j) (Cov k j).cutoff ε) u z) →
                ∀ (NE NO : SmoothFiniteComplexBundle (n := n + r) Z)
                  (es : ∀ x, ((AS 0).Fiber x × (AS 1).Fiber x) ≃ₗ[ℂ] NE.Fiber x)
                  (fs : ∀ x, ((BS 0).Fiber x × (BS 1).Fiber x) ≃ₗ[ℂ] NO.Fiber x)
                  (hes₀ : IsSmoothBundleMap (n := n + r) (r := (AS 0).rank) (q := NE.rank)
                    (fun x ↦ (es x).toLinearMap.comp
                      (LinearMap.inl ℂ ((AS 0).Fiber x) ((AS 1).Fiber x))))
                  (hes₁ : IsSmoothBundleMap (n := n + r) (r := (AS 1).rank) (q := NE.rank)
                    (fun x ↦ (es x).toLinearMap.comp
                      (LinearMap.inr ℂ ((AS 0).Fiber x) ((AS 1).Fiber x))))
                  (hfs₀ : IsSmoothBundleMap (n := n + r) (r := (BS 0).rank) (q := NO.rank)
                    (fun x ↦ (fs x).toLinearMap.comp
                      (LinearMap.inl ℂ ((BS 0).Fiber x) ((BS 1).Fiber x))))
                  (hfs₁ : IsSmoothBundleMap (n := n + r) (r := (BS 1).rank) (q := NO.rank)
                    (fun x ↦ (fs x).toLinearMap.comp
                      (LinearMap.inr ℂ ((BS 0).Fiber x) ((BS 1).Fiber x))))
                  (Un : PseudodifferentialOperator (n := n + r) (r := (AS 0).rank)
                    (q := (BS 0).rank)
                    (AS 0).Fiber (BS 0).Fiber η 1)
                  (Vn : PseudodifferentialOperator (n := n + r) (r := (AS 0).rank)
                    (q := (BS 1).rank)
                    (AS 0).Fiber (BS 1).Fiber η 1)
                  (Wn : PseudodifferentialOperator (n := n + r) (r := (AS 1).rank)
                    (q := (BS 0).rank)
                    (AS 1).Fiber (BS 0).Fiber η 1)
                  (Zn : PseudodifferentialOperator (n := n + r) (r := (AS 1).rank)
                    (q := (BS 1).rank)
                    (AS 1).Fiber (BS 1).Fiber η 1)
                  (_DP : (i : Fin 2) → SmoothBundlePresentation (n := n + r)
                    (r := (AS i).rank) (AS i).Fiber)
                  (_HP : (j : Fin 2) → SmoothBundlePresentation (n := n + r)
                    (r := (BS j).rank) (BS j).Fiber)
                  (_SE : SmoothBundlePresentation (n := n + r) (r := NE.rank) NE.Fiber)
                  (_SO : SmoothBundlePresentation (n := n + r) (r := NO.rank) NO.Fiber)
                  (K : PseudodifferentialOperator (n := n + r) (r := NE.rank) (q := NO.rank)
                    NE.Fiber NO.Fiber η 1) (_hKell : K.IsElliptic),
                  let Φ := smoothSectionSumEquiv es hes₀ hes₁
                  let Ψ := smoothSectionSumEquiv fs hfs₀ hfs₁
                  (∀ u v, K.toLinearMap (Φ (u, v)) = Ψ
                    (Un.toLinearMap u - Wn.toLinearMap v,
                      Vn.toLinearMap u + Zn.toLinearMap v)) →
                  (∀ w, Un.toLinearMap (SI w) = SH (∑ k, ∑ j, O k j (Uh k j (I k j w)))) →
                  (∀ w, Vn.toLinearMap (SI w) = SV (∑ k, ∑ j, Ov k j (Uv k j (Iv k j w)))) →
                  ∃ C : ℝ, 0 ≤ C ∧ ∀ w : AT.smoothSections,
                    ‖Li.smoothToSobolev 1 w‖ ≤ C *
                      (‖i w‖ + ‖ih (L.horizontalLift S E A σ E' hA w)‖ + ‖iv (V w)‖) := by
  as_aux_forward_joint_zeta =>
    classical
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    have hHdata := horizontal_reverse_low_cone_global_metric_bound
      (n := n) (r := r) (a := a) (a' := a') (P := P) (B := B)
      (projection := projection) S E F σ hσ F' σ' hσ' E'
      ν kFiber kFiber' Q hQ hQell N' L J Co hCoFrame hCo hCoOne κ hκ hκK hκsupport hκone
    have hVdata := vertical_regularization_global_metric_bound
      (n := n) (r := r) (a := a) (P := P) (B := B) (projection := projection)
      S E F σ hσ F' σ' hσ' ν kFiber kFiber' Q hQ hQell N'
      N₀ Jbase bv hJbase Cov hCov J Ls Kov
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
    intro AT ATv AT' V J₀ Kout Din Dout α Dinv Doutv β I O hI hO Iv Ov hIv hOv
      Li Lv Lh l hl lv hlv lh hlh AS BS kI kV kH η hη
    let := modelTopology (EuclideanSpace ℂ (Fin (AS 0).rank)) (AS 0).Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin (BS 1).rank)) (BS 1).Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin (BS 0).rank)) (BS 0).Fiber
    intro eI heI hiI eV heV hiV eH heH hiH hpI hpV hpH SI SV SH i iv ih ε hε
      Uh Uv hUh hUv NE NO es fs hes₀ hes₁ hfs₀ hfs₁ Un Vn Wn Zn DP HP SE SO K hKell
      Φ Ψ hK hUn hVn
    have hHmetric := hHdata I O hI hO Li Lv Lh l hl lv hlv
      (AS 0) (BS 1) kI kV η eI heI hiI eV heV hiV hpI hpV ε hε
    have hVmetric := hVdata Iv Ov hIv hOv Li Lv l hl lv hlv
      (AS 0) (BS 1) kI kV η eI heI hiI eV heV hiV hpI hpV ε hε
    let cH : ℝ := hHmetric.choose
    have hcH : 0 ≤ cH := hHmetric.choose_spec.1
    have hHerr := hHmetric.choose_spec.2
    let cV : ℝ := hVmetric.choose
    have hcV : 0 ≤ cV := hVmetric.choose_spec.1
    have hVreg := hVmetric.choose_spec.2
    have hcolumnData := graded_left_column_elliptic_bound NE NO AS BS es fs
      hes₀ hes₁ hfs₀ hfs₁ Un Vn Wn Zn DP HP SE SO K hKell hK
    let cK : ℝ := hcolumnData.choose
    have hcK : 0 ≤ cK := hcolumnData.choose_spec.1
    have hcolumn := hcolumnData.choose_spec.2
    -- Continue with the same isomorphisms at H1 and H0, then the original metric comparisons.
    have hIsoI₁ := exists_atlasSmoothSectionEquiv_sobolev_comparison
      AT (nativeSmoothComplexBundleAtlas (AS 0).Fiber) eI heI hiI
      Li (DP 0).toAtlasBundlePresentation 1
    have hIsoI₀ := exists_atlasSmoothSectionEquiv_sobolev_comparison
      AT (nativeSmoothComplexBundleAtlas (AS 0).Fiber) eI heI hiI
      Li (DP 0).toAtlasBundlePresentation 0
    have hIsoH₀ := exists_atlasSmoothSectionEquiv_sobolev_comparison
      AT' (nativeSmoothComplexBundleAtlas (BS 0).Fiber) eH heH hiH
      Lh (HP 0).toAtlasBundlePresentation 0
    have hIsoV₀ := exists_atlasSmoothSectionEquiv_sobolev_comparison
      ATv (nativeSmoothComplexBundleAtlas (BS 1).Fiber) eV heV hiV
      Lv (HP 1).toAtlasBundlePresentation 0
    let a₁ : ℝ := hIsoI₁.choose
    have ha₁ : 0 ≤ a₁ := hIsoI₁.choose_spec.1
    have hbI₁ := hIsoI₁.choose_spec.2
    let a₀ : ℝ := hIsoI₀.choose
    have ha₀ : 0 ≤ a₀ := hIsoI₀.choose_spec.1
    have hbI₀ := hIsoI₀.choose_spec.2
    let b₀ : ℝ := hIsoH₀.choose
    have hb₀ : 0 ≤ b₀ := hIsoH₀.choose_spec.1
    have hbH₀ := hIsoH₀.choose_spec.2
    let d₀ : ℝ := hIsoV₀.choose
    have hd₀ : 0 ≤ d₀ := hIsoV₀.choose_spec.1
    have hbV₀ := hIsoV₀.choose_spec.2
    have hmiData := AT.exists_sobolevZero_l2_comparison
      Li l hl (AS 0) kI η eI heI hiI hpI
    let mi : ℝ := hmiData.choose
    have hmi : 0 < mi := hmiData.choose_spec.choose_spec.1
    have hmiB := hmiData.choose_spec.choose_spec.2.2
    have hmhData := AT'.exists_sobolevZero_l2_comparison
      Lh lh hlh (BS 0) kH η eH heH hiH hpH
    let mh : ℝ := hmhData.choose
    have hmh : 0 < mh := hmhData.choose_spec.choose_spec.1
    have hmhB := hmhData.choose_spec.choose_spec.2.2
    -- The native atlas isometry below keeps the actual native section values at each order.
    have hnative (N : SmoothFiniteComplexBundle (n := n + r) Z)
        (J : SmoothBundlePresentation (n := n + r) (r := N.rank) N.Fiber) (s : ℝ) :
        letI := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
        ∀ w : (nativeSmoothComplexBundleAtlas N.Fiber).smoothSections,
          ‖J.toAtlasBundlePresentation.smoothToSobolev s w‖ =
            ‖J.smoothToSobolev s (nativeSmoothSectionLinearEquiv N.Fiber w)‖ := by
      let := modelTopology (EuclideanSpace ℂ (Fin N.rank)) N.Fiber
      intro w
      have h := J.nativeAtlasSobolevEquiv_smoothToSobolev s
        (nativeSmoothSectionLinearEquiv N.Fiber w)
      have hn := congrArg (fun u ↦ ‖u‖) h
      simpa only [LinearIsometryEquiv.norm_map, LinearEquiv.symm_apply_apply] using hn.symm
    have hnativeI (s : ℝ) (w : AT.smoothSections) :
        ‖(DP 0).toAtlasBundlePresentation.smoothToSobolev s
          (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas (AS 0).Fiber)
            eI heI hiI w)‖ = ‖(DP 0).smoothToSobolev s (SI w)‖ := hnative (AS 0) (DP 0) s _
    have hnativeH (w : AT'.smoothSections) :
        ‖(HP 0).toAtlasBundlePresentation.smoothToSobolev 0
          (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas (BS 0).Fiber)
            eH heH hiH w)‖ = ‖(HP 0).smoothToSobolev 0 (SH w)‖ := hnative (BS 0) (HP 0) 0 _
    have hnativeV (w : ATv.smoothSections) :
        ‖(HP 1).toAtlasBundlePresentation.smoothToSobolev 0
          (atlasSmoothSectionEquiv ATv (nativeSmoothComplexBundleAtlas (BS 1).Fiber)
            eV heV hiV w)‖ = ‖(HP 1).smoothToSobolev 0 (SV w)‖ := hnative (BS 1) (HP 1) 0 _
    let total : ℝ := a₀ * mi + b₀ * (mh + cH) + d₀ * cV
    have htotal : 0 ≤ total := add_nonneg
      (add_nonneg (mul_nonneg ha₀ hmi.le) (mul_nonneg hb₀ (add_nonneg hmh.le hcH)))
      (mul_nonneg hd₀ hcV)
    refine ⟨a₁ * cK * total, mul_nonneg (mul_nonneg ha₁ hcK) htotal, ?_⟩
    intro w
    let g : ℝ := ‖i w‖ + ‖ih (L.horizontalLift S E A σ E' hA w)‖ + ‖iv (V w)‖
    have hx : ‖i w‖ ≤ g := by
      change ‖i w‖ ≤ ‖i w‖ + ‖ih (L.horizontalLift S E A σ E' hA w)‖ + ‖iv (V w)‖
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans
        (le_add_of_nonneg_right (norm_nonneg _))
    have hy : ‖ih (L.horizontalLift S E A σ E' hA w)‖ ≤ g := by
      exact (le_add_of_nonneg_left (norm_nonneg _)).trans
        (le_add_of_nonneg_right (norm_nonneg _))
    have hxz : ‖i w‖ + ‖iv (V w)‖ ≤ g := by
      have h := norm_nonneg (ih (L.horizontalLift S E A σ E' hA w))
      dsimp only [g]
      linarith only [h]
    have hleft : ‖Li.smoothToSobolev 1 w‖ ≤ a₁ * ‖(DP 0).smoothToSobolev 1 (SI w)‖ := by
      exact ((hbI₁ w).2).trans_eq (congrArg (fun x : ℝ ↦ a₁ * x) (hnativeI 1 w))
    have hin : ‖(DP 0).smoothToSobolev 0 (SI w)‖ ≤ (a₀ * mi) * g := by
      have h := (hnativeI 0 w).symm.trans_le (hbI₀ w).1
      exact (h.trans (mul_le_mul_of_nonneg_left
        ((hmiB w).1.trans (mul_le_mul_of_nonneg_left hx hmi.le)) ha₀)).trans_eq (by ring)
    let hr := ∑ k, ∑ j, O k j (Uh k j (I k j w))
    let vr := ∑ k, ∑ j, Ov k j (Uv k j (Iv k j w))
    have hhr : ‖Lh.smoothToSobolev 0 hr‖ ≤ (mh + cH) * g := by
      have hsplit : hr = L.horizontalLift S E A σ E' hA w -
          (L.horizontalLift S E A σ E' hA w - hr) := by abel
      have hmap := (congrArg (Lh.smoothToSobolev 0) hsplit).trans
        ((Lh.smoothToSobolev 0).map_sub _ _)
      have h₁ := (hmhB (L.horizontalLift S E A σ E' hA w)).1.trans
        (mul_le_mul_of_nonneg_left hy hmh.le)
      have h₂ := (hHerr Uh hUh w).trans (mul_le_mul_of_nonneg_left hxz hcH)
      have hn := norm_sub_le
        (Lh.smoothToSobolev 0 (L.horizontalLift S E A σ E' hA w))
        (Lh.smoothToSobolev 0 (L.horizontalLift S E A σ E' hA w - hr))
      exact ((congrArg norm hmap).trans_le (hn.trans (add_le_add h₁ h₂))).trans_eq (by ring)
    have hvr : ‖Lv.smoothToSobolev 0 vr‖ ≤ cV * g :=
      (hVreg Uv hUv w).trans (mul_le_mul_of_nonneg_left hxz hcV)
    have houtH : ‖(HP 0).smoothToSobolev 0 (Un.toLinearMap (SI w))‖ ≤
        (b₀ * (mh + cH)) * g := by
      have h := (hnativeH hr).symm.trans_le (hbH₀ hr).1
      have hn := congrArg (fun u ↦ ‖(HP 0).smoothToSobolev 0 u‖) (hUn w)
      exact (hn.trans_le (h.trans (mul_le_mul_of_nonneg_left hhr hb₀))).trans_eq (by ring)
    have houtV : ‖(HP 1).smoothToSobolev 0 (Vn.toLinearMap (SI w))‖ ≤
        (d₀ * cV) * g := by
      have h := (hnativeV vr).symm.trans_le (hbV₀ vr).1
      have hn := congrArg (fun u ↦ ‖(HP 1).smoothToSobolev 0 u‖) (hVn w)
      exact (hn.trans_le (h.trans (mul_le_mul_of_nonneg_left hvr hd₀))).trans_eq (by ring)
    have hsum := add_le_add (add_le_add hin houtH) houtV
    have hsum' : ‖(DP 0).smoothToSobolev 0 (SI w)‖ +
        ‖(HP 0).smoothToSobolev 0 (Un.toLinearMap (SI w))‖ +
        ‖(HP 1).smoothToSobolev 0 (Vn.toLinearMap (SI w))‖ ≤ total * g :=
      hsum.trans_eq (by dsimp [total]; ring)
    exact (hleft.trans (mul_le_mul_of_nonneg_left
      ((hcolumn (SI w)).trans (mul_le_mul_of_nonneg_left hsum' hcK)) ha₁)).trans_eq (by ring)

end AtiyahSinger
