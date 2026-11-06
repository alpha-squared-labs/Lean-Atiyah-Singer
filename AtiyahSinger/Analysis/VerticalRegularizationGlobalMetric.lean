/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorGlobalVerticalEstimate
public import AtiyahSinger.Analysis.CompactLocalSymbolCalculus
public import AtiyahSinger.Analysis.NativePresentationChartCutoff
public import AtiyahSinger.Analysis.VerticalRegularizationGlobalNative

/-!
# The specified finite vertical regularization is controlled by the original metric graph

Public module ID: M1048.

The original whole-sphere elliptic estimate supplies native H¹ families for each
unchanged base cutoff. These same pointwise rows enter the finite
regularization bound. One finite scalar estimate gives the global metric graph
bound, retaining the actual Q, I/O/U maps and both native metric isomorphisms.
-/

@[expose] public noncomputable section

set_option Elab.async false


open Lean Elab Tactic Meta in
local elab "as_aux_global_metric_zeta" " => " seq:tacticSeq : tactic => withMainContext do
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

variable [CompactSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [MeasurableSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [BorelSpace
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option cleanup.letToHave false in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
-- Retain the same native whole-fiber rows and both actual global metric identifications.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The actual finite vertical regularization is bounded by the original global metric graph. -/
theorem vertical_regularization_global_metric_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (kFiber : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
    (kFiber' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic)
    (N' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
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
    let QA := Q.toAtlasPseudodifferentialOperator
    let hQA := (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
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
    let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
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
      ∀ (_Li : AtlasBundlePresentation AT) (Lo : AtlasBundlePresentation AT')
        (l : ContinuousHermitianMetric T) (_hl : AT.IsSmoothHermitianMetric l)
        (l' : ContinuousHermitianMetric T') (_hl' : AT'.IsSmoothHermitianMetric l')
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
          (e' : Iso T' Ng'.Fiber)
          (he' : IsSmoothAtlasBundleMap AT' (nativeSmoothComplexBundleAtlas Ng'.Fiber)
            e'.toHom.linearMap)
          (hi' : IsSmoothAtlasBundleMap (nativeSmoothComplexBundleAtlas Ng'.Fiber) AT'
            e'.symm.toHom.linearMap),
          (∀ (z : Z) (v w : T z),
            kGlobal.pairing z (e.linearEquiv z v) (e.linearEquiv z w) =
              (l.toCore z).inner v w) →
          (∀ (z : Z) (v w : T' z),
            kGlobal'.pairing z (e'.linearEquiv z v) (e'.linearEquiv z w) =
              (l'.toCore z).inner v w) →
          let sectionEquiv :=
            (atlasSmoothSectionEquiv AT (nativeSmoothComplexBundleAtlas Ng.Fiber) e he hi).trans
              (nativeSmoothSectionLinearEquiv Ng.Fiber)
          let sectionEquiv' :=
            (atlasSmoothSectionEquiv AT' (nativeSmoothComplexBundleAtlas Ng'.Fiber)
              e' he' hi').trans (nativeSmoothSectionLinearEquiv Ng'.Fiber)
          let inclusion := (kGlobal.smoothToL2 η).comp sectionEquiv.toLinearMap
          let inclusion' := (kGlobal'.smoothToL2 η).comp sectionEquiv'.toLinearMap
          ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
            ∀ U : Fin J.size → Fin N₀ →
                𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
                  𝓢(XY, EuclideanSpace ℂ (Fin (a * F'.rank))),
              (∀ k j v z, U k j v z = quantize
                (rightProductCutoffSymbol (n := n) (m := r) (r := a)
                  (s := F.rank) (t := F'.rank) (β j) (Co k j).cutoff ε) v z) →
              ∀ w : AT.smoothSections,
                ‖Lo.smoothToSobolev 0 (∑ k, ∑ j, O k j (U k j (I k j w)))‖ ≤
                  C * (‖inclusion w‖ + ‖inclusion' (V w)‖) := by
  as_aux_global_metric_zeta =>
    classical
    -- The supplied finite compactly supported partition already makes the base compact.
    have hcover : (Set.univ : Set B) ⊆ ⋃ j, tsupport (J.cutoff j) := by
      intro x _
      by_contra h
      have hz (j : Fin J.size) : J.cutoff j x = 0 := by
        by_contra hne
        exact h (Set.mem_iUnion.mpr ⟨j, subset_tsupport (J.cutoff j) hne⟩)
      have hs := J.sum_cutoff x
      simp only [hz, Finset.sum_const_zero] at hs
      exact zero_ne_one hs
    let : CompactSpace B :=
      ⟨(isCompact_iUnion J.compact_support).of_isClosed_subset isClosed_univ hcover⟩
    have hsqrt (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 ≤ c)
        (h : x ^ 2 ≤ c * y ^ 2) : x ≤ Real.sqrt c * y := by
      apply (sq_le_sq₀ hx (mul_nonneg (Real.sqrt_nonneg _) hy)).mp
      simpa only [mul_pow, Real.sq_sqrt hc] using h
    -- The auxiliary plateau is built around the original cutoff, without changing its rows.
    have hplateau (j : Fin J.size) : ∃ χ : B → ℝ,
        ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ ∧
        tsupport χ ⊆ (S.trivialization (b j)).baseSet ∧
        ∀ x ∈ (J.chart j).symm '' tsupport (J.chartCutoff E j).cutoff, χ x = 1 := by
      let input := J.chartCutoff E j
      have hinput : (J.chart j).symm '' tsupport input.cutoff ⊆
          (S.trivialization (b j)).baseSet :=
        fun _ hx ↦ hJ j (J.chartCutoff_support_subset E j hx)
      have hbase : IsCompact ((J.chart j).symm '' tsupport input.cutoff) :=
        input.compact_support.image_of_continuousOn
          ((J.chart j).continuousOn_symm.mono (fun x hx ↦ (input.support_subset hx).1))
      obtain ⟨U₁, hU₁, hKU₁, hU₁base, hU₁compact⟩ :=
        exists_open_between_and_isCompact_closure hbase
          (S.trivialization (b j)).open_baseSet hinput
      obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
        (I := 𝓡 n) (n := ⊤) hbase.isClosed (hKU₁.trans hU₁.subset_interior_closure)
      have hχsupport : tsupport χ ⊆ (S.trivialization (b j)).baseSet := by
        apply Set.Subset.trans ?_ hU₁base
        apply closure_minimal ?_ hU₁compact.isClosed
        intro x hx
        by_contra hn
        exact hx (hχzero x hn)
      exact ⟨χ, χ.contMDiff, hχsupport, fun x hx ↦ hχone.self_of_nhdsSet x hx⟩
    choose χ hχ hsχ hχone using hplateau
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    have hfamily (j : Fin J.size) :=
      exists_associatedSphereTensorLocalizedVertical_global_sobolev_bound (a := a)
        S E F F' σ σ' hσ hσ' kFiber kFiber' ν Q hQ hQell N N' (b j)
        (J.chartCutoff E j) (J.chart_mem_atlas j)
        (fun _ hx ↦ hJ j (J.chartCutoff_support_subset E j hx))
        (χ j) (hχ j) (hsχ j) (hχone j)
    have hnative := vertical_regularization_global_native_bound
      (n := n) (r := r) (a := a) (P := P) (B := B) (projection := projection)
      S E F σ hσ F' σ' hσ' N₀ J b hJ Co hCo N L Ko
    intro A A' hA hA' QA hQA
    let := modelTopology (EuclideanSpace ℂ (Fin a)) E
    let : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    let : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    let := associatedSphereChartedSpace S
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let := linearModelChartedSpace split.symm Z
    let := isManifold_linearModelChartedSpace split.symm Z
    intro AT AT' V Din Dout β I O hI hO Li Lo l hl l' hl' Ng Ng' kGlobal kGlobal' η hη
    let := modelTopology (EuclideanSpace ℂ (Fin Ng.rank)) Ng.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin Ng'.rank)) Ng'.Fiber
    intro e he hi e' he' hi' hpair hpair' sectionEquiv sectionEquiv' inclusion inclusion' ε hε
    have hmetricData (j : Fin J.size) := (hfamily j).choose_spec
      Li Lo l hl l' hl' Ng Ng' kGlobal kGlobal' η e he hi e' he' hi' hpair hpair'
    let Ck (j : Fin J.size) : ℝ := (hmetricData j).choose
    have hCk (j : Fin J.size) : 0 ≤ Ck j := (hmetricData j).choose_spec.1
    have hf (j : Fin J.size) := (hmetricData j).choose_spec.2
    have hnativeData := hnative I O hI hO Lo ε hε
    let cN : ℝ := hnativeData.choose
    have hcN : 0 ≤ cN := hnativeData.choose_spec.1
    have hn := hnativeData.choose_spec.2
    let total : ℝ := (a : ℝ) * ∑ j : Fin J.size, Ck j ^ 2
    have htotal : 0 ≤ total := mul_nonneg (Nat.cast_nonneg _)
      (Finset.sum_nonneg (fun j _ ↦ sq_nonneg _))
    refine ⟨Real.sqrt (cN * total), Real.sqrt_nonneg _, ?_⟩
    intro U hU w
    -- These actual native rows, with their exact coordinate identities, enter both bounds.
    let u (j : Fin J.size) : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber :=
      (hf j w).choose
    have hvalue (j : Fin J.size) := (hf j w).choose_spec.1
    let hu (j : Fin J.size) := (hf j w).choose_spec.2.choose
    have hb (j : Fin J.size) := (hf j w).choose_spec.2.choose_spec
    have hnorm := hn U hU w u hvalue hu
    let v : ℝ := ‖inclusion w‖ + ‖inclusion' (V w)‖
    have hv : 0 ≤ v := add_nonneg (norm_nonneg _) (norm_nonneg _)
    have hrow (j : Fin J.size) (i : Fin a) :
        ‖(hu j i).toLp (fun x ↦ N.smoothToSobolev 1 (u j x i))‖ ^ 2 ≤ Ck j ^ 2 * v ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) (hb j i) 2).trans_eq (mul_pow _ _ 2)
    have hsum : (∑ j, ∑ i : Fin a,
        ‖(hu j i).toLp (fun x ↦ N.smoothToSobolev 1 (u j x i))‖ ^ 2) ≤ total * v ^ 2 := by
      calc
        _ ≤ ∑ j : Fin J.size, ∑ i : Fin a, Ck j ^ 2 * v ^ 2 :=
          Finset.sum_le_sum (fun j _ ↦ Finset.sum_le_sum (fun i _ ↦ hrow j i))
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.mul_sum, ← Finset.sum_mul, total, mul_assoc]
    have hsq := hnorm.trans (mul_le_mul_of_nonneg_left hsum hcN)
    have hsq' := hsq.trans_eq (mul_assoc cN total (v ^ 2)).symm
    exact hsqrt _ v (cN * total) (norm_nonneg _) hv (mul_nonneg hcN htotal) hsq'

end AtiyahSinger
