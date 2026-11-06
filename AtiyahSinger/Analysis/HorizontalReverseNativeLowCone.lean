/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HorizontalReverseLowCone
public import AtiyahSinger.Analysis.AssociatedTensorSupportedReturnBound
public import AtiyahSinger.Analysis.AssociatedTensorVerticalCoordinateEnergy

/-!
# Actual native whole-fiber control of the original horizontal cutoff error

Public module ID: M0755.

Compare the tensor input coordinates with the supplied native fiber family.
The source low-cone bound and the exact row identity give whole-fiber Sobolev
control of the local horizontal cutoff error.
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

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
-- Compare the original dependent tensor coordinates and both native Sobolev realizations.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The literal local horizontal error is bounded by its original native fiber family. -/
theorem horizontal_reverse_low_cone_native_bound
    (L : PseudodifferentialPiece (n := n) (r := a) (q := a') E E' 1) (b : B)
    (hinput : L.chart.symm '' tsupport L.input.cutoff ⊆ (S.trivialization b).baseSet)
    (houtput : L.chart.symm '' tsupport L.output.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ L.chart.symm '' tsupport L.input.cutoff, χ x = 1)
    (J : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (Co : BundleChartCutoff (r := a') E' L.chart) (hCoFrame : Co.frame = L.output.frame)
    (hCo : L.chart.symm '' tsupport Co.cutoff ⊆ (S.trivialization b).baseSet)
    (hCoOne : ∀ x ∈ tsupport L.output.cutoff, Co.cutoff x = 1)
    (κ : Fin J.size → Yc → ℝ) (hκ : ∀ j, ContDiff ℝ ∞ (κ j))
    (hκK : ∀ j, HasCompactSupport (κ j))
    (hκsupport : ∀ j, tsupport (κ j) ⊆ (J.chart j).target ∩
      (J.chart j).symm ⁻¹' (J.frame j).baseSet)
    (hκone : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      ∀ j y, y ∈ tsupport (J.toAtlasBundlePresentation.chartCutoff j).cutoff →
        κ j y = 1) :
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
    let Kout (j : Fin J.size) : AtlasChartCutoff A (J.chart j) :=
      ⟨J₀.frameIndex j, κ j, hκ j, hκK j, hκsupport j⟩
    let Din (j : Fin J.size) := associatedSphereTensorChartCutoff S E A σ hA b
      L.chart L.input hinput (J.chart j) (J₀.chartCutoff j)
    let Dout (j : Fin J.size) := associatedSphereTensorChartCutoff S E' A σ hA b
      L.chart Co hCo (J.chart j) (Kout j)
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    ∀ (I : ∀ _j : Fin J.size, AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))))
      (O : ∀ _j : Fin J.size,
        𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))) →ₗ[ℂ] AT'.smoothSections),
      (∀ j w z, I j w z = (Din j).localizedFunction w z) →
      (∀ j v z, (O j v).val z = (Dout j).extendedFunction v z) →
      ∀ (Lo : AtlasBundlePresentation (n := n + r) (M := Z) (E := T') AT'),
        ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
          ∀ U : ∀ _j : Fin J.size,
            𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
              𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))),
            (∀ j v z, U j v z = quantize
              (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
                (productCutoffSymbol α (κ j) ε x ξ)) v z) →
            ∀ (w : AT.smoothSections)
              (u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber),
              (∀ x i, u x i = nativeSmoothSectionLinearEquiv F.Fiber
                ((L.input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
                  associatedSphereTensorLocalFiberCoordinates S E A b L.input.frame
                    L.input.frame_mem_atlas i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                    (L.chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x)))) →
              ∀ hu : ∀ i : Fin a,
                  MemLp (fun x ↦ J.smoothToSobolev 1 (u x i)) 2 (volume : Measure Xp),
                ‖Lo.smoothToSobolev 0
                  (associatedSphereTensorLocalHorizontalLift (a := a)
                    S E A σ E' L hA b χ hχ hχsupport houtput w -
                      ∑ j, O j (U j (I j w)))‖ ^ 2 ≤
                  C * ∑ i : Fin a,
                    ‖(hu i).toLp (fun x ↦ J.smoothToSobolev 1 (u x i))‖ ^ 2 := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let J₀ := J.toAtlasBundlePresentation
  -- Apply the source low-cone estimate to the same localized maps.
  have hraw := horizontal_reverse_low_cone_source_bound
    (n := n) (r := r) (a := a) (a' := a') (P := P) (B := B)
    (F := F.Fiber) (projection := projection)
    S E A σ E' L hA b hinput houtput χ hχ hχsupport hχone
    J₀ Co hCoFrame hCo hCoOne κ hκ hκK hκsupport hκone
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
  let Kin (j : Fin J.size) := J₀.chartCutoff j
  dsimp only
  intro I O hI hO Lo ε hε
  change AtlasBundlePresentation AT' at Lo
  have hdata : ∃ C : ℝ, 0 ≤ C ∧
      ∀ U : ∀ _j : Fin J.size,
        𝓢(XY, EuclideanSpace ℂ (Fin (a * F.rank))) →L[ℂ]
          𝓢(XY, EuclideanSpace ℂ (Fin (a' * F.rank))),
        (∀ j v z, U j v z = quantize
          (fun x ξ ↦ tensorIdentitySymbolMap a a' F.rank
            (productCutoffSymbol (zeroExtendedSymbol Set.univ L.output.cutoff L.symbol)
              (κ j) ε x ξ)) v z) →
        ∀ w : AT.smoothSections,
          ‖Lo.smoothToSobolev 0
            (associatedSphereTensorLocalHorizontalLift (a := a)
              S E A σ E' L hA b χ hχ hχsupport houtput w -
                ∑ j, O j (U j (I j w)))‖ ^ 2 ≤
            C * ∑ j : Fin J.size, (‖(I j w).toLp 2‖ ^ 2 +
              ∑ l : Fin r, ‖(LineDeriv.lineDerivOp
                (EuclideanSpace.single (Fin.natAdd n l) (1 : ℝ)) (I j w)).toLp 2‖ ^ 2) :=
    hraw I O hI hO Lo ε hε
  let C : ℝ := hdata.choose
  have hC : 0 ≤ C := hdata.choose_spec.1
  have hbound := hdata.choose_spec.2
  let K : ℝ := 1 + (2 * Real.pi) ^ 2
  have hK : 0 ≤ K := add_nonneg zero_le_one (sq_nonneg _)
  refine ⟨C * (J.size * K), mul_nonneg hC (mul_nonneg (Nat.cast_nonneg _) hK), ?_⟩
  intro U hU w u hvalue hu
  have hsource := hbound U hU w
  -- The original native chart localization is exactly its atlas-coordinate realization.
  have hNative (j : Fin J.size) (s : A.smoothSections) (y : Yc) :
      (Kin j).localize (J.chart_mem_atlas j) s y =
        J.localize j (nativeSmoothSectionLinearEquiv F.Fiber s) y := by
    change (if y ∈ (J.chart j).target then
      (((if y ∈ (J.chart j).target then J.cutoff j ((J.chart j).symm y) else 0) : ℝ) : ℂ) •
        (EuclideanSpace.equiv (Fin F.rank) ℂ).symm
          ((EuclideanSpace.equiv (Fin F.rank) ℂ)
            (J.frame j ⟨(J.chart j).symm y, s.val ((J.chart j).symm y)⟩).2) else 0) =
      (if y ∈ (J.chart j).target then
        (J.cutoff j ((J.chart j).symm y) : ℂ) •
          (J.frame j ⟨(J.chart j).symm y, s.val ((J.chart j).symm y)⟩).2 else 0)
    rw [ContinuousLinearEquiv.symm_apply_apply]
    by_cases hy : y ∈ (J.chart j).target
    · simp only [ite_eq_left hy]
    · simp only [ite_eq_right hy]
  -- Keep the same original family u, without choosing a new fiber representative.
  have hcoords (j : Fin J.size) (i : Fin a) (x : Xp) (y : Yc) (l : Fin F.rank) :
      J.localize j (u x i) y l =
        I j w (e.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x, y))
          (finProdFinEquiv (i, l)) := by
    symm
    rw [hI]
    have h := associatedSphereTensorChartCutoff_localizedFunction (a := a)
      S E A σ hA b L.chart L.input hinput (J.chart j) (J.chart_mem_atlas j) (Kin j)
      w ((EuclideanSpace.equiv (Fin n) ℝ).symm x) y i l
    refine h.trans ?_
    have hn := hNative j
      ((L.input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm x) : ℂ) •
        associatedSphereTensorLocalFiberCoordinates S E A b L.input.frame
          L.input.frame_mem_atlas i
          (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
          (L.chart.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm x))) y
    exact (congrArg (fun v : EuclideanSpace ℂ (Fin F.rank) ↦ v l) hn).trans
      (congrArg (fun s ↦ J.localize j s y l) (hvalue x i).symm)
  have henergy (j : Fin J.size) :=
    J.vertical_energy_le_family_sobolev u hu j (I j w) (hcoords j)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ henergy j)
  have hfinite : (∑ _j : Fin J.size,
      K * ∑ i : Fin a, ‖(hu i).toLp (fun x ↦ J.smoothToSobolev 1 (u x i))‖ ^ 2) =
      (J.size * K) * ∑ i : Fin a,
        ‖(hu i).toLp (fun x ↦ J.smoothToSobolev 1 (u x i))‖ ^ 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have hscaled := mul_le_mul_of_nonneg_left (hsum.trans_eq hfinite) hC
  have hresult := hsource.trans hscaled
  exact hresult.trans_eq (mul_assoc C (J.size * K) _).symm

end AtiyahSinger
