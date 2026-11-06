/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorVerticalCutoffCoordinates
public import AtiyahSinger.Analysis.AssociatedTensorVerticalKernel

/-!
# Returning a vertical piece through the principal chart

Public module ID: M0201.

The unregularized full Fourier output is compared with the complete sphere
piece through the same tensor frames and normalized principal representative.
The base and sphere output plateaus equal one on the respective output
supports, while the supplied base multiplier equals one on the input support.
The sphere output cutoff remains present exactly once. The return identity
retains the original base localization and includes all off-support cases.

Source: the local vertical construction in SG III.13.6.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
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


local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ


variable
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)] [∀ y, Module ℂ (F' y)]
  [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The full vertical Fourier output returns to the original localized tensor extension. -/
theorem exists_associatedSphereTensorVerticalCutoff_extension
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A') (b : B)
    (c : OpenPartialHomeomorph B X) (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (L : AtlasPseudodifferentialPiece A A' 1)
    (γ : X → ℝ) (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ)
    (hsγ : tsupport γ ⊆ c.target ∩ c.symm ⁻¹' C.frame.baseSet)
    (hbγ : c.symm '' tsupport γ ⊆ (S.trivialization b).baseSet)
    (hγone : ∀ x ∈ tsupport C.cutoff, γ x = 1)
    (κ : Y → ℝ) (hκ : ContDiff ℝ ∞ κ) (hcκ : HasCompactSupport κ)
    (hsκ : tsupport κ ⊆ L.chart.target ∩ L.chart.symm ⁻¹'
      (A'.chart L.output.frameIndex).baseSet)
    (hκone : ∀ y ∈ tsupport L.output.cutoff, κ y = 1)
    (ρ : X → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ)
    (hρone : ∀ x ∈ tsupport C.cutoff, ρ x = 1) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI : TopologicalSpace (TotalSpace Unit T') :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI (x : B) : FiniteDimensional ℂ (E x) :=
      VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let Co : BundleChartCutoff E c :=
      { C with
        cutoff := γ
        smooth_cutoff := hγ
        compact_support := hcγ
        support_subset := hsγ }
    let Ko : AtlasChartCutoff A' L.chart :=
      { L.output with
        cutoff := κ
        smooth_cutoff := hκ
        compact_support := hcκ
        support_subset := hsκ }
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
    let Dout := associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    let β := fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
      (A'.rank L.output.frameIndex) a (α y η)
    let p := isometricSymbolTransport (productCoordinateSwap n r)
      (tensorCoordinateSwap a (A.rank L.input.frameIndex))
      (tensorCoordinateSwap a (A'.rank L.output.frameIndex)).symm (liftedProductSymbol β ρ)
    ∀ I : AT.smoothSections →ₗ[ℂ]
        𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))),
      (∀ w z, I w z = Din.localizedFunction w z) →
      ∀ w : AT.smoothSections,
        ∃ v : 𝓢(XY, EuclideanSpace ℂ (Fin (a * A'.rank L.output.frameIndex))),
          (∀ z, quantize p (I w) z = v z) ∧
          (tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
            (tsupport C.cutoff ×ˢ tsupport L.output.cutoff)) ∧
          ∀ (x : B), x ∈ c.source → x ∈ (S.trivialization b).baseSet →
            x ∈ C.frame.baseSet → ∀ y : OrthogonalSphere r,
              let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
              Dout.extendedFunction v (associatedBundleMk G P (OrthogonalSphere r) p y) =
                (C.cutoff (c x) : ℂ) • associatedSphereTensorFiberEquiv S E σ' p y
                  ((tensorSectionOperator (E (projection p)) A.smoothSections A'.smoothSections
                    L.toLinearMap (associatedSphereTensorFiberRestriction (a := a)
                      S E A σ hσ p w)).val y) := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace ef.symm Z
  let (x : B) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin a)) E x
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let AT' : SmoothComplexBundleAtlas (n := n + r) T' :=
    associatedSphereTensorBundleAtlas (a := a) S E A' σ' hσ'
  let Co : BundleChartCutoff E c :=
    { C with
      cutoff := γ
      smooth_cutoff := hγ
      compact_support := hcγ
      support_subset := hsγ }
  let Ko : AtlasChartCutoff A' L.chart :=
    { L.output with
      cutoff := κ
      smooth_cutoff := hκ
      compact_support := hcκ
      support_subset := hsκ }
  let CP := associatedSphereProductChart S b c L.chart
  let Dout : AtlasChartCutoff AT' CP :=
    associatedSphereTensorChartCutoff S E A' σ' hσ' b c Co hbγ L.chart Ko
  let t := associatedSphereTrivialization S b
  let R := associatedSphereTensorFiberRestriction (a := a) S E A σ hσ
  dsimp only
  intro I hI w
  obtain ⟨v, hv, hvsupport, hrow⟩ :=
    exists_associatedSphereTensorVerticalCutoff_coordinates S E A σ A' hσ b c C hC
      L ρ hρ hcρ I hI w
  let family (p : P) := tensorSectionOperator (E (projection p)) A.smoothSections
    A'.smoothSections L.toLinearMap (R p w)
  have hcoordinates (l : Fin a) (x : B) :
      associatedSphereTensorLocalFiberCoordinates S E A' b C.frame C.frame_mem_atlas l family x =
        L.toLinearMap (associatedSphereTensorLocalFiberCoordinates S E A b
          C.frame C.frame_mem_atlas l (fun p ↦ R p w) x) := by
    by_cases hx : x ∈ (S.trivialization b).baseSet ∩ C.frame.baseSet
    · let := C.frame_mem_atlas
      let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
      let φ : E (projection p) →ₗ[ℂ] ℂ := (LinearMap.proj l).comp
        ((EuclideanSpace.equiv (Fin a) ℂ).toLinearMap.comp
          ((C.frame.linearEquivAt ℂ x hx.2).toLinearMap.comp
            (LinearEquiv.cast (R := ℂ) (M := E)
              ((S.trivialization b).proj_symm_apply' hx.1)).toLinearMap))
      apply Subtype.ext
      have h := tensorSectionOperator_contract (E (projection p)) A.smoothSections
        A'.smoothSections L.toLinearMap (R p w) φ
      simpa only [associatedSphereTensorLocalFiberCoordinates, dite_eq_left hx, family] using h
    · simp only [associatedSphereTensorLocalFiberCoordinates, dite_eq_right hx, map_zero]
  have hzero (p : P) (y : OrthogonalSphere r)
      (hy : y ∉ L.chart.symm '' tsupport L.output.cutoff) : (family p).val y = 0 := by
    have hL (u : A.smoothSections) : (L.toLinearMap u).val y = 0 :=
      L.toLinearMap_support_properties.1 u y hy
    obtain ⟨u, hu⟩ := (tensorSectionEquiv (E (projection p)) A.smoothSections).surjective (R p w)
    have hact : family p = tensorSectionEquiv (E (projection p)) A'.smoothSections
        ((L.toLinearMap.lTensor (E (projection p))) u) := by
      simp only [family, ← hu, tensorSectionOperator, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [hact]
    change tensorSectionEvaluation (E (projection p)) A'.smoothSections
      ((L.toLinearMap.lTensor (E (projection p))) u) y = 0
    clear hu hact
    induction u using TensorProduct.inductionOn with
    | tmul e f => simp [tensorSectionEvaluation_tmul, hL]
    | add u v hu hv => simp only [map_add, Pi.add_apply, hu, hv, add_zero]
  refine ⟨v, hv, hvsupport, ?_⟩
  intro x hx hxb hxe y
  let p := (S.trivialization b).toOpenPartialHomeomorph.symm (x, 1)
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  have htbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have htt : (x, y) ∈ t.target := t.mem_target.mpr (htbase.symm ▸ hxb)
  have hzinv : t.toOpenPartialHomeomorph.symm (x, y) = z :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.2 x y hxb
  have hzt : z ∈ t.source := hzinv ▸ t.toOpenPartialHomeomorph.map_target htt
  have htz : t z = (x, y) := by
    rw [← hzinv]
    exact t.toOpenPartialHomeomorph.right_inv htt
  have hcp : CP z = ef.symm (c x, L.chart y) := by
    change ef.symm (c (t z).1, L.chart (t z).2) = _
    rw [htz]
  have hsource (hy : y ∈ L.chart.source) : z ∈ CP.source := by
    refine ⟨⟨hzt, ?_⟩, Set.mem_univ _⟩
    change (t z).1 ∈ c.source ∧ (t z).2 ∈ L.chart.source
    rw [htz]
    exact ⟨hx, hy⟩
  have hy_of_source (hz : z ∈ CP.source) : y ∈ L.chart.source := by
    have h := hz.1.2
    change (t z).1 ∈ c.source ∧ (t z).2 ∈ L.chart.source at h
    rw [htz] at h
    exact h.2
  change Dout.extendedFunction v z = (C.cutoff (c x) : ℂ) •
    associatedSphereTensorFiberEquiv S E σ' p y ((family p).val y)
  by_cases hxcut : c x ∈ tsupport C.cutoff
  · by_cases hycut : y ∈ L.chart.symm '' tsupport L.output.cutoff
    · obtain ⟨η, hη, hηy⟩ := hycut
      have hysource : y ∈ L.chart.source := hηy ▸ L.chart.map_target (L.output.support_subset hη).1
      have hyframe : y ∈ (A'.chart L.output.frameIndex).baseSet :=
        hηy ▸ (L.output.support_subset hη).2
      have hycoord : L.chart y = η := by
        rw [← hηy, L.chart.right_inv (L.output.support_subset hη).1]
      have hzCP := hsource hysource
      have hcut : Dout.cutoff (CP z) = 1 := by
        rw [hcp]
        change γ (ef (ef.symm (c x, L.chart y))).1 * κ (ef (ef.symm (c x, L.chart y))).2 = 1
        rw [ef.apply_symm_apply, hγone _ hxcut, hycoord, hκone _ hη, mul_one]
      have hzcut : CP z ∈ tsupport Dout.cutoff := subset_tsupport _ (by
        change Dout.cutoff (CP z) ≠ 0
        rw [hcut]
        exact one_ne_zero)
      have hzframe : z ∈ (AT'.chart Dout.frameIndex).baseSet := by
        have h := (Dout.support_subset hzcut).2
        change CP.symm (CP z) ∈ (AT'.chart Dout.frameIndex).baseSet at h
        rwa [CP.left_inv hzCP] at h
      have hz : z ∈ CP.source ∩ (AT'.chart Dout.frameIndex).baseSet := ⟨hzCP, hzframe⟩
      simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hz,
        hcut, Complex.ofReal_one, one_smul]
      let frame := AT'.frameLinearEquiv Dout.frameIndex z hzframe
      apply frame.injective
      change frame (frame.symm
        ((EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ) (v (CP z)))) = _
      rw [frame.apply_symm_apply, frame.map_smul]
      funext k
      obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      have hcoord := associatedSphereTensorLocalFiberCoordinates_chart S E A' σ' hσ' b
        C.frame C.frame_mem_atlas l family L.output.frameIndex x hxb hxe y hyframe j
      rw [hcoordinates] at hcoord
      let u := associatedSphereTensorLocalFiberCoordinates S E A b C.frame C.frame_mem_atlas l
        (fun p ↦ R p w) x
      have hlocal : (A'.chart L.output.frameIndex ⟨y, (L.toLinearMap u).val y⟩).2 j =
          (L.output.cutoff (L.chart y) : ℂ) *
            L.operator (L.input.localize L.chart_mem_atlas u) (L.chart y) j := by
        change (A'.frameLinearEquiv L.output.frameIndex y hyframe)
          (L.output.extendedFunction (L.operator (L.input.localize L.chart_mem_atlas u)) y) j = _
        have hy : y ∈ L.chart.source ∩ (A'.chart L.output.frameIndex).baseSet :=
          ⟨hysource, hyframe⟩
        simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hy]
        rw [map_smul, LinearEquiv.apply_symm_apply]
        rfl
      change v (CP z) (finProdFinEquiv (l, j)) = (C.cutoff (c x) : ℂ) *
        (AT'.chart Dout.frameIndex ⟨z,
          associatedSphereTensorFiberEquiv S E σ' p y ((family p).val y)⟩).2
          (finProdFinEquiv (l, j))
      rw [hcp, hrow, hρone _ hxcut, Complex.ofReal_one, one_mul, c.left_inv hx]
      have hscale := (L.input.localizeLinearMap L.chart_mem_atlas).map_smul
        (C.cutoff (c x) : ℂ) u
      change L.input.localize L.chart_mem_atlas ((C.cutoff (c x) : ℂ) • u) =
        (C.cutoff (c x) : ℂ) • L.input.localize L.chart_mem_atlas u at hscale
      rw [hscale, map_smul]
      change (L.output.cutoff (L.chart y) : ℂ) * ((C.cutoff (c x) : ℂ) * _) = _
      change (A'.chart L.output.frameIndex ⟨y, (L.toLinearMap u).val y⟩).2 j =
        (AT'.chart Dout.frameIndex ⟨z,
          associatedSphereTensorFiberEquiv S E σ' p y ((family p).val y)⟩).2
          (finProdFinEquiv (l, j)) at hcoord
      rw [← hcoord, hlocal]
      change (L.output.cutoff (L.chart y) : ℂ) * ((C.cutoff (c x) : ℂ) *
        L.operator (L.input.localize L.chart_mem_atlas u) (L.chart y) j) =
          (C.cutoff (c x) : ℂ) * ((L.output.cutoff (L.chart y) : ℂ) *
            L.operator (L.input.localize L.chart_mem_atlas u) (L.chart y) j)
      exact mul_left_comm _ _ _
    · rw [hzero p y hycut, map_zero, smul_zero]
      by_cases hz : z ∈ CP.source ∩ (AT'.chart Dout.frameIndex).baseSet
      · have hy := hy_of_source hz.1
        have hη : L.chart y ∉ tsupport L.output.cutoff :=
          fun h ↦ hycut ⟨L.chart y, h, L.chart.left_inv hy⟩
        have hvzero : v (CP z) = 0 := by
          apply PiLp.ext
          intro k
          obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
          rw [hcp, hrow]
          simp [image_eq_zero_of_notMem_tsupport hη]
        simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hz]
        change (Dout.cutoff (CP z) : ℂ) • (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm
          ((EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ) (v (CP z))) = 0
        rw [hvzero, (EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ).map_zero,
          (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm.map_zero]
        exact smul_zero _
      · simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hz]
  · have hc0 : C.cutoff (c x) = 0 := image_eq_zero_of_notMem_tsupport hxcut
    rw [hc0, Complex.ofReal_zero, zero_smul]
    by_cases hz : z ∈ CP.source ∩ (AT'.chart Dout.frameIndex).baseSet
    · have hvzero : v (CP z) = 0 := by
        apply PiLp.ext
        intro k
        obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
        rw [hcp, hrow]
        have hzero : L.input.localize L.chart_mem_atlas (0 : A.smoothSections) = 0 :=
          (L.input.localizeLinearMap L.chart_mem_atlas).map_zero
        simp [hc0, hzero]
      simp only [AtlasChartCutoff.extendedFunction, dite_eq_left hz]
      change (Dout.cutoff (CP z) : ℂ) • (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm
        ((EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ) (v (CP z))) = 0
      rw [hvzero, (EuclideanSpace.equiv (Fin (a * A'.rank L.output.frameIndex)) ℂ).map_zero,
        (AT'.frameLinearEquiv Dout.frameIndex z hz.2).symm.map_zero]
      exact smul_zero _
    · simp only [AtlasChartCutoff.extendedFunction, dite_eq_right hz]

end AtiyahSinger
