/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.ProductCompactSchwartz
public import AtiyahSinger.Analysis.RightProductSchwartzSlice

/-!
# Vertical piece coordinates on the associated bundle

Public module ID: M0198.

The unregularized right-factor Fourier action has a joint Schwartz output on
each compact associated input. Each base-first row equals the complete sphere
piece action multiplied by the supplied compact base multiplier. The sphere
output cutoff occurs exactly once, and the output support lies in the product
of the base input-cutoff and sphere output-cutoff supports.

Source: SG III.13.5--13.6 and the project chart Fourier convention.
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
  [TopologicalSpace (TotalSpace Unit F')]
  (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))
local notation "V₀" => EuclideanSpace ℂ (Fin a)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The vertical Fourier output has the scaled whole sphere-piece rows and product support. -/
theorem exists_associatedSphereTensorVerticalCutoff_coordinates
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (c : OpenPartialHomeomorph B X) (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (L : AtlasPseudodifferentialPiece A A' 1)
    (ρ : X → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hcρ : HasCompactSupport ρ) :
    letI := modelTopology V₀ E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    let Din := associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
    let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
    let β : SymbolFunction r (A.rank L.input.frameIndex * a)
        (A'.rank L.output.frameIndex * a) :=
      fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
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
          tsupport v ⊆ EuclideanSpace.finAddEquivProd.symm ''
            (tsupport C.cutoff ×ˢ tsupport L.output.cutoff) ∧
          ∀ (x : X) (y : Y) (i : Fin a) (j : Fin (A'.rank L.output.frameIndex)),
            v (EuclideanSpace.finAddEquivProd.symm (x, y)) (finProdFinEquiv (i, j)) =
              (ρ x : ℂ) * ((L.output.cutoff y : ℂ) *
                L.operator (L.input.localize L.chart_mem_atlas
                  ((C.cutoff x : ℂ) • associatedSphereTensorLocalFiberCoordinates S E A b
                    C.frame C.frame_mem_atlas i
                    (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
                    (c.symm x))) y j) := by
  classical
  let := modelTopology V₀ E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let ef := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace ef.symm Z
  let AT := associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let Din := associatedSphereTensorChartCutoff S E A σ hσ b c C hC L.chart L.input
  let α := zeroExtendedSymbol Set.univ L.output.cutoff L.symbol
  have hα : IsSymbol Set.univ 1 α :=
    isSymbol_zeroExtendedSymbol Set.univ isOpen_univ 1 L.output.cutoff
      L.output.smooth_cutoff L.output.compact_support (Set.subset_univ _) L.symbol L.isSymbol
  have hαK : HasCompactSupport α := hasCompactSupport_zeroExtendedSymbol Set.univ
    L.output.cutoff L.symbol L.output.compact_support
  let β : SymbolFunction r (A.rank L.input.frameIndex * a)
      (A'.rank L.output.frameIndex * a) :=
    fun y η ↦ tensorIdentitySymbolMap (A.rank L.input.frameIndex)
      (A'.rank L.output.frameIndex) a (α y η)
  have hβ : IsSymbol Set.univ 1 β := isSymbol_continuousLinearMap 1 α hα
    ((tensorIdentitySymbolMap (A.rank L.input.frameIndex)
      (A'.rank L.output.frameIndex) a).restrictScalars ℝ)
  have hβK : HasCompactSupport β := by
    apply hαK.of_isClosed_subset (isClosed_tsupport β)
    apply closure_minimal _ (isClosed_tsupport α)
    intro y hy
    by_contra hout
    apply hy
    funext η
    change tensorIdentitySymbolMap _ _ _ (α y η) = 0
    rw [image_eq_zero_of_notMem_tsupport hout]
    exact (tensorIdentitySymbolMap _ _ _).map_zero
  let e := productCoordinateSwap n r
  let i := tensorCoordinateSwap a (A.rank L.input.frameIndex)
  let o := (tensorCoordinateSwap a (A'.rank L.output.frameIndex)).symm
  let p := isometricSymbolTransport e i o (liftedProductSymbol β ρ)
  dsimp only
  intro I hI w
  change AT.smoothSections →ₗ[ℂ]
    𝓢(XY, EuclideanSpace ℂ (Fin (a * A.rank L.input.frameIndex))) at I
  change ∀ w z, I w z = Din.localizedFunction w z at hI
  have hcompact : HasCompactSupport (I w) := by
    apply Din.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal _ (isClosed_tsupport Din.cutoff)
    intro z hz
    by_contra hout
    apply hz
    rw [hI]
    simp [AtlasChartCutoff.localizedFunction, image_eq_zero_of_notMem_tsupport hout]
  let w' := schwartzCoordinateEquiv e.symm i (I w)
  have hwcompact : HasCompactSupport w' := by
    apply (hcompact.image e.continuous).of_isClosed_subset (isClosed_tsupport w')
    apply closure_minimal _ (hcompact.image e.continuous).isClosed
    intro z hz
    refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
    apply subset_tsupport
    intro hzero
    apply hz
    change i (I w (e.symm z)) = 0
    rw [hzero, map_zero]
  -- Construct the complete Fourier output, including the original output cutoff.
  obtain ⟨v', hv', _⟩ := exists_schwartz_quantize_liftedProductSymbol_of_hasCompactSupport
    β hβ hβK ρ hρ hcρ w' hwcompact
  let v := schwartzCoordinateEquiv e o v'
  have hw : schwartzCoordinateEquiv e i.symm w' = I w := by
    apply SchwartzMap.ext
    intro z
    change i.symm (i (I w (e.symm (e z)))) = I w z
    rw [e.symm_apply_apply, i.symm_apply_apply]
  have hv (z : XY) : quantize p (I w) z = v z := by
    have h := quantize_isometricSymbolTransport e i o (liftedProductSymbol β ρ) w' z
    rw [hw, hv'] at h
    exact h
  have hαquant (f : 𝓢(Y, EuclideanSpace ℂ (Fin (A.rank L.input.frameIndex)))) (y : Y) :
      quantize α f y = (L.output.cutoff y : ℂ) • quantize L.symbol f y := by
    simp only [α, zeroExtendedSymbol, Set.mem_univ, ↓reduceIte, quantize, smul_apply]
    simp_rw [smul_comm (Complex.exp _) (L.output.cutoff y : ℂ)]
    rw [integral_smul, smul_comm]
  have hrow (x : X) (y : Y) (l : Fin a) (j : Fin (A'.rank L.output.frameIndex)) :
      v (ef.symm (x, y)) (finProdFinEquiv (l, j)) =
        (ρ x : ℂ) * ((L.output.cutoff y : ℂ) *
          L.operator (L.input.localize L.chart_mem_atlas
            ((C.cutoff x : ℂ) • associatedSphereTensorLocalFiberCoordinates S E A b
              C.frame C.frame_mem_atlas l
              (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
              (c.symm x))) y j) := by
    let f := L.input.localize L.chart_mem_atlas
      ((C.cutoff x : ℂ) • associatedSphereTensorLocalFiberCoordinates S E A b
        C.frame C.frame_mem_atlas l
        (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w) (c.symm x))
    have hf (z : Y) (k : Fin (A.rank L.input.frameIndex)) :
        f z k = I w (ef.symm (x, z)) (finProdFinEquiv (l, k)) := by
      rw [hI]
      exact (associatedSphereTensorChartCutoff_localizedFunction S E A σ hσ b c C hC
        L.chart L.chart_mem_atlas L.input w x z l k).symm
    rw [← hv]
    change quantize (isometricSymbolTransport e i o (liftedProductSymbol β ρ)) (I w)
      (ef.symm (x, y)) (finProdFinEquiv (l, j)) = _
    rw [quantize_rightProductLift_eq_slice α hα hαK ρ (I w) x l f hf y j, hαquant]
    rw [← L.operator_apply]
    rfl
  -- Vanishing outside either original support is a full-row statement on this same output.
  have hsupport : tsupport v ⊆ ef.symm ''
      (tsupport C.cutoff ×ˢ tsupport L.output.cutoff) := by
    have hK := (C.compact_support.prod L.output.compact_support).image ef.symm.continuous
    apply closure_minimal _ hK.isClosed
    intro z hz
    refine ⟨ef z, ⟨?_, ?_⟩, ef.symm_apply_apply z⟩
    · by_contra hout
      apply hz
      apply PiLp.ext
      intro k
      obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      rw [← ef.symm_apply_apply z, hrow]
      have hzero : L.input.localize L.chart_mem_atlas (0 : A.smoothSections) = 0 :=
        (L.input.localizeLinearMap L.chart_mem_atlas).map_zero
      simp [image_eq_zero_of_notMem_tsupport hout, hzero]
    · by_contra hout
      apply hz
      apply PiLp.ext
      intro k
      obtain ⟨⟨l, j⟩, rfl⟩ := finProdFinEquiv.surjective k
      rw [← ef.symm_apply_apply z, hrow]
      simp [image_eq_zero_of_notMem_tsupport hout]
  exact ⟨v, hv, hsupport, hrow⟩

end AtiyahSinger
