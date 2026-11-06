/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.AssociatedVerticalSymbolCoordinates
public import AtiyahSinger.Analysis.AtlasQuantization

/-!
# The actual saturated family equals the canonical descended vertical symbol

Public module ID: M0223.

The same native full q determines both the fixed quantization family and the
unique descended symbol. The actual finite associated factor is evaluated on
one original total covector. Its chart restriction is identified with the
original fiber derivative, so the equality uses the same global descended
factor for every normalized principal representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology

variable {n r d e : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {F F' : OrthogonalSphere r → Type*}
  [∀ y, NormedAddCommGroup (F y)] [∀ y, NormedSpace ℂ (F y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin d)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin d)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin d)) F]
  [IsSmoothComplexBundle (n := r) (r := d) F]
  [∀ y, NormedAddCommGroup (F' y)] [∀ y, NormedSpace ℂ (F' y)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin e)) F')]
  [FiberBundle (EuclideanSpace ℂ (Fin e)) F']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin e)) F']
  [IsSmoothComplexBundle (n := r) (r := e) F']
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (τ : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The actual saturated finite factor is the same canonical descended q in every local gauge. -/
theorem associatedSphereVerticalFullSymbol_eq_saturated_finite_sum
    (q : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q.val = q.val) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
    let a := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := d) F
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := e) F'
    let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
    let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle τ
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
    ∀ (hσ : σ.IsSmoothAtlas IG A) (hτ : τ.IsSmoothAtlas IG A')
      (b : B) (c : OpenPartialHomeomorph B X) (_hc : c ∈ atlas X B)
      (p : P) (_hp : projection p ∈ (S.trivialization b).baseSet)
      (_hg : (S.trivialization b p).2 = 1) (_hx : projection p ∈ c.source)
      (y : OrthogonalSphere r) (R : AtlasQuantizationPresentation A A')
      (θ : ℝ) (w : Fin R.size → ℝ),
      (∀ j, (R.patch j).weight y ≠ 0 → w j = 1) →
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      letI : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let z := associatedBundleMk G P (OrthogonalSphere r) p y
      ∀ ξ : EuclideanSpace ℝ (Fin (n + r)) →L[ℝ] ℝ,
        let CP := fun j ↦ associatedSphereProductChart S b c (L j).chart
        let cov := fun j ↦ split (covectorInChart (CP j) z ξ)
        let factor := fun j ↦
          if hz : z ∈ (CP j).source ∩ (AD.chart (b, (L j).input.frameIndex)).baseSet ∩
              (AD'.chart (b, (L j).output.frameIndex)).baseSet then
            let eIn := (AD.frameLinearEquiv (b, (L j).input.frameIndex) z hz.1.2).trans
              (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut := (AD'.frameLinearEquiv (b, (L j).output.frameIndex) z hz.2).trans
              (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((θ * (L j).input.cutoff ((L j).chart y) *
              (L j).output.cutoff ((L j).chart y) * w j : ℝ) : ℂ) •
                (eOut.symm.toLinearMap.comp
                  (((L j).symbol ((L j).chart y) (cov j).2).toLinearMap.comp eIn.toLinearMap))
          else (0 : D z →ₗ[ℂ] D' z)
        (∑ j, factor j) = (θ : ℂ) • a z (ξ.comp split.symm.toContinuousLinearMap) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  let a := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
  have ha := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose_spec.1
  let v (p : P) (y : OrthogonalSphere r) := mfderiv (𝓡 r) 𝓘(ℝ, X × Y)
    (associatedBundleMk G P (OrthogonalSphere r) p) y
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := d) F
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := e) F'
  let D := AssociatedEquivariantFiber S.toIsPrincipalBundle σ
  let D' := AssociatedEquivariantFiber S.toIsPrincipalBundle τ
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
  change ∀ (hσ : σ.IsSmoothAtlas IG A) (hτ : τ.IsSmoothAtlas IG A'), _
  intro hσ hτ b c hc p hp hg hx y R θ w hw
  let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace split.symm Z
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  let t := associatedSphereTrivialization S b
  change ∀ ξ : EuclideanSpace ℝ (Fin (n + r)) →L[ℝ] ℝ, _
  intro ξ CP cov factor
  -- The normalized original representative fixes the trivialization and fiber covector.
  have ht : t z = (projection p, y) := by
    have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
    change t z = (projection p, (S.trivialization b p).2 • y) at h
    rw [hg, one_smul] at h
    exact h
  have hη := associatedSphereVerticalCovector_eq_fiberRestriction S b p hp hg y ξ
  change ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r))
    t.toOpenPartialHomeomorph.symm (projection p, y)).comp
      (ContinuousLinearMap.inr ℝ X Y)) =
        (ξ.comp split.symm.toContinuousLinearMap).comp (v p y) at hη
  apply LinearMap.ext
  intro u
  obtain ⟨u₀, rfl⟩ :=
    (associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y rfl).2 u
  -- Use the actual fixed patches and actual chart-frequency factors, then identify the covector.
  let η := ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r))
    t.toOpenPartialHomeomorph.symm (t z)).comp (ContinuousLinearMap.inr ℝ X Y))
  have h := associatedSphereVerticalFactor_apply_eq_finiteSymbol S A A' σ τ
    hσ hτ b c hc p hp hg hx y R.size L θ w ξ u₀
  have hsum : (∑ j, (w j : ℂ) • (L j).globalSymbolFunction y η u₀) = q.val y η u₀ := by
    have hpoint (j : Fin R.size) : (w j : ℂ) • (L j).globalSymbolFunction y η u₀ =
        ((R.patch j).weight y : ℂ) • q.val y η u₀ := by
      have hpiece := AtlasQuantizationPatch.globalSymbolFunction_toPiece
        (R.patch j) (nativeAtlasGlobalSymbol 1 q)
      change (w j : ℂ) •
        (((R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)).globalSymbolFunction y η u₀) = _
      rw [hpiece]
      change (w j : ℂ) • (((R.patch j).weight y : ℂ) • q.val y η u₀) = _
      by_cases hj : (R.patch j).weight y = 0
      · simp only [hj, Complex.ofReal_zero, zero_smul, smul_zero]
      · rw [hw j hj, Complex.ofReal_one, one_smul]
    simp_rw [hpoint]
    rw [← Finset.sum_smul]
    have hweight : (∑ j, ((R.patch j).weight y : ℂ)) = 1 := by
      exact_mod_cast R.sum_weight y
    rw [hweight, one_smul]
  change (∑ j, factor j) (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u₀) =
    associatedEquivariantFiberMk S.toIsPrincipalBundle τ p y rfl
      ((θ : ℂ) • ∑ j, (w j : ℂ) • (L j).globalSymbolFunction y η u₀) at h
  rw [hsum] at h
  change (∑ j, factor j) (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u₀) =
    associatedEquivariantFiberMk S.toIsPrincipalBundle τ p y rfl
      ((θ : ℂ) • q.val y (ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r))
        t.toOpenPartialHomeomorph.symm (t z)).comp (ContinuousLinearMap.inr ℝ X Y))) u₀) at h
  rw [ht, hη] at h
  rw [h]
  change _ = (θ : ℂ) • a z (ξ.comp split.symm.toContinuousLinearMap)
    (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u₀)
  -- The canonical descended map is evaluated on exactly the same restricted covector.
  rw [ha p y rfl]
  exact (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle τ p y rfl).map_smul θ _

end AtiyahSinger
