/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolSaturation

/-!
# Exact finite recovery of the original descended vertical full symbol

The original fixed sphere quantization patches recover the same invariant full
symbol on every original base gauge. The prescribed guarded base partition
then recovers the canonical descended full symbol at every total covector.
Inactive base charts require no overlap, and zero base weights vanish directly.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup
  associatedEquivariantFiberAddCommGroup associatedEquivariantFiberModule
  associatedEquivariantTotalTopology

variable {n r d e : ℕ} {ι P B : Type*} [Fintype ι] [TopologicalSpace P] [TopologicalSpace B]
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

local notation "H" => EuclideanSpace ℝ (Fin (n + r))

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The original finite base and sphere partitions recover the canonical full vertical symbol. -/
theorem sum_associatedSphereVerticalFullSymbol_eq
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
      (R : AtlasQuantizationPresentation A A')
      (b : ι → B) (c : ι → OpenPartialHomeomorph B X) (_hc : ∀ i, c i ∈ atlas X B)
      (θ : ι → X → ℝ),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let t := fun i ↦ associatedSphereTrivialization S (b i)
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      let Ci := fun i j ↦ associatedSphereProductChart S (b i) (c i) (L j).chart
      let weight := fun i (z : Z) ↦
        if z ∈ (t i).source ∧ (t i z).1 ∈ (c i).source then
          θ i (c i (t i z).1) else 0
      ∀ z : Z, (∑ i, weight i z) = 1 → ∀ Ξ : H →L[ℝ] ℝ,
        let cov := fun i j ↦ split (covectorInChart (Ci i j) z Ξ)
        let factor := fun i j ↦
          if hz : z ∈ (Ci i j).source ∩
              (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
              (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
            let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) z hz.1.2).trans
              (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) z hz.2).trans
              (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((θ i (c i (t i z).1) * (L j).input.cutoff ((L j).chart (t i z).2) *
              (L j).output.cutoff ((L j).chart (t i z).2) : ℝ) : ℂ) •
                (eOut.symm.toLinearMap.comp
                  (((L j).symbol ((L j).chart (t i z).2) (cov i j).2).toLinearMap.comp
                    eIn.toLinearMap))
          else (0 : D z →ₗ[ℂ] D' z)
        (∑ i, ∑ j, factor i j) = a z (Ξ.comp split.symm.toContinuousLinearMap) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  let a := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
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
  intro hσ hτ R b c hc θ split
  let := linearModelChartedSpace split.symm Z
  intro AD AD' t L Ci weight z hpartition Ξ cov factor
  -- Every original base gauge gives its guarded scalar times the same descended full symbol.
  have hpiece (i : ι) : (∑ j, factor i j) =
      (weight i z : ℂ) • a z (Ξ.comp split.symm.toContinuousLinearMap) := by
    by_cases hbase : z ∈ (t i).source ∧ (t i z).1 ∈ (c i).source
    · by_cases hθ : θ i (c i (t i z).1) = 0
      · have hzero (j : Fin R.size) : factor i j = 0 := by
          dsimp only [factor]
          split_ifs <;> simp only [hθ, zero_mul, Complex.ofReal_zero, zero_smul]
        simp only [hzero, Finset.sum_const_zero, weight, ite_eq_left hbase, hθ,
          Complex.ofReal_zero, zero_smul]
      · let p := (S.trivialization (b i)).toOpenPartialHomeomorph.symm ((t i z).1, 1)
        let y := (t i z).2
        have htbase : (t i).baseSet = (S.trivialization (b i)).baseSet :=
          (exists_associatedBundleTrivialization S.toIsPrincipalBundle
            (S.trivialization (b i)) (S.equivariant (b i))).choose_spec.1
        have hxb : (t i z).1 ∈ (S.trivialization (b i)).baseSet :=
          htbase ▸ (t i).mem_target.mp ((t i).map_source hbase.1)
        have hp : projection p = (t i z).1 :=
          (S.trivialization (b i)).proj_symm_apply' hxb
        have hpb : projection p ∈ (S.trivialization (b i)).baseSet := hp.symm ▸ hxb
        have hpc : projection p ∈ (c i).source := hp.symm ▸ hbase.2
        have hg : (S.trivialization (b i) p).2 = 1 := by
          exact congrArg Prod.snd ((S.trivialization (b i)).apply_symm_apply' hxb)
        have hrep : associatedBundleMk G P (OrthogonalSphere r) p y = z :=
          ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
            (S.trivialization (b i)) (S.equivariant (b i))).choose_spec.2.2 _ _ hxb).symm.trans
              ((t i).left_inv hbase.1)
        let w : Fin R.size → ℝ := fun _ ↦ 1
        have hw (j : Fin R.size) (_hj : (R.patch j).weight y ≠ 0) : w j = 1 := rfl
        -- Every normalized gauge evaluates the same canonical quotient map on this total covector.
        have h := associatedSphereVerticalFullSymbol_eq_saturated_finite_sum S σ τ q hq
          hσ hτ (b i) (c i) (hc i) p hpb hg hpc y R (θ i (c i (t i z).1)) w hw Ξ
        let value (z' : Z) : D z' →ₗ[ℂ] D' z' := ∑ j,
          if hz' : z' ∈ (Ci i j).source ∩
              (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
              (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
            let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) z' hz'.1.2).trans
              (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
            let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) z' hz'.2).trans
              (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
            ((θ i (c i (t i z).1) * (L j).input.cutoff ((L j).chart y) *
              (L j).output.cutoff ((L j).chart y) * w j : ℝ) : ℂ) •
                (eOut.symm.toLinearMap.comp
                  (((L j).symbol ((L j).chart y)
                    (split (covectorInChart (Ci i j) z' Ξ)).2).toLinearMap.comp eIn.toLinearMap))
          else 0
        let property (z' : Z) : Prop := value z' =
          (θ i (c i (t i z).1) : ℂ) • a z' (Ξ.comp split.symm.toContinuousLinearMap)
        have hvalue : property (associatedBundleMk G P (OrthogonalSphere r) p y) := h
        have htransport : property z := hrep ▸ hvalue
        simpa only [property, value, factor, cov, weight, ite_eq_left hbase, w, y, mul_one] using
          htransport
    · have hzero (j : Fin R.size) : factor i j = 0 := by
        have hnot : ¬z ∈ (Ci i j).source ∩
            (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
            (AD'.chart (b i, (L j).output.frameIndex)).baseSet := by
          intro hj
          exact hbase ⟨hj.1.1.1.1, hj.1.1.1.2.1⟩
        exact dite_eq_right hnot
      simp only [hzero, Finset.sum_const_zero, weight, ite_eq_right hbase,
        Complex.ofReal_zero, zero_smul]
  -- The actual base partition, after the exact sphere sum, recovers this same descended symbol.
  simp_rw [hpiece]
  rw [← Finset.sum_smul]
  have hsum : (∑ i, (weight i z : ℂ)) = 1 := by exact_mod_cast hpartition
  rw [hsum, one_smul]

end AtiyahSinger
