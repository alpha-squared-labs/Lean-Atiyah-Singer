/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedProductVerticalCovector
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSymbol
public import AtiyahSinger.Geometry.AssociatedSmoothBundleDescent

/-!
# The original vertical finite factor in one sphere covector

Public module ID: M0224.

In a specified normalized principal representative, the actual finite vertical
factor is the same weighted sum of the original intrinsic sphere symbols.
Every coordinate frequency has the same sphere covector as its argument, by
the derivative formula for the original product charts. The associated frames
cancel only using their actual representative formulas. The original source
and target fiber ranks remain independent and may vary by sphere chart.

The real weights can be the actual SG frequency cutoffs or their saturated
values. No cancellation of that frequency partition, gauge invariance, or
principal equality is assumed. Exact recovery of a specified full sphere
representative follows by applying its actual finite partition identity.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
open scoped Manifold ContDiff Matrix.Norms.L2Operator

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B] [IsManifold (𝓡 n) ∞ B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  {F : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
  [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
  {F' : OrthogonalSphere r → Type*} [∀ y, AddCommGroup (F' y)] [∀ y, Module ℂ (F' y)]
  [TopologicalSpace (TotalSpace Unit F')] [IsFiniteRank F']
  (A : SmoothComplexBundleAtlas (n := r) F) (A' : SmoothComplexBundleAtlas (n := r) F')
  (σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F)
  (σ' : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F')

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The actual vertical finite factor acts through one original sphere covector. -/
theorem associatedSphereVerticalFactor_apply_eq_finiteSymbol
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A)
    (hσ' : σ'.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A')
    (b : B) (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (p : P) (hp : projection p ∈ (S.trivialization b).baseSet)
    (hg : (S.trivialization b p).2 = 1) (hx : projection p ∈ c.source)
    (y : OrthogonalSphere r) (N : ℕ) (L : Fin N → AtlasPseudodifferentialPiece A A' 1)
    (θ : ℝ) (w : Fin N → ℝ) :
    letI (z : Z) : AddCommGroup (D z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
    letI (z : Z) : Module ℂ (D z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
    letI (z : Z) : AddCommGroup (D' z) :=
      associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
    letI (z : Z) : Module ℂ (D' z) :=
      associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
    letI : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AD := associatedSphereSmoothBundleAtlas S A σ hσ
    let AD' := associatedSphereSmoothBundleAtlas S A' σ' hσ'
    let z := associatedBundleMk G P (OrthogonalSphere r) p y
    let t := (associatedSphereTrivialization S b).toOpenPartialHomeomorph
    ∀ ξ : TangentSpace (𝓡 (n + r)) z →L[ℝ] ℝ,
      let η : CotangentFiber (n := r) y :=
        ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r)) t.symm (t z)).comp
          (ContinuousLinearMap.inr ℝ X Y))
      let CP := fun j ↦ associatedSphereProductChart S b c (L j).chart
      let cov := fun j ↦ EuclideanSpace.finAddEquivProd (n := n) (m := r)
        (covectorInChart (CP j) z ξ)
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
      ∀ u : F y,
        (∑ j, factor j) (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u) =
          associatedEquivariantFiberMk S.toIsPrincipalBundle σ' p y rfl
            ((θ : ℂ) • ∑ j, (w j : ℂ) • (L j).globalSymbolFunction y η u) := by
  classical
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ' z
  let (z : Z) : Module ℂ (D' z) :=
    associatedEquivariantFiberModule S.toIsPrincipalBundle σ' z
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let AD := associatedSphereSmoothBundleAtlas S A σ hσ
  let AD' := associatedSphereSmoothBundleAtlas S A' σ' hσ'
  let z := associatedBundleMk G P (OrthogonalSphere r) p y
  let t := associatedSphereTrivialization S b
  let mi : F y →ₗ[ℂ] D z :=
    (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ p y rfl).mk'
  let mo : F' y →ₗ[ℂ] D' z :=
    (associatedEquivariantFiberMk_isLinear S.toIsPrincipalBundle σ' p y rfl).mk'
  have hforward : t z = (projection p, y) := by
    have h : t z = (projection p, (S.trivialization b p).2 • y) :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
    rw [hg, one_smul] at h
    exact h
  have hzt : z ∈ t.source := by
    have hbase : t.baseSet = (S.trivialization b).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization b) (S.equivariant b)).choose_spec.1
    exact t.mem_source.mpr (hbase.symm ▸ hp)
  have hbaseI (j : A.Index) : (AD.chart (b, j)).baseSet =
      t.source ∩ t ⁻¹' (univ ×ˢ (A.chart j).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.1
  have hbaseO (j : A'.Index) : (AD'.chart (b, j)).baseSet =
      t.source ∩ t ⁻¹' (univ ×ˢ (A'.chart j).baseSet) :=
    (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ'
      (S.trivialization b) (S.equivariant b) (A'.chart j) (A'.linear j)).choose_spec.1
  -- Each original associated frame is the original sphere frame on this same representative.
  have hframeI (j : A.Index) (hz : z ∈ (AD.chart (b, j)).baseSet)
      (hy : y ∈ (A.chart j).baseSet) (u : F y) :
      AD.frameLinearEquiv (b, j) z hz (mi u) = A.frameLinearEquiv j y hy u := by
    change (AD.chart (b, j) ⟨z, mi u⟩).2 = (A.chart j ⟨y, u⟩).2
    have h := (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ
      (S.trivialization b) (S.equivariant b) (A.chart j) (A.linear j)).choose_spec.2.2
        p y z rfl u hp
    rw [hg] at h
    exact h.trans (congrArg (fun v : TotalSpace Unit F ↦ (A.chart j v).2) (σ.one_map y u))
  have hframeO (j : A'.Index) (hz : z ∈ (AD'.chart (b, j)).baseSet)
      (hy : y ∈ (A'.chart j).baseSet) (u : F' y) :
      AD'.frameLinearEquiv (b, j) z hz (mo u) = A'.frameLinearEquiv j y hy u := by
    change (AD'.chart (b, j) ⟨z, mo u⟩).2 = (A'.chart j ⟨y, u⟩).2
    have h := (exists_associatedEquivariant_chart S.toIsPrincipalBundle σ'
      (S.trivialization b) (S.equivariant b) (A'.chart j) (A'.linear j)).choose_spec.2.2
        p y z rfl u hp
    rw [hg] at h
    exact h.trans (congrArg (fun v : TotalSpace Unit F' ↦ (A'.chart j v).2) (σ'.one_map y u))
  change ∀ ξ : TangentSpace (𝓡 (n + r)) z →L[ℝ] ℝ, _
  intro ξ η CP cov factor u
  change (∑ j, factor j) (mi u) = mo ((θ : ℂ) • ∑ j, (w j : ℂ) •
    (L j).globalSymbolFunction y η u)
  simp only [LinearMap.sum_apply, map_smul, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  let d := (L j).chart
  have hvalid : z ∈ (CP j).source ∩ (AD.chart (b, (L j).input.frameIndex)).baseSet ∩
      (AD'.chart (b, (L j).output.frameIndex)).baseSet ↔
      y ∈ d.source ∩ (A.chart (L j).input.frameIndex).baseSet ∩
        (A'.chart (L j).output.frameIndex).baseSet := by
    rw [hbaseI, hbaseO]
    constructor
    · intro hz
      have hd : y ∈ d.source := by
        have h := hz.1.1.1.2.2
        change (t z).2 ∈ d.source at h
        rw [hforward] at h
        exact h
      refine ⟨⟨hd, ?_⟩, ?_⟩
      · simpa only [mem_preimage, hforward, mem_prod, mem_univ, true_and] using hz.1.2.2
      · simpa only [mem_preimage, hforward, mem_prod, mem_univ, true_and] using hz.2.2
    · intro hy
      have hprod : (t z).1 ∈ c.source ∧ (t z).2 ∈ d.source := by
        rw [hforward]
        exact ⟨hx, hy.1.1⟩
      exact ⟨⟨⟨⟨hzt, hprod⟩, mem_univ _⟩,
        hzt, by simpa only [mem_preimage, hforward, mem_prod, mem_univ, true_and] using hy.1.2⟩,
        hzt, by simpa only [mem_preimage, hforward, mem_prod, mem_univ, true_and] using hy.2⟩
  by_cases hy : y ∈ d.source ∩ (A.chart (L j).input.frameIndex).baseSet ∩
      (A'.chart (L j).output.frameIndex).baseSet
  · have hz := hvalid.mpr hy
    have hcov : (cov j).2 = covectorInChart d y η := by
      have h := covectorInChart_associatedSphereProductChart_snd S b c hc d
        (L j).chart_mem_atlas z hz.1.1 ξ
      change (cov j).2 = covectorInChart d (t z).2 η at h
      rw [hforward] at h
      exact h
    let eIn := (AD.frameLinearEquiv (b, (L j).input.frameIndex) z hz.1.2).trans
      (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
    let eOut := (AD'.frameLinearEquiv (b, (L j).output.frameIndex) z hz.2).trans
      (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
    let e₀ := (A.frameLinearEquiv (L j).input.frameIndex y hy.1.2).trans
      (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
    let e₁ := (A'.frameLinearEquiv (L j).output.frameIndex y hy.2).trans
      (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
    have hi (w : F y) : eIn (mi w) = e₀ w := by
      exact congrArg (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm
        (hframeI _ hz.1.2 hy.1.2 w)
    have ho (w : F' y) : eOut (mo w) = e₁ w := by
      exact congrArg (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm
        (hframeO _ hz.2 hy.2 w)
    let s := (L j).symbol (d y) (covectorInChart d y η)
    have hconj : eOut.symm (s (eIn (mi u))) = mo (e₁.symm (s (e₀ u))) := by
      apply eOut.injective
      rw [eOut.apply_symm_apply, hi, ho, e₁.apply_symm_apply]
    dsimp only [factor]
    rw [dite_eq_left hz]
    change ((θ * (L j).input.cutoff (d y) * (L j).output.cutoff (d y) * w j : ℝ) : ℂ) •
      eOut.symm ((L j).symbol (d y) (cov j).2 (eIn (mi u))) = _
    rw [hcov, hconj]
    have hsymbol : (L j).globalSymbolFunction y η u =
        (((L j).output.cutoff (d y) * (L j).input.cutoff (d y) : ℝ) : ℂ) •
          e₁.symm (s (e₀ u)) := by
      unfold AtlasPseudodifferentialPiece.globalSymbolFunction
      rw [dite_eq_left hy]
      rfl
    rw [hsymbol, map_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  · have hz := mt hvalid.mp hy
    dsimp only [factor]
    rw [dite_eq_right hz]
    unfold AtlasPseudodifferentialPiece.globalSymbolFunction
    rw [dite_eq_right hy]
    simp only [LinearMap.zero_apply, map_zero, smul_zero]

end AtiyahSinger
