/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasQuantizationCutoffHomogeneity
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffRecovery
public import AtiyahSinger.Analysis.FiniteChartHomogeneousTail

/-!
# Homogeneous tails of the original descended vertical cutoff family

Public module ID: M0218.

Each original sphere quantization patch retains the local symbol of R(q).
Its product with the given compact base partition is supported in the same
associated product chart. Compact norm comparison supplies a common tail for
their exact finite sum under any specified upstairs cotangent metric.

The actual associated frames and the original full sphere covector remain
fixed throughout positive dilation. No arbitrary PDO representation is selected.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set
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

open scoped Classical in
/-- The actual finite vertical cutoff family retains the full symbol's homogeneous tail. -/
theorem exists_associatedSphereVerticalCutoff_homogeneous_of_tail
    (q : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (k : SmoothCotangentMetric (n := r) (M := OrthogonalSphere r)) (R₀ : ℝ)
    (hq : ∀ y ξ (s : ℝ), 0 < s → R₀ ≤ k.length y ξ →
      R₀ ≤ k.length y (s • ξ) → q.val y (s • ξ) = (s : ℂ) • q.val y ξ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
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
      (θ : ι → X → ℝ) (_hθK : ∀ i, HasCompactSupport (θ i))
      (_hθchart : ∀ i, tsupport (θ i) ⊆ (c i).target)
      (_hθbase : ∀ i, (c i).symm '' tsupport (θ i) ⊆ (S.trivialization (b i)).baseSet)
      (ε : ℝ) (_hε : 0 < ε),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := associatedSphereIsManifold S
      letI := linearModelChartedSpace split.symm Z
      letI := isManifold_linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let t := fun i ↦ associatedSphereTrivialization S (b i)
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      let Ci := fun i j ↦ associatedSphereProductChart S (b i) (c i) (L j).chart
      let field := fun (i : ι) (j : Fin R.size) (z : Z)
          (ν : CotangentFiber (n := n + r) z) ↦
        let cov := split (covectorInChart (Ci i j) z ν)
        if hz : z ∈ (Ci i j).source ∩
            (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
            (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
          let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) z hz.1.2).trans
            (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
          let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) z hz.2).trans
            (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
          ((θ i (c i (t i z).1) * (L j).input.cutoff ((L j).chart (t i z).2) *
            (L j).output.cutoff ((L j).chart (t i z).2) *
            productFrequencyCutoff ε ‖cov.2‖ ‖cov.1‖ : ℝ) : ℂ) •
              (eOut.symm.toLinearMap.comp
                (((L j).symbol ((L j).chart (t i z).2) cov.2).toLinearMap.comp eIn.toLinearMap))
        else (0 : D z →ₗ[ℂ] D' z)
      ∀ g : SmoothCotangentMetric (n := n + r) (M := Z),
        ∃ R₁ : ℝ, 0 < R₁ ∧ ∀ z ν (s : ℝ), 0 < s →
          R₁ ≤ g.length z ν → R₁ ≤ g.length z (s • ν) →
            (∑ i, ∑ j, field i j z (s • ν)) = (s : ℂ) • ∑ i, ∑ j, field i j z ν := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
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
  intro hσ hτ R b c hc θ hθK hθchart hθbase ε hε split
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro AD AD' t L Ci field g
  let χ (ij : ι × Fin R.size) (z : H) :=
    θ ij.1 (split z).1 * (R.patch ij.2).output.cutoff (split z).2
  have hsupport (ij : ι × Fin R.size) : tsupport (χ ij) ⊆
      split ⁻¹' (tsupport (θ ij.1) ×ˢ tsupport (R.patch ij.2).output.cutoff) := by
    apply closure_minimal ?_
      (((isClosed_tsupport (θ ij.1)).prod
        (isClosed_tsupport (R.patch ij.2).output.cutoff)).preimage split.continuous)
    intro z hz
    constructor
    · apply subset_tsupport
      intro h
      exact hz (by simp only [χ, h, zero_mul])
    · apply subset_tsupport
      intro h
      exact hz (by simp only [χ, h, mul_zero])
  have hχK (ij : ι × Fin R.size) : HasCompactSupport (χ ij) := by
    have hprod := ((hθK ij.1).prod (R.patch ij.2).output.compact_support).image
      split.symm.continuous
    apply hprod.of_isClosed_subset (isClosed_tsupport (χ ij))
    intro z hz
    exact ⟨split z, hsupport ij hz, split.symm_apply_apply z⟩
  have hχchart (ij : ι × Fin R.size) : tsupport (χ ij) ⊆ (Ci ij.1 ij.2).target := by
    intro z hz
    have hx := (hsupport ij hz).1
    have hy := (hsupport ij hz).2
    have hxb := hθbase ij.1 ⟨(split z).1, hx, rfl⟩
    have htbase : (t ij.1).baseSet = (S.trivialization (b ij.1)).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization (b ij.1)) (S.equivariant (b ij.1))).choose_spec.1
    have htarg : ((c ij.1).symm (split z).1, (R.patch ij.2).chart.symm (split z).2) ∈
        (t ij.1).target := (t ij.1).mem_target.mpr (htbase.symm ▸ hxb)
    exact ⟨Set.mem_univ _, ⟨hθchart ij.1 hx, ((R.patch ij.2).output.support_subset hy).1⟩,
      htarg⟩
  have hCi (ij : ι × Fin R.size) :
      Ci ij.1 ij.2 ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S (b ij.1) (c ij.1) (hc ij.1)
      (R.patch ij.2).chart (R.patch ij.2).chart_mem_atlas
  have hzero (ij : ι × Fin R.size) (z : Z)
      (hz : z ∉ (Ci ij.1 ij.2).symm '' tsupport (χ ij))
      (ν : CotangentFiber (n := n + r) z) : field ij.1 ij.2 z ν = 0 := by
    dsimp only [field]
    split_ifs with hf
    · have hcoords : split (Ci ij.1 ij.2 z) =
          (c ij.1 (t ij.1 z).1, (L ij.2).chart (t ij.1 z).2) :=
        split.apply_symm_apply _
      have hcut : θ ij.1 (c ij.1 (t ij.1 z).1) *
          (L ij.2).output.cutoff ((L ij.2).chart (t ij.1 z).2) = 0 := by
        by_contra h
        apply hz
        refine ⟨Ci ij.1 ij.2 z, ?_, (Ci ij.1 ij.2).left_inv hf.1.1⟩
        apply subset_tsupport
        change χ ij (Ci ij.1 ij.2 z) ≠ 0
        dsimp only [χ]
        rw [hcoords]
        exact h
      rcases mul_eq_zero.mp hcut with h | h
      · simp only [h, zero_mul, Complex.ofReal_zero, zero_smul]
      · simp only [h, mul_zero, zero_mul, Complex.ofReal_zero, zero_smul]
    · rfl
  let qA := nativeAtlasGlobalSymbol 1 q
  have hqA : ∀ y ξ (s : ℝ), 0 < s → R₀ ≤ k.length y ξ →
      R₀ ≤ k.length y (s • ξ) → qA.val y (s • ξ) = (s : ℂ) • qA.val y ξ := by
    intro y ξ s hs hξ hsξ
    change (q.val y (s • ξ)).toLinearMap = (s : ℂ) • (q.val y ξ).toLinearMap
    rw [hq y ξ s hs hξ hsξ]
    rfl
  choose Rj hRj hlocal using fun j ↦
    (R.patch j).exists_productCutoff_localSymbol_homogeneous_of_tail
      («Y» := X) qA k R₀ hqA ε hε
  let D₀ := 1 + ‖split.symm.toContinuousLinearMap‖
  have hD₀ : 0 < D₀ := add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg _)
  have hnorm (ν : H) : ‖ν‖ ≤ D₀ * (‖(split ν).2‖ + ‖(split ν).1‖) := by
    have hsum : ‖split ν‖ ≤ ‖(split ν).2‖ + ‖(split ν).1‖ := by
      exact max_le (le_add_of_nonneg_left (norm_nonneg _))
        (le_add_of_nonneg_right (norm_nonneg _))
    calc
      ‖ν‖ = ‖split.symm (split ν)‖ := congrArg norm (split.symm_apply_apply ν).symm
      _ ≤ ‖split.symm.toContinuousLinearMap‖ * ‖split ν‖ :=
        split.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ D₀ * (‖(split ν).2‖ + ‖(split ν).1‖) :=
        mul_le_mul (le_add_of_nonneg_left zero_le_one) hsum (norm_nonneg _) hD₀.le
  have htail (ij : ι × Fin R.size) (z : Z)
      (hz : z ∈ (Ci ij.1 ij.2).symm '' tsupport (χ ij)) (ν : H) (s : ℝ) (hs : 0 < s)
      (hν : D₀ * Rj ij.2 ≤ ‖ν‖) (hsν : D₀ * Rj ij.2 ≤ ‖s • ν‖) :
      field ij.1 ij.2 z (covectorFromChart (Ci ij.1 ij.2) z (s • ν)) =
        (s : ℂ) • field ij.1 ij.2 z (covectorFromChart (Ci ij.1 ij.2) z ν) := by
    obtain ⟨w, hw, hwz⟩ := hz
    have hzC : z ∈ (Ci ij.1 ij.2).source :=
      hwz ▸ (Ci ij.1 ij.2).map_target (hχchart ij hw)
    have hcoord (η : H) :
        covectorInChart (Ci ij.1 ij.2) z (covectorFromChart (Ci ij.1 ij.2) z η) = η := by
      have hdiff : (Ci ij.1 ij.2).MDifferentiable (𝓡 (n + r)) (𝓡 (n + r)) :=
        ⟨(contMDiffOn_of_mem_maximalAtlas (hCi ij)).mdifferentiableOn (by simp),
          (contMDiffOn_symm_of_mem_maximalAtlas (hCi ij)).mdifferentiableOn (by simp)⟩
      have hderiv := hdiff.comp_symm_deriv ((Ci ij.1 ij.2).map_source hzC)
      rw [(Ci ij.1 ij.2).left_inv hzC] at hderiv
      ext a
      change inner ℝ η ((mfderiv _ _ (Ci ij.1 ij.2) z)
        ((mfderiv _ _ (Ci ij.1 ij.2).symm (Ci ij.1 ij.2 z))
          (EuclideanSpace.single a 1))) = η a
      have h := congrArg (fun T : H →L[ℝ] H ↦ T (EuclideanSpace.single a 1)) hderiv
      change (mfderiv _ _ (Ci ij.1 ij.2) z)
        ((mfderiv _ _ (Ci ij.1 ij.2).symm (Ci ij.1 ij.2 z))
          (EuclideanSpace.single a 1)) = EuclideanSpace.single a 1 at h
      rw [h]
      simp [EuclideanSpace.inner_single_right]
    have hlarge := le_of_mul_le_mul_left (hν.trans (hnorm ν)) hD₀
    have hlarge' := le_of_mul_le_mul_left (hsν.trans (hnorm (s • ν))) hD₀
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd] at hlarge'
    have hp := hlocal ij.2 ((L ij.2).chart (t ij.1 z).2)
      (split ν).2 (split ν).1 s hs hlarge hlarge'
    dsimp only [field]
    rw [hcoord (s • ν), hcoord ν]
    simp only [map_smul, Prod.smul_fst, Prod.smul_snd]
    split_ifs with hf
    · let eIn := (AD.frameLinearEquiv (b ij.1, (L ij.2).input.frameIndex) z hf.1.2).trans
        (EuclideanSpace.equiv (Fin (A.rank (L ij.2).input.frameIndex)) ℂ).symm.toLinearEquiv
      let eOut := (AD'.frameLinearEquiv (b ij.1, (L ij.2).output.frameIndex) z hf.2).trans
        (EuclideanSpace.equiv (Fin (A'.rank (L ij.2).output.frameIndex)) ℂ).symm.toLinearEquiv
      let transport :
          (EuclideanSpace ℂ (Fin (A.rank (L ij.2).input.frameIndex)) →L[ℂ]
            EuclideanSpace ℂ (Fin (A'.rank (L ij.2).output.frameIndex))) →ₗ[ℂ]
            (D z →ₗ[ℂ] D' z) := {
        toFun := fun T ↦ eOut.symm.toLinearMap.comp (T.toLinearMap.comp eIn.toLinearMap)
        map_add' := by intros; ext v; simp
        map_smul' := by intros; ext v; simp }
      let α := (L ij.2).symbol ((L ij.2).chart (t ij.1 z).2) (s • (split ν).2)
      let β := (L ij.2).symbol ((L ij.2).chart (t ij.1 z).2) (split ν).2
      let c₁ : ℂ := productFrequencyCutoff ε ‖s • (split ν).2‖ ‖s • (split ν).1‖
      let c₀ : ℂ := productFrequencyCutoff ε ‖(split ν).2‖ ‖(split ν).1‖
      change c₁ • α = (s : ℂ) • (c₀ • β) at hp
      have hp' := congrArg transport hp
      change transport (c₁ • α) = transport ((s : ℂ) • (c₀ • β)) at hp'
      rw [transport.map_smul c₁ α, transport.map_smul (s : ℂ) (c₀ • β),
        transport.map_smul c₀ β] at hp'
      let w := θ ij.1 (c ij.1 (t ij.1 z).1) *
        (L ij.2).input.cutoff ((L ij.2).chart (t ij.1 z).2) *
        (L ij.2).output.cutoff ((L ij.2).chart (t ij.1 z).2)
      change ((w * productFrequencyCutoff ε ‖s • (split ν).2‖ ‖s • (split ν).1‖ : ℝ) : ℂ) •
          transport α = (s : ℂ) •
            ((w * productFrequencyCutoff ε ‖(split ν).2‖ ‖(split ν).1‖ : ℝ) : ℂ) • transport β
      rw [Complex.ofReal_mul w
        (productFrequencyCutoff ε ‖s • (split ν).2‖ ‖s • (split ν).1‖),
        Complex.ofReal_mul w (productFrequencyCutoff ε ‖(split ν).2‖ ‖(split ν).1‖)]
      change ((w : ℂ) * c₁) • transport α = (s : ℂ) • ((w : ℂ) * c₀) • transport β
      calc
        ((w : ℂ) * c₁) • transport α = (w : ℂ) • (c₁ • transport α) := mul_smul _ _ _
        _ = (w : ℂ) • ((s : ℂ) • (c₀ • transport β)) := congrArg ((w : ℂ) • ·) hp'
        _ = (s : ℂ) • ((w : ℂ) • (c₀ • transport β)) := smul_comm _ _ _
        _ = (s : ℂ) • ((w : ℂ) * c₀) • transport β :=
          congrArg ((s : ℂ) • ·) (mul_smul (w : ℂ) c₀ (transport β)).symm
    · exact (smul_zero _).symm
  obtain ⟨R₁, hR₁, hscale⟩ := exists_sum_homogeneous_of_compact_chart_tails g
    (fun ij : ι × Fin R.size ↦ Ci ij.1 ij.2) hCi (fun ij ↦ tsupport (χ ij))
    hχK hχchart (fun ij ↦ field ij.1 ij.2) hzero (fun ij ↦ D₀ * Rj ij.2) htail
  refine ⟨R₁, hR₁, ?_⟩
  intro z ν s hs hν hsν
  simpa only [Fintype.sum_prod_type] using hscale z ν s hs hν hsν

end AtiyahSinger
