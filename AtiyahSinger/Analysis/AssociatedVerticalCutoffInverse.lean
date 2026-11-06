/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.NativeAtlasPseudodifferential
public import AtiyahSinger.Analysis.AssociatedProductCovectorCoordinates
public import AtiyahSinger.Analysis.AssociatedProductFiniteCotangentBounds
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolInverse
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbolSaturation
public import AtiyahSinger.Analysis.SplitCotangentCutoffSaturation

/-!
# Quantitative ellipticity of the actual finite vertical cutoff factor

Public module ID: M0219.

The original base cutoffs and fixed sphere quantization patches have one
common saturation cone on a compact target window. Their actual finite sum
then recovers the same canonical descended full symbol. The original
invariant metrics and the target's normalized principal representative give
its quantitative inverse bound, uniformly before epsilon, point and covector.
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

variable [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 2400000 in
-- Normalize the equivariant vertical cutoff factors and their original inverse bound.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
open scoped Classical in
/-- The actual vertical cutoff factor has the original uniform metric inverse bound in a cone. -/
theorem exists_associatedSphereVerticalCutoffFullSymbol_inverse_bound
    (q : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q.val = q.val)
    (hEll : IsEllipticFullGlobalSymbol (r := d) (q := e) F F' 1 q.val)
    (g : SmoothCotangentMetric (n := r) (M := OrthogonalSphere r))
    (h : SmoothHermitianMetric (n := r) (r := d) F)
    (k : SmoothHermitianMetric (n := r) (r := e) F')
    (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
      ∀ (g : G) (y : OrthogonalSphere r) (u v : F y),
      h.pairing (g • y) (σ.linearMap g y u) (σ.linearMap g y v) = h.pairing y u v)
    (kInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
      ∀ (g : G) (y : OrthogonalSphere r) (u v : F' y),
      k.pairing (g • y) (τ.linearMap g y u) (τ.linearMap g y v) = k.pairing y u v) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI := associatedSphereChartedSpace S
    let _a := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
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
      (b₀ : B) (c₀ : OpenPartialHomeomorph B X) (_hc₀ : c₀ ∈ atlas X B)
      (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
      (_hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
      (K : Set H) (_hK : IsCompact K)
      (_hKChart : K ⊆ (associatedSphereProductChart S b₀ c₀ d₀).target)
      (e₀ : Trivialization (EuclideanSpace ℂ (Fin d)) (π (EuclideanSpace ℂ (Fin d)) F))
      (f₀ : Trivialization (EuclideanSpace ℂ (Fin e)) (π (EuclideanSpace ℂ (Fin e)) F'))
      [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
      (Ky : Set (OrthogonalSphere r)) (_hKy : IsCompact Ky)
      (_hKye : Ky ⊆ d₀.source ∩ e₀.baseSet) (_hKyf : Ky ⊆ d₀.source ∩ f₀.baseSet)
      (_hKfiber : ∀ z ∈ K, (associatedSphereTrivialization S b₀
        ((associatedSphereProductChart S b₀ c₀ d₀).symm z)).2 ∈ Ky)
      (δ₀ : ℝ) (_hδ₀ : 0 < δ₀),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let CP := associatedSphereProductChart S b₀ c₀ d₀
      let t := fun i ↦ associatedSphereTrivialization S (b i)
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      let Ci := fun i j ↦ associatedSphereProductChart S (b i) (c i) (L j).chart
      let weight := fun i (z : Z) ↦
        if z ∈ (t i).source ∧ (t i z).1 ∈ (c i).source then
          θ i (c i (t i z).1) else 0
      (∀ z ∈ K, ∑ i, weight i (CP.symm z) = 1) →
      ∃ δ ε₀ R₀ M : ℝ, 0 < δ ∧ δ ≤ δ₀ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R₀ ∧ 0 ≤ M ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ z ∈ K, ∀ ξ η, δ * ‖ξ‖ ≤ ‖η‖ → R₀ ≤ ‖η‖ →
          let coefficient : ℝ := M / (1 + ‖η‖) ^ 2
          let pre := CP.symm z
          let Ξ := covectorFromChart CP pre (split.symm (ξ, η))
          let cov := fun i j ↦ split (covectorInChart (Ci i j) pre Ξ)
          let factor := fun i j ↦
            if hz : pre ∈ (Ci i j).source ∩
                (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
                (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
              let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) pre hz.1.2).trans
                (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
              let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) pre hz.2).trans
                (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
              ((θ i (c i (t i pre).1) * (L j).input.cutoff ((L j).chart (t i pre).2) *
                (L j).output.cutoff ((L j).chart (t i pre).2) *
                productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ : ℝ) : ℂ) •
                  (eOut.symm.toLinearMap.comp
                    (((L j).symbol ((L j).chart (t i pre).2) (cov i j).2).toLinearMap.comp
                      eIn.toLinearMap))
            else (0 : D pre →ₗ[ℂ] D' pre)
          let Q := ∑ i, ∑ j, factor i j
          Function.Bijective Q ∧ ∀ u : D pre,
            ((associatedEquivariantMetricCore S.toIsPrincipalBundle σ
              h.toContinuousHermitianMetric pre).inner u u).re ≤ coefficient *
                ((associatedEquivariantMetricCore S.toIsPrincipalBundle τ
                  k.toContinuousHermitianMetric pre).inner (Q u) (Q u)).re := by
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
  intro hσ hτ R b c hc θ hθK hθchart hθbase b₀ c₀ hc₀ d₀ hd₀ K hK hKChart
    e₀ f₀ _ _ Ky hKy hKye hKyf hKfiber δ₀ hδ₀ split
  let := linearModelChartedSpace split.symm Z
  intro AD AD' CP t L Ci weight hpartition
  obtain ⟨R₀, M, hR₀, hM, hinverse⟩ :=
    exists_associatedSphereVerticalFullSymbol_inverse_bound S σ τ q hq hEll g h k
      hInvariant kInvariant b₀ c₀ hc₀ d₀ hd₀ e₀ f₀ Ky hKy hKye hKyf
  -- The original product cutoff supports provide a single finite family of actual overlaps.
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
  let support (ij : ι × Fin R.size) := (Ci ij.1 ij.2).symm '' tsupport (χ ij)
  have hs (ij : ι × Fin R.size) : IsCompact (support ij) :=
    (hχK ij).image_of_continuousOn ((Ci ij.1 ij.2).continuousOn_symm.mono (hχchart ij))
  have hsChart (ij : ι × Fin R.size) : support ij ⊆ (Ci ij.1 ij.2).source := by
    rintro z ⟨x, hx, rfl⟩
    exact (Ci ij.1 ij.2).map_target (hχchart ij hx)
  let e := fun ij : ι × Fin R.size ↦ (Ci ij.1 ij.2).symm.trans CP
  let pr := (ContinuousLinearMap.fst ℝ X Y).comp split.toContinuousLinearMap
  let qr := (ContinuousLinearMap.snd ℝ X Y).comp split.toContinuousLinearMap
  let inx := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ X Y)
  let iny := split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ X Y)
  obtain ⟨D₀, hD₀, hbound⟩ := exists_associatedSphereProductChart_finite_cotangent_block_bounds S
    (fun ij : ι × Fin R.size ↦ b ij.1) (fun ij ↦ c ij.1) (fun ij ↦ hc ij.1)
    (fun ij ↦ (R.patch ij.2).chart) (fun ij ↦ (R.patch ij.2).chart_mem_atlas)
    b₀ c₀ hc₀ d₀ hd₀ support hs hsChart K hK hKChart
  let Active := { iz : (ι × Fin R.size) × H //
    iz.2 ∈ K ∧ CP.symm iz.2 ∈ support iz.1 }
  let A₀ (iz : Active) :=
    (fderiv ℝ ((c iz.val.1.1).symm.trans c₀) (pr ((e iz.val.1).symm iz.val.2))).adjoint
  let B₀ (iz : Active) :=
    (qr.comp ((fderiv ℝ (e iz.val.1) ((e iz.val.1).symm iz.val.2)).comp inx)).adjoint
  let V₀ (iz : Active) :=
    (qr.comp ((fderiv ℝ (e iz.val.1) ((e iz.val.1).symm iz.val.2)).comp iny)).adjoint
  have hactive (iz : Active) :
      ‖A₀ iz‖ ≤ D₀ ∧ (∀ ξ, ‖ξ‖ ≤ D₀ * ‖A₀ iz ξ‖) ∧ ‖B₀ iz‖ ≤ D₀ ∧
        ‖V₀ iz‖ ≤ D₀ ∧ ∀ η, ‖η‖ ≤ D₀ * ‖V₀ iz η‖ :=
    hbound iz.val.1 iz.val.2 iz.property.1 iz.property.2
  obtain ⟨δ, ε₀, hδ, hδle, hε₀, hε₀one, hsaturate⟩ :=
    exists_productCutoffHomotopyWeight_eq_one_in_split_cones A₀ B₀ V₀ D₀ δ₀ hD₀ hδ₀
      (fun iz ↦ (hactive iz).1) (fun iz ↦ (hactive iz).2.1)
      (fun iz ↦ (hactive iz).2.2.1) (fun iz ↦ (hactive iz).2.2.2.1)
      (fun iz ↦ (hactive iz).2.2.2.2)
  refine ⟨δ, ε₀, R₀, M, hδ, hδle, hε₀, hε₀one, hR₀, hM, ?_⟩
  intro ε hε hεle z hz ξ η hcone hη coefficient pre Ξ cov factor Q
  have hsat (i : ι) (hzt : pre ∈ (t i).source) (hxc : (t i pre).1 ∈ (c i).source)
      (hθ : θ i (c i (t i pre).1) ≠ 0) (j : Fin R.size)
      (hw : (R.patch j).weight (t i pre).2 ≠ 0) :
      productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ = 1 := by
    let y := (t i pre).2
    change (R.patch j).weight y ≠ 0 at hw
    have hy : y ∈ (R.patch j).chart.source := by
      by_contra hnot
      exact hw (by simp only [AtlasQuantizationPatch.weight, ite_eq_right hnot])
    have hout : (R.patch j).output.cutoff ((R.patch j).chart y) ≠ 0 := by
      simpa only [AtlasQuantizationPatch.weight, ite_eq_left hy] using hw
    have hsource : pre ∈ (Ci i j).source := ⟨⟨hzt, hxc, hy⟩, Set.mem_univ _⟩
    have hχ : χ (i, j) (Ci i j pre) ≠ 0 := by
      change θ i (split (split.symm ((c i (t i pre).1,
        (R.patch j).chart (t i pre).2)))).1 *
          (R.patch j).output.cutoff (split (split.symm ((c i (t i pre).1,
            (R.patch j).chart (t i pre).2)))).2 ≠ 0
      rw [split.apply_symm_apply]
      exact mul_ne_zero hθ hout
    have hsupport : pre ∈ support (i, j) :=
      ⟨Ci i j pre, subset_tsupport _ hχ, (Ci i j).left_inv hsource⟩
    let iz : Active := ⟨((i, j), z), hz, hsupport⟩
    have hcoord := covectorInChart_associatedSphereProductChart_split
      S (b i) b₀ (c i) c₀ (hc i) hc₀ (L j).chart d₀ (L j).chart_mem_atlas hd₀
        z ⟨hKChart hz, hsource⟩ ξ η
    have hfrequency : cov i j = (A₀ iz ξ + B₀ iz η, V₀ iz η) := by
      change split (covectorInChart (Ci i j) pre Ξ) = _
      rw [hcoord, split.apply_symm_apply]
    rw [hfrequency]
    have hh := (hsaturate ε hε hεle (1 : Set.Icc (0 : ℝ) 1) iz ξ η).2 hcone
    simpa only [productCutoffHomotopyWeight, show ((1 : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl,
      one_smul, sub_self, zero_mul, one_mul, zero_add] using hh
  have heq : Q = a pre (Ξ.comp split.symm.toContinuousLinearMap) := by
    change (∑ i, ∑ j, factor i j) = a pre (Ξ.comp split.symm.toContinuousLinearMap)
    have hpiece (i : ι) : (∑ j, factor i j) =
        (weight i pre : ℂ) • a pre (Ξ.comp split.symm.toContinuousLinearMap) := by
      by_cases hbase : pre ∈ (t i).source ∧ (t i pre).1 ∈ (c i).source
      · by_cases hθ : θ i (c i (t i pre).1) = 0
        · have hzero (j : Fin R.size) : factor i j = 0 := by
            dsimp only [factor]
            split_ifs <;> simp only [hθ, zero_mul, Complex.ofReal_zero, zero_smul]
          simp only [hzero, Finset.sum_const_zero, weight, ite_eq_left hbase, hθ,
            Complex.ofReal_zero, zero_smul]
        · let p := (S.trivialization (b i)).toOpenPartialHomeomorph.symm ((t i pre).1, 1)
          let y := (t i pre).2
          have htbase : (t i).baseSet = (S.trivialization (b i)).baseSet :=
            (exists_associatedBundleTrivialization S.toIsPrincipalBundle
              (S.trivialization (b i)) (S.equivariant (b i))).choose_spec.1
          have hxb : (t i pre).1 ∈ (S.trivialization (b i)).baseSet :=
            htbase ▸ (t i).mem_target.mp ((t i).map_source hbase.1)
          have hp : projection p = (t i pre).1 :=
            (S.trivialization (b i)).proj_symm_apply' hxb
          have hpb : projection p ∈ (S.trivialization (b i)).baseSet := hp.symm ▸ hxb
          have hpc : projection p ∈ (c i).source := hp.symm ▸ hbase.2
          have hg : (S.trivialization (b i) p).2 = 1 := by
            exact congrArg Prod.snd ((S.trivialization (b i)).apply_symm_apply' hxb)
          have hrep : associatedBundleMk G P (OrthogonalSphere r) p y = pre :=
            ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
              (S.trivialization (b i)) (S.equivariant (b i))).choose_spec.2.2 _ _ hxb).symm.trans
                ((t i).left_inv hbase.1)
          let w := fun j ↦ productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖
          have hw (j : Fin R.size) (hj : (R.patch j).weight y ≠ 0) : w j = 1 :=
            hsat i hbase.1 hbase.2 hθ j hj
          -- Every normalized gauge evaluates the same canonical map on this total covector.
          have h := associatedSphereVerticalFullSymbol_eq_saturated_finite_sum S σ τ q hq
            hσ hτ (b i) (c i) (hc i) p hpb hg hpc y R (θ i (c i (t i pre).1)) w hw Ξ
          let value (z' : Z) : D z' →ₗ[ℂ] D' z' := ∑ j,
            if hz' : z' ∈ (Ci i j).source ∩
                (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
                (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
              let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) z' hz'.1.2).trans
                (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
              let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) z' hz'.2).trans
                (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
              ((θ i (c i (t i pre).1) * (L j).input.cutoff ((L j).chart y) *
                (L j).output.cutoff ((L j).chart y) * w j : ℝ) : ℂ) •
                  (eOut.symm.toLinearMap.comp
                    (((L j).symbol ((L j).chart y)
                      (split (covectorInChart (Ci i j) z' Ξ)).2).toLinearMap.comp eIn.toLinearMap))
            else 0
          let property (z' : Z) : Prop := value z' =
            (θ i (c i (t i pre).1) : ℂ) • a z' (Ξ.comp split.symm.toContinuousLinearMap)
          have hvalue : property (associatedBundleMk G P (OrthogonalSphere r) p y) := h
          have htransport : property pre := hrep ▸ hvalue
          simpa only [property, value, factor, cov, weight, ite_eq_left hbase, w, y] using
            htransport
      · have hzero (j : Fin R.size) : factor i j = 0 := by
          have hnot : ¬pre ∈ (Ci i j).source ∩
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
    have hsum : (∑ i, (weight i pre : ℂ)) = 1 := by exact_mod_cast hpartition z hz
    rw [hsum, one_smul]
  -- The same normalized target representative transfers the canonical vertical inverse estimate.
  rw [heq]
  let t₀ := associatedSphereTrivialization S b₀
  have hpre : pre ∈ CP.source := CP.map_target (hKChart hz)
  have hpt : pre ∈ t₀.source := hpre.1.1
  have hpc : (t₀ pre).1 ∈ c₀.source := hpre.1.2.1
  have htbase : t₀.baseSet = (S.trivialization b₀).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b₀) (S.equivariant b₀)).choose_spec.1
  have hxb : (t₀ pre).1 ∈ (S.trivialization b₀).baseSet :=
    htbase ▸ t₀.mem_target.mp (t₀.map_source hpt)
  let p₀ := (S.trivialization b₀).toOpenPartialHomeomorph.symm ((t₀ pre).1, 1)
  let y₀ := (t₀ pre).2
  have hp₀ : projection p₀ = (t₀ pre).1 := (S.trivialization b₀).proj_symm_apply' hxb
  have hg₀ : (S.trivialization b₀ p₀).2 = 1 :=
    congrArg Prod.snd ((S.trivialization b₀).apply_symm_apply' hxb)
  have hrep : associatedBundleMk G P (OrthogonalSphere r) p₀ y₀ = pre :=
    ((exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b₀) (S.equivariant b₀)).choose_spec.2.2 _ _ hxb).symm.trans
        (t₀.left_inv hpt)
  have hb := hinverse p₀ (hp₀.symm ▸ hxb) hg₀ (hp₀.symm ▸ hpc)
    y₀ (hKfiber z hz) ξ η hη
  let hproperty (z' : Z) : Prop :=
    let Ξ' := covectorFromChart CP z' (split.symm (ξ, η))
    let Q' := a z' (Ξ'.comp split.symm.toContinuousLinearMap)
    Function.Bijective Q' ∧ ∀ u : D z',
      ((associatedEquivariantMetricCore S.toIsPrincipalBundle σ
        h.toContinuousHermitianMetric z').inner u u).re ≤ coefficient *
          ((associatedEquivariantMetricCore S.toIsPrincipalBundle τ
            k.toContinuousHermitianMetric z').inner (Q' u) (Q' u)).re
  have hvalue : hproperty (associatedBundleMk G P (OrthogonalSphere r) p₀ y₀) := hb
  change hproperty pre
  exact hrep ▸ hvalue

end AtiyahSinger
