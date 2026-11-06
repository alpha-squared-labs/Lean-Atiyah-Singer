/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCutoffTensorInverse
public import AtiyahSinger.Geometry.AssociatedSphereCompactChartCover

/-!
# Finite compact native-covector inverse bounds for the actual cutoff factors

Public module ID: M0086.

The original local quantitative inverse estimates are transported to native
covectors on a finite cover by actual product charts. The exact C and R(q)
factors, four prescribed metric pairings, and original Hermitian core norms
are retained. No homogeneous tail or horizontal-lift provenance is needed.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Set MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

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

variable {a a' : ℕ} [T2Space B] [SecondCountableTopology B] [CompactSpace B]
  [MeasurableSpace B] [BorelSpace B]
  (E : B → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin a)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a)) E]
  [IsSmoothComplexBundle (n := n) (r := a) E]
  (E' : B → Type*) [∀ x, NormedAddCommGroup (E' x)] [∀ x, NormedSpace ℂ (E' x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin a')) E')]
  [FiberBundle (EuclideanSpace ℂ (Fin a')) E']
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin a')) E']
  [IsSmoothComplexBundle (n := n) (r := a') E']
  {μ : Measure B} [IsSmoothPositiveMeasure (n := n) μ]

variable [CompactSpace
  (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
-- Normalize the original cutoff factors and their inverse bounds on one finite cover.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option cleanup.letToHave false in
open scoped Classical in
/-- The original cutoff tensor factors have quantitative inverse bounds on one finite cover. -/
theorem exists_associatedSphereCutoffTensorSymbol_finite_inverse_bounds
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic)
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (hE : SmoothHermitianMetric (n := n) (r := a) E)
    (kE : SmoothHermitianMetric (n := n) (r := a') E')
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
      (J : AtlasBundlePresentation A) (R : AtlasQuantizationPresentation A A')
      (b : ι → B) (c : ι → OpenPartialHomeomorph B X) (_hc : ∀ i, c i ∈ atlas X B)
      (θ : ι → X → ℝ) (_hθK : ∀ i, HasCompactSupport (θ i))
      (_hθchart : ∀ i, tsupport (θ i) ⊆ (c i).target)
      (_hθbase : ∀ i, (c i).symm '' tsupport (θ i) ⊆ (S.trivialization (b i)).baseSet),
      let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
      letI := associatedSphereIsManifold S
      letI := linearModelChartedSpace split.symm Z
      letI := isManifold_linearModelChartedSpace split.symm Z
      let AD := associatedSphereSmoothBundleAtlas S A σ hσ
      let AD' := associatedSphereSmoothBundleAtlas S A' τ hτ
      let t := fun i ↦ associatedSphereTrivialization S (b i)
      let L := fun j ↦ (R.patch j).toPiece (nativeAtlasGlobalSymbol 1 q)
      let Ci := fun i j ↦ associatedSphereProductChart S (b i) (c i) (L j).chart
      let CH := fun i j ↦ associatedSphereProductChart S (C.center i) (C.piece i).chart (J.chart j)
      let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
      let weight := fun i (z : Z) ↦
        if z ∈ (t i).source ∧ (t i z).1 ∈ (c i).source then θ i (c i (t i z).1) else 0
      (∀ z : Z, ∑ i, weight i z = 1) →
      let pf (ε : ℝ) (pre : Z) (Ξ : CotangentFiber (n := n + r) pre) :=
          let covH := fun i j ↦ split (covectorInChart (CH i j) pre Ξ)
          (∑ i, ∑ j,
            ((J.cutoff j (associatedSphereTrivialization S (C.center i) pre).2 *
              productFrequencyCutoff ε ‖(covH i j).1‖ ‖(covH i j).2‖ : ℝ) : ℂ) •
                (C.piece i).globalSymbolFunction (base pre)
                  (covectorFromChart (C.piece i).chart (base pre) (covH i j).1)).toLinearMap
      let qf (ε : ℝ) (pre : Z) (Ξ : CotangentFiber (n := n + r) pre) :=
          let cov := fun i j ↦ split (covectorInChart (Ci i j) pre Ξ)
          let factor := fun i j ↦
            if hz : pre ∈ (Ci i j).source ∩
                (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
                (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
              let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) pre hz.1.2).trans
                (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
              let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) pre hz.2).trans
                (EuclideanSpace.equiv (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
              ((θ i (c i (base pre)) * (L j).input.cutoff ((L j).chart (t i pre).2) *
                (L j).output.cutoff ((L j).chart (t i pre).2) *
                productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ : ℝ) : ℂ) •
                  (eOut.symm.toLinearMap.comp
                    (((L j).symbol ((L j).chart (t i pre).2) (cov i j).2).toLinearMap.comp
                      eIn.toLinearMap))
            else (0 : D pre →ₗ[ℂ] D' pre)
         ∑ i, ∑ j, factor i j
      ∃ (N : ℕ) (CP : Fin N → OpenPartialHomeomorph Z H) (K : Fin N → Set Z),
        (∀ i, CP i ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z) ∧
        (∀ i, IsCompact (K i)) ∧ (∀ i, K i ⊆ (CP i).source) ∧
        (∀ pre : Z, ∃ i, pre ∈ K i) ∧
        ∀ i, ∃ ε₀ R₀ M : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ 0 < R₀ ∧ 0 ≤ M ∧
          ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ pre ∈ K i,
            ∀ Ξ : CotangentFiber (n := n + r) pre,
              R₀ ≤ ‖covectorInChart (CP i) pre Ξ‖ →
                let h₀ := hE.toCore (base pre)
                let h₁ := kE.toCore (base pre)
                let k₀ := associatedEquivariantMetricCore S.toIsPrincipalBundle σ
                  h.toContinuousHermitianMetric pre
                let k₁ := associatedEquivariantMetricCore S.toIsPrincipalBundle τ
                  k.toContinuousHermitianMetric pre
                ∀ (pi : E' (base pre) →ₗ[ℂ] E (base pre)) (qi : D' pre →ₗ[ℂ] D pre),
                  (∀ u v, h₁.inner (pf ε pre Ξ u) v = h₀.inner u (pi v)) →
                  (∀ u v, k₁.inner (qf ε pre Ξ u) v = k₀.inner u (qi v)) →
                  letI : Module ℂ (E (base pre)) := inferInstance
                  letI : Module ℂ (E' (base pre)) := inferInstance
                  letI : InnerProductSpace.Core ℂ (E (base pre)) := h₀
                  letI : InnerProductSpace.Core ℂ (E' (base pre)) := h₁
                  letI : InnerProductSpace.Core ℂ (D pre) := k₀
                  letI : InnerProductSpace.Core ℂ (D' pre) := k₁
                  letI : NormedAddCommGroup (E (base pre)) :=
                    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
                  letI : NormedAddCommGroup (E' (base pre)) :=
                    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
                  letI : NormedAddCommGroup (D pre) :=
                    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
                  letI : NormedAddCommGroup (D' pre) :=
                    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
                  letI : TopologicalSpace (D pre) :=
                    (inferInstance : PseudoMetricSpace (D pre)).toUniformSpace.toTopologicalSpace
                  letI : TopologicalSpace (D' pre) :=
                    (inferInstance : PseudoMetricSpace (D' pre)).toUniformSpace.toTopologicalSpace
                  letI : InnerProductSpace ℂ (E (base pre)) := InnerProductSpace.ofCore
                    (inferInstance : PreInnerProductSpace.Core ℂ _)
                  letI : InnerProductSpace ℂ (E' (base pre)) := InnerProductSpace.ofCore
                    (inferInstance : PreInnerProductSpace.Core ℂ _)
                  letI : InnerProductSpace ℂ (D pre) := InnerProductSpace.ofCore
                    (inferInstance : PreInnerProductSpace.Core ℂ _)
                  letI : InnerProductSpace ℂ (D' pre) := InnerProductSpace.ofCore
                    (inferInstance : PreInnerProductSpace.Core ℂ _)
                  let T := reciprocalTensorSymbol (pf ε pre Ξ) pi (qf ε pre Ξ) qi
                  Function.Bijective T ∧ ∀ u,
                    ‖u‖ ≤ (M / (1 + ‖covectorInChart (CP i) pre Ξ‖)) * ‖T u‖ :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let := associatedSphereChartedSpace S
  intro A A' D D'
  let (z : Z) : AddCommGroup (D z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle σ z
  let (z : Z) : Module ℂ (D z) := associatedEquivariantFiberModule S.toIsPrincipalBundle σ z
  let (z : Z) : AddCommGroup (D' z) :=
    associatedEquivariantFiberAddCommGroup S.toIsPrincipalBundle τ z
  let (z : Z) : Module ℂ (D' z) := associatedEquivariantFiberModule S.toIsPrincipalBundle τ z
  intro hσ hτ J R b c hc θ hθK hθchart hθbase split
  let := associatedSphereIsManifold S
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro AD AD' t L Ci CH base weight hpartition pf qf
  -- Each retained center supplies the actual four frames used by its local inverse estimate.
  let t₀ (z : Z) := associatedSphereTrivialization S (base z)
  let y₀ (z : Z) := (t₀ z z).2
  let eB (z : Z) := trivializationAt (EuclideanSpace ℂ (Fin a)) E (base z)
  let fB (z : Z) := trivializationAt (EuclideanSpace ℂ (Fin a')) E' (base z)
  let eF (z : Z) := trivializationAt (EuclideanSpace ℂ (Fin d)) F (y₀ z)
  let fF (z : Z) := trivializationAt (EuclideanSpace ℂ (Fin e)) F' (y₀ z)
  let U (z : Z) : Set Z :=
    base ⁻¹' ((eB z).baseSet ∩ (fB z).baseSet) ∩
      ((t₀ z).source ∩ (t₀ z) ⁻¹' (univ ×ˢ ((eF z).baseSet ∩ (fF z).baseSet)))
  have hU (z : Z) : IsOpen (U z) :=
    (((eB z).open_baseSet.inter (fB z).open_baseSet).preimage base.continuous).inter
      ((t₀ z).toOpenPartialHomeomorph.isOpen_inter_preimage
        (isOpen_univ.prod ((eF z).open_baseSet.inter (fF z).open_baseSet)))
  have hmemU (z : Z) : z ∈ U z := by
    have htbase : (t₀ z).baseSet = (S.trivialization (base z)).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization (base z)) (S.equivariant (base z))).choose_spec.1
    exact ⟨⟨FiberBundle.mem_baseSet_trivializationAt _ _ _,
        FiberBundle.mem_baseSet_trivializationAt _ _ _⟩,
      (t₀ z).mem_source.mpr (htbase.symm ▸ S.mem_baseSet (base z)), mem_univ _,
        FiberBundle.mem_baseSet_trivializationAt _ _ _,
        FiberBundle.mem_baseSet_trivializationAt _ _ _⟩
  obtain ⟨N, point, K, hK, hKChart, hKU, hcover⟩ :=
    exists_associatedSphereProductChart_compact_cover S U hU hmemU
  let b₀ (i : Fin N) := base (point i)
  let c₀ (i : Fin N) := chartAt X (b₀ i)
  let d₀ (i : Fin N) := chartAt Y (y₀ (point i))
  let CP (i : Fin N) := associatedSphereProductChart S (b₀ i) (c₀ i) (d₀ i)
  have hKCP (i : Fin N) : K i ⊆ (CP i).target := hKChart i
  have hCP (i : Fin N) : CP i ∈ IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S (b₀ i) (c₀ i) (chart_mem_atlas X _)
      (d₀ i) (chart_mem_atlas Y _)
  let fiber (i : Fin N) (z : H) := (t₀ (point i) ((CP i).symm z)).2
  let Ky (i : Fin N) : Set (OrthogonalSphere r) := fiber i '' K i
  have hKy (i : Fin N) : IsCompact (Ky i) := by
    apply (hK i).image_of_continuousOn
    exact continuous_snd.comp_continuousOn
      ((t₀ (point i)).toOpenPartialHomeomorph.continuousOn.comp
        ((CP i).symm.continuousOn.mono (hKCP i))
        (fun z hz ↦ ((CP i).map_target (hKCP i hz)).1.1))
  have hKye (i : Fin N) : Ky i ⊆ (d₀ i).source ∩ (eF (point i)).baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨((CP i).map_target (hKCP i hz)).1.2.2, (hKU i z hz).2.2.2.1⟩
  have hKyf (i : Fin N) : Ky i ⊆ (d₀ i).source ∩ (fF (point i)).baseSet := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨((CP i).map_target (hKCP i hz)).1.2.2, (hKU i z hz).2.2.2.2⟩
  have hKfiber (i : Fin N) (z : H) (hz : z ∈ K i) : fiber i z ∈ Ky i := ⟨z, hz, rfl⟩
  have hframe (i : Fin N) (z : H) (hz : z ∈ K i) :
      base ((CP i).symm z) ∈ (eB (point i)).baseSet ∩ (fB (point i)).baseSet :=
    (hKU i z hz).1
  -- Each actual product window retains the original base and sphere frame conditions.
  have hlocal (i : Fin N) :=
    exists_associatedSphereCutoffTensorSymbol_inverse_bound S σ τ E E' C hC gB hE kE
      q hq hEll g h k hInvariant kInvariant hσ hτ J R b c hc θ hθK hθchart hθbase
      (b₀ i) (c₀ i) (chart_mem_atlas X _) (d₀ i) (chart_mem_atlas Y _)
      (K i) (hK i) (hKCP i) (eF (point i)) (fF (point i))
      (Ky i) (hKy i) (hKye i) (hKyf i) (hKfiber i)
      (eB (point i)) (fB (point i)) (hframe i) (fun z _ ↦ hpartition ((CP i).symm z))
  let KN (i : Fin N) : Set Z := (CP i).symm '' K i
  have hKN (i : Fin N) : IsCompact (KN i) :=
    (hK i).image_of_continuousOn ((CP i).continuousOn_symm.mono (hKCP i))
  have hKNsource (i : Fin N) : KN i ⊆ (CP i).source := by
    rintro _ ⟨z, hz, rfl⟩
    exact (CP i).map_target (hKCP i hz)
  have hKNcover (pre : Z) : ∃ i, pre ∈ KN i := by
    obtain ⟨i, hsource, hwindow⟩ := hcover pre
    exact ⟨i, CP i pre, hwindow, (CP i).left_inv hsource⟩
  refine ⟨N, CP, KN, hCP, hKN, hKNsource, hKNcover, ?_⟩
  intro i
  obtain ⟨ε₀, rad, M, hε₀, hε₀one, hrad, hM, hinverse⟩ := hlocal i
  let op : ℝ := ‖split.symm.toContinuousLinearMap‖
  refine ⟨ε₀, (1 + op) * rad, (1 + op) * M, hε₀, hε₀one,
    mul_pos (by dsimp [op]; positivity) hrad,
    mul_nonneg (by dsimp [op]; positivity) hM, ?_⟩
  intro ε hε hεsmall pre hpre Ξ hΞ
  have hsource : pre ∈ (CP i).source := hKNsource i hpre
  have hwindow : CP i pre ∈ K i := by
    obtain ⟨z, hz, rfl⟩ := hpre
    rwa [(CP i).right_inv (hKCP i hz)]
  let ν := covectorInChart (CP i) pre Ξ
  let ξ := (split ν).1
  let η := (split ν).2
  have hsplit : split.symm (ξ, η) = ν := split.symm_apply_apply ν
  have hnorm : ‖ν‖ ≤ op * (‖ξ‖ + ‖η‖) := by
    calc
      ‖ν‖ = ‖split.symm (ξ, η)‖ := congrArg norm hsplit.symm
      _ ≤ op * ‖(ξ, η)‖ := split.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ op * (‖ξ‖ + ‖η‖) := mul_le_mul_of_nonneg_left
        (by simpa only [Prod.norm_def] using
          (max_le_add_of_nonneg (norm_nonneg ξ) (norm_nonneg η))) (norm_nonneg _)
  have hfreq : rad ≤ ‖ξ‖ + ‖η‖ := by
    change (1 + op) * rad ≤ ‖ν‖ at hΞ
    nlinarith [norm_nonneg split.symm.toContinuousLinearMap]
  have hcoefficient : M / (1 + ‖ξ‖ + ‖η‖) ≤
      ((1 + op) * M) / (1 + ‖ν‖) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hm := mul_le_mul_of_nonneg_left hnorm hM
    have ho := mul_nonneg (norm_nonneg split.symm.toContinuousLinearMap) hM
    nlinarith
  -- Recover the original native covector in the selected maximal chart before specializing.
  have hback : covectorFromChart (CP i) pre ν = Ξ := by
    have hcoord : innerSL ℝ ν =
        Ξ.comp (mfderiv (𝓡 (n + r)) (𝓡 (n + r)) (CP i).symm (CP i pre)) := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin (n + r)) ℝ).toBasis.ext
      intro j
      simp [ν, covectorInChart, EuclideanSpace.basisFun_apply,
        EuclideanSpace.inner_single_right]
      rfl
    have hdiff : (CP i).MDifferentiable (𝓡 (n + r)) (𝓡 (n + r)) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas (hCP i)).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas (hCP i)).mdifferentiableOn (by simp)⟩
    ext v
    have h := congrArg (fun T : TangentSpace (𝓡 (n + r)) pre →L[ℝ]
      TangentSpace (𝓡 (n + r)) pre ↦ T v) (hdiff.symm_comp_deriv hsource)
    change (mfderiv _ _ (CP i).symm (CP i pre)) ((mfderiv _ _ (CP i) pre) v) = v at h
    calc
      covectorFromChart (CP i) pre ν v =
          Ξ ((mfderiv _ _ (CP i).symm (CP i pre)) ((mfderiv _ _ (CP i) pre) v)) :=
        DFunLike.congr_fun hcoord ((mfderiv _ _ (CP i) pre) v)
      _ = Ξ v := congrArg Ξ h
  -- The active chart guard identifies the trivialization base with the original projection.
  let qRaw (z : Z) (Ξ : CotangentFiber (n := n + r) z) :=
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
          (L j).output.cutoff ((L j).chart (t i z).2) *
          productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ : ℝ) : ℂ) •
            (eOut.symm.toLinearMap.comp
              (((L j).symbol ((L j).chart (t i z).2) (cov i j).2).toLinearMap.comp
                eIn.toLinearMap))
      else (0 : D z →ₗ[ℂ] D' z)
    ∑ i, ∑ j, factor i j
  have hqeq (z : Z) (ξ : CotangentFiber (n := n + r) z) : qf ε z ξ = qRaw z ξ := by
    dsimp only [qf, qRaw]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro l _
    split_ifs with hz
    · have hsource : z ∈ (t j).source := hz.1.1.1.1
      rw [(t j).coe_fst hsource]
    · rfl
  let claim (pre : Z) (Ξ : CotangentFiber (n := n + r) pre) : Prop :=
    let h₀ := hE.toCore (base pre)
    let h₁ := kE.toCore (base pre)
    let k₀ := associatedEquivariantMetricCore S.toIsPrincipalBundle σ
      h.toContinuousHermitianMetric pre
    let k₁ := associatedEquivariantMetricCore S.toIsPrincipalBundle τ
      k.toContinuousHermitianMetric pre
    ∀ (pi : E' (base pre) →ₗ[ℂ] E (base pre)) (qi : D' pre →ₗ[ℂ] D pre),
      (∀ u v, h₁.inner (pf ε pre Ξ u) v = h₀.inner u (pi v)) →
      (∀ u v, k₁.inner (qRaw pre Ξ u) v = k₀.inner u (qi v)) →
      letI : Module ℂ (E (base pre)) := inferInstance
      letI : Module ℂ (E' (base pre)) := inferInstance
      letI : InnerProductSpace.Core ℂ (E (base pre)) := h₀
      letI : InnerProductSpace.Core ℂ (E' (base pre)) := h₁
      letI : InnerProductSpace.Core ℂ (D pre) := k₀
      letI : InnerProductSpace.Core ℂ (D' pre) := k₁
      letI : NormedAddCommGroup (E (base pre)) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      letI : NormedAddCommGroup (E' (base pre)) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      letI : NormedAddCommGroup (D pre) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      letI : NormedAddCommGroup (D' pre) :=
        InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
      letI : TopologicalSpace (D pre) :=
        (inferInstance : PseudoMetricSpace (D pre)).toUniformSpace.toTopologicalSpace
      letI : TopologicalSpace (D' pre) :=
        (inferInstance : PseudoMetricSpace (D' pre)).toUniformSpace.toTopologicalSpace
      letI : InnerProductSpace ℂ (E (base pre)) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      letI : InnerProductSpace ℂ (E' (base pre)) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      letI : InnerProductSpace ℂ (D pre) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      letI : InnerProductSpace ℂ (D' pre) := InnerProductSpace.ofCore
        (inferInstance : PreInnerProductSpace.Core ℂ _)
      let T := reciprocalTensorSymbol (pf ε pre Ξ) pi (qRaw pre Ξ) qi
      Function.Bijective T ∧ ∀ u, ‖u‖ ≤ (M / (1 + ‖ξ‖ + ‖η‖)) * ‖T u‖
  have hraw : claim ((CP i).symm (CP i pre))
      (covectorFromChart (CP i) ((CP i).symm (CP i pre)) (split.symm (ξ, η))) :=
    hinverse ε hε hεsmall (CP i pre) hwindow ξ η hfreq
  rw [(CP i).left_inv hsource, hsplit, hback] at hraw
  dsimp only [claim] at hraw
  rw [← hqeq] at hraw
  intro h₀ h₁ k₀ k₁ pi qi hpi hqi
  let : Module ℂ (E (base pre)) := inferInstance
  let : Module ℂ (E' (base pre)) := inferInstance
  let : InnerProductSpace.Core ℂ (E (base pre)) := h₀
  let : InnerProductSpace.Core ℂ (E' (base pre)) := h₁
  let : InnerProductSpace.Core ℂ (D pre) := k₀
  let : InnerProductSpace.Core ℂ (D' pre) := k₁
  let : NormedAddCommGroup (E (base pre)) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (E' (base pre)) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (D pre) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : NormedAddCommGroup (D' pre) :=
    InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let : InnerProductSpace ℂ (E (base pre)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (E' (base pre)) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (D pre) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  let : InnerProductSpace ℂ (D' pre) := InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ _)
  dsimp only at hraw ⊢
  obtain ⟨hbij, hbound⟩ := hraw pi qi hpi hqi
  refine ⟨hbij, ?_⟩
  intro u
  exact (hbound u).trans (mul_le_mul_of_nonneg_right hcoefficient (norm_nonneg _))

end AtiyahSinger
