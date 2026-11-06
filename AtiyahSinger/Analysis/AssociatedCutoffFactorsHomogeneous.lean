/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedCutoffTensorHomotopy
public import AtiyahSinger.Analysis.AssociatedCutoffTensorGlobalHomotopy
public import AtiyahSinger.Analysis.AssociatedVerticalCutoffHomogeneity
public import AtiyahSinger.Analysis.PrincipalLocalizationHorizontalHomogeneity
public import AtiyahSinger.Analysis.QuantizationPieceCutoffHomogeneity
public import AtiyahSinger.Geometry.AssociatedSphereCompactChartCover

/-!
# The actual two cutoff factors have one homogeneous invertible exterior

Public module ID: M0085.

The horizontal pieces retain their original quantization origins and the
vertical pieces are exactly R(q). Their two original full-symbol tails give
one common metric exterior. The affine path at s = 1 proves the
reciprocal matrix invertible there with the same metric adjoints.
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
local notation "YS" => EuclideanSpace ℝ (Fin r)
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
set_option maxHeartbeats 2400000 in
-- Normalize the original cutoff factors with exact homogeneous tails and reciprocal blocks.
set_option cleanup.letToHave false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- The original C/R(q) factors supply exact homogeneous tails and reciprocal invertibility. -/
theorem associated_actual_cutoff_factors_homogeneous_bijective_call
    (C : PrincipalPseudodifferentialLocalization (a := a) (a' := a') S E E' μ 1)
    (hC : C.baseOperator.IsElliptic)
    (Rp : QuantizationPresentation (n := n) (r := a) (q := a') E E')
    (p : globalSymbolSpace (n := n) (r := a) (q := a') E E' 1)
    (index : Fin C.size → Fin Rp.size)
    (χ ρ : Fin C.size → X → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (horigin : ∀ i, C.piece i = ((Rp.patch (index i)).toPiece p).coordinateCutoff
      (χ i) (ρ i) (hχ i) (hρ i))
    (ℋ : letI := associatedSphereChartedSpace S
      letI := associatedSphereIsManifold S
      SmoothHorizontalLift (smoothAssociatedSphereProjection S))
    (gB : SmoothCotangentMetric (n := n) (M := B))
    (RpTail : ℝ)
    (hpTail : ∀ x ξ (s : ℝ), 0 < s → RpTail ≤ gB.length x ξ →
      RpTail ≤ gB.length x (s • ξ) → p.val x (s • ξ) = (s : ℂ) • p.val x ξ)
    (hE : SmoothHermitianMetric (n := n) (r := a) E)
    (kE : SmoothHermitianMetric (n := n) (r := a') E')
    (q : globalSymbolSpace (n := r) (r := d) (q := e) F F' 1)
    (hq : ∀ g : G, equivariantGlobalSymbolLinearMap IG σ τ g q.val = q.val)
    (hEll : IsEllipticFullGlobalSymbol (r := d) (q := e) F F' 1 q.val)
    (g : SmoothCotangentMetric (n := r) (M := OrthogonalSphere r))
    (RqTail : ℝ)
    (hqTail : ∀ y ξ (s : ℝ), 0 < s → RqTail ≤ g.length y ξ →
      RqTail ≤ g.length y (s • ξ) → q.val y (s • ξ) = (s : ℂ) • q.val y ξ)
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
      ∀ gZ : SmoothCotangentMetric (n := n + r) (M := Z),
      ∀ (_hweight : ∀ z : Z, ∑ i, weight i z = 1),
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          let pf (z : Z) (Ξ : CotangentFiber (n := n + r) z) :=
            let covH := fun i j ↦ split (covectorInChart (CH i j) z Ξ)
            (∑ i, ∑ j,
              ((J.cutoff j (associatedSphereTrivialization S (C.center i) z).2 *
              productFrequencyCutoff ε ‖(covH i j).1‖ ‖(covH i j).2‖ : ℝ) : ℂ) •
                (C.piece i).globalSymbolFunction (base z)
                  (covectorFromChart (C.piece i).chart (base z) (covH i j).1)).toLinearMap
          let qf (z : Z) (Ξ : CotangentFiber (n := n + r) z) :=
            let cov := fun i j ↦ split (covectorInChart (Ci i j) z Ξ)
            let factor := fun i j ↦
              if hz : z ∈ (Ci i j).source ∩
                  (AD.chart (b i, (L j).input.frameIndex)).baseSet ∩
                  (AD'.chart (b i, (L j).output.frameIndex)).baseSet then
                let eIn := (AD.frameLinearEquiv (b i, (L j).input.frameIndex) z hz.1.2).trans
                  (EuclideanSpace.equiv (Fin (A.rank (L j).input.frameIndex)) ℂ).symm.toLinearEquiv
                let eOut := (AD'.frameLinearEquiv (b i, (L j).output.frameIndex) z hz.2).trans
                  (EuclideanSpace.equiv
                    (Fin (A'.rank (L j).output.frameIndex)) ℂ).symm.toLinearEquiv
                ((θ i (c i (base z)) * (L j).input.cutoff ((L j).chart (t i z).2) *
                  (L j).output.cutoff ((L j).chart (t i z).2) *
                  productFrequencyCutoff ε ‖(cov i j).2‖ ‖(cov i j).1‖ : ℝ) : ℂ) •
                    (eOut.symm.toLinearMap.comp
                      (((L j).symbol ((L j).chart (t i z).2) (cov i j).2).toLinearMap.comp
                        eIn.toLinearMap))
              else (0 : D z →ₗ[ℂ] D' z)
            ∑ i, ∑ j, factor i j
          ∃ Rtail : ℝ, 0 < Rtail ∧
            (∀ z ξ (s : ℝ), 0 < s → Rtail ≤ gZ.length z ξ →
              Rtail ≤ gZ.length z (s • ξ) → pf z (s • ξ) = (s : ℂ) • pf z ξ) ∧
            (∀ z ξ (s : ℝ), 0 < s → Rtail ≤ gZ.length z ξ →
              Rtail ≤ gZ.length z (s • ξ) → qf z (s • ξ) = (s : ℂ) • qf z ξ) ∧
            ∀ z ξ, Rtail ≤ gZ.length z ξ →
              ∀ (pi : E' (base z) →ₗ[ℂ] E (base z)) (qi : D' z →ₗ[ℂ] D z),
                (∀ u v, (kE.toCore (base z)).inner (pf z ξ u) v =
                  (hE.toCore (base z)).inner u (pi v)) →
                (∀ u v, (associatedEquivariantMetricCore S.toIsPrincipalBundle τ
                    k.toContinuousHermitianMetric z).inner (qf z ξ u) v =
                  (associatedEquivariantMetricCore S.toIsPrincipalBundle σ
                    h.toContinuousHermitianMetric z).inner u (qi v)) →
                Function.Bijective (reciprocalTensorSymbol (pf z ξ) pi (qf z ξ) qi) :=
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
  intro AD AD' t L Ci CH base weight gZ hweight
  -- Choose the one uniform cutoff threshold from the original affine family.
  obtain ⟨ε₀, Rinv, hε₀, hε₀one, hRinv, hinv⟩ :=
    exists_associatedSphereCutoffTensorSymbol_global_affine_bijective S σ τ E E'
      C hC ℋ gB hE kE q hq hEll g h k hInvariant kInvariant
      hσ hτ J R b c hc θ hθK hθchart hθbase gZ hweight
  refine ⟨ε₀, hε₀, hε₀one, ?_⟩
  intro ε hε hεmax pf qf
  -- The horizontal finite sum uses the actual retained quantization origins.
  have hpiece (i : Fin C.size) :=
    (Rp.patch (index i)).exists_refined_productCutoff_homogeneous_of_tail
      (Y := YS) p gB RpTail hpTail (χ i) (ρ i) (hχ i) (hρ i) ε hε
  let Ri (i : Fin C.size) : ℝ := (hpiece i).choose
  have hi (i : Fin C.size) (x : B) (ξ : X) (η : YS) (s : ℝ) (hs : 0 < s)
      (hξ : Ri i ≤ ‖ξ‖ + ‖η‖) (hsξ : Ri i ≤ ‖s • ξ‖ + ‖s • η‖) :
      (productFrequencyCutoff ε ‖s • ξ‖ ‖s • η‖ : ℂ) •
          (C.piece i).globalSymbolFunction x
            (covectorFromChart (C.piece i).chart x (s • ξ)) =
        (s : ℂ) • ((productFrequencyCutoff ε ‖ξ‖ ‖η‖ : ℂ) •
          (C.piece i).globalSymbolFunction x
            (covectorFromChart (C.piece i).chart x ξ)) := by
    rw [horigin i]
    exact (hpiece i).choose_spec.2 x ξ η s hs hξ hsξ
  obtain ⟨Rh, hRh, hhorizontal⟩ :=
    PrincipalPseudodifferentialLocalization.exists_horizontalCutoff_homogeneous_of_piece_tails
      S E E' A C J ε Ri hi gZ
  -- On the active product-chart guard, the trivialization's base is the projection.
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
  have hqeq (z : Z) (ξ : CotangentFiber (n := n + r) z) : qf z ξ = qRaw z ξ := by
    dsimp only [qf, qRaw]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with hz
    · have hsource : z ∈ (t i).source := hz.1.1.1.1
      rw [(t i).coe_fst hsource]
    · rfl
  obtain ⟨Rv, hRv, hvertical⟩ :=
    exists_associatedSphereVerticalCutoff_homogeneous_of_tail S σ τ q g RqTail hqTail
      hσ hτ R b c hc θ hθK hθchart hθbase ε hε gZ
  let Rtail := max Rh (max Rv Rinv)
  have hRhTail : Rh ≤ Rtail := le_max_left _ _
  have hRvTail : Rv ≤ Rtail := (le_max_left _ _).trans (le_max_right _ _)
  have hRinvTail : Rinv ≤ Rtail := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨Rtail, hRh.trans_le hRhTail, ?_, ?_, ?_⟩
  · intro z ξ s hs hξ hsξ
    exact congrArg ContinuousLinearMap.toLinearMap
      (hhorizontal z ξ s hs (hRhTail.trans hξ) (hRhTail.trans hsξ))
  · intro z ξ s hs hξ hsξ
    rw [hqeq, hqeq]
    exact hvertical z ξ s hs (hRvTail.trans hξ) (hRvTail.trans hsξ)
  · intro z ξ hξ pi qi hpi hqi
    -- The endpoint s=1 is the actual cutoff pair, with the same specified adjoints.
    have hendpoint := hinv ε hε hεmax (1 : unitInterval) z ξ (hRinvTail.trans hξ)
    dsimp only at hendpoint
    have hone : ((1 : unitInterval) : ℂ) = 1 := rfl
    simp only [hone, sub_self, zero_smul, one_smul, zero_add] at hendpoint
    change ∀ (pi : E' (base z) →ₗ[ℂ] E (base z)) (qi : D' z →ₗ[ℂ] D z),
      (∀ u v, (kE.toCore (base z)).inner (pf z ξ u) v =
        (hE.toCore (base z)).inner u (pi v)) →
      (∀ u v, (associatedEquivariantMetricCore S.toIsPrincipalBundle τ
          k.toContinuousHermitianMetric z).inner (qRaw z ξ u) v =
        (associatedEquivariantMetricCore S.toIsPrincipalBundle σ
          h.toContinuousHermitianMetric z).inner u (qi v)) →
      Function.Bijective (reciprocalTensorSymbol (pf z ξ) pi (qRaw z ξ) qi) at hendpoint
    have hqRaw : qRaw z ξ = qf z ξ := (hqeq z ξ).symm
    rw [hqRaw] at hendpoint
    exact hendpoint pi qi hpi hqi

end AtiyahSinger
