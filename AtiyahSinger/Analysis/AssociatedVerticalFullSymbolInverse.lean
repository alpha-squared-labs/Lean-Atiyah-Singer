/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedVerticalCovectorRestriction
public import AtiyahSinger.Analysis.AssociatedVerticalFullSymbol
public import AtiyahSinger.Analysis.FullSymbolMetricInverseBound
public import AtiyahSinger.Topology.AssociatedInvariantMetric

/-!
# Quantitative vertical ellipticity of the actual descended full symbol

Public module ID: M0222.

The invariant native full symbol descends to the original associated fibers.
In its actual product chart, restriction of the total covector has exactly the
original sphere frequency. The given invariant metrics make every principal
representative isometric. Consequently the original full-symbol inverse bound
passes to one uniform lower energy estimate on the descended vertical map.
The constant is independent of the base representative and horizontal frequency.
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

local notation "H" => EuclideanSpace ℝ (Fin (n + r))

set_option maxSynthPendingDepth 40 in
set_option cleanup.letToHave false in
set_option maxHeartbeats 2400000 in
-- Normalize the associated local frames and original vertical inverse energy bound.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
open scoped Classical in
/-- The actual descended vertical full symbol has a uniform inverse energy bound. -/
theorem exists_associatedSphereVerticalFullSymbol_inverse_bound
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
      k.pairing (g • y) (τ.linearMap g y u) (τ.linearMap g y v) = k.pairing y u v)
    (b : B) (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (d₀ : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd₀ : d₀ ∈ atlas Y (OrthogonalSphere r))
    (e₀ : Trivialization (EuclideanSpace ℂ (Fin d)) (π (EuclideanSpace ℂ (Fin d)) F))
    (f₀ : Trivialization (EuclideanSpace ℂ (Fin e)) (π (EuclideanSpace ℂ (Fin e)) F'))
    [MemTrivializationAtlas e₀] [MemTrivializationAtlas f₀]
    (K : Set (OrthogonalSphere r)) (hK : IsCompact K)
    (hKe : K ⊆ d₀.source ∩ e₀.baseSet) (hKf : K ⊆ d₀.source ∩ f₀.baseSet) :
    letI := modelTopology (EuclideanSpace ℂ (Fin d)) F
    letI := modelTopology (EuclideanSpace ℂ (Fin e)) F'
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
    letI : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
    letI := associatedSphereChartedSpace S
    let a := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    letI := linearModelChartedSpace split.symm Z
    let CP := associatedSphereProductChart S b c d₀
    ∃ R C : ℝ, 0 < R ∧ 0 ≤ C ∧
      ∀ (p : P) (_hp : projection p ∈ (S.trivialization b).baseSet)
        (_hg : (S.trivialization b p).2 = 1) (_hpc : projection p ∈ c.source)
        (y : OrthogonalSphere r) (_hy : y ∈ K) (ξ : X) (η : Y), R ≤ ‖η‖ →
        let coefficient : ℝ := C / (1 + ‖η‖) ^ 2
        let z := associatedBundleMk G P (OrthogonalSphere r) p y
        let Ξ := covectorFromChart CP z (split.symm (ξ, η))
        let Q := a z (Ξ.comp split.symm.toContinuousLinearMap)
        Function.Bijective Q ∧ ∀ u : AssociatedEquivariantFiber S.toIsPrincipalBundle σ z,
          ((associatedEquivariantMetricCore S.toIsPrincipalBundle σ
            h.toContinuousHermitianMetric z).inner u u).re ≤ coefficient *
              ((associatedEquivariantMetricCore S.toIsPrincipalBundle τ
                k.toContinuousHermitianMetric z).inner (Q u) (Q u)).re :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  obtain ⟨R, C, hR, hC, hbound⟩ := hEll.exists_compact_metric_inverse_bound
    q.val g h k d₀ hd₀ e₀ f₀ K hK hKe hKf
  let := modelTopology (EuclideanSpace ℂ (Fin d)) F
  let := modelTopology (EuclideanSpace ℂ (Fin e)) F'
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin d)) F
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin e)) F'
  let : ChartedSpace (X × Y) (B × OrthogonalSphere r) := prodChartedSpace X B Y _
  let := associatedSphereChartedSpace S
  intro a split
  have ha := (existsUnique_associatedSphereVerticalFullSymbol S σ τ q.val hq).choose_spec.1
  let ν (p : P) (y : OrthogonalSphere r) (Ξ : H →L[ℝ] ℝ) :=
    (Ξ.comp split.symm.toContinuousLinearMap).comp
      (mfderiv (𝓡 r) 𝓘(ℝ, X × Y) (associatedBundleMk G P (OrthogonalSphere r) p) y)
  let := linearModelChartedSpace split.symm Z
  let := isManifold_linearModelChartedSpace split.symm Z
  intro CP
  refine Exists.intro R ?_
  refine Exists.intro C ?_
  refine And.intro hR (And.intro hC ?_)
  intro p hp hg hpc y hy ξ η hη coefficient z Ξ Q
  let t := associatedSphereTrivialization S b
  have htbase : t.baseSet = (S.trivialization b).baseSet :=
    (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.1
  have hzt : z ∈ t.source := t.mem_source.mpr (htbase.symm ▸ hp)
  have ht : t z = (projection p, y) := by
    have h := (exists_associatedBundleTrivialization S.toIsPrincipalBundle
      (S.trivialization b) (S.equivariant b)).choose_spec.2.1 p y hp
    change t z = (projection p, (S.trivialization b p).2 • y) at h
    simpa only [hg, one_smul] using h
  have hzCP : z ∈ CP.source := by
    refine ⟨⟨hzt, ?_, ?_⟩, Set.mem_univ _⟩
    · change (t z).1 ∈ c.source
      rw [ht]
      exact hpc
    · change (t z).2 ∈ d₀.source
      rw [ht]
      exact (hKe hy).1
  have hCP := associatedSphereProductChart_mem_maximalAtlas S b c hc d₀ hd₀
  -- Cancel the actual target chart derivatives, including the fixed total model flattening.
  have hround : covectorInChart CP z Ξ = split.symm (ξ, η) := by
    have hdiff : CP.MDifferentiable (𝓡 (n + r)) (𝓡 (n + r)) :=
      ⟨(contMDiffOn_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp),
        (contMDiffOn_symm_of_mem_maximalAtlas hCP).mdifferentiableOn (by simp)⟩
    have hderiv := hdiff.comp_symm_deriv (CP.map_source hzCP)
    rw [CP.left_inv hzCP] at hderiv
    ext j
    change inner ℝ (split.symm (ξ, η)) ((mfderiv _ _ CP z)
      ((mfderiv _ _ CP.symm (CP z)) (EuclideanSpace.single j 1))) = _
    have hd := congrArg (fun L : H →L[ℝ] H ↦ L (EuclideanSpace.single j 1)) hderiv
    change (mfderiv _ _ CP z) ((mfderiv _ _ CP.symm (CP z))
      (EuclideanSpace.single j 1)) = EuclideanSpace.single j 1 at hd
    rw [hd]
    simp [EuclideanSpace.inner_single_right]
  have hvertical : (split (covectorInChart CP z Ξ)).2 = covectorInChart d₀ (t z).2
      (Ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r)) t.toOpenPartialHomeomorph.symm
        (t z)).comp (ContinuousLinearMap.inr ℝ X Y))) :=
    covectorInChart_associatedSphereProductChart_snd S b c hc d₀ hd₀ z hzCP Ξ
  have hrestrict : Ξ.comp ((mfderiv 𝓘(ℝ, X × Y) (𝓡 (n + r)) t.toOpenPartialHomeomorph.symm
      (projection p, y)).comp (ContinuousLinearMap.inr ℝ X Y)) = ν p y Ξ :=
    associatedSphereVerticalCovector_eq_fiberRestriction S b p hp hg y Ξ
  rw [ht] at hvertical
  rw [hrestrict, hround, split.apply_symm_apply] at hvertical
  have hfreq : covectorInChart d₀ y (ν p y Ξ) = η := hvertical.symm
  obtain ⟨hPi, hPb⟩ := hbound y hy (ν p y Ξ) (hfreq.symm ▸ hη)
  have hformula (u : F y) :
      Q (associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u) =
        associatedEquivariantFiberMk S.toIsPrincipalBundle τ p y rfl (q.val y (ν p y Ξ) u) :=
    ha p y rfl (Ξ.comp split.symm.toContinuousLinearMap) u
  -- The quotient representative maps are bijections for the exact original source and target.
  have hin := associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle σ p y rfl
  have hout := associatedEquivariantFiberMk_bijective S.toIsPrincipalBundle τ p y rfl
  have hbij : Function.Bijective Q := by
    constructor
    · intro u v huv
      obtain ⟨u₀, rfl⟩ := hin.2 u
      obtain ⟨v₀, rfl⟩ := hin.2 v
      rw [hformula, hformula] at huv
      exact congrArg _ (hPi.injective (hout.1 huv))
    · intro v
      obtain ⟨v₀, rfl⟩ := hout.2 v
      obtain ⟨u₀, hu₀⟩ := hPi.surjective v₀
      exact ⟨associatedEquivariantFiberMk S.toIsPrincipalBundle σ p y rfl u₀,
        (hformula u₀).trans (congrArg _ hu₀)⟩
  refine ⟨hbij, ?_⟩
  intro u
  obtain ⟨u₀, rfl⟩ := hin.2 u
  rw [hformula]
  change ((associatedEquivariantMetricCore S.toIsPrincipalBundle σ
      h.toContinuousHermitianMetric z).inner _ _).re ≤ _
  rw [associatedEquivariantMetricCore_inner S.toIsPrincipalBundle σ
    h.toContinuousHermitianMetric hInvariant p y rfl]
  change (h.pairing y u₀ u₀).re ≤ C / (1 + ‖η‖) ^ 2 *
    ((associatedEquivariantMetricCore S.toIsPrincipalBundle τ
      k.toContinuousHermitianMetric z).inner _ _).re
  rw [associatedEquivariantMetricCore_inner S.toIsPrincipalBundle τ
    k.toContinuousHermitianMetric kInvariant p y rfl]
  have hb := hPb (q.val y (ν p y Ξ) u₀)
  rw [hPi.inverse_apply_self, hfreq] at hb
  exact hb

end AtiyahSinger
