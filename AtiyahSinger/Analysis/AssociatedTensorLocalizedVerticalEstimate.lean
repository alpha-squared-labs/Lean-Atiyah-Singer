/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorLocalFiberSobolev
public import AtiyahSinger.Analysis.AssociatedTensorVerticalSobolev

/-!
# The localized vertical H¹ graph estimate

Public module ID: M0185.

The compact whole-fiber input and vertical-output families both lie in the
specified metric L² spaces over Euclidean base coordinates. A full elliptic
sphere parametrix gives a uniform H¹ graph estimate for these same native
families. Its constant is chosen before the upstairs section, and all input
and output coordinates use the same cutoff, base frame, and normalized
principal representative.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

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
  (F F' : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Y" => OrthogonalSphere r
local notation "Z" => AssociatedBundle G P Y
local notation "IG" => 𝓘(ℝ, OrthogonalGroupModel r)

variable
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F.Fiber)
  (σ' : letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) F'.Fiber)
  (hσ : σ.IsSmooth (n := r) (r := F.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (hσ' : σ'.IsSmooth (n := r) (r := F'.rank) 𝓘(ℝ, OrthogonalGroupModel r))
  (k : SmoothHermitianMetric (n := r) (r := F.rank) F.Fiber)
  (k' : SmoothHermitianMetric (n := r) (r := F'.rank) F'.Fiber)
  [T2Space B]

local notation "D" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ
local notation "D'" => AssociatedEquivariantFiber S.toIsPrincipalBundle σ'
local notation "πS" => associatedBundleProjection (F := Y) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (πS z) ⊗[ℂ] D z
local notation "T'" => fun z : Z ↦ E (πS z) ⊗[ℂ] D' z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Xp" => Fin n → ℝ

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 3200000 in
-- The extended limit accommodates the full localized fiber Sobolev and graph estimates.
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The original localized vertical graph controls its actual whole-fiber H¹ family. -/
theorem exists_associatedSphereTensorLocalizedVertical_sobolev_bound
    (ν : Measure Y) [IsSmoothPositiveMeasure (n := r) ν]
    (Q : PseudodifferentialOperator (n := r) (r := F.rank) (q := F'.rank)
      F.Fiber F'.Fiber ν 1)
    (hQ : Q.IsEquivariant IG σ σ' hσ hσ') (hQell : Q.IsElliptic)
    (L : SmoothBundlePresentation (n := r) (r := F.rank) F.Fiber)
    (L' : SmoothBundlePresentation (n := r) (r := F'.rank) F'.Fiber)
    (b : B) {c : OpenPartialHomeomorph B X}
    (input : BundleChartCutoff (r := a) E c) (hc : c ∈ atlas X B)
    (hinput : c.symm '' tsupport input.cutoff ⊆ (S.trivialization b).baseSet)
    (χ : B → ℝ) (hχ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ χ)
    (hχsupport : tsupport χ ⊆ (S.trivialization b).baseSet)
    (hχone : ∀ x ∈ c.symm '' tsupport input.cutoff, χ x = 1) :
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
    let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
    let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
    let hA := σ.isSmoothAtlas_native IG hσ
    let hA' := σ'.isSmoothAtlas_native IG hσ'
    let QA := Q.toAtlasPseudodifferentialOperator
    ∃ hQA : QA.IsEquivariant IG σ σ' hA hA',
      letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
      letI : TopologicalSpace (TotalSpace Unit T) :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
      letI : TopologicalSpace (TotalSpace Unit T') :=
        tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
      letI := associatedSphereChartedSpace S
      letI := linearModelChartedSpace
        (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
      let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ w : (associatedSphereTensorBundleAtlas (a := a) S E A σ hA).smoothSections,
          ∃ u : Xp → Fin a → smoothSections (n := r) (r := F.rank) F.Fiber,
          ∃ v : Xp → Fin a → smoothSections (n := r) (r := F'.rank) F'.Fiber,
            (∀ (z : Xp) (i : Fin a), u z i = nativeSmoothSectionLinearEquiv F.Fiber
              ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
                associatedSphereTensorLocalFiberCoordinates S E A b input.frame
                  input.frame_mem_atlas i
                  (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hA p w)
                  (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
            (∀ (z : Xp) (i : Fin a), v z i = nativeSmoothSectionLinearEquiv F'.Fiber
              ((input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ) •
                associatedSphereTensorLocalFiberCoordinates S E A' b input.frame
                  input.frame_mem_atlas i
                  (fun p ↦ associatedSphereTensorFiberRestriction (a := a)
                    S E A' σ' hA' p (V w))
                  (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))) ∧
            ∃ (hu : ∀ i, MemLp (fun z ↦ k.smoothToL2 ν (u z i)) 2 (volume : Measure Xp))
              (hv : ∀ i, MemLp (fun z ↦ k'.smoothToL2 ν (v z i)) 2 (volume : Measure Xp))
              (h₁ : ∀ i, MemLp (fun z ↦ L.smoothToSobolev 1 (u z i)) 2 (volume : Measure Xp)),
              ∀ i : Fin a,
                ‖(h₁ i).toLp (fun z ↦ L.smoothToSobolev 1 (u z i))‖ ≤
                  C * (‖(hu i).toLp (fun z ↦ k.smoothToL2 ν (u z i))‖ +
                    ‖(hv i).toLp (fun z ↦ k'.smoothToL2 ν (v z i))‖) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let := isFiniteRank_model (EuclideanSpace ℂ (Fin F'.rank)) F'.Fiber
  let A := nativeSmoothComplexBundleAtlas (n := r) (r := F.rank) F.Fiber
  let A' := nativeSmoothComplexBundleAtlas (n := r) (r := F'.rank) F'.Fiber
  let hA := σ.isSmoothAtlas_native IG hσ
  let hA' := σ'.isSmoothAtlas_native IG hσ'
  let QA := Q.toAtlasPseudodifferentialOperator
  have hQA : QA.IsEquivariant IG σ σ' hA hA' :=
    (Q.isEquivariant_toAtlas_iff IG σ σ' hσ hσ').mpr hQ
  -- The complete native elliptic parametrix fixes the graph constant before any section.
  have hparam :
      ∃ R : k'.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
      ∃ R₀ : k.L2SectionSpace ν →L[ℂ] L.SobolevSpace 1,
        ∀ z : smoothSections (n := r) (r := F.rank) F.Fiber,
          L.smoothToSobolev 1 z =
            R (k'.smoothToL2 ν (Q.toLinearMap z)) + R₀ (k.smoothToL2 ν z) :=
    PseudodifferentialOperator.exists_metricSobolev_left_parametrix
      (n := r) (r := F.rank) (q := F'.rank) (M := Y)
      (E := F.Fiber) (F := F'.Fiber) (μ := ν) k k' Q hQell L L'
  obtain ⟨R, R₀, hsplit⟩ := hparam
  refine ⟨hQA, ?_⟩
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D)
  let : TopologicalSpace (TotalSpace Unit T') :=
    tensorTopology (E := (πS : Z → B) *ᵖ E) (F := D')
  let := associatedSphereChartedSpace S
  let := linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
  let V := associatedSphereTensorVerticalOperator (a := a) S E A σ hA A' σ' hA' QA hQA
  dsimp only
  refine ⟨‖R‖ + ‖R₀‖, add_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  intro w
  -- Both metric L² memberships are proved for the same actual compact coordinate families.
  obtain ⟨u, huvalue, _huzero, huSobolev, hu⟩ :=
    exists_associatedSphereTensorLocalizedFiber_sobolev (a := a)
      S E F σ hσ b input hc hinput χ hχ hχsupport hχone L k ν w
  obtain ⟨v, hvvalue, _hvzero, _hvSobolev, hv⟩ :=
    exists_associatedSphereTensorLocalizedFiber_sobolev (a := a)
      S E F' σ' hσ' b input hc hinput χ hχ hχsupport hχone L' k' ν (V w)
  have h₁ (i : Fin a) :
      MemLp (fun z ↦ L.smoothToSobolev 1 (u z i)) 2 (volume : Measure Xp) :=
    (huSobolev 1 i).2
  have hvQ (z : Xp) (i : Fin a) : v z i = Q.toLinearMap (u z i) := by
    have hcoord := congrArg (nativeSmoothSectionLinearEquiv F'.Fiber)
      (associatedSphereTensorVerticalOperator_localFiberCoordinates (a := a)
        S E A σ hA A' σ' hA' QA hQA b input.frame input.frame_mem_atlas i
        (fun _ ↦ (input.cutoff ((EuclideanSpace.equiv (Fin n) ℝ).symm z) : ℂ)) w
        (c.symm ((EuclideanSpace.equiv (Fin n) ℝ).symm z)))
    exact (hvvalue z i).trans
      (hcoord.trans (congrArg Q.toLinearMap (huvalue z i).symm))
  -- Prove the norm estimate for arbitrary Hilbert-valued families before substitution.
  have hLpBound (f₀ : Xp → k.L2SectionSpace ν) (f₁ : Xp → k'.L2SectionSpace ν)
      (f : Xp → L.SobolevSpace 1) (hsplit₀ : ∀ z, f z = R (f₁ z) + R₀ (f₀ z))
      (μ : Measure Xp) (hf₀ : MemLp f₀ 2 μ) (hf₁ : MemLp f₁ 2 μ) (hf : MemLp f 2 μ) :
      ‖hf.toLp f‖ ≤ (‖R‖ + ‖R₀‖) * (‖hf₀.toLp f₀‖ + ‖hf₁.toLp f₁‖) := by
    let g₀ := hf₀.toLp f₀
    let g₁ := hf₁.toLp f₁
    have hLp : hf.toLp f = R.compLpL 2 μ g₁ + R₀.compLpL 2 μ g₀ := by
      apply Lp.ext
      filter_upwards [hf.coeFn_toLp, hf₀.coeFn_toLp, hf₁.coeFn_toLp,
        Lp.coeFn_add (R.compLpL 2 μ g₁) (R₀.compLpL 2 μ g₀),
        R.coeFn_compLpL g₁, R₀.coeFn_compLpL g₀] with z hfz h₀z h₁z hadd hR hR₀
      exact hfz.trans ((hsplit₀ z).trans
        ((congrArg₂ (fun x y ↦ R x + R₀ y) h₁z.symm h₀z.symm).trans
          ((congrArg₂ (· + ·) hR.symm hR₀.symm).trans hadd.symm)))
    have hRbound : ‖R.compLpL 2 μ g₁‖ ≤ ‖R‖ * ‖g₁‖ := R.norm_compLp_le g₁
    have hR₀bound : ‖R₀.compLpL 2 μ g₀‖ ≤ ‖R₀‖ * ‖g₀‖ := R₀.norm_compLp_le g₀
    calc
      ‖hf.toLp f‖ = ‖R.compLpL 2 μ g₁ + R₀.compLpL 2 μ g₀‖ := congrArg norm hLp
      _ ≤ ‖R‖ * ‖g₁‖ + ‖R₀‖ * ‖g₀‖ :=
        (norm_add_le _ _).trans (add_le_add hRbound hR₀bound)
      _ ≤ (‖R‖ + ‖R₀‖) * (‖g₀‖ + ‖g₁‖) := by
        nlinarith [mul_nonneg (norm_nonneg R) (norm_nonneg g₀),
          mul_nonneg (norm_nonneg R₀) (norm_nonneg g₁)]
  refine ⟨u, v, huvalue, hvvalue, hu, hv, h₁, ?_⟩
  intro i
  apply hLpBound _ _ _ ?_ volume (hu i) (hv i) (h₁ i)
  intro z
  exact (hsplit (u z i)).trans
    (congrArg (fun v ↦ R (k'.smoothToL2 ν v) + R₀ (k.smoothToL2 ν (u z i)))
      (hvQ z i).symm)

end AtiyahSinger
