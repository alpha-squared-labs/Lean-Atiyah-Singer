/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AssociatedTensorChartCutoff
public import AtiyahSinger.Analysis.AtlasSmoothChartSobolevLocalization

import AtiyahSinger.Analysis.SobolevMultiplication

/-!
# Associated tensor cutoff columns in the Sobolev norm

The supplied product cutoff yields finite sphere-frame columns. Each column
extends boundedly from the finite-atlas Sobolev completion to its real-order
Bessel coordinate space, with the normalized whole-sphere input formula on
smooth sections.

A compact auxiliary multiplier equals one on the fixed input support, so it
implements the column projections without changing their values. The column
maps are chosen uniformly over all smooth input sections.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Matrix.Norms.L2Operator TensorProduct SchwartzMap

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
local notation "q" => associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
local notation "T" => fun z : Z ↦ E (q z) ⊗[ℂ] D z

local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "XY" => EuclideanSpace ℝ (Fin (n + r))

variable [T2Space
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [SecondCountableTopology
    (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

set_option maxSynthPendingDepth 40 in
set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- All actual input columns are bounded in the same specified global real-order Sobolev norm. -/
theorem exists_associatedSphereTensorCutoff_sobolev_columns
    (hσ : σ.IsSmoothAtlas 𝓘(ℝ, OrthogonalGroupModel r) A) (b : B)
    (c : OpenPartialHomeomorph B X) (hc : c ∈ atlas X B)
    (C : BundleChartCutoff (r := a) E c)
    (hC : c.symm '' tsupport C.cutoff ⊆ (S.trivialization b).baseSet)
    (d : OpenPartialHomeomorph (OrthogonalSphere r) Y)
    (hd : d ∈ atlas Y (OrthogonalSphere r)) (K : AtlasChartCutoff A d) (s : ℝ) :
    letI := modelTopology (EuclideanSpace ℂ (Fin a)) E
    letI : TopologicalSpace (TotalSpace Unit T) :=
      tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
    letI := associatedSphereChartedSpace S
    letI := linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    letI := isManifold_linearModelChartedSpace
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm Z
    let AT : SmoothComplexBundleAtlas (n := n + r) T :=
      associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
    ∀ L : AtlasBundlePresentation (n := n + r) (M := Z) (E := T) AT,
      ∃ R : Fin (A.rank K.frameIndex) →
          L.SobolevSpace s →L[ℂ] Lp (EuclideanSpace ℂ (Fin a)) 2 (volume : Measure XY),
        ∀ w : AT.smoothSections,
          ∃ f : Fin (A.rank K.frameIndex) → 𝓢(XY, EuclideanSpace ℂ (Fin a)),
            (∀ x y i j, f j (EuclideanSpace.finAddEquivProd.symm (x, y)) i =
              K.localize hd ((C.cutoff x : ℂ) •
                associatedSphereTensorLocalFiberCoordinates S E A b C.frame C.frame_mem_atlas i
                  (fun p ↦ associatedSphereTensorFiberRestriction (a := a) S E A σ hσ p w)
                  (c.symm x)) y j) ∧
            (∀ j, HasCompactSupport (f j)) ∧
            ∀ j, R j (L.smoothToSobolev s w) = schwartzSobolevCoordinate s (f j) := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin a)) E
  let : TopologicalSpace (TotalSpace Unit T) :=
    tensorTopology (E := (q : Z → B) *ᵖ E) (F := D)
  let := associatedSphereChartedSpace S
  let e := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  let := linearModelChartedSpace e.symm Z
  let := isManifold_linearModelChartedSpace e.symm Z
  let AT : SmoothComplexBundleAtlas (n := n + r) T :=
    associatedSphereTensorBundleAtlas (a := a) S E A σ hσ
  let Bcut : AtlasChartCutoff AT (associatedSphereProductChart S b c d) :=
    associatedSphereTensorChartCutoff S E A σ hσ b c C hC d K
  let V := EuclideanSpace ℂ (Fin (a * A.rank K.frameIndex))
  let W := EuclideanSpace ℂ (Fin a)
  dsimp only
  intro L
  change AtlasBundlePresentation AT at L
  -- Localize in the compatible chart, retaining the unchanged original finite-atlas norm.
  have hchart : associatedSphereProductChart S b c d ∈
      IsManifold.maximalAtlas (𝓡 (n + r)) ∞ Z :=
    associatedSphereProductChart_mem_maximalAtlas S b c hc d hd
  have hlocal : ∃ I : AT.smoothSections →ₗ[ℂ] 𝓢(XY, V),
      (∀ u z, I u z = Bcut.localizedFunction u z) ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ u : AT.smoothSections,
          ‖schwartzSobolevCoordinate s (I u)‖ ≤ C * ‖L.smoothToSobolev s u‖ :=
    AtlasChartCutoff.exists_localize_sobolev_of_mem_maximalAtlas
      (n := n + r) (M := Z) (E := T) (A := AT) Bcut hchart L s
  obtain ⟨I, hI, cI, _hcI, hbI⟩ := hlocal
  have hIz (w : AT.smoothSections) (z : XY) (hz : z ∉ tsupport Bcut.cutoff) : I w z = 0 := by
    rw [hI]
    have hzero := image_eq_zero_of_notMem_tsupport hz
    simp only [AtlasChartCutoff.localizedFunction, hzero, Complex.ofReal_zero, zero_smul, ite_self]
  have hcutoffK : IsCompact (tsupport (Bcut.cutoff : XY → ℝ)) := Bcut.compact_support
  have hneighborhood : ∃ O : Set XY, IsOpen O ∧ tsupport Bcut.cutoff ⊆ O ∧
      closure O ⊆ Set.univ ∧ IsCompact (closure O) :=
    exists_open_between_and_isCompact_closure hcutoffK isOpen_univ (Set.subset_univ _)
  obtain ⟨O, hOo, hKO, _, hOc⟩ := hneighborhood
  have hcutoff : ∃ η : XY → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧
      Set.range η ⊆ Set.Icc (0 : ℝ) 1 ∧ Function.support η = O ∧
        (∀ z, z ∈ tsupport Bcut.cutoff ↔ η z = 1) :=
    exists_contDiff_support_eq_eq_one_iff
      (n := (⊤ : ℕ∞)) hOo (isClosed_tsupport Bcut.cutoff) hKO
  obtain ⟨η, hη, _, hsη, honeη⟩ := hcutoff
  have hηK : HasCompactSupport η := by
    simpa only [HasCompactSupport, tsupport, hsη] using hOc
  have hηone (z : XY) (hz : z ∈ tsupport Bcut.cutoff) : η z = 1 :=
    (honeη z).mp hz
  let col (j : Fin (A.rank K.frameIndex)) : V →L[ℂ] W :=
    LinearMap.toContinuousLinearMap {
      toFun v := WithLp.toLp 2 (fun i ↦ v (finProdFinEquiv (i, j)))
      map_add' v v' := by ext i; rfl
      map_smul' z v := by ext i; rfl }
  let M (j : Fin (A.rank K.frameIndex)) (z : XY) : V →L[ℂ] W := η z • col j
  have hM (j : Fin (A.rank K.frameIndex)) : ContDiff ℝ ∞ (M j) := hη.smul contDiff_const
  have hMK (j : Fin (A.rank K.frameIndex)) : HasCompactSupport (M j) := hηK.smul_right
  let Tcol (j : Fin (A.rank K.frameIndex)) := matrixMultiplierCLM (M j) (hM j) (hMK j)
  have hbounds (j : Fin (A.rank K.frameIndex)) :=
    exists_norm_matrixMultiplier_sobolev_le (M j) (hM j) (hMK j) s
  choose cT hcT hbT using hbounds
  -- Each fixed compact column projection extends on the same dense smooth embedding.
  let Fcol (j : Fin (A.rank K.frameIndex)) := (Tcol j).toLinearMap.comp I
  let Bcol (j : Fin (A.rank K.frameIndex)) :=
    (schwartzSobolevCoordinateLinearMap (n + r) a s).comp (Fcol j)
  have hB (j : Fin (A.rank K.frameIndex)) (w : AT.smoothSections) :
      ‖Bcol j w‖ ≤ cT j * cI * ‖L.smoothToSobolev s w‖ := by
    apply (hbT j (I w)).trans
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hbI w) (hcT j)
  let R (j : Fin (A.rank K.frameIndex)) := (Bcol j).extendOfNorm (L.smoothToSobolev s)
  have hR (j : Fin (A.rank K.frameIndex)) (w : AT.smoothSections) :
      R j (L.smoothToSobolev s w) = schwartzSobolevCoordinate s (Fcol j w) :=
    (Bcol j).extendOfNorm_eq (L.denseRange_smoothToSobolev s) ⟨cT j * cI, hB j⟩ w
  refine ⟨R, ?_⟩
  intro w
  have hF (j : Fin (A.rank K.frameIndex)) (z : XY) : Fcol j w z = col j (I w z) := by
    change matrixMultiplierCLM (M j) (hM j) (hMK j) (I w) z = _
    rw [matrixMultiplierCLM_apply]
    change (η z • col j) (I w z) = _
    by_cases hz : z ∈ tsupport Bcut.cutoff
    · rw [hηone z hz, one_smul]
    · rw [hIz w z hz, map_zero, map_zero]
  refine ⟨fun j ↦ Fcol j w, ?_, ?_, fun j ↦ hR j w⟩
  · -- The original tensor frame and normalized whole-sphere family give the exact column formula.
    intro x y i j
    rw [hF]
    change I w (e.symm (x, y)) (finProdFinEquiv (i, j)) = _
    rw [hI]
    exact associatedSphereTensorChartCutoff_localizedFunction (a := a)
      S E A σ hσ b c C hC d hd K w x y i j
  · intro j
    apply Bcut.compact_support.of_isClosed_subset (isClosed_tsupport _)
    apply closure_minimal ?_ (isClosed_tsupport Bcut.cutoff)
    intro z hz
    by_contra hzero
    apply hz
    rw [hF, hIz w z hzero, map_zero]

end AtiyahSinger
