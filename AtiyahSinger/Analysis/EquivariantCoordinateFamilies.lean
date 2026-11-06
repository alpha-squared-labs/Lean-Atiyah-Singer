/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CoordinateChangeFamilies
public import AtiyahSinger.Analysis.EquivariantPrincipalSymbol
public import AtiyahSinger.Analysis.SmoothCompositionFamilies

/-!
# Spatial jets of the actual moving coordinates

Public module ID: M0495.

The original charts composed with the group action have jointly continuous
spatial jets after restricting a smooth forward-action family along the
continuous inverse graph. This retains the weaker group assumptions of the
original Haar average and supplies the actual parameter-dependent coordinates.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped ContDiff Manifold

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hG hAction

omit [ContinuousSMul G M] in
/-- All spatial jets of the original inverse moving chart depend continuously on the group. -/
theorem continuousOn_iteratedFDeriv_inverse_smul_chart
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M) (k : ℕ) :
    ContinuousOn
      (fun p : G × EuclideanSpace ℝ (Fin n) ↦
        iteratedFDeriv ℝ k (fun z ↦ d (p.1⁻¹ • c.symm z)) p.2)
      {p | p.2 ∈ c.target ∧ p.1⁻¹ • c.symm p.2 ∈ d.source} := by
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let C : Set (G × X) := univ ×ˢ c.target
  let moved (p : G × X) : M := p.1 • c.symm p.2
  have hchart : ContMDiffOn (IG.prod I) I ∞ (fun p : G × X ↦ c.symm p.2) C :=
    (contMDiffOn_symm_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc)).comp
        contMDiffOn_snd (fun _ hp ↦ hp.2)
  have hmove : ContMDiffOn (IG.prod I) I ∞ moved C := contMDiffOn_fst.smul hchart
  let W := C ∩ moved ⁻¹' d.source
  have hW : IsOpen W := hmove.continuousOn.isOpen_inter_preimage
    (isOpen_univ.prod c.open_target) d.open_source
  have hraw : ContMDiffOn (IG.prod I) I ∞ (fun p : G × X ↦ d (moved p)) W :=
    (contMDiffOn_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd)).comp
        (hmove.mono inter_subset_left) (fun _ hp ↦ hp.2)
  -- Differentiate the smooth forward family first; invert only the topological parameter.
  have hjets := (contMDiffOn_iteratedFDeriv_parameter IG hW hraw k).continuousOn
  have hinverse : Continuous (fun p : G × X ↦ (p.1⁻¹, p.2)) :=
    continuous_fst.inv.prodMk continuous_snd
  exact hjets.comp hinverse.continuousOn (fun p hp ↦ ⟨⟨mem_univ _, hp.1⟩, hp.2⟩)

/-- The original group-conjugated charts share a parameter-and-endpoint frequency neighborhood. -/
theorem exists_inverse_smul_chart_coordinate_neighborhood
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M) :
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let e (g : G) := d.symm.trans
      ((Diffeomorph.smul (M := M) IG I ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
    ∃ W : Set (G × (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))),
      IsOpen W ∧ (∀ g x, x ∈ (e g).target → (g, (x, x)) ∈ W) ∧
      ∀ p ∈ W, segment ℝ p.2.2 p.2.1 ⊆ (e p.1).target ∧
        (averagedFDeriv (e p.1).symm p.2.1 p.2.2).IsInvertible := by
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let e (g : G) := d.symm.trans
    ((Diffeomorph.smul (M := M) IG I ∞ g).toHomeomorph.toOpenPartialHomeomorph.trans c)
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have he (g : G) : ContDiffOn ℝ ∞ (e g) (e g).source := by
    intro z hz
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1
    have hmove := (Diffeomorph.smul (M := M) IG I ∞ g).contMDiffAt.comp z hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hz.2.2).comp z hmove).contDiffAt.contDiffWithinAt
  have hψ (g : G) : ContDiffOn ℝ ∞ (e g).symm (e g).target := by
    intro z hz
    have hchart := contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1.1
    have hmove := (Diffeomorph.smul (M := M) IG I ∞ g).symm.contMDiffAt.comp z hchart
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hz.2).comp z hmove).contDiffAt.contDiffWithinAt
  let C : Set (G × X) := univ ×ˢ c.target
  let moved (p : G × X) : M := p.1⁻¹ • c.symm p.2
  have hmove : ContinuousOn moved C := continuous_fst.inv.continuousOn.smul
    (c.continuousOn_symm.comp continuous_snd.continuousOn (fun _ hp ↦ hp.2))
  have hdom : {p : G × X | p.2 ∈ (e p.1).target} =
      {p | p.2 ∈ c.target ∧ p.1⁻¹ • c.symm p.2 ∈ d.source} := by
    ext p
    change ((p.2 ∈ c.target ∧ c.symm p.2 ∈ univ) ∧ p.1⁻¹ • c.symm p.2 ∈ d.source) ↔ _
    simp only [mem_univ, and_true, mem_ofPred_eq]
  have hdom' : {p : G × X | p.2 ∈ (e p.1).target} = C ∩ moved ⁻¹' d.source := by
    rw [hdom]
    ext p
    simp only [C, moved, mem_inter_iff, mem_prod, mem_univ, true_and,
      mem_preimage, mem_ofPred_eq]
  have hopen : IsOpen {p : G × X | p.2 ∈ (e p.1).target} := by
    rw [hdom']
    exact hmove.isOpen_inter_preimage (isOpen_univ.prod c.open_target) d.open_source
  -- The actual inverse chart is the previously controlled inverse action formula.
  have hraw (g : G) : ⇑(e g).symm = (fun z ↦ d (g⁻¹ • c.symm z)) := rfl
  have hjets := continuousOn_iteratedFDeriv_inverse_smul_chart (G := G) IG c d hc hd 1
  have hfd : ContinuousOn (fun p : G × X ↦ fderiv ℝ (e p.1).symm p.2)
      {p | p.2 ∈ (e p.1).target} := by
    rw [hdom]
    have h := (continuousMultilinearCurryFin1 ℝ X X).continuous.comp_continuousOn hjets
    apply h.congr
    intro p _
    change fderiv ℝ (e p.1).symm p.2 =
      (continuousMultilinearCurryFin1 ℝ X X)
        (iteratedFDeriv ℝ 1 (fun z ↦ d (p.1⁻¹ • c.symm z)) p.2)
    rw [hraw]
    apply ContinuousLinearMap.ext
    intro v
    change fderiv ℝ (fun z ↦ d (p.1⁻¹ • c.symm z)) p.2 v =
      iteratedFDeriv ℝ 1 (fun z ↦ d (p.1⁻¹ • c.symm z)) p.2 (Fin.snoc 0 v)
    rw [iteratedFDeriv_one_apply]
    rfl
  exact exists_coordinateChange_family_neighborhood e he hψ hopen hfd

end AtiyahSinger
