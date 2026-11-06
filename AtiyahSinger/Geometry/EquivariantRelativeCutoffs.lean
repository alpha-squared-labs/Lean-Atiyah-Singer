/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.EquivariantSmoothCutoff
public import AtiyahSinger.Topology.EquivariantSupportTriple

/-!
# Invariant compact windows for relative symbol smoothing

Public module ID: M1202.

A specified invariant compact set inside an invariant open manifold admits
three nested compact windows and the exact cutoffs needed by controlled
relative smoothing. The two exterior cutoffs vanish on neighborhoods of the
preceding windows, so their closed supports avoid those windows. Saturation
and averaging retain the original action and the prescribed open image.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open ComplexBundle Set TopologicalSpace Topology
open scoped Manifold ContDiff Pointwise

variable {VG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace VG G]
  [hLie : LieGroup 𝓘(ℝ, VG) ∞ G] [hGC : CompactSpace G]
  [MeasurableSpace G] [hGB : BorelSpace G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul 𝓘(ℝ, VG) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

include hLie hGC hGB hAction

/-- Relative smoothing cutoffs exist inside the specified invariant open image. -/
theorem exists_invariant_relative_cutoffs
    (D : Set M) (hD : IsCompact D)
    (hDi : ∀ (g : G) (x : M), g • x ∈ D ↔ x ∈ D)
    (U : Opens M) (hDU : D ⊆ U)
    (hUi : ∀ (g : G) (x : M), g • x ∈ U ↔ x ∈ U) :
    ∃ K₀ K₁ K₂ : Set M,
      IsCompact K₀ ∧ IsCompact K₁ ∧ IsCompact K₂ ∧ D ⊆ K₀ ∧
      K₀ ⊆ K₁ ∧ K₁ ⊆ interior K₂ ∧ K₂ ⊆ U ∧
      (∀ (g : G) (x : M), g • x ∈ K₀ ↔ x ∈ K₀) ∧
      (∀ (g : G) (x : M), g • x ∈ K₁ ↔ x ∈ K₁) ∧
      (∀ (g : G) (x : M), g • x ∈ K₂ ↔ x ∈ K₂) ∧
      ∃ ψ χ₀ χ₁ : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), M; 𝓘(ℝ), ℝ⟯,
        (∀ x ∈ D, ψ x = 0) ∧ (∀ x ∉ K₀, ψ x = 1) ∧
        (∀ (g : G) (x : M), ψ (g • x) = ψ x) ∧
        tsupport χ₀ ⊆ K₀ᶜ ∧ tsupport χ₁ ⊆ K₁ᶜ ∧
        (∀ x ∉ K₁, χ₀ x = 1) ∧ (∀ x ∉ K₂, χ₁ x = 1) ∧
        (∀ x, 0 ≤ χ₁ x ∧ χ₁ x ≤ 1) ∧
        (∀ (g : G) (x : M), χ₀ (g • x) = χ₀ x) ∧
        ∀ (g : G) (x : M), χ₁ (g • x) = χ₁ x := by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  -- Compact saturation enlarges each window without leaving the original invariant open set.
  have henlarge (K : Set M) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ L : Set M, IsCompact L ∧ K ⊆ interior L ∧ L ⊆ U ∧
        ∀ (g : G) (x : M), g • x ∈ L ↔ x ∈ L := by
    obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK U.isOpen hKU
    obtain ⟨hS, hLS, hSi⟩ := compact_saturation_properties (G := G) L hL
    refine ⟨(univ : Set G) • L, hS, hKL.trans (interior_mono hLS), ?_, hSi⟩
    rintro x ⟨g, _, y, hy, rfl⟩
    exact (hUi g y).mpr (hLU hy)
  obtain ⟨K₀, hK₀, hD₀, hK₀U, hK₀i⟩ := henlarge D hD hDU
  obtain ⟨L₀, hL₀, hK₀L₀, hL₀U, hL₀i⟩ := henlarge K₀ hK₀ hK₀U
  obtain ⟨K₁, hK₁, hL₀K₁, hK₁U, hK₁i⟩ := henlarge L₀ hL₀ hL₀U
  obtain ⟨L₁, hL₁, hK₁L₁, hL₁U, hL₁i⟩ := henlarge K₁ hK₁ hK₁U
  obtain ⟨K₂, hK₂, hL₁K₂, hK₂U, hK₂i⟩ := henlarge L₁ hL₁ hL₁U
  obtain ⟨η, hηone, hηsupport, _hηbounds, hηinv⟩ :=
    exists_invariant_smooth_cutoff (VG := VG) (n := n) D K₀ hD hK₀ hD₀ hDi hK₀i
  obtain ⟨η₀, hη₀one, hη₀support, _hη₀bounds, hη₀inv⟩ :=
    exists_invariant_smooth_cutoff (VG := VG) (n := n) L₀ K₁ hL₀ hK₁ hL₀K₁ hL₀i hK₁i
  obtain ⟨η₁, hη₁one, hη₁support, hη₁bounds, hη₁inv⟩ :=
    exists_invariant_smooth_cutoff (VG := VG) (n := n) L₁ K₂ hL₁ hK₂ hL₁K₂ hL₁i hK₂i
  let ψ : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ 1 - η x, contMDiff_const.sub η.property⟩
  let χ₀ : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ 1 - η₀ x, contMDiff_const.sub η₀.property⟩
  let χ₁ : C^∞⟮𝓘(ℝ, EuclideanSpace ℝ (Fin n)), M; 𝓘(ℝ), ℝ⟯ :=
    ⟨fun x ↦ 1 - η₁ x, contMDiff_const.sub η₁.property⟩
  -- The intermediate windows give neighborhood vanishing, hence the required closed supports.
  have hsupport₀ : tsupport χ₀ ⊆ (interior L₀)ᶜ := by
    apply closure_minimal ?_ isOpen_interior.isClosed_compl
    intro x hx hxL
    apply hx
    change 1 - η₀ x = 0
    simp only [hη₀one (interior_subset hxL), Pi.one_apply, sub_self]
  have hsupport₁ : tsupport χ₁ ⊆ (interior L₁)ᶜ := by
    apply closure_minimal ?_ isOpen_interior.isClosed_compl
    intro x hx hxL
    apply hx
    change 1 - η₁ x = 0
    simp only [hη₁one (interior_subset hxL), Pi.one_apply, sub_self]
  refine ⟨K₀, K₁, K₂, hK₀, hK₁, hK₂, hD₀.trans interior_subset,
    (hK₀L₀.trans interior_subset).trans (hL₀K₁.trans interior_subset),
    (hK₁L₁.trans interior_subset).trans hL₁K₂, hK₂U, hK₀i, hK₁i, hK₂i,
    ψ, χ₀, χ₁, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change 1 - η x = 0
    simp only [hηone hx, Pi.one_apply, sub_self]
  · intro x hx
    change 1 - η x = 1
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hηsupport h)), sub_zero]
  · intro g x
    exact congrArg (1 - ·) (hηinv g x)
  · exact hsupport₀.trans (compl_subset_compl.mpr hK₀L₀)
  · exact hsupport₁.trans (compl_subset_compl.mpr hK₁L₁)
  · intro x hx
    change 1 - η₀ x = 1
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hη₀support h)), sub_zero]
  · intro x hx
    change 1 - η₁ x = 1
    rw [image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hη₁support h)), sub_zero]
  · intro x
    change 0 ≤ 1 - η₁ x ∧ 1 - η₁ x ≤ 1
    exact ⟨sub_nonneg.mpr (hη₁bounds x).2, sub_le_self _ (hη₁bounds x).1⟩
  · intro g x
    exact congrArg (1 - ·) (hη₀inv g x)
  · intro g x
    exact congrArg (1 - ·) (hη₁inv g x)

end AtiyahSinger
