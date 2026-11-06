/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.AssociatedSphereProductChart

/-!
# A finite compact cover by actual associated product charts

Public module ID: M1069.

Every point lies in the product chart obtained from its original principal
trivialization and the original base and sphere charts. Shrinking inside these
sources and taking a finite subcover gives compact coordinate windows covering
the original associated sphere bundle.

Each window stays in a supplied open neighborhood of its retained center;
these neighborhoods can impose the original base and sphere frame conditions.
The windows are used to take a common cutoff parameter and to construct one
compact exterior for the supported symbol homotopy. Their existence uses the
underlying compact space, independently of whether any symbol vanishes or any
bundle rank is zero. The actual chosen associated atlas is not replaced.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Set
open scoped Manifold ContDiff

attribute [local instance] continuousSMul_orthogonalSphere

variable {n r : ℕ} {P B : Type*} [TopologicalSpace P] [TopologicalSpace B]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) B]
  [MulAction (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  [ContinuousSMul (Matrix.orthogonalGroup (Fin r) ℝ)ᵐᵒᵖ P]
  {projection : P → B} (S : SmoothOrthogonalPrincipalAtlas r (𝓡 n) projection)
  [CompactSpace (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]
  [T2Space (AssociatedBundle (Matrix.orthogonalGroup (Fin r) ℝ) P (OrthogonalSphere r))]

local notation "G" => Matrix.orthogonalGroup (Fin r) ℝ
local notation "Z" => AssociatedBundle G P (OrthogonalSphere r)
local notation "X" => EuclideanSpace ℝ (Fin n)
local notation "Y" => EuclideanSpace ℝ (Fin r)
local notation "H" => EuclideanSpace ℝ (Fin (n + r))

/-- The original compact associated bundle has a product-chart cover in prescribed neighborhoods. -/
theorem exists_associatedSphereProductChart_compact_cover
    (U : Z → Set Z) (hU : ∀ z, IsOpen (U z)) (hmemU : ∀ z, z ∈ U z) :
    ∃ (N : ℕ) (point : Fin N → Z),
      let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
      let b := fun i ↦ base (point i)
      let c := fun i ↦ chartAt X (b i)
      let d := fun i ↦ chartAt Y (associatedSphereTrivialization S (b i) (point i)).2
      let C := fun i ↦ associatedSphereProductChart S (b i) (c i) (d i)
      ∃ K : Fin N → Set H, (∀ i, IsCompact (K i)) ∧
        (∀ i, K i ⊆ (C i).target) ∧
        (∀ i w, w ∈ K i → (C i).symm w ∈ U (point i)) ∧
        ∀ z : Z, ∃ i, z ∈ (C i).source ∧ C i z ∈ K i := by
  classical
  let base := associatedBundleProjection (F := OrthogonalSphere r) S.toIsPrincipalBundle
  let t (z : Z) := associatedSphereTrivialization S (base z)
  let c (z : Z) := chartAt X (base z)
  let d (z : Z) := chartAt Y (t z z).2
  let C (z : Z) := associatedSphereProductChart S (base z) (c z) (d z)
  -- The point's original principal chart and its two original manifold charts contain it.
  have hsource (z : Z) : z ∈ (C z).source := by
    have htbase : (t z).baseSet = (S.trivialization (base z)).baseSet :=
      (exists_associatedBundleTrivialization S.toIsPrincipalBundle
        (S.trivialization (base z)) (S.equivariant (base z))).choose_spec.1
    have htz : z ∈ (t z).source :=
      (t z).mem_source.mpr (htbase.symm ▸ S.mem_baseSet (base z))
    refine ⟨⟨htz, ?_, mem_chart_source Y (t z z).2⟩, mem_univ _⟩
    change (t z z).1 ∈ (c z).source
    rw [(t z).coe_fst htz]
    exact mem_chart_source X (base z)
  have hwindow (z : Z) : ∃ L : Set Z,
      IsCompact L ∧ z ∈ interior L ∧ L ⊆ (C z).source ∩ U z := by
    obtain ⟨L, hL, hzL, hLC⟩ := exists_compact_between isCompact_singleton
      ((C z).open_source.inter (hU z))
      (singleton_subset_iff.mpr ⟨hsource z, hmemU z⟩)
    exact ⟨L, hL, hzL (mem_singleton z), hLC⟩
  choose L hL hinside hLW using hwindow
  have hLC (z : Z) : L z ⊆ (C z).source := fun _ hw ↦ (hLW z hw).1
  have hcover : (univ : Set Z) ⊆ ⋃ z, interior (L z) := by
    intro z _
    exact mem_iUnion.mpr ⟨z, hinside z⟩
  -- Compactness gives a finite family; retain each selected chart and its own compact window.
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun z ↦ interior (L z)) (fun _ ↦ isOpen_interior) hcover
  let e := s.equivFin.symm
  let point (i : Fin s.card) : Z := e i
  let K (i : Fin s.card) : Set H := (C (point i)) '' L (point i)
  have hK (i : Fin s.card) : IsCompact (K i) :=
    (hL (point i)).image_of_continuousOn ((C (point i)).continuousOn.mono (hLC (point i)))
  have hKC (i : Fin s.card) : K i ⊆ (C (point i)).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (C (point i)).map_source (hLC (point i) hz)
  refine ⟨s.card, point, K, hK, hKC, ?_, ?_⟩
  · intro i w hw
    obtain ⟨z, hz, rfl⟩ := hw
    change (C (point i)).symm (C (point i) z) ∈ U (point i)
    rw [(C (point i)).left_inv (hLC (point i) hz)]
    exact (hLW (point i) hz).2
  · intro z
    obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hs (mem_univ z))
    let i := e.symm ⟨w, hw⟩
    have hpoint : point i = w := congrArg Subtype.val (e.apply_symm_apply ⟨w, hw⟩)
    have hzL : z ∈ L (point i) := hpoint ▸ interior_subset hzw
    exact ⟨i, hLC (point i) hzL, ⟨z, hzL, rfl⟩⟩

end AtiyahSinger
