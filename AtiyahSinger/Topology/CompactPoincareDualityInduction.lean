/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactPoincareDualityDirectedUnion

/-!
# Local-to-global induction for compact Poincaré duality

Public module ID: M1645.

This module isolates the topological induction from the Mayer--Vietoris
comparison. Bounded convex open sets provide the Euclidean basis; finite unions
and directed open unions extend the assertion first to Euclidean open sets and
then to arbitrary charted manifolds. The Mayer--Vietoris hypothesis is an explicit
input, so the induction does not assert that the connecting cap square is automatic.

Source: Hatcher, *Algebraic Topology*, Theorem 3.35 and Lemma 3.36.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open CategoryTheory TopologicalSpace Topology

universe u

/- The two private predicates package entire complementary-degree families during induction.
They introduce neither a new cohomology theory nor a replacement duality map. -/
private def HasCompactDuality (n : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] [T2Space X] [SecondCountableTopology X] : Prop :=
  ∀ (O : HomologicalOrientation n X) (p q : ℕ) (h : p + q = n),
    Function.Bijective (compactPoincareDuality O p q h)

private def HasCompactDualityMayerVietoris (n : ℕ) : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [T2Space X] [SecondCountableTopology X] (U V : Opens X), U ⊔ V = ⊤ →
      HasCompactDuality n U → HasCompactDuality n V → HasCompactDuality n ↥(U ⊓ V) →
      HasCompactDuality n X

section Topology

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y]
variable [T2Space X] [T2Space Y] [SecondCountableTopology X] [SecondCountableTopology Y]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasCompactDuality_homeomorph (e : X ≃ₜ Y)
    (hX : HasCompactDuality n X) : HasCompactDuality n Y := by
  let : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) Y
  intro O p q h
  let O' := homologicalOrientationOpenPullback O ⟨e, e.continuous⟩ e.isOpenEmbedding
  exact compactPoincareDuality_bijective_of_homeomorph e O' O
    (homologicalOrientationOpenPullback_orientationPreserving O
      ⟨e, e.continuous⟩ e.isOpenEmbedding) p q h (hX O' p q h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasCompactDuality_sup (hmv : HasCompactDualityMayerVietoris.{u} n)
    (U V : Opens X) (hU : HasCompactDuality n U) (hV : HasCompactDuality n V)
    (hI : HasCompactDuality n ↥(U ⊓ V)) : HasCompactDuality n ↥(U ⊔ V) := by
  let W := U ⊔ V
  let U' : Opens W := ⟨Subtype.val ⁻¹' (U : Set X), U.isOpen.preimage continuous_subtype_val⟩
  let V' : Opens W := ⟨Subtype.val ⁻¹' (V : Set X), V.isOpen.preimage continuous_subtype_val⟩
  have hcover : U' ⊔ V' = ⊤ := by
    ext x
    exact iff_true_intro x.property
  have he (A : Opens X) (hA : A ≤ W) :
      (⟨Subtype.val ⁻¹' (A : Set X), A.isOpen.preimage continuous_subtype_val⟩ : Opens W) ≃ₜ A :=
    IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun x hx ↦ ⟨⟨x, hA hx⟩, rfl⟩)
  apply hmv W U' V' hcover
  · exact hasCompactDuality_homeomorph (he U le_sup_left).symm hU
  · exact hasCompactDuality_homeomorph (he V le_sup_right).symm hV
  · exact hasCompactDuality_homeomorph
      (he (U ⊓ V) (inf_le_left.trans le_sup_left)).symm hI

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasCompactDuality_iSup {ι : Type u} [Nonempty ι]
    (U : ι → Opens X) (hdir : Directed (· ≤ ·) U)
    (hU : ∀ i, HasCompactDuality n (U i)) : HasCompactDuality n ↥(⨆ i, U i) := by
  let W := ⨆ i, U i
  let : LocallyCompactSpace W := ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) W
  let V (i : ι) : Opens W :=
    ⟨Subtype.val ⁻¹' (U i : Set X), (U i).isOpen.preimage continuous_subtype_val⟩
  have hVdir : Directed (· ≤ ·) V := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, fun x hx ↦ hik hx, fun x hx ↦ hjk hx⟩
  have hVcover : ⋃ i, (V i : Set W) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : x.val ∈ ⋃ i, (U i : Set X) := by
      have hx : x.val ∈ ((⨆ i, U i : Opens X) : Set X) := x.property
      simpa only [Opens.coe_iSup] using hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hV (i : ι) : HasCompactDuality n (V i) := by
    let e : V i ≃ₜ U i := IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (fun x hx ↦ ⟨⟨x, (le_iSup U i) hx⟩, rfl⟩)
    exact hasCompactDuality_homeomorph e.symm (hU i)
  intro O p q h
  exact compactPoincareDuality_bijective_of_directedCover V hVdir hVcover O p q h
    (fun i ↦ hV i _ p q h)

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasCompactDuality_iSup_of_inter_closed
    (hmv : HasCompactDualityMayerVietoris.{u} n)
    (B : Set (Opens X)) (hB : ∀ U ∈ B, HasCompactDuality n U)
    (hinter : ∀ U ∈ B, ∀ V ∈ B, U ⊓ V ∈ B)
    {ι : Type u} (U : ι → Opens X) (hU : ∀ i, U i ∈ B) :
    HasCompactDuality n ↥(⨆ i, U i) := by
  classical
  have hfinite (s : Finset ι) : ∀ (V : ι → Opens X),
      (∀ i, V i ∈ B) → HasCompactDuality n ↥(s.sup V) := by
    induction s using Finset.induction_on with
    | empty =>
      intro V _
      change HasCompactDuality n ↥(⊥ : Opens X)
      let : IsEmpty ↥(⊥ : Opens X) := ⟨fun x ↦ x.property⟩
      intro O p q h
      exact compactPoincareDuality_bijective_of_isEmpty O p q h
    | @insert a s _ ih =>
      intro V hV
      rw [Finset.sup_insert]
      apply hasCompactDuality_sup hmv
      · exact hB (V a) (hV a)
      · exact ih V hV
      · rw [Finset.sup_inf_distrib_left]
        exact ih (fun i ↦ V a ⊓ V i) (fun i ↦ hinter (V a) (hV a) (V i) (hV i))
  -- Finite unions form a directed cover of the original open union.
  let V (s : Finset ι) : Opens X := s.sup U
  have hdir : Directed (· ≤ ·) V := by
    intro s t
    refine ⟨s ∪ t, ?_, ?_⟩
    · exact Finset.sup_le fun i hi ↦ Finset.le_sup (Finset.mem_union_left t hi)
    · exact Finset.sup_le fun i hi ↦ Finset.le_sup (Finset.mem_union_right s hi)
  have hsup : (⨆ s, V s) = ⨆ i, U i := by
    apply le_antisymm
    · exact iSup_le fun s ↦ Finset.sup_le fun i _ ↦ le_iSup U i
    · apply iSup_le
      intro i
      exact (show U i ≤ V {i} by simp [V]).trans (le_iSup V {i})
  rw [← hsup]
  exact hasCompactDuality_iSup V hdir (fun s ↦ hfinite s U hU)

end Topology

section Euclidean

variable {n : ℕ} {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) E] [SecondCountableTopology E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem hasCompactDuality_euclideanOpen
    (hmv : HasCompactDualityMayerVietoris.{u} n)
    (e : E ≃L[ℝ] (Fin n → ℝ)) (U : Opens E) : HasCompactDuality n U := by
  let B : Set (Opens E) :=
    {V | Convex ℝ (V : Set E) ∧ Bornology.IsBounded (V : Set E)}
  have hB (V : Opens E) (hV : V ∈ B) : HasCompactDuality n V := by
    intro O p q h
    exact compactPoincareDuality_bijective_of_bounded_convex e V hV.1 hV.2 O p q h
  have hBI (V : Opens E) (hV : V ∈ B) (W : Opens E) (hW : W ∈ B) : V ⊓ W ∈ B :=
    ⟨hV.1.inter hW.1, hV.2.subset Set.inter_subset_left⟩
  let I := {V : Opens E // V ∈ B ∧ V ≤ U}
  let V (i : I) : Opens E := i.val
  have hsup : (⨆ i, V i) = U := by
    apply le_antisymm
    · exact iSup_le fun i ↦ i.property.2
    · intro x hx
      obtain ⟨r, hr, hru⟩ := Metric.isOpen_iff.mp U.isOpen x hx
      let W : Opens E := ⟨Metric.ball x r, Metric.isOpen_ball⟩
      let i : I := ⟨W, ⟨convex_ball x r, Metric.isBounded_ball⟩, hru⟩
      exact (le_iSup V i) (Metric.mem_ball_self hr)
  rw [← hsup]
  exact hasCompactDuality_iSup_of_inter_closed hmv B hB hBI V
    (fun i ↦ i.property.1)

end Euclidean

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The genuine two-open-set Mayer--Vietoris transfer implies duality on every manifold.
The transfer hypothesis covers all complementary degrees and all specified orientations. -/
theorem compactPoincareDuality_bijective_of_mayerVietoris
    {n : ℕ}
    (hmv : ∀ (Y : Type u) [TopologicalSpace Y]
      [ChartedSpace (EuclideanSpace ℝ (Fin n)) Y] [T2Space Y] [SecondCountableTopology Y]
      (U V : Opens Y), U ⊔ V = ⊤ →
        (∀ (OU : HomologicalOrientation n U) (p q : ℕ) (h : p + q = n),
          Function.Bijective (compactPoincareDuality OU p q h)) →
        (∀ (OV : HomologicalOrientation n V) (p q : ℕ) (h : p + q = n),
          Function.Bijective (compactPoincareDuality OV p q h)) →
        (∀ (OI : HomologicalOrientation n ↥(U ⊓ V)) (p q : ℕ) (h : p + q = n),
          Function.Bijective (compactPoincareDuality OI p q h)) →
        ∀ (OY : HomologicalOrientation n Y) (p q : ℕ) (h : p + q = n),
          Function.Bijective (compactPoincareDuality OY p q h))
    {X : Type u} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
    [T2Space X] [SecondCountableTopology X]
    (O : HomologicalOrientation n X) (p q : ℕ) (h : p + q = n) :
    Function.Bijective (compactPoincareDuality O p q h) := by
  -- Lift the Euclidean model to the same universe as the given manifold.
  let H := EuclideanSpace ℝ (Fin n)
  let E := ULift.{u} H
  let down : E ≃ₜ H := Homeomorph.ulift
  let : ChartedSpace H E := down.isOpenEmbedding.singletonChartedSpace
  let eL : E ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.ulift.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n ↦ ℝ))
  have hE (U : Opens E) : HasCompactDuality n U := hasCompactDuality_euclideanOpen hmv eL U
  let B : Set (Opens X) := {V | ∃ x : X, (V : Set X) ⊆ (chartAt H x).source}
  have hB (V : Opens X) (hV : V ∈ B) : HasCompactDuality n V := by
    obtain ⟨x, hx⟩ := hV
    let c := chartAt H x
    let f : C(V, c.source) := ContinuousMap.inclusion hx
    have hf : IsOpenEmbedding f :=
      IsOpenEmbedding.inclusion hx (V.isOpen.preimage continuous_subtype_val)
    let g : C(V, E) :=
      ⟨fun y ↦ ULift.up (c y.val),
        Homeomorph.ulift.symm.continuous.comp
          (c.isOpenEmbedding_restrict.continuous.comp f.continuous)⟩
    have hg : IsOpenEmbedding g :=
      Homeomorph.ulift.symm.isOpenEmbedding.comp (c.isOpenEmbedding_restrict.comp hf)
    let W : Opens E := ⟨Set.range g, hg.isOpen_range⟩
    let e : V ≃ₜ W := hg.isEmbedding.toHomeomorph
    exact hasCompactDuality_homeomorph e.symm (hE W)
  have hBI (U : Opens X) (hU : U ∈ B) (V : Opens X) (_hV : V ∈ B) : U ⊓ V ∈ B := by
    obtain ⟨x, hx⟩ := hU
    exact ⟨x, Set.inter_subset_left.trans hx⟩
  -- Chart domains cover the manifold; their intersections remain inside a chart.
  let U (x : X) : Opens X := ⟨(chartAt H x).source, (chartAt H x).open_source⟩
  have htop : (⨆ x, U x) = ⊤ := by
    apply top_unique
    intro x _hx
    exact (le_iSup U x) (mem_chart_source H x)
  have htopDuality : HasCompactDuality n ↥(⊤ : Opens X) := by
    rw [← htop]
    exact hasCompactDuality_iSup_of_inter_closed hmv B hB hBI U
      (fun x ↦ ⟨x, Set.Subset.rfl⟩)
  let eTop : (⊤ : Opens X) ≃ₜ X := Homeomorph.Set.univ X
  exact hasCompactDuality_homeomorph eTop htopDuality O p q h

end AtiyahSinger
