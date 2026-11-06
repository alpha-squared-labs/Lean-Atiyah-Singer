/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.CompactSupportCohomologyRadialControl
public import AtiyahSinger.Topology.RelativeSupportedCohomologyThom

/-!
# Compact-support cohomology below the fiber rank

Public module ID: M2207.

The complete cochain Thom comparisons retain their zero terms below the rank.
The exact joint-relative row transfers that vanishing to zero-section supports.
Compact radial control then gives vanishing in the actual compact-support colimit.
No negative degree is replaced by degree zero, and no base dimension is required.

Sources: the relative Thom theorem and the long exact sequence of a pair,
Hatcher, Algebraic Topology, Sections 3.2 and 4.D.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits HomologicalComplex TopologicalSpace

universe u

variable (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X]
  [T2Space X] (E : X → Type u)
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Cohomology supported on a compact part of the zero section vanishes below the rank. -/
theorem supportedCohomologyThomSupport_subsingleton_below_rank
    (o : CohomologyOrientation R r E) (K : Compacts X) (k : ℕ) (hk : k < r) :
    Subsingleton (relativeSingularCohomology R
      ((supportedCohomologyThomSupport r E K :
        Set (TotalSpace (EuclideanSpace ℝ (Fin r)) E))ᶜ) k) := by
  let S := (K : Set X)ᶜ
  let A := bundleNonzero r E
  let B := (bundleProjection r E) ⁻¹' S
  let t := cohomologyThomClass R r E o
  let T := relativeUnionSingularCochainSequence R A B
  -- Use an actual cocycle for the specified Thom class and restrict that same cocycle.
  obtain ⟨c, hc⟩ := (relativeSingularCoboundaries R A r).mkQ_surjective
    (((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom t)
  have hct : relativeSingularCocycleClass R A r c = t := by
    change ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.inv
      ((relativeSingularCoboundaries R A r).mkQ c) = t
    rw [hc]
    exact congrArg (fun f ↦ f t)
      ((relativeSingularCochains R A).sc r).moduleCatHomologyIso.hom_inv_id
  let cB : relativeSingularCocycles R (bundleNonzeroOver r E S) r := ⟨T.g.f r c.val, by
    change T.X₃.dFrom r (T.g.f r c.val) = 0
    have h := congrArg (fun f ↦ f c.val) (T.g.comm_from r)
    change T.X₃.dFrom r (T.g.f r c.val) = T.g.next r (T.X₂.dFrom r c.val) at h
    have hclosed : T.X₂.dFrom r c.val = 0 := c.property
    rw [h, hclosed, map_zero]⟩
  have hcBclass : relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB =
      relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
        (A := bundleNonzeroOver r E S) (B := A) (fun _ hx ↦ hx) r t := by
    have h := homologyMap_cycleClass R T.X₂ T.X₃ T.g r c cB rfl
    change relativeSingularCohomologyPullback R (ContinuousMap.subtypeVal B)
      (A := bundleNonzeroOver r E S) (B := A) (fun _ hx ↦ hx) r
        (relativeSingularCocycleClass R A r c) =
      relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB at h
    rw [hct] at h
    exact h.symm
  have ht (x : X) : relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
      (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r t = o.fiberClass x :=
    (existsUnique_cohomologyThomClass R r E o).exists.choose_spec x
  have hgen (x : X) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
        (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r
          (relativeSingularCocycleClass R A r c)) := by
    rw [hct, ht]
    exact o.is_generator x
  have hgenB (x : X) (hx : x ∈ S) : Function.Bijective (fun a : R ↦ a •
      relativeSingularCohomologyPullback R (bundleFiberInclusionOver r E S x hx)
        (A := {v : E x | v ≠ 0}) (B := bundleNonzeroOver r E S) (fun _ hv ↦ hv) r
          (relativeSingularCocycleClass R (bundleNonzeroOver r E S) r cB)) := by
    rw [hcBclass, ← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp]
    change Function.Bijective (fun a : R ↦ a • relativeSingularCohomologyPullback R
      (bundleFiberInclusion r E x) (A := {v : E x | v ≠ 0}) (B := A) (fun _ hv ↦ hv) r t)
    rw [ht]
    exact o.is_generator x
  -- The two complete cochain comparisons yield the actual joint-relative cup bijection.
  have hGlobal := relativeSingularCochainCupMap_bijective_of_bundle_generator R r E c hgen
  have hRestricted := relativeSingularCochainCupMap_bijective_of_bundleTotalOver_generator
    R r E S cB hgenB
  -- The extended source is genuinely zero in degrees below the fiber rank.
  let e : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
    ComplexShape.embeddingUp'Add (1 : ℕ) r
  have hzero (C : CochainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) (hj : j < r) :
      Subsingleton ((C.extend e).homology j) := by
    apply ModuleCat.isZero_iff_subsingleton.mp
    apply (exactAt_iff_isZero_homology _ _).mp
    exact extend_exactAt _ e j (by
      intro p hp
      change p + r = j at hp
      omega)
  have hmiddle (j : ℕ) (hj : j < r) : Subsingleton (T.X₂.homology j) := by
    let := hzero (singularCochains R (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) j hj
    exact (hGlobal j).surjective.subsingleton
  have hright (j : ℕ) (hj : j < r) : Subsingleton (T.X₃.homology j) := by
    let := hzero (singularCochains R (BundleTotalOver r E S)) j hj
    exact (hRestricted j).surjective.subsingleton
  -- The initial degree uses injectivity; positive degrees use the preceding term of the row.
  have hT := shortExact_relativeUnionSingularCochainSequence R A B
  have hjoint : Subsingleton (T.X₁.homology k) := by
    let := hmiddle k hk
    cases k with
    | zero =>
      have := hT.mono_f
      have hmono : Mono (homologyMap T.f 0) := by
        apply mono_homologyMap_of_mono_of_not_rel
        simp
      exact ((ModuleCat.mono_iff_injective _).mp hmono).subsingleton
    | succ j =>
      let := hright j (by omega)
      have hz (z : T.X₁.homology (j + 1)) : z = 0 := by
        have hm : homologyMap T.f (j + 1) z = 0 := Subsingleton.elim _ _
        obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
          (hT.homology_exact₁ j (j + 1) rfl) z hm
        have ha0 : a = 0 := Subsingleton.elim _ _
        simpa only [ha0, map_zero] using ha.symm
      exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩
  -- The open-union comparison is the original support-complement identification.
  have hOpen := isOpen_supportedCohomologyThomSubspaces r E K
  have : Subsingleton (relativeUnionSingularCohomology R B A k) := hjoint
  have : Subsingleton (relativeSingularCohomology R (B ∪ A) k) :=
    (relativeUnionCohomologyComparison_bijective R B A hOpen.1 hOpen.2 k).injective.subsingleton
  rw [← supportedCohomologyThomSupport_compl r E K]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- For an oriented bundle over a Hausdorff base, compact-support cohomology vanishes
below its rank, independently of any manifold dimension on the base. -/
theorem compactSupportCohomology_subsingleton_below_rank_of_orientation
    (o : CohomologyOrientation R r E) (k : ℕ) (hk : k < r) :
    Subsingleton (compactSupportCohomology R
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E) k) := by
  let Y := TotalSpace (EuclideanSpace ℝ (Fin r)) E
  let G := compactSupportCohomologyFunctor R Y k
  have hz (a : compactSupportCohomology R Y k) : a = 0 := by
    obtain ⟨L, c, rfl⟩ := compactSupportCohomology_exists_representative R Y k a
    -- Enlarge this precise compact representative to its radial control.
    obtain ⟨D, hLD, hZD, hbij⟩ :=
      exists_compact_thomSupport_restriction_bijective R r E L k
    let K := L.map (bundleProjection r E) (bundleProjection r E).continuous
    obtain ⟨z, hz⟩ := hbij.surjective (G.map (homOfLE hLD) c)
    have hz0 : z = 0 :=
      (supportedCohomologyThomSupport_subsingleton_below_rank R r E o K k hk).elim _ _
    have hc0 : G.map (homOfLE hLD) c = 0 := by
      rw [← hz, hz0, map_zero]
    -- Naturality of the same colimit injection kills the original representative.
    change (colimit.ι G L) c = 0
    rw [← colimit.w G (homOfLE hLD)]
    change (colimit.ι G D) (G.map (homOfLE hLD) c) = 0
    rw [hc0, map_zero]
  exact ⟨fun a b ↦ (hz a).trans (hz b).symm⟩

end AtiyahSinger
