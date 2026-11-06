/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.RelativeCohomologySequence
public import AtiyahSinger.Topology.SingularCohomologyDescent
public import AtiyahSinger.Topology.SupportedCohomologyThom

/-!
# Radial compact controls in a vector bundle

Public module ID: M1666.

Every compact total-space control has a compact fiberwise radial hull. Its
relative support cohomology agrees with support on the zero section over its
compact projection. The comparison is the original relative restriction.

The proof uses the open exhaustion obtained by positive integral dilations.
The inclusions of relative subspaces in finite intersections have radial
homotopy inverses. The actual small-chain Čech descent then proves the
relative complement pair acyclic. No continuous global fiber norm or local compactness is used.

This is a supplementary singular-cochain proof of the compact-control step
in the compact-support Thom theorem, using relative sequences and excision
as in Hatcher, Algebraic Topology, Sections 3.1 and 3.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits HomologicalComplex TopologicalSpace
open scoped unitInterval

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem radial_cover_acyclic
    (R : Type) [CommRing R] {Y : Type u} [TopologicalSpace Y]
    (s : ℝ → Y → Y) (hs : Continuous (fun p : ℝ × Y ↦ s p.1 p.2))
    (hone : ∀ y, s 1 y = y) (A : Set Y)
    (hA : ∀ c, 1 ≤ c → ∀ y ∈ A, s c y ∈ A)
    {ι : Type u} (U : ι → Set Y) (hU : ∀ i, IsOpen (U i))
    (hcover : ⋃ i, U i = Set.univ)
    (hstable : ∀ i c, 1 ≤ c → ∀ y ∈ U i, s c y ∈ U i)
    (c : ι → ℝ) (hc : ∀ i, 1 ≤ c i)
    (hpush : ∀ i y, y ∈ U i → s (c i) y ∈ A) (k : ℕ) :
    Subsingleton (relativeSingularCohomology R A k) := by
  -- Each finite-intersection inclusion has a radial homotopy inverse on its relative subspace.
  have hlocal (n : ℕ) (a : Fin (n + 1) → ι) (q : ℕ) :
      Subsingleton (relativeSingularCohomology R
        ((Subtype.val : singularCechIntersection U a → Y) ⁻¹' A) q) := by
    let W := singularCechIntersection U a
    let B : Set W := (Subtype.val : W → Y) ⁻¹' A
    let i : C(B, W) := ⟨Subtype.val, continuous_subtype_val⟩
    let g : C(W, B) :=
      ⟨fun y ↦ ⟨⟨s (c (a 0)) y.val,
          fun j ↦ hstable (a j) (c (a 0)) (hc (a 0)) y.val (y.property j)⟩,
            hpush (a 0) y.val (y.property 0)⟩,
        ((hs.comp (continuous_const.prodMk continuous_subtype_val)).subtype_mk _).subtype_mk _⟩
    let tscale (t : unitInterval) : ℝ := 1 + (1 - (t : ℝ)) * (c (a 0) - 1)
    have ht (t : unitInterval) : 1 ≤ tscale t :=
      le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr t.property.2)
        (sub_nonneg.mpr (hc (a 0))))
    have htcont : Continuous tscale := by dsimp [tscale]; fun_prop
    have hgi : (g.comp i).Homotopic (ContinuousMap.id B) := by
      refine ⟨{ toFun p := ⟨⟨s (tscale p.1) p.2.val.val,
                  fun j ↦ hstable (a j) _ (ht _) _ (p.2.val.property j)⟩,
                  hA _ (ht _) _ p.2.property⟩
                continuous_toFun := ?_
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · exact ((hs.comp ((htcont.comp continuous_fst).prodMk
          (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))))
          |>.subtype_mk _).subtype_mk _
      · intro y
        apply Subtype.ext
        apply Subtype.ext
        simp [tscale, g, i]
      · intro y
        apply Subtype.ext
        apply Subtype.ext
        simp [tscale, hone]
    have hig : (i.comp g).Homotopic (ContinuousMap.id W) := by
      refine ⟨{ toFun p := ⟨s (tscale p.1) p.2.val,
                  fun j ↦ hstable (a j) _ (ht _) _ (p.2.property j)⟩
                continuous_toFun := ?_
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · exact (hs.comp ((htcont.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      · intro y
        apply Subtype.ext
        simp [tscale, g, i]
      · intro y
        apply Subtype.ext
        simp [tscale, hone]
    exact subsingleton_relativeSingularCohomology_of_isIso_inclusion R B
      (fun j ↦ isIso_singularCohomologyPullback_of_homotopyInverse R i g hgi hig j) q
  -- The actual augmented Čech complex detects the global class; all local classes vanish.
  have hprod : Subsingleton ((singularCechCochains R U A 1).homology k) := by
    let F (a : Fin 1 → ι) := relativeSingularCochains R
      ((Subtype.val : singularCechIntersection U a → Y) ⁻¹' A)
    have (a : Fin 1 → ι) : Subsingleton ((F a).homology k) := hlocal 0 a k
    exact (bijective_homologyMap_cochainFamilyProductProjection R F k).injective.subsingleton
  obtain ⟨z, _hz, huniq⟩ := existsUnique_relativeSingularCohomology_of_cech R U A hU hcover k
    (fun m a q _hq ↦ hlocal (m + 1) a q) 0 (map_zero _)
  exact ⟨fun x y ↦ (huniq x (Subsingleton.elim _ _)).trans
    (huniq y (Subsingleton.elim _ _)).symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem radial_restriction_isIso
    (R : Type) [CommRing R] {Y : Type u} [TopologicalSpace Y]
    (s : ℝ → Y → Y) (hs : Continuous (fun p : ℝ × Y ↦ s p.1 p.2))
    (hone : ∀ y, s 1 y = y) (hmul : ∀ a b y, s a (s b y) = s (a * b) y)
    (D Z : Set Y) (hD : IsClosed D) (hZD : Z ⊆ D)
    (hZ : ∀ c, 1 ≤ c → ∀ y ∉ Z, s c y ∉ Z)
    (hout : ∀ c, 1 ≤ c → ∀ y ∉ D, s c y ∉ D)
    (hescape : ∀ y ∉ Z, ∃ n : ℕ, s ((n : ℝ) + 1) y ∉ D) (k : ℕ) :
    IsIso (relativeSingularCohomologyRestriction R Dᶜ Zᶜ
      (Set.compl_subset_compl.mpr hZD) k) := by
  let C := Zᶜ
  let A : Set C := (Subtype.val : C → Y) ⁻¹' Dᶜ
  let dilate (c : ℝ) (y : C) : C :=
    ⟨s (max 1 c) y.val, hZ _ (le_max_left _ _) _ y.property⟩
  have hdilate : Continuous (fun p : ℝ × C ↦ dilate p.1 p.2) :=
    (hs.comp ((continuous_const.max continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  let U (n : ULift.{u} ℕ) : Set C := {y | s ((n.down : ℝ) + 1) y.val ∉ D}
  have hU (n : ULift.{u} ℕ) : IsOpen (U n) :=
    hD.isOpen_compl.preimage
      (hs.comp (continuous_const.prodMk continuous_subtype_val))
  have hcover : ⋃ n, U n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := hescape y.val y.property
    exact Set.mem_iUnion.mpr ⟨ULift.up n, hn⟩
  have hzero (q : ℕ) : Subsingleton (relativeSingularCohomology R A q) := by
    apply radial_cover_acyclic R dilate hdilate (fun y ↦ Subtype.ext (by simp [dilate, hone])) A
      (fun c hc y hy ↦ ?_) U hU hcover (fun n c hc y hy ↦ ?_)
      (fun n ↦ (n.down : ℝ) + 1) (fun n ↦ by
        have := Nat.cast_nonneg (α := ℝ) n.down
        linarith) (fun n y hy ↦ ?_) q
    · change s (max 1 c) y.val ∉ D
      exact hout _ (le_max_left _ _) _ hy
    · change s ((n.down : ℝ) + 1) (s (max 1 c) y.val) ∉ D
      rw [hmul, mul_comm, ← hmul]
      exact hout _ (le_max_left _ _) _ hy
    · change s (max 1 ((n.down : ℝ) + 1)) y.val ∉ D
      rw [max_eq_right (by
        have := Nat.cast_nonneg (α := ℝ) n.down
        linarith : (1 : ℝ) ≤ (n.down : ℝ) + 1)]
      exact hy
  -- The third term of the original triple is acyclic, so its first arrow is an isomorphism.
  let S := relativeSingularCochainTripleSequence R Dᶜ Zᶜ
    (Set.compl_subset_compl.mpr hZD)
  have hS : S.ShortExact := shortExact_relativeSingularCochainTripleSequence R Dᶜ Zᶜ
    (Set.compl_subset_compl.mpr hZD)
  have hthird (q : ℕ) : IsZero (S.X₃.homology q) :=
    ModuleCat.isZero_iff_subsingleton.mpr (hzero q)
  change IsIso (homologyMap S.f k)
  have hepi : Epi (homologyMap S.f k) :=
    (hS.homology_exact₂ k).epi_f ((hthird k).eq_of_tgt _ _)
  have hmono : Mono (homologyMap S.f k) := by
    cases k with
    | zero =>
      have := hS.mono_f
      apply mono_homologyMap_of_mono_of_not_rel
      simp
    | succ n =>
      exact (hS.homology_exact₁ n (n + 1) rfl).mono_g ((hthird n).eq_of_src _ _)
  exact isIso_of_mono_of_epi _

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Every compact total-space control enlarges to a compact radial hull whose original
support restriction from its compact zero section is bijective in every degree. -/
theorem exists_compact_thomSupport_restriction_bijective
    (R : Type) [CommRing R] (r : ℕ) {X : Type u} [TopologicalSpace X] [T2Space X]
    (E : X → Type u) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
    [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
    [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
    [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
    (L : Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (k : ℕ) :
    ∃ (D : Compacts (TotalSpace (EuclideanSpace ℝ (Fin r)) E)) (_hLD : L ≤ D)
      (hZD : supportedCohomologyThomSupport r E
        (L.map (bundleProjection r E) (bundleProjection r E).continuous) ≤ D),
        Function.Bijective ((compactSupportCohomologyFunctor R _ k).map (homOfLE hZD)) := by
  /- Form the compact radial hull in the actual bundle. Its complement is stable under
  outward dilation. Positive integral dilations exhaust the complement of its zero support;
  the preceding relative Čech argument identifies the same original support restriction. -/
  let F := EuclideanSpace ℝ (Fin r)
  let T := TotalSpace F E
  let : T2Space T := t2Space_fiberBundleTotal F E
  let s (a : ℝ) (y : T) : T := ⟨y.proj, a • y.snd⟩
  have hs : Continuous (fun p : ℝ × T ↦ s p.1 p.2) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    let e := trivializationAt F E p.2.proj
    have h := (FiberBundle.continuousAt_totalSpace F _).mp
      (continuous_snd.continuousAt (x := p))
    apply (FiberBundle.continuousAt_totalSpace F _).mpr
    refine ⟨h.1, ?_⟩
    apply (continuous_fst.continuousAt.smul h.2).congr_of_eventuallyEq
    filter_upwards [h.1.eventually (e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F E p.2.proj))] with q hq
    exact (e.linear ℝ hq).map_smul q.1 q.2.snd
  have hone (y : T) : s 1 y = y := by cases y; simp [s]
  have hmul (a b : ℝ) (y : T) : s a (s b y) = s (a * b) y := by
    simp [s, smul_smul]
  let K : Compacts X := L.map (bundleProjection r E) (bundleProjection r E).continuous
  let Z := supportedCohomologyThomSupport r E K
  let D : Compacts T :=
    ⟨(fun p : ℝ × T ↦ s p.1 p.2) '' (Set.Icc (0 : ℝ) 1 ×ˢ (L : Set T)),
      (isCompact_Icc.prod L.isCompact).image hs⟩
  have hLD : L ≤ D := by
    intro y hy
    exact ⟨(1, y), ⟨⟨zero_le_one, le_rfl⟩, hy⟩, hone y⟩
  have hZD : Z ≤ D := by
    rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨z, hz, rfl⟩
    refine ⟨(0, z), ⟨⟨le_rfl, zero_le_one⟩, hz⟩, ?_⟩
    simp [s, bundleZeroSection, bundleProjection, zeroSection]
  have hDproj (y : T) (hy : y ∈ D) : y.proj ∈ K := by
    rcases hy with ⟨⟨a, z⟩, ⟨_ha, hz⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  have hstar (a : ℝ) (ha : a ∈ Set.Icc (0 : ℝ) 1) (y : T) (hy : y ∈ D) :
      s a y ∈ D := by
    rcases hy with ⟨⟨b, z⟩, ⟨hb, hz⟩, rfl⟩
    refine ⟨(a * b, z), ⟨⟨mul_nonneg ha.1 hb.1, ?_⟩, hz⟩, ?_⟩
    · change a * b ≤ 1
      exact (mul_le_mul_of_nonneg_right ha.2 hb.1).trans (by simpa using hb.2)
    · exact (hmul a b z).symm
  have hZscale (a : ℝ) (y : T) (hy : y ∈ Z) : s a y ∈ Z := by
    rcases hy with ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    simp [s, bundleZeroSection, zeroSection]
  have hZ (a : ℝ) (ha : 1 ≤ a) (y : T) (hy : y ∉ Z) : s a y ∉ Z := by
    intro h
    have h' := hZscale a⁻¹ (s a y) h
    rw [hmul, inv_mul_cancel₀ (ne_of_gt (lt_of_lt_of_le zero_lt_one ha)), hone] at h'
    exact hy h'
  have hout (a : ℝ) (ha : 1 ≤ a) (y : T) (hy : y ∉ D) : s a y ∉ D := by
    intro h
    have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
    have h' := hstar a⁻¹ ⟨le_of_lt (inv_pos.mpr ha0), inv_le_one_of_one_le₀ ha⟩ (s a y) h
    rw [hmul, inv_mul_cancel₀ (ne_of_gt ha0), hone] at h'
    exact hy h'
  have hescape (y : T) (hy : y ∉ Z) : ∃ n : ℕ, s ((n : ℝ) + 1) y ∉ D := by
    by_cases hy0 : y.snd = 0
    · refine ⟨0, ?_⟩
      simp only [Nat.cast_zero, zero_add, hone]
      intro h
      apply hy
      refine ⟨y.proj, hDproj y h, ?_⟩
      change (⟨y.proj, 0⟩ : T) = y
      exact congrArg (fun v : E y.proj ↦ (⟨y.proj, v⟩ : T)) hy0.symm
    · -- Compactness is used only on this closed fiber, where its original norm is continuous.
      have hfiber : IsCompact ((TotalSpace.mk y.proj : E y.proj → T) ⁻¹' (D : Set T)) :=
        (FiberBundle.totalSpaceMk_isClosedEmbedding F E y.proj).isCompact_preimage D.isCompact
      obtain ⟨b, hb⟩ := hfiber.bddAbove_image continuous_norm.continuousOn
      obtain ⟨n, hn⟩ := exists_nat_gt (b / ‖y.snd‖)
      refine ⟨n, ?_⟩
      intro h
      have hbound : ‖((n : ℝ) + 1) • y.snd‖ ≤ b :=
        hb (Set.mem_image_of_mem _ h)
      rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hbound
      have hn' : b < (n : ℝ) * ‖y.snd‖ := (div_lt_iff₀ (norm_pos_iff.mpr hy0)).mp hn
      nlinarith [norm_nonneg y.snd]
  refine ⟨D, hLD, hZD, ?_⟩
  have hiso : IsIso ((compactSupportCohomologyFunctor R T k).map (homOfLE hZD)) := by
    change IsIso (relativeSingularCohomologyRestriction R (D : Set T)ᶜ (Z : Set T)ᶜ
      (Set.compl_subset_compl.mpr hZD) k)
    exact radial_restriction_isIso R s hs hone hmul (D : Set T) (Z : Set T)
      D.isCompact.isClosed hZD hZ hout hescape k
  exact ConcreteCategory.bijective_of_isIso _

end AtiyahSinger
