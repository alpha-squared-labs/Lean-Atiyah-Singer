/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleInfinityContraction
public import AtiyahSinger.Topology.CohomologyEuler
public import AtiyahSinger.Topology.RelativeCohomologySequence
public import Mathlib.Topology.VectorBundle.Riemannian

/-!
# Compact-support Thom integration over a compact base

Public module ID: M1634.

C03, with S04 as its first supported-character consumer. The forward map is
the existing zero-section pushforward, namely the original Thom multiplication
followed by the original compact-support colimit injection. Its inverse is
therefore fixed by that map, rather than chosen as an unrelated equivalence.

The base is compact Hausdorff and the original continuous Riemannian bundle
has finite real rank. Compact disk bundles are cofinal among total-space
compact supports. Radial deformation identifies the punctured bundle with
the complement of each disk for the relative-cohomology comparison. This
upgrades the relative Thom isomorphism to the actual compact-support model.
Rank zero is included. No properness of the bundle projection is assumed.

Sources: Hatcher, Algebraic Topology, Corollary 4D.9, and the compact-support
construction on pp.243--245; SG III.12.1--12.2 motivates the fiber-integral notation.
ThomGysinComparison proves the signed rational Poincare-Gysin comparison
under its manifold hypotheses. The zero-support comparison is proved below;
the compact-support bijection composes it with the specified relative Thom map.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Limits Opposite TopologicalSpace
open scoped unitInterval

universe u

variable (R : Type) [CommRing R] (r : ℕ) {B : Type u}
  [TopologicalSpace B] [CompactSpace B] [T2Space B]
  (E : B → Type u) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin r)) E]
  (o : CohomologyOrientation R r E)

/-- Over a compact base with a continuous fiber metric, zero support computes compact supports.
The map is the original support-colimit injection, in every degree and over any commutative ring. -/
theorem compactSupportCohomologyClass_zeroSection_bijective (k : ℕ) :
    Function.Bijective (compactSupportCohomologyClass R
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (cohomologyZeroSectionSupport r E) k) := by
  /- Expand every nonzero fiber vector beyond a fixed disk, compare the two
  original relative cochain sequences, then place each compact-support
  representative and relation in one larger native metric disk. -/
  let F := EuclideanSpace ℝ (Fin r)
  let T := TotalSpace F E
  let Z := cohomologyZeroSectionSupport r E
  have hnorm : Continuous (fun v : T ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  have hdisk (a : ℝ) : IsCompact {v : T | ‖v.snd‖ ≤ a} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := F) (E := E) (K := Set.univ) isCompact_univ a
  -- A positive-radius complement includes into the same punctured bundle by a homotopy equivalence.
  have hcomparison (a : ℝ) (ha : 0 < a) (j : ℕ) :
      IsIso (relativeSingularCohomologyRestriction R
        ({v : T | ‖v.snd‖ ≤ a}ᶜ) ((Z : Set T)ᶜ)
        (by
          intro v hv hz
          change v.snd = 0 at hz
          change ¬ ‖v.snd‖ ≤ a at hv
          exact hv (by simpa [hz] using ha.le)) j) := by
    let A := ({v : T | ‖v.snd‖ ≤ a}ᶜ)
    let C := ((Z : Set T)ᶜ)
    have hAC : A ⊆ C := by
      intro v hv hz
      change v.snd = 0 at hz
      change ¬ ‖v.snd‖ ≤ a at hv
      exact hv (by simpa [hz] using ha.le)
    let i : C(A, C) := ⟨fun v ↦ ⟨v.val, hAC v.property⟩,
      continuous_subtype_val.subtype_mk _⟩
    have hne (v : C) : v.val.snd ≠ 0 := v.property
    let q (v : C) : ℝ := max 1 ((a + 1) / ‖v.val.snd‖)
    have hq (v : C) : 1 ≤ q v := le_max_left _ _
    have hqCont : Continuous q := continuous_const.max
      (continuous_const.div (hnorm.comp continuous_subtype_val)
        (fun v ↦ norm_ne_zero_iff.mpr (hne v)))
    have hfar (v : C) : a < ‖q v • v.val.snd‖ := by
      rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one (hq v))]
      have hlarge : a + 1 ≤ q v * ‖v.val.snd‖ :=
        (div_le_iff₀ (norm_pos_iff.mpr (hne v))).mp (le_max_right _ _)
      exact (lt_add_one a).trans_le hlarge
    let g : C(C, A) :=
      ⟨fun v ↦ ⟨⟨v.val.proj, q v • v.val.snd⟩, not_le.mpr (hfar v)⟩,
        ((continuous_bundleFiberScale F E).comp
          (hqCont.prodMk continuous_subtype_val)).subtype_mk _⟩
    let scale (t : unitInterval) (v : C) : ℝ :=
      1 + (1 - (t : ℝ)) * (q v - 1)
    have hscale (t : unitInterval) (v : C) : 1 ≤ scale t v := by
      exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr t.property.2)
        (sub_nonneg.mpr (hq v)))
    have hscaleCont : Continuous (fun p : unitInterval × C ↦ scale p.1 p.2) := by
      dsimp only [scale]
      fun_prop
    have hgi : (g.comp i).Homotopic (ContinuousMap.id A) := by
      refine ⟨{ toFun p := ⟨⟨p.2.val.proj, scale p.1 (i p.2) • p.2.val.snd⟩, ?_⟩
                continuous_toFun := ?_
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · change ¬ ‖scale p.1 (i p.2) • p.2.val.snd‖ ≤ a
        apply not_le.mpr
        rw [norm_smul, Real.norm_of_nonneg (le_trans zero_le_one (hscale p.1 (i p.2)))]
        exact (not_le.mp (show ¬ ‖p.2.val.snd‖ ≤ a from p.2.property)).trans_le
          (le_mul_of_one_le_left (norm_nonneg _) (hscale p.1 (i p.2)))
      · exact ((continuous_bundleFiberScale F E).comp
          ((hscaleCont.comp (continuous_fst.prodMk (i.continuous.comp continuous_snd))).prodMk
            (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      · intro v
        apply Subtype.ext
        simp [scale, g, i]
      · rintro ⟨⟨x, v⟩, hv⟩
        apply Subtype.ext
        simp [scale]
    have hig : (i.comp g).Homotopic (ContinuousMap.id C) := by
      refine ⟨{ toFun p := ⟨⟨p.2.val.proj, scale p.1 p.2 • p.2.val.snd⟩, ?_⟩
                continuous_toFun := ?_
                map_zero_left := ?_
                map_one_left := ?_ }⟩
      · exact smul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one (hscale p.1 p.2)))
          (hne p.2)
      · exact ((continuous_bundleFiberScale F E).comp
          (hscaleCont.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
      · intro v
        apply Subtype.ext
        simp [scale, g, i]
      · rintro ⟨⟨x, v⟩, hv⟩
        apply Subtype.ext
        simp [scale]
    -- Compare the actual pair through its unchanged ambient map and the complement homotopy.
    have hi (n : ℕ) : IsIso (singularCohomologyPullback R i n) :=
      isIso_singularCohomologyPullback_of_homotopyInverse R i g hgi hig n
    have hid (n : ℕ) :
        IsIso (singularCohomologyPullback R (ContinuousMap.id T) n) := by
      change IsIso ((singularCohomologyFunctor R n).map (𝟙 (Opposite.op (TopCat.of T))))
      infer_instance
    change IsIso (relativeSingularCohomologyPullback R (ContinuousMap.id T)
      (fun v hv ↦ hAC hv) j)
    exact isIso_relativeSingularCohomologyPullback_of_absolute R (ContinuousMap.id T)
      (fun v hv ↦ hAC hv) hid hi j
  -- Every compact control is contained in one of these same native metric disks.
  let H := compactSupportCohomologyFunctor R T k
  have hlarger (K : Compacts T) : ∃ (D : Compacts T) (hKD : K ≤ D) (hZD : Z ≤ D),
      Function.Bijective (H.map (homOfLE hZD)) := by
    obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
    let a : ℝ := max b 1
    have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    let D : Compacts T := ⟨{v | ‖v.snd‖ ≤ a}, hdisk a⟩
    have hKD : K ≤ D := fun v hv ↦ (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
    have hZD : Z ≤ D := by
      intro v hv
      change v.snd = 0 at hv
      change ‖v.snd‖ ≤ a
      simpa [hv] using ha.le
    refine ⟨D, hKD, hZD, ?_⟩
    have : IsIso (H.map (homOfLE hZD)) := hcomparison a ha k
    exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  constructor
  · intro x y hxy
    obtain ⟨K, hx, hy, heq⟩ :=
      (compactSupportCohomologyClass_eq_iff R T x y).mp hxy
    obtain ⟨D, hKD, hZD, hD⟩ := hlarger K
    apply hD.injective
    have h := congrArg (H.map (homOfLE hKD)) heq
    change (H.map (homOfLE hx) ≫ H.map (homOfLE hKD)) x =
      (H.map (homOfLE hy) ≫ H.map (homOfLE hKD)) y at h
    rw [← Functor.map_comp] at h
    exact h
  · intro x
    obtain ⟨K, y, hy⟩ := compactSupportCohomology_exists_representative R T k x
    obtain ⟨D, hKD, hZD, hD⟩ := hlarger K
    obtain ⟨z, hz⟩ := hD.surjective (H.map (homOfLE hKD) y)
    refine ⟨z, ?_⟩
    calc
      compactSupportCohomologyClass R T Z k z =
          compactSupportCohomologyClass R T D k (H.map (homOfLE hZD) z) :=
        (congrArg (fun f ↦ f z) (colimit.w H (homOfLE hZD))).symm
      _ = compactSupportCohomologyClass R T D k (H.map (homOfLE hKD) y) :=
        congrArg (compactSupportCohomologyClass R T D k) hz
      _ = compactSupportCohomologyClass R T K k y :=
        congrArg (fun f ↦ f y) (colimit.w H (homOfLE hKD))
      _ = x := hy

/-- The original zero-section Thom map is bijective in total compact-support cohomology. -/
theorem cohomologyZeroSectionPushforward_bijective (p : ℕ) :
    Function.Bijective (cohomologyZeroSectionPushforward R r E o p) := by
  -- Compact metric disks and radial deformation identify the original support injection.
  have hsupport := compactSupportCohomologyClass_zeroSection_bijective R r E (p + r)
  -- Compose with the same oriented Thom multiplication used in the pushforward definition.
  exact hsupport.comp (cohomologyThomMap_bijective R r E o p)

/-- The compact-support Thom equivalence retains the existing zero-section map. -/
def compactBaseCohomologyThomEquiv (p : ℕ) :
    singularCohomology R B p ≃ₗ[R]
      compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) :=
  LinearEquiv.ofBijective (cohomologyZeroSectionPushforward R r E o p)
    (cohomologyZeroSectionPushforward_bijective R r E o p)

/-- Fiber integration is the inverse of the actual compact-support Thom multiplication. -/
def compactSupportCohomologyFiberIntegral (p : ℕ) :
    compactSupportCohomology R (TotalSpace (EuclideanSpace ℝ (Fin r)) E) (p + r) →ₗ[R]
      singularCohomology R B p :=
  (compactBaseCohomologyThomEquiv R r E o p).symm.toLinearMap

end AtiyahSinger
