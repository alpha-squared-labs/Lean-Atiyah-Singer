/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleSphereCompactSupport
public import AtiyahSinger.Topology.BundleInfinityContraction

/-!
# Detection of compact supports in the original fiberwise sphere

Public module ID: M1593.

For the given Riemannian bundle over a compact Hausdorff manifold, positive
metric disks are cofinal compact supports. Their complements in the
original sphere are northern caps and retract onto its same infinity section.
Excision and the original relative cohomology sequence therefore identify the
support colimit with the relative sphere group. The actual retraction onto the
infinity section makes the latter inject into ordinary sphere cohomology.

Sources: SG III.13, fiberwise compactification; Hatcher, Algebraic Topology,
Sections 3.1--3.3, for excision, relative cohomology and compact supports.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Topology TopologicalSpace
open scoped Manifold ContDiff unitInterval

variable (r : ℕ) {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [FiniteDimensional ℝ EB]
  {B : Type*} [TopologicalSpace B] [ChartedSpace EB B]
  [IsManifold 𝓘(ℝ, EB) ∞ B] [T2Space B] [CompactSpace B]
  (V : B → Type*) [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) V)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) V]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) V]
  [ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin r)) V 𝓘(ℝ, EB)]
  [hMetric : IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ (EuclideanSpace ℝ (Fin r)) V]

attribute [local instance] t2Space_fiberBundleTotal orthogonalFrameTopology
  continuousSMul_orthogonalSphere

local notation "Rr" => EuclideanSpace ℝ (Fin r)
local notation "S" => SphereCompactification r V

/-- Cofinal metric supports have complements retracting onto the same sphere boundary. -/
theorem cofinal_isIso_sphereCompactificationComplementInclusion
    (R : Type) [CommRing R] (K : Compacts (TotalSpace Rr V)) :
    ∃ L : Compacts (TotalSpace Rr V), K ≤ L ∧ ∀ k : ℕ,
      IsIso (singularCohomologyPullback R (compactificationComplementInclusion
        (sphereCompactificationInclusion (EB := EB) r V) L) k) := by
  classical
  obtain ⟨g, hg, hmetric⟩ := hMetric.exists_contMDiff
  let : IsContinuousRiemannianBundle Rr V := ⟨⟨g, hg.continuous, hmetric⟩⟩
  let j := sphereCompactificationInclusion (EB := EB) r V
  have hj := isOpenEmbedding_sphereCompactificationInclusion (EB := EB) r V
  have hnorm : Continuous (fun v : TotalSpace Rr V ↦ ‖v.snd‖) :=
    Poincare.VectorBundle.continuous_fiber_norm
  obtain ⟨b, hb⟩ := K.isCompact.bddAbove_image hnorm.continuousOn
  let a : ℝ := max b 2
  have ha : 2 ≤ a := le_max_right _ _
  have ha0 : 0 ≤ a := by linarith
  have hda : 0 < a ^ 2 + 4 := by positivity
  have hdisk : IsCompact {v : TotalSpace Rr V | ‖v.snd‖ ≤ a} := by
    simpa using Poincare.VectorBundle.isCompact_disk_over
      (F := Rr) (E := V) (K := Set.univ) isCompact_univ a
  let L : Compacts (TotalSpace Rr V) := ⟨{v | ‖v.snd‖ ≤ a}, hdisk⟩
  refine ⟨L, ?_, ?_⟩
  · intro v hv
    exact (hb (Set.mem_image_of_mem _ hv)).trans (le_max_left _ _)
  intro k
  let A : Set S := (Set.range j)ᶜ
  let N : Set S := (openEmbeddingCompactImage j L : Set S)ᶜ
  let c : ℝ := (a ^ 2 - 4) / (a ^ 2 + 4)
  have hc0 : 0 ≤ c := div_nonneg (by nlinarith) hda.le
  have hc1 : c < 1 := (div_lt_one hda).mpr (by linarith)
  have hA (z : S) : z ∈ A ↔ z.val.2 = 1 := by
    dsimp only [A, j]
    rw [range_sphereCompactificationInclusion (EB := EB) r V]
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not]
  have hjheight (v : TotalSpace Rr V) :
      (j v).val.2 = (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4) := by
    let := continuousSMul_orthogonalFrame r V 𝓘(ℝ, EB)
    let atlas := smoothOrthogonalFrameAtlas r V 𝓘(ℝ, EB)
    let := associatedSphereChartedSpace atlas
    exact congrArg Prod.snd
      ((frameSphereStereographic_spec (EB := EB) r V).2.2.2.1 v)
  -- The original stereographic formula identifies these complements with northern caps.
  have hN (z : S) : z ∈ N ↔ c < z.val.2 := by
    constructor
    · intro hz
      by_cases ht : z.val.2 = 1
      · rwa [ht]
      have hrange : z ∈ Set.range j := by
        rw [show Set.range j = {z : S | z.val.2 ≠ 1} from
          range_sphereCompactificationInclusion (EB := EB) r V]
        exact ht
      obtain ⟨v, rfl⟩ := hrange
      have hav : a < ‖v.snd‖ := lt_of_not_ge (fun hv ↦ hz ⟨v, hv, rfl⟩)
      rw [hjheight]
      have hdv : 0 < ‖v.snd‖ ^ 2 + 4 := by positivity
      apply (div_lt_div_iff₀ hda hdv).mpr
      nlinarith [sq_nonneg (‖v.snd‖ - a)]
    · intro hz himage
      obtain ⟨v, hv, rfl⟩ := himage
      rw [hjheight] at hz
      have hv' : ‖v.snd‖ ≤ a := hv
      have hdv : 0 < ‖v.snd‖ ^ 2 + 4 := by positivity
      have hbound : (‖v.snd‖ ^ 2 - 4) / (‖v.snd‖ ^ 2 + 4) ≤ c := by
        apply (div_le_div_iff₀ hdv hda).mpr
        nlinarith [sq_nonneg (a - ‖v.snd‖), norm_nonneg v.snd]
      exact (not_lt_of_ge hbound) hz
  let north := sphereCompactificationInfinity r V
  let πS := sphereCompactificationProjection r V
  have hnorth (z : S) (ht : z.val.2 = 1) : north (πS z) = z := by
    have heq : ‖z.val.1.snd‖ ^ 2 + z.val.2 ^ 2 = 1 := z.property
    rw [ht] at heq
    have hv : z.val.1.snd = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg z.val.1.snd]
    apply Subtype.ext
    apply Prod.ext
    · rcases z with ⟨⟨⟨x, v⟩, t⟩, hz⟩
      change (⟨x, 0⟩ : TotalSpace Rr V) = ⟨x, v⟩
      change v = 0 at hv
      rw [hv]
    · exact ht.symm
  let i : C(A, N) := compactificationComplementInclusion j L
  let ret : C(N, A) := ⟨fun z ↦ ⟨north (πS z.val), (hA _).mpr rfl⟩,
    (north.continuous.comp (πS.continuous.comp continuous_subtype_val)).subtype_mk _⟩
  have hret : ret.comp i = ContinuousMap.id A := by
    apply ContinuousMap.ext
    intro z
    exact Subtype.ext (hnorth z.val ((hA z.val).mp z.property))
  -- Shrink the original horizontal vector and reconstruct the positive sphere height.
  -- On a northern cap this keeps the height nondecreasing, including at the north section.
  let α (t : I) : ℝ := 1 - (t : ℝ)
  let q (z : N) : ℝ := ‖z.val.val.1.snd‖ ^ 2
  have hq (z : N) : 0 ≤ q z := sq_nonneg _
  have hα (t : I) : 0 ≤ α t ∧ α t ^ 2 ≤ 1 := by
    dsimp only [α]
    constructor <;> nlinarith [t.property.1, t.property.2]
  have hheight (p : I × N) :
      p.2.val.val.2 ≤ Real.sqrt (1 - α p.1 ^ 2 * q p.2) := by
    have hz : 0 ≤ p.2.val.val.2 := hc0.trans ((hN p.2.val).mp p.2.property).le
    have heq : q p.2 + p.2.val.val.2 ^ 2 = 1 := p.2.val.property
    have hprod : α p.1 ^ 2 * q p.2 ≤ q p.2 :=
      mul_le_of_le_one_left (hq p.2) (hα p.1).2
    have hsquare : p.2.val.val.2 ^ 2 ≤ 1 - α p.1 ^ 2 * q p.2 := by linarith
    exact (Real.sqrt_sq hz).symm.trans_le (Real.sqrt_le_sqrt hsquare)
  have hnonneg (p : I × N) : 0 ≤ 1 - α p.1 ^ 2 * q p.2 := by
    have heq : q p.2 + p.2.val.val.2 ^ 2 = 1 := p.2.val.property
    have hprod : α p.1 ^ 2 * q p.2 ≤ q p.2 :=
      mul_le_of_le_one_left (hq p.2) (hα p.1).2
    nlinarith [sq_nonneg p.2.val.val.2]
  let H : (ContinuousMap.id N).Homotopy (i.comp ret) :=
    { toFun := fun p ↦
        ⟨⟨((⟨p.2.val.val.1.proj, α p.1 • p.2.val.val.1.snd⟩ : TotalSpace Rr V),
          Real.sqrt (1 - α p.1 ^ 2 * q p.2)), by
          change ‖α p.1 • p.2.val.val.1.snd‖ ^ 2 +
            Real.sqrt (1 - α p.1 ^ 2 * q p.2) ^ 2 = 1
          rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hnonneg p)]
          dsimp only [q]
          ring⟩,
          (hN _).mpr (((hN p.2.val).mp p.2.property).trans_le (hheight p))⟩
      continuous_toFun := by
        have hvector : Continuous (fun p : I × N ↦ p.2.val.val.1) :=
          continuous_fst.comp (continuous_subtype_val.comp
            (continuous_subtype_val.comp continuous_snd))
        have hscale : Continuous (fun p : I × N ↦ α p.1) :=
          continuous_const.sub (continuous_subtype_val.comp continuous_fst)
        have hqcont : Continuous (fun p : I × N ↦ q p.2) :=
          (hnorm.comp hvector).pow 2
        exact (((continuous_bundleFiberScale Rr V).comp (hscale.prodMk hvector)).prodMk
          (Real.continuous_sqrt.comp (continuous_const.sub
            ((hscale.pow 2).mul hqcont)))).subtype_mk _ |>.subtype_mk _
      map_zero_left := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · change (⟨z.val.val.1.proj, (1 - (0 : ℝ)) • z.val.val.1.snd⟩ :
            TotalSpace Rr V) = z.val.val.1
          simp
        · change Real.sqrt (1 - (1 - (0 : ℝ)) ^ 2 * q z) = z.val.val.2
          have heq : q z + z.val.val.2 ^ 2 = 1 := z.val.property
          have hz : 0 ≤ z.val.val.2 := hc0.trans ((hN z.val).mp z.property).le
          simp only [sub_zero, one_pow, one_mul]
          rw [show 1 - q z = z.val.val.2 ^ 2 by linarith, Real.sqrt_sq hz]
      map_one_left := by
        intro z
        apply Subtype.ext
        apply Subtype.ext
        apply Prod.ext
        · change (⟨z.val.val.1.proj, (1 - (1 : ℝ)) • z.val.val.1.snd⟩ :
            TotalSpace Rr V) = ⟨z.val.val.1.proj, 0⟩
          simp
        · change Real.sqrt (1 - (1 - (1 : ℝ)) ^ 2 * q z) = 1
          norm_num }
  exact isIso_singularCohomologyPullback_of_homotopyInverse R i ret
    (hret ▸ ContinuousMap.Homotopic.refl (ContinuousMap.id A)) ⟨H.symm⟩ k

/-- The original support colimit is the relative group of the specified fiberwise sphere. -/
theorem compactSupportCohomologyToSphere_bijective (R : Type) [CommRing R] (k : ℕ) :
    Function.Bijective (compactSupportCohomologyToCompactification R
      (sphereCompactificationInclusion (EB := EB) r V)
      (isOpenEmbedding_sphereCompactificationInclusion (EB := EB) r V) k) := by
  exact compactSupportCohomologyToCompactification_bijective R
    (sphereCompactificationInclusion (EB := EB) r V)
    (isOpenEmbedding_sphereCompactificationInclusion (EB := EB) r V)
    (cofinal_isIso_sphereCompactificationComplementInclusion (EB := EB) r V R) k

/-- Ordinary cohomology of this sphere detects the original compact-support class. -/
theorem compactSupportCohomologyToSphere_toOrdinary_injective
    (R : Type) [CommRing R] (k : ℕ) :
    Function.Injective (fun a : compactSupportCohomology R (TotalSpace Rr V) k ↦
      relativeSingularCohomologyToOrdinary R
        ((Set.range (sphereCompactificationInclusion (EB := EB) r V))ᶜ) k
        (compactSupportCohomologyToCompactification R
          (sphereCompactificationInclusion (EB := EB) r V)
          (isOpenEmbedding_sphereCompactificationInclusion (EB := EB) r V) k a)) := by
  exact (relativeSingularCohomologyToOrdinary_sphere_injective (EB := EB) r V R k).comp
    (compactSupportCohomologyToSphere_bijective (EB := EB) r V R k).injective

end AtiyahSinger
