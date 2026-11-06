/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.Pseudolocal

/-!
# Local Sobolev regularity of tempered distributions

Public module ID: M0789.

The usual H^s_loc condition, tested by compact smooth cutoffs in an
open set. The ambient distribution is tempered; the predicate is local and imposes
no global H^s bound. Its relation to smoothness supplies the localization step in
SG III.4.5 and III.5.2(i). General distributions on an open set remain separate.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff Manifold SchwartzMap Topology

variable {n r : ℕ}

/-- The standard local L² Sobolev condition, using all real compact smooth cutoffs in U. -/
def MemSobolevOn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) (s : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
    tsupport χ ⊆ U →
      (TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun x ↦ (χ x : ℂ)) u).MemSobolev s 2

/-- Local Sobolev regularity restricts to smaller sets. -/
theorem MemSobolevOn.mono
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))} {s : ℝ}
    {U V : Set (EuclideanSpace ℝ (Fin n))} (hu : MemSobolevOn u s U)
    (hVU : V ⊆ U) : MemSobolevOn u s V := by
  /- Every admitted cutoff in V is also admitted in U. The same global cutoff
  distribution and the same Sobolev order occur on both sides; no extension is needed. -/
  intro χ hχ hcχ hχV
  exact hu χ hχ hcχ (hχV.trans hVU)

/-- A global H^s distribution is locally H^s on every set. -/
theorem memSobolevOn_of_memSobolev
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) (s : ℝ)
    (hu : u.MemSobolev s 2) (U : Set (EuclideanSpace ℝ (Fin n))) :
    MemSobolevOn u s U := by
  /- Realize u in its H^s Bessel coordinates. The existing sobolevCutoffCLM
  multiplies its distribution by each compact smooth cutoff and remains in H^s.
  Apply the Bessel characterization of MemSobolev to this actual multiplier identity. -/
  intro χ hχ hcχ _
  obtain ⟨f, rfl⟩ := (memSobolev_iff_exists_besselRealization s u).mp hu
  apply (memSobolev_iff_exists_besselRealization s _).mpr
  exact ⟨sobolevCutoffCLM s χ hχ hcχ f,
    besselRealization_sobolevCutoffCLM s χ hχ hcχ f⟩

/-- Lowering the real Sobolev order preserves local membership. -/
theorem MemSobolevOn.of_le
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))} {s t : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : MemSobolevOn u s U)
    (hts : t ≤ s) : MemSobolevOn u t U := by
  /- Apply the natural H^s to H^t inclusion to every cutoff distribution.
  Its Bessel intertwining identity preserves the distribution, not its L² coordinates. -/
  intro χ hχ hcχ hχU
  exact (hu χ hχ hcχ hχU).mono hts

/-- The sum of two locally H^s distributions is locally H^s. -/
theorem MemSobolevOn.add
    {u v : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))} {s : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : MemSobolevOn u s U) (hv : MemSobolevOn v s U) : MemSobolevOn (u + v) s U := by
  /- Cutoff multiplication is complex-linear. Add the two H^s Bessel coordinates
  for each cutoff and use linearity of the Bessel realization. -/
  intro χ hχ hcχ hχU
  -- The multiplier acts on the distribution itself, before taking Sobolev membership.
  rw [map_add]
  exact (hu χ hχ hcχ hχU).add (hv χ hχ hcχ hχU)

/-- A constant complex scalar preserves local H^s regularity. -/
theorem MemSobolevOn.smul
    {u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))} {s : ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : MemSobolevOn u s U)
    (c : ℂ) : MemSobolevOn (c • u) s U := by
  /- Scalar multiplication commutes with cutoff multiplication and with J^(-s).
  Multiply each existing H^s coordinate by c; no inverse or nonzero assumption is needed. -/
  intro χ hχ hcχ hχU
  rw [map_smul]
  exact (hu χ hχ hcχ hχU).smul c

/-- Local membership can be checked by one cutoff equal to one near each point. -/
theorem memSobolevOn_iff_exists_cutoff
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) (s : ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) :
    MemSobolevOn u s U ↔ ∀ x ∈ U,
      ∃ χ : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
        tsupport χ ⊆ U ∧ x ∈ interior {y | χ y = 1} ∧
          (TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
            (fun y ↦ (χ y : ℂ)) u).MemSobolev s 2 := by
  /- Forward: choose a smooth bump with compact support in U, equal to one near x.
  Reverse: cover the compact support of any test cutoff by finitely many of these
  neighborhoods. A subordinate smooth partition splits that cutoff into finitely
  many factors supported where the respective χ is one. Multiplication by each
  factor is bounded in H^s; add the resulting cutoff distributions. No uniform
  bound over all points of a noncompact U is asserted. -/
  classical
  let V := EuclideanSpace ℝ (Fin n)
  let H := EuclideanSpace ℂ (Fin r)
  constructor
  · intro hu x hx
    -- A closed ball inside U supplies a bump that is one on a smaller open ball.
    obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
    let χ : ContDiffBump x :=
      { rIn := d / 2
        rOut := d
        rIn_pos := half_pos hd
        rIn_lt_rOut := half_lt_self hd }
    have hχU : tsupport χ ⊆ U := by rw [χ.tsupport_eq]; exact hdU
    have hone : x ∈ interior {y | χ y = 1} := by
      apply mem_interior_iff_mem_nhds.mpr
      apply Filter.mem_of_superset (Metric.ball_mem_nhds x χ.rIn_pos)
      intro y hy
      exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
    exact ⟨χ, χ.contDiff, χ.hasCompactSupport, hχU, hone,
      hu χ χ.contDiff χ.hasCompactSupport hχU⟩
  · intro hlocal ψ hψ hcψ hψU
    choose χ hχ hcχ hχU hxχ hχsob using fun x : U ↦ hlocal x x.property
    let W (i : U) : Set V := interior {y | χ i y = 1}
    have hcover : tsupport ψ ⊆ ⋃ i : U, W i := by
      intro y hy
      exact Set.mem_iUnion.mpr ⟨⟨y, hψU hy⟩, hxχ ⟨y, hψU hy⟩⟩
    -- Local finiteness leaves only finitely many partition functions meeting this cutoff.
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, V) (isClosed_tsupport ψ) W (fun _ ↦ isOpen_interior) hcover
    have hfinite : {i : U | (Function.support (ρ i) ∩ tsupport ψ).Nonempty}.Finite :=
      ρ.locallyFinite.finite_nonempty_inter_compact hcψ
    let S : Finset U := hfinite.toFinset
    let θ (i : U) (y : V) : ℝ := ρ i y * ψ y
    have hθ (i : U) : ContDiff ℝ ∞ (θ i) := (ρ i).contMDiff.contDiff.mul hψ
    have hcθ (i : U) : HasCompactSupport (θ i) := hcψ.mul_left
    have hθW (i : U) : tsupport (θ i) ⊆ W i :=
      (tsupport_mul_subset_left : tsupport (θ i) ⊆ tsupport (ρ i)).trans (hρ i)
    have hgrowth (i : U) : (fun y ↦ (θ i y : ℂ)).HasTemperateGrowth :=
      ((hcθ i).comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp (hθ i))
    have hdecomp (y : V) : ψ y = ∑ i ∈ S, θ i y := by
      by_cases hy : ψ y = 0
      · simp [θ, hy]
      have hyψ := subset_tsupport ψ hy
      have hsum : ∑ i ∈ S, ρ i y = 1 := by
        apply ρ.sum_finsupport' y hyψ
        intro i hi
        have hiρ : y ∈ Function.support (ρ i) := by
          simpa only [SmoothPartitionOfUnity.mem_finsupport, Function.mem_support] using hi
        exact hfinite.mem_toFinset.mpr ⟨y, hiρ, hyψ⟩
      simp only [θ, ← Finset.sum_mul, hsum, one_mul]
    have hterm (i : U) :
        (TemperedDistribution.smulLeftCLM H (fun y ↦ (θ i y : ℂ)) u).MemSobolev s 2 := by
      have hbase := memSobolevOn_of_memSobolev _ s (hχsob i) Set.univ
        (θ i) (hθ i) (hcθ i) (Set.subset_univ _)
      have hi : (fun y ↦ (χ i y : ℂ)).HasTemperateGrowth :=
        ((hcχ i).comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
          (Complex.ofRealCLM.contDiff.comp (hχ i))
      rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply hi (hgrowth i)] at hbase
      have hfactor : (fun y ↦ (χ i y : ℂ)) * (fun y ↦ (θ i y : ℂ)) =
          (fun y ↦ (θ i y : ℂ)) := by
        funext y
        by_cases hy : θ i y = 0
        · simp [hy]
        have hyone : χ i y = 1 :=
          interior_subset (s := {y | χ i y = 1}) (hθW i (subset_tsupport (θ i) hy))
        simp [hyone]
      rwa [hfactor] at hbase
    -- The same finite sum of Bessel coordinates realizes the original cutoff distribution.
    have hsum : (∑ i ∈ S,
        TemperedDistribution.smulLeftCLM H (fun y ↦ (θ i y : ℂ)) u).MemSobolev s 2 := by
      induction S using Finset.induction_on with
      | empty =>
        simp only [Finset.sum_empty]
        apply (memSobolev_iff_exists_besselRealization s _).mpr
        exact ⟨0, map_zero _⟩
      | @insert i S hi ih =>
        rw [Finset.sum_insert hi]
        exact (hterm i).add ih
    have hdist : TemperedDistribution.smulLeftCLM H (fun y ↦ (ψ y : ℂ)) u =
        ∑ i ∈ S, TemperedDistribution.smulLeftCLM H (fun y ↦ (θ i y : ℂ)) u := by
      have hcomplex : (fun y ↦ (ψ y : ℂ)) = fun y ↦ ∑ i ∈ S, (θ i y : ℂ) := by
        funext y
        rw [hdecomp y, Complex.ofReal_sum]
      rw [hcomplex, TemperedDistribution.smulLeftCLM_sum (fun i _ ↦ hgrowth i)]
      simp only [sum_apply]
    rwa [hdist]

/-- For a distribution supported in a compact subset of U, local H^s is global H^s. -/
theorem memSobolev_iff_memSobolevOn_of_isSupportedIn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r))) (s : ℝ)
    (U K : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) (hK : IsCompact K)
    (hKU : K ⊆ U) (hu : IsSupportedIn u K) :
    u.MemSobolev s 2 ↔ MemSobolevOn u s U := by
  /- Only the reverse implication needs support information. Choose a compact
  smooth χ supported in U and equal to one near K. The support hypothesis shows
  χu=u on compact tests. Approximate arbitrary Schwartz tests by compact smooth
  cutoffs in the Schwartz topology to obtain equality in S'. Then apply local
  membership to χ. Without compact support, local H^s on all of R^n need not be H^s. -/
  constructor
  · intro hs
    exact memSobolevOn_of_memSobolev u s hs U
  · intro hlocal
    -- Choose a compact smooth plateau on a neighborhood of the fixed support K.
    obtain ⟨L, hL, hLc, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
    obtain ⟨χ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hK.isClosed hKL (n := (⊤ : ℕ∞))
    have hχ : ContDiff ℝ ∞ χ := χ.contMDiff.contDiff
    have hcχ : HasCompactSupport χ := HasCompactSupport.intro' hL hLc hzero
    have hsχ : tsupport χ ⊆ U := by
      apply Set.Subset.trans ?_ hLU
      apply closure_minimal ?_ hLc
      intro x hx
      by_contra hxL
      exact hx (hzero x hxL)
    have hg : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
      (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    let T := TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
      (fun x ↦ (χ x : ℂ)) u
    -- The support condition first identifies the two distributions on compact tests.
    have htest (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hφ : HasCompactSupport φ) :
        T φ = u φ := by
      let ψ := SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ
      have hcψ : HasCompactSupport ψ := by
        rw [show ⇑ψ = fun x ↦ (χ x : ℂ) • φ x from
          SchwartzMap.smulLeftCLM_apply hg φ]
        exact hφ.smul_left (f := fun x ↦ (χ x : ℂ))
      have hd : Disjoint (tsupport (φ - ψ)) K := by
        apply Set.disjoint_left.mpr
        intro x hx hxK
        apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hx
        have hnear : ∀ᶠ y in 𝓝 x, χ y = 1 := mem_nhdsSet_iff_forall.mp hone x hxK
        filter_upwards [hnear] with y hy
        change φ y - ψ y = 0
        rw [SchwartzMap.smulLeftCLM_apply_apply hg]
        simp only [hy, Complex.ofReal_one, one_smul, sub_self]
      have hpair := hu.apply_eq_zero (φ - ψ) (hφ.sub hcψ) hd
      rw [map_sub] at hpair
      exact (sub_eq_zero.mp hpair).symm
    -- Full Schwartz-topology density now extends the compact-test identity to S'.
    have hT : T = u := by
      apply DFunLike.ext
      intro φ
      have hc : IsClosed {φ | T φ = u φ} := isClosed_eq T.continuous u.continuous
      exact closure_minimal htest hc (dense_hasCompactSupport_schwartz n φ)
    rw [← hT]
    exact hlocal χ hχ hcχ hsχ

/-- Smoothness is equivalent to local Sobolev regularity of every real order. -/
theorem isSmoothDistributionOn_iff_forall_memSobolevOn
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U) :
    IsSmoothDistributionOn u U ↔ ∀ s : ℝ, MemSobolevOn u s U := by
  /- Forward: every compact cutoff of a local smooth representative is smooth
  and compactly supported, hence Schwartz and in every H^s. Reverse: each cutoff
  distribution lies in every H^s, so Sobolev embedding gives a smooth representative.
  Choose cutoffs equal to one near each point. Their continuous representatives
  agree on overlaps by uniqueness as distributions and therefore glue on U.
  This does not claim a global H^s bound for u or its uncut smooth representative. -/
  constructor
  · intro hu s χ hχ hcχ hχU
    -- A compact cutoff of this same local representative is a Schwartz distribution.
    obtain ⟨v, hv⟩ :=
      (isSmoothDistributionOn_iff_schwartz_cutoffs u U hU).mp hu χ hχ hcχ hχU
    rw [hv]
    exact v.memSobolev
  · intro hlocal
    -- Construct smooth representatives on small balls, then use the proved local gluing theorem.
    apply (isSmoothDistributionOn_iff_disjoint_singularSupport u U hU).mpr
    apply Set.disjoint_left.mpr
    intro x hxU hxs
    obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
    let χ : ContDiffBump x :=
      { rIn := d / 2
        rOut := d
        rIn_pos := half_pos hd
        rIn_lt_rOut := half_lt_self hd }
    have hχU : tsupport χ ⊆ U := by
      rw [χ.tsupport_eq]
      exact hdU
    let w := TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
      (fun y ↦ (χ y : ℂ)) u
    have hw : ∀ s : ℝ, w.MemSobolev s 2 :=
      fun s ↦ hlocal s χ χ.contDiff χ.hasCompactSupport hχU
    obtain ⟨f, hf, hpair⟩ := isSmoothDistributionOn_of_forall_memSobolev w hw
    apply hxs
    refine ⟨Metric.ball x χ.rIn, Metric.isOpen_ball, Metric.mem_ball_self χ.rIn_pos,
      f, hf.mono (Set.subset_univ _), ?_⟩
    intro φ hφ hφball
    -- The bump is one on the test support, so its actual multiplier fixes the test.
    have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
      (χ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp χ.contDiff)
    have hmult : SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ = φ := by
      ext y
      rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
      by_cases hy : φ y = 0
      · simp [hy]
      have hyball := hφball (subset_tsupport φ hy)
      rw [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hyball)]
      simp
    calc
      u φ = w φ := by
        dsimp only [w]
        rw [TemperedDistribution.smulLeftCLM_apply_apply, hmult]
      _ = ∫ y, φ y • f y := hpair φ hφ (Set.subset_univ _)

end AtiyahSinger
