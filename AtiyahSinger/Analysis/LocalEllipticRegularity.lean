/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.LocalizedParametrix

/-!
# Local elliptic regularity in the existing Sobolev realization

Public module ID: M0786.

SG III.4.5 and the local assertion of III.5.2(i), with the real-order
Sobolev refinement. Taylor III.1.4 states the singular-support equality for properly
supported operators on all distributions. Here the actual quantization acts on a
global H^s input, and ellipticity is required only on the indicated open set.
The equality of singular supports is consequently restricted to that set.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- A spatially compact symbol preserves local Sobolev regularity with its order shift. -/
theorem memSobolevOn_quantizeSobolev
    (m s t : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (hu : MemSobolevOn (besselRealization n r s f) t U) :
    MemSobolevOn
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) (t - m) U := by
  /- Fix a compact cutoff χ in U and choose ρ supported in U, equal to one near
  tsupport χ. The distribution ρu is globally H^t by hu. Quantize at that order
  and use compatibility with its H^s realization to see χPρu lies in H^(t-m).
  The separated term χP(1-ρ)u has a compact smoothing symbol and belongs to every
  H^l by the off-diagonal identity. Adding both parts proves the required cutoff
  membership. This argument uses no ellipticity and no inequality between s and t. -/
  let V := EuclideanSpace ℝ (Fin n)
  let Hq := EuclideanSpace ℂ (Fin q)
  let P := quantizeSobolev m s p hp hc
  let B := besselRealization n q (s - m)
  -- It suffices to control one cutoff equal to one near each point of the open set.
  apply (memSobolevOn_iff_exists_cutoff _ (t - m) U hU).mpr
  intro x hxU
  obtain ⟨d, hd, hdU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hxU)
  let ρ : ContDiffBump x :=
    { rIn := d / 2
      rOut := d
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let χ : ContDiffBump x :=
    { rIn := d / 8
      rOut := d / 4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  have hρU : tsupport (ρ : V → ℝ) ⊆ U := by
    rw [ρ.tsupport_eq]
    exact hdU
  have hχU : tsupport (χ : V → ℝ) ⊆ U := by
    rw [χ.tsupport_eq]
    apply Set.Subset.trans (Metric.closedBall_subset_closedBall (by dsimp [χ]; linarith)) hdU
  have hχone : x ∈ interior {y | χ y = 1} := by
    apply mem_interior_iff_mem_nhds.mpr
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x χ.rIn_pos)
    intro y hy
    exact χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)
  have hone : tsupport (χ : V → ℝ) ⊆ interior {y | ρ y = 1} := by
    apply Set.Subset.trans _ (interior_maximal
      (fun y hy ↦ ρ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy)) Metric.isOpen_ball)
    intro y hy
    rw [χ.tsupport_eq] at hy
    change dist y x ≤ d / 4 at hy
    change dist y x < d / 2
    linarith
  let Sρ := sobolevCutoffCLM (r := r) s ρ ρ.contDiff ρ.hasCompactSupport
  let Mχ := TemperedDistribution.smulLeftCLM Hq (fun y ↦ (χ y : ℂ))
  -- The localized input has both H^s and H^t coordinates for the same distribution.
  obtain ⟨g, hg⟩ := (memSobolev_iff_exists_besselRealization t _).mp
    (hu ρ ρ.contDiff ρ.hasCompactSupport hρU)
  have hsame : besselRealization n r s (Sρ f) = besselRealization n r t g :=
    (besselRealization_sobolevCutoffCLM s ρ ρ.contDiff ρ.hasCompactSupport f).trans hg.symm
  have hP : B (P (Sρ f)) =
      besselRealization n q (t - m) (quantizeSobolev m t p hp hc g) :=
    quantizeSobolev_compatible m m s t p hp hp hc (Sρ f) g hsame
  have hlocalized : (Mχ (B (P (Sρ f)))).MemSobolev (t - m) 2 := by
    rw [hP]
    apply (memSobolev_iff_exists_besselRealization (t - m) _).mpr
    exact ⟨sobolevCutoffCLM (t - m) χ χ.contDiff χ.hasCompactSupport
      (quantizeSobolev m t p hp hc g),
      besselRealization_sobolevCutoffCLM (t - m) χ χ.contDiff χ.hasCompactSupport _⟩
  -- The separated contribution is smooth; a second compact cutoff converts it to global H^(t-m).
  have hseparated : IsSmoothDistributionOn (Mχ (B (P (f - Sρ f)))) Set.univ :=
    isSmoothDistributionOn_cutoff_quantizeSobolev_sub m s p hp hc
      χ ρ χ.contDiff χ.hasCompactSupport ρ.contDiff ρ.hasCompactSupport hone f
  have hregular := (isSmoothDistributionOn_iff_forall_memSobolevOn
    _ Set.univ isOpen_univ).mp hseparated (t - m)
  have hseparatedSobolev : (Mχ (B (P (f - Sρ f)))).MemSobolev (t - m) 2 := by
    have hρgrowth : (fun y ↦ (ρ y : ℂ)).HasTemperateGrowth :=
      (ρ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp ρ.contDiff)
    have hχgrowth : (fun y ↦ (χ y : ℂ)).HasTemperateGrowth :=
      (χ.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp χ.contDiff)
    have hmult : TemperedDistribution.smulLeftCLM Hq (fun y ↦ (ρ y : ℂ))
        (Mχ (B (P (f - Sρ f)))) = Mχ (B (P (f - Sρ f))) := by
      ext1 φ
      change B (P (f - Sρ f))
        (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ))
          (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (ρ y : ℂ)) φ)) =
        B (P (f - Sρ f)) (SchwartzMap.smulLeftCLM ℂ (fun y ↦ (χ y : ℂ)) φ)
      congr 1
      ext1 y
      simp only [SchwartzMap.smulLeftCLM_apply_apply hχgrowth,
        SchwartzMap.smulLeftCLM_apply_apply hρgrowth]
      by_cases hy : χ y = 0
      · simp [hy]
      · have hρy : ρ y = 1 := show y ∈ {y | ρ y = 1} from
          interior_subset (hone (subset_tsupport χ hy))
        simp [hρy]
    have h := hregular ρ ρ.contDiff ρ.hasCompactSupport (Set.subset_univ _)
    change (TemperedDistribution.smulLeftCLM Hq (fun y ↦ (ρ y : ℂ))
      (Mχ (B (P (f - Sρ f))))).MemSobolev (t - m) 2 at h
    rw [hmult] at h
    exact h
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, hχU, hχone, ?_⟩
  have hdecompose : Mχ (B (P f)) =
      Mχ (B (P (f - Sρ f))) + Mχ (B (P (Sρ f))) := by
    simp only [map_sub]
    abel
  rw [show TemperedDistribution.smulLeftCLM Hq (fun y ↦ (χ y : ℂ)) (B (P f)) =
    Mχ (B (P (f - Sρ f))) + Mχ (B (P (Sρ f))) from hdecompose]
  exact hseparatedSobolev.add hlocalized

/-- Local ellipticity recovers the full m derivatives from the local regularity of Pu. -/
theorem memSobolevOn_of_quantizeSobolev_of_isEllipticFullSymbol
    (m s t : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p)
    (hPu : MemSobolevOn
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) t U) :
    MemSobolevOn (besselRealization n r s f) (t + m) U := by
  /- For each requested compact cutoff χ in U, use its localized left parametrix
  to obtain QPu=χu+Ru as actual distributions. The local mapping theorem gives
  QPu in local H^(t+m), while Ru is smooth. Thus χu has that same local order.
  Its support lies in the compact set tsupport χ inside U, so the compact-support
  criterion upgrades this to the global Sobolev membership required by MemSobolevOn.
  Arbitrary real m is allowed; when m is negative, this is a loss of regularity
  relative to Pu, with precisely the inverse operator's order. -/
  -- For an arbitrary compact cutoff, use its one fixed actual left parametrix.
  intro χ hχ hcχ hχU
  obtain ⟨b, c, hb, hcb, _, hcs, hcc, hid⟩ :=
    exists_localized_left_parametrix m p hp hc U hU he χ hχ hcχ hχU
  let Mχ := TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
    (fun x ↦ (χ x : ℂ))
  have hQ := memSobolevOn_quantizeSobolev (-m) (s - m) t b hb hcb
    (quantizeSobolev m s p hp hc f) U hU hPu
  have horder : t - (-m) = t + m := by ring
  rw [horder] at hQ
  have hR := (isSmoothDistributionOn_iff_forall_memSobolevOn _ U hU).mp
    ((isSmoothDistributionOn_quantizeSobolev_of_isSmoothingSymbol 0 s c hcs hcc f).mono
      hU (Set.subset_univ U)) (t + m)
  -- The exact distribution identity recovers the same cutoff of u, with a smooth error.
  have hlocal : MemSobolevOn (Mχ (besselRealization n r s f)) (t + m) U := by
    have h := hQ.add (hR.smul (-1))
    rw [besselRealization_quantizeSobolev_left_parametrix m s p b c hp hb hcs
      hc hcb hcc χ hχ hcχ hid f] at h
    simpa only [neg_one_smul, add_neg_cancel_right] using h
  have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hsupported : IsSupportedIn (Mχ (besselRealization n r s f)) (tsupport χ) := by
    apply (isSupportedIn_iff_compact_tests _ _ (isClosed_tsupport χ)).mpr
    intro φ _ hdisj
    have hz : SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ = 0 := by
      ext x
      rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
      by_cases hx : x ∈ tsupport φ
      · have hχx : χ x = 0 := image_eq_zero_of_notMem_tsupport
          (fun h ↦ Set.disjoint_left.mp hdisj hx h)
        simp [hχx]
      · simp [image_eq_zero_of_notMem_tsupport hx]
    change (besselRealization n r s f)
      (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) = 0
    rw [hz, map_zero]
  -- Compact support inside U upgrades this local membership to the required global cutoff norm.
  exact (memSobolev_iff_memSobolevOn_of_isSupportedIn _ (t + m) U (tsupport χ)
    hU hcχ hχU hsupported).mpr hlocal

/-- On the elliptic set, local Sobolev regularity is equivalent with the correct order shift. -/
theorem memSobolevOn_quantizeSobolev_iff_of_isEllipticFullSymbol
    (m s t : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p) :
    MemSobolevOn
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) (t - m) U ↔
        MemSobolevOn (besselRealization n r s f) t U := by
  /- Apply inverse regularity with output order t-m and simplify (t-m)+m=t.
  The reverse implication is the local mapping theorem at order t. The ambient
  realization still starts at s; it is not silently replaced by a global H^t input. -/
  constructor
  · intro hPu
    have h := memSobolevOn_of_quantizeSobolev_of_isEllipticFullSymbol
      m s (t - m) p hp hc f U hU he hPu
    simpa only [sub_add_cancel] using h
  · exact memSobolevOn_quantizeSobolev m s t p hp hc f U hU

/-- SG 4.5: an H^s distribution is smooth wherever its elliptic image is smooth. -/
theorem isSmoothDistributionOn_of_quantizeSobolev_of_isEllipticFullSymbol
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p)
    (hPu : IsSmoothDistributionOn
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) U) :
    IsSmoothDistributionOn (besselRealization n r s f) U := by
  /- Smoothness of Pu supplies every local Sobolev order. For any desired t,
  apply inverse regularity to its order t-m. The resulting all-order local
  membership makes u smooth on U. Equivalently, SG uses χu=QPu-Ru and the
  pseudolocal property of Q. No growth bound on the local smooth representative is imposed. -/
  apply (isSmoothDistributionOn_iff_forall_memSobolevOn _ U hU).mpr
  intro t
  have hlocal := (isSmoothDistributionOn_iff_forall_memSobolevOn _ U hU).mp hPu (t - m)
  have h := memSobolevOn_of_quantizeSobolev_of_isEllipticFullSymbol
    m s (t - m) p hp hc f U hU he hlocal
  simpa only [sub_add_cancel] using h

/-- The singular supports agree inside the elliptic open set. -/
theorem singularSupport_quantizeSobolev_inter_eq_of_isEllipticFullSymbol
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p) :
    singularSupport
      (besselRealization n q (s - m) (quantizeSobolev m s p hp hc f)) ∩ U =
        singularSupport (besselRealization n r s f) ∩ U := by
  /- Pseudolocality gives one inclusion on all of R^n. For the other, intersect
  an output smooth neighborhood with U. The compact-local ellipticity condition
  restricts to that open intersection, so local elliptic regularity gives input
  smoothness there. Taking complements inside U proves equality. There is no
  conclusion outside U, where a compactly supported symbol can vanish identically. -/
  apply Set.Subset.antisymm
  · exact Set.inter_subset_inter_left U (singularSupport_quantizeSobolev_subset m s p hp hc f)
  · rintro x ⟨hxu, hxU⟩
    refine ⟨?_, hxU⟩
    intro hnear
    obtain ⟨V, hV, hxV, hPV⟩ := hnear
    have heV : IsEllipticFullSymbol (V ∩ U) m p := by
      intro K hK hcompact
      exact he K (hK.trans Set.inter_subset_right) hcompact
    have hpu := hPV.mono (hV.inter hU) Set.inter_subset_left
    have hu := isSmoothDistributionOn_of_quantizeSobolev_of_isEllipticFullSymbol
      m s p hp hc f (V ∩ U) (hV.inter hU) heV hpu
    exact hxu ⟨V ∩ U, hV.inter hU, ⟨hxV, hxU⟩, hu⟩

/-- SG 4.5's eigenfunction consequence requires strictly positive order. -/
theorem isSmoothDistributionOn_of_quantizeSobolev_eq_smul
    (m s : ℝ) (hm : 0 < m) (p : SymbolFunction n r r)
    (hp : IsSymbol Set.univ m p) (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p) (z : ℂ)
    (hu : besselRealization n r (s - m) (quantizeSobolev m s p hp hc f) =
      z • besselRealization n r s f) :
    IsSmoothDistributionOn (besselRealization n r s f) U := by
  /- Start with u locally in H^s. If u is locally H^t, the eigen-equation puts Pu
  locally in H^t, and inverse regularity puts u locally in H^(t+m). Iterate to
  s+km; strict positivity makes these orders unbounded. Lowering orders then gives
  every local H^t, hence smoothness. This is the Sobolev version of SG's P-zI
  argument. At order zero the identity operator has nonsmooth eigen-distributions,
  so the positive-order hypothesis cannot be dropped. -/
  -- Each application gains exactly m on the same open elliptic set and original distribution.
  have hregular (k : ℕ) : MemSobolevOn (besselRealization n r s f) (s + (k : ℝ) * m) U := by
    induction k with
    | zero =>
      simp only [Nat.cast_zero, zero_mul, add_zero]
      apply memSobolevOn_of_memSobolev
      exact (memSobolev_iff_exists_besselRealization s _).mpr ⟨f, rfl⟩
    | succ k ih =>
      have hPu : MemSobolevOn
          (besselRealization n r (s - m) (quantizeSobolev m s p hp hc f))
          (s + (k : ℝ) * m) U := by
        rw [hu]
        exact ih.smul z
      have h := memSobolevOn_of_quantizeSobolev_of_isEllipticFullSymbol
        m s (s + (k : ℝ) * m) p hp hc f U hU he hPu
      convert h using 1
      push_cast
      ring
  -- Strict positivity makes these orders cofinal, so every local Sobolev order is attained.
  apply (isSmoothDistributionOn_iff_forall_memSobolevOn _ U hU).mpr
  intro t
  obtain ⟨k, hk⟩ := exists_nat_gt ((t - s) / m)
  apply (hregular k).of_le
  have hlt := (div_lt_iff₀ hm).mp hk
  linarith

end AtiyahSinger
