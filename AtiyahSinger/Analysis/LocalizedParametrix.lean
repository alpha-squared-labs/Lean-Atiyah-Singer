/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.FullSymbolEllipticity
public import AtiyahSinger.Analysis.LocalComposition
public import AtiyahSinger.Analysis.LocalSobolev
public import AtiyahSinger.Analysis.LocalTwoSidedParametrix

/-!
# A localized left parametrix and its actual Sobolev identity

Public module ID: M0792.

Localize SG III.4.3--4.5 to a compact cutoff inside the elliptic open set,
with Taylor III.1.1's compact-local inverse bounds. The output symbol is compactly
supported; this does not assert proper support of its operator. The exact identity
is first on Schwartz inputs and then on every existing H^s realization.
The same b and c work at all orders. The local two-sided construction supplies their
existence; the retained noncompact input tail is handled by the compact smoothing ideal.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open MeasureTheory
open scoped ContDiff SchwartzMap

variable {n r q : ℕ}

/-- A smoothing symbol with compact spatial support sends every H^s input to a smooth output. -/
theorem isSmoothDistributionOn_quantizeSobolev_of_isSmoothingSymbol
    (m s : ℝ) (p : SymbolFunction n r q) (hp : IsSmoothingSymbol Set.univ p)
    (hc : HasCompactSupport p)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    IsSmoothDistributionOn
      (besselRealization n q (s - m) (quantizeSobolev m s p (hp m) hc f)) Set.univ := by
  /- For each target order t use the same symbol at order s-t. Compatibility of
  quantizeSobolev identifies all these outputs as one distribution. It belongs
  to every H^t, and the existing Sobolev embedding criterion makes it smooth. -/
  apply isSmoothDistributionOn_of_forall_memSobolev
  intro t
  -- Changing the permitted symbol order retains exactly the same output distribution.
  have hsame := quantizeSobolev_compatible m (s - t) s s p (hp m) (hp (s - t)) hc
    f f rfl
  have horder : s - (s - t) = t := by ring
  rw [horder] at hsame
  apply (memSobolev_iff_exists_besselRealization t _).mpr
  exact ⟨quantizeSobolev (s - t) s p (hp (s - t)) hc f, hsame.symm⟩

/-- A compact cutoff inside the elliptic set has a left inverse modulo a smoothing symbol. -/
theorem exists_localized_left_parametrix
    (m : ℝ) (p : SymbolFunction n r q) (hp : IsSymbol Set.univ m p)
    (hc : HasCompactSupport p) (U : Set (EuclideanSpace ℝ (Fin n))) (hU : IsOpen U)
    (he : IsEllipticFullSymbol U m p) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) :
    ∃ b : SymbolFunction n q r, ∃ c : SymbolFunction n r r,
      IsSymbol Set.univ (-m) b ∧ HasCompactSupport b ∧ tsupport b ⊆ U ∧
        IsSmoothingSymbol Set.univ c ∧ HasCompactSupport c ∧
          ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
            ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
              (∀ x, v x = quantize p u x) →
                ∀ x, quantize b v x = χ x • u x + quantize c u x := by
  have hpU : IsSymbol U m p := by
    refine ⟨hp.1.mono (Set.prod_mono (Set.subset_univ _) Set.Subset.rfl), ?_⟩
    intro K _ hK
    exact hp.2 K (Set.subset_univ _) hK
  obtain ⟨ρ, hρ, hcρ, hρU, hρone, qSym, hq, hcq, _, L, hL, _, _, _, hparam⟩ :=
    exists_local_two_sided_parametrix m U hU p hpU he (tsupport χ) hcχ hχU
  let P := quantizeSchwartz m p hp hc
  let Q := quantizeSchwartz (-m) qSym hq hcq
  let pρ := zeroExtendedSymbol U ρ p
  have hpρ := isSymbol_zeroExtendedSymbol U hU m ρ hρ hcρ hρU p hpU
  have hcpρ := hasCompactSupport_zeroExtendedSymbol U ρ p hcρ
  let Pρ := quantizeSchwartz m pρ hpρ hcpρ
  let Mρ := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q)) (fun x ↦ (ρ x : ℂ))
  let Mχ := SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin r)) (fun x ↦ (χ x : ℂ))
  have hP : HasCompactSchwartzSymbol m P := ⟨p, hp, hc, rfl⟩
  have hQ : HasCompactSchwartzSymbol (-m) Q := ⟨qSym, hq, hcq, rfl⟩
  have hsymbol : pρ = zeroExtendedSymbol Set.univ ρ p := by
    funext x ξ
    rw [zeroExtendedSymbol_apply_of_mem Set.univ ρ p x ξ (Set.mem_univ x)]
    by_cases hx : x ∈ U
    · exact zeroExtendedSymbol_apply_of_mem U ρ p x ξ hx
    · have hz : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρU h))
      simp [pρ, zeroExtendedSymbol, hx, hz]
  have hPρ : Pρ = Mρ.comp P := by
    rw [show Mρ = SchwartzMap.smulLeftCLM (EuclideanSpace ℂ (Fin q))
      (fun x ↦ (ρ x : ℂ)) from rfl,
      ← quantizeSchwartz_zeroExtendedSymbol_univ m p hp hc ρ hρ hcρ]
    apply ContinuousLinearMap.ext
    intro u
    apply SchwartzMap.ext
    intro x
    rw [quantizeSchwartz_apply, quantizeSchwartz_apply, hsymbol]
  obtain ⟨c₀, _, hc₀, _, hcc₀, _, _, _, hleft, _⟩ := hparam χ hχ hcχ hρone
  have hbase : HasCompactSmoothingSchwartzSymbol (Mχ.comp (Q.comp Pρ -
      ContinuousLinearMap.id ℂ _)) := ⟨c₀, hc₀, hcc₀, hleft⟩
  -- The larger input tail of the original operator is retained, not discarded.
  have htail := (hasCompactSmoothingSchwartzSymbol_offDiagonal hQ χ ρ
    hχ hcχ hρ hcρ hρone).comp_any hP
  have hfull : HasCompactSmoothingSchwartzSymbol ((Mχ.comp Q).comp P - Mχ) := by
    have h := hbase.add htail
    rw [hPρ] at h
    convert h using 1
    apply ContinuousLinearMap.ext
    intro u
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply,
      ContinuousLinearMap.id_apply, map_sub]
    abel
  obtain ⟨c, hcs, hcc, hcreal⟩ := hfull
  let b := zeroExtendedSymbol Set.univ χ qSym
  have hb := isSymbol_zeroExtendedSymbol Set.univ isOpen_univ (-m) χ hχ hcχ
    (Set.subset_univ _) qSym hq
  have hcb := hasCompactSupport_zeroExtendedSymbol Set.univ χ qSym hcχ
  have hbreal : quantizeSchwartz (-m) b hb hcb = Mχ.comp Q :=
    quantizeSchwartz_zeroExtendedSymbol_univ (-m) qSym hq hcq χ hχ hcχ
  refine ⟨b, c, hb, hcb, (tsupport_zeroExtendedSymbol_subset Set.univ χ qSym).trans hχU,
    hcs, hcc, ?_⟩
  intro u v hv x
  have hvP : P u = v := by
    apply SchwartzMap.ext
    intro y
    rw [quantizeSchwartz_apply]
    exact (hv y).symm
  have hχT : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  have hact := congrArg (fun T : LocalSchwartzOperator n r r ↦ T u x) hcreal
  rw [← hbreal] at hact
  simp only [ContinuousLinearMap.comp_apply, sub_apply, hvP,
    quantizeSchwartz_apply, Mχ, SchwartzMap.smulLeftCLM_apply_apply hχT] at hact
  calc
    quantize b v x = quantize c u x + (χ x : ℂ) • u x := sub_eq_iff_eq_add.mp hact
    _ = χ x • u x + quantize c u x := by rw [Complex.coe_smul, add_comm]

/-- The exact Schwartz parametrix identity extends to every real Sobolev input order. -/
theorem besselRealization_quantizeSobolev_left_parametrix
    (m s : ℝ) (p : SymbolFunction n r q) (b : SymbolFunction n q r)
    (c : SymbolFunction n r r) (hp : IsSymbol Set.univ m p)
    (hb : IsSymbol Set.univ (-m) b) (hc : IsSmoothingSymbol Set.univ c)
    (hpSupp : HasCompactSupport p) (hbSupp : HasCompactSupport b)
    (hcSupp : HasCompactSupport c) (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hid : ∀ u : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin r)),
      ∀ v : 𝓢(EuclideanSpace ℝ (Fin n), EuclideanSpace ℂ (Fin q)),
        (∀ x, v x = quantize p u x) →
          ∀ x, quantize b v x = χ x • u x + quantize c u x)
    (f : Lp (EuclideanSpace ℂ (Fin r)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    besselRealization n r ((s - m) - (-m))
      (quantizeSobolev (-m) (s - m) b hb hbSupp
        (quantizeSobolev m s p hp hpSupp f)) =
      TemperedDistribution.smulLeftCLM (EuclideanSpace ℂ (Fin r))
        (fun x ↦ (χ x : ℂ)) (besselRealization n r s f) +
          besselRealization n r (s - 0) (quantizeSobolev 0 s c (hc 0) hcSupp f) := by
  /- Stage 1: on Schwartz coordinates choose the actual Schwartz representative
  of Pu. The quantization test identity and Bessel injectivity identify its H^(s-m)
  coordinates with the first Sobolev output. Apply hid and the exact cutoff identity.
  Stage 2: all terms are continuous maps from the H^s coordinates into S'.
  Density extends their equality to every f. The outer target order is displayed
  as (s-m)-(-m); its equality to s is arithmetic, not identity of arbitrary coordinates.
  This transport lemma needs the supplied exact identity but no separate ellipticity. -/
  let V := EuclideanSpace ℝ (Fin n)
  let Hr := EuclideanSpace ℂ (Fin r)
  let Hq := EuclideanSpace ℂ (Fin q)
  let P := quantizeSobolev m s p hp hpSupp
  let Q := quantizeSobolev (-m) (s - m) b hb hbSupp
  let R := quantizeSobolev 0 s c (hc 0) hcSupp
  let Mχ := TemperedDistribution.smulLeftCLM Hr (fun x ↦ (χ x : ℂ))
  have hχgrowth : (fun x ↦ (χ x : ℂ)).HasTemperateGrowth :=
    (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
      (Complex.ofRealCLM.contDiff.comp hχ)
  -- Identify the actual intermediate Schwartz output in the prescribed Bessel coordinates.
  have hsmooth (u : 𝓢(V, Hr)) :
      besselRealization n r ((s - m) - (-m)) (Q (P (schwartzSobolevCoordinate s u))) =
        Mχ (besselRealization n r s (schwartzSobolevCoordinate s u)) +
          besselRealization n r (s - 0) (R (schwartzSobolevCoordinate s u)) := by
    obtain ⟨v, hv⟩ := exists_schwartz_quantize m p hp hpSupp u
    have hP : P (schwartzSobolevCoordinate s u) =
        schwartzSobolevCoordinate (s - m) v := by
      apply besselRealization_injective n q (s - m)
      ext1 φ
      rw [besselRealization_schwartzSobolevCoordinate, SchwartzMap.coe_apply]
      change besselRealization n q (s - m)
        (quantizeSobolev m s p hp hpSupp (schwartzSobolevCoordinate s u)) φ = _
      rw [besselRealization_quantizeSobolev]
      apply integral_congr_ae
      filter_upwards with x
      change φ x • quantize p u x = φ x • v x
      rw [hv x]
    rw [hP]
    ext1 φ
    change besselRealization n r ((s - m) - (-m))
      (quantizeSobolev (-m) (s - m) b hb hbSupp
        (schwartzSobolevCoordinate (s - m) v)) φ =
      besselRealization n r s (schwartzSobolevCoordinate s u)
        (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) +
      besselRealization n r (s - 0)
        (quantizeSobolev 0 s c (hc 0) hcSupp (schwartzSobolevCoordinate s u)) φ
    rw [besselRealization_quantizeSobolev, besselRealization_schwartzSobolevCoordinate,
      SchwartzMap.coe_apply, besselRealization_quantizeSobolev]
    have hfirst : Integrable (fun x ↦
        (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) x • u x) :=
      (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ)
        (SchwartzMap.smulLeftCLM ℂ (fun x ↦ (χ x : ℂ)) φ) u).integrable
    obtain ⟨w, hw⟩ := exists_schwartz_quantize 0 c (hc 0) hcSupp u
    have hsecond : Integrable (fun x ↦ φ x • quantize c u x) := by
      have heq : (fun x ↦ φ x • quantize c u x) = fun x ↦ φ x • w x := by
        funext x
        rw [hw x]
      rw [heq]
      exact (SchwartzMap.pairing (ContinuousLinearMap.lsmul ℂ ℂ) φ w).integrable
    rw [← integral_add hfirst hsecond]
    apply integral_congr_ae
    filter_upwards with x
    rw [hid u v hv x, smul_add, SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
    congr 1
    rw [smul_comm, Complex.coe_smul]
    exact (smul_assoc _ _ _).symm
  -- The two sides are continuous maps of the original input coordinates into distributions.
  have heq := (denseRange_schwartzSobolevCoordinate n r s).equalizer
    ((besselRealization n r ((s - m) - (-m))).continuous.comp
      (Q.continuous.comp P.continuous))
    ((Mχ.continuous.comp (besselRealization n r s).continuous).add
      ((besselRealization n r (s - 0)).continuous.comp R.continuous)) (funext hsmooth)
  exact congrFun heq f

end AtiyahSinger
