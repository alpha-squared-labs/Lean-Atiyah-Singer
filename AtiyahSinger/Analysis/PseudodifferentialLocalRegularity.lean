/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticRegularity
public import AtiyahSinger.Analysis.FullSymbolParametrix
public import AtiyahSinger.Analysis.LocalEllipticRegularity
public import AtiyahSinger.Analysis.SobolevCutoff
public import AtiyahSinger.Analysis.SobolevLocalComparison

/-!
# Local regularity of global PDO Sobolev realizations

Public module ID: M0896.

A02/A06: globalize the local mapping and pseudolocal properties, then apply the
actual left parametrix identity to recover local regularity on any open subset.
SG III.5.2(i) is stated for the original differential realization at the end.
The extension to general full-symbol ellipticity uses SG III.4.7 and Taylor
III.1.4--1.5. Inputs remain global H^s sections on the closed fixed-rank base.
There is no arbitrary-distribution carrier, boundary condition or spectral claim.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 15

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [MeasurableSpace M] [BorelSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [hμ : IsSmoothPositiveMeasure (n := n) μ]

include hM hT2 hSC hC hE hF hμ

namespace PseudodifferentialOperator

variable {m : ℝ} (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- The original Sobolev extension maps local H^t to local H^(t-m). -/
theorem memSobolevOn_sobolevExtension (s t : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) (hu : A.MemSobolevOn s u t U) :
    B.MemSobolevOn (s - m) (P.sobolevExtension A B s u) (t - m) U := by
  /- Localize the input by a scalar equal to one near the requested output
  cutoff. Its higher-order lift is an actual Sobolev vector. The separated
  section operator has a smooth kernel, by the local pieces and the smoothing
  ideal. Identify this decomposition on dense smooth sections at the original
  ambient order; no limit in a weaker norm is used to infer higher regularity. -/
  classical
  by_cases hst : s ≤ t
  · intro j χ hχ hcχ hsχ
    let X := EuclideanSpace ℝ (Fin n)
    let V := EuclideanSpace ℂ (Fin q)
    let I := 𝓘(ℝ, X)
    let K := (B.chart j).symm '' tsupport χ
    have hχtarget : tsupport χ ⊆ (B.chart j).target := by
      rintro z hz
      obtain ⟨x, hx, rfl⟩ := hsχ hz
      exact (B.chart j).map_source hx.2
    have hK : IsCompact K := hcχ.image_of_continuousOn
      ((B.chart j).continuousOn_symm.mono hχtarget)
    have hKU : K ⊆ U := by
      rintro _ ⟨z, hz, rfl⟩
      obtain ⟨x, hx, hzx⟩ := hsχ hz
      rw [← hzx, (B.chart j).left_inv hx.2]
      exact hx.1
    have cutoff (S W : Set M) (hS : IsCompact S) (hW : IsOpen W) (hSW : S ⊆ W) :
        ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ HasCompactSupport φ ∧
          tsupport φ ⊆ W ∧ S ⊆ interior {x | φ x = 1} := by
      obtain ⟨O, hO, hSO, hOW, hOc⟩ := exists_open_between_and_isCompact_closure hS hW hSW
      obtain ⟨φ, hone, hzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
        (I := I) (n := ⊤) hS.isClosed (hSO.trans hO.subset_interior_closure)
      have hs : tsupport φ ⊆ closure O := by
        apply closure_minimal ?_ hOc.isClosed
        intro x hx
        by_contra hn
        exact hx (hzero x hn)
      exact ⟨φ, φ.contMDiff, hOc.of_isClosed_subset (isClosed_tsupport _) hs,
        hs.trans hOW, subset_interior_iff_mem_nhdsSet.mpr hone⟩
    obtain ⟨φ, hφ, hcφ, hsφ, honeφ⟩ := cutoff K U hK hU hKU
    obtain ⟨ψ, hψ, _, hsψ, honeψ⟩ := cutoff (tsupport φ) U hcφ hU hsφ
    let η : M → ℝ := fun x ↦ 1 - ψ x
    have hη : ContMDiff I 𝓘(ℝ) ∞ η := contMDiff_const.sub hψ
    let Tψ := smoothSectionMul (n := n) (r := r) E (fun x ↦ (ψ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hψ)
    let Tη := smoothSectionMul (n := n) (r := r) E (fun x ↦ (η x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hη)
    let Tφ := smoothSectionMul (n := n) (r := q) F (fun x ↦ (φ x : ℂ))
      (Complex.ofRealCLM.contMDiff.comp hφ)
    have hψpdo : IsPseudodifferentialOperator E E μ 0 Tψ :=
      isPseudodifferentialOperator_smoothSectionMul _ _
    have hηpdo : IsPseudodifferentialOperator E E μ 0 Tη :=
      isPseudodifferentialOperator_smoothSectionMul _ _
    have hφpdo : IsPseudodifferentialOperator F F μ 0 Tφ :=
      isPseudodifferentialOperator_smoothSectionMul _ _
    let Rψ : PseudodifferentialOperator (n := n) (r := r) (q := r) E E μ 0 := ⟨Tψ, hψpdo⟩
    let Sψ := Rψ.sobolevRealization A A s s (by simp)
    have hSψ (v : smoothSections (n := n) (r := r) E) :
        Sψ (A.smoothToSobolev s v) = A.smoothToSobolev s (Tψ v) :=
      Rψ.sobolevRealization_smoothToSobolev A A s s (by simp) v
    obtain ⟨v, hv, _⟩ := A.exists_sobolev_lift_of_cutoff s t hst u U hu ψ hψ hsψ Sψ hSψ
    -- The near contribution is the inclusion of the output on this actual higher-order lift.
    have hcompat (w : A.SobolevSpace t) :
        P.sobolevExtension A B s (A.sobolevInclusion t s hst w) =
          B.sobolevInclusion (t - m) (s - m) (by linarith) (P.sobolevExtension A B t w) := by
      refine (A.denseRange_smoothToSobolev t).induction_on w
        (isClosed_eq ((P.sobolevExtension A B s).continuous.comp
          (A.sobolevInclusion t s hst).continuous)
          ((B.sobolevInclusion (t - m) (s - m) (by linarith)).continuous.comp
            (P.sobolevExtension A B t).continuous)) ?_
      intro w
      rw [A.sobolevInclusion_smoothToSobolev, P.sobolevExtension_smoothToSobolev,
        P.sobolevExtension_smoothToSobolev, B.sobolevInclusion_smoothToSobolev]
    have hnear : B.MemSobolevOn (s - m) (P.sobolevExtension A B s (Sψ u)) (t - m) U := by
      rw [← hv, hcompat]
      exact (B.memSobolevOn_sobolevInclusion_iff (t - m) (s - m) (t - m)
        (by linarith) _ U).mpr (B.memSobolevOn_self (t - m) _ U)
    -- The two scalar supports have zero product, hence each separated local piece is smoothing.
    have hzero (x : M) : φ x * η x = 0 := by
      by_cases hx : φ x = 0
      · rw [hx, zero_mul]
      · have hψx : ψ x = 1 := (interior_subset (s := {x | ψ x = 1})) (honeψ (subset_tsupport φ hx))
        simp [η, hψx]
    obtain ⟨N, L, K₀, hK₀⟩ := P.isPseudodifferentialOperator
    have hpieces (i : Fin N) :
        IsSmoothingOperator μ (Tφ.comp ((L i).toLinearMap.comp Tη)) :=
      (L i).isSmoothingOperator_cutoff_of_mul_eq_zero φ η hφ hη hzero
    have hkernel : IsSmoothingOperator μ (Tφ.comp ((K₀.toLinearMap μ).comp Tη)) := by
      have hright := IsSmoothingOperator.comp_isPseudodifferentialOperator
        (K₀.toLinearMap μ) Tη ⟨K₀, rfl⟩ hηpdo
      exact IsPseudodifferentialOperator.comp_isSmoothingOperator
        Tφ ((K₀.toLinearMap μ).comp Tη) hφpdo hright
    have hdecompose : Tφ.comp (P.toLinearMap.comp Tη) =
        (∑ i, Tφ.comp ((L i).toLinearMap.comp Tη)) +
          Tφ.comp ((K₀.toLinearMap μ).comp Tη) := by
      rw [hK₀]
      ext w
      simp
    have herror : IsSmoothingOperator μ (Tφ.comp (P.toLinearMap.comp Tη)) := by
      apply (isSmoothingOperator_iff_forall_isPseudodifferentialOperator μ _ A B).mpr
      intro l
      rw [hdecompose]
      exact (pseudodifferentialSpace E F μ l).add_mem
        ((pseudodifferentialSpace E F μ l).sum_mem (fun i _ ↦
          (hpieces i).isPseudodifferentialOperator l _))
        (hkernel.isPseudodifferentialOperator l _)
    obtain ⟨K₁, hK₁⟩ := herror
    have hsmooth := B.isSmoothOn_smoothToSobolev (s - m)
      (K₁.sobolevToSmooth μ A B s u) U hU
    rw [K₁.smoothToSobolev_sobolevToSmooth] at hsmooth
    have hfar := (B.isSmoothOn_iff_forall_memSobolevOn (s - m) _ U hU).mp hsmooth (t - m)
    -- On the requested output cutoff the actual section decomposition is exact.
    let Mχ := TemperedDistribution.smulLeftCLM V (fun z ↦ (χ z : ℂ))
    let D : B.SobolevSpace (s - m) →L[ℂ] TemperedDistribution X V :=
      Mχ.comp ((besselRealization n q (s - m)).comp
        ((PiLp.proj (𝕜 := ℂ) 2 _ j).comp
          (B.sobolevCoordinates (s - m)).range.topologicalClosure.subtypeL))
    have hχgrowth : (fun z ↦ (χ z : ℂ)).HasTemperateGrowth :=
      (hcχ.comp_left (g := Complex.ofRealCLM) rfl).hasTemperateGrowth
        (Complex.ofRealCLM.contDiff.comp hχ)
    have hsection (w : smoothSections (n := n) (r := r) E) (x : M) (hx : x ∈ K) :
        (P.toLinearMap w).val x = (P.toLinearMap (Tψ w)).val x +
          (K₁.toLinearMap μ w).val x := by
      have hφx : φ x = 1 := (interior_subset (s := {x | φ x = 1})) (honeφ hx)
      have hηw : Tη w = w - Tψ w := by
        apply Subtype.ext
        funext y
        change ((1 - ψ y : ℝ) : ℂ) • w.val y = w.val y - (ψ y : ℂ) • w.val y
        rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [hK₁]
      change (P.toLinearMap w).val x = (P.toLinearMap (Tψ w)).val x +
        (φ x : ℂ) • (P.toLinearMap (Tη w)).val x
      rw [hφx, Complex.ofReal_one, one_smul, hηw, map_sub]
      change _ = _ + ((P.toLinearMap w).val x - (P.toLinearMap (Tψ w)).val x)
      abel
    have hcut (w : A.SobolevSpace s) :
        D (P.sobolevExtension A B s w) = D (P.sobolevExtension A B s (Sψ w)) +
          D (K₁.sobolevExtension μ A B s (s - m) w) := by
      refine (A.denseRange_smoothToSobolev s).induction_on w
        (isClosed_eq (D.continuous.comp (P.sobolevExtension A B s).continuous)
          ((D.continuous.comp ((P.sobolevExtension A B s).continuous.comp Sψ.continuous)).add
            (D.continuous.comp (K₁.sobolevExtension μ A B s (s - m)).continuous))) ?_
      intro w
      rw [hSψ, P.sobolevExtension_smoothToSobolev, P.sobolevExtension_smoothToSobolev,
        K₁.sobolevExtension_smoothToSobolev]
      change Mχ (B.localDistribution (s - m) j (B.smoothToSobolev (s - m) _)) =
        Mχ (B.localDistribution (s - m) j (B.smoothToSobolev (s - m) _)) +
          Mχ (B.localDistribution (s - m) j (B.smoothToSobolev (s - m) _))
      simp only [B.localDistribution_smoothToSobolev, ← map_add]
      -- The fixed Schwartz test multiplier sees only the compact set K.
      ext1 ζ
      change (∫ z, (SchwartzMap.smulLeftCLM ℂ (fun z ↦ (χ z : ℂ)) ζ) z •
        B.localize j (P.toLinearMap w) z) =
        ∫ z, (SchwartzMap.smulLeftCLM ℂ (fun z ↦ (χ z : ℂ)) ζ) z •
          ((B.localize j (P.toLinearMap (Tψ w))) z + (B.localize j (K₁.toLinearMap μ w)) z)
      apply integral_congr_ae
      filter_upwards with z
      rw [SchwartzMap.smulLeftCLM_apply_apply hχgrowth]
      by_cases hz : χ z = 0
      · simp [hz]
      · have hzT := hχtarget (subset_tsupport χ hz)
        have hxK : (B.chart j).symm z ∈ K := ⟨z, subset_tsupport χ hz, rfl⟩
        congr 1
        change B.localizedFunction j (P.toLinearMap w) z =
          B.localizedFunction j (P.toLinearMap (Tψ w)) z +
            B.localizedFunction j (K₁.toLinearMap μ w) z
        simp only [SmoothBundlePresentation.localizedFunction, ite_eq_left hzT, sectionInChart]
        rw [hsection w _ hxK]
        let := B.frame_mem_atlas j
        by_cases hχj : B.cutoff j ((B.chart j).symm z) = 0
        · simp [hχj]
        · have hxF := (B.support_subset j (subset_tsupport _ hχj)).2
          rw [((B.frame j).linear ℂ hxF).1, smul_add]
    change (D (P.sobolevExtension A B s u)).MemSobolev (t - m) 2
    rw [hcut]
    exact (hnear j χ hχ hcχ hsχ).add (hfar j χ hχ hcχ hsχ)
  · exact B.memSobolevOn_of_le (s - m) (s - m) (t - m) _ U
      (B.memSobolevOn_self (s - m) _ U) (by linarith [le_of_not_ge hst])

/-- Global PDOs are pseudolocal on their actual Sobolev realizations. -/
theorem isSmoothOn_sobolevExtension (s : ℝ) (u : A.SobolevSpace s)
    (U : Set M) (hU : IsOpen U) (hu : A.IsSmoothOn s u U) :
    B.IsSmoothOn (s - m) (P.sobolevExtension A B s u) U := by
  /- Local smoothness supplies every input order. Apply the same actual Sobolev
  realization at order t+m and then identify the desired output order t. -/
  apply (B.isSmoothOn_iff_forall_memSobolevOn (s - m)
    (P.sobolevExtension A B s u) U hU).mpr
  intro t
  have hin := (A.isSmoothOn_iff_forall_memSobolevOn s u U hU).mp hu (t + m)
  have hout := P.memSobolevOn_sobolevExtension A B s (t + m) u U hU hin
  simpa only [add_sub_cancel_right] using hout

/-- A global PDO creates no new singularities of a Sobolev section. -/
theorem singularSupport_sobolevExtension_subset (s : ℝ) (u : A.SobolevSpace s) :
    B.singularSupport (s - m) (P.sobolevExtension A B s u) ⊆ A.singularSupport s u := by
  /- The same open neighborhood smooth for the input remains smooth for its
  image. Taking the contrapositive preserves the original points of M. -/
  intro x hx
  change ¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U
  rintro ⟨U, hU, hxU, hu⟩
  exact hx ⟨U, hU, hxU, P.isSmoothOn_sobolevExtension A B s u U hU hu⟩

/-- A left smooth-kernel parametrix gives local regularity of the supplied Sobolev input. -/
theorem memSobolevOn_of_isSmoothingOperator
    (Q : PseudodifferentialOperator (n := n) (r := q) (q := r) F E μ (-m))
    (hQ : IsSmoothingOperator μ (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (s t : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U)
    (hPu : B.MemSobolevOn (s - m) (P.sobolevExtension A B s u) t U) :
    A.MemSobolevOn s u (t + m) U := by
  /- The original left residual gives QPu-u=Ku in A's ambient order s.
  The same Q maps the supplied local regularity, while K has an actual smooth
  output. Subtraction recovers u and requires no right parametrix error. -/
  obtain ⟨K, hK⟩ := hQ
  let v := P.sobolevExtension A B s u
  let R := Q.sobolevRealization B A (s - m) s (by linarith)
  have hregular : A.MemSobolevOn s (R v) (t + m) U := by
    have hbase := Q.memSobolevOn_sobolevExtension B A (s - m) t v U hU hPu
    have hout := (A.memSobolevOn_sobolevInclusion_iff ((s - m) - -m) s (t - -m)
      (by linarith) (Q.sobolevExtension B A (s - m) v) U).mpr hbase
    rw [show t - -m = t + m from sub_neg_eq_add t m] at hout
    exact hout
  have hkernel := A.isSmoothOn_smoothToSobolev s (K.sobolevToSmooth μ A A s u) U hU
  rw [K.smoothToSobolev_sobolevToSmooth] at hkernel
  have hKregular := (A.isSmoothOn_iff_forall_memSobolevOn s _ U hU).mp hkernel (t + m)
  have hres := congrArg (fun T : A.SobolevSpace s →L[ℂ] A.SobolevSpace s ↦ T u)
    (P.sobolevRealization_comp_sub_id_eq Q A B K hK s)
  change R v - u = K.sobolevExtension μ A A s s u at hres
  have hu_eq : u = R v - K.sobolevExtension μ A A s s u := by
    rw [← hres]
    abel
  rw [hu_eq]
  exact A.memSobolevOn_sub s (t + m) _ _ U hregular hKregular

/-- Full-symbol ellipticity recovers m local derivatives on every open subset of the base. -/
theorem memSobolevOn_of_isElliptic (hP : P.IsElliptic)
    (s t : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U)
    (hPu : B.MemSobolevOn (s - m) (P.sobolevExtension A B s u) t U) :
    A.MemSobolevOn s u (t + m) U := by
  /- Construct the full-symbol two-sided parametrix from hP and retain its left
  smooth-kernel error. Apply the previous theorem to the same u and U. Ellipticity
  is global here, whereas the regularity information about Pu is only local on U.
  The real order m can be negative or zero; no positive-order spectral argument is used. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix_of_isElliptic hP
  exact P.memSobolevOn_of_isSmoothingOperator A B Q hQ.1 s t u U hU hPu

/-- An elliptic global PDO is locally hypoelliptic for every supplied Sobolev section. -/
theorem isSmoothOn_of_isElliptic (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U)
    (hPu : B.IsSmoothOn (s - m) (P.sobolevExtension A B s u) U) :
    A.IsSmoothOn s u U := by
  /- For each desired local input order t, smoothness of Pu gives order t-m.
  Apply local elliptic regularity to obtain order (t-m)+m=t for u. The all-order
  criterion yields smoothness on U without requiring a globally smooth right-hand side. -/
  apply (A.isSmoothOn_iff_forall_memSobolevOn s u U hU).mpr
  intro t
  have hout := (B.isSmoothOn_iff_forall_memSobolevOn
    (s - m) (P.sobolevExtension A B s u) U hU).mp hPu (t - m)
  simpa only [sub_add_cancel] using P.memSobolevOn_of_isElliptic A B hP s (t - m) u U hU hout

/-- Local smoothness is equivalent for an elliptic input section and its image. -/
theorem isSmoothOn_sobolevExtension_iff_of_isElliptic (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U) :
    B.IsSmoothOn (s - m) (P.sobolevExtension A B s u) U ↔ A.IsSmoothOn s u U := by
  /- The forward implication is local elliptic regularity. The reverse is the
  pseudolocal property of P, which does not itself need ellipticity. Both concern
  the same Sobolev vector and open subset, with their original presentation maps. -/
  exact ⟨P.isSmoothOn_of_isElliptic A B hP s u U hU,
    P.isSmoothOn_sobolevExtension A B s u U hU⟩

/-- A globally elliptic PDO preserves the singular support of every Sobolev input exactly. -/
theorem singularSupport_sobolevExtension_eq_of_isElliptic (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) :
    B.singularSupport (s - m) (P.sobolevExtension A B s u) = A.singularSupport s u := by
  /- Apply the preceding equivalence on every open neighborhood of each base
  point. The negated neighborhood predicates agree. Unlike the Euclidean theorem
  with ellipticity only on U, hP is global, so no intersection with U is required. -/
  ext x
  change (¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      B.IsSmoothOn (s - m) (P.sobolevExtension A B s u) U) ↔
    (¬ ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ A.IsSmoothOn s u U)
  apply not_congr
  constructor
  · rintro ⟨U, hU, hx, hPu⟩
    exact ⟨U, hU, hx, P.isSmoothOn_of_isElliptic A B hP s u U hU hPu⟩
  · rintro ⟨U, hU, hx, hu⟩
    exact ⟨U, hU, hx, P.isSmoothOn_sobolevExtension A B s u U hU hu⟩

end PseudodifferentialOperator

namespace DifferentialOperator

variable {k : ℕ} (P : DifferentialOperator (n := n) (r := r) (q := q) E F k)
  (A : SmoothBundlePresentation (n := n) (r := r) E)
  (B : SmoothBundlePresentation (n := n) (r := q) F)

/-- Local real-order elliptic regularity for the original differential Sobolev extension. -/
theorem memSobolevOn_of_isElliptic (hP : P.IsElliptic)
    (s t : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U)
    (hPu : B.MemSobolevOn (s - k) (P.sobolevExtension A B s u) t U) :
    A.MemSobolevOn s u (t + k) U := by
  /- Choose the existing differential parametrix and use its left smoothing
  error for P's actual PDO inclusion. Its section map is P.toLinearMap, and the
  Sobolev comparison theorem identifies its extension with the differential one.
  Apply the PDO local lifting theorem. This includes k=0 and all real s,t;
  the fixed positive density is auxiliary to the parametrix construction. -/
  obtain ⟨Q, hQ⟩ := P.exists_parametrix μ hP
  have hPDO : B.MemSobolevOn (s - k)
      ((P.toPseudodifferentialOperator μ).sobolevExtension A B s u) t U := by
    rwa [P.sobolevExtension_toPseudodifferentialOperator μ A B s]
  exact (P.toPseudodifferentialOperator μ).memSobolevOn_of_isSmoothingOperator
    A B Q hQ.1 s t u U hU hPDO

/-- SG III.5.2(i): Pu smooth on any open U implies the original Sobolev section is smooth there. -/
theorem isSmoothOn_of_isElliptic (hP : P.IsElliptic)
    (s : ℝ) (u : A.SobolevSpace s) (U : Set M) (hU : IsOpen U)
    (hPu : B.IsSmoothOn (s - k) (P.sobolevExtension A B s u) U) :
    A.IsSmoothOn s u U := by
  /- Characterize the local smoothness of Pu by all local orders. For a desired
  input order t, apply the preceding differential result with right-hand-side
  order t-k. Then use the all-order characterization for u. This supplies the
  open-set assertion of SG 5.2(i), beyond the earlier whole-base smooth-lift theorem.
  It remains a statement for H^s inputs, not for all distribution sections. -/
  apply (A.isSmoothOn_iff_forall_memSobolevOn s u U hU).mpr
  intro t
  have hout := (B.isSmoothOn_iff_forall_memSobolevOn
    (s - k) (P.sobolevExtension A B s u) U hU).mp hPu (t - k)
  simpa only [sub_add_cancel] using
    P.memSobolevOn_of_isElliptic (μ := μ) A B hP s (t - k) u U hU hout

end DifferentialOperator

end AtiyahSinger
