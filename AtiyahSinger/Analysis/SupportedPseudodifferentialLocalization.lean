/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.PseudodifferentialCutoff
public import AtiyahSinger.Analysis.SectionOperatorSupport

/-!
# A supported PDO represented inside a prescribed open region

Public module ID: M1016.

Choose one smooth cutoff equal to one near the actual operator support. Absorb
it into both sides of every original native piece and both variables of the
original smoothing kernel. The resulting finite representation is an equality
of the original section maps, and one compact subset of the given open region
contains every piece and both kernel variables. This is the localization used
in the global open-extension argument of SG III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Manifold Topology

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
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]
  {μ : Measure M} [IsSmoothPositiveMeasure (n := n) μ]

/-- A supported PDO has an exact finite-piece and kernel representation inside any open region. -/
theorem PseudodifferentialOperator.exists_supported_representation {m : ℝ}
    (P : PseudodifferentialOperator (n := n) (r := r) (q := q) E F μ m)
    (K : Set M) (U : Opens M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (hP : HasSectionOperatorSupport K P.toLinearMap) :
    ∃ C : Set M, IsCompact C ∧ C ⊆ (U : Set M) ∧
      ∃ (d : ℕ) (T : Fin d → PseudodifferentialPiece (n := n) (r := r) (q := q) E F m)
        (S : SmoothKernel (n := n) (r := r) (q := q) E F),
        (∀ j, (T j).chart.symm ''
          (tsupport (T j).input.cutoff ∪ tsupport (T j).output.cutoff) ⊆ C) ∧
        (∀ x y, x ∉ C ∨ y ∉ C → S.toFun x y = 0) ∧
        P.toLinearMap = (∑ j, (T j).toLinearMap) + S.toLinearMap μ := by
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace
    (EuclideanSpace ℝ (Fin n)) M
  -- One compact plateau works simultaneously for the whole original representation.
  obtain ⟨W, hW, hKW, hWU, hWc⟩ :=
    exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨χ, hχone, hχzero, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (I := I) (n := ⊤) hK.isClosed (hKW.trans hW.subset_interior_closure)
  have hsχ : tsupport χ ⊆ closure W := by
    apply closure_minimal ?_ hWc.isClosed
    intro x hx
    by_contra hn
    exact hx (hχzero x hn)
  have hcχ : HasCompactSupport χ := hWc.of_isClosed_subset (isClosed_tsupport _) hsχ
  have hχU : tsupport χ ⊆ (U : Set M) := hsχ.trans hWU
  have hχK (x : M) (hx : x ∈ K) : χ x = 1 := by
    have heq : (fun y ↦ χ y) =ᶠ[𝓝 x] (fun _ ↦ (1 : ℝ)) :=
      hχone.filter_mono (nhds_le_nhdsSet hx)
    exact heq.eq_of_nhds
  let Tin := smoothSectionMul (n := n) (r := r) E (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  let Tout := smoothSectionMul (n := n) (r := q) F (fun x ↦ (χ x : ℂ))
    (Complex.ofRealCLM.contMDiff.comp χ.contMDiff)
  -- The inner error vanishes near K, and the outer cutoff fixes all supported outputs.
  have hinput : P.toLinearMap.comp Tin = P.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply sub_eq_zero.mp
    change P.toLinearMap (Tin u) - P.toLinearMap u = 0
    rw [← map_sub]
    apply hP.2
    apply Set.disjoint_left.mpr
    intro x hx hxK
    have hn : {y : M | χ y = 1} ∈ 𝓝 x :=
      hχone.filter_mono (nhds_le_nhdsSet hxK)
    obtain ⟨y, hy, hne⟩ := mem_closure_iff_nhds.mp hx _ hn
    change (χ y : ℂ) • u.val y - u.val y ≠ 0 at hne
    exact hne (by rw [hy, Complex.ofReal_one, one_smul, sub_self])
  have houtput : Tout.comp P.toLinearMap = P.toLinearMap := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    change (χ x : ℂ) • (P.toLinearMap u).val x = (P.toLinearMap u).val x
    by_cases hx : x ∈ K
    · rw [hχK x hx, Complex.ofReal_one, one_smul]
    · have hz : (P.toLinearMap u).val x = 0 := by
        by_contra hn
        exact hx (hP.1 u (subset_closure hn))
      rw [hz, smul_zero]
  obtain ⟨d, L, S, hS⟩ := P.isPseudodifferentialOperator
  let T (j : Fin d) := (L j).cutoff χ χ χ.contMDiff χ.contMDiff
  have hpiece (j : Fin d) : (T j).toLinearMap = Tout.comp ((L j).toLinearMap.comp Tin) :=
    (L j).toLinearMap_cutoff χ χ χ.contMDiff χ.contMDiff
  -- Coordinate continuity puts each new native cutoff in this same global compact support.
  have hcutSupport (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : tsupport f ⊆ c.target) :
      c.symm '' tsupport (fun z ↦ f z * χ (c.symm z)) ⊆ tsupport χ := by
    rintro x ⟨z, hz, rfl⟩
    by_contra hn
    have hzf : z ∈ tsupport f := tsupport_mul_subset_left hz
    have hnear := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
      (c.continuousAt_symm (hf hzf))
    have hzout : (fun y ↦ f y * χ (c.symm y)) =ᶠ[𝓝 z] 0 := by
      filter_upwards [hnear] with y hy
      rw [show χ (c.symm y) = 0 from hy, mul_zero]
      rfl
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzout) hz
  -- Reweight the same original smoothing kernel in its two variables.
  let S' : SmoothKernel (n := n) (r := r) (q := q) E F :=
    { toFun := fun x y ↦ ((χ x : ℂ) * (χ y : ℂ)) • S.toFun x y
      isSmooth := by
        intro e f _ _
        have hw : ContMDiff (I.prod I) 𝓘(ℝ, ℂ) ∞
            (fun z : M × M ↦ (χ z.1 : ℂ) * (χ z.2 : ℂ)) :=
          (contDiff_fst.mul contDiff_snd :
            ContDiff ℝ ∞ (fun z : ℂ × ℂ ↦ z.1 * z.2)).contMDiff.comp
              (((Complex.ofRealCLM.contMDiff.comp χ.contMDiff).comp contMDiff_fst).prodMk_space
                ((Complex.ofRealCLM.contMDiff.comp χ.contMDiff).comp contMDiff_snd))
        have hsmul : ContDiff ℝ ∞ (fun z : ℂ ×
            (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) ↦ z.1 • z.2) :=
          (show ContDiff ℂ ∞ _ from contDiff_fst.smul contDiff_snd).restrict_scalars ℝ
        apply (hsmul.contMDiff.comp_contMDiffOn
          (hw.contMDiffOn.prodMk_space (S.isSmooth e f))).congr
        intro z hz
        simp only [kernelInFrames, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul]
        rfl }
  have hkernel : S'.toLinearMap μ = Tout.comp ((S.toLinearMap μ).comp Tin) := by
    apply LinearMap.ext
    intro u
    apply Subtype.ext
    funext x
    let : NormedSpace ℝ (F x) := NormedSpace.restrictScalars ℝ ℂ (F x)
    change (∫ y, ((χ x : ℂ) * (χ y : ℂ)) • S.toFun x y (u.val y) ∂μ) =
      (χ x : ℂ) • ∫ y, S.toFun x y ((χ y : ℂ) • u.val y) ∂μ
    simp_rw [map_smul, mul_smul]
    exact integral_smul _ _
  refine ⟨tsupport χ, hcχ, hχU, d, T, S', ?_, ?_, ?_⟩
  · intro j x hx
    rcases hx with ⟨z, hz | hz, rfl⟩
    · exact hcutSupport (L j).chart (L j).input.cutoff
        (fun y hy ↦ ((L j).input.support_subset hy).1) ⟨z, hz, rfl⟩
    · exact hcutSupport (L j).chart (L j).output.cutoff
        (fun y hy ↦ ((L j).output.support_subset hy).1) ⟨z, hz, rfl⟩
  · intro x y hxy
    rcases hxy with hx | hy
    · simp [S', image_eq_zero_of_notMem_tsupport hx]
    · simp [S', image_eq_zero_of_notMem_tsupport hy]
  · have hsum : S'.toLinearMap μ = P.toLinearMap - ∑ j, (T j).toLinearMap := by
      rw [hkernel, hS]
      simp only [LinearMap.sub_comp, LinearMap.comp_sub, hinput, houtput, hpiece]
      congr 1
      apply LinearMap.ext
      intro u
      simp
    rw [hsum]
    abel

end AtiyahSinger
