/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasFullSymbolEllipticity
public import AtiyahSinger.Analysis.AtlasPseudodifferentialAsymptotics
public import AtiyahSinger.Analysis.AtlasPseudodifferentialIdentity
public import AtiyahSinger.Analysis.AtlasPseudodifferentialSobolev
public import AtiyahSinger.Analysis.AtlasQuantization
public import AtiyahSinger.Analysis.AtlasSymbolComposition

import AtiyahSinger.Analysis.AtlasPseudodifferentialComposition

/-!
# Two-sided parametrices for general elliptic atlas PDOs

Public module ID: M0243.

A04. SG III.4, Theorem 4.3, Lemma 4.4, Theorem 4.6 and Remark 4.7,
pp.189--191, applied to the original locally finite-rank smooth atlases.
Ellipticity tests a representative of the actual order-m principal quotient
using the compact-local inverse bound. It does not assume homogeneous leading
data or any analytic conclusion.

The parametrix is an actual order-minus-m operator on the original smooth
sections, and one operator Q has both all-order smoothing residuals. The
finite-chart proof uses the full local composition and asymptotic calculus;
pointwise multiplication of inverse symbols alone does not prove the result.
Remainders can couple different components. All original ranks, topologies,
cutoffs and section maps are retained.

The base is compact and without boundary. It may be disconnected, empty or
zero dimensional. In dimension zero its smooth section spaces are finite
dimensional, all operators are smoothing, and Q=0 is allowed even when the
two local ranks differ. No rank equality, positive dimension or global fiber
norm is added. Properly supported noncompact versions are separate statements.
The local inverse-symbol assembly and the common geometric asymptotic correction
are proved with these original objects below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Set
open scoped Manifold ContDiff Topology BigOperators

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  [TopologicalSpace (TotalSpace Unit F)]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [T2Space M] [SecondCountableTopology M] [CompactSpace M]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}

/-- One inverse symbol has both pointwise errors of every order. -/
theorem exists_inverse_atlasGlobalSymbol_of_isEllipticFullAtlasSymbol {m : ℝ}
    (a : atlasGlobalSymbolSpace A B m)
    (he : IsEllipticFullAtlasSymbol A B m a.val) :
    ∃ b : atlasGlobalSymbolSpace B A (-m), ∀ l : ℝ,
      IsAtlasGlobalSymbol A A l (atlasSymbolComp b.val a.val - fun _ _ ↦ LinearMap.id) ∧
      IsAtlasGlobalSymbol B B l (atlasSymbolComp a.val b.val - fun _ _ ↦ LinearMap.id) := by
  /- Assemble local matrix inverses with the original finite partition. On each compact
  overlap, cotangent transition maps admit a uniform lower bound at the unit sphere.
  Thus the same assembled symbol inverts on both sides at sufficiently high frequency.
  Smoothness and locally bounded frequency support then give every residual order. -/
  classical
  obtain ⟨C⟩ := nonempty_atlasQuantizationPresentation B A
  let D (j : Fin C.size) := atlasSymbolChartDomain A B (C.patch j).chart
    (C.patch j).output.frameIndex (C.patch j).input.frameIndex
  have hD (j : Fin C.size) : IsOpen (D j) := by
    simpa only [D, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
      (C.patch j).chart.isOpen_inter_preimage_symm
        ((A.chart (C.patch j).output.frameIndex).open_baseSet.inter
          (B.chart (C.patch j).input.frameIndex).open_baseSet)
  have hinput (j : Fin C.size) : tsupport (C.patch j).input.cutoff ⊆ D j := by
    intro z hz
    exact ⟨⟨((C.patch j).input.support_subset hz).1,
      (C.patch j).input_support_in_output_frame hz⟩,
      ((C.patch j).input.support_subset hz).2⟩
  have houtput (j : Fin C.size) : tsupport (C.patch j).output.cutoff ⊆ D j := by
    intro z hz
    exact ⟨(C.patch j).output.support_subset hz,
      (C.patch j).output_support_in_input_frame hz⟩
  -- Invert each local matrix above one radius on its actual output support.
  have hlocal (j : Fin C.size) :
      ∃ p : SymbolFunction n (B.rank (C.patch j).input.frameIndex)
          (A.rank (C.patch j).output.frameIndex), IsSymbol (D j) (-m) p ∧
        ∃ R : ℝ, 0 < R ∧ ∀ z ∈ tsupport (C.patch j).output.cutoff, ∀ η, R ≤ ‖η‖ →
          p z η = (atlasGlobalSymbolInChart A B a.val (C.patch j).chart
            (C.patch j).output.frameIndex (C.patch j).input.frameIndex z η).inverse ∧
          (atlasGlobalSymbolInChart A B a.val (C.patch j).chart
            (C.patch j).output.frameIndex (C.patch j).input.frameIndex z η).IsInvertible := by
    obtain ⟨p, hp, hpeq⟩ := exists_inverse_symbol_of_isEllipticFullSymbol (hD j)
      (atlasGlobalSymbolInChart A B a.val (C.patch j).chart
        (C.patch j).output.frameIndex (C.patch j).input.frameIndex)
      (a.property (C.patch j).chart (C.patch j).chart_mem_atlas
        (C.patch j).output.frameIndex (C.patch j).input.frameIndex)
      (he (C.patch j).chart (C.patch j).chart_mem_atlas
        (C.patch j).output.frameIndex (C.patch j).input.frameIndex)
    obtain ⟨R, hR, hpeq⟩ := hpeq _ (houtput j) (C.patch j).output.compact_support
    obtain ⟨S, d, hS, hd, hinv⟩ :=
      he (C.patch j).chart (C.patch j).chart_mem_atlas
        (C.patch j).output.frameIndex (C.patch j).input.frameIndex
        _ (houtput j) (C.patch j).output.compact_support
    refine ⟨p, hp, max R S, lt_of_lt_of_le hR (le_max_left _ _), ?_⟩
    intro z hz η hη
    exact ⟨hpeq z hz η ((le_max_left _ _).trans hη),
      (hinv z hz η ((le_max_right _ _).trans hη)).1⟩
  choose p hp R hR hpeq using hlocal
  let p' (j : Fin C.size) := zeroExtendedSymbol (D j) (C.patch j).input.cutoff (p j)
  have hp' (j : Fin C.size) : IsSymbol univ (-m) (p' j) :=
    isSymbol_zeroExtendedSymbol (D j) (hD j) (-m) (C.patch j).input.cutoff
      (C.patch j).input.smooth_cutoff (C.patch j).input.compact_support (hinput j)
      (p j) (hp j)
  have hcp' (j : Fin C.size) : HasCompactSupport (p' j) :=
    hasCompactSupport_zeroExtendedSymbol _ _ _ (C.patch j).input.compact_support
  let L (j : Fin C.size) : AtlasPseudodifferentialPiece B A (-m) :=
    { chart := (C.patch j).chart
      chart_mem_atlas := (C.patch j).chart_mem_atlas
      input := (C.patch j).input
      output := (C.patch j).output
      input_support_in_output_frame := (C.patch j).input_support_in_output_frame
      output_support_in_input_frame := (C.patch j).output_support_in_input_frame
      operator := quantizeSchwartz (-m) (p' j) (hp' j) (hcp' j)
      symbol := p' j
      isSymbol := hp' j
      operator_apply := quantizeSchwartz_apply (-m) (p' j) (hp' j) (hcp' j) }
  let b : atlasGlobalSymbolSpace B A (-m) := ∑ j, (L j).globalSymbol
  -- A contributing piece has both products equal to its original partition weight.
  have hpiece (j : Fin C.size) (x : M)
      (ξ : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ] ℝ)
      (hη : (C.patch j).weight x ≠ 0 → R j ≤ ‖covectorInChart (C.patch j).chart x ξ‖) :
      ((L j).globalSymbolFunction x ξ).comp (a.val x ξ) =
          ((C.patch j).weight x : ℂ) • LinearMap.id ∧
        (a.val x ξ).comp ((L j).globalSymbolFunction x ξ) =
          ((C.patch j).weight x : ℂ) • LinearMap.id := by
    by_cases hx : x ∈ (C.patch j).chart.source
    · by_cases hcut : (C.patch j).output.cutoff ((C.patch j).chart x) = 0
      · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, L,
          AtlasQuantizationPatch.weight, hx, hcut]
      · have hsupport : (C.patch j).chart x ∈ tsupport (C.patch j).output.cutoff :=
          subset_tsupport _ hcut
        have hi : x ∈ (B.chart (C.patch j).input.frameIndex).baseSet := by
          simpa only [Set.mem_preimage, (C.patch j).chart.left_inv hx] using
            (C.patch j).output_support_in_input_frame hsupport
        have ho : x ∈ (A.chart (C.patch j).output.frameIndex).baseSet := by
          simpa only [Set.mem_preimage, (C.patch j).chart.left_inv hx] using
            ((C.patch j).output.support_subset hsupport).2
        obtain ⟨V, _, hsV, hone⟩ := (C.patch j).input_eq_one
        have hin := hone _ (hsV hsupport)
        have hw : (C.patch j).weight x ≠ 0 := by
          simpa only [AtlasQuantizationPatch.weight, ite_eq_left hx] using hcut
        obtain ⟨hpval, hinv⟩ := hpeq j ((C.patch j).chart x) hsupport
          (covectorInChart (C.patch j).chart x ξ) (hη hw)
        let e := (A.frameLinearEquiv (C.patch j).output.frameIndex x ho).trans
          (EuclideanSpace.equiv (Fin (A.rank (C.patch j).output.frameIndex)) ℂ).symm.toLinearEquiv
        let f := (B.frameLinearEquiv (C.patch j).input.frameIndex x hi).trans
          (EuclideanSpace.equiv (Fin (B.rank (C.patch j).input.frameIndex)) ℂ).symm.toLinearEquiv
        let a₀ := atlasGlobalSymbolInChart A B a.val (C.patch j).chart
          (C.patch j).output.frameIndex (C.patch j).input.frameIndex
          ((C.patch j).chart x) (covectorInChart (C.patch j).chart x ξ)
        have hcoord (v : E x) : a₀ (e v) = f (a.val x ξ v) := by
          have hraw : ∀ (hA : (C.patch j).chart.symm ((C.patch j).chart x) ∈
                  (A.chart (C.patch j).output.frameIndex).baseSet)
              (hB : (C.patch j).chart.symm ((C.patch j).chart x) ∈
                  (B.chart (C.patch j).input.frameIndex).baseSet)
              (u : E ((C.patch j).chart.symm ((C.patch j).chart x))),
              a₀ ((EuclideanSpace.equiv _ ℂ).symm
                (A.frameLinearEquiv _ _ hA u)) =
                (EuclideanSpace.equiv _ ℂ).symm
                  (B.frameLinearEquiv _ _ hB
                    (a.val _ (covectorFromChart (C.patch j).chart _
                      (covectorInChart (C.patch j).chart x ξ)) u)) := by
            intro hA hB u
            simp only [a₀, atlasGlobalSymbolInChart, dite_eq_left (And.intro hA hB)]
            let eA := EuclideanSpace.equiv (Fin (A.rank (C.patch j).output.frameIndex)) ℂ
            let eB := EuclideanSpace.equiv (Fin (B.rank (C.patch j).input.frameIndex)) ℂ
            change eB.symm (B.frameLinearEquiv _ _ hB
              (a.val _ (covectorFromChart (C.patch j).chart _
                (covectorInChart (C.patch j).chart x ξ))
                  ((A.frameLinearEquiv _ _ hA).symm (eA (eA.symm
                    (A.frameLinearEquiv _ _ hA u)))))) = _
            rw [eA.apply_symm_apply, (A.frameLinearEquiv _ _ hA).symm_apply_apply]
          rw [(C.patch j).chart.left_inv hx] at hraw
          simpa [e, f, covectorFromChart_covectorInChart (C.patch j).chart
            (C.patch j).chart_mem_atlas x hx ξ] using hraw ho hi v
        let T : F x →ₗ[ℂ] E x := e.symm.toLinearMap.comp (a₀.inverse.toLinearMap.comp f.toLinearMap)
        have hleft : T.comp (a.val x ξ) = LinearMap.id := by
          ext v
          change e.symm (a₀.inverse (f (a.val x ξ v))) = v
          rw [← hcoord]
          have hh := congrArg (fun T ↦ T (e v)) hinv.inverse_comp_self
          change a₀.inverse (a₀ (e v)) = e v at hh
          rw [hh, e.symm_apply_apply]
        have hright : (a.val x ξ).comp T = LinearMap.id := by
          ext v
          apply f.injective
          change f (a.val x ξ (e.symm (a₀.inverse (f v)))) = f v
          rw [← hcoord, e.apply_symm_apply]
          exact congrArg (fun T ↦ T (f v)) hinv.self_comp_inverse
        have hformula : (L j).globalSymbolFunction x ξ =
            ((C.patch j).weight x : ℂ) • T := by
          simp only [AtlasPseudodifferentialPiece.globalSymbolFunction, L,
            dite_eq_left (show x ∈ (C.patch j).chart.source ∩
              (B.chart (C.patch j).input.frameIndex).baseSet ∩
              (A.chart (C.patch j).output.frameIndex).baseSet from ⟨⟨hx, hi⟩, ho⟩), p',
            zeroExtendedSymbol_apply_of_mem _ _ _ _ _ (houtput j hsupport), hin,
            mul_one, Complex.ofReal_one, one_smul, hpval,
            AtlasQuantizationPatch.weight, ite_eq_left hx]
          rfl
        rw [hformula, LinearMap.smul_comp, LinearMap.comp_smul, hleft, hright]
        exact ⟨rfl, rfl⟩
    · simp [AtlasPseudodifferentialPiece.globalSymbolFunction, L,
        AtlasQuantizationPatch.weight, hx]
  have hrecover (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
      (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K) (hKT : K ⊆ c.target) :
      ∃ R : ℝ, 0 < R ∧ ∀ z ∈ K, ∀ η, R ≤ ‖η‖ →
        (b.val (c.symm z) (covectorFromChart c (c.symm z) η)).comp
            (a.val (c.symm z) (covectorFromChart c (c.symm z) η)) = LinearMap.id ∧
        (a.val (c.symm z) (covectorFromChart c (c.symm z) η)).comp
            (b.val (c.symm z) (covectorFromChart c (c.symm z) η)) = LinearMap.id := by
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let T (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (z η : EuclideanSpace ℝ (Fin n)) :=
      covectorInChart d (c.symm z) (covectorFromChart c (c.symm z) η)
    have htransition (d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
        (z η : EuclideanSpace ℝ (Fin n)) (hz : z ∈ c.target)
        (hdz : c.symm z ∈ d.source) :
        ContDiffAt ℝ ∞ (Function.uncurry (T d)) (z, η) := by
      have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
      have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
      have hforward : ContDiffAt ℝ ∞ (d ∘ c.symm) z := by
        exact ((contMDiffAt_of_mem_maximalAtlas hdM hdz).comp z
          (contMDiffAt_symm_of_mem_maximalAtlas hcM hz)).contDiffAt
      have hinverse : ContDiffAt ℝ ∞ (c ∘ d.symm) (d (c.symm z)) := by
        have hbase : d.symm (d (c.symm z)) ∈ c.source := by
          rw [d.left_inv hdz]
          exact c.map_target hz
        exact ((contMDiffAt_of_mem_maximalAtlas hcM hbase).comp (d (c.symm z))
          (contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hdz))).contDiffAt
      have hderiv := (hinverse.fderiv_right (m := ∞) (by simp)).comp (z, η)
        (hforward.comp (z, η) contDiffAt_fst)
      apply contDiffAt_piLp'
      intro j
      have heval := hderiv.clm_apply (contDiffAt_const (c := EuclideanSpace.single j 1))
      have hscalar := contDiffAt_snd.inner ℝ heval
      apply hscalar.congr_of_eventuallyEq
      have hopen : IsOpen (c.target ∩ c.symm ⁻¹' d.source) :=
        c.continuousOn_symm.isOpen_inter_preimage c.open_target d.open_source
      filter_upwards [hopen.prod isOpen_univ |>.mem_nhds
        (show (z, η) ∈ (c.target ∩ c.symm ⁻¹' d.source) ×ˢ univ from ⟨⟨hz, hdz⟩, trivial⟩)]
        with p hp
      have hsource := hp.1.2
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (d (c.symm p.1))
        (by
          simpa only [d.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hcM (c.map_target hp.1.1)).mdifferentiableAt
              (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hdM (d.map_source hsource)).mdifferentiableAt
          (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [d.left_inv hsource] at hcomp
      change inner ℝ p.2 ((mfderiv I I c (c.symm p.1))
          ((mfderiv I I d.symm (d (c.symm p.1))) (EuclideanSpace.single j 1))) =
        inner ℝ p.2
          ((fderiv ℝ (c ∘ d.symm) (d (c.symm p.1))) (EuclideanSpace.single j 1))
      change fderiv ℝ (c ∘ d.symm) (d (c.symm p.1)) =
        (mfderiv I I c (c.symm p.1)).comp (mfderiv I I d.symm (d (c.symm p.1))) at hcomp
      rw [hcomp]
      rfl
    -- Each original patch has a fixed compact support wholly inside its own valid chart.
    let P (j : Fin C.size) := (C.patch j).chart.symm '' tsupport (C.patch j).output.cutoff
    have hP (j : Fin C.size) : IsCompact (P j) :=
      (C.patch j).output.compact_support.image_of_continuousOn
        ((C.patch j).chart.continuousOn_symm.mono
          (fun y hy ↦ ((C.patch j).output.support_subset hy).1))
    have hPsource (j : Fin C.size) : P j ⊆ (C.patch j).chart.source := by
      rintro x ⟨y, hy, rfl⟩
      exact (C.patch j).chart.map_target (((C.patch j).output.support_subset hy).1)
    have hweight (j : Fin C.size) (x : M) (hx : (C.patch j).weight x ≠ 0) : x ∈ P j := by
      have hsource : x ∈ (C.patch j).chart.source := by
        by_contra hout
        exact hx (by simp [AtlasQuantizationPatch.weight, hout])
      have hcut : (C.patch j).output.cutoff ((C.patch j).chart x) ≠ 0 := by
        simpa only [AtlasQuantizationPatch.weight, ite_eq_left hsource] using hx
      exact ⟨(C.patch j).chart x, subset_tsupport _ hcut,
        (C.patch j).chart.left_inv hsource⟩
    have hbaseK : IsCompact (c.symm '' K) := hK.image_of_continuousOn
      (c.continuousOn_symm.mono (fun z hz ↦ hKT hz))
    have hbaseKsource : c.symm '' K ⊆ c.source := by
      rintro x ⟨z, hz, rfl⟩
      exact c.map_target (hKT hz)
    -- On each compact overlap, invertibility gives a positive bound on the unit sphere.
    have hbound (j : Fin C.size) :
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ K, (C.patch j).weight (c.symm z) ≠ 0 →
          ∀ η, ρ ≤ ‖η‖ → R j ≤ ‖T (C.patch j).chart z η‖ := by
      let d := (C.patch j).chart
      have hd := (C.patch j).chart_mem_atlas
      let Q := c '' ((c.symm '' K) ∩ P j)
      have hQ : IsCompact Q := (hbaseK.inter (hP j)).image_of_continuousOn
        (c.continuousOn.mono (fun x hx ↦ hbaseKsource hx.1))
      have hQtarget : Q ⊆ c.target := by
        rintro z ⟨x, hx, rfl⟩
        exact c.map_source (hbaseKsource hx.1)
      have hQsource : ∀ z ∈ Q, c.symm z ∈ d.source := by
        rintro z ⟨x, hx, rfl⟩
        rw [c.left_inv (hbaseKsource hx.1)]
        exact hPsource j hx.2
      have hnonzero (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ Q)
          (η : EuclideanSpace ℝ (Fin n)) (hη : η ≠ 0) : T d z η ≠ 0 := by
        intro hzero
        have hinv := covectorFromChart_covectorInChart d hd (c.symm z) (hQsource z hz)
          (covectorFromChart c (c.symm z) η)
        have hd0 : covectorFromChart d (c.symm z) 0 = 0 := by
          ext v
          change inner ℝ (0 : EuclideanSpace ℝ (Fin n)) ((mfderiv I I d (c.symm z)) v) = 0
          exact inner_zero_left _
        change covectorFromChart d (c.symm z) (T d z η) = _ at hinv
        rw [hzero, hd0] at hinv
        have hback := covectorInChart_covectorFromChart c hc (c.symm z)
          (c.map_target (hQtarget hz)) η
        rw [← hinv] at hback
        have hc0 : covectorInChart c (c.symm z) 0 = 0 := by
          ext i
          rfl
        exact hη (hback.symm.trans hc0)
      let S := Q ×ˢ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
      have hS : IsCompact S := hQ.prod (isCompact_sphere _ _)
      have hcontinuous : ContinuousOn (fun w ↦ ‖T d w.1 w.2‖) S := by
        intro w hw
        exact ((htransition d hd w.1 w.2 (hQtarget hw.1)
          (hQsource w.1 hw.1)).continuousAt.norm).continuousWithinAt
      obtain ⟨b, hb, hlow⟩ := hS.exists_forall_le' hcontinuous (a := 0) (by
        intro w hw
        apply norm_pos_iff.mpr
        apply hnonzero w.1 hw.1
        intro hzero
        simpa only [hzero, Metric.mem_sphere, dist_self, zero_ne_one] using hw.2)
      refine ⟨R j / b, div_pos (hR j) hb, ?_⟩
      intro z hz hw η hη
      have hzQ : z ∈ Q :=
        ⟨c.symm z, ⟨⟨z, hz, rfl⟩, hweight j (c.symm z) hw⟩, c.right_inv (hKT hz)⟩
      have hηpos : 0 < ‖η‖ := lt_of_lt_of_le (div_pos (hR j) hb) hη
      have hηne := norm_pos_iff.mp hηpos
      let v := ‖η‖⁻¹ • η
      have hv : v ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
        simpa [v, mem_sphere_zero_iff_norm] using norm_smul_inv_norm (𝕜 := ℝ) hηne
      have hscale : ‖η‖ • v = η := by
        simp [v, smul_smul, norm_ne_zero_iff.mpr hηne]
      have hlinear (t : ℝ) : T d z (t • v) = t • T d z v := by
        ext i
        change inner ℝ (t • v) _ = t * inner ℝ v _
        exact real_inner_smul_left v _ t
      have hnorm : ‖T d z η‖ = ‖η‖ * ‖T d z v‖ := by
        calc
          ‖T d z η‖ = ‖T d z (‖η‖ • v)‖ :=
            congrArg (fun ξ ↦ ‖T d z ξ‖) hscale.symm
          _ = ‖η‖ * ‖T d z v‖ := by
            rw [hlinear, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg η)]
      rw [hnorm]
      have hone : R j ≤ ‖η‖ * b := (div_le_iff₀ hb).mp hη
      exact hone.trans (mul_le_mul_of_nonneg_left (hlow (z, v) ⟨hzQ, hv⟩) (norm_nonneg η))
    choose R' hR' hRbound using hbound
    let radius : ℝ := 1 + ∑ j, max 0 (R' j)
    have hradius : 0 < radius := by dsimp [radius]; positivity
    refine ⟨radius, hradius, ?_⟩
    intro z hz η hη
    have hRle (j : Fin C.size) : R' j ≤ radius := by
      have hsum : max 0 (R' j) ≤ ∑ l, max 0 (R' l) :=
        Finset.single_le_sum (fun l _ ↦ le_max_left 0 (R' l)) (Finset.mem_univ j)
      exact (le_max_right 0 (R' j)).trans (hsum.trans (by dsimp [radius]; linarith))
    have hw : (∑ j, ((C.patch j).weight (c.symm z) : ℂ)) = 1 := by
      simpa only [Complex.ofReal_sum, Complex.ofReal_one] using
        congrArg Complex.ofReal (C.sum_weight (c.symm z))
    constructor
    · ext v
      simp only [b, Submodule.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
        LinearMap.sum_apply, LinearMap.id_apply]
      change (∑ j, (L j).globalSymbolFunction (c.symm z)
        (covectorFromChart c (c.symm z) η)
          (a.val (c.symm z) (covectorFromChart c (c.symm z) η) v)) = v
      have hterm (j : Fin C.size) := LinearMap.congr_fun
        (hpiece j _ _ (fun hw ↦ hRbound j z hz hw η ((hRle j).trans hη))).1 v
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hterm
      simp_rw [hterm]
      rw [← Finset.sum_smul, hw, one_smul]
    · ext v
      simp only [b, Submodule.coe_sum, Finset.sum_apply, LinearMap.comp_apply,
        LinearMap.sum_apply, map_sum, LinearMap.id_apply]
      change (∑ j, a.val (c.symm z) (covectorFromChart c (c.symm z) η)
        ((L j).globalSymbolFunction (c.symm z)
          (covectorFromChart c (c.symm z) η) v)) = v
      have hterm (j : Fin C.size) := LinearMap.congr_fun
        (hpiece j _ _ (fun hw ↦ hRbound j z hz hw η ((hRle j).trans hη))).2 v
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at hterm
      simp_rw [hterm]
      rw [← Finset.sum_smul, hw, one_smul]
  refine ⟨b, ?_⟩
  intro l
  constructor
  · intro c hc i j
    let U := atlasSymbolChartDomain A A c i j
    let p₀ := atlasGlobalSymbolInChart A A
      (atlasSymbolComp b.val a.val - fun _ _ ↦ LinearMap.id) c i j
    have hU : IsOpen U := by
      simpa only [U, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.isOpen_inter_preimage_symm
          ((A.chart i).open_baseSet.inter (A.chart j).open_baseSet)
    -- The two actual symbols have a smooth order-zero product in these same frames.
    have hp₀ : IsAtlasGlobalSymbol A A 0 (atlasSymbolComp b.val a.val) := by
      simpa only [neg_add_cancel] using b.property.atlasSymbolComp a.property
    have hsub := (atlasGlobalSymbolSpace A A 0).sub_mem hp₀ (atlasGlobalIdentitySymbol A).property
    change IsAtlasGlobalSymbol A A 0 _ at hsub
    have hs : ContDiffOn ℝ ∞ (Function.uncurry p₀) (U ×ˢ univ) :=
      (hsub c hc i j).1
    change IsSymbol U l p₀
    refine ⟨hs, ?_⟩
    intro K hKU hK s t
    -- Vanishing is imposed on compact neighborhoods before any derivatives are taken.
    have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact N ∧ z.val ∈ interior N ∧ ∃ d : ℝ, 0 ≤ d ∧
          ∀ x ∈ N, ∀ η, ‖symbolDerivative p₀ s t x η‖ ≤
            d * (1 + ‖η‖) ^ (l - (t : ℝ)) := by
      obtain ⟨L, hL, hzL, hLU⟩ := exists_compact_subset hU z.property
      obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
      obtain ⟨R₀, _, hr⟩ := hrecover c hc L hL (fun y hy ↦ (hLU hy).1.1)
      have hsupp : ∀ y ∈ interior L, ∀ η, R₀ ≤ ‖η‖ → p₀ y η = 0 := by
        intro y hy η hη
        have heq := (hr y (interior_subset hy) η hη).1
        simp [p₀, atlasGlobalSymbolInChart, atlasSymbolComp, heq]
      have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p₀ R₀
        (hs.mono (Set.prod_mono (interior_subset.trans hLU) subset_rfl)) hsupp l
      obtain ⟨d, hd, hbound⟩ := hsmoothing.2 N hNL hN s t
      exact ⟨N, hN, hzN, d, hd, hbound⟩
    choose N hN hzN d hd hbound using hlocal
    -- A finite subcover combines those bounds on the originally requested compact set.
    obtain ⟨t₀, ht₀⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
    refine ⟨∑ z ∈ t₀, d z, Finset.sum_nonneg (fun z _ ↦ hd z), ?_⟩
    intro x hx η
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht₀ hx)
    apply (hbound z x (interior_subset hxz) η).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hd z) hzt
  · intro c hc i j
    let U := atlasSymbolChartDomain B B c i j
    let p₀ := atlasGlobalSymbolInChart B B
      (atlasSymbolComp a.val b.val - fun _ _ ↦ LinearMap.id) c i j
    have hU : IsOpen U := by
      simpa only [U, atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.isOpen_inter_preimage_symm
          ((B.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    -- The two actual symbols have a smooth order-zero product in these same frames.
    have hp₀ : IsAtlasGlobalSymbol B B 0 (atlasSymbolComp a.val b.val) := by
      simpa only [add_neg_cancel] using a.property.atlasSymbolComp b.property
    have hsub := (atlasGlobalSymbolSpace B B 0).sub_mem hp₀ (atlasGlobalIdentitySymbol B).property
    change IsAtlasGlobalSymbol B B 0 _ at hsub
    have hs : ContDiffOn ℝ ∞ (Function.uncurry p₀) (U ×ˢ univ) :=
      (hsub c hc i j).1
    change IsSymbol U l p₀
    refine ⟨hs, ?_⟩
    intro K hKU hK s t
    -- Vanishing is imposed on compact neighborhoods before any derivatives are taken.
    have hlocal (z : U) : ∃ N : Set (EuclideanSpace ℝ (Fin n)),
        IsCompact N ∧ z.val ∈ interior N ∧ ∃ d : ℝ, 0 ≤ d ∧
          ∀ x ∈ N, ∀ η, ‖symbolDerivative p₀ s t x η‖ ≤
            d * (1 + ‖η‖) ^ (l - (t : ℝ)) := by
      obtain ⟨L, hL, hzL, hLU⟩ := exists_compact_subset hU z.property
      obtain ⟨N, hN, hzN, hNL⟩ := exists_compact_subset isOpen_interior hzL
      obtain ⟨R₀, _, hr⟩ := hrecover c hc L hL (fun y hy ↦ (hLU hy).1.1)
      have hsupp : ∀ y ∈ interior L, ∀ η, R₀ ≤ ‖η‖ → p₀ y η = 0 := by
        intro y hy η hη
        have heq := (hr y (interior_subset hy) η hη).2
        simp [p₀, atlasGlobalSymbolInChart, atlasSymbolComp, heq]
      have hsmoothing := isSmoothingSymbol_of_frequency_support isOpen_interior p₀ R₀
        (hs.mono (Set.prod_mono (interior_subset.trans hLU) subset_rfl)) hsupp l
      obtain ⟨d, hd, hbound⟩ := hsmoothing.2 N hNL hN s t
      exact ⟨N, hN, hzN, d, hd, hbound⟩
    choose N hN hzN d hd hbound using hlocal
    -- A finite subcover combines those bounds on the originally requested compact set.
    obtain ⟨t₀, ht₀⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (N z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzN ⟨x, hKU hx⟩⟩)
    refine ⟨∑ z ∈ t₀, d z, Finset.sum_nonneg (fun z _ ↦ hd z), ?_⟩
    intro x hx η
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht₀ hx)
    apply (hbound z x (interior_subset hxz) η).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hd z) hzt

/-- Asymptotic geometric corrections improve both order-minus-one errors. -/
theorem exists_atlasParametrix_of_order_neg_one {m : ℝ}
    (P : AtlasPseudodifferentialOperator A B m)
    (Q₀ : AtlasPseudodifferentialOperator B A (-m))
    (hleft : IsAtlasPseudodifferentialOperator A A (-1)
      (Q₀.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (hright : IsAtlasPseudodifferentialOperator B B (-1)
      (P.toLinearMap.comp Q₀.toLinearMap - LinearMap.id)) :
    ∃ Q : AtlasPseudodifferentialOperator B A (-m),
      IsAtlasSmoothingOperator A A (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) ∧
      IsAtlasSmoothingOperator B B (P.toLinearMap.comp Q.toLinearMap - LinearMap.id) := by
  /- The jth correction is (I-Q₀P)^j Q₀. The same finite sum telescopes on both
  sides, with the two residual powers acting in their respective section spaces.
  Asymptotic summation and cofinal negative integer orders make both errors smoothing. -/
  classical
  let R := LinearMap.id - Q₀.toLinearMap.comp P.toLinearMap
  let S := LinearMap.id - P.toLinearMap.comp Q₀.toLinearMap
  have hR : IsAtlasPseudodifferentialOperator A A (-1) R := by
    have h := (atlasPseudodifferentialSpace A A (-1)).neg_mem hleft
    change IsAtlasPseudodifferentialOperator A A (-1) _ at h
    simpa only [neg_sub] using h
  have hS : IsAtlasPseudodifferentialOperator B B (-1) S := by
    have h := (atlasPseudodifferentialSpace B B (-1)).neg_mem hright
    change IsAtlasPseudodifferentialOperator B B (-1) _ at h
    simpa only [neg_sub] using h
  have hpowerA (N : ℕ) : IsAtlasPseudodifferentialOperator A A (-(N : ℝ)) (R ^ N) := by
    induction N with
    | zero =>
      simpa only [Nat.cast_zero, neg_zero, pow_zero, Module.End.one_eq_id,
        AtlasPseudodifferentialOperator.id] using
          (AtlasPseudodifferentialOperator.id A).isPseudodifferentialOperator
    | succ N hN =>
      have hcomp := IsAtlasPseudodifferentialOperator.comp (R ^ N) R hN hR
      convert hcomp using 1 <;>
        simp [Nat.cast_add, pow_succ, Module.End.mul_eq_comp, add_comm]
  have hpowerB (N : ℕ) : IsAtlasPseudodifferentialOperator B B (-(N : ℝ)) (S ^ N) := by
    induction N with
    | zero =>
      simpa only [Nat.cast_zero, neg_zero, pow_zero, Module.End.one_eq_id,
        AtlasPseudodifferentialOperator.id] using
          (AtlasPseudodifferentialOperator.id B).isPseudodifferentialOperator
    | succ N hN =>
      have hcomp := IsAtlasPseudodifferentialOperator.comp (S ^ N) S hN hS
      convert hcomp using 1 <;>
        simp [Nat.cast_add, pow_succ, Module.End.mul_eq_comp, add_comm]
  -- These exact identities use distinct source and target endomorphism rings.
  let partialSum (N : ℕ) := (∑ j ∈ Finset.range N, R ^ j).comp Q₀.toLinearMap
  have hleftSum (N : ℕ) : (partialSum N).comp P.toLinearMap - LinearMap.id = -(R ^ N) := by
    have hQP : Q₀.toLinearMap.comp P.toLinearMap = 1 - R := by
      change Q₀.toLinearMap.comp P.toLinearMap =
        LinearMap.id - (LinearMap.id - Q₀.toLinearMap.comp P.toLinearMap)
      abel
    change (∑ j ∈ Finset.range N, R ^ j) * (Q₀.toLinearMap.comp P.toLinearMap) - 1 = -(R ^ N)
    rw [hQP, geom_sum_mul_neg]
    abel
  have hrightSum (N : ℕ) : P.toLinearMap.comp (partialSum N) - LinearMap.id = -(S ^ N) := by
    have hstep : P.toLinearMap.comp R = S.comp P.toLinearMap := by
      ext u
      simp [R, S]
    have hmove (j : ℕ) : P.toLinearMap.comp (R ^ j) = (S ^ j).comp P.toLinearMap := by
      induction j with
      | zero =>
        simp only [pow_zero]
        rfl
      | succ j hj =>
        rw [pow_succ, pow_succ]
        change P.toLinearMap.comp ((R ^ j).comp R) = ((S ^ j).comp S).comp P.toLinearMap
        rw [← LinearMap.comp_assoc, hj, LinearMap.comp_assoc, hstep,
          ← LinearMap.comp_assoc]
    have hsum : P.toLinearMap.comp (partialSum N) =
        (∑ j ∈ Finset.range N, S ^ j) * (P.toLinearMap.comp Q₀.toLinearMap) := by
      apply LinearMap.ext
      intro u
      change P.toLinearMap ((∑ j ∈ Finset.range N, R ^ j) (Q₀.toLinearMap u)) =
        (∑ j ∈ Finset.range N, S ^ j) (P.toLinearMap (Q₀.toLinearMap u))
      simp only [LinearMap.sum_apply, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact LinearMap.congr_fun (hmove j) (Q₀.toLinearMap u)
    have hPQ : P.toLinearMap.comp Q₀.toLinearMap = 1 - S := by
      change P.toLinearMap.comp Q₀.toLinearMap =
        LinearMap.id - (LinearMap.id - P.toLinearMap.comp Q₀.toLinearMap)
      abel
    change P.toLinearMap.comp (partialSum N) - 1 = -(S ^ N)
    rw [hsum, hPQ, geom_sum_mul_neg]
    abel
  -- Sum the geometric corrections asymptotically; no operator-norm convergence is assumed.
  let orders : ℕ → ℝ := fun j ↦ -m - j
  let terms : ℕ → B.smoothSections →ₗ[ℂ] A.smoothSections :=
    fun j ↦ (R ^ j).comp Q₀.toLinearMap
  have horders : StrictAnti orders := by
    intro i j hij
    exact sub_lt_sub_left (Nat.cast_lt.mpr hij) _
  have hlim : Tendsto orders atTop atBot := by
    apply tendsto_atBot.mpr
    intro b
    obtain ⟨N, hN⟩ := exists_nat_ge (-m - b)
    filter_upwards [eventually_ge_atTop N] with j hj
    have hNj : (N : ℝ) ≤ j := Nat.cast_le.mpr hj
    dsimp [orders]
    linarith
  have hterms (j : ℕ) : IsAtlasPseudodifferentialOperator B A (orders j) (terms j) := by
    have h := IsAtlasPseudodifferentialOperator.comp (R ^ j) Q₀.toLinearMap
      (hpowerA j) Q₀.isPseudodifferentialOperator
    convert h using 1
    dsimp [orders]
    ring
  obtain ⟨Q, hQ⟩ := exists_atlasPseudodifferential_expansion B A orders horders hlim terms hterms
  have hsum (N : ℕ) : (∑ j ∈ Finset.range N, terms j) = partialSum N := by
    ext u
    simp [partialSum, terms]
  let Q' : AtlasPseudodifferentialOperator B A (-m) :=
    ⟨Q.toLinearMap, by simpa only [orders, Nat.cast_zero, sub_zero] using
      Q.isPseudodifferentialOperator⟩
  refine ⟨Q', ?_, ?_⟩
  · apply (isAtlasSmoothingOperator_iff_forall_isAtlasPseudodifferentialOperator A A _).mpr
    intro l
    obtain ⟨N, hN⟩ := exists_nat_ge (-l)
    have hNl : -(N : ℝ) ≤ l := by linarith
    have hrem := IsAtlasPseudodifferentialOperator.comp
      (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) P.toLinearMap (hQ N)
      P.isPseudodifferentialOperator
    have hrem' : IsAtlasPseudodifferentialOperator A A (-(N : ℝ))
        ((Q.toLinearMap - partialSum N).comp P.toLinearMap) := by
      rw [← hsum]
      convert hrem using 1
      dsimp [orders]
      ring
    have hpower := (atlasPseudodifferentialSpace A A (-(N : ℝ))).neg_mem (hpowerA N)
    have h := (atlasPseudodifferentialSpace A A (-(N : ℝ))).add_mem hrem' hpower
    change IsAtlasPseudodifferentialOperator A A (-(N : ℝ)) _ at h
    have heq : (Q.toLinearMap - partialSum N).comp P.toLinearMap + -(R ^ N) =
        Q'.toLinearMap.comp P.toLinearMap - LinearMap.id := by
      rw [← hleftSum N]
      simp only [LinearMap.sub_comp, Q']
      abel
    rw [heq] at h
    exact IsAtlasPseudodifferentialOperator.mono A A hNl h
  · apply (isAtlasSmoothingOperator_iff_forall_isAtlasPseudodifferentialOperator B B _).mpr
    intro l
    obtain ⟨N, hN⟩ := exists_nat_ge (-l)
    have hNl : -(N : ℝ) ≤ l := by linarith
    have hrem := IsAtlasPseudodifferentialOperator.comp P.toLinearMap
      (Q.toLinearMap - ∑ j ∈ Finset.range N, terms j) P.isPseudodifferentialOperator (hQ N)
    have hrem' : IsAtlasPseudodifferentialOperator B B (-(N : ℝ))
        (P.toLinearMap.comp (Q.toLinearMap - partialSum N)) := by
      rw [← hsum]
      convert hrem using 1
      dsimp [orders]
      ring
    have hpower := (atlasPseudodifferentialSpace B B (-(N : ℝ))).neg_mem (hpowerB N)
    have h := (atlasPseudodifferentialSpace B B (-(N : ℝ))).add_mem hrem' hpower
    change IsAtlasPseudodifferentialOperator B B (-(N : ℝ)) _ at h
    have heq : P.toLinearMap.comp (Q.toLinearMap - partialSum N) + -(S ^ N) =
        P.toLinearMap.comp Q'.toLinearMap - LinearMap.id := by
      rw [← hrightSum N]
      simp only [LinearMap.comp_sub, Q']
      abel
    rw [heq] at h
    exact IsAtlasPseudodifferentialOperator.mono B B hNl h

namespace AtlasPseudodifferentialOperator

variable {m : ℝ} (P : AtlasPseudodifferentialOperator A B m)

/-- Standard ellipticity of the actual principal class, with no parametrix or Fredholm input. -/
def IsElliptic : Prop :=
  ∃ a : atlasGlobalSymbolSpace A B m,
    P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a ∧
      IsEllipticFullAtlasSymbol A B m a.val

/-- Any specified full representative tests the same ellipticity condition. -/
theorem isElliptic_iff_of_principalSymbol_eq
    (a : atlasGlobalSymbolSpace A B m)
    (hPa : P.principalSymbol = atlasGlobalPrincipalSymbolClass A B m a) :
    P.IsElliptic ↔ IsEllipticFullAtlasSymbol A B m a.val := by
  /- In the forward direction compare the existential full representative
  with this same a in the actual principal quotient. Their difference
  has one lower order, so compact-local inverse bounds are equivalent.
  In the reverse direction use a and hPa themselves as the witness.
  No homogeneous symbol or separately chosen operator is required. -/
  constructor
  · rintro ⟨b, hPb, hb⟩
    -- The same principal class relates the existential representative to the supplied one.
    have hba : atlasGlobalPrincipalSymbolClass A B m b =
        atlasGlobalPrincipalSymbolClass A B m a := hPb.symm.trans hPa
    exact (isEllipticFullAtlasSymbol_iff_of_class_eq A B b a hba).mp hb
  · intro ha
    exact ⟨a, hPa, ha⟩

/-- SG Remark 4.7: general full-symbol ellipticity gives one actual two-sided parametrix. -/
theorem exists_parametrix_of_isElliptic (hP : P.IsElliptic) :
    ∃ Q : AtlasPseudodifferentialOperator B A (-m),
      IsAtlasSmoothingOperator A A (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) ∧
      IsAtlasSmoothingOperator B B (P.toLinearMap.comp Q.toLinearMap - LinearMap.id) := by
  /- Quantize the one inverse symbol, retaining the actual principal classes of P
  and both composites. Exactness lowers both initial errors to order minus one.
  The same geometric asymptotic correction then supplies both smoothing errors. -/
  obtain ⟨a, hPa, ha⟩ := hP
  obtain ⟨b, hb⟩ := exists_inverse_atlasGlobalSymbol_of_isEllipticFullAtlasSymbol a ha
  obtain ⟨C⟩ := nonempty_atlasQuantizationPresentation B A
  let Q₀ := C.quantize b
  have hQ₀ : Q₀.principalSymbol = atlasGlobalPrincipalSymbolClass B A (-m) b :=
    C.principalSymbol_quantize b
  have lowerA (l : ℝ) (hl : l = 0)
      (T : AtlasPseudodifferentialOperator A A l)
      (p : atlasGlobalSymbolSpace A A l)
      (hT : T.principalSymbol = atlasGlobalPrincipalSymbolClass A A l p)
      (hp : IsAtlasGlobalSymbol A A (l - 1) (p.val - fun _ _ ↦ LinearMap.id)) :
      IsAtlasPseudodifferentialOperator A A (-1) (T.toLinearMap - LinearMap.id) := by
    subst l
    have hclass : T.principalSymbol = (AtlasPseudodifferentialOperator.id A).principalSymbol := by
      rw [hT, AtlasPseudodifferentialOperator.principalSymbol_id,
        atlasGlobalPrincipalSymbolClass_eq_iff]
      exact hp
    simpa only [zero_sub, AtlasPseudodifferentialOperator.id] using
      (AtlasPseudodifferentialOperator.principalSymbol_eq_iff A A T
        (AtlasPseudodifferentialOperator.id A)).mp hclass
  have lowerB (l : ℝ) (hl : l = 0)
      (T : AtlasPseudodifferentialOperator B B l)
      (p : atlasGlobalSymbolSpace B B l)
      (hT : T.principalSymbol = atlasGlobalPrincipalSymbolClass B B l p)
      (hp : IsAtlasGlobalSymbol B B (l - 1) (p.val - fun _ _ ↦ LinearMap.id)) :
      IsAtlasPseudodifferentialOperator B B (-1) (T.toLinearMap - LinearMap.id) := by
    subst l
    have hclass : T.principalSymbol = (AtlasPseudodifferentialOperator.id B).principalSymbol := by
      rw [hT, AtlasPseudodifferentialOperator.principalSymbol_id,
        atlasGlobalPrincipalSymbolClass_eq_iff]
      exact hp
    simpa only [zero_sub, AtlasPseudodifferentialOperator.id] using
      (AtlasPseudodifferentialOperator.principalSymbol_eq_iff B B T
        (AtlasPseudodifferentialOperator.id B)).mp hclass
  have hleft : IsAtlasPseudodifferentialOperator A A (-1)
      (Q₀.toLinearMap.comp P.toLinearMap - LinearMap.id) := by
    have hcomp : (Q₀.comp P).principalSymbol =
        atlasGlobalPrincipalSymbolClass A A (-m + m) (atlasGlobalSymbolSpaceComp b a) := by
      rw [Q₀.principalSymbol_comp P, hQ₀, hPa, atlasGlobalPrincipalSymbolComp_class]
    exact lowerA (-m + m) (by ring) (Q₀.comp P) (atlasGlobalSymbolSpaceComp b a)
      hcomp (hb ((-m + m) - 1)).1
  have hright : IsAtlasPseudodifferentialOperator B B (-1)
      (P.toLinearMap.comp Q₀.toLinearMap - LinearMap.id) := by
    have hcomp : (P.comp Q₀).principalSymbol =
        atlasGlobalPrincipalSymbolClass B B (m + -m) (atlasGlobalSymbolSpaceComp a b) := by
      rw [P.principalSymbol_comp Q₀, hPa, hQ₀, atlasGlobalPrincipalSymbolComp_class]
    exact lowerB (m + -m) (by ring) (P.comp Q₀) (atlasGlobalSymbolSpaceComp a b)
      hcomp (hb ((m + -m) - 1)).2
  exact exists_atlasParametrix_of_order_neg_one P Q₀ hleft hright

/-- A left and a right PDO parametrix of the same action agree modulo all-order smoothing. -/
theorem isAtlasSmoothingOperator_sub_of_parametrices
    (Q Q' : AtlasPseudodifferentialOperator B A (-m))
    (hleft : IsAtlasSmoothingOperator A A
      (Q.toLinearMap.comp P.toLinearMap - LinearMap.id))
    (hright : IsAtlasSmoothingOperator B B
      (P.toLinearMap.comp Q'.toLinearMap - LinearMap.id)) :
    IsAtlasSmoothingOperator B A (Q.toLinearMap - Q'.toLinearMap) := by
  /- Compose the left smoothing residual with Q' and the right smoothing
  residual with Q. Their all-order Sobolev extensions use matching
  intermediate orders. Subtract the two resulting bounded maps; on smooth
  sections, (QP-I)Q' - Q(PQ'-I) = Q-Q'. The common triple composite
  cancels, giving the all-order smoothing difference for these same
  opposite parametrices, as in SG Theorem 4.3 and Theorem 4.6. -/
  -- The two residuals are composed with the specified opposite parametrices.
  have h₁ := IsAtlasSmoothingOperator.comp_isAtlasPseudodifferentialOperator
    (Q.toLinearMap.comp P.toLinearMap - LinearMap.id) Q'.toLinearMap
    hleft Q'.isPseudodifferentialOperator
  have h₂ := IsAtlasPseudodifferentialOperator.comp_isAtlasSmoothingOperator
    Q.toLinearMap (P.toLinearMap.comp Q'.toLinearMap - LinearMap.id)
    Q.isPseudodifferentialOperator hright
  intro L K s t
  obtain ⟨T, hT⟩ := h₁ L K s t
  obtain ⟨S, hS⟩ := h₂ L K s t
  refine ⟨T - S, ?_⟩
  intro u
  rw [sub_apply, hT, hS, ← map_sub]
  -- Subtracting the two actual residual actions cancels the common triple composite.
  congr 1
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply, map_sub]
  abel

end AtlasPseudodifferentialOperator

end AtiyahSinger
