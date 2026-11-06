/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GlobalPrincipalSymbol
public import AtiyahSinger.Analysis.OpenOperatorCoordinates
public import AtiyahSinger.Geometry.CotangentDiffeomorph

/-!
# Principal classes of native pieces under open transport

Public module ID: M0834.

The exact matrix/cotangent comparison of a transported full symbol determines
its global principal class. Source cutoff reduction contributes one lower
order. The four target cutoff factors cancel on the support of the specified
global symbol. Compact support then extends the local estimate across the
chart boundary using the original coordinate and frame transition laws.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle IsManifold MeasureTheory Set
open scoped Manifold ContDiff SchwartzMap Topology

set_option maxSynthPendingDepth 40

section ChartSupport

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


variable [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [T2Space M]
  [IsSmoothComplexBundle (n := n) (r := r) E]
  [IsSmoothComplexBundle (n := n) (r := q) F]

set_option maxHeartbeats 2000000 in
-- The arbitrary target coordinates retain the complete original covector and frame transition.
private theorem isGlobalSymbol_of_compactSupportInChart (m : ℝ)
    (p : GlobalSymbolFunction (n := n) E F)
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    (f : Trivialization (EuclideanSpace ℂ (Fin q)) (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas f]
    (K : Set M) (hK : IsCompact K)
    (hKD : K ⊆ c.source ∩ e.baseSet ∩ f.baseSet)
    (hzero : ∀ x, x ∉ K → ∀ ξ, p x ξ = 0)
    (hp : IsSymbol (symbolChartDomain E F c e f) m (globalSymbolInChart E F p c e f)) :
    IsGlobalSymbol (n := n) (r := r) (q := q) E F m p := by
  -- A test chart meets either the original compact support or its open zero region.
  intro d hd e' f' _ _
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let U := symbolChartDomain E F d e' f'
  let pnew := globalSymbolInChart E F p d e' f'
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
  -- Equality on an open spatial set identifies every original mixed derivative there.
  have congrSymbol {V : Set X} (hV : IsOpen V) (a b : SymbolFunction n r q)
      (ha : IsSymbol V m a) (hab : ∀ x ∈ V, ∀ ξ, a x ξ = b x ξ) :
      IsSymbol V m b := by
    refine ⟨ha.1.congr (fun z hz ↦ (hab z.1 hz.1 z.2).symm), ?_⟩
    intro C hCV hC i j
    obtain ⟨B, hB, hbound⟩ := ha.2 C hCV hC i j
    refine ⟨B, hB, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (a y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (b y) ξ) := by
      filter_upwards [hV.mem_nhds (hCV hx)] with y hy
      rw [funext (hab y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  -- Each point uses a member of the actual covering atlas, on an open overlap.
  apply IsSymbol.of_locally hU
  intro z hz
  by_cases hzK : d.symm z ∈ K
  · have hj := hKD hzK
    let D := c.source ∩ e.baseSet ∩ f.baseSet
    have hD : IsOpen D := (c.open_source.inter e.open_baseSet).inter
      f.open_baseSet
    let V := U ∩ d.symm ⁻¹' D
    have hV : IsOpen V :=
      (d.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU hD
    have hzV : z ∈ V := ⟨hz, hj⟩
    let S := symbolChartDomain E F c e f
    have hS : IsOpen S := isOpen_symbolChartDomain E F c e f
    let t₀ : OpenPartialHomeomorph X X := c.symm.trans d
    let t : OpenPartialHomeomorph X X := t₀.restrOpen S hS
    have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
    have ht₀ : ContDiffOn ℝ ∞ t₀ t₀.source := by
      intro y hy
      exact (((contMDiffAt_of_mem_maximalAtlas hdM hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas hcM hy.1)).contDiffAt).contDiffWithinAt
    have hts₀ : ContDiffOn ℝ ∞ t₀.symm t₀.target := by
      intro y hy
      exact (((contMDiffAt_of_mem_maximalAtlas hcM hy.2).comp y
        (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1)).contDiffAt).contDiffWithinAt
    have ht : ContDiffOn ℝ ∞ t t.source := ht₀.mono Set.inter_subset_left
    have hts : ContDiffOn ℝ ∞ t.symm t.target := hts₀.mono Set.inter_subset_left
    have h_old (y : X) (hy : y ∈ V) : c (d.symm y) ∈ S := by
      refine ⟨⟨c.map_source hy.2.1.1, ?_⟩, ?_⟩
      · change c.symm (c (d.symm y)) ∈ e.baseSet
        simpa only [c.left_inv hy.2.1.1] using hy.2.1.2
      · change c.symm (c (d.symm y)) ∈ f.baseSet
        simpa only [c.left_inv hy.2.1.1] using hy.2.2
    have hVt : V ⊆ t.target := fun y hy ↦
      ⟨⟨hy.1.1.1, hy.2.1.1⟩, h_old y hy⟩
    let p₀ := globalSymbolInChart E F p c e f
    have hpt : IsSymbol V m (cotangentSymbol t p₀) :=
      (isSymbol_cotangentSymbol t ht hts m p₀
        (hp.restrict Set.inter_subset_right)).restrict hVt
    let A : X → (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) :=
      fun y ↦ (f.coordChangeL ℂ f' (d.symm y)).toContinuousLinearMap
    let B : X → (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) :=
      fun y ↦ (e.coordChangeL ℂ e' (d.symm y)).symm.toContinuousLinearMap
    have hdV : ContMDiffOn I I ∞ d.symm V := by
      intro y hy
      exact (contMDiffAt_symm_of_mem_maximalAtlas hdM hy.1.1.1).contMDiffWithinAt
    have hA : ContDiffOn ℝ ∞ A V := contDiffOn_coordChangeL_comp F
      f f' V d.symm hdV (fun y hy ↦ ⟨hy.2.2, hy.1.2⟩)
    have hB : ContDiffOn ℝ ∞ B V := contDiffOn_symm_coordChangeL_comp E
      e e' V d.symm hdV (fun y hy ↦ ⟨hy.2.1.2, hy.1.1.2⟩)
    refine ⟨V, hV, hzV, Set.inter_subset_left,
      congrSymbol hV _ pnew (isSymbol_matrixSymbol V hV m _ hpt A B hA hB) ?_⟩
    intro y hy η
    -- Both sides are the same covector and Hom map in the prescribed two frames.
    have hfreq : covectorInChart c (d.symm y)
        (covectorFromChart d (d.symm y) η) =
          (fderiv ℝ t (t.symm y)).adjoint η := by
      have hsource := hy.2.1.1
      have hcomp := mfderiv_comp (I := I) (I' := I) (I'' := I) (c (d.symm y))
        (by
          simpa only [c.left_inv hsource] using
            (contMDiffAt_of_mem_maximalAtlas hdM
              (d.map_target hy.1.1.1)).mdifferentiableAt (by simp))
        ((contMDiffAt_symm_of_mem_maximalAtlas hcM
          (c.map_source hsource)).mdifferentiableAt (by simp))
      rw [mfderiv_eq_fderiv] at hcomp
      dsimp [NormedSpace.fromTangentSpace, tangentSpaceCastModel] at hcomp
      rw [c.left_inv hsource] at hcomp
      have htcomp : fderiv ℝ t (t.symm y) =
          (mfderiv I I d (d.symm y)).comp
            (mfderiv I I c.symm (c (d.symm y))) := hcomp
      ext a
      change inner ℝ η ((mfderiv I I d (d.symm y))
          ((mfderiv I I c.symm (c (d.symm y)))
            (EuclideanSpace.single a 1))) =
        ((fderiv ℝ t (t.symm y)).adjoint η) a
      have hadj := (fderiv ℝ t (t.symm y)).adjoint_inner_left
        (EuclideanSpace.single a 1) η
      calc
        _ = inner ℝ η ((fderiv ℝ t (t.symm y)) (EuclideanSpace.single a 1)) := by
          rw [htcomp]
          rfl
        _ = inner ℝ ((fderiv ℝ t (t.symm y)).adjoint η)
            (EuclideanSpace.single a 1) := hadj.symm
        _ = _ := by
          simpa using EuclideanSpace.inner_single_right (𝕜 := ℝ) a 1
            ((fderiv ℝ t (t.symm y)).adjoint η)
    have hchange := globalSymbolInChart_transition E F p c d
      hc hd e e' f f' (d.symm y)
      hy.2.1.1 (d.map_target hy.1.1.1) ⟨hy.2.1.2, hy.1.1.2⟩ ⟨hy.2.2, hy.1.2⟩
      (covectorFromChart d (d.symm y) η)
    rw [covectorInChart_covectorFromChart d hd (d.symm y) (d.map_target hy.1.1.1) η,
      d.right_inv hy.1.1.1, hfreq] at hchange
    exact hchange.symm
  · let V := U ∩ d.symm ⁻¹' Kᶜ
    have hV : IsOpen V :=
      (d.continuousOn_symm.mono (fun y hy ↦ hy.1.1)).isOpen_inter_preimage hU
        hK.isClosed.isOpen_compl
    refine ⟨V, hV, ⟨hz, hzK⟩, Set.inter_subset_left,
      congrSymbol hV 0 pnew (isSymbol_zero V m) ?_⟩
    intro y hy η
    change 0 = globalSymbolInChart E F p d e' f' y η
    simp only [globalSymbolInChart, hzero (d.symm y) hy.2,
      ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero]


end ChartSupport

section OpenPiece

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N] [T2Space N]
  (E F : SmoothFiniteComplexBundle (n := n) M)
  (G H : SmoothFiniteComplexBundle (n := n) N)

set_option maxHeartbeats 2000000 in
-- The same four cutoff factors are removed using the actual support of J.
/-- The same native transported piece has the principal class of its specified global symbol. -/
theorem globalPrincipalSymbolClass_eq_of_openPiece {m : ℝ}
    (P : PseudodifferentialPiece (n := n) (r := E.rank) (q := F.rank) E.Fiber F.Fiber m)
    (Q : PseudodifferentialPiece (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
    (J : globalSymbolSpace (n := n) (r := G.rank) (q := H.rank) G.Fiber H.Fiber m)
    (L : Set N) (hL : IsCompact L)
    (hLbase : L ⊆ Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet)
    (hzero : ∀ y, y ∉ L → ∀ η, J.val y η = 0)
    (hsame : Q.output.cutoff = Q.input.cutoff)
    (hone : ∀ y ∈ L, Q.input.cutoff (Q.chart y) = 1)
    (t : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)))
    (ht : ContDiffOn ℝ ∞ t t.source) (hts : ContDiffOn ℝ ∞ t.symm t.target)
    (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω) (hΩt : Ω ⊆ t.target)
    (hcut : tsupport Q.input.cutoff ⊆ Ω)
    (A : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin F.rank) →L[ℂ] EuclideanSpace ℂ (Fin H.rank))
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank))
    (hA : ContDiffOn ℝ ∞ A Ω) (hB : ContDiffOn ℝ ∞ B Ω)
    (hprincipal : IsSymbol t.target (m - 1)
      (Q.symbol - matrixSymbol (cutoffMatrix Q.input.cutoff A)
        (cutoffMatrix Q.input.cutoff B)
        (cotangentSymbol t (cutoffSymbol P.output.cutoff P.input.cutoff P.symbol))))
    (hcoordinates : letI := Q.input.frame_mem_atlas
      letI := Q.output.frame_mem_atlas
      ∀ z ∈ Ω, ∀ η, globalSymbolInChart G.Fiber H.Fiber J.val Q.chart
        Q.input.frame Q.output.frame z η =
          matrixSymbol A B (cotangentSymbol t
            (fun x ξ ↦ cutoffAmplitude P.output.cutoff P.input.cutoff P.symbol x x ξ)) z η) :
    globalPrincipalSymbolClass G.Fiber H.Fiber m Q.globalSymbol =
      globalPrincipalSymbolClass G.Fiber H.Fiber m J := by
  classical
  let := Q.input.frame_mem_atlas
  let := Q.output.frame_mem_atlas
  let X := EuclideanSpace ℝ (Fin n)
  let χ := Q.input.cutoff
  let p₀ := cutoffSymbol P.output.cutoff P.input.cutoff P.symbol
  let pLead : SymbolFunction n E.rank F.rank :=
    fun x ξ ↦ cutoffAmplitude P.output.cutoff P.input.cutoff P.symbol x x ξ
  let S := symbolChartDomain G.Fiber H.Fiber Q.chart Q.input.frame Q.output.frame
  have hS : IsOpen S := isOpen_symbolChartDomain G.Fiber H.Fiber Q.chart
    Q.input.frame Q.output.frame
  let j := globalSymbolInChart G.Fiber H.Fiber J.val Q.chart Q.input.frame Q.output.frame
  have hχ : ContDiffOn ℝ ∞ χ Ω := Q.input.smooth_cutoff.contDiffOn
  -- Reduce the source cutoffs by one order before applying the original coordinate matrices.
  have hsource : IsSymbol Set.univ (m - 1) (p₀ - pLead) := by
    have h := hasSymbolExpansion_cutoffSymbol m P.symbol P.isSymbol
      P.output.cutoff P.input.cutoff P.output.smooth_cutoff P.input.smooth_cutoff
      P.output.compact_support P.input.compact_support 1
    simpa only [Nat.cast_one, Finset.sum_range_one, amplitudeExpansionTerm_zero] using h
  have htrans := (isSymbol_cotangentSymbol t ht hts (m - 1) (p₀ - pLead)
    (hsource.restrict (Set.subset_univ _))).restrict hΩt
  have hmat := isSymbol_matrixSymbol Ω hΩ (m - 1) _ htrans
    (cutoffMatrix χ A) (cutoffMatrix χ B) (hχ.smul hA) (hχ.smul hB)
  have herr : IsSymbol Ω (m - 1)
      (Q.symbol - matrixSymbol (cutoffMatrix χ A) (cutoffMatrix χ B)
        (cotangentSymbol t pLead)) := by
    convert (hprincipal.restrict hΩt).add hΩ hmat using 1
    funext z η
    simp only [Pi.add_apply, Pi.sub_apply, matrixSymbol, cotangentSymbol,
      ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  let C (z : X) : EuclideanSpace ℂ (Fin H.rank) →L[ℂ] EuclideanSpace ℂ (Fin H.rank) :=
    χ z • ContinuousLinearMap.id ℂ _
  let D (z : X) : EuclideanSpace ℂ (Fin G.rank) →L[ℂ] EuclideanSpace ℂ (Fin G.rank) :=
    χ z • ContinuousLinearMap.id ℂ _
  have hweighted := isSymbol_matrixSymbol Ω hΩ (m - 1) _ herr C D
    (hχ.smul contDiffOn_const) (hχ.smul contDiffOn_const)
  -- All four target factors equal one on L, while the prescribed symbol vanishes outside L.
  have hmask (z : X) (hz : z ∈ S) (η : X) :
      χ z • (χ z • (χ z • (χ z • j z η))) = j z η := by
    by_cases hy : Q.chart.symm z ∈ L
    · have hχz : χ z = 1 := by
        have h := hone _ hy
        rw [Q.chart.right_inv hz.1.1] at h
        exact h
      simp only [hχz, one_smul]
    · have hjz : j z η = 0 := by
        simp only [j, globalSymbolInChart, hzero _ hy, ContinuousLinearMap.zero_comp,
          ContinuousLinearMap.comp_zero]
      simp only [hjz, smul_zero]
  have hlocal : IsSymbol S (m - 1)
      (globalSymbolInChart G.Fiber H.Fiber Q.globalSymbolFunction Q.chart
        Q.input.frame Q.output.frame - j) := by
    apply IsSymbol.of_locally hS
    intro z hz
    by_cases hzs : z ∈ tsupport χ
    · refine ⟨S ∩ Ω, hS.inter hΩ, ⟨hz, hcut hzs⟩, Set.inter_subset_left, ?_⟩
      apply (hweighted.restrict Set.inter_subset_right).congr_on (hS.inter hΩ)
      intro y hy
      funext η
      simp only [Pi.sub_apply, matrixSymbol, C, D, cutoffMatrix, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]
      change χ y • (χ y • (Q.symbol y η -
        χ y • (χ y • matrixSymbol A B (cotangentSymbol t pLead) y η))) = _
      rw [← hcoordinates y hy.2 η]
      rw [Q.globalSymbolInChart_globalSymbolFunction y η hy.1]
      change χ y • (χ y • (Q.symbol y η - χ y • (χ y • j y η))) =
        ((Q.output.cutoff y * Q.input.cutoff y : ℝ) : ℂ) • Q.symbol y η - j y η
      rw [hsame, Complex.coe_smul, mul_smul, smul_sub, smul_sub, hmask y hy.1 η]
    · let W := S ∩ (tsupport χ)ᶜ
      have hW : IsOpen W := hS.inter (isClosed_tsupport χ).isOpen_compl
      refine ⟨W, hW, ⟨hz, hzs⟩, Set.inter_subset_left, ?_⟩
      apply (isSymbol_zero W (m - 1)).congr_on hW
      intro y hy
      funext η
      have hχzero : χ y = 0 := image_eq_zero_of_notMem_tsupport hy.2
      have hout : Q.chart.symm y ∉ L := by
        intro hyL
        have h := hone _ hyL
        rw [Q.chart.right_inv hy.1.1.1] at h
        exact zero_ne_one (hχzero.symm.trans h)
      rw [Pi.sub_apply, Pi.sub_apply,
        Q.globalSymbolInChart_globalSymbolFunction y η hy.1]
      have hχzero' : Q.input.cutoff y = 0 := hχzero
      simp only [hsame, hχzero', zero_mul, Complex.ofReal_zero, zero_smul,
        j, globalSymbolInChart, hzero _ hout, ContinuousLinearMap.zero_comp,
        ContinuousLinearMap.comp_zero, sub_zero, Pi.zero_apply]
  -- The common chart estimate globalizes because both actual symbols have compact base support.
  apply (globalPrincipalSymbolClass_eq_iff G.Fiber H.Fiber m Q.globalSymbol J).mpr
  let K := Q.chart.symm '' tsupport χ ∪ L
  have hK : IsCompact K := (Q.input.compact_support.image_of_continuousOn
    (Q.chart.continuousOn_symm.mono (fun z hz ↦ (Q.input.support_subset hz).1))).union hL
  have hKbase : K ⊆ Q.chart.source ∩ Q.input.frame.baseSet ∩ Q.output.frame.baseSet := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩ | hy
    · exact ⟨⟨Q.chart.map_target (Q.input.support_subset hz).1,
        (Q.input.support_subset hz).2⟩, Q.input_support_in_output_frame hz⟩
    · exact hLbase hy
  apply isGlobalSymbol_of_compactSupportInChart (m - 1) (Q.globalSymbolFunction - J.val)
    Q.chart Q.chart_mem_atlas Q.input.frame Q.output.frame K hK hKbase ?_ ?_
  · intro y hy η
    have hQzero := Q.globalSymbolFunction_eq_zero y
      (fun h ↦ hy (Or.inl ((Set.image_mono Set.inter_subset_right) h))) η
    simp only [Pi.sub_apply, hQzero, hzero y (fun h ↦ hy (Or.inr h)), sub_zero]
  · convert hlocal using 1
    ext z η v
    simp [globalSymbolInChart, j]

end OpenPiece

end AtiyahSinger
