/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CompactSymbolCoordinateFamilies
public import AtiyahSinger.Analysis.EquivariantSymbolJetFamilies
public import AtiyahSinger.Analysis.LinearFrequencyJetFamilies

/-!
# Compact orbits of original global symbol seminorms

Public module ID: M0600.

Fixed original charts and frames describe the moving geometric action on an
open parameter-and-space overlap. Their continuous spatial jets, and the actual
inverse cotangent matrices, give uniform symbol estimates on each compact
neighborhood. A finite cover of the group times the original compact test set
then bounds the exact global seminorm. The original weak group hypotheses are
retained throughout.
-/

@[expose] public noncomputable section
namespace AtiyahSinger

open Bundle IsManifold Manifold Set Topology
open scoped Manifold ContDiff
set_option maxSynthPendingDepth 20

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [MulAction G M] [ContinuousSMul G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
    ComplexBundle.EquivariantStructure G E)
  (τ : letI := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
    ComplexBundle.EquivariantStructure G F)

variable [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

variable [hG : IsManifold IG ∞ G]
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hτ : τ.IsSmooth (n := n) (r := q) IG)


omit hG in
include hM hσ hτ in
private theorem contDiffOn_equivariantSymbolCoordinateData
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f'] (g : G) :
    ContDiffOn ℝ ∞ (equivariantSymbolCoordinateData σ τ c d e e' f f' g)
      {x | x ∈ symbolChartDomain E F d e' f' ∧
        g⁻¹ • d.symm x ∈ c.source ∩ e.baseSet ∩ f.baseSet} := by
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := ComplexBundle.modelTopology (EuclideanSpace ℂ (Fin q)) F
  let (x : M) : FiniteDimensional ℂ (E x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin r)) E x
  let (x : M) : FiniteDimensional ℂ (F x) :=
    VectorBundle.finiteDimensional ℂ (EuclideanSpace ℂ (Fin q)) F x
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let I := 𝓘(ℝ, X)
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  intro x hx
  let old (z : X) := g⁻¹ • d.symm z
  have hbase := contMDiffAt_symm_of_mem_maximalAtlas hdM hx.1.1.1
  have hold : ContMDiffAt I I ∞ old x :=
    (Diffeomorph.smul (M := M) IG I ∞ g⁻¹).contMDiffAt.comp x hbase
  have hφ := (contMDiffAt_of_mem_maximalAtlas hcM hx.2.1.1).comp x hold
  have hfw : ContDiffAt ℝ ∞ (fun w ↦ d (g • c.symm w)) (c (old x)) := by
    have hc' := contMDiffAt_symm_of_mem_maximalAtlas hcM (c.map_source hx.2.1.1)
    have hmove := (Diffeomorph.smul (M := M) IG I ∞ g).contMDiffAt.comp (c (old x)) hc'
    have hreturn : g • c.symm (c (old x)) = d.symm x := by
      rw [c.left_inv hx.2.1.1]
      exact smul_inv_smul g (d.symm x)
    have hd' : g • c.symm (c (old x)) ∈ d.source := by
      rw [hreturn]
      exact d.map_target hx.1.1.1
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hd').comp (c (old x)) hmove).contDiffAt
  let J : (X →L[ℝ] X) ≃ₗᵢ[ℝ] (X →L[ℝ] X) := {
    toEquiv := (ContinuousLinearMap.adjoint : (X →L[ℝ] X) ≃ₗᵢ⋆[ℝ]
      (X →L[ℝ] X)).toEquiv
    map_add' := map_add ContinuousLinearMap.adjoint
    map_smul' := by intro t L; simp
    norm_map' := ContinuousLinearMap.adjoint.norm_map }
  have hΘ : ContDiffAt ℝ ∞
      (fun z ↦ (fderiv ℝ (fun w ↦ d (g • c.symm w)) (c (old z))).adjoint) x :=
    J.contDiff.contDiffAt.comp x ((hfw.fderiv_right (m := ∞) (by simp)).comp x hφ.contDiffAt)
  have hA : ContDiffAt ℝ ∞ (fun z : X ↦
      (f'.continuousLinearMapAt ℂ (g • old z)).comp
        ((τ.linearMap g (old z)).toContinuousLinearMap.comp (f.symmL ℂ (old z)))) x := by
    have hopen : IsOpen {z : G × M | z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} :=
      (f.open_baseSet.preimage continuous_snd).inter
        (f'.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hm : (g, old x) ∈ {z : G × M |
        z.2 ∈ f.baseSet ∧ z.1 • z.2 ∈ f'.baseSet} := by
      refine ⟨hx.2.2, ?_⟩
      change g • (g⁻¹ • d.symm x) ∈ f'.baseSet
      rw [smul_inv_smul]
      exact hx.1.2
    have h := (τ.contMDiffOn_frameMap IG hτ f f').contMDiffAt (hopen.mem_nhds hm)
    exact (h.comp x (contMDiffAt_const.prodMk hold)).contDiffAt
  have hB : ContDiffAt ℝ ∞ (fun z : X ↦
      (e.continuousLinearMapAt ℂ (old z)).comp
        ((σ.linearMap g⁻¹ (d.symm z)).toContinuousLinearMap.comp (e'.symmL ℂ (d.symm z)))) x := by
    have hopen : IsOpen {z : G × M | z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} :=
      (e'.open_baseSet.preimage continuous_snd).inter
        (e.open_baseSet.preimage (continuous_fst.smul continuous_snd))
    have hm : (g⁻¹, d.symm x) ∈ {z : G × M |
        z.2 ∈ e'.baseSet ∧ z.1 • z.2 ∈ e.baseSet} := ⟨hx.1.1.2, hx.2.1.2⟩
    have h := (σ.contMDiffOn_frameMap IG hσ e' e).contMDiffAt (hopen.mem_nhds hm)
    exact (h.comp x (contMDiffAt_const.prodMk hbase)).contDiffAt
  exact (hφ.contDiffAt.prodMk (hΘ.prodMk (hA.prodMk hB))).contDiffWithinAt

omit hG in
include IG hM in
private theorem isInvertible_equivariantSymbolCoordinateData
    (c d : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    (hc : c ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (hd : d ∈ atlas (EuclideanSpace ℝ (Fin n)) M)
    (e e' : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E))
    (f f' : Trivialization (EuclideanSpace ℂ (Fin q))
      (π (EuclideanSpace ℂ (Fin q)) F))
    [MemTrivializationAtlas e] [MemTrivializationAtlas e']
    [MemTrivializationAtlas f] [MemTrivializationAtlas f']
    (g : G) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ symbolChartDomain E F d e' f' ∧
      g⁻¹ • d.symm x ∈ c.source ∩ e.baseSet ∩ f.baseSet) :
    ((equivariantSymbolCoordinateData σ τ c d e e' f f' g x).2.1).IsInvertible := by
  let X := EuclideanSpace ℝ (Fin n)
  let I := 𝓘(ℝ, X)
  let D := Diffeomorph.smul (M := M) IG I ∞ g
  let t := c.symm.trans (D.toHomeomorph.toOpenPartialHomeomorph.trans d)
  have hcM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc
  have hdM := IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd
  have hxT : x ∈ t.target := ⟨⟨hx.1.1.1, mem_univ _⟩, hx.2.1.1⟩
  have he : ContDiffOn ℝ ∞ t t.source := by
    intro z hz
    have hsource := contMDiffAt_symm_of_mem_maximalAtlas hcM hz.1
    have hmove := D.contMDiffAt.comp z hsource
    exact ((contMDiffAt_of_mem_maximalAtlas hdM hz.2.2).comp z hmove).contDiffAt.contDiffWithinAt
  have hi : ContDiffOn ℝ ∞ t.symm t.target := by
    intro z hz
    have htarget := contMDiffAt_symm_of_mem_maximalAtlas hdM hz.1.1
    have hmove := D.symm.contMDiffAt.comp z htarget
    exact ((contMDiffAt_of_mem_maximalAtlas hcM hz.2).comp z hmove).contDiffAt.contDiffWithinAt
  have hsource := t.map_target hxT
  have hforward := (he.contDiffAt (t.open_source.mem_nhds hsource)).differentiableAt (by simp)
  have hbackward := (hi.contDiffAt (t.open_target.mem_nhds hxT)).differentiableAt (by simp)
  have hright : (fderiv ℝ t (t.symm x)).comp (fderiv ℝ t.symm x) =
      ContinuousLinearMap.id ℝ X := by
    apply (hforward.hasFDerivAt.comp x hbackward.hasFDerivAt).unique
    apply (hasFDerivAt_id x).congr_of_eventuallyEq
    filter_upwards [t.open_target.mem_nhds hxT] with y hy
    exact t.right_inv hy
  have hleft : (fderiv ℝ t.symm x).comp (fderiv ℝ t (t.symm x)) =
      ContinuousLinearMap.id ℝ X := by
    have hbackward' : HasFDerivAt t.symm (fderiv ℝ t.symm x) (t (t.symm x)) := by
      simpa only [t.right_inv hxT] using hbackward.hasFDerivAt
    apply (hbackward'.comp (t.symm x) hforward.hasFDerivAt).unique
    apply (hasFDerivAt_id (t.symm x)).congr_of_eventuallyEq
    filter_upwards [t.open_source.mem_nhds hsource] with y hy
    exact t.left_inv hy
  change ((fderiv ℝ t (t.symm x)).adjoint).IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse (g := (fderiv ℝ t.symm x).adjoint)
  · simpa only [X, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hleft
  · simpa only [X, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg ContinuousLinearMap.adjoint hright

variable [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F] [CompactSpace G] [T2Space G]

attribute [local instance] GlobalSymbolSeminormIndex.input_mem_atlas
  GlobalSymbolSeminormIndex.output_mem_atlas

omit [T2Space G] in
include hG hM hE hF hσ hτ in
/-- Every original global symbol seminorm is bounded on a compact geometric group orbit. -/
theorem bddAbove_range_globalSymbolSeminorm_equivariant
    (m : ℝ) (p : globalSymbolSpace (n := n) (r := r) (q := q) E F m)
    (J : GlobalSymbolSeminormIndex (n := n) (r := r) (q := q) E F) :
    BddAbove (range (fun g : G ↦ globalSymbolSeminorm E F m J
      (equivariantGlobalSymbolRepresentation IG σ τ hσ hτ m g p))) := by
  classical
  let X := EuclideanSpace ℝ (Fin n)
  let R := EuclideanSpace ℂ (Fin r)
  let Q := EuclideanSpace ℂ (Fin q)
  let H := R →L[ℂ] Q
  let Y := X × ((X →L[ℝ] X) × ((Q →L[ℂ] Q) × (R →L[ℂ] R)))
  let d := J.chart
  let e' := J.inputFrame
  let f' := J.outputFrame
  let K := J.localIndex.compactSet
  let i := J.localIndex.spatialOrder
  let j := J.localIndex.frequencyOrder
  let U := symbolChartDomain E F d e' f'
  have hU : IsOpen U := isOpen_symbolChartDomain E F d e' f'
  let target (g : G) := globalSymbolInChart E F
    (equivariantGlobalSymbolLinearMap IG σ τ g p.val) d e' f'
  -- Each moving point has a compact neighborhood using one fixed set of source frames.
  have hlocal (a : G × X) (ha : a ∈ univ ×ˢ K) :
      ∃ C : Set (G × X), IsCompact C ∧ a ∈ interior C ∧
        ∃ D : ℝ, 0 ≤ D ∧ ∀ g x, (g, x) ∈ C → ∀ ξ,
          ‖symbolDerivative (target g) i j x ξ‖ ≤ D * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
    let y₀ := a.1⁻¹ • d.symm a.2
    let c := chartAt X y₀
    let e := trivializationAt R E y₀
    let f := trivializationAt Q F y₀
    have hc : c ∈ atlas X M := chart_mem_atlas X y₀
    let W : Set (G × X) := {z | z.2 ∈ U ∧
      z.1⁻¹ • d.symm z.2 ∈ c.source ∩ e.baseSet ∩ f.baseSet}
    have hmove : ContinuousOn (fun z : G × X ↦ z.1⁻¹ • d.symm z.2) (univ ×ˢ U) :=
      continuous_fst.inv.continuousOn.smul (d.continuousOn_symm.comp
        continuous_snd.continuousOn (fun z hz ↦ hz.2.1.1))
    have hW : IsOpen W := by
      have h := hmove.isOpen_inter_preimage (isOpen_univ.prod hU)
        ((c.open_source.inter e.open_baseSet).inter f.open_baseSet)
      convert h using 1
      ext z
      simp only [W, mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, true_and, mem_preimage]
    have haW : a ∈ W := ⟨J.localIndex.subset_domain ha.2,
      ⟨⟨mem_chart_source X y₀, mem_baseSet_trivializationAt R E y₀⟩,
        mem_baseSet_trivializationAt Q F y₀⟩⟩
    obtain ⟨C, hC, haC, hCW⟩ := exists_compact_subset hW haW
    let data := equivariantSymbolCoordinateData σ τ c d e e' f f'
    have hd (g : G) : ContDiffOn ℝ ∞ (data g) {x | (g, x) ∈ W} :=
      contDiffOn_equivariantSymbolCoordinateData IG σ τ hσ hτ c d hc J.mem_atlas e e' f f' g
    have hdata (k : ℕ) : ContinuousOn
        (fun z : G × X ↦ iteratedFDeriv ℝ k (data z.1) z.2) W :=
      continuousOn_iteratedFDeriv_equivariantSymbolCoordinateData
        IG σ τ hσ hτ c d hc J.mem_atlas e e' f f' k
    have hds (z : G × X) (hz : z ∈ W) : ContDiffAt ℝ ∞ (data z.1) z.2 :=
      (hd z.1).contDiffAt ((hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds hz)
    have hdcont : ContinuousOn (fun z : G × X ↦ data z.1 z.2) W := by
      have h := (continuousMultilinearCurryFin0 ℝ X Y).continuous
        |>.comp_continuousOn (hdata 0)
      change ContinuousOn (fun z : G × X ↦ (iteratedFDeriv ℝ 0 (data z.1) z.2).curry0) W at h
      simpa only [ContinuousMultilinearMap.curry0_apply, iteratedFDeriv_zero_apply] using h
    let P : Y → X × (X →L[ℝ] X) := fun z ↦ (z.1, z.2.1)
    have hP : ContDiff ℝ ∞ P := contDiff_fst.prodMk contDiff_snd.fst
    let coordinates (g : G) (x : X) := P (data g x)
    have hcoordinates (g : G) : ContDiffOn ℝ ∞ (coordinates g) {x | (g, x) ∈ W} :=
      hP.comp_contDiffOn (hd g)
    have hcoordjets (k : ℕ) : ContinuousOn
        (fun z : G × X ↦ iteratedFDeriv ℝ k (coordinates z.1) z.2) W :=
      continuousOn_iteratedFDeriv_comp_family (fun _ : G ↦ P) data W
        (fun _ _ ↦ hP.contDiffAt) hds
        (fun a ↦ (hP.continuous_iteratedFDeriv (by simp)).comp_continuousOn hdcont) hdata k
    let φ (g : G) (x : X) := (coordinates g x).1
    let Θ (g : G) (x : X) := (coordinates g x).2
    let multiplier (z : Y) : H →L[ℝ] H :=
      ((ContinuousLinearMap.compL ℂ R Q Q z.2.2.1).comp
        ((ContinuousLinearMap.compL ℂ R R Q).flip z.2.2.2)).restrictScalars ℝ
    have hmultiplier : ContDiff ℝ ∞ multiplier := by
      let A : (Q →L[ℂ] Q) × (R →L[ℂ] R) → H →L[ℂ] H := fun z ↦
        (ContinuousLinearMap.compL ℂ R Q Q z.1).comp
          ((ContinuousLinearMap.compL ℂ R R Q).flip z.2)
      have hA : ContDiff ℂ ∞ A :=
        ((ContinuousLinearMap.compL ℂ R Q Q).contDiff.comp contDiff_fst).clm_comp
          ((ContinuousLinearMap.compL ℂ R R Q).flip.contDiff.comp contDiff_snd)
      exact ((ContinuousLinearMap.restrictScalarsL ℂ H H ℝ ℝ).contDiff.comp
        (hA.restrict_scalars ℝ)).comp contDiff_snd.snd
    let L (g : G) (x : X) : H →L[ℝ] H := multiplier (data g x)
    have hL (g : G) : ContDiffOn ℝ ∞ (L g) {x | (g, x) ∈ W} :=
      hmultiplier.comp_contDiffOn (hd g)
    have hLjets (k : ℕ) : ContinuousOn
        (fun z : G × X ↦ iteratedFDeriv ℝ k (L z.1) z.2) W :=
      continuousOn_iteratedFDeriv_comp_family (fun _ : G ↦ multiplier) data W
        (fun _ _ ↦ hmultiplier.contDiffAt) hds
        (fun a ↦ (hmultiplier.continuous_iteratedFDeriv (by simp)).comp_continuousOn hdcont)
        hdata k
    have hφU (z : G × X) (hz : z ∈ W) : φ z.1 z.2 ∈ symbolChartDomain E F c e f := by
      refine ⟨⟨c.map_source hz.2.1.1, ?_⟩, ?_⟩
      · change c.symm (c (z.1⁻¹ • d.symm z.2)) ∈ e.baseSet
        rw [c.left_inv hz.2.1.1]
        exact hz.2.1.2
      · change c.symm (c (z.1⁻¹ • d.symm z.2)) ∈ f.baseSet
        rw [c.left_inv hz.2.1.1]
        exact hz.2.2
    obtain ⟨D, hD, hDb⟩ := exists_bound_symbol_comp_of_isCompact_parameter
      (symbolChartDomain E F c e f) (isOpen_symbolChartDomain E F c e f) m
      (globalSymbolInChart E F p.val c e f) (p.property c hc e f)
      W C hW hC hCW φ Θ L (fun g ↦ (hcoordinates g).fst) (fun g ↦ (hcoordinates g).snd)
      hL (hdcont.fst) (hdcont.snd.fst) hφU
      (fun z hz ↦ isInvertible_equivariantSymbolCoordinateData IG σ τ c d hc J.mem_atlas
        e e' f f' z.1 z.2 hz)
      (fun k ↦ continuousOn_iteratedFDeriv_linear_frequency_family coordinates W hW
        hcoordinates hcoordjets k) hLjets i j
    refine ⟨C, hC, haC, D, hD, ?_⟩
    intro g x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (target g y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j
          (fun η ↦ L g y (globalSymbolInChart E F p.val c e f (φ g y) (Θ g y η))) ξ) := by
      filter_upwards [(hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds (hCW hx)]
        with y hy
      congr 1
      funext η
      exact equivariantGlobalSymbolInChart_eq IG σ τ g p.val c d hc J.mem_atlas
        e e' f f' y hy.1 hy.2 η
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [(hnear.iteratedFDeriv ℝ i).eq_of_nhds]
    exact hDb g x hx ξ
  -- Finitely many original coordinate neighborhoods cover the compact orbit test set.
  choose C hC haC D hD hDb using fun a : (univ : Set G) ×ˢ K ↦ hlocal a.val a.property
  obtain ⟨s, hs⟩ := (isCompact_univ.prod J.localIndex.isCompact).elim_finite_subcover
    (fun a : (univ : Set G) ×ˢ K ↦ interior (C a)) (fun _ ↦ isOpen_interior) (by
      intro a ha
      exact mem_iUnion.mpr ⟨⟨a, ha⟩, haC ⟨a, ha⟩⟩)
  let B : ℝ := ∑ a ∈ s, D a
  have hB : 0 ≤ B := Finset.sum_nonneg (fun a _ ↦ hD a)
  have hbound (g : G) (x : X) (hx : x ∈ K) (ξ : X) :
      ‖symbolDerivative (target g) i j x ξ‖ ≤ B * (1 + ‖ξ‖) ^ (m - (j : ℝ)) := by
    obtain ⟨a, has, ha⟩ := mem_iUnion₂.mp
      (hs (show (g, x) ∈ (univ : Set G) ×ˢ K from ⟨mem_univ g, hx⟩))
    apply (hDb a g x (interior_subset ha) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun a _ ↦ hD a) has
  refine ⟨B, ?_⟩
  rintro t ⟨g, rfl⟩
  change symbolSeminormValue hU m J.localIndex _ ≤ B
  unfold symbolSeminormValue
  by_cases hK : K.Nonempty
  · obtain ⟨x, hx⟩ := hK
    refine csSup_le ⟨_, x, hx, 0, rfl⟩ ?_
    rintro v ⟨x, hx, ξ, rfl⟩
    exact (div_le_iff₀ (Real.rpow_pos_of_pos (by positivity) _)).mpr (hbound g x hx ξ)
  · have hK' : K = ∅ := not_nonempty_iff_eq_empty.mp hK
    change sSup {t : ℝ | ∃ x ∈ K, ∃ ξ,
      t = ‖symbolDerivative (target g) i j x ξ‖ / (1 + ‖ξ‖) ^ (m - (j : ℝ))} ≤ B
    simpa only [hK', mem_empty_iff_false, false_and, exists_false, ofPred_false,
      Real.sSup_empty] using hB

end AtiyahSinger
