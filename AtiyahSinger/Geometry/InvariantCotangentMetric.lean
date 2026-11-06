/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.CotangentMetric
public import AtiyahSinger.Geometry.EquivariantCotangentAction

import AtiyahSinger.Geometry.CompactParameterIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Invariant smooth metrics on the original cotangent bundle

Public module ID: M1283.

A compact Hausdorff group with a finite-dimensional smooth model, acting
smoothly on a Hausdorff second-countable finite-dimensional manifold, admits
an invariant smooth metric on its original cotangent bundle. The conclusion fixes
the existing inverse-differential lift and the native Riemannian metric type;
it does not replace the cotangent topology or choose a new fiber norm.

This is the real cotangent version of the compact-group averaging in SG III.9,
pp.211--214. It supplies invariant radial coordinates for the equivariant
extension of III.13 Lemma 13.3. The precise native-bundle formulation is a
standard supplement, not a separately numbered theorem in the book.
The base need not be compact. Smoothness of group inversion is unnecessary:
the given jointly smooth action already gives the smooth cotangent lift.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle MeasureTheory Set
open scoped Manifold ContDiff Topology

variable {V HG : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [hV : FiniteDimensional ℝ V] [TopologicalSpace HG]
  (IG : ModelWithCorners ℝ V HG)
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hTG : T2Space G] [hCG : CompactSpace G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G]
  {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hS : SecondCountableTopology M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]

set_option maxSynthPendingDepth 30 in
set_option synthInstance.maxHeartbeats 200000 in

set_option linter.unusedSectionVars false in
-- The group model is finite-dimensional in this formulation.
set_option maxHeartbeats 4000000 in

include hV hTG hCG hG hM hT hS in
/-- A smooth cotangent metric invariant under the given original inverse-differential action. -/
theorem exists_invariant_smoothCotangentMetric :
    ∃ h : SmoothCotangentMetric (n := n) (M := M),
      ∀ (g : G) (x : M) (ξ η : CotangentFiber (n := n) x),
        h.inner (g • x)
            (cotangentDiffeomorphMap
              (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
              ⟨x, ξ⟩).snd
            (cotangentDiffeomorphMap
              (Diffeomorph.smul (M := M) IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ g)
              ⟨x, η⟩).snd = h.inner x ξ η := by
  /- Average the original lifted scalar pairing, then prove smoothness in native local
  Hom coordinates. The same total-space action law and right Haar invariance give the
  final invariance identity; the original cotangent topology is retained throughout. -/
  classical
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let E := CotangentFiber (n := n) (M := M)
  let F := CotangentModel n
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let μ := Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts G)
  let : IsProbabilityMeasure μ := ⟨Measure.haarMeasure_self⟩
  let : μ.IsMulRightInvariant := ⟨fun g ↦
    Measure.isHaarMeasure_eq_of_isProbabilityMeasure (μ.map (· * g)) μ⟩
  obtain ⟨h⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
  let := smoothCotangentMulAction (n := n) (G := G) (M := M) IG
  let := contMDiffSMul_smoothCotangent (n := n) (G := G) (M := M) IG
  let L (g : G) (x : M) : E x →ₗ[ℝ] E (g • x) :=
    { toFun ξ := ξ.comp (mfderiv I I
        (Diffeomorph.smul (M := M) IG I ∞ g).symm (g • x))
      map_add' ξ η := by ext v; rfl
      map_smul' a ξ := by ext v; rfl }
  have hlift (g : G) (x : M) (ξ : E x) :
      (g • (⟨x, ξ⟩ : TotalSpace F E)) = ⟨g • x, L g x ξ⟩ := rfl
  let P (g : G) (x : M) (ξ η : E x) : ℝ := h.inner (g • x) (L g x ξ) (L g x η)
  -- Smoothness is checked on the original bundle, with both vectors over the same moving base.
  have hp (x : M) (ξ η : E x) : Continuous (fun g : G ↦ P g x ξ η) := by
    have hξ : ContMDiff IG (I.prod 𝓘(ℝ, F)) ∞
        (fun g : G ↦ (⟨g • x, L g x ξ⟩ : TotalSpace F E)) := by
      change ContMDiff IG (I.prod 𝓘(ℝ, F)) ∞
        (fun g : G ↦ g • (⟨x, ξ⟩ : TotalSpace F E))
      exact contMDiff_smul.comp (contMDiff_id.prodMk contMDiff_const)
    have hη : ContMDiff IG (I.prod 𝓘(ℝ, F)) ∞
        (fun g : G ↦ (⟨g • x, L g x η⟩ : TotalSpace F E)) := by
      change ContMDiff IG (I.prod 𝓘(ℝ, F)) ∞
        (fun g : G ↦ g • (⟨x, η⟩ : TotalSpace F E))
      exact contMDiff_smul.comp (contMDiff_id.prodMk contMDiff_const)
    have hb : ContMDiff IG I ∞ (fun g : G ↦ g • x) :=
      contMDiff_smul.comp (contMDiff_id.prodMk contMDiff_const)
    have hs : ContMDiff IG (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun g : G ↦ (⟨g • x, P g x ξ η⟩ : TotalSpace ℝ (Bundle.Trivial M ℝ))) :=
      (h.contMDiff.comp hb).clm_bundle_apply₂ hξ hη
    apply continuous_iff_continuousAt.mpr
    intro g
    have hc := (contMDiffAt_totalSpace.mp (hs g)).2.continuousAt
    simpa using hc
  have hint (x : M) (ξ η : E x) : Integrable (fun g : G ↦ P g x ξ η) μ :=
    (hp x ξ η).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let : ∀ x, FiniteDimensional ℝ (E x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F E x).symm.toLinearEquiv.finiteDimensional
  let : ∀ x, IsNormableSpace ℝ (E x) := fun x ↦
    (VectorBundle.continuousLinearEquivAt ℝ F E x).isNormableSpace
  -- Scalar integration preserves the two linear variables; continuity follows in finite dimension.
  let qL (x : M) : E x →ₗ[ℝ] E x →ₗ[ℝ] ℝ :=
    { toFun ξ :=
        { toFun η := ∫ g, P g x ξ η ∂μ
          map_add' η ζ := by
            simp only [P, map_add]
            exact integral_add (hint x ξ η) (hint x ξ ζ)
          map_smul' a η := by
            simp only [P, map_smul, smul_eq_mul]
            exact integral_const_mul a _ }
      map_add' ξ ζ := by
        ext η
        simp only [P, map_add, add_apply, LinearMap.coe_mk,
          AddHom.coe_mk, LinearMap.add_apply]
        exact integral_add (hint x ξ η) (hint x ζ η)
      map_smul' a ξ := by
        ext η
        simp only [P, map_smul, smul_apply, smul_eq_mul,
          LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        exact integral_const_mul a _ }
  let q (x : M) : E x →L[ℝ] E x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E x) (F' := E x →L[ℝ] ℝ)
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E x) (F' := ℝ)).toLinearMap.comp
        (qL x))
  have hq (x : M) (ξ η : E x) : q x ξ η = ∫ g, P g x ξ η ∂μ := rfl
  have hsymm (x : M) (ξ η : E x) : q x ξ η = q x η ξ := by
    simp only [hq, P, h.symm]
  have hpos (x : M) (ξ : E x) (hξ : ξ ≠ 0) : 0 < q x ξ ξ := by
    have hinj (g : G) : L g x ξ ≠ 0 := by
      intro hz
      have heq : g • (⟨x, ξ⟩ : TotalSpace F E) = g • (⟨x, 0⟩ : TotalSpace F E) := by
        rw [hlift, hlift, hz, map_zero]
      exact hξ (TotalSpace.mk_injective x ((MulAction.injective g) heq))
    have hpositive (g : G) : 0 < P g x ξ ξ := h.pos _ _ (hinj g)
    rw [hq]
    exact integral_pos_of_integrable_nonneg_nonzero (hp x ξ ξ) (hint x ξ ξ)
      (fun g ↦ (hpositive g).le) (hpositive 1).ne'
  have hsmooth : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ) x (q x)) := by
    -- Finite-dimensional operator coordinates are smooth once all scalar evaluations are smooth.
    have hclm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
        {f : G × M → F →L[ℝ] W} {s : Set (G × M)}
        (hf : ∀ v, ContMDiffOn (IG.prod I) 𝓘(ℝ, W) ∞ (fun p ↦ f p v) s) :
        ContMDiffOn (IG.prod I) 𝓘(ℝ, F →L[ℝ] W) ∞ f s := by
      let d := Module.finrank ℝ F
      let e₁ : F ≃L[ℝ] (Fin d → ℝ) :=
        ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun ℝ).symm
      let e₂ := (e₁.arrowCongr (1 : W ≃L[ℝ] W)).trans
        (ContinuousLinearEquiv.piRing (Fin d))
      rw [← Function.id_comp f, ← e₂.symm_comp_self]
      exact e₂.symm.contDiff.contMDiff.comp_contMDiffOn
        (contMDiffOn_pi_space.mpr fun i ↦ hf _)
    intro x
    let e := trivializationAt F E x
    let t := trivializationAt ℝ (Bundle.Trivial M ℝ) x
    let d := e.continuousLinearMap (RingHom.id ℝ) t
    let f := e.continuousLinearMap (RingHom.id ℝ) d
    have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt _ _ _
    let Φ (p : G × M) : F →L[ℝ] F →L[ℝ] ℝ :=
      (h.inner (p.1 • p.2)).bilinearComp
        ((L p.1 p.2).toContinuousLinearMap.comp (e.symmL ℝ p.2))
        ((L p.1 p.2).toContinuousLinearMap.comp (e.symmL ℝ p.2))
    have hΦ : ContMDiffOn (IG.prod I) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
        Φ (univ ×ˢ e.baseSet) := by
      apply hclm
      intro u
      apply hclm
      intro v
      have hvectors (w : F) : ContMDiffOn (IG.prod I) (I.prod 𝓘(ℝ, F)) ∞
          (fun p : G × M ↦ (⟨p.1 • p.2,
            L p.1 p.2 (e.symmL ℝ p.2 w)⟩ : TotalSpace F E)) (univ ×ˢ e.baseSet) := by
        have hw : ContMDiffOn I (I.prod 𝓘(ℝ, F)) ∞
            (fun y ↦ (⟨y, e.symmL ℝ y w⟩ : TotalSpace F E)) e.baseSet := by
          apply (e.contMDiffOn_section_iff e.open_baseSet (subset_rfl)).mpr
          apply (contMDiffOn_const (c := w)).congr
          intro y hy
          simp only [e.symmL_apply hy, e.apply_mk_symm hy]
        change ContMDiffOn (IG.prod I) (I.prod 𝓘(ℝ, F)) ∞
          (fun p : G × M ↦ p.1 • (⟨p.2, e.symmL ℝ p.2 w⟩ : TotalSpace F E))
          (univ ×ˢ e.baseSet)
        exact contMDiff_smul.comp_contMDiffOn
          (contMDiffOn_fst.prodMk (hw.comp contMDiffOn_snd (fun _ hp ↦ hp.2)))
      have hb : ContMDiff (IG.prod I) I ∞ (fun p : G × M ↦ p.1 • p.2) :=
        contMDiff_smul
      have hpair : ContMDiffOn (IG.prod I) (I.prod 𝓘(ℝ, ℝ)) ∞
          (fun p : G × M ↦ (⟨p.1 • p.2, Φ p u v⟩ :
            TotalSpace ℝ (Bundle.Trivial M ℝ))) (univ ×ˢ e.baseSet) :=
        (h.contMDiff.comp hb).contMDiffOn.clm_bundle_apply₂ (hvectors u) (hvectors v)
      intro p hp
      have heval := (contMDiffWithinAt_totalSpace.mp (hpair p hp)).2
      simpa using heval
    -- Differentiate the entire coordinate bilinear form under the same compact Haar integral.
    let c := chartAt (EuclideanSpace ℝ (Fin n)) x
    let s := c.target ∩ c.symm ⁻¹' e.baseSet
    have hs : IsOpen s := c.isOpen_inter_preimage_symm e.open_baseSet
    have hcx : c x ∈ s := ⟨c.map_source (mem_chart_source _ x), by
      simpa only [Set.mem_preimage, c,
        OpenPartialHomeomorph.left_inv _ (mem_chart_source _ x)] using hx⟩
    have hchart : ContMDiffOn (IG.prod I) 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ) ∞
        (fun p : G × EuclideanSpace ℝ (Fin n) ↦ Φ (p.1, c.symm p.2))
        (univ ×ˢ s) := by
      apply hΦ.comp
        (contMDiffOn_fst.prodMk ((contMDiffOn_chart_symm (I := I) (x := x)).comp
          contMDiffOn_snd (fun _ hp ↦ hp.2.1)))
      intro p hp
      exact ⟨mem_univ _, hp.2.2⟩
    have havg : ContDiffOn ℝ ∞
        (fun y : EuclideanSpace ℝ (Fin n) ↦ ∫ g : G, Φ (g, c.symm y) ∂μ) s :=
      contDiffOn_integral_of_compact_manifold IG μ hs hchart
    have hlocal := (havg.contMDiffOn.contMDiffAt (hs.mem_nhds hcx)).comp x
      (contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := I) x)
        (mem_chart_source _ x))
    -- Evaluation commutes with integration, so these coordinates represent exactly q.
    apply (f.contMDiffAt_section_iff (show x ∈ f.baseSet from ⟨hx, hx, by simp [t]⟩)).mpr
    apply hlocal.congr_of_eventuallyEq
    filter_upwards [c.open_source.mem_nhds (mem_chart_source _ x),
      e.open_baseSet.mem_nhds hx] with y hy hey
    simp only [Function.comp_apply, c.left_inv hy]
    have hcont : Continuous (fun g : G ↦ Φ (g, y)) :=
      continuousOn_univ.mp (hΦ.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun g _ ↦ ⟨mem_univ g, hey⟩))
    have hintΦ : Integrable (fun g : G ↦ Φ (g, y)) μ :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    ext u v
    rw [ContinuousLinearMap.integral_apply hintΦ]
    have hintu : Integrable (fun g : G ↦ Φ (g, y) u) μ :=
      (ContinuousLinearMap.apply ℝ (F →L[ℝ] ℝ) u).integrable_comp hintΦ
    rw [ContinuousLinearMap.integral_apply hintu]
    rw [show f = e.continuousLinearMap (RingHom.id ℝ) d from rfl,
      Trivialization.continuousLinearMap_apply]
    simp only [ContinuousLinearMap.comp_apply]
    rw [d.continuousLinearMapAt_apply_of_mem ℝ ⟨hey, by simp [t]⟩]
    change (t.continuousLinearMapAt ℝ y)
      (q y (e.symmL ℝ y u) (e.symmL ℝ y v)) = ∫ g, Φ (g, y) u v ∂μ
    have ht : t.continuousLinearMapAt ℝ y = ContinuousLinearMap.id ℝ ℝ := by
      change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ y = _
      exact Bundle.Trivial.continuousLinearMapAt_trivialization _ _ _ _
    rw [ht, ContinuousLinearMap.id_apply, hq]
    rfl
  have hbounded (x : M) : Bornology.IsVonNBounded ℝ {ξ : E x | q x ξ ξ < 1} := by
    let core : InnerProductSpace.Core ℝ (ULift.{0} (E x)) :=
      { inner u v := q x u.down v.down
        conj_inner_symm u v := hsymm x v.down u.down
        re_inner_nonneg v := by
          by_cases hv : v.down = 0
          · simp [hv]
          · exact (hpos x v.down hv).le
        add_left u v w := by simp
        smul_left a u v := by simp
        definite v h := by
          have hv : v.down = 0 := by
            by_contra hv
            exact (ne_of_gt (hpos x v.down hv)) h
          exact ULift.ext hv }
    let : InnerProductSpace.Core ℝ (ULift.{0} (E x)) := core
    let t : TopologicalSpace (ULift.{0} (E x)) :=
      core.toNormedAddCommGroup.toMetricSpace.toUniformSpace.toTopologicalSpace
    let : NormedAddCommGroup (ULift.{0} (E x)) := core.toNormedAddCommGroup
    let : NormedSpace ℝ (ULift.{0} (E x)) :=
      InnerProductSpace.Core.toNormedSpace
    let : InnerProductSpace ℝ (ULift.{0} (E x)) :=
      InnerProductSpace.ofCore core.toCore
    let : FiniteDimensional ℝ (ULift.{0} (E x)) :=
      (ULift.moduleEquiv (R := ℝ) (M := E x)).symm.finiteDimensional
    -- Finite-dimensional linear equivalence transfers the bounded unit ball to the original fiber.
    let e : ULift.{0} (E x) ≃L[ℝ] E x :=
      (ULift.moduleEquiv (R := ℝ) (M := E x)).toContinuousLinearEquiv
    have hball : Bornology.IsVonNBounded ℝ
        (Metric.ball (0 : ULift.{0} (E x)) 1) :=
      (NormedSpace.isVonNBounded_iff ℝ).mpr Metric.isBounded_ball
    have himage := hball.image e.toContinuousLinearMap
    have hset : e '' Metric.ball (0 : ULift.{0} (E x)) 1 =
        {v : E x | q x v v < 1} := by
      ext v
      simp only [Set.mem_image, Metric.mem_ball, dist_zero_right, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hnorm : inner ℝ u u = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
        change q x u.down u.down = ‖u‖ ^ 2 at hnorm
        change q x u.down u.down < 1
        nlinarith [norm_nonneg u]
      · intro hv
        refine ⟨ULift.up v, ?_, rfl⟩
        have hnorm : inner ℝ (ULift.up v) (ULift.up v) =
            ‖(ULift.up v : ULift.{0} (E x))‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
        change q x v v = ‖(ULift.up v : ULift.{0} (E x))‖ ^ 2 at hnorm
        nlinarith [norm_nonneg (ULift.up v : ULift.{0} (E x))]
    change Bornology.IsVonNBounded ℝ
      (e '' Metric.ball (0 : ULift.{0} (E x)) 1) at himage
    rwa [hset] at himage
  refine ⟨{ inner := q
            symm := hsymm
            pos := hpos
            isVonNBounded := hbounded
            contMDiff := hsmooth }, ?_⟩
  intro g x ξ η
  change q (g • x) (L g x ξ) (L g x η) = q x ξ η
  rw [hq, hq]
  have hpair {y z : M} {u v : E y} {u' v' : E z}
      (hu : (⟨y, u⟩ : TotalSpace F E) = ⟨z, u'⟩)
      (hv : (⟨y, v⟩ : TotalSpace F E) = ⟨z, v'⟩) :
      h.inner y u v = h.inner z u' v' := by
    obtain ⟨hyz, huu⟩ := TotalSpace.mk.inj hu
    cases hyz
    have huu' := eq_of_heq huu
    have hvv := TotalSpace.mk_injective y hv
    rw [huu', hvv]
  have hmul (a : G) : P a (g • x) (L g x ξ) (L g x η) = P (a * g) x ξ η := by
    exact hpair ((mul_smul a g (⟨x, ξ⟩ : TotalSpace F E)).symm)
      ((mul_smul a g (⟨x, η⟩ : TotalSpace F E)).symm)
  simp_rw [hmul]
  exact integral_mul_right_eq_self (μ := μ) (fun a ↦ P a x ξ η) g

end AtiyahSinger
