/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EquivariantSmoothSections
public import AtiyahSinger.Analysis.HermitianMetricL2
public import AtiyahSinger.Geometry.SmoothInvariantMetric
public import Mathlib.RepresentationTheory.Continuous.Basic

import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.Compact

/-!
# The geometric unitary action on the specified integral L² completion

Public module ID: M0532.

The original smooth section action extends uniquely to the existing
`SmoothHermitianMetric.L2SectionSpace` for the same explicit metric and measure.
Its integral norm uses exactly their pairing. Invariance of both chosen data is
an explicit hypothesis, matching the earlier metric and density constructions.
No fiber norm, inner-product instance, or presentation Sobolev norm is changed.

Sources: SG III.9, printed pp.211--212, with the integral Hilbert structure of
III.5, pp.194--195. The uniqueness and joint-continuity argument is the standard
dense isometric extension underlying the book's induced Hilbert-space action.
Group compactness is needed to produce invariant data by averaging, but is not
needed after those data are supplied. The given topological group inversion
suffices here; no smoothness of inversion or operator-norm continuity is asserted.
The original geometric action extends isometrically, and its joint strong
continuity is proved directly from the original integral metric.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.SmoothHermitianMetric

open Bundle ComplexBundle MeasureTheory
open scoped Manifold ContDiff Topology

variable {n r : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT2 : T2Space M] [hSC : SecondCountableTopology M] [hC : CompactSpace M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  (h : SmoothHermitianMetric (n := n) (r := r) E)
  [MeasurableSpace M] [BorelSpace M] (μ : Measure M)
  [hμ : IsSmoothPositiveMeasure (n := n) μ]

variable {V HG G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ V HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  [hG : IsManifold IG ∞ G] [MulAction G M] [ContinuousSMul G M]
  [hAction : ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    EquivariantStructure G E)
  (hσ : σ.IsSmooth (n := n) (r := r) IG)
  (hInvariant : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
    ∀ (g : G) (x : M) (u v : E x),
      h.pairing (g • x) (σ.linearMap g x u) (σ.linearMap g x v) = h.pairing x u v)
  (hμInvariant : ∀ g : G, Measure.map (fun x : M ↦ g • x) μ = μ)

include hM hT2 hSC hC hE hμ hG hAction hInvariant hμInvariant

/-- The original geometric action has a unique unitary extension to this integral completion. -/
theorem existsUnique_l2IsometryRepresentation :
    ∃! ρ : G →* (h.L2SectionSpace μ ≃ₗᵢ[ℂ] h.L2SectionSpace μ),
      ∀ (g : G) (u : smoothSections (n := n) (r := r) E),
        ρ g (h.smoothToL2 μ u) =
          h.smoothToL2 μ ((σ.smoothSectionRepresentation IG hσ g) u) := by
  /- Preserve the original integral norm by fixed-element change of variables.
  Then extend each inverse pair of smooth operators isometrically to the
  existing completion. The original dense smooth image determines its group
  laws and the uniqueness of the resulting representation. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let R := σ.smoothSectionRepresentation IG hσ
  let ι := h.smoothToL2 μ
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} hxy ↦ by
    subst y
    exact LinearMap.id
  have hpair_transport {x y : M} (hxy : x = y) (u v : E x) :
      h.pairing y (transport hxy u) (transport hxy v) = h.pairing x u v := by
    subst y
    rfl
  -- The same moving-fiber maps preserve the same original integral pairing.
  have hnorm (g : G) (u : smoothSections (n := n) (r := r) E) :
      ‖ι (R g u)‖ = ‖ι u‖ := by
    have hpoint (x : M) :
        h.pairing x ((R g u).val x) ((R g u).val x) =
          h.pairing (g⁻¹ • x) (u.val (g⁻¹ • x)) (u.val (g⁻¹ • x)) := by
      change h.pairing x
        (transport (smul_inv_smul g x) (σ.linearMap g (g⁻¹ • x) (u.val (g⁻¹ • x))))
        (transport (smul_inv_smul g x) (σ.linearMap g (g⁻¹ • x) (u.val (g⁻¹ • x)))) = _
      rw [hpair_transport]
      exact hInvariant g (g⁻¹ • x) _ _
    have hpreserving : MeasurePreserving (fun x : M ↦ g⁻¹ • x) μ μ :=
      ⟨(MeasurableEquiv.smul g⁻¹).measurable, hμInvariant g⁻¹⟩
    have hpair : h.sectionPairing μ (R g u) (R g u) = h.sectionPairing μ u u := by
      unfold sectionPairing
      simp_rw [hpoint]
      exact hpreserving.integral_comp (MeasurableEquiv.smul g⁻¹).measurableEmbedding
        (fun x : M ↦ h.pairing x (u.val x) (u.val x))
    have hsq : ‖ι (R g u)‖ ^ 2 = ‖ι u‖ ^ 2 := by
      change ‖h.smoothToL2 μ (R g u)‖ ^ 2 = ‖h.smoothToL2 μ u‖ ^ 2
      rw [h.norm_smoothToL2_sq, h.norm_smoothToL2_sq, hpair]
    nlinarith [norm_nonneg (ι (R g u)), norm_nonneg (ι u)]
  -- The inverse group element supplies the inverse smooth action before completion.
  let e (g : G) :
      smoothSections (n := n) (r := r) E ≃ₗ[ℂ]
        smoothSections (n := n) (r := r) E :=
    LinearEquiv.ofLinearMap (R g) (R g⁻¹)
      (by change R g * R g⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
      (by change R g⁻¹ * R g = 1; rw [← map_mul, inv_mul_cancel, map_one])
  let T (g : G) : h.L2SectionSpace μ ≃ₗᵢ[ℂ] h.L2SectionSpace μ :=
    (e g).extendOfIsometry ι ι (h.denseRange_smoothToL2 μ)
      (h.denseRange_smoothToL2 μ) (hnorm g)
  have hT (g : G) (u : smoothSections (n := n) (r := r) E) :
      T g (ι u) = ι (R g u) :=
    (e g).extendOfIsometry_eq ι ι (h.denseRange_smoothToL2 μ)
      (h.denseRange_smoothToL2 μ) (hnorm g) u
  -- Equality on that dense image proves the actual completed group laws.
  let ρ : G →* (h.L2SectionSpace μ ≃ₗᵢ[ℂ] h.L2SectionSpace μ) :=
    { toFun := T
      map_one' := by
        apply DFunLike.coe_injective
        apply (h.denseRange_smoothToL2 μ).equalizer (T 1).continuous continuous_id
        funext u
        change T 1 (ι u) = ι u
        rw [hT, map_one]
        rfl
      map_mul' := by
        intro g k
        apply DFunLike.coe_injective
        apply (h.denseRange_smoothToL2 μ).equalizer (T (g * k)).continuous
          ((T g).continuous.comp (T k).continuous)
        funext u
        change T (g * k) (ι u) = T g (T k (ι u))
        rw [hT, hT, hT, map_mul]
        rfl }
  refine ⟨ρ, hT, ?_⟩
  intro ρ' hρ'
  apply MonoidHom.ext
  intro g
  apply DFunLike.coe_injective
  apply (h.denseRange_smoothToL2 μ).equalizer (ρ' g).continuous (ρ g).continuous
  funext u
  exact (hρ' g u).trans (hT g u).symm

/-- The unitary representation on the already specified metric integral completion. -/
def l2IsometryRepresentation : G →* (h.L2SectionSpace μ ≃ₗᵢ[ℂ] h.L2SectionSpace μ) :=
  Classical.choose (h.existsUnique_l2IsometryRepresentation μ IG σ hσ
    hInvariant hμInvariant).exists

/-- The completed action retains the exact original geometric action on smooth sections. -/
theorem l2IsometryRepresentation_smoothToL2 (g : G)
    (u : smoothSections (n := n) (r := r) E) :
    h.l2IsometryRepresentation μ IG σ hσ hInvariant hμInvariant g (h.smoothToL2 μ u) =
      h.smoothToL2 μ ((σ.smoothSectionRepresentation IG hσ g) u) := by
  /- Read the defining dense-domain specification of the unique extension.
  Both inclusions refer to the same original section and the same h and μ;
  no identification with a presentation completion is inserted. -/
  exact (Classical.choose_spec (h.existsUnique_l2IsometryRepresentation μ IG σ hσ
    hInvariant hμInvariant).exists) g u

/-- The same unitary operators in the continuous-representation interface used by the index. -/
def l2ContRepresentation : ContRepresentation ℂ G (h.L2SectionSpace μ) := by
  let ρ := h.l2IsometryRepresentation μ IG σ hσ hInvariant hμInvariant
  exact ⟨
    { toFun := fun g ↦ (ρ g).toLinearIsometry.toContinuousLinearMap
      map_one' := by
        apply ContinuousLinearMap.ext
        intro u
        change ρ 1 u = u
        rw [map_one]
        rfl
      map_mul' := by
        intro g k
        apply ContinuousLinearMap.ext
        intro u
        change ρ (g * k) u = ρ g (ρ k u)
        rw [map_mul]
        rfl }⟩

/-- The actual unitary action is jointly continuous in the group and completed L² vector. -/
theorem continuous_l2ContRepresentation :
    Continuous (fun p : G × h.L2SectionSpace μ ↦
      h.l2ContRepresentation μ IG σ hσ hInvariant hμInvariant p.1 p.2) := by
  /- The original joint action and metric first give continuous integral
  matrix coefficients on smooth vectors. Their invariant Hilbert norms give
  continuous smooth-vector orbits. Density and the common isometry bound
  extend orbit continuity to all vectors and then give joint continuity.
  Only the base is compact; no local compactness of the group is used. -/
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let : TopologicalSpace (TotalSpace Unit (E ×ᵇ E)) := sumTopology
  let : MulAction G (TotalSpace Unit E) := σ.toMulAction
  let : IsFiniteMeasure μ := isFiniteMeasure_of_smoothPositiveMeasure (n := n) μ
  let R := σ.smoothSectionRepresentation IG hσ
  let ρ := h.l2IsometryRepresentation μ IG σ hσ hInvariant hμInvariant
  let ι := h.smoothToL2 μ
  have hsmooth (g : G) (u : smoothSections (n := n) (r := r) E) :
      ρ g (ι u) = ι (R g u) :=
    h.l2IsometryRepresentation_smoothToL2 μ IG σ hσ hInvariant hμInvariant g u
  -- A smooth section is continuous in the original modeled total topology.
  have hsection (u : smoothSections (n := n) (r := r) E) :
      Continuous (fun x : M ↦ (⟨x, u.val x⟩ : TotalSpace Unit E)) := by
    apply (continuous_model_section_iff (EuclideanSpace ℂ (Fin r)) E u.val).mpr
    rw [continuous_iff_continuousAt]
    intro x
    apply (FiberBundle.continuousAt_section (EuclideanSpace ℂ (Fin r)) x).mpr
    exact (u.property (trivializationAt (EuclideanSpace ℂ (Fin r)) E x)
      inferInstance).continuousOn.continuousAt
        ((trivializationAt (EuclideanSpace ℂ (Fin r)) E x).open_baseSet.mem_nhds
          (mem_baseSet_trivializationAt _ _ x))
  -- Equality of original total vectors accounts for the section action's fiber transport.
  let transport : ∀ {x y : M}, x = y → E x →ₗ[ℂ] E y := fun {x y} hxy ↦ by
    subst y
    exact LinearMap.id
  have htransport {x y : M} (hxy : x = y) (v : E x) :
      (⟨y, transport hxy v⟩ : TotalSpace Unit E) = ⟨x, v⟩ := by
    subst y
    rfl
  have htotal (g : G) (u : smoothSections (n := n) (r := r) E) (x : M) :
      (⟨x, (R g u).val x⟩ : TotalSpace Unit E) =
        g • (⟨g⁻¹ • x, u.val (g⁻¹ • x)⟩ : TotalSpace Unit E) := by
    change (⟨x, transport (smul_inv_smul g x)
      (σ.linearMap g (g⁻¹ • x) (u.val (g⁻¹ • x)))⟩ : TotalSpace Unit E) = _
    exact htransport (smul_inv_smul g x) _
  have htotal_cont (u : smoothSections (n := n) (r := r) E) :
      Continuous (fun p : G × M ↦ (⟨p.2, (R p.1 u).val p.2⟩ : TotalSpace Unit E)) := by
    have hsource : Continuous (fun p : G × M ↦
        (p.1, (⟨p.1⁻¹ • p.2, u.val (p.1⁻¹ • p.2)⟩ : TotalSpace Unit E))) :=
      continuous_fst.prodMk ((hsection u).comp (continuous_fst.inv.smul continuous_snd))
    apply (σ.continuous_action.comp hsource).congr
    intro p
    exact (htotal p.1 u p.2).symm
  -- Integration is bounded on C(M,ℂ) for the same finite measure.
  have hintegrable (f : C(M, ℂ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let integralMap : C(M, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ ∫ x, f x ∂μ
      map_add' := fun f k ↦ integral_add (hintegrable f) (hintegrable k)
      map_smul' := fun c f ↦ integral_smul c f }
  have hbound (f : C(M, ℂ)) : ‖integralMap f‖ ≤ μ.real Set.univ * ‖f‖ := by
    change ‖∫ x, f x ∂μ‖ ≤ μ.real Set.univ * ‖f‖
    simpa only [mul_comm] using norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall f.norm_coe_le_norm)
  let integralCLM : C(M, ℂ) →L[ℂ] ℂ := integralMap.mkContinuous (μ.real Set.univ) hbound
  -- Compact-base currying gives continuous integral matrix coefficients, with no group bounds.
  have hsmooth_orbit (u : smoothSections (n := n) (r := r) E) :
      Continuous (fun g : G ↦ ρ g (ι u)) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    have hcross : Continuous (fun p : G × M ↦
        h.pairing p.2 ((R p.1 u).val p.2) ((R g₀ u).val p.2)) := by
      have hdouble : Continuous (fun p : G × M ↦
          (⟨p.2, ((R p.1 u).val p.2, (R g₀ u).val p.2)⟩ :
            TotalSpace Unit (E ×ᵇ E))) := by
        apply continuous_induced_rng.mpr
        exact (htotal_cont u).prodMk ((hsection (R g₀ u)).comp continuous_snd)
      exact h.continuous_totalPairing.comp hdouble
    let F : G → C(M, ℂ) := fun g ↦
      ⟨fun x ↦ h.pairing x ((R g u).val x) ((R g₀ u).val x),
        hcross.comp (continuous_const.prodMk continuous_id)⟩
    have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F hcross
    have hinner : Continuous (fun g : G ↦ inner ℂ (ρ g (ι u)) (ρ g₀ (ι u))) := by
      have hpair : Continuous (fun g : G ↦ h.sectionPairing μ (R g u) (R g₀ u)) :=
        integralCLM.continuous.comp hF
      apply hpair.congr
      intro g
      rw [hsmooth, hsmooth]
      exact (h.inner_smoothToL2 μ (R g u) (R g₀ u)).symm
    have hsquare : Continuous (fun g : G ↦ ‖ρ g (ι u) - ρ g₀ (ι u)‖ ^ 2) := by
      have hscalar : Continuous (fun g : G ↦
          ‖ι u‖ ^ 2 - 2 * (inner ℂ (ρ g (ι u)) (ρ g₀ (ι u))).re + ‖ι u‖ ^ 2) :=
        (continuous_const.sub (continuous_const.mul
          (Complex.continuous_re.comp hinner))).add continuous_const
      apply hscalar.congr
      intro g
      rw [norm_sub_sq (𝕜 := ℂ), (ρ g).norm_map, (ρ g₀).norm_map]
      simp only [RCLike.re_eq_complex_re]
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    have hnear : ∀ᶠ g in 𝓝 g₀, ‖ρ g (ι u) - ρ g₀ (ι u)‖ ^ 2 < ε ^ 2 :=
      hsquare.continuousAt.eventually (gt_mem_nhds (by simpa using sq_pos_of_pos hε))
    filter_upwards [hnear] with g hg
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (ρ g (ι u) - ρ g₀ (ι u))]
  -- One dense smooth approximation controls both errors uniformly in the group element.
  have horbit (u : h.L2SectionSpace μ) : Continuous (fun g : G ↦ ρ g u) := by
    rw [continuous_iff_continuousAt]
    intro g₀
    apply Metric.continuousAt_iff'.mpr
    intro ε hε
    obtain ⟨v, hv⟩ := (h.denseRange_smoothToL2 μ).exists_dist_lt u
      (show 0 < ε / 3 by positivity)
    have hnear : ∀ᶠ g in 𝓝 g₀, dist (ρ g (ι v)) (ρ g₀ (ι v)) < ε / 3 :=
      Metric.continuousAt_iff'.mp (hsmooth_orbit v).continuousAt (ε / 3) (by positivity)
    filter_upwards [hnear] with g hg
    calc
      dist (ρ g u) (ρ g₀ u) ≤
          dist (ρ g u) (ρ g (ι v)) + dist (ρ g (ι v)) (ρ g₀ u) := dist_triangle _ _ _
      _ ≤ dist (ρ g u) (ρ g (ι v)) +
          (dist (ρ g (ι v)) (ρ g₀ (ι v)) + dist (ρ g₀ (ι v)) (ρ g₀ u)) :=
        add_le_add le_rfl (dist_triangle _ _ _)
      _ = dist u (ι v) + (dist (ρ g (ι v)) (ρ g₀ (ι v)) + dist u (ι v)) := by
        rw [(ρ g).isometry.dist_eq, (ρ g₀).isometry.dist_eq, dist_comm (ι v) u]
      _ < ε := by linarith
  -- Split the joint variation into a vector change and the orbit of one fixed vector.
  change Continuous (fun p : G × h.L2SectionSpace μ ↦ ρ p.1 p.2)
  rw [continuous_iff_continuousAt]
  intro p₀
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hvector : ∀ᶠ p : G × h.L2SectionSpace μ in 𝓝 p₀, dist p.2 p₀.2 < ε / 2 :=
    Metric.continuousAt_iff'.mp continuous_snd.continuousAt (ε / 2) (by positivity)
  have hgroup : ∀ᶠ p : G × h.L2SectionSpace μ in 𝓝 p₀,
      dist (ρ p.1 p₀.2) (ρ p₀.1 p₀.2) < ε / 2 :=
    Metric.continuousAt_iff'.mp ((horbit p₀.2).comp continuous_fst).continuousAt
      (ε / 2) (by positivity)
  filter_upwards [hvector, hgroup] with p hpvector hpgroup
  calc
    dist (ρ p.1 p.2) (ρ p₀.1 p₀.2) ≤
        dist (ρ p.1 p.2) (ρ p.1 p₀.2) + dist (ρ p.1 p₀.2) (ρ p₀.1 p₀.2) :=
      dist_triangle _ _ _
    _ = dist p.2 p₀.2 + dist (ρ p.1 p₀.2) (ρ p₀.1 p₀.2) := by
      rw [(ρ p.1).isometry.dist_eq]
    _ < ε := by linarith

end AtiyahSinger.SmoothHermitianMetric
