/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.CosphereFamilies

import AtiyahSinger.Topology.FiberBundleTopology
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.Topology.TietzeExtension

/-!
# The compact-open topology on continuous cosphere sections

Public module ID: M0413.

Continuous sections embed in actual continuous maps to the Hom total space.
The induced compact-open topology is used for C-zero homotopies and open
invertibility. It does not assume that the original fiber norms vary continuously.
On compact Hausdorff second-countable bases, smooth approximation is a density theorem,
not supplied as a field of a data structure. The continuous-topology exponential law
and interpolation path, smooth inclusion, and smooth density are proved below.
This is a project supplement to
SG III.7.10--7.11. Parametric differentiability is not required.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Function IsManifold MeasureTheory Set Topology
open scoped Manifold ContDiff ComplexConjugate Topology

set_option maxSynthPendingDepth 20


set_option linter.unusedSectionVars false

variable {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  {F : M → Type*}
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hE : IsSmoothComplexBundle (n := n) (r := r) E]
  [hF : IsSmoothComplexBundle (n := n) (r := q) F]

variable (g : SmoothCotangentMetric (n := n) (M := M))

/-- Continuous sections of the pulled-back Hom bundle over the cosphere. -/
abbrev ContinuousCosphereSymbol : Type _ :=
  {a : CosphereSymbolFunction (E := E) (F := F) g //
    IsContinuousCosphereSymbol (r := r) (q := q) g a}

/-- The actual continuous Hom total-space map associated with a continuous section. -/
def continuousCosphereSymbolMap (a : ContinuousCosphereSymbol (r := r) (q := q)
      (E := E) (F := F) g) :
    C(CosphereBundle g, TotalSpace
      (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)) (fun x ↦ E x →L[ℂ] F x)) :=
  ⟨cosphereSymbolTotal (r := r) (q := q) g a.val, a.property⟩

/-- Compact-open convergence of the actual total-space sections. -/
@[instance_reducible]
def continuousCosphereSymbolTopology :
    TopologicalSpace (ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g) :=
  TopologicalSpace.induced (continuousCosphereSymbolMap (r := r) (q := q) g) inferInstance

attribute [local instance] continuousCosphereSymbolTopology smoothCosphereSymbolTopology

/-- The inclusion of smooth sections into continuous sections. -/
def smoothCosphereToContinuous (a : smoothCosphereSymbolSpace (r := r) (q := q)
      (E := E) (F := F) g) :
    ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g :=
  ⟨a.val, IsSmoothCosphereSymbol.continuous g a.property⟩

/-- Affine interpolation as a path of actual continuous sections. -/
def continuousCosphereInterpolation
    (a b : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g)
    (t : unitInterval) : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g :=
  ⟨cosphereInterpolation g a.val b.val t,
    IsContinuousCosphereFamily.slice g
      (isContinuousCosphereFamily_interpolation g a.val b.val a.property b.property) t⟩

/-- The total-space-map inclusion is injective. -/
theorem continuousCosphereSymbolMap_injective :
    Function.Injective (continuousCosphereSymbolMap (r := r) (q := q) (E := E) (F := F) g) := by
  /- Equality of bundled continuous maps gives equality of their
  values. The common base projection lets total-space equality recover equality in
  each Hom fiber. Apply dependent function and subtype extensionality. -/
  intro a b h
  apply Subtype.ext
  funext z
  have hz := DFunLike.congr_fun h z
  exact (TotalSpace.mk_injective z.val.proj) hz

/-- Smooth-to-continuous inclusion retains the underlying section. -/
theorem smoothCosphereToContinuous_injective :
    Function.Injective (smoothCosphereToContinuous (r := r) (q := q) (E := E) (F := F) g) := by
  /- The map forgets only a smoothness certificate and retains the
  actual dependent Hom function. Equality of these functions identifies the two smooth subtypes. -/
  intro a b hab
  -- Forgetting a certificate retains exactly the same dependent section function.
  apply Subtype.ext
  exact congrArg (fun c : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g ↦
    c.val) hab

/-- Smooth convergence implies compact-open convergence of sections. -/
theorem continuous_smoothCosphereToContinuous :
    Continuous (smoothCosphereToContinuous (r := r) (q := q) (E := E) (F := F) g) := by
  /- Joint evaluation of the original smooth sections is continuous by the
  mixed derivative seminorm estimate. Currying gives the compact-open continuity
  of their original total-space maps; the induced section topology retains it. -/
  rw [continuous_induced_rng]
  apply ContinuousMap.continuous_of_continuous_uncurry
  -- This direction of the compact-open exponential law needs no separation hypothesis.
  exact isContinuousCosphereFamily_of_continuous g
    (fun a : smoothCosphereSymbolSpace (r := r) (q := q) (E := E) (F := F) g ↦ a)
    continuous_id

/-- Continuous-section paths are exactly jointly continuous total-space families. -/
theorem continuous_cosphere_iff [T2Space M] {Z : Type*} [TopologicalSpace Z]
    (a : Z → ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g) :
    Continuous a ↔ IsContinuousCosphereFamily (r := r) (q := q) g (fun z ↦ (a z).val) := by
  /- The cosphere is a closed subset of a locally compact Hausdorff
  finite-dimensional bundle, hence locally compact. Use the compact-open exponential
  law and the induced topology. The fixed-base condition is retained on both sides. -/
  -- The same native cotangent atlas gives a finite-dimensional locally compact model.
  let : LocallyCompactSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) :=
    inferInstanceAs (LocallyCompactSpace
      (EuclideanSpace ℝ (Fin n) × CotangentModel n))
  let : LocallyCompactSpace (CotangentTotalSpace (n := n) (M := M)) :=
    ChartedSpace.locallyCompactSpace
      (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) _
  let : LocallyCompactSpace (CosphereBundle g) := g.isClosed_cosphere.locallyCompactSpace
  -- The induced topology keeps precisely the compact-open continuity of the original maps.
  change Continuous a ↔ Continuous (fun p : Z × CosphereBundle g ↦
    continuousCosphereSymbolMap (r := r) (q := q) g (a p.1) p.2)
  rw [continuous_induced_rng]
  exact ⟨fun h ↦ ContinuousMap.continuous_uncurry_of_continuous ⟨_, h⟩,
    fun h ↦ ContinuousMap.continuous_of_continuous_uncurry
      (continuousCosphereSymbolMap (r := r) (q := q) g ∘ a) h⟩

/-- The canonical interpolation is continuous in the compact-open section topology. -/
theorem continuous_continuousCosphereInterpolation [T2Space M]
    (a b : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g) :
    Continuous (continuousCosphereInterpolation g a b) := by
  /- Use the joint-continuity theorem for affine interpolation and
  continuous_cosphere_iff. This is a continuity statement only; invertibility requires
  an additional small-neighborhood hypothesis supplied in CosphereEllipticity. -/
  apply (continuous_cosphere_iff g _).mpr
  exact isContinuousCosphereFamily_interpolation g a.val b.val a.property b.property

/-- Continuous interpolation has the prescribed first endpoint. -/
theorem continuousCosphereInterpolation_zero
    (a b : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g) :
    continuousCosphereInterpolation g a b 0 = a := by
  /- The underlying functions agree by cosphereInterpolation_zero.
  Subtype extensionality discards only the certificates that both functions are continuous. -/
  apply Subtype.ext
  exact cosphereInterpolation_zero g a.val b.val

/-- Continuous interpolation has the prescribed last endpoint. -/
theorem continuousCosphereInterpolation_one
    (a b : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g) :
    continuousCosphereInterpolation g a b 1 = b := by
  /- The underlying functions agree by cosphereInterpolation_one.
  The total-space base and the actual linear maps at every covector remain unchanged. -/
  apply Subtype.ext
  exact cosphereInterpolation_one g a.val b.val

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
include hE hF in
/-- Every open neighborhood of a continuous section contains a smooth section. -/
theorem exists_smoothCosphere_mem [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (a : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g)
    (U : Set (ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g))
    (hU : IsOpen U) (ha : a ∈ U) :
    ∃ b : smoothCosphereSymbolSpace (r := r) (q := q)
      (E := E) (F := F) g, smoothCosphereToContinuous (r := r) (q := q) g b ∈ U := by
  /- Extend the original frame coefficients from closed cosphere patches to the native
  cotangent total space. Smooth approximation there, followed by reconstruction with
  a base partition of unity, produces the required section in the original topology. -/
  classical
  -- Stage 1: establish the separation and countability needed for ambient approximation.
  let T := CotangentTotalSpace (n := n) (M := M)
  let H := EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin q)
  let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
  let IT := I.prod 𝓘(ℝ, CotangentModel n)
  let : T2Space T := t2Space_fiberBundleTotal (CotangentModel n) (CotangentFiber (n := n))
  have : IsManifold IT ∞ T := inferInstance
  let : LocallyCompactSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) :=
    inferInstanceAs (LocallyCompactSpace (EuclideanSpace ℝ (Fin n) × CotangentModel n))
  let : LocallyCompactSpace T := ChartedSpace.locallyCompactSpace
    (ModelProd (EuclideanSpace ℝ (Fin n)) (CotangentModel n)) T
  let e (x : M) := trivializationAt (CotangentModel n) (CotangentFiber (n := n)) x
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : M ↦ (e x).baseSet) (fun x ↦ (e x).open_baseSet) (by
      intro x _
      exact mem_iUnion.mpr ⟨x, mem_baseSet_trivializationAt _ _ _⟩)
  have hlocal (x : s) : SecondCountableTopology (e x).source :=
    (e x).toOpenPartialHomeomorph.secondCountableTopology_source
  let : SecondCountableTopology T := TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun x : s ↦ (e x).open_source) (by
      ext z
      simp only [mem_iUnion, mem_univ, iff_true]
      obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hs (mem_univ z.proj))
      exact ⟨⟨x, hx⟩, hzx⟩)
  have : SigmaCompactSpace T := inferInstance
  have : NormalSpace T := inferInstance
  let : FiniteDimensional ℝ H := Module.Finite.trans ℂ H
  have extend {K : Type _} [TopologicalSpace K] (e : K → T)
      (he : IsClosedEmbedding e) (f : C(K, H)) :
      ∃ F : C(T, H), F.comp ⟨e, he.continuous⟩ = f :=
    @ContinuousMap.exists_extension K _ T _ _ e H _
      (TietzeExtension.of_homeo (Module.finBasis ℝ H).equivFunL.toHomeomorph) he f
  -- Stage 2: choose a finite smooth partition subordinate to the original bundle frames.
  let S := CosphereBundle g
  let V := fun x : M ↦ E x →L[ℂ] F x
  let : CompactSpace S := g.compactSpace_cosphere
  let : T2Space S := inferInstance
  let : LocallyCompactSpace S := inferInstance
  let eE (x : M) := trivializationAt (EuclideanSpace ℂ (Fin r)) E x
  let eF (x : M) := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
  let O (x : M) := (eE x).baseSet ∩ (eF x).baseSet
  have hO (x : M) : IsOpen (O x) := (eE x).open_baseSet.inter (eF x).open_baseSet
  obtain ⟨cover, hcover⟩ := isCompact_univ.elim_finite_subcover O hO (by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_baseSet_trivializationAt _ _ _,
      mem_baseSet_trivializationAt _ _ _⟩)
  let J := {x : M // x ∈ cover}
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun j : J ↦ O j.val) (fun j ↦ hO j.val) (by
      intro x hx
      obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hcover hx)
      exact mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)
  let inv (j : J) (x : M) (L : H) : V x :=
    (eF j.val).symmL ℂ x |>.comp (L.comp ((eE j.val).continuousLinearMapAt ℂ x))
  -- Stage 3: reconstruction is continuous for compact-open section convergence.
  have hcontinuous {Z : Type _} [TopologicalSpace Z] (j : J)
      (b : Z → M) (hb : Continuous b) (v : Z → H) (hv : Continuous v) :
      Continuous (fun z ↦ (⟨b z, (ρ j (b z) : ℂ) • inv j (b z) (v z)⟩ : TotalSpace H V)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    by_cases hz : b z ∈ tsupport (ρ j)
    · let eH := (eE j.val).continuousLinearMap (RingHom.id ℂ) (eF j.val)
      have hframe : b z ∈ eH.baseSet := hρ j hz
      have hm : ContinuousAt (fun y ↦ (b y, (ρ j (b y) : ℂ) • v y)) z :=
        hb.continuousAt.prodMk
          ((Complex.continuous_ofReal.comp ((ρ j).property.continuous.comp hb)).continuousAt.smul
            hv.continuousAt)
      have hh := (eH.toOpenPartialHomeomorph.continuousAt_symm
        (eH.mem_target.mpr hframe)).comp hm
      apply hh.congr
      filter_upwards with y
      change (⟨b y, inv j (b y) ((ρ j (b y) : ℂ) • v y)⟩ : TotalSpace H V) = _
      apply congrArg (TotalSpace.mk (b y))
      ext w
      simp [inv]
    · have hzero : ∀ᶠ y in 𝓝 z, ρ j (b y) = 0 :=
        Filter.Eventually.mono
          (hb.continuousAt ((isClosed_tsupport (f := (ρ j : M → ℝ))).isOpen_compl.mem_nhds hz))
          (fun y hy ↦ image_eq_zero_of_notMem_tsupport hy)
      have hzeroSection :=
        (Trivialization.continuous_zeroSection (R := ℂ) (F := H) (E := V)).comp hb
      apply hzeroSection.continuousAt.congr_of_eventuallyEq
      filter_upwards [hzero] with y hy
      simp [hy, zeroSection]
  have hsum {Z : Type _} [TopologicalSpace Z] (b : Z → M) (hb : Continuous b)
      (v : J → Z → H) (hv : ∀ j, Continuous (v j)) :
      Continuous (fun z ↦ (⟨b z, ∑ j, (ρ j (b z) : ℂ) • inv j (b z) (v j z)⟩ :
        TotalSpace H V)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    let eH := trivializationAt H V (b z)
    apply (FiberBundle.continuousAt_totalSpace H _).mpr
    refine ⟨hb.continuousAt, ?_⟩
    have hc (j : J) := ((FiberBundle.continuousAt_totalSpace H _).mp
      ((hcontinuous j b hb (v j) (hv j)).continuousAt (x := z))).2
    have hsumAt : ContinuousAt (fun y ↦ ∑ j, (eH ⟨b y,
        (ρ j (b y) : ℂ) • inv j (b y) (v j y)⟩).2) z :=
      tendsto_finsetSum Finset.univ (fun j _ ↦ hc j)
    apply hsumAt.congr_of_eventuallyEq
    filter_upwards [hb.continuousAt (eH.open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt H V (b z)))] with y hy
    change (eH ⟨b y, ∑ j, (ρ j (b y) : ℂ) • inv j (b y) (v j y)⟩).2 = _
    simp only [← eH.continuousLinearMapAt_apply_of_mem ℂ hy, map_sum]
  let hbase : Continuous (fun z : S ↦ z.val.proj) :=
    (FiberBundle.continuous_proj (CotangentModel n) (CotangentFiber (n := n))).comp
      continuous_subtype_val
  let R (f : J → C(S, H)) : ContinuousCosphereSymbol (r := r) (q := q) (E := E) (F := F) g :=
    ⟨fun z ↦ ∑ j, (ρ j z.val.proj : ℂ) • inv j z.val.proj (f j z),
      hsum _ hbase (fun j ↦ f j) (fun j ↦ (f j).continuous)⟩
  have hR : Continuous R := by
    rw [continuous_induced_rng]
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact hsum (fun p : (J → C(S, H)) × S ↦ p.2.val.proj)
      (hbase.comp continuous_snd) (fun j p ↦ p.1 j p.2) (fun j ↦
        continuous_eval.comp ((continuous_apply j |>.comp continuous_fst).prodMk continuous_snd))
  -- Stage 4: extend each frame coefficient from precisely the closed support where it is used.
  let K (j : J) := {z : S | z.val.proj ∈ tsupport (ρ j)}
  have hK (j : J) : IsClosed (K j) := (isClosed_tsupport (f := (ρ j : M → ℝ))).preimage hbase
  let incl (j : J) : K j → T := fun z ↦ z.val.val
  have hincl (j : J) : IsClosedEmbedding (incl j) :=
    g.isClosed_cosphere.isClosedEmbedding_subtypeVal.comp (hK j).isClosedEmbedding_subtypeVal
  let eH (j : J) := (eE j.val).continuousLinearMap (RingHom.id ℂ) (eF j.val)
  let coords (j : J) : C(K j, H) :=
    ⟨fun z ↦ (eH j (cosphereSymbolTotal (r := r) (q := q) g a.val z.val)).2, by
      apply continuous_iff_continuousAt.mpr
      intro z
      apply ((eH j).continuousAt ?_).snd.comp
        (a.property.continuousAt.comp continuous_subtype_val.continuousAt)
      exact (eH j).mem_source.mpr (hρ j z.property)⟩
  choose extension hextension using fun j ↦ extend (incl j) (hincl j) (coords j)
  let original (j : J) : C(S, H) :=
    (extension j).comp ⟨Subtype.val, continuous_subtype_val⟩
  -- The partition recovers the very same original dependent section.
  have hRa : R original = a := by
    apply Subtype.ext
    funext z
    change ∑ j, (ρ j z.val.proj : ℂ) • inv j z.val.proj (original j z) = a.val z
    have hterm (j : J) : (ρ j z.val.proj : ℂ) • inv j z.val.proj (original j z) =
        (ρ j z.val.proj : ℂ) • a.val z := by
      -- On the support use smooth transitions; off the closed support the summand vanishes.
      by_cases hz : ρ j z.val.proj = 0
      · simp [hz]
      have hzs : z.val.proj ∈ tsupport (ρ j) := subset_tsupport _ (mem_support.mpr hz)
      have hf := DFunLike.congr_fun (hextension j) ⟨z, hzs⟩
      have hframe := hρ j hzs
      change original j z = (eH j (cosphereSymbolTotal (r := r) (q := q) g a.val z)).2 at hf
      rw [hf]
      congr 1
      simp only [inv, eH, Trivialization.continuousLinearMap_apply, cosphereSymbolTotal,
        ContinuousLinearMap.comp_assoc]
      ext v
      simp only [ContinuousLinearMap.comp_apply]
      rw [(eE j.val).symmL_continuousLinearMapAt (R := ℂ) hframe.1,
        (eF j.val).symmL_continuousLinearMapAt (R := ℂ) hframe.2]
    simp_rw [hterm]
    rw [← Finset.sum_smul]
    have hpartition : ∑ j : J, (ρ j z.val.proj : ℂ) = 1 := by
      have hsum : ∑ j : J, ρ j z.val.proj = 1 := by
        simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ z.val.proj)
      exact_mod_cast hsum
    rw [hpartition, one_smul]
  -- Stage 5: one uniform tolerance in the finite coefficient space controls the neighborhood.
  have hnear : R ⁻¹' U ∈ 𝓝 original := hR.continuousAt.preimage_mem_nhds
    (hU.mem_nhds (by simpa only [hRa] using ha))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
  choose smooth hsmooth hsupport using fun j : J ↦
    (extension j).continuous.exists_contMDiff_approx IT (⊤ : ℕ∞)
      (continuous_const : Continuous (fun _ : T ↦ ε)) (fun _ ↦ hε)
  let approx (j : J) : C(S, H) :=
    (⟨smooth j, (smooth j).property.continuous⟩ : C(T, H)).comp
      ⟨Subtype.val, continuous_subtype_val⟩
  have happrox : R approx ∈ U := by
    apply hball
    rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    apply (ContinuousMap.dist_lt_iff hε).mpr
    intro z
    exact hsmooth j z.val
  -- Stage 6: verify smoothness in every original chart and pair of bundle frames.
  let symbol : GlobalSymbolFunction (n := n) E F :=
    fun x ξ ↦ ∑ j, (ρ j x : ℂ) • inv j x (smooth j ⟨x, ξ⟩)
  have hsymbol : IsSmoothOffZeroGlobalSymbol (r := r) (q := q) E F symbol := by
    intro c hc e f _ _ p hp
    let IP := 𝓘(ℝ, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    have hcm : c ∈ maximalAtlas I ∞ M := subset_maximalAtlas (I := I) hc
    have hbase' : ContMDiffAt IP I ∞ (fun p ↦ c.symm p.1) p :=
      (contMDiffAt_symm_of_mem_maximalAtlas hcm hp.1.1.1).comp p
        contDiffAt_fst.contMDiffAt
    have hd := ((contMDiffAt_of_mem_maximalAtlas hcm (c.map_target hp.1.1.1)).mfderiv_const
      (m := (∞ : WithTop ℕ∞)) (by simp)).comp p hbase'
    have hinner : ContMDiffAt IP 𝓘(ℝ, CotangentModel n) ∞
        (fun p ↦ innerSL ℝ p.2) p :=
      (innerSL ℝ).contDiff.contMDiff.contMDiffAt.comp p contDiffAt_snd.contMDiffAt
    -- The actual inverse chart and differential define the native cotangent coordinate map.
    have hmap : ContMDiffAt IP IT ∞
        (fun p ↦ (⟨c.symm p.1, covectorFromChart c (c.symm p.1) p.2⟩ : T)) p := by
      apply (contMDiffAt_hom_bundle _).mpr
      refine ⟨hbase', ?_⟩
      apply (hinner.clm_comp hd).congr_of_eventuallyEq
      filter_upwards with z
      ext v
      simp [covectorFromChart, inTangentCoordinates, ContinuousLinearMap.inCoordinates,
        Function.id_def, ContinuousLinearMap.comp_apply, I]
      rfl
    have hterm (j : J) : ContDiffAt ℝ ∞
        (fun p ↦ (f.continuousLinearMapAt ℂ (c.symm p.1)).comp
          (((ρ j (c.symm p.1) : ℂ) •
            inv j (c.symm p.1) (smooth j ⟨c.symm p.1,
              covectorFromChart c (c.symm p.1) p.2⟩)).comp (e.symmL ℂ (c.symm p.1)))) p := by
      -- On the support use smooth transitions; off the closed support the summand vanishes.
      by_cases hz : c.symm p.1 ∈ tsupport (ρ j)
      · have hframes := hρ j hz
        have hout := ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (r := q) (eF j.val) f)
          _ ⟨hframes.2, hp.1.2⟩).contMDiffAt
          (((eF j.val).open_baseSet.inter f.open_baseSet).mem_nhds ⟨hframes.2, hp.1.2⟩)
        have hin := ((IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (r := r) e (eE j.val))
          _ ⟨hp.1.1.2, hframes.1⟩).contMDiffAt
          ((e.open_baseSet.inter (eE j.val).open_baseSet).mem_nhds ⟨hp.1.1.2, hframes.1⟩)
        have hval := (smooth j).property.contMDiffAt.comp p hmap
        have hweight : ContMDiffAt IP 𝓘(ℝ, ℂ) ∞
            (fun p ↦ (ρ j (c.symm p.1) : ℂ)) p :=
          Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp p
            ((ρ j).property.contMDiffAt.comp p hbase')
        have hcompIn : ContDiff ℝ ∞
            (fun t : H × (EuclideanSpace ℂ (Fin r) →L[ℂ] EuclideanSpace ℂ (Fin r)) ↦
              t.1.comp t.2) :=
          isBoundedBilinearMap_comp.contDiff.restrict_scalars ℝ
        have hcompOut : ContDiff ℝ ∞
            (fun t : (EuclideanSpace ℂ (Fin q) →L[ℂ] EuclideanSpace ℂ (Fin q)) × H ↦
              t.1.comp t.2) :=
          isBoundedBilinearMap_comp.contDiff.restrict_scalars ℝ
        have ht := hweight.contDiffAt.smul (hcompOut.comp₂_contDiffAt
          (hout.comp p hbase').contDiffAt (hcompIn.comp₂_contDiffAt
            hval.contDiffAt (hin.comp p hbase').contDiffAt))
        apply ht.congr_of_eventuallyEq
        filter_upwards [hbase'.continuousAt
          ((e.open_baseSet.inter ((eE j.val).open_baseSet.inter
            ((eF j.val).open_baseSet.inter f.open_baseSet))).mem_nhds
              ⟨hp.1.1.2, hframes.1, hframes.2, hp.1.2⟩)] with z hz
        change (f.continuousLinearMapAt ℂ (c.symm z.1)).comp
          (((ρ j (c.symm z.1) : ℂ) • inv j (c.symm z.1)
            (smooth j ⟨c.symm z.1, covectorFromChart c (c.symm z.1) z.2⟩)).comp
              (e.symmL ℂ (c.symm z.1))) =
            (ρ j (c.symm z.1) : ℂ) •
              ((eF j.val).coordChangeL ℂ f (c.symm z.1)).toContinuousLinearMap.comp
                ((smooth j ⟨c.symm z.1, covectorFromChart c (c.symm z.1) z.2⟩).comp
                  (e.coordChangeL ℂ (eE j.val) (c.symm z.1)).toContinuousLinearMap)
        apply ContinuousLinearMap.ext
        intro v
        simp only [inv, ContinuousLinearMap.comp_apply, smul_apply,
          map_smul, ContinuousLinearEquiv.coe_coe]
        rw [(eF j.val).coordChangeL_apply f ⟨hz.2.2.1, hz.2.2.2⟩,
          e.coordChangeL_apply (eE j.val) ⟨hz.1, hz.2.1⟩,
          (eF j.val).symmL_apply hz.2.2.1,
          e.symmL_apply hz.1,
          (eE j.val).continuousLinearMapAt_apply_of_mem ℂ hz.2.1,
          f.continuousLinearMapAt_apply_of_mem ℂ hz.2.2.2]
      · have heq : (fun p ↦ (f.continuousLinearMapAt ℂ (c.symm p.1)).comp
            (((ρ j (c.symm p.1) : ℂ) •
              inv j (c.symm p.1) (smooth j ⟨c.symm p.1,
                covectorFromChart c (c.symm p.1) p.2⟩)).comp (e.symmL ℂ (c.symm p.1))))
            =ᶠ[𝓝 p] (fun _ ↦ (0 : H)) := by
          filter_upwards [hbase'.continuousAt
            ((isClosed_tsupport (f := (ρ j : M → ℝ))).isOpen_compl.mem_nhds hz)] with z hz
          simp [image_eq_zero_of_notMem_tsupport hz]
        exact contDiffAt_const.congr_of_eventuallyEq heq
    apply (ContDiffAt.sum (s := Finset.univ) (fun j _ ↦ hterm j)).contDiffWithinAt.congr
    · intro z _
      ext v
      simp [Function.uncurry_def, globalSymbolInChart, symbol]
    · ext v
      simp [Function.uncurry_def, globalSymbolInChart, symbol]
  -- Stage 7: restriction uses the original radial smoothness criterion on the cosphere.
  have hsmoothR : IsSmoothCosphereSymbol (r := r) (q := q) g (R approx).val :=
    isSmoothCosphereSymbol_restriction g symbol hsymbol
  refine ⟨⟨(R approx).val, hsmoothR⟩, ?_⟩
  exact happrox

include hE hF in
/-- Smooth sections have dense image in the continuous section space. -/
theorem denseRange_smoothCosphereToContinuous
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    DenseRange (smoothCosphereToContinuous (r := r) (q := q) (E := E) (F := F) g) := by
  /- Apply exists_smoothCosphere_mem to every open neighborhood of each
  continuous section. The neighborhood characterization of closure then gives dense range. -/
  intro a
  apply mem_closure_iff.mpr
  intro U hU ha
  obtain ⟨b, hb⟩ := exists_smoothCosphere_mem g a U hU ha
  exact ⟨smoothCosphereToContinuous g b, hb, ⟨b, rfl⟩⟩

end AtiyahSinger
