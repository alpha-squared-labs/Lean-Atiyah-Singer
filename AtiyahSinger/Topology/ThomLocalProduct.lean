/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleHomologicalOrientation
public import AtiyahSinger.Topology.LocalCohomologyChart
public import AtiyahSinger.Topology.RelativeCohomologyContractibleProduct
public import AtiyahSinger.Topology.SupportedThomOpenExtension
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# The original Thom product in its native total-space chart

Public module ID: M2249.

At a zero-section point, the singleton-supported Thom product becomes the
genuine union cup of the same base chart class and the same specified fiber
orientation class. The total chart uses the original preferred trivialization
and grouped base-first Euclidean coordinates.

The comparison is detected on a small ball in the base chart. Contractibility
identifies the restricted original Thom factor with its restriction to the
specified fiber; no new local orientation or replacement Thom class is chosen.

Source: the local product description of the Thom class, Hatcher, Algebraic
Topology, Section 4.D, and relative excision, Section 2.1.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory TopologicalSpace Topology

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] {n : ℕ} (r : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [T2Space M]
  (E : M → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]
  [VectorBundle ℝ (EuclideanSpace ℝ (Fin r)) E]

local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "F" => EuclideanSpace ℝ (Fin r)
local notation "W" => EuclideanSpace ℝ (Fin (n + r))
local notation "TE" => TotalSpace F E

attribute [local instance] t2Space_fiberBundleTotal bundleTotalEuclideanChartedSpace

omit [T2Space M] [∀ x, NormedSpace ℝ (E x)] [VectorBundle ℝ F E] in
private theorem nativeBundleChart (z : TE) :
    let g := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    chartAt W z = ((trivializationAt F E z.proj).toOpenPartialHomeomorph.trans
      ((chartAt V z.proj).prod (OpenPartialHomeomorph.refl F))).trans
        g.symm.toHomeomorph.toOpenPartialHomeomorph := by
  let g := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  change (chartAt (ModelProd V F) z).trans g.toHomeomorph.toOpenPartialHomeomorph = _
  rw [FiberBundle.chartedSpace_chartAt]

omit [T2Space M] in
private theorem nativeBundleChart_zeroSection (x : M) :
    chartAt W (zeroSection F E x) (zeroSection F E x) =
      (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
        (chartAt V x x, 0) := by
  rw [nativeBundleChart r E]
  change (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
    ((chartAt V x).prod (OpenPartialHomeomorph.refl F)
      ((trivializationAt F E x) (zeroSection F E x))) = _
  rw [(trivializationAt F E x).zeroSection ℝ (mem_baseSet_trivializationAt F E x)]
  rfl

omit [T2Space M] in
/-- The two coordinate support complements are the original native zero-point complement. -/
theorem bundleTotalEuclideanChart_support (x : M) :
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    {y : W | (split y).1 ≠ chartAt V x x} ∪ {y : W | (split y).2 ≠ 0} =
      ({chartAt W (zeroSection F E x) (zeroSection F E x)}ᶜ : Set W) := by
  dsimp only
  rw [nativeBundleChart_zeroSection r E]
  ext y
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  have hpoint : y = split.symm (chartAt V x x, 0) ↔
      (split y).1 = chartAt V x x ∧ (split y).2 = 0 := by
    constructor
    · intro h
      rw [h, split.apply_symm_apply]
      exact ⟨rfl, rfl⟩
    · intro h
      apply split.injective
      rw [split.apply_symm_apply]
      exact Prod.ext h.1 h.2
  simpa only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_singleton_iff,
    not_and_or] using (not_congr hpoint).symm

/-- The singleton-supported Thom product has the same base and fiber factors in the native chart. -/
theorem supportedCohomologyThomMap_localChart (o : CohomologyOrientation R r E)
    (x : M) (p : ℕ) (a : relativeSingularCohomology R ({x}ᶜ : Set M) p) :
    let K : Compacts M := ⟨{x}, isCompact_singleton⟩
    let z := zeroSection F E x
    let c := chartAt V x
    let t := chartAt W z
    let L := VectorBundle.continuousLinearEquivAt ℝ F E x
    let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
    let aChart := (localCohomologyChartIso R c x (mem_chart_source V x) p).hom a
    let bFiber := relativeSingularCohomologyPullback R (⟨L.symm, L.symm.continuous⟩ : C(F, E x))
      (A := {v : F | v ≠ 0}) (B := {v : E x | v ≠ 0})
      (fun _ hv ↦ L.symm.map_ne_zero_iff.mpr hv) r (o.fiberClass x)
    let A : Set W := {y | (split y).1 ≠ c x}
    let B : Set W := {y | (split y).2 ≠ 0}
    let hK : ((supportedCohomologyThomSupport r E K : Set TE)ᶜ) = ({z}ᶜ : Set TE) := by
      change ((bundleZeroSection r E) '' {x})ᶜ = ({z}ᶜ : Set TE)
      rw [Set.image_singleton]
      rfl
    (localCohomologyChartIso R t z (mem_chart_source W z) (p + r)).hom
        ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hK)).hom
          (supportedCohomologyThomMap R r E o K p a)) =
      (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r))
        (bundleTotalEuclideanChart_support r E x))).hom
        (relativeSingularCohomologyUnionCup R A B
          (isOpen_ne.preimage (continuous_fst.comp split.continuous))
          (isOpen_ne.preimage (continuous_snd.comp split.continuous)) p r
          (relativeSingularCohomologyPullback R
            (⟨fun y ↦ (split y).1, continuous_fst.comp split.continuous⟩ : C(W, V))
            (A := A) (B := ({c x}ᶜ : Set V)) (fun _ hy ↦ hy) p aChart)
          (relativeSingularCohomologyPullback R
            (⟨fun y ↦ (split y).2, continuous_snd.comp split.continuous⟩ : C(W, F))
            (A := B) (B := {v : F | v ≠ 0}) (fun _ hy ↦ hy) r bFiber)) := by
  classical
  have mapCongr {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
      {A : Set X₁} {B : Set X₂} (g h : C(X₁, X₂)) (heq : g = h)
      (hg : Set.MapsTo g A B) (hh : Set.MapsTo h A B) (k : ℕ) :
      relativeSingularCohomologyPullback R g hg k =
        relativeSingularCohomologyPullback R h hh k := by
    subst h
    rfl
  -- A small contractible ball in the original chart will detect this local class equality.
  let K : Compacts M := ⟨{x}, isCompact_singleton⟩
  let z := zeroSection F E x
  let c := chartAt V x
  let t := chartAt W z
  let e := trivializationAt F E x
  let L := VectorBundle.continuousLinearEquivAt ℝ F E x
  let split := EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)
  have hx : x ∈ c.source := mem_chart_source V x
  have hxe : x ∈ e.baseSet := mem_baseSet_trivializationAt F E x
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' e.baseSet := by
    refine ⟨c.map_source hx, ?_⟩
    change c.symm (c x) ∈ e.baseSet
    rw [c.left_inv hx]
    exact hxe
  obtain ⟨ε, hε, hball⟩ := (Metric.isOpen_iff.mp
    (c.isOpen_inter_preimage_symm e.open_baseSet)) (c x) hcx
  let U := Metric.ball (c x) ε
  let xU : U := ⟨c x, Metric.mem_ball_self hε⟩
  let : ContractibleSpace U := Metric.contractibleSpace_ball hε
  let Y := U × F
  let y₀ : Y := (xU, 0)
  let base : C(U, M) := ⟨fun u ↦ c.symm u.val,
    c.symm.continuousOn.comp_continuous continuous_subtype_val
      (fun u ↦ (hball u.property).1)⟩
  have hbase (u : U) : base u ∈ c.source ∧ base u ∈ e.baseSet :=
    ⟨c.map_target (hball u.property).1, (hball u.property).2⟩
  have hbaseChart (u : U) : c (base u) = u.val := c.right_inv (hball u.property).1
  have hbaseX : base xU = x := c.left_inv hx
  have htarget (u : U) (v : F) : (base u, v) ∈ e.target := by
    rw [e.target_eq]
    exact ⟨(hbase u).2, Set.mem_univ _⟩
  let f : C(Y, TE) := ⟨fun y ↦ e.toOpenPartialHomeomorph.symm (base y.1, y.2),
    e.toOpenPartialHomeomorph.symm.continuousOn.comp_continuous
      ((base.continuous.comp continuous_fst).prodMk continuous_snd)
      (fun y ↦ htarget y.1 y.2)⟩
  let q : C(Y, W) := ⟨fun y ↦ split.symm (y.1.val, y.2),
    split.symm.continuous.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)⟩
  have hform (y : Y) : f y =
      ⟨base y.1, (e.continuousLinearEquivAt ℝ (base y.1) (hbase y.1).2).symm y.2⟩ :=
    e.symm_apply_eq_mk_continuousLinearEquivAt_symm (base y.1) (hbase y.1).2 y.2
  have hproj (y : Y) : (f y).proj = base y.1 := by rw [hform]
  have hnonzero (y : Y) : f y ∈ bundleNonzero r E ↔ y.2 ≠ 0 := by
    rw [hform]
    change (e.continuousLinearEquivAt ℝ (base y.1) (hbase y.1).2).symm y.2 ≠ 0 ↔ y.2 ≠ 0
    exact (e.continuousLinearEquivAt ℝ (base y.1) (hbase y.1).2).symm.map_ne_zero_iff
  have hef (y : Y) : e (f y) = (base y.1, y.2) :=
    e.toOpenPartialHomeomorph.right_inv (htarget y.1 y.2)
  have hsource (y : Y) : f y ∈ t.source := by
    change f y ∈ (chartAt W z).source
    rw [nativeBundleChart (n := n) r E z]
    refine ⟨⟨e.toOpenPartialHomeomorph.map_target (htarget y.1 y.2), ?_⟩, Set.mem_univ _⟩
    change (e (f y)).1 ∈ c.source ∧ (e (f y)).2 ∈ Set.univ
    rw [hef]
    exact ⟨(hbase y.1).1, Set.mem_univ _⟩
  have hchart (y : Y) : t (f y) = q y := by
    change chartAt W z (f y) = q y
    rw [nativeBundleChart (n := n) r E z]
    change split.symm (c (e (f y)).1, (e (f y)).2) = split.symm (y.1.val, y.2)
    rw [hef, hbaseChart]
  have hfx : f y₀ = z := by
    change e.toOpenPartialHomeomorph.symm (base xU, 0) = z
    rw [hbaseX, ← e.zeroSection ℝ hxe]
    exact e.toOpenPartialHomeomorph.left_inv (e.mem_source.mpr hxe)
  have hqx : q y₀ = t z := by rw [← hchart, hfx]
  have hq : IsOpenEmbedding q := split.symm.toHomeomorph.isOpenEmbedding.comp
    (Metric.isOpen_ball.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id)
  let A₀ : Set Y := {y | y.1.val ≠ c x}
  let B₀ : Set Y := {y | y.2 ≠ 0}
  let D₀ := A₀ ∪ B₀
  have hD : D₀ = ({y₀}ᶜ : Set Y) := by
    ext y
    change (y.1.val ≠ c x ∨ y.2 ≠ 0) ↔ y ≠ (xU, 0)
    have hpoint : y = (xU, 0) ↔ y.1.val = c x ∧ y.2 = 0 := by
      constructor
      · intro h
        rw [h]
        exact ⟨rfl, rfl⟩
      · intro h
        exact Prod.ext (Subtype.ext h.1) h.2
    simpa only [not_and_or] using (not_congr hpoint).symm
  have hbasePair (y : Y) (hy : y ∈ A₀) : base y.1 ≠ x := by
    intro h
    apply hy
    rw [← hbaseChart, h]
  have hfA : Set.MapsTo f A₀ ((bundleProjection r E) ⁻¹' ({x}ᶜ : Set M)) := by
    intro y hy
    change (f y).proj ≠ x
    rw [hproj]
    exact hbasePair y hy
  have hfB : Set.MapsTo f B₀ (bundleNonzero r E) := fun y hy ↦ (hnonzero y).mpr hy
  have hfPoint : Set.MapsTo f D₀ ({z}ᶜ : Set TE) := by
    intro y hy h
    have heq : q y = q y₀ := by rw [hqx, ← hchart, h]
    have hy₀ := hq.injective heq
    rw [hD] at hy
    exact hy hy₀
  -- Contractibility retains the actual restriction of the original Thom class to this fiber.
  let LF : C(F, E x) := ⟨L.symm, L.symm.continuous⟩
  have hLF : Set.MapsTo LF {v : F | v ≠ 0} {v : E x | v ≠ 0} :=
    fun _ hv ↦ L.symm.map_ne_zero_iff.mpr hv
  let bFiber := relativeSingularCohomologyPullback R LF hLF r (o.fiberClass x)
  let prF : C(Y, F) := ContinuousMap.snd
  let sF : C(F, Y) := ⟨fun v ↦ (xU, v), continuous_const.prodMk continuous_id⟩
  have hsF : Set.MapsTo sF {v : F | v ≠ 0} B₀ := fun _ hv ↦ hv
  have hprF : Set.MapsTo prF B₀ {v : F | v ≠ 0} := fun _ hv ↦ hv
  let uLocal := relativeSingularCohomologyPullback R f hfB r (cohomologyThomClass R r E o)
  have hfiber : f.comp sF = (bundleFiberInclusion r E x).comp LF := by
    apply ContinuousMap.ext
    intro v
    change e.toOpenPartialHomeomorph.symm (base xU, v) = ⟨x, L.symm v⟩
    rw [hbaseX, e.symm_apply_eq_mk_continuousLinearEquivAt_symm (R := ℝ) x hxe v]
    rfl
  have hspec : relativeSingularCohomologyPullback R (bundleFiberInclusion r E x)
      (A := {v : E x | v ≠ 0}) (B := bundleNonzero r E) (fun _ hv ↦ hv) r
      (cohomologyThomClass R r E o) = o.fiberClass x :=
    (existsUnique_cohomologyThomClass R r E o).exists.choose_spec x
  have hIncl : Set.MapsTo (bundleFiberInclusion r E x) {v : E x | v ≠ 0}
      (bundleNonzero r E) := fun _ hv ↦ hv
  have hrestriction : relativeSingularCohomologyPullback R sF hsF r uLocal = bFiber := by
    change relativeSingularCohomologyPullback R sF hsF r
      (relativeSingularCohomologyPullback R f hfB r (cohomologyThomClass R r E o)) = _
    rw [← ModuleCat.comp_apply, ← relativeSingularCohomologyPullback_comp R sF f hsF hfB r,
      mapCongr _ _ hfiber _ (hIncl.comp hLF) r,
      relativeSingularCohomologyPullback_comp R LF (bundleFiberInclusion r E x) hLF hIncl r,
      ModuleCat.comp_apply, hspec]
  have hThom : relativeSingularCohomologyPullback R prF hprF r bFiber = uLocal := by
    have h := relativeSingularCohomology_prod_eq_pullback_fiber R xU
      {v : F | v ≠ 0} r uLocal
    change relativeSingularCohomologyPullback R prF hprF r
      (relativeSingularCohomologyPullback R sF hsF r uLocal) = uLocal at h
    rw [hrestriction] at h
    exact h
  -- The same base chart comparison pulls back to the original class on the small ball.
  let aChart := (localCohomologyChartIso R c x hx p).hom a
  let prV : C(Y, V) := ⟨fun y ↦ y.1.val, continuous_subtype_val.comp continuous_fst⟩
  let pBase : C(Y, M) := base.comp ContinuousMap.fst
  have hpBase : Set.MapsTo pBase A₀ ({x}ᶜ : Set M) := hbasePair
  have hprV : Set.MapsTo prV A₀ ({c x}ᶜ : Set V) := fun _ hy ↦ hy
  have hBase : relativeSingularCohomologyPullback R prV hprV p aChart =
      relativeSingularCohomologyPullback R pBase hpBase p a := by
    have h := congrArg (fun g ↦ g a) (localCohomologyChartIso_naturality R c x hx pBase
      (fun y ↦ (hbase y.1).1) hpBase p)
    change relativeSingularCohomologyPullback R
      (⟨fun y ↦ c (pBase y), c.continuousOn.comp_continuous pBase.continuous
        (fun y ↦ (hbase y.1).1)⟩ : C(Y, V)) _ p aChart = _ at h
    have hcmap : (⟨fun y ↦ c (pBase y), c.continuousOn.comp_continuous pBase.continuous
        (fun y ↦ (hbase y.1).1)⟩ : C(Y, V)) = prV := by
      apply ContinuousMap.ext
      intro y
      exact hbaseChart y.1
    rw [mapCongr _ prV hcmap _ hprV p] at h
    exact h
  -- All products now use the same two relative subspaces on the small product chart.
  let A : Set W := {y | (split y).1 ≠ c x}
  let B : Set W := {y | (split y).2 ≠ 0}
  let fstW : C(W, V) := ⟨fun y ↦ (split y).1, continuous_fst.comp split.continuous⟩
  let sndW : C(W, F) := ⟨fun y ↦ (split y).2, continuous_snd.comp split.continuous⟩
  have hfstW : Set.MapsTo fstW A ({c x}ᶜ : Set V) := fun _ hy ↦ hy
  have hsndW : Set.MapsTo sndW B {v : F | v ≠ 0} := fun _ hy ↦ hy
  have hA : IsOpen A := isOpen_ne.preimage fstW.continuous
  have hB : IsOpen B := isOpen_ne.preimage sndW.continuous
  have hA₀ : IsOpen A₀ := isOpen_ne.preimage prV.continuous
  have hB₀ : IsOpen B₀ := isOpen_ne.preimage prF.continuous
  have hqA : Set.MapsTo q A₀ A := by
    intro y hy
    change (split (split.symm (y.1.val, y.2))).1 ≠ c x
    rw [split.apply_symm_apply]
    exact hy
  have hqB : Set.MapsTo q B₀ B := by
    intro y hy
    change (split (split.symm (y.1.val, y.2))).2 ≠ 0
    rw [split.apply_symm_apply]
    exact hy
  have hqCup : Set.MapsTo q D₀ (A ∪ B) :=
    fun _ hy ↦ hy.elim (fun ha ↦ Or.inl (hqA ha)) (fun hb ↦ Or.inr (hqB hb))
  have hqPoint : Set.MapsTo q D₀ ({t z}ᶜ : Set W) := by
    intro y hy heq
    rw [hD] at hy
    exact hy (hq.injective (heq.trans hqx.symm))
  have hK : ((supportedCohomologyThomSupport r E K : Set TE)ᶜ) = ({z}ᶜ : Set TE) := by
    change ((bundleZeroSection r E) '' {x})ᶜ = ({z}ᶜ : Set TE)
    rw [Set.image_singleton]
    rfl
  have hS : A ∪ B = ({t z}ᶜ : Set W) := bundleTotalEuclideanChart_support r E x
  let uThom := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hK)).hom
    (supportedCohomologyThomMap R r E o K p a)
  let aW := relativeSingularCohomologyPullback R fstW hfstW p aChart
  let bW := relativeSingularCohomologyPullback R sndW hsndW r bFiber
  let rhs := (eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hS)).hom
    (relativeSingularCohomologyUnionCup R A B hA hB p r aW bW)
  change (localCohomologyChartIso R t z (mem_chart_source W z) (p + r)).hom uThom = rhs
  have castPullback {X₁ X₂ : Type} [TopologicalSpace X₁] [TopologicalSpace X₂]
      (g : C(X₁, X₂)) (D : Set X₁) (S T : Set X₂) (hST : S = T)
      (hgS : Set.MapsTo g D S) (hgT : Set.MapsTo g D T) (k : ℕ)
      (u : relativeSingularCohomology R S k) :
      relativeSingularCohomologyPullback R g hgT k
          ((eqToIso (congrArg (fun A ↦ relativeSingularCohomology R A k) hST)).hom u) =
        relativeSingularCohomologyPullback R g hgS k u := by
    subst T
    rfl
  have hTotal : relativeSingularCohomologyPullback R q hqPoint (p + r)
      ((localCohomologyChartIso R t z (mem_chart_source W z) (p + r)).hom uThom) =
      relativeSingularCohomologyPullback R f hfPoint (p + r) uThom := by
    have h := congrArg (fun g ↦ g uThom)
      (localCohomologyChartIso_naturality R t z (mem_chart_source W z) f hsource hfPoint (p + r))
    have hqmap : (⟨fun y ↦ t (f y), t.continuousOn.comp_continuous f.continuous hsource⟩ :
        C(Y, W)) = q := by
      apply ContinuousMap.ext
      exact hchart
    change relativeSingularCohomologyPullback R
      (⟨fun y ↦ t (f y), t.continuousOn.comp_continuous f.continuous hsource⟩ : C(Y, W)) _
      (p + r) ((localCohomologyChartIso R t z (mem_chart_source W z) (p + r)).hom uThom) = _ at h
    rw [mapCongr _ q hqmap _ hqPoint (p + r)] at h
    exact h
  have hLeft : relativeSingularCohomologyPullback R f hfPoint (p + r) uThom =
      relativeSingularCohomologyUnionCup R A₀ B₀ hA₀ hB₀ p r
        (relativeSingularCohomologyPullback R pBase hpBase p a) uLocal := by
    let A' := (bundleProjection r E) ⁻¹' ({x}ᶜ : Set M)
    let B' := bundleNonzero r E
    let hopen := isOpen_supportedCohomologyThomSubspaces r E K
    have hπ : Set.MapsTo (bundleProjection r E) A' ({x}ᶜ : Set M) := fun _ hy ↦ hy
    have hfCup : Set.MapsTo f D₀ (A' ∪ B') :=
      fun _ hy ↦ hy.elim (fun ha ↦ Or.inl (hfA ha)) (fun hb ↦ Or.inr (hfB hb))
    have hfSupport : Set.MapsTo f D₀ ((supportedCohomologyThomSupport r E K : Set TE)ᶜ) := by
      intro y hy
      rw [← supportedCohomologyThomSupport_compl r E K]
      exact hfCup hy
    change relativeSingularCohomologyPullback R f hfPoint (p + r)
      ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hK)).hom
        (supportedCohomologyThomMap R r E o K p a)) = _
    rw [castPullback f D₀ _ _ hK hfSupport hfPoint]
    change relativeSingularCohomologyPullback R f hfSupport (p + r)
      ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r))
        (supportedCohomologyThomSupport_compl r E K))).hom
          (relativeSingularCohomologyUnionCup R A' B' hopen.1 hopen.2 p r
            (relativeSingularCohomologyPullback R (bundleProjection r E) hπ p a)
            (cohomologyThomClass R r E o))) = _
    rw [castPullback f D₀ _ _ (supportedCohomologyThomSupport_compl r E K) hfCup hfSupport]
    have hcup := relativeSingularCohomologyPullback_unionCup R f
      (A := A₀) (B := B₀) (A' := A') (B' := B') hA₀ hB₀ hopen.1 hopen.2 hfA hfB p r
      (relativeSingularCohomologyPullback R (bundleProjection r E) hπ p a)
      (cohomologyThomClass R r E o)
    refine hcup.trans ?_
    have hπf : (bundleProjection r E).comp f = pBase := by
      apply ContinuousMap.ext
      exact hproj
    have hbasePull : relativeSingularCohomologyPullback R f hfA p
        (relativeSingularCohomologyPullback R (bundleProjection r E) hπ p a) =
          relativeSingularCohomologyPullback R pBase hpBase p a := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp R f (bundleProjection r E) hfA hπ p,
        mapCongr _ pBase hπf _ hpBase p]
    exact congrArg (fun u ↦ relativeSingularCohomologyUnionCup R A₀ B₀ hA₀ hB₀ p r u uLocal)
      hbasePull
  have hRight : relativeSingularCohomologyPullback R q hqPoint (p + r) rhs =
      relativeSingularCohomologyUnionCup R A₀ B₀ hA₀ hB₀ p r
        (relativeSingularCohomologyPullback R prV hprV p aChart)
        (relativeSingularCohomologyPullback R prF hprF r bFiber) := by
    change relativeSingularCohomologyPullback R q hqPoint (p + r)
      ((eqToIso (congrArg (fun S ↦ relativeSingularCohomology R S (p + r)) hS)).hom
        (relativeSingularCohomologyUnionCup R A B hA hB p r aW bW)) = _
    rw [castPullback q D₀ _ _ hS hqCup hqPoint,
      relativeSingularCohomologyPullback_unionCup R q hA₀ hB₀ hA hB hqA hqB]
    have hfstq : fstW.comp q = prV := by
      apply ContinuousMap.ext
      intro y
      exact congrArg Prod.fst (split.apply_symm_apply (y.1.val, y.2))
    have hsndq : sndW.comp q = prF := by
      apply ContinuousMap.ext
      intro y
      exact congrArg Prod.snd (split.apply_symm_apply (y.1.val, y.2))
    change relativeSingularCohomologyUnionCup R A₀ B₀ hA₀ hB₀ p r
      (relativeSingularCohomologyPullback R q hqA p
        (relativeSingularCohomologyPullback R fstW hfstW p aChart))
      (relativeSingularCohomologyPullback R q hqB r
        (relativeSingularCohomologyPullback R sndW hsndW r bFiber)) = _
    have hfstPull : relativeSingularCohomologyPullback R q hqA p
        (relativeSingularCohomologyPullback R fstW hfstW p aChart) =
          relativeSingularCohomologyPullback R prV hprV p aChart := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp R q fstW hqA hfstW p,
        mapCongr _ prV hfstq _ hprV p]
    have hsndPull : relativeSingularCohomologyPullback R q hqB r
        (relativeSingularCohomologyPullback R sndW hsndW r bFiber) =
          relativeSingularCohomologyPullback R prF hprF r bFiber := by
      rw [← ModuleCat.comp_apply,
        ← relativeSingularCohomologyPullback_comp R q sndW hqB hsndW r,
        mapCongr _ prF hsndq _ hprF r]
    exact congrArg₂ (fun u v ↦ relativeSingularCohomologyUnionCup R A₀ B₀ hA₀ hB₀ p r u v)
      hfstPull hsndPull
  -- Excision on this exact small-chart inclusion detects equality at the native total point.
  have hexc {D : Set Y} {S : Set W} (hD : D = ({y₀}ᶜ : Set Y))
      (hS : S = ({q y₀}ᶜ : Set W)) (hqS : Set.MapsTo q D S) :
      IsIso (relativeSingularCohomologyPullback R q hqS (p + r)) := by
    subst D
    subst S
    change IsIso ((localCohomologyOpenEmbeddingIso R q hq y₀ (p + r)).hom)
    infer_instance
  have := hexc hD (by rw [hqx]) hqPoint
  apply (ConcreteCategory.bijective_of_isIso
    (relativeSingularCohomologyPullback R q hqPoint (p + r))).injective
  rw [hTotal, hLeft, hRight, hBase, hThom]

end AtiyahSinger
