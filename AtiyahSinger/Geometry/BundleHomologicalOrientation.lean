/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.BundleOrientationChartTransport
public import AtiyahSinger.Geometry.ManifoldModelChange
public import AtiyahSinger.Topology.ChartHomologicalOrientation
public import AtiyahSinger.Topology.CohomologyOrientation
public import AtiyahSinger.Topology.FiberBundleTopology
public import AtiyahSinger.Topology.HomologicalOrientation
public import AtiyahSinger.Topology.LocalHomologyChart
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Topology.Bases

/-!
# The ordered homological orientation of an oriented vector-bundle total space

Public module ID: M1107.

The original bundle charts give coordinates (base, fiber). Mathlib's actual
finAddEquivProd inverse lists all base coordinates first, followed by all fiber
coordinates, without changing the total-space carrier or topology. The base
orientation and integral fiber cohomology orientation determine the signs of
the corresponding positive Euclidean local homology classes.

The base sign is read using the inverse of the specified integral local
generator map. The fiber sign is the original cap evaluation of the specified
fiber cohomology class on the simplex from the same native linear fiber chart.
Their product normalizes the local generator in the grouped total chart.
Both signs are integral units. This construction retains negative signs when
the base dimension or fiber rank is zero, without a positive empty-basis
assumption. No metric, smooth structure, compactness or connectedness is needed.

Sources: Hatcher, Algebraic Topology, section 3.3, for local homological
orientations; Milnor--Stasheff, Characteristic Classes, section 9, for integral
fiber orientations. The explicit grouped chart/cap normalization is a project
supplement fixing the order used in the Thom and Poincare-duality comparison.
It does not define orientation through a desired pushforward or index equality.
The local homology map API uses a common universe, so the geometric construction
uses M and its fibers in Type. The separate countability lemma is unrestricted.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle CategoryTheory Manifold Topology

section Countability

variable {B : Type*} [TopologicalSpace B]
  (F : Type*) [TopologicalSpace F] (E : B → Type*)
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)]
  [hE : FiberBundle F E]

include hE

/-- A fiber bundle with second-countable base and model fiber has second-countable total space. -/
theorem secondCountable_fiberBundleTotal
    [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (TotalSpace F E) := by
  /- Stage 1: the native trivialization base sets form an open cover of B.
  A second-countable space is Lindelof, so take a countable subcover.
  Stage 2: each original total chart source is homeomorphic to its open
  base set times F. The base subspace and F are second countable, hence so
  is that product and its original chart source. These sources cover the
  original total space because the selected base sets cover B.
  Stage 3: combine countable bases on this countable open cover. No global
  trivialization, metric, Hausdorff assumption or compactness is needed. -/
  classical
  -- Select countably many of the original base neighborhoods covering the base.
  let U (b : B) : Set B := (trivializationAt F E b).baseSet
  have hcover : ⋃ b, U b = Set.univ := by
    apply Set.eq_univ_of_forall
    intro b
    exact Set.mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F E b⟩
  obtain ⟨T, hT, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable U
    (fun b ↦ (trivializationAt F E b).open_baseSet)
  let : Countable T := hT.to_subtype
  let V (t : T) : Set (TotalSpace F E) := (trivializationAt F E t.val).source
  -- The existing chart homeomorphism identifies each source with U(t) × F.
  let : ∀ t : T, SecondCountableTopology (V t) := fun t ↦
    (trivializationAt F E t.val).sourceHomeomorphBaseSetProd.secondCountableTopology
  apply TopologicalSpace.secondCountableTopology_of_countable_cover
    (U := V) (fun t ↦ (trivializationAt F E t.val).open_source)
  apply Set.eq_univ_of_forall
  intro z
  have hz : z.proj ∈ ⋃ b ∈ T, U b := by rw [hTU, hcover]; trivial
  obtain ⟨b, hb, hzb⟩ := Set.mem_iUnion₂.mp hz
  exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, (trivializationAt F E b).mem_source.mpr hzb⟩

end Countability

section Charts

variable (n r : ℕ) {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (E : M → Type) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℝ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℝ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℝ (Fin r)) E]

/-- The original bundle charts in the existing base-first finite Euclidean coordinates. -/
@[reducible]
def bundleTotalEuclideanChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin (n + r)))
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E) := by
  -- Expose the original product chart model without changing any chart or topology.
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin r))
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E) :=
    inferInstanceAs (ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin r)))
      (TotalSpace (EuclideanSpace ℝ (Fin r)) E))
  -- finAddEquivProd puts the first n coordinates before the final r coordinates.
  exact linearModelChartedSpace
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
    (TotalSpace (EuclideanSpace ℝ (Fin r)) E)

end Charts

variable {n : ℕ} (r : ℕ) {M : Type} [TopologicalSpace M]
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

/-- The product of the original base sign and the actual fiber-cap sign in the same native chart. -/
def bundleTotalLocalOrientationCoefficient (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) (z : TE) : ℤ := by
  -- Compare the positive local base chart cycle with this exact integral base orientation.
  let c := chartAt V z.proj
  let a : relativeSingularHomology ℤ ({z.proj}ᶜ : Set M) n :=
    (localHomologyChartEquiv c z.proj (mem_chart_source V z.proj) n).symm
      (euclideanLocalOrientationCycle n (c z.proj))
  let baseSign : ℤ := (O.localGenerator z.proj).symm a
  -- The native total chart uses this same preferred linear trivialization on its fiber.
  let e : E z.proj ≃L[ℝ] F := VectorBundle.continuousLinearEquivAt ℝ F E z.proj
  let b : Module.Basis (Fin r) ℝ (E z.proj) :=
    (EuclideanSpace.basisFun (Fin r) ℝ).toBasis.map e.symm.toLinearEquiv
  let fiberSign : ℤ := realOrientationEvaluation b b.orientation (o.fiberClass z.proj)
  exact baseSign * fiberSign

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Base-first charts and the two integral orientations determine one total orientation. -/
theorem existsUnique_bundleHomologicalOrientation (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) :
    ∃! OT : HomologicalOrientation (n + r) TE, ∀ z : TE,
      localHomologyChartEquiv (chartAt W z) z (mem_chart_source W z) (n + r)
        (OT.localGenerator z 1) =
          bundleTotalLocalOrientationCoefficient r E O o z •
            euclideanLocalOrientationCycle (n + r) (chartAt W z z) := by
  /- Stage 1: both the chart-positive base cycle and O.localGenerator x 1
  generate the same integral local group, so baseSign is +1 or -1. Its
  inverse is itself. Thus the image of O.localGenerator x 1 in the base
  chart is baseSign times the positive Euclidean cycle. The original fiber
  class o.fiberClass x is an integral generator; cap and augmentation on
  the preferred positive fiber simplex evaluate it to fiberSign = +1 or -1.
  Stage 2: give the total local group the product orientation, using the
  ordered base and fiber coordinates. Translation from fiber zero to z.snd
  preserves this orientation. Excision through the actual grouped total
  chart transports the signed Euclidean generator to the original total
  local group. Integer multiplication by this generator is an equivalence.
  Stage 3: work on one fixed sufficiently small native bundle chart. The
  local compatibility of O and o makes both their coordinate signs locally
  constant. A change of base chart contributes its local orientation sign;
  a change of linear bundle coordinates contributes its determinant sign.
  The total transition has the corresponding product sign in base-first
  order. These signs cancel the coordinate changes in the two prescribed
  factors. Thus the chosen generators agree with one local relative class
  on a smaller total chart neighborhood, giving the required local
  compatibility. Preferred charts need not depend continuously on z.
  Stage 4: the displayed normalization determines each image of 1, hence
  every local integer-linear equivalence. Extensionality and proof
  irrelevance give uniqueness. In base dimension zero or fiber rank zero,
  retain each signed point class through its same cap evaluation; no
  positive basis for a negative empty orientation is asserted. Empty and
  disconnected bases satisfy the same local argument. No target duality,
  pushforward equality or degree-dependent orientation is assumed. -/
  classical
  let g := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := n) (m := r)).symm
  have hchart (p : TE) : chartAt W p =
      ((trivializationAt F E p.proj).toOpenPartialHomeomorph.trans
        ((chartAt V p.proj).prod (OpenPartialHomeomorph.refl F))).trans
          g.toHomeomorph.toOpenPartialHomeomorph := by
    change (chartAt (ModelProd V F) p).trans g.toHomeomorph.toOpenPartialHomeomorph = _
    rw [FiberBundle.chartedSpace_chartAt]
  have hparts (p y : TE) (hy : y ∈ (chartAt W p).source) :
      y.proj ∈ (chartAt V p.proj).source ∧
        y.proj ∈ (trivializationAt F E p.proj).baseSet := by
    rw [hchart p] at hy
    have hty := hy.1.1
    refine ⟨?_, (trivializationAt F E p.proj).mem_source.mp hty⟩
    have hbc : ((trivializationAt F E p.proj) y).1 ∈ (chartAt V p.proj).source :=
      hy.1.2.1
    rwa [(trivializationAt F E p.proj).coe_fst hty] at hbc
  have hsource (p y : TE) (hc : y.proj ∈ (chartAt V p.proj).source)
      (ht : y.proj ∈ (trivializationAt F E p.proj).baseSet) :
      y ∈ (chartAt W p).source := by
    rw [hchart p]
    refine ⟨⟨(trivializationAt F E p.proj).mem_source.mpr ht, ?_⟩, Set.mem_univ _⟩
    change ((trivializationAt F E p.proj) y).1 ∈ (chartAt V p.proj).source ∧
      ((trivializationAt F E p.proj) y).2 ∈ Set.univ
    rw [(trivializationAt F E p.proj).coe_fst' ht]
    exact ⟨hc, Set.mem_univ _⟩
  let coeff (p y : TE) (hc : y.proj ∈ (chartAt V p.proj).source)
      (ht : y.proj ∈ (trivializationAt F E p.proj).baseSet) : ℤ :=
    homologicalOrientationChartSign O (chartAt V p.proj) y.proj hc *
      bundleFiberChartSign r E o (trivializationAt F E p.proj) y.proj ht
  have hcoeff (y : TE) : bundleTotalLocalOrientationCoefficient r E O o y =
      coeff y y (mem_chart_source V y.proj) (mem_baseSet_trivializationAt F E y.proj) := rfl
  have hunit (y : TE) : IsUnit (bundleTotalLocalOrientationCoefficient r E O o y) := by
    rw [hcoeff]
    exact (isUnit_homologicalOrientationChartSign O (chartAt V y.proj) y.proj
      (mem_chart_source V y.proj)).mul
        (isUnit_bundleFiberChartSign r E o (trivializationAt F E y.proj) y.proj
          (mem_baseSet_trivializationAt F E y.proj))
  let Z (y : TE) := (localHomologyChartEquiv (chartAt W y) y (mem_chart_source W y)
    (n + r)).symm (bundleTotalLocalOrientationCoefficient r E O o y •
      euclideanLocalOrientationCycle (n + r) (chartAt W y y))
  -- The actual native chart comparison transports these prescribed generators on overlaps.
  have hnorm (p y : TE) (hy : y ∈ (chartAt W p).source) :
      localHomologyChartEquiv (chartAt W p) y hy (n + r) (Z y) =
        coeff p y (hparts p y hy).1 (hparts p y hy).2 •
          euclideanLocalOrientationCycle (n + r) (chartAt W p y) := by
    let bp := homologicalOrientationChartSign O (chartAt V y.proj) y.proj
      (mem_chart_source V y.proj)
    let bq := homologicalOrientationChartSign O (chartAt V p.proj) y.proj (hparts p y hy).1
    let fp := bundleFiberChartSign r E o (trivializationAt F E y.proj) y.proj
      (mem_baseSet_trivializationAt F E y.proj)
    let fq := bundleFiberChartSign r E o (trivializationAt F E p.proj) y.proj (hparts p y hy).2
    let τ : C(W, W) := ⟨fun w ↦ chartAt W p y + (w - chartAt W y y),
      continuous_const.add (continuous_id.sub continuous_const)⟩
    have hτ : Set.MapsTo τ ({chartAt W y y}ᶜ : Set W) ({chartAt W p y}ᶜ : Set W) :=
      fun _ hw heq ↦ hw (sub_eq_zero.mp (add_left_cancel (heq.trans (add_zero _).symm)))
    let T := relativeSingularHomologyMap ℤ τ hτ (n + r)
    let Cp := localHomologyChartEquiv (chartAt W y) y (mem_chart_source W y) (n + r)
    let Cq := localHomologyChartEquiv (chartAt W p) y hy (n + r)
    have hmap : Cq.toModuleIso.hom = ((bq * bp) * (fp * fq)) • (Cp.toModuleIso.hom ≫ T) := by
      have h := localHomologyChartEquiv_bundle_eq_sign_smul n r E O o
        (chartAt V y.proj) (chartAt V p.proj)
        (trivializationAt F E y.proj) (trivializationAt F E p.proj) g y
        (mem_chart_source V y.proj) (hparts p y hy).1
        (mem_baseSet_trivializationAt F E y.proj) (hparts p y hy).2
        (by rw [← hchart y]; exact mem_chart_source W y)
        (by rw [← hchart p]; exact hy)
      have htransport (c₁ c₂ : OpenPartialHomeomorph TE W)
          (he₁ : c₁ = chartAt W y) (he₂ : c₂ = chartAt W p)
          (hy₁ : y ∈ c₁.source) (hy₂ : y ∈ c₂.source) :
          (localHomologyChartEquiv c₂ y hy₂ (n + r)).toModuleIso.hom =
            ((bq * bp) * (fp * fq)) •
              ((localHomologyChartEquiv c₁ y hy₁ (n + r)).toModuleIso.hom ≫
                relativeSingularHomologyMap ℤ
                  (⟨fun w : W ↦ c₂ y + (w - c₁ y),
                    continuous_const.add (continuous_id.sub continuous_const)⟩ : C(W, W))
                  (A := ({c₁ y}ᶜ : Set W)) (B := ({c₂ y}ᶜ : Set W))
                  (fun _ hw heq ↦ hw (sub_eq_zero.mp
                    (add_left_cancel (heq.trans (add_zero _).symm)))) (n + r)) →
            Cq.toModuleIso.hom = ((bq * bp) * (fp * fq)) • (Cp.toModuleIso.hom ≫ T) := by
        subst c₁
        subst c₂
        exact fun hh ↦ hh
      exact htransport _ _ (hchart y).symm (hchart p).symm _ _ h
    have hbp : bp * bp = 1 := by
      rcases Int.isUnit_iff.mp (isUnit_homologicalOrientationChartSign O
        (chartAt V y.proj) y.proj (mem_chart_source V y.proj)) with h | h
      · change bp = 1 at h
        rw [h]
        norm_num
      · change bp = -1 at h
        rw [h]
        norm_num
    have hfp : fp * fp = 1 := by
      rcases Int.isUnit_iff.mp (isUnit_bundleFiberChartSign r E o
        (trivializationAt F E y.proj) y.proj
        (mem_baseSet_trivializationAt F E y.proj)) with h | h
      · change fp = 1 at h
        rw [h]
        norm_num
      · change fp = -1 at h
        rw [h]
        norm_num
    have hfactor : ((bq * bp) * (fp * fq)) *
        bundleTotalLocalOrientationCoefficient r E O o y = bq * fq := by
      rw [hcoeff]
      change ((bq * bp) * (fp * fq)) * (bp * fp) = bq * fq
      calc
        _ = (bq * fq) * (bp * bp) * (fp * fp) := by ring
        _ = bq * fq := by rw [hbp, hfp, mul_one, mul_one]
    have htcycle : T (euclideanLocalOrientationCycle (n + r) (chartAt W y y)) =
        euclideanLocalOrientationCycle (n + r) (chartAt W p y) :=
      euclideanLocalOrientationCycle_translate (n + r) (chartAt W y y) (chartAt W p y)
    have hv := congrArg (fun L ↦ L (Z y)) hmap
    change Cq (Z y) = ((bq * bp) * (fp * fq)) • T
      (Cp (Cp.symm (bundleTotalLocalOrientationCoefficient r E O o y •
        euclideanLocalOrientationCycle (n + r) (chartAt W y y)))) at hv
    rw [Cp.apply_symm_apply, map_zsmul, htcycle, smul_smul, hfactor] at hv
    exact hv
  -- Each prescribed class remains primitive: both signs are units and chart excision is invertible.
  have hgen (y : TE) : Function.Bijective (LinearMap.toSpanSingleton ℤ _ (Z y)) := by
    let C := localHomologyChartEquiv (chartAt W y) y (mem_chart_source W y) (n + r)
    let k := bundleTotalLocalOrientationCoefficient r E O o y
    have hk : Function.Bijective (fun m : ℤ ↦ m * k) :=
      IsUnit.isUnit_iff_mulRight_bijective.mp (hunit y)
    have h := C.symm.bijective.comp
      ((euclideanLocalOrientationCycle_is_generator (n + r) (chartAt W y y)).comp hk)
    convert h using 1
    funext m
    change (relativeSingularHomology ℤ ({y}ᶜ : Set TE) (n + r)).isModule.smul
      m (C.symm (k • euclideanLocalOrientationCycle (n + r) (chartAt W y y))) =
        C.symm ((m * k) • euclideanLocalOrientationCycle (n + r) (chartAt W y y))
    rw [int_smul_eq_zsmul, map_zsmul, map_zsmul, smul_smul]
  let b := (EuclideanSpace.basisFun (Fin (n + r)) ℝ).toBasis
  -- On one fixed native chart, both independent orientation signs are locally constant.
  have hlocal (p : TE) : ∃ U : Set TE, IsOpen U ∧ p ∈ U ∧
      ∃ hUs : U ⊆ (chartAt W p).source,
      ∃ c₀ : relativeSingularHomology ℤ {w : W | w ≠ 0} (n + r),
        ∀ y (hy : y ∈ U), relativeSingularHomologyMap ℤ
          (⟨fun w : W ↦ chartAt W p y + w, continuous_const.add continuous_id⟩ : C(W, W))
          (A := {w : W | w ≠ 0}) (B := ({chartAt W p y}ᶜ : Set W))
          (fun _ hw heq ↦ hw (add_left_cancel
            (heq.trans (add_zero (chartAt W p y)).symm))) (n + r) c₀ =
            localHomologyChartEquiv (chartAt W p) y (hUs hy) (n + r) (Z y) := by
    obtain ⟨Ub, hUb, hpb, hUbsource, hb⟩ :=
      exists_locally_constant_homologicalOrientationChartSign O (chartAt V p.proj) p.proj
        (mem_chart_source V p.proj)
    obtain ⟨Uf, hUf, hpf, hUft, hUfsource, hf⟩ :=
      exists_locally_constant_bundleFiberChartSign r E o (trivializationAt F E p.proj)
        (chartAt V p.proj) p.proj (mem_chart_source V p.proj)
        (mem_baseSet_trivializationAt F E p.proj)
    let U : Set TE := (π F E) ⁻¹' (Ub ∩ Uf)
    have hU : IsOpen U := (hUb.inter hUf).preimage (FiberBundle.continuous_proj F E)
    have hpU : p ∈ U := ⟨hpb, hpf⟩
    have hUs : U ⊆ (chartAt W p).source := fun y hy ↦
      hsource p y (hUbsource hy.1) (hUft hy.2)
    let k := coeff p p (mem_chart_source V p.proj) (mem_baseSet_trivializationAt F E p.proj)
    refine ⟨U, hU, hpU, hUs, k • realOrientationCycle b b.orientation, ?_⟩
    intro y hy
    have hconst : coeff p y (hparts p y (hUs hy)).1 (hparts p y (hUs hy)).2 = k := by
      dsimp only [coeff, k]
      rw [hb y.proj hy.1, hf y.proj hy.2]
    rw [map_zsmul]
    change k • euclideanLocalOrientationCycle (n + r) (chartAt W p y) = _
    rw [hnorm p y (hUs hy), hconst]
  -- Fixed chart classes give local compatibility; normalization then determines uniqueness.
  obtain ⟨OT, hOT, hUnique⟩ := existsUnique_homologicalOrientation_of_chart_transport Z hgen hlocal
  refine ⟨OT, ?_, ?_⟩
  · intro y
    rw [hOT]
    exact (localHomologyChartEquiv (chartAt W y) y (mem_chart_source W y)
      (n + r)).apply_symm_apply _
  · intro OT' hOT'
    apply hUnique
    intro y
    apply (localHomologyChartEquiv (chartAt W y) y (mem_chart_source W y) (n + r)).injective
    exact (hOT' y).trans ((localHomologyChartEquiv (chartAt W y) y
      (mem_chart_source W y) (n + r)).apply_symm_apply _).symm

/-- The ordered total orientation chosen from the same local chart normalization. -/
def bundleHomologicalOrientation (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) : HomologicalOrientation (n + r) TE :=
  (existsUnique_bundleHomologicalOrientation r E O o).exists.choose

/-- The selected total orientation has exactly the base-first signed local generator. -/
theorem bundleHomologicalOrientation_chart (O : HomologicalOrientation n M)
    (o : CohomologyOrientation ℤ r E) (z : TE) :
    localHomologyChartEquiv (chartAt W z) z (mem_chart_source W z) (n + r)
      ((bundleHomologicalOrientation r E O o).localGenerator z 1) =
        bundleTotalLocalOrientationCoefficient r E O o z •
          euclideanLocalOrientationCycle (n + r) (chartAt W z z) := by
  /- Take the normalization from the exact unique-existence witness used
  by bundleHomologicalOrientation. Both local signs, the total point,
  grouped chart and positive simplex are those of this same construction. -/
  exact (existsUnique_bundleHomologicalOrientation r E O o).exists.choose_spec z

end AtiyahSinger
