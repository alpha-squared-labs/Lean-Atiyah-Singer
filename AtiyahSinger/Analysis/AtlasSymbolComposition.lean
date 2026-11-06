/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.AtlasGlobalSymbol

/-!
# Composition of symbols on the original locally finite-rank bundles

Public module ID: M0310.

A02: the filtered Hom composition in SG III.3.10 and III.3.18--3.19,
pp.183--188. Both factors act at the same original base point and covector.
Their intermediate fiber agrees exactly; their three local ranks are
otherwise independent. No fixed global rank, metric or compactness is used.

The pointwise product has order l+m. Changing either representative by
one lower order changes that product by one lower order, so the actual
formula descends through both principal-symbol quotients. This product is
not asserted to be a full symbol of operator composition: the latter has
lower-order correction terms, supplied by the local composition calculus.
The operator comparison is in AtlasPseudodifferentialComposition.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {E : M → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  {F : M → Type*} [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
  {G : M → Type*} [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]

/-- Actual fiberwise composition, with the output factor first. -/
def atlasSymbolComp (b : AtlasSymbolFunction (n := n) F G)
    (a : AtlasSymbolFunction (n := n) E F) : AtlasSymbolFunction (n := n) E G :=
  fun x ξ ↦ (b x ξ).comp (a x ξ)

variable [TopologicalSpace (TotalSpace Unit E)]
  [TopologicalSpace (TotalSpace Unit F)] [TopologicalSpace (TotalSpace Unit G)]
  {A : SmoothComplexBundleAtlas (n := n) E}
  {B : SmoothComplexBundleAtlas (n := n) F}
  {C : SmoothComplexBundleAtlas (n := n) G}

/-- Composition adds symbol orders while retaining the original intermediate fiber. -/
theorem IsAtlasGlobalSymbol.atlasSymbolComp {l m : ℝ}
    {b : AtlasSymbolFunction (n := n) F G} {a : AtlasSymbolFunction (n := n) E F}
    (hb : IsAtlasGlobalSymbol B C l b) (ha : IsAtlasGlobalSymbol A B m a) :
    IsAtlasGlobalSymbol A C (l + m) (atlasSymbolComp b a) := by
  /- Stage 1: fix a base chart and the two outer frames. Near each point
  choose an actual atlas frame of B. Its inverse and forward maps cancel
  in the original intermediate fiber, so the coordinate expression is
  symbolComp of the two local symbols at the same transformed covector.
  The mixed Leibniz estimates give order l+m, with each frequency
  derivative lowering the combined order by one. Smoothness is local.
  Stage 2: cover a compact subset of the outer coordinate domain by
  finitely many smaller compact neighborhoods in these middle-frame
  domains. Combine their estimates. The middle rank may change between
  disjoint neighborhoods; each estimate uses its own finite-dimensional
  Hom spaces. No globally valid middle frame or compact base is required. -/
  classical
  intro c hc i k
  let U := atlasSymbolChartDomain A C c i k
  let p := atlasGlobalSymbolInChart A C (AtiyahSinger.atlasSymbolComp b a) c i k
  -- Equality on an open domain preserves the actual total mixed derivatives there.
  have hcongr {V : Set (EuclideanSpace ℝ (Fin n))} (hV : IsOpen V)
      (p₁ p₂ : SymbolFunction n (A.rank i) (C.rank k)) (hp₁ : IsSymbol V (l + m) p₁)
      (heq : ∀ z ∈ V, ∀ η, p₁ z η = p₂ z η) : IsSymbol V (l + m) p₂ := by
    refine ⟨hp₁.1.congr (fun z hz ↦ (heq z.1 hz.1 z.2).symm), ?_⟩
    intro K hKV hK i j
    obtain ⟨C, hC, hbound⟩ := hp₁.2 K hKV hK i j
    refine ⟨C, hC, ?_⟩
    intro x hx ξ
    have hnear : (fun y ↦ iteratedFDeriv ℝ j (p₁ y) ξ) =ᶠ[nhds x]
        (fun y ↦ iteratedFDeriv ℝ j (p₂ y) ξ) := by
      filter_upwards [hV.mem_nhds (hKV hx)] with y hy
      rw [funext (heq y hy)]
    have hder := (hnear.iteratedFDeriv ℝ i).eq_of_nhds
    change ‖iteratedFDeriv ℝ i _ x‖ ≤ _
    rw [← hder]
    exact hbound x hx ξ
  -- A middle frame is chosen only near each base point, with its own valid overlap.
  have hlocal (z : U) : ∃ V : Set (EuclideanSpace ℝ (Fin n)),
      IsOpen V ∧ z.val ∈ V ∧ IsSymbol V (l + m) p := by
    obtain ⟨j, hj⟩ := B.covers (c.symm z.val)
    let V := atlasSymbolChartDomain A B c i j ∩ atlasSymbolChartDomain B C c j k
    have hleft : IsOpen (atlasSymbolChartDomain A B c i j) := by
      simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.continuousOn_symm.isOpen_inter_preimage c.open_target
          ((A.chart i).open_baseSet.inter (B.chart j).open_baseSet)
    have hright : IsOpen (atlasSymbolChartDomain B C c j k) := by
      simpa only [atlasSymbolChartDomain, Set.preimage_inter, Set.inter_assoc] using
        c.continuousOn_symm.isOpen_inter_preimage c.open_target
          ((B.chart j).open_baseSet.inter (C.chart k).open_baseSet)
    have hV : IsOpen V := hleft.inter hright
    have hzV : z.val ∈ V := ⟨⟨⟨z.property.1.1, z.property.1.2⟩, hj⟩,
      ⟨⟨z.property.1.1, hj⟩, z.property.2⟩⟩
    have ha' : IsSymbol V m (atlasGlobalSymbolInChart A B a c i j) := by
      refine ⟨(ha c hc i j).1.mono (Set.prod_mono Set.inter_subset_left subset_rfl), ?_⟩
      intro K hK hcompact u v
      exact (ha c hc i j).2 K (hK.trans Set.inter_subset_left) hcompact u v
    have hb' : IsSymbol V l (atlasGlobalSymbolInChart B C b c j k) := by
      refine ⟨(hb c hc j k).1.mono (Set.prod_mono Set.inter_subset_right subset_rfl), ?_⟩
      intro K hK hcompact u v
      exact (hb c hc j k).2 K (hK.trans Set.inter_subset_right) hcompact u v
    refine ⟨V, hV, hzV, hcongr hV _ _ (hb'.symbolComp hV ha') ?_⟩
    intro x hx ξ
    -- The very same middle frame and Euclidean coordinates cancel on this fiber.
    have hA : c.symm x ∈ (A.chart i).baseSet := hx.1.1.2
    have hB : c.symm x ∈ (B.chart j).baseSet := hx.1.2
    have hC : c.symm x ∈ (C.chart k).baseSet := hx.2.2
    ext v
    simp [p, atlasGlobalSymbolInChart, AtiyahSinger.atlasSymbolComp, symbolComp,
      hA, hB, hC, EuclideanSpace.equiv, PiLp.continuousLinearEquiv]
  choose V hV hzV hpV using hlocal
  -- Smoothness is local; no smoothness of a globally selected middle frame is needed.
  refine ⟨?_, ?_⟩
  · intro z hz
    exact ((hpV ⟨z.1, hz.1⟩).1.contDiffAt
      (((hV ⟨z.1, hz.1⟩).prod isOpen_univ).mem_nhds
        ⟨hzV ⟨z.1, hz.1⟩, Set.mem_univ z.2⟩)).contDiffWithinAt
  · intro K hKU hK i j
    -- Smaller compact neighborhoods permit finitely many original local symbol estimates.
    choose L hL hzL hLV using fun z : U ↦ exists_compact_subset (hV z) (hzV z)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : U ↦ interior (L z))
      (fun _ ↦ isOpen_interior) (by
        intro x hx
        exact Set.mem_iUnion.mpr ⟨⟨x, hKU hx⟩, hzL ⟨x, hKU hx⟩⟩)
    choose C hC hbound using fun z : U ↦ (hpV z).2 (L z) (hLV z) (hL z) i j
    refine ⟨∑ z ∈ t, C z, Finset.sum_nonneg (fun z _ ↦ hC z), ?_⟩
    intro x hx ξ
    obtain ⟨z, hzt, hxz⟩ := Set.mem_iUnion₂.mp (ht hx)
    apply (hbound z x (interior_subset hxz) ξ).trans
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
    exact Finset.single_le_sum (fun z _ ↦ hC z) hzt

/-- The actual pointwise product, packaged in the order-l+m symbol module. -/
def atlasGlobalSymbolSpaceComp {l m : ℝ}
    (b : atlasGlobalSymbolSpace B C l) (a : atlasGlobalSymbolSpace A B m) :
    atlasGlobalSymbolSpace A C (l + m) :=
  ⟨atlasSymbolComp b.val a.val, b.property.atlasSymbolComp a.property⟩

/-- The filtered composition is independent of both representatives in the principal quotient. -/
theorem atlasGlobalPrincipalSymbolClass_comp_congr {l m : ℝ}
    (b b' : atlasGlobalSymbolSpace B C l) (a a' : atlasGlobalSymbolSpace A B m)
    (hb : atlasGlobalPrincipalSymbolClass B C l b =
      atlasGlobalPrincipalSymbolClass B C l b')
    (ha : atlasGlobalPrincipalSymbolClass A B m a =
      atlasGlobalPrincipalSymbolClass A B m a') :
    atlasGlobalPrincipalSymbolClass A C (l + m) (atlasGlobalSymbolSpaceComp b a) =
      atlasGlobalPrincipalSymbolClass A C (l + m) (atlasGlobalSymbolSpaceComp b' a') := by
  /- Stage 1: quotient equality gives the actual lower-order differences
  b-b' and a-a'. On each original fiber expand ba-b'a' as
  (b-b')a + b'(a-a'), keeping the noncommuting factors in this order.
  Stage 2: the two filtered composition estimates have orders
  (l-1)+m and l+(m-1). Both are l+m-1. Closure under addition and the
  original quotient equality criterion prove the displayed equality.
  This uses no homogeneous representatives or operator choices. -/
  -- The original quotient equalities supply the actual one-order-lower differences.
  have hb' := (atlasGlobalPrincipalSymbolClass_eq_iff B C l b b').mp hb
  have ha' := (atlasGlobalPrincipalSymbolClass_eq_iff A B m a a').mp ha
  have hleft : IsAtlasGlobalSymbol A C (l + m - 1)
      (atlasSymbolComp (b.val - b'.val) a.val) := by
    convert hb'.atlasSymbolComp a.property using 1
    ring
  have hright : IsAtlasGlobalSymbol A C (l + m - 1)
      (atlasSymbolComp b'.val (a.val - a'.val)) := by
    convert b'.property.atlasSymbolComp ha' using 1
    ring
  -- Expand in the actual Hom fibers while retaining the noncommutative factor order.
  apply (atlasGlobalPrincipalSymbolClass_eq_iff A C (l + m) _ _).mpr
  change IsAtlasGlobalSymbol A C (l + m - 1)
    (atlasSymbolComp b.val a.val - atlasSymbolComp b'.val a'.val)
  have hexpand : atlasSymbolComp b.val a.val - atlasSymbolComp b'.val a'.val =
      atlasSymbolComp (b.val - b'.val) a.val + atlasSymbolComp b'.val (a.val - a'.val) := by
    funext x ξ
    apply LinearMap.ext
    intro v
    simp only [atlasSymbolComp, Pi.sub_apply, Pi.add_apply, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.comp_apply, map_sub]
    abel
  rw [hexpand]
  exact (isAtlasGlobalSymbol_closure A C (l + m - 1)).2.1 _ _ hleft hright

/-- Actual fiberwise composition descended through both principal-symbol quotients. -/
def atlasGlobalPrincipalSymbolComp {l m : ℝ} :
    AtlasGlobalPrincipalSymbolSpace B C l → AtlasGlobalPrincipalSymbolSpace A B m →
      AtlasGlobalPrincipalSymbolSpace A C (l + m) :=
  Quotient.lift₂
    (fun b a ↦
      atlasGlobalPrincipalSymbolClass A C (l + m) (atlasGlobalSymbolSpaceComp b a))
    (fun b a b' a' hb ha ↦ atlasGlobalPrincipalSymbolClass_comp_congr b b' a a'
      (Quotient.sound hb) (Quotient.sound ha))

/-- Any specified representatives compute the quotient product by their original fiber maps. -/
theorem atlasGlobalPrincipalSymbolComp_class {l m : ℝ}
    (b : atlasGlobalSymbolSpace B C l) (a : atlasGlobalSymbolSpace A B m) :
    atlasGlobalPrincipalSymbolComp (atlasGlobalPrincipalSymbolClass B C l b)
        (atlasGlobalPrincipalSymbolClass A B m a) =
      atlasGlobalPrincipalSymbolClass A C (l + m) (atlasGlobalSymbolSpaceComp b a) := by
  /- Evaluate the two quotient lifts on these exact representatives.
  Their congruence certificate establishes well-definedness; the value
  remains precisely the class of the original pointwise composition.
  In particular no separately chosen full symbol occurs in this formula. -/
  rfl

end AtiyahSinger
