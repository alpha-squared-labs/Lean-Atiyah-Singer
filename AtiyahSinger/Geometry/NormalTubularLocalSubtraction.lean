/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Smooth local subtraction near the diagonal

Public module ID: M1312.

Every finite-dimensional sigma-compact Hausdorff smooth real manifold without boundary admits
smooth tangent-valued subtraction on a neighborhood of its diagonal. It vanishes on the diagonal,
and its derivative in the second variable is the identity on the native tangent space.

In each chart, coordinate subtraction is transported back by the inverse tangent trivialization.
A smooth partition of unity in the first variable combines these maps. Local finiteness supplies
an open neighborhood of the whole diagonal where every active chart also contains the second
point. The weights are constant when differentiating the second variable, so their sum equal to
one preserves the exact derivative normalization. Compactness and a uniform radius are not used.

The function `d` takes values in the model space, which represents each native tangent fiber.
Smoothness is asserted for the associated map into the actual tangent bundle, with its original
smooth atlas, rather than for this coordinate representation on the entire product.
This is a supplementary construction for smooth local additions and tubular neighborhoods.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle Filter Manifold Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Smooth tangent-valued subtraction exists near the diagonal, is zero on the diagonal,
and has identity differential in the second variable. -/
theorem exists_smooth_localSubtraction :
    ∃ (Ω : Set (M × M)) (d : M → M → E), IsOpen Ω ∧ (∀ x, (x, x) ∈ Ω) ∧
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
        (fun z : M × M ↦ (⟨z.1, d z.1 z.2⟩ : TangentBundle (𝓘(ℝ, E)) M)) Ω ∧
      (∀ x, d x x = 0) ∧
      ∀ x, HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (d x) x (ContinuousLinearMap.id ℝ E) := by
  classical
  -- Build coordinate subtraction in each original chart and its actual tangent trivialization.
  have hchart : ∀ c : M,
      ∃ d : M → M → E,
        ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
          (((𝓘(ℝ, E)).prod (𝓘(ℝ, E))).prod (𝓘(ℝ, E × E))) ∞
          (fun z : M × M ↦ (⟨z, (d z.1 z.2, 0)⟩ :
            TangentBundle ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M)))
          ((chartAt E c).source ×ˢ (chartAt E c).source) ∧
        (∀ x, d x x = 0) ∧
        ∀ x ∈ (chartAt E c).source,
          HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (d x) x (ContinuousLinearMap.id ℝ E) := by
    intro c
    let φ := chartAt E c
    let e := trivializationAt E (TangentSpace (𝓘(ℝ, E))) c
    let d : M → M → E := fun x y ↦ e.symmL ℝ x (φ y - φ x)
    -- The inverse tangent trivialization gives smoothness of the local tangent-valued map.
    have hfirst : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
        (fun z : M × M ↦ (⟨z.1, d z.1 z.2⟩ : TangentBundle (𝓘(ℝ, E)) M))
        (φ.source ×ˢ φ.source) := by
      have hcoords : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
          ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
          (fun z : M × M ↦ (z.1, φ z.2 - φ z.1)) (φ.source ×ˢ φ.source) := by
        apply contMDiffOn_fst.prodMk
        exact ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := c)).comp
          contMDiffOn_snd (fun z hz ↦ hz.2)).sub
          ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (x := c)).comp
            contMDiffOn_fst (fun z hz ↦ hz.1))
      apply (e.contMDiffOn_symm.comp hcoords (fun z hz ↦ ⟨hz.1, trivial⟩)).congr
      intro z hz
      change (⟨z.1, e.symmL ℝ z.1 (φ z.2 - φ z.1)⟩ : TangentBundle (𝓘(ℝ, E)) M) = _
      rw [e.symmL_apply hz.1]
      exact e.mk_symm hz.1 _
    refine ⟨d, ?_, ?_, ?_⟩
    · exact (contMDiff_equivTangentBundleProd_symm (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))).comp_contMDiffOn
        (hfirst.prodMk
          ((contMDiff_zeroSection ℝ (TangentSpace (𝓘(ℝ, E)))).comp contMDiff_snd).contMDiffOn)
    · intro x
      simp [d]
      rfl
    · intro x hx
      -- The chart differential and the inverse fiber trivialization cancel exactly.
      have hφ : MDifferentiableAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x :=
        ((contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := c)).contMDiffAt
          (φ.open_source.mem_nhds hx)).mdifferentiableAt (by simp)
      let L : E →L[ℝ] E := e.symmL ℝ x
      let A : E →L[ℝ] E := mfderiv (𝓘(ℝ, E)) (𝓘(ℝ, E)) φ x
      let B : E →L[ℝ] E := e.continuousLinearMapAt ℝ x
      have hh := (L.hasFDerivAt.hasMFDerivAt).comp x
        (hφ.hasMFDerivAt.sub (hasMFDerivAt_const (φ x) x))
      have hchart : B = A := by
        simpa only [mfld_simps] using!
          (TangentBundle.continuousLinearMapAt_trivializationAt (I := 𝓘(ℝ, E)) hx)
      have hderiv : L.comp (A - 0) =
          ContinuousLinearMap.id ℝ E := by
        ext v
        change L (A v - 0) = v
        rw [sub_zero, ← hchart]
        exact e.symmL_continuousLinearMapAt hx v
      exact hderiv ▸ hh
  choose dc hdc hzero hderiv using hchart
  -- Local finiteness permits a common open domain for every chart active at the first point.
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source (𝓘(ℝ, E)) M
  let bad : M → Set (M × M) := fun c ↦ tsupport (ρ c) ×ˢ (chartAt E c).sourceᶜ
  have hbadfin : LocallyFinite bad := ρ.locallyFinite.closure.prod_right _
  have hbadclosed : ∀ c, IsClosed (bad c) := fun c ↦
    (isClosed_tsupport _).prod (chartAt E c).open_source.isClosed_compl
  let Ω : Set (M × M) := (⋃ c, bad c)ᶜ
  have hΩ : IsOpen Ω := (hbadfin.isClosed_iUnion hbadclosed).isOpen_compl
  have hdiag : ∀ x, (x, x) ∈ Ω := by
    intro x hx
    obtain ⟨c, hc⟩ := mem_iUnion.mp hx
    exact hc.2 (hρ c hc.1)
  -- Work first in the product tangent bundle so that section sums use the standard bundle API.
  let t : M → (z : M × M) → TangentSpace ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) z :=
    fun c z ↦ ρ c z.1 • (dc c z.1 z.2, 0)
  have htfin : LocallyFinite (fun c ↦ {z : M × M | t c z ≠ 0}) := by
    apply (ρ.locallyFinite.preimage_continuous continuous_fst).subset
    intro c z hz
    exact left_ne_zero_of_smul hz
  have htsmooth (c : M) :
      ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E)))
        (((𝓘(ℝ, E)).prod (𝓘(ℝ, E))).prod (𝓘(ℝ, E × E))) ∞
        (fun z : M × M ↦ (⟨z, t c z⟩ :
          TangentBundle ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M))) Ω := by
    intro z hz
    apply ContMDiffAt.contMDiffWithinAt
    by_cases hzc : z.1 ∈ tsupport (ρ c)
    · have hzchart : z ∈ (chartAt E c).source ×ˢ (chartAt E c).source := by
        refine ⟨hρ c hzc, ?_⟩
        by_contra hn
        exact hz (mem_iUnion_of_mem c ⟨hzc, hn⟩)
      exact (((ρ c).contMDiff.comp contMDiff_fst).contMDiffAt).smul_section
        ((hdc c).contMDiffAt
          (((chartAt E c).open_source.prod (chartAt E c).open_source).mem_nhds hzchart))
    · apply (contMDiffAt_zeroSection ℝ
        (TangentSpace ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))))).congr_of_eventuallyEq
      have heq : ∀ᶠ y in 𝓝 z.1, ρ c y = 0 := notMem_tsupport_iff_eventuallyEq.mp hzc
      filter_upwards [continuous_fst.continuousAt heq] with p hp
      have hp' : ρ c p.1 = 0 := hp
      apply congrArg (fun v : E × E ↦ (⟨p, v⟩ :
        TangentBundle ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M)))
      change ρ c p.1 • (dc c p.1 p.2, (0 : E)) = (0 : E × E)
      rw [hp', zero_smul]
  -- The sum is smooth; projection to the first tangent factor is the actual tangent map.
  have hsumSmooth := ContMDiffOn.finsum_section_of_locallyFinite htfin htsmooth
  let d : M → M → E := fun x y ↦ (∑ᶠ c, t c (x, y)).1
  have hsum (x y : M) : d x y = ∑ c ∈ ρ.finsupport x, ρ c x • dc c x y := by
    have hs : Function.support (fun c ↦ t c (x, y)) ⊆ (ρ.finsupport x : Set M) := by
      intro c hc
      exact (ρ.mem_finsupport x).mpr (left_ne_zero_of_smul hc)
    change (∑ᶠ c, t c (x, y)).1 = _
    rw [finsum_eq_sum_of_support_subset _ hs]
    change (LinearMap.fst ℝ E E)
      (∑ c ∈ ρ.finsupport x, (ρ c x • (dc c x y, (0 : E)) : E × E)) = _
    rw [map_sum]
    rfl
  refine ⟨Ω, d, hΩ, hdiag, ?_, ?_, ?_⟩
  · have hmap : ContMDiff (((𝓘(ℝ, E)).prod (𝓘(ℝ, E))).prod (𝓘(ℝ, E × E)))
        ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
        (fun z : TangentBundle ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (M × M) ↦
          (⟨z.proj.1, z.snd.1⟩ : TangentBundle (𝓘(ℝ, E)) M)) := by
      have hfst := contMDiff_fst (I := 𝓘(ℝ, E)) (J := 𝓘(ℝ, E)) (M := M) (N := M) (n := ∞)
      apply (hfst.contMDiff_tangentMap (m := ∞) (by simp)).congr
      intro z
      exact (tangentMap_prodFst (p := z)).symm
    exact hmap.comp_contMDiffOn hsumSmooth
  · intro x
    rw [hsum]
    simp [hzero]
  · intro x
    -- For fixed x only finitely many constant weights occur, and their sum is one.
    have hdEq : d x = ∑ c ∈ ρ.finsupport x, ρ c x • dc c x := by
      funext y
      simpa only [Finset.sum_apply, Pi.smul_apply] using hsum x y
    rw [hdEq]
    have hterms : ∀ c ∈ ρ.finsupport x,
        HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, E)) (ρ c x • dc c x) x
          (ρ c x • ContinuousLinearMap.id ℝ E) := by
      intro c hc
      exact (hderiv c x (hρ c (subset_closure ((ρ.mem_finsupport x).mp hc)))).const_smul _
    have hsumDeriv := HasMFDerivAt.sum hterms
    have hId : (∑ c ∈ ρ.finsupport x, ρ c x • ContinuousLinearMap.id ℝ E) =
        ContinuousLinearMap.id ℝ E := by
      rw [← Finset.sum_smul, ρ.sum_finsupport x (mem_univ x), one_smul]
    exact hId ▸ hsumDeriv

end AtiyahSinger
