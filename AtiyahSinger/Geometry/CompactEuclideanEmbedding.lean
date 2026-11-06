/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
public import Mathlib.Geometry.Manifold.ContMDiffMap
public import Mathlib.Geometry.Manifold.SmoothEmbedding
public import Mathlib.Geometry.Manifold.WhitneyEmbedding
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Proper Euclidean embeddings of compact smooth manifolds

Public module ID: M1129.

Mathlib's `exists_embedding_euclidean_of_compact` already constructs a smooth
closed embedding with injective manifold differential into some Euclidean
space. The finite-dimensional immersion criterion below upgrades its injective
differential to the local-normal-form predicate `IsSmoothEmbedding` for full real
models. The compact existence statement uses the same map and dimension supplied
by mathlib.

The existence conclusion gives some finite target dimension. It does not
assert the sharp Whitney dimension bound or the usual weak bound. Compactness
and Hausdorffness are sufficient for this imported construction; no extra
second-countability, nonemptiness or positive-dimension hypothesis is needed.
Indeed, a finite cover by second-countable chart domains gives second
countability in this compact finite-dimensional setting. Keeping the target
dimension unspecified also permits a zero-dimensional manifold with several
points; such a manifold need not embed into zero-dimensional Euclidean space.
The full model restriction excludes boundary and corner compatibility issues
from the immersion criterion.

Sources: HU XVIII.2, printed p.265, gives the inverse function theorem and
Definition 2.5's injective-differential immersion criterion, followed by its
local embedding consequence. The explicit normal form and fixed-complement
formulation below expand that standard argument. The global existence proof
is the finite smooth bump-cover construction already formalized in mathlib's
WhitneyEmbedding module; the dimension-bounded Whitney theorem is not used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Manifold Set Topology
open scoped ContDiff

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {M N : Type*}
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N]

/-- For finite-dimensional full real models, injective differential implies smooth immersion. -/
theorem isImmersion_of_injective_mfderiv
    (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, F) M N ∞)
    (hf : ∀ x : M, Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x)) :
    IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
  /- Stage 1: fix the common Euclidean complement model of dimension
  dim F - dim E. At a point x, the derivative in the original source
  and target charts is injective because it is the original mfderiv.
  Choose a genuine linear complement D to its target range.
  Stage 2: augment the local map by D. Its derivative is an isomorphism,
  so the smooth inverse function theorem gives an inverse chart.
  Restrict to the open locus of invertible derivatives and check both
  directions in the original maximal atlas. In these precise charts
  f has the form u ↦ e (u, 0), with e : E × D ≃L[ℝ] F.
  Full real models put this construction on open sets.
  Stage 3: the complement D has the fixed required dimension. Transfer
  each local normal form to the already selected common complement,
  then use the native immersion universe adapter. An empty source
  has no local conditions; zero-dimensional models use the same argument. -/
  classical
  -- Fix one complement model for every point; the local construction also works at rank zero.
  let C := EuclideanSpace ℝ (Fin (Module.finrank ℝ F - Module.finrank ℝ E))
  have hlocal : IsImmersionOfComplement C 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f := by
    intro x
    -- Work on the actual overlap of the original source and target charts.
    let φ := chartAt E x
    let ψ := chartAt F (f x)
    let a : E := φ x
    let g : E → F := ψ ∘ f ∘ φ.symm
    let Ω : Set E := φ.target ∩ φ.symm ⁻¹' (f ⁻¹' ψ.source)
    have hΩ : IsOpen Ω :=
      φ.isOpen_inter_preimage_symm (ψ.open_source.preimage f.contMDiff.continuous)
    have haΩ : a ∈ Ω := by
      simp [Ω, a, φ, ψ]
    have hg : ContDiffOn ℝ ∞ g Ω := by
      apply ContMDiffOn.contDiffOn
      apply (contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f x)).comp
      · exact f.contMDiff.comp_contMDiffOn
          ((contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x)).mono (fun y hy ↦ hy.1))
      · intro y hy
        exact hy.2
    have hga : ContDiffAt ℝ ∞ g a := hg.contDiffAt (hΩ.mem_nhds haΩ)
    -- The chart derivative is the original manifold derivative in its native coordinates.
    let L : E →L[ℝ] F := fderiv ℝ g a
    have hL : Function.Injective L := by
      have hd := (f.contMDiff x).mdifferentiableAt (by simp)
      have heq : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) f x) = L := by
        simp only [mfderiv, hd, ↓reduceIte, writtenInExtChartAt, mfld_simps,
          fderivWithin_univ]
        rfl
      exact heq ▸ hf x
    -- Add genuine complementary directions so that the augmented derivative is invertible.
    obtain ⟨D, hD⟩ := Submodule.exists_isCompl L.range
    let e : (E × D) ≃L[ℝ] F :=
      L.coprodSubtypeLEquivOfIsCompl hD (LinearMap.ker_eq_bot.mpr hL)
    have he (z : E × D) : e z = L z.1 + z.2.val := rfl
    let h : E × D → F := fun z ↦ g z.1 + z.2.val
    let W : Set (E × D) := Ω ×ˢ Set.univ
    have hW : IsOpen W := hΩ.prod isOpen_univ
    have haW : (a, (0 : D)) ∈ W := ⟨haΩ, trivial⟩
    have hh : ContDiffOn ℝ ∞ h W := by
      exact (hg.comp contDiff_fst.contDiffOn (fun z hz ↦ hz.1)).add
        ((D.subtypeL.contDiff.comp contDiff_snd).contDiffOn)
    have hha : ContDiffAt ℝ ∞ h (a, (0 : D)) := hh.contDiffAt (hW.mem_nhds haW)
    have hhd : HasFDerivAt h (e : E × D →L[ℝ] F) (a, 0) := by
      have hd := ((hga.differentiableAt (by simp)).hasFDerivAt.comp (a, (0 : D))
          (hasFDerivAt_fst (p := (a, (0 : D))))).add
        (D.subtypeL.hasFDerivAt.comp (a, (0 : D)) (hasFDerivAt_snd (p := (a, (0 : D)))))
      convert hd using 1
      · funext z
        rfl
      · apply ContinuousLinearMap.ext
        intro z
        exact he z
    -- Restrict the inverse-function chart to the open locus of invertible derivatives.
    -- This ensures that its inverse is smooth at every point of its entire target.
    let W' : Set (E × D) := W ∩ {z | (fderiv ℝ h z).IsInvertible}
    have hW' : IsOpen W' :=
      (hh.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW
        ContinuousLinearMap.isOpen_setOfPred_isInvertible
    have haW' : (a, (0 : D)) ∈ W' := by
      refine ⟨haW, ?_⟩
      exact ⟨e, hhd.fderiv.symm⟩
    let H₀ : OpenPartialHomeomorph (E × D) F :=
      hha.toOpenPartialHomeomorph h hhd (by simp)
    let H : OpenPartialHomeomorph (E × D) F := H₀.restr W'
    have hHsource : H.source ⊆ W' := by
      intro z hz
      exact hW'.interior_eq ▸ hz.2
    have haH : (a, (0 : D)) ∈ H.source := by
      exact ⟨hha.mem_toOpenPartialHomeomorph_source hhd (by simp),
        (by simpa only [hW'.interior_eq] using haW')⟩
    have hH (z : E × D) : H z = h z := rfl
    have hHcd : ContDiffOn ℝ ∞ H H.source := by
      exact hh.mono (fun z hz ↦ (hHsource hz).1)
    have hHinv : ContDiffOn ℝ ∞ H.symm H.target := by
      intro y hy
      have hp := hHsource (H.map_target hy)
      have hhp : ContDiffAt ℝ ∞ h (H.symm y) := hh.contDiffAt (hW.mem_nhds hp.1)
      obtain ⟨d, hd⟩ := hp.2
      have hd' : HasFDerivAt H (d : E × D →L[ℝ] F) (H.symm y) := by
        change HasFDerivAt h _ _
        rw [hd]
        exact (hhp.differentiableAt (by simp)).hasFDerivAt
      exact (H.contDiffAt_symm hy hd' hhp).contDiffWithinAt
    -- The inverse augmented map supplies a chart in the original target maximal atlas.
    -- Both chart directions are checked, rather than assuming an arbitrary inverse is smooth.
    let χ : OpenPartialHomeomorph N F :=
      ψ.trans (H.symm.trans e.toHomeomorph.toOpenPartialHomeomorph)
    have hχ : χ ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N := by
      apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
      · apply e.contDiff.contMDiff.comp_contMDiffOn
        apply (contMDiffOn_iff_contDiffOn.mpr hHinv).comp
          ((contMDiffOn_chart (I := 𝓘(ℝ, F)) (x := f x)).mono (fun z hz ↦ hz.1))
        intro z hz
        exact hz.2.1
      · apply (contMDiffOn_chart_symm (I := 𝓘(ℝ, F)) (x := f x)).comp
        · exact (contMDiffOn_iff_contDiffOn.mpr hHcd).comp
            e.symm.contDiff.contMDiff.contMDiffOn (fun z hz ↦ hz.1.2)
        · intro z hz
          exact hz.2
    -- Restrict the original source chart until every (u, 0) lies in that same inverse chart.
    let U : Set E := (fun u : E ↦ (u, (0 : D))) ⁻¹' H.source
    have hU : IsOpen U := H.open_source.preimage (continuous_id.prodMk continuous_const)
    let V : Set M := φ.source ∩ φ ⁻¹' U
    have hV : IsOpen V := φ.isOpen_inter_preimage hU
    let θ := φ.restr V
    have hxθ : x ∈ θ.source := by
      have hxV : x ∈ V := ⟨mem_chart_source E x, haH⟩
      change x ∈ φ.source ∩ interior V
      refine ⟨mem_chart_source E x, ?_⟩
      simpa only [hV.interior_eq] using hxV
    have hfxχ : f x ∈ χ.source := by
      refine ⟨mem_chart_source F (f x), ?_⟩
      refine ⟨?_, trivial⟩
      have heqa : h (a, (0 : D)) = ψ (f x) := by simp [h, g, a, φ]
      change ψ (f x) ∈ H.target
      rw [← heqa]
      exact H.map_source haH
    have hθ : θ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M :=
      restr_mem_maximalAtlas (contDiffGroupoid ∞ 𝓘(ℝ, E))
        (IsManifold.chart_mem_maximalAtlas x) hV
    -- In these precise charts the original map is exactly u ↦ e (u, 0).
    have hi : IsImmersionAtOfComplement D 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f x := by
      apply IsImmersionAtOfComplement.mk_of_continuousAt f.contMDiff.continuous.continuousAt e
        θ χ hxθ hfxχ hθ hχ
      intro u hu
      have hu' : u ∈ θ.target := by simpa only [mfld_simps] using hu
      have huθ : θ.symm u ∈ θ.source := θ.map_target hu'
      have huH : (u, (0 : D)) ∈ H.source := by
        have hv : θ.symm u ∈ V := hV.interior_eq ▸ huθ.2
        have heu : φ (θ.symm u) = u := θ.right_inv hu'
        exact heu ▸ hv.2
      change e (H.symm (ψ (f (φ.symm u)))) = e (u, 0)
      apply congrArg e
      simpa only [hH, h, g, Function.comp_apply, Submodule.coe_zero, add_zero] using H.left_inv huH
    -- Finite-dimensional complements all have the required fixed dimension.
    have hdim : Module.finrank ℝ D = Module.finrank ℝ F - Module.finrank ℝ E := by
      have hadd := Submodule.finrank_add_eq_of_isCompl hD
      rw [LinearMap.finrank_range_of_inj hL] at hadd
      omega
    have heC : D ≃L[ℝ] C := ContinuousLinearEquiv.ofFinrankEq (by simpa [C] using hdim)
    exact hi.trans_F heC
  -- The standard universe adapter treats an empty source vacuously; no point is selected.
  exact hlocal.isImmersion

/-- A compact Hausdorff smooth manifold has a proper smooth embedding in some Euclidean space. -/
theorem exists_proper_smoothEmbedding_euclidean [T2Space M] [CompactSpace M] :
    ∃ (n : ℕ)
      (f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        M (EuclideanSpace ℝ (Fin n)) ∞),
      IsSmoothEmbedding 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f ∧
        IsProperMap f := by
  /- Stage 1: apply the existing exists_embedding_euclidean_of_compact at the
  original full real model. It supplies one dimension n and one function e,
  together with smoothness, IsClosedEmbedding e and injectivity of every
  original mfderiv. Its finite smooth bump covering separates both points
  and tangent vectors before the finite product is identified with Euclidean
  space. The target dimension is unspecified; no sharp bound is used here.
  Stage 2: bundle this same e and its supplied smoothness as ContMDiffMap f.
  Apply isImmersion_of_injective_mfderiv to the same differential witnesses,
  and pair it with the original closed embedding's topological embedding.
  This gives IsSmoothEmbedding for that very f, with no replacement map or
  independently selected existence witness.
  Stage 3: use IsClosedEmbedding.isProperMap for the same original e and
  return n, f and both certificates together. Alternatively compact-source
  properness follows from f.continuous and the Hausdorff Euclidean target.
  The imported existence theorem and the immersion criterion both include
  empty M and zero-dimensional models. No second-countability assumption or
  positive target dimension is introduced. This is compact unbounded-dimension
  Whitney existence, not the sharp or dimension-bounded weak theorem. -/
  -- Retain the very same map and dimension constructed by the imported compact embedding theorem.
  obtain ⟨n, e, he, hemb, hderiv⟩ :=
    exists_embedding_euclidean_of_compact (I := 𝓘(ℝ, E)) (M := M)
  let f : ContMDiffMap 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      M (EuclideanSpace ℝ (Fin n)) ∞ := ⟨e, he⟩
  -- The normal-form criterion upgrades its actual differential certificate to an immersion.
  have himm : IsImmersion 𝓘(ℝ, E) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f :=
    isImmersion_of_injective_mfderiv f hderiv
  -- Its original closed embedding gives properness without choosing another embedding.
  exact ⟨n, f, ⟨himm, hemb.isEmbedding⟩, hemb.isProperMap⟩

end AtiyahSinger
