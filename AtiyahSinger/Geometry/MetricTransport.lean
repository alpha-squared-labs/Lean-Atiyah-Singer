/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.HermitianMetric
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback

/-!
# Transport of smooth Hermitian metrics

Public module ID: M1301.

D02/E01: pull a positive smooth form back along a specified smooth bundle
isomorphism or a smooth base map. The conclusions specify every original fiber
pairing; neither operation installs a new norm. HU III.9 gives the standard metric
data; these smooth transport statements are project supplements for SG III.13.4.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff ComplexConjugate

set_option maxSynthPendingDepth 25

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
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

include hM

set_option linter.unusedSectionVars false in
/-- Pulling a metric through a smooth fiber equivalence on the original smooth bundle
determines a unique smooth metric. -/
theorem SmoothHermitianMetric.existsUnique_transport
    [hE : IsSmoothComplexBundle (n := n) (r := r) E]
    (k : SmoothHermitianMetric (n := n) (r := q) F) (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q) (fun x ↦ (e x).toLinearMap)) :
    ∃! h : SmoothHermitianMetric (n := n) (r := r) E,
      ∀ (x : M) (v w : E x), h.pairing x v w = k.pairing x (e x v) (e x w) := by
  classical
  -- Pull back the positive forms themselves, retaining the given fiber norms.
  let core (x : M) : InnerProductSpace.Core ℂ (E x) := {
    inner := fun v w ↦ k.pairing x (e x v) (e x w)
    conj_inner_symm := fun v w ↦ (k.toCore x).conj_inner_symm _ _
    re_inner_nonneg := fun v ↦ (k.toCore x).re_inner_nonneg _
    add_left := by
      intro u v w
      rw [(e x).map_add]
      exact (k.toCore x).add_left _ _ _
    smul_left := by
      intro v w c
      change k.pairing x (e x (c • v)) (e x w) = _
      rw [(e x).map_smul]
      exact (k.toCore x).smul_left _ _ _
    definite := by
      intro v hv
      apply (e x).injective
      exact ((k.toCore x).definite _ hv).trans ((e x).map_zero.symm) }
  have hsmooth : ∀ (d : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) E)) [MemTrivializationAtlas d],
      ∀ i j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ (core x).inner (d.symmL ℂ x (EuclideanSpace.single i 1))
            (d.symmL ℂ x (EuclideanSpace.single j 1))) d.baseSet := by
    intro d hd i j x hx
    let f := trivializationAt (EuclideanSpace ℂ (Fin q)) F x
    have hfx : x ∈ f.baseSet := mem_baseSet_trivializationAt _ _ x
    -- On this overlap, the exact transported Gram entry is the finite sum A* G A.
    have hcolumn (a : Fin r) (b : Fin q) :
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
          (fun y ↦ (f ⟨y, e y (d.symmL ℂ y (EuclideanSpace.single a 1))⟩).2 b)
          (d.baseSet ∩ f.baseSet) :=
      ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin q ↦ ℂ) b).restrictScalars ℝ).contMDiff
        |>.comp_contMDiffOn (he d f a)
    have hsum : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ ∑ a, ∑ b,
          conj ((f ⟨y, e y (d.symmL ℂ y (EuclideanSpace.single i 1))⟩).2 a) *
            k.gramMatrix f y a b *
              (f ⟨y, e y (d.symmL ℂ y (EuclideanSpace.single j 1))⟩).2 b)
        (d.baseSet ∩ f.baseSet) := by
      apply contMDiffOn_finsetSum
      intro a _
      apply contMDiffOn_finsetSum
      intro b _
      have hconj := Complex.conjCLE.contDiff.contMDiff.comp_contMDiffOn (hcolumn i a)
      have hgram := (k.contMDiffOn_gram f a b).mono
        (Set.inter_subset_right (s := d.baseSet))
      have hmul : ContDiff ℝ ∞ (fun p : ℂ × ℂ ↦ p.1 * p.2) := contDiff_mul
      exact hmul.contMDiff.comp_contMDiffOn
        ((hmul.contMDiff.comp_contMDiffOn (hconj.prodMk_space hgram)).prodMk_space
          (hcolumn j b))
    have hlocal := hsum.congr (f₁ := fun y ↦ (core y).inner
      (d.symmL ℂ y (EuclideanSpace.single i 1))
      (d.symmL ℂ y (EuclideanSpace.single j 1))) (by
        intro y hy
        exact k.pairing_eq_gramMatrix f y hy.2 _ _)
    exact (hlocal.contMDiffAt
      ((d.open_baseSet.inter f.open_baseSet).mem_nhds ⟨hx, hfx⟩)).contMDiffWithinAt
  let h : SmoothHermitianMetric (n := n) (r := r) E := ⟨core, hsmooth, hE⟩
  refine ⟨h, fun _ _ _ ↦ rfl, ?_⟩
  -- The specified pairing fixes the entire form; all remaining fields are proofs.
  intro h' hh'
  cases h' with
  | mk hCore hGram hBundle =>
    suffices hCore = core by
      subst hCore
      rfl
    funext x
    have hinner (v w : E x) : (hCore x).inner v w = (core x).inner v w := hh' x v w
    have core_ext (a b : InnerProductSpace.Core ℂ (E x))
        (hab : ∀ v w, a.inner v w = b.inner v w) : a = b := by
      rcases a with ⟨⟨⟨a⟩, _, _, _, _⟩, _⟩
      rcases b with ⟨⟨⟨b⟩, _, _, _, _⟩, _⟩
      have hab' : a = b := funext (fun v ↦ funext (hab v))
      subst b
      rfl
    exact core_ext _ _ hinner

set_option linter.unusedSectionVars false in
/-- Native smooth pullback carries the unique metric with the original fiber pairings. -/
theorem SmoothHermitianMetric.existsUnique_pullback
    (h : SmoothHermitianMetric (n := n) (r := r) E)
    {m : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) ∞ N]
    (f : C(N, M))
    (hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin m))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ f) :
    ∃! k : SmoothHermitianMetric (n := m) (r := r) ((f : N → M) *ᵖ E),
      ∀ (x : N) (v w : E (f x)), k.pairing x v w = h.pairing (f x) v w := by
  classical
  -- The pullback keeps exactly the original positive form on E(f(x)).
  let core (x : N) : InnerProductSpace.Core ℂ (((f : N → M) *ᵖ E) x) := h.toCore (f x)
  have hsmooth : ∀ (d : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) ((f : N → M) *ᵖ E))) [MemTrivializationAtlas d],
      ∀ i j : Fin r,
        ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 𝓘(ℝ, ℂ) ∞
          (fun x ↦ (core x).inner (d.symmL ℂ x (EuclideanSpace.single i 1))
            (d.symmL ℂ x (EuclideanSpace.single j 1))) d.baseSet := by
    rintro _ ⟨d, hd, rfl⟩ i j
    let := hd
    -- Every native pullback frame is an original frame evaluated at f(x).
    have hcomp := (h.contMDiffOn_gram d i j).comp hf.contMDiffOn (fun x hx ↦ hx)
    apply hcomp.congr
    intro x hx
    have hframe (v : EuclideanSpace ℂ (Fin r)) :
        (d.pullback f).symmL ℂ x v = d.symmL ℂ (f x) v := by
      rw [(d.pullback f).symmL_apply hx, d.symmL_apply hx]
      rw [(d.pullback f).symm_apply hx]
      rfl
    change (h.toCore (f x)).inner _ _ = _
    rw [hframe, hframe]
    rfl
  -- Pull back the original smooth transition atlas along the same base map.
  let : IsSmoothComplexBundle (n := n) (r := r) E := h.isSmoothBundle
  let k : SmoothHermitianMetric (n := m) (r := r) ((f : N → M) *ᵖ E) :=
    ⟨core, hsmooth, isSmoothComplexBundle_pullback E f hf⟩
  refine ⟨k, fun _ _ _ ↦ rfl, ?_⟩
  -- Pairwise equality on the same actual fibers determines the unique smooth metric.
  intro k' hk'
  cases k' with
  | mk kCore kGram kBundle =>
    suffices kCore = core by
      subst kCore
      rfl
    funext x
    have hinner (v w : E (f x)) : (kCore x).inner v w = (core x).inner v w := hk' x v w
    have core_ext (a b : InnerProductSpace.Core ℂ (E (f x)))
        (hab : ∀ v w, a.inner v w = b.inner v w) : a = b := by
      rcases a with ⟨⟨⟨a⟩, _, _, _, _⟩, _⟩
      rcases b with ⟨⟨⟨b⟩, _, _, _, _⟩, _⟩
      have hab' : a = b := funext (fun v ↦ funext (hab v))
      subst b
      rfl
    exact core_ext _ _ hinner

end AtiyahSinger
