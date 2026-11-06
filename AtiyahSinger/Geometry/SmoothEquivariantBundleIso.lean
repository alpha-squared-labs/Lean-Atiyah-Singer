/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothEquivariantBundle

/-!
# Smooth equivariant actions under actual bundle isomorphisms

Public module ID: M1392.

A smooth fiber isomorphism which intertwines two continuous bundle actions
transports joint smoothness of the action. The proof uses the specified map
and its inverse in the original local frames. This is the local matrix
criterion for equivariant bundles, needed when identifying relative smooth
realizations on a common open submanifold in analytic excision.

No compactness, fixed point, invariant metric or finite-dimensional group
hypothesis is needed. Empty model fibers remain covered by the finite sums.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 30

variable {VG HG G : Type*} [NormedAddCommGroup VG] [NormedSpace ℝ VG]
  [TopologicalSpace HG] (IG : ModelWithCorners ℝ VG HG)
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace HG G]
  {n r q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [MulAction G M] [ContinuousSMul G M]
  [ContMDiffSMul IG 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ G M]
  {E F : M → Type*}
  [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]
  [∀ x, NormedAddCommGroup (F x)] [∀ x, NormedSpace ℂ (F x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin q)) F)]
  [FiberBundle (EuclideanSpace ℂ (Fin q)) F]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin q)) F]

local notation "I" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))

set_option maxHeartbeats 1600000 in
-- Compose the inverse frame map, joint action and forward frame map on one moving overlap.
/-- A specified smooth equivariant bundle isomorphism transports joint smoothness. -/
theorem EquivariantStructure.IsSmooth.of_iso
    (σ : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      EquivariantStructure G E)
    (τ : letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      EquivariantStructure G F)
    (hσ : σ.IsSmooth (n := n) (r := r) IG)
    (e : ∀ x, E x ≃ₗ[ℂ] F x)
    (he : IsSmoothBundleMap (n := n) (r := r) (q := q)
      (fun x ↦ (e x).toLinearMap))
    (heq : letI := modelTopology (EuclideanSpace ℂ (Fin r)) E
      letI := modelTopology (EuclideanSpace ℂ (Fin q)) F
      ∀ (g : G) (x : M) (v : E x),
      e (g • x) (σ.linearMap g x v) = τ.linearMap g x (e x v)) :
    τ.IsSmooth (n := n) (r := q) IG := by
  classical
  let := modelTopology (EuclideanSpace ℂ (Fin r)) E
  let := modelTopology (EuclideanSpace ℂ (Fin q)) F
  have hei := he.symm e
  intro f₀ f₁ hf₀ hf₁ j p hp
  let := hf₀
  let := hf₁
  let d₀ := trivializationAt (EuclideanSpace ℂ (Fin r)) E p.2
  let d₁ := trivializationAt (EuclideanSpace ℂ (Fin r)) E (p.1 • p.2)
  let S : Set (G × M) := {z | z.2 ∈ f₀.baseSet ∧ z.2 ∈ d₀.baseSet ∧
    z.1 • z.2 ∈ d₁.baseSet ∧ z.1 • z.2 ∈ f₁.baseSet}
  have hact : ContMDiff (IG.prod I) I ∞
      (fun z : G × M ↦ z.1 • z.2) := ContMDiffSMul.contMDiff_smul
  have hS : IsOpen S :=
    (f₀.open_baseSet.preimage continuous_snd).inter
      ((d₀.open_baseSet.preimage continuous_snd).inter
        ((d₁.open_baseSet.preimage hact.continuous).inter
          (f₁.open_baseSet.preimage hact.continuous)))
  have hpS : p ∈ S := ⟨hp.1, mem_baseSet_trivializationAt _ _ _,
    mem_baseSet_trivializationAt _ _ _, hp.2⟩
  -- The first matrix is the actual inverse of the given fiber map at the source point.
  let a (z : G × M) : EuclideanSpace ℂ (Fin r) :=
    (d₀ ⟨z.2, (e z.2).symm
      (f₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2
  have ha : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞ a S :=
    (hei f₀ d₀ j).comp contMDiff_snd.contMDiffOn (fun _ hz ↦ ⟨hz.1, hz.2.1⟩)
  let b (k : Fin r) (z : G × M) : EuclideanSpace ℂ (Fin r) :=
    (d₁ ⟨z.1 • z.2, σ.linearMap z.1 z.2
      (d₀.symmL ℂ z.2 (EuclideanSpace.single k 1))⟩).2
  have hb (k : Fin r) :
      ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin r)) ∞ (b k) S :=
    (hσ d₀ d₁ k).mono (fun _ hz ↦ ⟨hz.2.1, hz.2.2.1⟩)
  -- The last matrix is the same forward isomorphism at the moved point.
  let c (l : Fin r) (z : G × M) : EuclideanSpace ℂ (Fin q) :=
    (f₁ ⟨z.1 • z.2, e (z.1 • z.2)
      (d₁.symmL ℂ (z.1 • z.2) (EuclideanSpace.single l 1))⟩).2
  have hc (l : Fin r) :
      ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞ (c l) S :=
    (he d₁ f₁ l).comp hact.contMDiffOn (fun _ hz ↦ hz.2.2)
  have hcoord {s : ℕ} (f : G × M → EuclideanSpace ℂ (Fin s))
      (hf : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin s)) ∞ f S)
      (i : Fin s) : ContMDiffOn (IG.prod I) 𝓘(ℝ, ℂ) ∞ (fun z ↦ f z i) S :=
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin s ↦ ℂ) i).restrictScalars ℝ).contMDiff
      |>.comp_contMDiffOn hf
  have hsum : ContMDiffOn (IG.prod I) 𝓘(ℝ, EuclideanSpace ℂ (Fin q)) ∞
      (fun z ↦ ∑ k : Fin r, ∑ l : Fin r, (a z k * b k z l) • c l z) S := by
    apply contMDiffOn_finsetSum
    intro k _
    apply contMDiffOn_finsetSum
    intro l _
    have hmul : ContDiff ℝ ∞
        (fun w : ℂ × EuclideanSpace ℂ (Fin q) ↦ w.1 • w.2) := contDiff_smul
    have hprod : ContDiff ℝ ∞ (fun w : ℂ × ℂ ↦ w.1 * w.2) := contDiff_mul
    have hcoeff := hprod.contMDiff.comp_contMDiffOn
      ((hcoord a ha k).prodMk_space (hcoord (b k) (hb k) l))
    exact hmul.contMDiff.comp_contMDiffOn
      (hcoeff.prodMk_space (hc l))
  -- Reconstruct both intermediate vectors in their original frames, then use intertwining.
  have hlocal := hsum.congr (f₁ := fun z ↦
    (f₁ ⟨z.1 • z.2, τ.linearMap z.1 z.2
      (f₀.symmL ℂ z.2 (EuclideanSpace.single j 1))⟩).2) ?_
  · exact (hlocal.contMDiffAt (hS.mem_nhds hpS)).contMDiffWithinAt
  · intro z hz
    let v := (e z.2).symm (f₀.symmL ℂ z.2 (EuclideanSpace.single j 1))
    let L := (f₁.linearMapAt ℂ (z.1 • z.2)).comp
      ((e (z.1 • z.2)).toLinearMap.comp (σ.linearMap z.1 z.2))
    have hfirst := congrArg (L.comp (d₀.symmL ℂ z.2).toLinearMap)
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (a z))
    have hsecond (k : Fin r) := congrArg
      ((f₁.linearMapAt ℂ (z.1 • z.2)).comp
        ((e (z.1 • z.2)).toLinearMap.comp (d₁.symmL ℂ (z.1 • z.2)).toLinearMap))
      ((EuclideanSpace.basisFun (Fin r) ℂ).sum_repr (b k z))
    have hsecond' (k : Fin r) :
        (f₁ ⟨z.1 • z.2, e (z.1 • z.2) (σ.linearMap z.1 z.2
          (d₀.symmL ℂ z.2 (EuclideanSpace.single k 1)))⟩).2 =
            ∑ l : Fin r, b k z l • c l z := by
      simpa [c, b, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, f₁.coe_linearMapAt_of_mem hz.2.2.2,
        d₁.symmL_apply hz.2.2.1, d₁.symm_apply_apply_mk hz.2.2.1] using hsecond k |>.symm
    have hfirst' :
        (f₁ ⟨z.1 • z.2, e (z.1 • z.2) (σ.linearMap z.1 z.2 v)⟩).2 =
          ∑ k : Fin r, a z k •
            (f₁ ⟨z.1 • z.2, e (z.1 • z.2) (σ.linearMap z.1 z.2
              (d₀.symmL ℂ z.2 (EuclideanSpace.single k 1)))⟩).2 := by
      simpa [L, v, a, map_sum, map_smul, EuclideanSpace.basisFun_apply,
        EuclideanSpace.basisFun_repr, f₁.coe_linearMapAt_of_mem hz.2.2.2,
        d₀.symmL_apply hz.2.1, d₀.symm_apply_apply_mk hz.2.1] using hfirst.symm
    rw [heq, show e z.2 v = f₀.symmL ℂ z.2 (EuclideanSpace.single j 1) from
      (e z.2).apply_symm_apply _] at hfirst'
    rw [hfirst']
    simp only [hsecond', Finset.smul_sum, smul_smul]

end AtiyahSinger.ComplexBundle
