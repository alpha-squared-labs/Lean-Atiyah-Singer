/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedOperatorKernels

/-!
# Closed joint zero modes under a bounded Green splitting

Public module ID: M0339.

An exact bounded splitting and the projected smooth coefficient graph persist
on the original simultaneous graph closure. Isometric coefficient embeddings
make the actual closed coefficient graph image closed. A joint zero mode is
therefore the image of a zero mode of that same coefficient operator.
No identification with intersections of separate closures is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

/-- A bounded Green splitting reduces original closed joint zero modes to the coefficient kernel. -/
theorem ker_le_map_of_closedJointGreenSplitting
    {S X Y Z C₀ C₁ : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z]
    [NormedAddCommGroup C₀] [NormedSpace ℂ C₀] [CompleteSpace C₀]
    [NormedAddCommGroup C₁] [NormedSpace ℂ C₁] [CompleteSpace C₁]
    (i : S →ₗ[ℂ] X) (h : S →ₗ[ℂ] Y) (v : S →ₗ[ℂ] Z)
    (R : X →ₗ.[ℂ] (Y × Z))
    (hR : R.graph = (i.prod (h.prod v)).range.topologicalClosure)
    (L : C₀ →ₗ.[ℂ] C₁) (hL : L.IsClosed)
    (e₀ : C₀ →ₗᵢ[ℂ] X) (e₁ : C₁ →ₗᵢ[ℂ] Y)
    (P₀ : X →L[ℂ] X) (P₁ : Y →L[ℂ] Y) (G : Z →L[ℂ] X)
    (hsplit : ∀ s : S, P₀ (i s) = i s - G (v s))
    (hcoefficient : ∀ s : S, (P₀ (i s), P₁ (h s)) ∈
      L.graph.map (e₀.toLinearMap.prodMap e₁.toLinearMap)) :
    R.ker ≤ L.ker.map e₀.toLinearMap := by
  let I := L.graph.map (e₀.toLinearMap.prodMap e₁.toLinearMap)
  have hI : IsClosed (I : Set (X × Y)) := by
    exact (e₀.isometry.prodMap e₁.isometry).isClosedEmbedding.isClosedMap _ hL
  -- The projected coefficient graph is closed in the original ambient product.
  let F : (X × Y × Z) →L[ℂ] X × Y :=
    (P₀.comp (ContinuousLinearMap.fst ℂ X (Y × Z))).prod
      (P₁.comp ((ContinuousLinearMap.fst ℂ Y Z).comp
        (ContinuousLinearMap.snd ℂ X (Y × Z))))
  have hproject : R.graph ≤ I.comap F.toLinearMap := by
    rw [hR]
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨s, rfl⟩
      exact hcoefficient s
    · exact hI.preimage F.continuous
  -- The same bounded Green identity also extends on the full joint graph closure.
  let D : (X × Y × Z) →L[ℂ] X :=
    P₀.comp (ContinuousLinearMap.fst ℂ X (Y × Z)) -
      ContinuousLinearMap.fst ℂ X (Y × Z) +
      G.comp ((ContinuousLinearMap.snd ℂ Y Z).comp
        (ContinuousLinearMap.snd ℂ X (Y × Z)))
  have hdefect : R.graph ≤ D.ker := by
    rw [hR]
    apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨s, rfl⟩
      change P₀ (i s) - i s + G (v s) = 0
      rw [hsplit]
      abel
    · exact D.isClosed_ker
  intro x hx
  obtain ⟨u, hu, hRu⟩ := R.mem_ker_iff.mp hx
  have hxgraph : (x, (0, 0)) ∈ R.graph :=
    R.mem_graph_iff.mpr ⟨u, hu.symm, hRu⟩
  have hfixed : P₀ x = x := by
    have hz := hdefect hxgraph
    change P₀ x - x + G 0 = 0 at hz
    simpa only [map_zero, add_zero, sub_eq_zero] using hz
  have hpair := hproject hxgraph
  change (P₀ x, P₁ 0) ∈ I at hpair
  rw [hfixed, map_zero] at hpair
  obtain ⟨⟨c, d⟩, hcd, he⟩ := hpair
  have hc : e₀ c = x := congrArg Prod.fst he
  have hd : e₁ d = 0 := congrArg Prod.snd he
  have hdzero : d = 0 := e₁.injective (hd.trans e₁.map_zero.symm)
  obtain ⟨w, hw, hLw⟩ := L.mem_graph_iff.mp hcd
  have hckernel : c ∈ L.ker := L.mem_ker_iff.mpr ⟨w, hw.symm, hLw.trans hdzero⟩
  exact ⟨c, hckernel, hc⟩

end AtiyahSinger
