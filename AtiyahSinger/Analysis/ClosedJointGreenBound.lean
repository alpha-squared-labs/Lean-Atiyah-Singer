/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedJointKernelReduction
public import AtiyahSinger.Analysis.ClosedOperatorRange

/-!
# Closed range from the same joint Green splitting

Public module ID: M0338.

The original coefficient generalized inverse controls the projected graph.
The bounded Green defect controls the remaining vertical part. Orthogonal
projection removes exactly the image of the original coefficient kernel,
giving an ambient lower bound on the original joint domain. The actual joint
range is therefore closed and its kernel finite dimensional.

The target keeps its original product norm. No identification with a separate
closure intersection or replacement of the original coefficient inverse is used.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

set_option maxHeartbeats 600000 in

/-- The same bounded joint Green splitting gives a lower bound, closed range and finite kernel. -/
theorem exists_closedJointGreenBound
    {S X Y Z C₀ C₁ : Type*} [AddCommGroup S] [Module ℂ S]
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y] [CompleteSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [NormedAddCommGroup C₀] [InnerProductSpace ℂ C₀] [CompleteSpace C₀]
    [NormedAddCommGroup C₁] [InnerProductSpace ℂ C₁] [CompleteSpace C₁]
    (i : S →ₗ[ℂ] X) (h : S →ₗ[ℂ] Y) (v : S →ₗ[ℂ] Z)
    (R : X →ₗ.[ℂ] (Y × Z))
    (hR : R.graph = (i.prod (h.prod v)).range.topologicalClosure)
    (L : C₀ →ₗ.[ℂ] C₁) (hL : L.IsClosed) (hLdense : Dense (L.domain : Set C₀))
    (hLrange : IsClosed (L.toFun.range : Set C₁)) [FiniteDimensional ℂ L.ker]
    (e₀ : C₀ →ₗᵢ[ℂ] X) (e₁ : C₁ →ₗᵢ[ℂ] Y)
    (P₀ : X →L[ℂ] X) (P₁ : Y →L[ℂ] Y) (G : Z →L[ℂ] X)
    (hsplit : ∀ s : S, P₀ (i s) = i s - G (v s))
    (hcoefficient : ∀ s : S, (P₀ (i s), P₁ (h s)) ∈
      L.graph.map (e₀.toLinearMap.prodMap e₁.toLinearMap))
    (hkernel : L.ker.map e₀.toLinearMap ≤ R.ker) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ u : R.domain, (u : X) ∈ R.ker.orthogonal → ‖(u : X)‖ ≤ C * ‖R u‖) ∧
      IsClosed (R.toFun.range : Set (Y × Z)) ∧ FiniteDimensional ℂ R.ker := by
  have hreduce := ker_le_map_of_closedJointGreenSplitting
    i h v R hR L hL e₀ e₁ P₀ P₁ G hsplit hcoefficient
  have hfinite : FiniteDimensional ℂ R.ker :=
    FiniteDimensional.of_injective (Submodule.inclusion hreduce)
      (Submodule.inclusion_injective hreduce)
  let := hfinite
  have hRclosed : R.IsClosed := by
    change IsClosed (R.graph : Set (X × Y × Z))
    rw [hR]
    exact Submodule.isClosed_topologicalClosure _
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
  -- Use the bounded inverse of this same closed coefficient graph, with its actual range.
  obtain ⟨B, _, hBgraph⟩ := L.exists_bounded_generalizedInverse hLdense hL hLrange
  let C : ℝ := ‖B‖ * ‖P₁‖ + ‖G‖
  have hC : 0 ≤ C := add_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)
  have hbound (u : R.domain) (hu : (u : X) ∈ R.ker.orthogonal) :
      ‖(u : X)‖ ≤ C * ‖R u‖ := by
    let x : X := u
    let y : Y := (R u).1
    let z : Z := (R u).2
    have hxgraph : (x, (y, z)) ∈ R.graph := R.mem_graph u
    have hpair := hproject hxgraph
    change (P₀ x, P₁ y) ∈ I at hpair
    obtain ⟨⟨c, d⟩, hcd, he⟩ := hpair
    have hc : e₀ c = P₀ x := congrArg Prod.fst he
    have hd : e₁ d = P₁ y := congrArg Prod.snd he
    have hdRange : d ∈ L.toFun.range := LinearPMap.mem_range_iff.mpr ⟨c, hcd⟩
    have hdiff : c - B d ∈ L.ker := by
      have hg := L.graph.sub_mem hcd (hBgraph d hdRange)
      obtain ⟨w, hw, hLw⟩ := L.mem_graph_iff.mp hg
      exact L.mem_ker_iff.mpr ⟨w, hw.symm, hLw.trans (sub_self d)⟩
    let k : X := e₀ (c - B d)
    have hk : k ∈ R.ker := hkernel ⟨c - B d, hdiff, rfl⟩
    have hx : x = e₀ c + G z := by
      have hz := hdefect hxgraph
      change P₀ x - x + G z = 0 at hz
      rw [← hc] at hz
      apply sub_eq_zero.mp
      calc
        x - (e₀ c + G z) = -(e₀ c - x + G z) := by abel
        _ = 0 := by rw [hz, neg_zero]
    let w : X := e₀ (B d) + G z
    have hw : w = x - k := by
      rw [hx]
      change e₀ (B d) + G z = e₀ c + G z - e₀ (c - B d)
      rw [map_sub]
      abel
    -- Orthogonal projection removes the actual coefficient zero mode, with norm at most one.
    let K := R.ker.orthogonal
    let : CompleteSpace K := R.ker.isClosed_orthogonal.completeSpace_coe
    have hprojection : K.starProjection w = x := by
      rw [hw, map_sub, K.starProjection_eq_self_iff.mpr hu,
        K.starProjection_apply_eq_zero_iff.mpr (R.ker.le_orthogonal_orthogonal hk), sub_zero]
    have hxnorm : ‖x‖ ≤ ‖w‖ := by
      simpa only [hprojection] using K.norm_starProjection_apply_le w
    have hdnorm : ‖d‖ = ‖P₁ y‖ := (e₁.norm_map d).symm.trans (congrArg norm hd)
    have hy : ‖y‖ ≤ ‖R u‖ := le_max_left _ _
    have hz : ‖z‖ ≤ ‖R u‖ := le_max_right _ _
    calc
      ‖(u : X)‖ ≤ ‖w‖ := hxnorm
      _ ≤ ‖B d‖ + ‖G z‖ := by
        exact (norm_add_le _ _).trans_eq (congrArg (fun t ↦ t + ‖G z‖) (e₀.norm_map _))
      _ ≤ ‖B‖ * ‖d‖ + ‖G‖ * ‖z‖ := add_le_add (B.le_opNorm _) (G.le_opNorm _)
      _ ≤ ‖B‖ * (‖P₁‖ * ‖y‖) + ‖G‖ * ‖z‖ := by
        rw [hdnorm]
        exact add_le_add (mul_le_mul_of_nonneg_left (P₁.le_opNorm y) (norm_nonneg B)) le_rfl
      _ ≤ ‖B‖ * (‖P₁‖ * ‖R u‖) + ‖G‖ * ‖R u‖ := by
        gcongr
      _ = C * ‖R u‖ := by dsimp only [C]; ring
  -- The original graph norm is controlled on the same kernel complement; its range is closed.
  have hkerClosed : IsClosed (R.ker : Set X) := R.ker.closed_of_finiteDimensional
  let : CompleteSpace R.ker := hkerClosed.completeSpace_coe
  let J := R.graph ⊓ R.ker.orthogonal.comap (LinearMap.fst ℂ X (Y × Z))
  have hJ : IsClosed (J : Set (X × Y × Z)) :=
    hRclosed.inter (R.ker.isClosed_orthogonal.preimage continuous_fst)
  let : CompleteSpace J := hJ.completeSpace_coe
  let f : J →L[ℂ] Y × Z := (ContinuousLinearMap.snd ℂ X (Y × Z)).comp J.subtypeL
  have hanti : AntilipschitzWith (Real.toNNReal (max C 1)) f := by
    apply f.antilipschitz_of_bound
    intro z
    obtain ⟨u, hu, hRu⟩ := R.mem_graph_iff.mp z.property.1
    have huorth : (u : X) ∈ R.ker.orthogonal := hu ▸ z.property.2
    have hn := hbound u huorth
    rw [hu, hRu] at hn
    change max ‖z.val.1‖ ‖z.val.2‖ ≤ ↑(Real.toNNReal (max C 1)) * ‖z.val.2‖
    rw [Real.coe_toNNReal _ (le_max_of_le_right zero_le_one)]
    exact max_le (hn.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)))
      (by simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (le_max_right C 1) (norm_nonneg z.val.2))
  have hclosed : IsClosed (f.range : Set (Y × Z)) :=
    hanti.isClosed_range f.uniformContinuous
  have hrange : f.range = R.toFun.range := by
    apply le_antisymm
    · rintro y ⟨z, rfl⟩
      obtain ⟨u, _, hRu⟩ := R.mem_graph_iff.mp z.property.1
      exact ⟨u, hRu⟩
    · rintro y ⟨u, rfl⟩
      obtain ⟨k, hk, hRk⟩ := R.mem_ker_iff.mp (R.ker.starProjection_apply_mem (u : X))
      have hvorth : ((u - k : R.domain) : X) ∈ R.ker.orthogonal := by
        change (u : X) - k ∈ R.ker.orthogonal
        rw [← hk]
        exact R.ker.sub_starProjection_mem_orthogonal _
      refine ⟨⟨((↑(u - k) : X), R (u - k)), ⟨R.mem_graph _, hvorth⟩⟩, ?_⟩
      change R (u - k) = R u
      rw [R.map_sub, hRk, sub_zero]
  exact ⟨C, hC, hbound, hrange ▸ hclosed, hfinite⟩

end AtiyahSinger
