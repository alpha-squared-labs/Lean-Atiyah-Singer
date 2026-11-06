/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.HilbertTensorOperator

/-!
# Graded tensor cores inherited from specified factor cores

Public module ID: M0717.

If each factor graph and each adjoint graph is the closure of a specified
linear core, the original graded tensor graph is the closure of its two
corresponding core columns. The proof uses continuity of tensor products in
the graph coordinates; no equality merely on an algebraic domain is used to
identify the full closed operator.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open UniformSpace
open scoped TensorProduct

variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [CompleteSpace K₁]
  {S₀ S₁ T₀ T₁ : Type*}
  [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
  [AddCommGroup T₀] [Module ℂ T₀] [AddCommGroup T₁] [Module ℂ T₁]

/-- Specified dense graph cores in the factors give the same full closed graded tensor graph. -/
theorem gradedTensorOperator_graph_of_cores
    (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (i₀ : S₀ →ₗ[ℂ] H₀) (p : S₀ →ₗ[ℂ] H₁)
    (i₁ : S₁ →ₗ[ℂ] H₁) (pa : S₁ →ₗ[ℂ] H₀)
    (j₀ : T₀ →ₗ[ℂ] K₀) (q : T₀ →ₗ[ℂ] K₁)
    (j₁ : T₁ →ₗ[ℂ] K₁) (qa : T₁ →ₗ[ℂ] K₀)
    (hP : P.graph = (i₀.prod p).range.topologicalClosure)
    (hPa : P.adjoint.graph = (i₁.prod pa).range.topologicalClosure)
    (hQ : Q.graph = (j₀.prod q).range.topologicalClosure)
    (hQa : Q.adjoint.graph = (j₁.prod qa).range.topologicalClosure) :
    (gradedTensorOperator P Q).graph =
      (Submodule.span ℂ
        ((Set.range fun z : S₀ × T₀ ↦
          (WithLp.toLp 2 ((↑(i₀ z.1 ⊗ₜ[ℂ] j₀ z.2) : HilbertTensorProduct H₀ K₀), 0),
            WithLp.toLp 2 ((↑(p z.1 ⊗ₜ[ℂ] j₀ z.2) : HilbertTensorProduct H₁ K₀),
              (↑(i₀ z.1 ⊗ₜ[ℂ] q z.2) : HilbertTensorProduct H₀ K₁)))) ∪
        (Set.range fun z : S₁ × T₁ ↦
          (WithLp.toLp 2 (0, (↑(i₁ z.1 ⊗ₜ[ℂ] j₁ z.2) : HilbertTensorProduct H₁ K₁)),
            WithLp.toLp 2 (-(↑(i₁ z.1 ⊗ₜ[ℂ] qa z.2) : HilbertTensorProduct H₁ K₀),
              (↑(pa z.1 ⊗ₜ[ℂ] j₁ z.2) : HilbertTensorProduct H₀ K₁)))))).topologicalClosure := by
  let E := WithLp 2 (HilbertTensorProduct H₀ K₀ × HilbertTensorProduct H₁ K₁)
  let O := WithLp 2 (HilbertTensorProduct H₁ K₀ × HilbertTensorProduct H₀ K₁)
  let b₀ (x : H₀ × H₁) (y : K₀ × K₁) : E × O :=
    (WithLp.toLp 2 (↑(x.1 ⊗ₜ[ℂ] y.1), 0),
      WithLp.toLp 2 (↑(x.2 ⊗ₜ[ℂ] y.1), ↑(x.1 ⊗ₜ[ℂ] y.2)))
  let b₁ (x : H₁ × H₀) (y : K₁ × K₀) : E × O :=
    (WithLp.toLp 2 (0, ↑(x.1 ⊗ₜ[ℂ] y.1)),
      WithLp.toLp 2 (-(↑(x.1 ⊗ₜ[ℂ] y.2) : HilbertTensorProduct H₁ K₀),
        ↑(x.2 ⊗ₜ[ℂ] y.1)))
  let S := Submodule.span ℂ
    (Set.range (fun z : S₀ × T₀ ↦ b₀ (i₀ z.1, p z.1) (j₀ z.2, q z.2)) ∪
      Set.range (fun z : S₁ × T₁ ↦ b₁ (i₁ z.1, pa z.1) (j₁ z.2, qa z.2)))
  let C := S.topologicalClosure
  have hPclosed : P.IsClosed := by
    change IsClosed (P.graph : Set (H₀ × H₁))
    rw [hP]
    exact (i₀.prod p).range.isClosed_topologicalClosure
  have hQclosed : Q.IsClosed := by
    change IsClosed (Q.graph : Set (K₀ × K₁))
    rw [hQ]
    exact (j₀.prod q).range.isClosed_topologicalClosure
  rw [(gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed).2.1]
  change (gradedTensorGraph P Q).topologicalClosure = C
  -- A closed set containing the specified core columns contains every original domain column.
  have hfirst (x : H₀ × H₁) (hx : x ∈ P.graph)
      (y : K₀ × K₁) (hy : y ∈ Q.graph) : b₀ x y ∈ C := by
    rw [hP] at hx
    refine (S.isClosed_topologicalClosure.preimage
      (show Continuous (fun x ↦ b₀ x y) from by dsimp [b₀]; fun_prop)).closure_subset_iff.mpr
        ?_ hx
    rintro _ ⟨u, rfl⟩
    rw [hQ] at hy
    refine (S.isClosed_topologicalClosure.preimage
      (show Continuous (fun y ↦ b₀ ((i₀.prod p) u) y) from by
        dsimp [b₀]
        fun_prop)).closure_subset_iff.mpr
        ?_ hy
    rintro _ ⟨v, rfl⟩
    exact S.le_topologicalClosure (Submodule.subset_span (Or.inl ⟨(u, v), rfl⟩))
  have hsecond (x : H₁ × H₀) (hx : x ∈ P.adjoint.graph)
      (y : K₁ × K₀) (hy : y ∈ Q.adjoint.graph) : b₁ x y ∈ C := by
    rw [hPa] at hx
    refine (S.isClosed_topologicalClosure.preimage
      (show Continuous (fun x ↦ b₁ x y) from by dsimp [b₁]; fun_prop)).closure_subset_iff.mpr
        ?_ hx
    rintro _ ⟨u, rfl⟩
    rw [hQa] at hy
    refine (S.isClosed_topologicalClosure.preimage
      (show Continuous (fun y ↦ b₁ ((i₁.prod pa) u) y) from by
        dsimp [b₁]
        fun_prop)).closure_subset_iff.mpr
        ?_ hy
    rintro _ ⟨v, rfl⟩
    exact S.le_topologicalClosure (Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩))
  apply le_antisymm
  · apply (gradedTensorGraph P Q).topologicalClosure_minimal
      _ S.isClosed_topologicalClosure
    apply Submodule.span_le.mpr
    rintro _ (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩)
    · exact hfirst _ (P.mem_graph u) _ (Q.mem_graph v)
    · exact hsecond _ (P.adjoint.mem_graph u) _ (Q.adjoint.mem_graph v)
  · -- Conversely, each specified core graph pair belongs to its original factor graph.
    apply S.topologicalClosure_minimal _ (gradedTensorGraph P Q).isClosed_topologicalClosure
    apply Submodule.span_le.mpr
    rintro _ (⟨⟨u, v⟩, rfl⟩ | ⟨⟨u, v⟩, rfl⟩)
    · have hu : (i₀ u, p u) ∈ P.graph := by
        rw [hP]
        exact (i₀.prod p).range.le_topologicalClosure ⟨u, rfl⟩
      have hv : (j₀ v, q v) ∈ Q.graph := by
        rw [hQ]
        exact (j₀.prod q).range.le_topologicalClosure ⟨v, rfl⟩
      obtain ⟨x, hx, hpx⟩ := P.mem_graph_iff.mp hu
      obtain ⟨y, hy, hqy⟩ := Q.mem_graph_iff.mp hv
      change (x : H₀) = i₀ u at hx
      change P x = p u at hpx
      change (y : K₀) = j₀ v at hy
      change Q y = q v at hqy
      change b₀ (i₀ u, p u) (j₀ v, q v) ∈ _
      rw [← hx, ← hpx, ← hy, ← hqy]
      exact (gradedTensorGraph P Q).le_topologicalClosure
        (Submodule.subset_span (Or.inl ⟨(x, y), rfl⟩))
    · have hu : (i₁ u, pa u) ∈ P.adjoint.graph := by
        rw [hPa]
        exact (i₁.prod pa).range.le_topologicalClosure ⟨u, rfl⟩
      have hv : (j₁ v, qa v) ∈ Q.adjoint.graph := by
        rw [hQa]
        exact (j₁.prod qa).range.le_topologicalClosure ⟨v, rfl⟩
      obtain ⟨x, hx, hpx⟩ := P.adjoint.mem_graph_iff.mp hu
      obtain ⟨y, hy, hqy⟩ := Q.adjoint.mem_graph_iff.mp hv
      change (x : H₁) = i₁ u at hx
      change P.adjoint x = pa u at hpx
      change (y : K₁) = j₁ v at hy
      change Q.adjoint y = qa v at hqy
      change b₁ (i₁ u, pa u) (j₁ v, qa v) ∈ _
      rw [← hx, ← hpx, ← hy, ← hqy]
      exact (gradedTensorGraph P Q).le_topologicalClosure
        (Submodule.subset_span (Or.inr ⟨(x, y), rfl⟩))

end AtiyahSinger
