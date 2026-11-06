/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.GradedJointKernel

/-!
# The exact core graph of the closed graded joint operator

Public module ID: M0706.

The actual two simultaneous graph closures determine the closure of the signed
core matrix graph. Its domain and kernel are the products of the original
joint domains and kernels. On the original core, the kernel condition
retains all four operator images. This combines the existing energy, graph
closure and closed-domain results without separately closing the two entries.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w

/-- The signed core matrix graph has the exact closed joint domain and kernel. -/
theorem exists_closed_gradedSmoothGraph {S₀ : Type v} {S₁ : Type w}
    [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    {X₀ X₁ Y₀ Y₁ : Type u}
    [NormedAddCommGroup X₀] [NormedSpace ℂ X₀] [CompleteSpace X₀]
    [NormedAddCommGroup X₁] [NormedSpace ℂ X₁] [CompleteSpace X₁]
    [NormedAddCommGroup Y₀] [InnerProductSpace ℂ Y₀] [CompleteSpace Y₀]
    [NormedAddCommGroup Y₁] [InnerProductSpace ℂ Y₁] [CompleteSpace Y₁]
    (i₀ : S₀ →ₗ[ℂ] X₀) (i₁ : S₁ →ₗ[ℂ] X₁)
    (h₀ : S₀ →ₗ[ℂ] Y₀) (v₀ : S₀ →ₗ[ℂ] Y₁)
    (v₁ : S₁ →ₗ[ℂ] Y₀) (h₁ : S₁ →ₗ[ℂ] Y₁)
    (R₀ : X₀ →ₗ.[ℂ] (Y₀ × Y₁)) (R₁ : X₁ →ₗ.[ℂ] (Y₀ × Y₁))
    (hgraph₀ : R₀.graph = (i₀.prod (h₀.prod v₀)).range.topologicalClosure)
    (hclosed₀ : R₀.IsClosed) (hdense₀ : Dense (R₀.domain : Set X₀))
    (hgraph₁ : R₁.graph = (i₁.prod (v₁.prod h₁)).range.topologicalClosure)
    (hclosed₁ : R₁.IsClosed) (hdense₁ : Dense (R₁.domain : Set X₁))
    (hcross : ∀ (u : R₀.domain) (v : R₁.domain),
      inner ℂ (R₀ u).1 (R₁ v).1 = inner ℂ (R₀ u).2 (R₁ v).2) :
    let Even := WithLp 2 (X₀ × X₁)
    let Odd := WithLp 2 (Y₀ × Y₁)
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀ X₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ Y₀ Y₁
    let iEven := cEven.symm.toLinearMap.comp (i₀.prodMap i₁)
    let dSmooth := cOdd.symm.toLinearMap.comp
      ((h₀.coprod (-v₁)).prod (v₀.coprod h₁))
    ∃ L : Even →ₗ.[ℂ] Odd,
      L.IsClosed ∧ Dense (L.domain : Set Even) ∧
      L.graph = (iEven.prod dSmooth).range.topologicalClosure ∧
      L.domain = (R₀.domain.prod R₁.domain).comap cEven.toLinearMap ∧
      L.ker = (R₀.ker.prod R₁.ker).comap cEven.toLinearMap ∧
      (∀ (u : R₀.domain) (v : R₁.domain),
        (WithLp.toLp 2 (u.val, v.val),
          WithLp.toLp 2 ((R₀ u).1 - (R₁ v).1, (R₀ u).2 + (R₁ v).2)) ∈ L.graph) ∧
      ∀ (s : S₀) (t : S₁), iEven (s, t) ∈ L.ker ↔
        (h₀ s = 0 ∧ v₀ s = 0) ∧ (v₁ t = 0 ∧ h₁ t = 0) := by
  intro Even Odd cEven cOdd iEven dSmooth
  have hgraded := exists_closed_gradedJointOperator R₀ R₁ hclosed₀ hclosed₁ hcross
  obtain ⟨L, hLclosed, hLdom, hL⟩ := hgraded
  have hLker := ker_eq_prod_of_gradedJointOperator R₀ R₁ hcross L hLdom hL
  have hLdense : Dense (L.domain : Set Even) := by
    rw [hLdom]
    exact (hdense₀.prod hdense₁).preimage cEven.toHomeomorph.isOpenMap
  -- Keep both inputs and all four outputs when passing from joint to graded graphs.
  let f : ((X₀ × Y₀ × Y₁) × (X₁ × Y₀ × Y₁)) →L[ℂ] Even × Odd := {
    toFun z := (WithLp.toLp 2 (z.1.1, z.2.1),
      WithLp.toLp 2 (z.1.2.1 - z.2.2.1, z.1.2.2 + z.2.2.2))
    map_add' z w := by
      apply Prod.ext <;> apply WithLp.ofLp_injective
      · rfl
      · change ((z.1.2.1 + w.1.2.1) - (z.2.2.1 + w.2.2.1),
          (z.1.2.2 + w.1.2.2) + (z.2.2.2 + w.2.2.2)) =
          ((z.1.2.1 - z.2.2.1) + (w.1.2.1 - w.2.2.1),
            (z.1.2.2 + z.2.2.2) + (w.1.2.2 + w.2.2.2))
        congr 1 <;> abel
    map_smul' a z := by
      apply Prod.ext <;> apply WithLp.ofLp_injective
      · rfl
      · change (a • z.1.2.1 - a • z.2.2.1, a • z.1.2.2 + a • z.2.2.2) =
          (a • (z.1.2.1 - z.2.2.1), a • (z.1.2.2 + z.2.2.2))
        rw [smul_sub, smul_add]
    cont := by fun_prop }
  have hLgraph : L.graph = (R₀.graph.prod R₁.graph).map f.toLinearMap := by
    ext z
    constructor
    · intro hz
      have hzdom := LinearPMap.mem_domain_of_mem_graph hz
      rw [hLdom] at hzdom
      let u : R₀.domain := ⟨z.1.ofLp.1, hzdom.1⟩
      let v : R₁.domain := ⟨z.1.ofLp.2, hzdom.2⟩
      have hin : WithLp.toLp 2 (u.val, v.val) = z.1 := WithLp.toLp_ofLp 2 z.1
      have hout := L.mem_graph_snd_inj (hL u v) hz hin
      exact ⟨((u.val, R₀ u), (v.val, R₁ v)), ⟨R₀.mem_graph u, R₁.mem_graph v⟩,
        Prod.ext hin hout⟩
    · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
      obtain ⟨u, rfl⟩ := R₀.mem_graph_iff'.mp hx
      obtain ⟨v, rfl⟩ := R₁.mem_graph_iff'.mp hy
      exact hL u v
  let J₀ := (i₀.prod (h₀.prod v₀)).range
  let J₁ := (i₁.prod (v₁.prod h₁)).range
  have henergy (x : X₀ × Y₀ × Y₁) (hx : x ∈ J₀)
      (y : X₁ × Y₀ × Y₁) (hy : y ∈ J₁) :
      inner ℂ x.2.1 y.2.1 = inner ℂ x.2.2 y.2.2 := by
    have hxR : x ∈ R₀.graph := hgraph₀ ▸ J₀.le_topologicalClosure hx
    have hyR : y ∈ R₁.graph := hgraph₁ ▸ J₁.le_topologicalClosure hy
    obtain ⟨u, rfl⟩ := R₀.mem_graph_iff'.mp hxR
    obtain ⟨v, rfl⟩ := R₁.mem_graph_iff'.mp hyR
    exact hcross u v
  have hmap := map_jointGraphClosure_of_inner_eq J₀ J₁ f (fun _ _ ↦ rfl) henergy
  have hrange : (J₀.prod J₁).map f.toLinearMap = (iEven.prod dSmooth).range := by
    ext z
    constructor
    · rintro ⟨⟨x, y⟩, ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, rfl⟩
      exact ⟨(s, t), by simp [iEven, dSmooth, cEven, cOdd, f, sub_eq_add_neg]⟩
    · rintro ⟨⟨s, t⟩, rfl⟩
      refine ⟨((i₀ s, (h₀ s, v₀ s)),
        (i₁ t, (v₁ t, h₁ t))), ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩, ?_⟩
      simp [iEven, dSmooth, cEven, cOdd, f, sub_eq_add_neg]
  have hLsmoothGraph : L.graph = (iEven.prod dSmooth).range.topologicalClosure := by
    calc
      L.graph = (R₀.graph.prod R₁.graph).map f.toLinearMap := hLgraph
      _ = ((J₀.prod J₁).map f.toLinearMap).topologicalClosure := by
        rw [hgraph₀, hgraph₁]
        exact hmap
      _ = (iEven.prod dSmooth).range.topologicalClosure := by rw [hrange]
  have hzero_iff {α β : Type u} [AddCommGroup α] [Module ℂ α]
      [AddCommGroup β] [Module ℂ β] (R : α →ₗ.[ℂ] β) (x : α) (y : β)
      (hxy : (x, y) ∈ R.graph) : x ∈ R.ker ↔ y = 0 := by
    constructor
    · intro hx
      obtain ⟨u, hu, hRu⟩ := R.mem_ker_iff.mp hx
      exact R.mem_graph_snd_inj hxy (hRu ▸ R.mem_graph u) hu
    · intro hy
      obtain ⟨u, hu, hRu⟩ := R.mem_graph_iff.mp hxy
      exact R.mem_ker_iff.mpr ⟨u, hu.symm, hRu.trans hy⟩
  have hsmoothKer (s : S₀) (t : S₁) :
      iEven (s, t) ∈ L.ker ↔
        (h₀ s = 0 ∧ v₀ s = 0) ∧ (v₁ t = 0 ∧ h₁ t = 0) := by
    have hs : (i₀ s, (h₀ s, v₀ s)) ∈ R₀.graph := by
      rw [hgraph₀]
      exact J₀.le_topologicalClosure ⟨s, rfl⟩
    have ht : (i₁ t, (v₁ t, h₁ t)) ∈ R₁.graph := by
      rw [hgraph₁]
      exact J₁.le_topologicalClosure ⟨t, rfl⟩
    rw [hLker]
    change (i₀ s ∈ R₀.ker ∧ i₁ t ∈ R₁.ker) ↔ _
    rw [hzero_iff R₀ _ _ hs, hzero_iff R₁ _ _ ht]
    simp only [Prod.mk_eq_zero]
  exact ⟨L, hLclosed, hLdense, hLsmoothGraph, hLdom, hLker, hL, hsmoothKer⟩

end AtiyahSinger
