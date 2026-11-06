/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedGraphFormalAdjunction
public import AtiyahSinger.Analysis.GradedJointSmoothGraph

/-!
# The actual transpose of the signed graded joint graph

Public module ID: M0702.

The opposite signed matrix has the wrong two vertical signs for formal
adjunction. Conjugating it by the isometries negating the second input and
second output gives the actual transpose matrix. This retains its original
joint domain and kernel, and transports the exact smooth graph closure.
The four original core pairings then extend to formal adjunction with the
original graded operator. No equality with a maximal Hilbert-adjoint domain
is inferred from formal adjunction alone.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

universe u v w v' w'

/-- The opposite joint graph gives the actual signed transpose in the same four spaces. -/
theorem exists_closed_gradedFormalAdjoint
    {S₀ : Type v} {S₁ : Type w} {T₀ : Type v'} {T₁ : Type w'}
    [AddCommGroup S₀] [Module ℂ S₀] [AddCommGroup S₁] [Module ℂ S₁]
    [AddCommGroup T₀] [Module ℂ T₀] [AddCommGroup T₁] [Module ℂ T₁]
    {X₀ X₁ Y₀ Y₁ : Type u}
    [NormedAddCommGroup X₀] [InnerProductSpace ℂ X₀]
    [NormedAddCommGroup X₁] [InnerProductSpace ℂ X₁]
    [NormedAddCommGroup Y₀] [InnerProductSpace ℂ Y₀]
    [NormedAddCommGroup Y₁] [InnerProductSpace ℂ Y₁]
    (i₀ : S₀ →ₗ[ℂ] X₀) (i₁ : S₁ →ₗ[ℂ] X₁)
    (j₀ : T₀ →ₗ[ℂ] Y₀) (j₁ : T₁ →ₗ[ℂ] Y₁)
    (h₀ : S₀ →ₗ[ℂ] Y₀) (v₀ : S₀ →ₗ[ℂ] Y₁)
    (v₁ : S₁ →ₗ[ℂ] Y₀) (h₁ : S₁ →ₗ[ℂ] Y₁)
    (h₀a : T₀ →ₗ[ℂ] X₀) (v₁a : T₀ →ₗ[ℂ] X₁)
    (v₀a : T₁ →ₗ[ℂ] X₀) (h₁a : T₁ →ₗ[ℂ] X₁)
    (hh₀ : ∀ s t, inner ℂ (h₀ s) (j₀ t) = inner ℂ (i₀ s) (h₀a t))
    (hv₀ : ∀ s t, inner ℂ (v₀ s) (j₁ t) = inner ℂ (i₀ s) (v₀a t))
    (hv₁ : ∀ s t, inner ℂ (v₁ s) (j₀ t) = inner ℂ (i₁ s) (v₁a t))
    (hh₁ : ∀ s t, inner ℂ (h₁ s) (j₁ t) = inner ℂ (i₁ s) (h₁a t)) :
    let Even := WithLp 2 (X₀ × X₁)
    let Odd := WithLp 2 (Y₀ × Y₁)
    let cEven := WithLp.prodContinuousLinearEquiv 2 ℂ X₀ X₁
    let cOdd := WithLp.prodContinuousLinearEquiv 2 ℂ Y₀ Y₁
    let sEven := cEven.trans (((ContinuousLinearEquiv.refl ℂ X₀).prodCongr
      (LinearIsometryEquiv.neg ℂ (E := X₁)).toContinuousLinearEquiv).trans cEven.symm)
    let sOdd := cOdd.trans (((ContinuousLinearEquiv.refl ℂ Y₀).prodCongr
      (LinearIsometryEquiv.neg ℂ (E := Y₁)).toContinuousLinearEquiv).trans cOdd.symm)
    let iEven := cEven.symm.toLinearMap.comp (i₀.prodMap i₁)
    let jOdd := cOdd.symm.toLinearMap.comp (j₀.prodMap j₁)
    let dSmooth := cOdd.symm.toLinearMap.comp ((h₀.coprod (-v₁)).prod (v₀.coprod h₁))
    let gSmooth := cEven.symm.toLinearMap.comp
      ((h₀a.coprod (-v₀a)).prod (v₁a.coprod h₁a))
    let aSmooth := cEven.symm.toLinearMap.comp
      ((h₀a.coprod v₀a).prod ((-v₁a).coprod h₁a))
    ∀ (D : Even →ₗ.[ℂ] Odd) (G : Odd →ₗ.[ℂ] Even)
      (R₀ : Y₀ →ₗ.[ℂ] (X₀ × X₁)) (R₁ : Y₁ →ₗ.[ℂ] (X₀ × X₁)),
      D.graph = (iEven.prod dSmooth).range.topologicalClosure →
      G.graph = (jOdd.prod gSmooth).range.topologicalClosure →
      G.IsClosed → Dense (G.domain : Set Odd) →
      G.domain = (R₀.domain.prod R₁.domain).comap cOdd.toLinearMap →
      G.ker = (R₀.ker.prod R₁.ker).comap cOdd.toLinearMap →
      ∃ A : Odd →ₗ.[ℂ] Even,
        A.IsClosed ∧ Dense (A.domain : Set Odd) ∧
        A.domain = G.domain ∧ A.ker = G.ker ∧
        A.graph = G.graph.map (sOdd.prodCongr sEven).toLinearMap ∧
        A.graph = (jOdd.prod aSmooth).range.topologicalClosure ∧
        D.IsFormalAdjoint A := by
  intro Even Odd cEven cOdd sEven sOdd iEven jOdd dSmooth gSmooth aSmooth
    D G R₀ R₁ hD hG hGclosed hGdense hGdomain hGker
  -- Negating the second coordinate preserves each original joint submodule.
  have hEvenInv : Function.Involutive sEven := by
    intro x
    apply WithLp.ofLp_injective
    change (x.ofLp.1, - -x.ofLp.2) = x.ofLp
    simp only [neg_neg]
  have hOddInv : Function.Involutive sOdd := by
    intro x
    apply WithLp.ofLp_injective
    change (x.ofLp.1, - -x.ofLp.2) = x.ofLp
    simp only [neg_neg]
  have hdomain (x : Odd) : sOdd x ∈ G.domain ↔ x ∈ G.domain := by
    rw [hGdomain]
    change (x.ofLp.1 ∈ R₀.domain ∧ -x.ofLp.2 ∈ R₁.domain) ↔
      (x.ofLp.1 ∈ R₀.domain ∧ x.ofLp.2 ∈ R₁.domain)
    simp only [Submodule.neg_mem_iff]
  have hker (x : Odd) : sOdd x ∈ G.ker ↔ x ∈ G.ker := by
    rw [hGker]
    change (x.ofLp.1 ∈ R₀.ker ∧ -x.ofLp.2 ∈ R₁.ker) ↔
      (x.ofLp.1 ∈ R₀.ker ∧ x.ofLp.2 ∈ R₁.ker)
    simp only [Submodule.neg_mem_iff]
  let sDomain : G.domain →ₗ[ℂ] G.domain :=
    { toFun := fun x ↦ ⟨sOdd x.val, (hdomain x.val).mpr x.property⟩
      map_add' := by intros; apply Subtype.ext; exact sOdd.map_add _ _
      map_smul' := by intros; apply Subtype.ext; exact sOdd.map_smul _ _ }
  let A : Odd →ₗ.[ℂ] Even :=
    { domain := G.domain
      toFun := sEven.toLinearMap.comp (G.toFun.comp sDomain) }
  let signGraph := sOdd.prodCongr sEven
  -- The exact graph is the image under the two specified coordinate isometries.
  have hAimage : A.graph = G.graph.map signGraph.toLinearMap := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp hz
      refine ⟨((sDomain u).val, G (sDomain u)), G.mem_graph (sDomain u), ?_⟩
      exact Prod.ext ((hOddInv u.val).trans hu) hAu
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨u, hu, hGu⟩ := G.mem_graph_iff.mp hz
      let v : A.domain := ⟨sOdd u.val, (hdomain u.val).mpr u.property⟩
      have hvu : sDomain v = u := Subtype.ext (hOddInv u.val)
      refine A.mem_graph_iff.mpr ⟨v, congrArg sOdd hu, ?_⟩
      change sEven (G (sDomain v)) = sEven z.2
      rw [hvu, hGu]
  have hAclosed : A.IsClosed := by
    change IsClosed (A.graph : Set (Odd × Even))
    rw [hAimage]
    exact signGraph.toHomeomorph.isClosedMap _ hGclosed
  have hAker : A.ker = G.ker := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu, hAu⟩ := A.mem_ker_iff.mp hx
      apply (hker x).mp
      refine G.mem_ker_iff.mpr ⟨sDomain u, congrArg sOdd hu, ?_⟩
      exact sEven.injective (hAu.trans sEven.map_zero.symm)
    · intro hx
      have hsx := (hker x).mpr hx
      obtain ⟨u, hu, hGu⟩ := G.mem_ker_iff.mp hsx
      let v : A.domain := ⟨sOdd u.val, (hdomain u.val).mpr u.property⟩
      have hvu : sDomain v = u := Subtype.ext (hOddInv u.val)
      refine A.mem_ker_iff.mpr ⟨v, (hOddInv x).symm.trans (congrArg sOdd hu), ?_⟩
      change sEven (G (sDomain v)) = 0
      rw [hvu, hGu, map_zero]
  -- The same signs turn the opposite smooth matrix into the literal formal transpose.
  have hArange : (jOdd.prod gSmooth).range.map signGraph.toLinearMap =
      (jOdd.prod aSmooth).range := by
    ext z
    constructor
    · rintro ⟨z, ⟨⟨s, t⟩, rfl⟩, rfl⟩
      refine ⟨(s, -t), ?_⟩
      simp [jOdd, gSmooth, aSmooth, signGraph, sEven, sOdd, cEven, cOdd, add_comm]
    · rintro ⟨⟨s, t⟩, rfl⟩
      refine ⟨(jOdd (s, -t), gSmooth (s, -t)), ⟨(s, -t), rfl⟩, ?_⟩
      simp [jOdd, gSmooth, aSmooth, signGraph, sEven, sOdd, cEven, cOdd, add_comm]
  have hAgraph : A.graph = (jOdd.prod aSmooth).range.topologicalClosure := by
    rw [hAimage, hG]
    have hclosure : ((jOdd.prod gSmooth).range.topologicalClosure).map
        signGraph.toLinearMap =
        ((jOdd.prod gSmooth).range.map signGraph.toLinearMap).topologicalClosure := by
      ext z
      exact Set.ext_iff.mp (signGraph.toHomeomorph.image_closure
        ((jOdd.prod gSmooth).range : Set _)) z
    rw [hclosure, hArange]
  have hpair (s : S₀ × S₁) (t : T₀ × T₁) :
      inner ℂ (dSmooth s) (jOdd t) = inner ℂ (iEven s) (aSmooth t) := by
    simp [dSmooth, jOdd, iEven, aSmooth, cEven, cOdd, WithLp.prod_inner_apply,
      Function.prod, inner_add_left, inner_add_right, hh₀, hv₀, hv₁, hh₁]
    abel
  exact ⟨A, hAclosed, hGdense, rfl, hAker, hAimage, hAgraph,
    AtiyahSinger.LinearPMap.isFormalAdjoint_of_graph_eq_closure
      iEven jOdd dSmooth aSmooth D A hD hAgraph hpair⟩

end AtiyahSinger
