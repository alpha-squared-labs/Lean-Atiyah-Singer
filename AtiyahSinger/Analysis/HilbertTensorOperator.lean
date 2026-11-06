/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.ClosedOperatorKernels
public import AtiyahSinger.Analysis.GradedTensorEnergy
public import AtiyahSinger.Analysis.HilbertTensorApproximation
public import AtiyahSinger.Analysis.HilbertTensorKernels
public import AtiyahSinger.Analysis.HilbertTensorRange
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-!
# The closed graded tensor operator on actual Hilbert tensor products

Public module ID: M0736.

For closed densely defined operators `P : H₀ → H₁` and `Q : K₀ → K₁`,
the even-to-odd operator has matrix `[[P ⊗ 1, -1 ⊗ Q†], [1 ⊗ Q, P† ⊗ 1]]`.
Its core graph is the complex span of the two explicit pure-tensor graph
families below, using the original domains of P, Q and their actual unbounded
Hilbert adjoints. Its realization is the closure of that very partial map.

Every Hilbert tensor is the completion of mathlib's inner-product tensor
space. The parity sums use `WithLp 2`, keeping their Hilbert norms. The kernel
inclusion and cokernel map use completed tensors of the original kernel
subspaces; neither finiteness nor completeness of a bare algebraic tensor
product is assumed. The cokernel is the quotient by the actual operator range.

Source: SG III.13.5, (13.12)--(13.14), pp.249--250, and the reuse in III.13.6,
pp.252--253. The general closed-operator statement isolates the functional
analysis behind this argument; it is a project supplement, not another
numbered lemma attributed to SG. Mathlib's partial-map conventions and graph
closure come from its LinearPMap API, referenced there to Weidmann.

UL01: the realization and full kernel inclusion are proved here. Closed
factor ranges also give the actual cokernel decomposition.
`HilbertTensorDomain` handles the joint-domain identification and energy.
Geometric product Sobolev models, group actions and associated-bundle
transport are compared in their respective modules.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open scoped TensorProduct

/-- The standard Hilbert tensor product, with the original inner-product tensor norm. -/
abbrev HilbertTensorProduct (H K : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] : Type _ :=
  UniformSpace.Completion (H ⊗[ℂ] K)

/-- Complete the actual tensor of two bounded linear maps. -/
def hilbertTensorMap {H H' K K' : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [NormedAddCommGroup K'] [InnerProductSpace ℂ K']
    (f : H →L[ℂ] H') (g : K →L[ℂ] K') :
    HilbertTensorProduct H K →L[ℂ] HilbertTensorProduct H' K' :=
  (TensorProduct.mapL f g).completion

/-- The adjoint domain of a closed Hilbert-space operator is dense.
This concerns the domain even when the original operator is not densely defined;
the adjunction identity itself still requires its usual density assumption. -/
theorem dense_adjoint_domain_of_isClosed {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (T : E →ₗ.[ℂ] F) (hT : T.IsClosed) : Dense (T.adjoint.domain : Set F) := by
  /- In the Hilbert direct sum, the original graph equals its double orthogonal.
  If y annihilates the adjoint domain, (0,y) belongs to that double orthogonal;
  functionality of the original closed graph forces y=0. -/
  let G := T.graph.comap (WithLp.linearEquiv 2 ℂ (E × F)).toLinearMap
  have hG : IsClosed (G : Set (WithLp 2 (E × F))) :=
    hT.preimage (WithLp.prod_continuous_ofLp 2 E F)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply eq_bot_iff.mpr
  intro y hy
  change y = 0
  have hy' : ∀ z ∈ T.adjoint.domain, inner ℂ z y = 0 := hy
  -- Each graph-orthogonal vector supplies a representing vector for an adjoint-domain test.
  have hz : WithLp.toLp 2 ((0 : E), y) ∈ G.orthogonal.orthogonal := by
    intro w hw
    have hw' : (WithLp.ofLp w).2 ∈ T.adjoint.domain := by
      apply LinearPMap.mem_adjoint_domain_of_exists
      refine ⟨-(WithLp.ofLp w).1, ?_⟩
      intro x
      have hxG : WithLp.toLp 2 ((x : E), T x) ∈ G := by
        exact LinearPMap.mem_graph T x
      have h := hw _ hxG
      simp only [WithLp.prod_inner_apply] at h
      have hc := congrArg (starRingEnd ℂ) h
      simp only [map_add, inner_conj_symm, map_zero] at hc
      rw [inner_neg_left]
      exact neg_eq_iff_add_eq_zero.mpr hc
    simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_zero_right, zero_add]
      using hy' _ hw'
  -- Closedness returns the double-orthogonal vector to the same original graph.
  have hzG : WithLp.toLp 2 ((0 : E), y) ∈ G := by
    rw [Submodule.orthogonal_orthogonal_eq_closure, hG.submodule_topologicalClosure_eq] at hz
    exact hz
  exact T.graph_fst_eq_zero_snd hzG rfl

/-- Pure tensors of dense factor subsets span densely in the specified Hilbert tensor product. -/
theorem dense_span_hilbertTensorProduct {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (s : Set E) (t : Set F) (hs : Dense s) (ht : Dense t) :
    Dense (Submodule.span ℂ (Set.range fun z : s × t ↦
      ((z.1.val ⊗ₜ[ℂ] z.2.val : E ⊗[ℂ] F) : HilbertTensorProduct E F)) :
        Set (HilbertTensorProduct E F)) := by
  /- Continuity of tensoring extends membership in the closed span from each
  dense factor subset to every pure tensor. Algebraic tensor induction and
  density in the Hilbert completion then fill the whole space. -/
  let L := Submodule.span ℂ (Set.range fun z : s × t ↦
    ((z.1.val ⊗ₜ[ℂ] z.2.val : E ⊗[ℂ] F) : HilbertTensorProduct E F))
  let C := L.topologicalClosure
  have hpure (x : E) (y : F) :
      ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : HilbertTensorProduct E F) ∈ C := by
    refine hs.induction (P := fun x ↦
      ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : HilbertTensorProduct E F) ∈ C) ?_ ?_ x
    · intro x hx
      refine ht.induction (P := fun y ↦
        ((x ⊗ₜ[ℂ] y : E ⊗[ℂ] F) : HilbertTensorProduct E F) ∈ C) ?_ ?_ y
      · intro y hy
        exact L.le_topologicalClosure (Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
      · exact L.isClosed_topologicalClosure.preimage (by fun_prop)
    · exact L.isClosed_topologicalClosure.preimage (by fun_prop)
  -- The pure tensors span the algebraic tensor product, whose image is dense in its completion.
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro z _
  refine UniformSpace.Completion.induction_on (p := fun z ↦ z ∈ C) z
    L.isClosed_topologicalClosure ?_
  intro u
  induction u using TensorProduct.inductionOn with
  | tmul x y => exact hpure x y
  | add u v hu hv =>
    simpa only [UniformSpace.Completion.coe_add] using C.add_mem hu hv

variable {H₀ H₁ K₀ K₁ : Type*}
  [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀] [hH₀ : CompleteSpace H₀]
  [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [hH₁ : CompleteSpace H₁]
  [NormedAddCommGroup K₀] [InnerProductSpace ℂ K₀] [hK₀ : CompleteSpace K₀]
  [NormedAddCommGroup K₁] [InnerProductSpace ℂ K₁] [hK₁ : CompleteSpace K₁]
  (P : H₀ →ₗ.[ℂ] H₁) (Q : K₀ →ₗ.[ℂ] K₁)

local notation "Even" =>
  WithLp 2 (HilbertTensorProduct H₀ K₀ × HilbertTensorProduct H₁ K₁)
local notation "Odd" =>
  WithLp 2 (HilbertTensorProduct H₁ K₀ × HilbertTensorProduct H₀ K₁)
local notation "ι₀₀" =>
  (UniformSpace.Completion.toComplL (S := ℂ) (α := H₀ ⊗[ℂ] K₀))
local notation "ι₁₀" =>
  (UniformSpace.Completion.toComplL (S := ℂ) (α := H₁ ⊗[ℂ] K₀))
local notation "ι₀₁" =>
  (UniformSpace.Completion.toComplL (S := ℂ) (α := H₀ ⊗[ℂ] K₁))
local notation "ι₁₁" =>
  (UniformSpace.Completion.toComplL (S := ℂ) (α := H₁ ⊗[ℂ] K₁))

/-- The actual graded matrix graph on finite sums of original domain pure tensors. -/
def gradedTensorGraph : Submodule ℂ (Even × Odd) :=
  Submodule.span ℂ
    ((Set.range fun z : P.domain × Q.domain ↦
      (WithLp.toLp 2 (ι₀₀ ((z.1 : H₀) ⊗ₜ[ℂ] (z.2 : K₀)), 0),
        WithLp.toLp 2 (ι₁₀ (P z.1 ⊗ₜ[ℂ] (z.2 : K₀)),
          ι₀₁ ((z.1 : H₀) ⊗ₜ[ℂ] Q z.2)))) ∪
    (Set.range fun z : P.adjoint.domain × Q.adjoint.domain ↦
      (WithLp.toLp 2 (0, ι₁₁ ((z.1 : H₁) ⊗ₜ[ℂ] (z.2 : K₁))),
        WithLp.toLp 2 (-ι₁₀ ((z.1 : H₁) ⊗ₜ[ℂ] Q.adjoint z.2),
          ι₀₁ (P.adjoint z.1 ⊗ₜ[ℂ] (z.2 : K₁))))))

/-- The partial operator with this specified algebraic pure-tensor core graph. -/
def gradedTensorCoreOperator : Even →ₗ.[ℂ] Odd :=
  (gradedTensorGraph P Q).toLinearPMap

/-- The closed graded tensor realization obtained by closing the specified core operator. -/
def gradedTensorOperator : Even →ₗ.[ℂ] Odd :=
  (gradedTensorCoreOperator P Q).closure


set_option linter.unusedSectionVars false in
/-- The specified graph is functional, so its partial-map construction keeps the actual matrix. -/
theorem gradedTensorCoreOperator_graph :
    (gradedTensorCoreOperator P Q).graph = gradedTensorGraph P Q := by
  /- Extend the factor maps algebraically and retract each Hilbert completion
  onto its algebraic tensor subspace. Their signed matrix provides a linear
  identity satisfied by every prescribed graph generator, hence by its span.
  These auxiliary maps are used only to prove that zero input forces zero
  output. No continuity is claimed for them, and the original core graph
  remains the graph selected by toLinearPMap. -/
  classical

  obtain ⟨p, hp⟩ := P.toFun.exists_extend
  obtain ⟨q, hq⟩ := Q.toFun.exists_extend
  obtain ⟨p', hp'⟩ := P.adjoint.toFun.exists_extend
  obtain ⟨q', hq'⟩ := Q.adjoint.toFun.exists_extend
  -- Each algebraic tensor injects into its Hilbert completion, so choose linear retractions.
  let r₀₀ := (ι₀₀).toLinearMap.leftInverse
  let r₁₁ := (ι₁₁).toLinearMap.leftInverse
  have hr₀₀ (u : H₀ ⊗[ℂ] K₀) : r₀₀ (u : HilbertTensorProduct H₀ K₀) = u :=
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (UniformSpace.Completion.coe_injective _)) u
  have hr₁₁ (u : H₁ ⊗[ℂ] K₁) : r₁₁ (u : HilbertTensorProduct H₁ K₁) = u :=
    LinearMap.leftInverse_apply_of_inj
      (LinearMap.ker_eq_bot.mpr (UniformSpace.Completion.coe_injective _)) u
  -- Form the same signed block matrix using the factor extensions.
  let a : (H₀ ⊗[ℂ] K₀) →ₗ[ℂ] HilbertTensorProduct H₁ K₀ :=
    (ι₁₀).toLinearMap.comp (TensorProduct.map p LinearMap.id)
  let b : (H₀ ⊗[ℂ] K₀) →ₗ[ℂ] HilbertTensorProduct H₀ K₁ :=
    (ι₀₁).toLinearMap.comp (TensorProduct.map LinearMap.id q)
  let c : (H₁ ⊗[ℂ] K₁) →ₗ[ℂ] HilbertTensorProduct H₁ K₀ :=
    (ι₁₀).toLinearMap.comp (TensorProduct.map LinearMap.id q')
  let d : (H₁ ⊗[ℂ] K₁) →ₗ[ℂ] HilbertTensorProduct H₀ K₁ :=
    (ι₀₁).toLinearMap.comp (TensorProduct.map p' LinearMap.id)
  let T : Even →ₗ[ℂ] Odd :=
    { toFun := fun u ↦ WithLp.toLp 2
        (a (r₀₀ (WithLp.ofLp u).1) - c (r₁₁ (WithLp.ofLp u).2),
          b (r₀₀ (WithLp.ofLp u).1) + d (r₁₁ (WithLp.ofLp u).2))
      map_add' := by
        intro u v
        apply WithLp.ofLp_injective
        change (a (r₀₀ ((WithLp.ofLp u).1 + (WithLp.ofLp v).1)) -
            c (r₁₁ ((WithLp.ofLp u).2 + (WithLp.ofLp v).2)),
          b (r₀₀ ((WithLp.ofLp u).1 + (WithLp.ofLp v).1)) +
            d (r₁₁ ((WithLp.ofLp u).2 + (WithLp.ofLp v).2))) = _
        simp only [map_add, WithLp.ofLp_add]
        ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> abel
      map_smul' := by
        intro z u
        apply WithLp.ofLp_injective
        change (a (r₀₀ (z • (WithLp.ofLp u).1)) - c (r₁₁ (z • (WithLp.ofLp u).2)),
          b (r₀₀ (z • (WithLp.ofLp u).1)) + d (r₁₁ (z • (WithLp.ofLp u).2))) = _
        simp [map_smul, smul_sub, smul_add] }
  -- Every original core generator has its specified value under this auxiliary linear map.
  have hgraph : ∀ z ∈ gradedTensorGraph P Q, z.2 = T z.1 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨uv, rfl⟩ | ⟨uv, rfl⟩
      · have hpv : p (uv.1 : H₀) = P uv.1 := LinearMap.congr_fun hp uv.1
        have hqv : q (uv.2 : K₀) = Q uv.2 := LinearMap.congr_fun hq uv.2
        simp [T, hr₀₀, a, b, hpv, hqv]
      · have hpv : p' (uv.1 : H₁) = P.adjoint uv.1 := LinearMap.congr_fun hp' uv.1
        have hqv : q' (uv.2 : K₁) = Q.adjoint uv.2 := LinearMap.congr_fun hq' uv.2
        simp [T, hr₁₁, c, d, hpv, hqv]
    | zero => simp
    | add x y hx hy hxT hyT => simp only [Prod.fst_add, Prod.snd_add, map_add, hxT, hyT]
    | smul z x hx hxT =>
      change z • x.2 = T (z • x.1)
      rw [map_smul, hxT]
  -- Linearity extends that identity to the span; a zero input therefore has zero output.
  apply Submodule.toLinearPMap_graph_eq
  intro z hz hzero
  rw [hgraph z hz, hzero, map_zero]


include hH₀ hH₁ hK₀ hK₁ in
/-- Closing the actual graded core gives a densely defined closed operator with that graph. -/
theorem gradedTensorOperator_realization
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed) :
    (gradedTensorCoreOperator P Q).IsClosable ∧
      (gradedTensorOperator P Q).graph = (gradedTensorGraph P Q).topologicalClosure ∧
      (gradedTensorOperator P Q).IsClosed ∧
      Dense ((gradedTensorOperator P Q).domain : Set Even) := by
  /- Test the graph closure against the two reverse signed matrix columns.
  The factor adjunction identities hold on every original core generator,
  hence on the span and its closure. Dense adjoint-domain tensor tests imply
  that this closure is functional. The original core domain is itself dense
  by the two even tensor spans, so its closed extension remains dense. -/
  classical
  have hPadj := dense_adjoint_domain_of_isClosed P hPclosed
  have hQadj := dense_adjoint_domain_of_isClosed Q hQclosed
  have hPformal := (P.adjoint_isFormalAdjoint hPdense).symm
  have hQformal := (Q.adjoint_isFormalAdjoint hQdense).symm
  let G := gradedTensorGraph P Q
  let C := G.topologicalClosure
  -- A continuous adjunction identity on the original generators persists on the graph closure.
  have hpair (u : Odd) (v : Even)
      (h : ∀ z ∈ ((Set.range fun z : P.domain × Q.domain ↦
        (WithLp.toLp 2 (ι₀₀ ((z.1 : H₀) ⊗ₜ[ℂ] (z.2 : K₀)), 0),
          WithLp.toLp 2 (ι₁₀ (P z.1 ⊗ₜ[ℂ] (z.2 : K₀)),
            ι₀₁ ((z.1 : H₀) ⊗ₜ[ℂ] Q z.2)))) ∪
        (Set.range fun z : P.adjoint.domain × Q.adjoint.domain ↦
          (WithLp.toLp 2 (0, ι₁₁ ((z.1 : H₁) ⊗ₜ[ℂ] (z.2 : K₁))),
            WithLp.toLp 2 (-ι₁₀ ((z.1 : H₁) ⊗ₜ[ℂ] Q.adjoint z.2),
              ι₀₁ (P.adjoint z.1 ⊗ₜ[ℂ] (z.2 : K₁)))))),
        inner ℂ z.2 u = inner ℂ z.1 v) :
      ∀ z ∈ C, inner ℂ z.2 u = inner ℂ z.1 v := by
    have hclosed : IsClosed {z : Even × Odd | inner ℂ z.2 u = inner ℂ z.1 v} := by
      apply isClosed_eq <;> fun_prop
    apply hclosed.closure_subset_iff.mpr
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz => exact h z hz
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      change inner ℂ x.2 u = inner ℂ x.1 v at h₁
      change inner ℂ y.2 u = inner ℂ y.1 v at h₂
      change inner ℂ (x.2 + y.2) u = inner ℂ (x.1 + y.1) v
      simp only [inner_add_left, h₁, h₂]
    | smul a x hx h₁ =>
      change inner ℂ x.2 u = inner ℂ x.1 v at h₁
      change inner ℂ (a • x.2) u = inner ℂ (a • x.1) v
      simp only [inner_smul_left, h₁]
  -- These two reverse matrix columns retain the original adjoints and the required minus sign.
  have h10 (u : P.adjoint.domain) (v : Q.domain) :
      ∀ z ∈ C,
        inner ℂ z.2 (WithLp.toLp 2 (ι₁₀ ((u : H₁) ⊗ₜ[ℂ] (v : K₀)), 0)) =
          inner ℂ z.1 (WithLp.toLp 2
            (ι₀₀ (P.adjoint u ⊗ₜ[ℂ] (v : K₀)), -ι₁₁ ((u : H₁) ⊗ₜ[ℂ] Q v))) := by
    apply hpair
    intro z hz
    rcases hz with ⟨⟨a, b⟩, rfl⟩ | ⟨⟨a, b⟩, rfl⟩
    · simpa using congrArg (fun t : ℂ ↦ t * inner ℂ (b : K₀) (v : K₀)) (hPformal a u)
    · simpa using congrArg (fun t : ℂ ↦ -(inner ℂ (a : H₁) (u : H₁) * t))
        ((Q.adjoint_isFormalAdjoint hQdense) b v)
  have h01 (u : P.domain) (v : Q.adjoint.domain) :
      ∀ z ∈ C,
        inner ℂ z.2 (WithLp.toLp 2 (0, ι₀₁ ((u : H₀) ⊗ₜ[ℂ] (v : K₁)))) =
          inner ℂ z.1 (WithLp.toLp 2
            (ι₀₀ ((u : H₀) ⊗ₜ[ℂ] Q.adjoint v), ι₁₁ (P u ⊗ₜ[ℂ] (v : K₁)))) := by
    apply hpair
    intro z hz
    rcases hz with ⟨⟨a, b⟩, rfl⟩ | ⟨⟨a, b⟩, rfl⟩
    · simpa using congrArg (fun t : ℂ ↦ inner ℂ (a : H₀) (u : H₀) * t) (hQformal b v)
    · simpa using congrArg (fun t : ℂ ↦ t * inner ℂ (b : K₁) (v : K₁))
        ((P.adjoint_isFormalAdjoint hPdense) a u)
  -- Dense reverse test tensors force every closure vector with zero input to have zero output.
  have hD10 := dense_span_hilbertTensorProduct (P.adjoint.domain : Set H₁)
    (Q.domain : Set K₀) hPadj hQdense
  have hD01 := dense_span_hilbertTensorProduct (P.domain : Set H₀)
    (Q.adjoint.domain : Set K₁) hPdense hQadj
  have hfunctional (z : Even × Odd) (hz : z ∈ C) (hz0 : z.1 = 0) : z.2 = 0 := by
    have hy10 : (WithLp.ofLp z.2).1 = 0 := by
      apply hD10.eq_zero_of_inner_left ℂ
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨u, v⟩, rfl⟩ := hw
        have h := h10 u v z hz
        rw [hz0, inner_zero_left] at h
        simpa using h
      | zero => simp
      | add x y hx hy h₁ h₂ => simp only [inner_add_right, h₁, h₂, add_zero]
      | smul a x hx h₁ => simp only [inner_smul_right, h₁, mul_zero]
    have hy01 : (WithLp.ofLp z.2).2 = 0 := by
      apply hD01.eq_zero_of_inner_left ℂ
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨⟨u, v⟩, rfl⟩ := hw
        have h := h01 u v z hz
        rw [hz0, inner_zero_left] at h
        simpa using h
      | zero => simp
      | add x y hx hy h₁ h₂ => simp only [inner_add_right, h₁, h₂, add_zero]
      | smul a x hx h₁ => simp only [inner_smul_right, h₁, mul_zero]
    apply WithLp.ofLp_injective
    exact Prod.ext hy10 hy01
  have hclos : (gradedTensorCoreOperator P Q).IsClosable := by
    refine ⟨C.toLinearPMap, ?_⟩
    rw [gradedTensorCoreOperator_graph, C.toLinearPMap_graph_eq hfunctional]
  -- Both even summands of the core contain their dense original domain tensor spans.
  have hD00 := dense_span_hilbertTensorProduct (P.domain : Set H₀)
    (Q.domain : Set K₀) hPdense hQdense
  have hD11 := dense_span_hilbertTensorProduct (P.adjoint.domain : Set H₁)
    (Q.adjoint.domain : Set K₁) hPadj hQadj
  let D := (gradedTensorCoreOperator P Q).domain.topologicalClosure
  have hd00 (w : HilbertTensorProduct H₀ K₀) : WithLp.toLp 2 (w, 0) ∈ D := by
    refine hD00.induction ?_ ?_ w
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨u, v⟩, rfl⟩ := hx
        have hg : (WithLp.toLp 2 (ι₀₀ ((u : H₀) ⊗ₜ[ℂ] (v : K₀)), 0),
            WithLp.toLp 2 (ι₁₀ (P u ⊗ₜ[ℂ] (v : K₀)),
              ι₀₁ ((u : H₀) ⊗ₜ[ℂ] Q v))) ∈ (gradedTensorCoreOperator P Q).graph := by
          rw [gradedTensorCoreOperator_graph]
          exact Submodule.subset_span (Or.inl ⟨(u, v), rfl⟩)
        apply (gradedTensorCoreOperator P Q).domain.le_topologicalClosure
        exact LinearPMap.mem_domain_iff.mpr ⟨_, hg⟩
      | zero => exact D.zero_mem
      | add x y hx hy h₁ h₂ =>
        simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero] using D.add_mem h₁ h₂
      | smul a x hx h₁ =>
        simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero] using D.smul_mem a h₁
    · exact (gradedTensorCoreOperator P Q).domain.isClosed_topologicalClosure.preimage
        (by fun_prop)
  have hd11 (w : HilbertTensorProduct H₁ K₁) : WithLp.toLp 2 (0, w) ∈ D := by
    refine hD11.induction ?_ ?_ w
    · intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨u, v⟩, rfl⟩ := hx
        have hg : (WithLp.toLp 2 (0, ι₁₁ ((u : H₁) ⊗ₜ[ℂ] (v : K₁))),
            WithLp.toLp 2 (-ι₁₀ ((u : H₁) ⊗ₜ[ℂ] Q.adjoint v),
              ι₀₁ (P.adjoint u ⊗ₜ[ℂ] (v : K₁)))) ∈ (gradedTensorCoreOperator P Q).graph := by
          rw [gradedTensorCoreOperator_graph]
          exact Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩)
        apply (gradedTensorCoreOperator P Q).domain.le_topologicalClosure
        exact LinearPMap.mem_domain_iff.mpr ⟨_, hg⟩
      | zero => exact D.zero_mem
      | add x y hx hy h₁ h₂ =>
        simpa only [← WithLp.toLp_add, Prod.mk_add_mk, zero_add] using D.add_mem h₁ h₂
      | smul a x hx h₁ =>
        simpa only [← WithLp.toLp_smul, Prod.smul_mk, smul_zero] using D.smul_mem a h₁
    · exact (gradedTensorCoreOperator P Q).domain.isClosed_topologicalClosure.preimage
        (by fun_prop)
  have hcoreDense : Dense ((gradedTensorCoreOperator P Q).domain : Set Even) := by
    apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
    apply top_unique
    intro z _
    simpa only [← WithLp.toLp_add, Prod.mk_add_mk, add_zero, zero_add,
      Prod.eta, WithLp.toLp_ofLp] using D.add_mem (hd00 (WithLp.ofLp z).1)
        (hd11 (WithLp.ofLp z).2)
  -- The standard partial-map closure now supplies exactly the displayed graph and domain claims.
  refine ⟨hclos, ?_, hclos.closure_isClosed, ?_⟩
  · exact (hclos.graph_closure_eq_closure_graph.symm).trans
      (congrArg Submodule.topologicalClosure (gradedTensorCoreOperator_graph P Q))
  · exact hcoreDense.mono (gradedTensorCoreOperator P Q).le_closure.1

local notation "KernelEven" =>
  WithLp 2 (HilbertTensorProduct P.ker Q.ker ×
    HilbertTensorProduct P.adjoint.ker Q.adjoint.ker)
local notation "KernelOdd" =>
  WithLp 2 (HilbertTensorProduct P.adjoint.ker Q.ker ×
    HilbertTensorProduct P.ker Q.adjoint.ker)

/-- Include the completed tensors of the original even kernel pairs into the ambient space. -/
def gradedTensorKernelInclusion : KernelEven →L[ℂ] Even :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ
      (HilbertTensorProduct H₀ K₀) (HilbertTensorProduct H₁ K₁)).symm.toContinuousLinearMap.comp
    (((hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL).prodMap
        (hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ
        (HilbertTensorProduct P.ker Q.ker)
        (HilbertTensorProduct P.adjoint.ker Q.adjoint.ker)).toContinuousLinearMap)

include hH₀ hH₁ hK₀ hK₁ in
open UniformSpace in
/-- The actual even kernel inclusion identifies precisely the entire closed tensor kernel. -/
theorem gradedTensorKernelInclusion_decomposition
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed) :
    Function.Injective (gradedTensorKernelInclusion P Q) ∧
      (gradedTensorKernelInclusion P Q).toLinearMap.range = (gradedTensorOperator P Q).ker := by
  /- Expand the energy identity on the actual finite tensor core. Each factor
  pairing is bounded by the graded output norm, so its continuous inequality
  passes to the closure of the original graph. On the closed kernel the four
  pairings vanish. The actual factor adjoint ranges and orthogonal kernel
  projections then identify the two completed kernel tensor summands. This
  proves the kernel statement without presuming full joint-domain density. -/
  let H₀₀ := HilbertTensorProduct H₀ K₀
  let H₁₀ := HilbertTensorProduct H₁ K₀
  let H₀₁ := HilbertTensorProduct H₀ K₁
  let H₁₁ := HilbertTensorProduct H₁ K₁
  let X := P.domain ⊗[ℂ] Q.domain
  let Y := P.adjoint.domain ⊗[ℂ] Q.adjoint.domain
  let u₀ : X →ₗ[ℂ] H₀₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.domain.subtype Q.domain.subtype)
  let a : X →ₗ[ℂ] H₁₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.toFun Q.domain.subtype)
  let b : X →ₗ[ℂ] H₀₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.domain.subtype Q.toFun)
  let u₁ : Y →ₗ[ℂ] H₁₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.domain.subtype Q.adjoint.domain.subtype)
  let c : Y →ₗ[ℂ] H₀₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.toFun Q.adjoint.domain.subtype)
  let d : Y →ₗ[ℂ] H₁₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.domain.subtype Q.adjoint.toFun)
  let Z : (X × Y) →ₗ[ℂ] (Even × Odd) :=
    ((WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).symm.toLinearMap.comp (u₀.prodMap u₁)).prod
      ((WithLp.linearEquiv 2 ℂ (H₁₀ × H₀₁)).symm.toLinearMap.comp
        ((a.coprod (-d)).prod (b.coprod c)))
  -- Every point of the original algebraic graph has these two finite tensor coordinates.
  have hrep : gradedTensorGraph P Q ≤ Z.range := by
    apply Submodule.span_le.mpr
    rintro z (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩)
    · refine ⟨(x ⊗ₜ[ℂ] y, 0), ?_⟩
      simp only [LinearMap.prod_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.prod_apply, Function.comp_apply, LinearMap.prodMap_apply,
        ContinuousLinearMap.coe_coe, Completion.coe_toComplL, map_zero,
        WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, LinearMap.coprod_apply,
        add_zero, Prod.mk.injEq, WithLp.toLp.injEq,
        and_true, Z, u₀, u₁, a, d, b, c]
      exact ⟨rfl, rfl, rfl⟩
    · refine ⟨(0, x ⊗ₜ[ℂ] y), ?_⟩
      simp only [LinearMap.prod_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.prod_apply, Function.comp_apply, LinearMap.prodMap_apply,
        ContinuousLinearMap.coe_coe, Completion.coe_toComplL, map_zero,
        WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, LinearMap.coprod_apply,
        LinearMap.neg_apply, zero_add, Prod.mk.injEq, WithLp.toLp.injEq,
        true_and, Z, u₀, u₁, a, d, b, c]
      exact ⟨rfl, rfl, rfl⟩
  have henergy (x : X) (y : Y) :
      ‖(Z (x, y)).2‖ ^ 2 = ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c y‖ ^ 2 + ‖d y‖ ^ 2 := by
    change ‖WithLp.toLp 2 (a x + -(d y), b x + c y)‖ ^ 2 = _
    rw [← sub_eq_add_neg]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact LinearPMap.graded_tensor_core_energy P Q hPdense hQdense x y
  -- A continuous test bounded by the original output norm vanishes on the full closed kernel.
  have htest (w : Even) (hw : w ∈ (gradedTensorOperator P Q).ker)
      (test : Even → ℂ) (hcontinuous : Continuous test) (C : ℝ)
      (hbound : ∀ x y, ‖test (Z (x, y)).1‖ ≤ ‖(Z (x, y)).2‖ * C) : test w = 0 := by
    have hwgraph : (w, (0 : Odd)) ∈ (gradedTensorGraph P Q).topologicalClosure := by
      rw [← (gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed).2.1]
      obtain ⟨v, rfl, hv⟩ := (gradedTensorOperator P Q).mem_ker_iff.mp hw
      exact (gradedTensorOperator P Q).mem_graph_iff.mpr ⟨v, rfl, hv⟩
    have hclosed : IsClosed {z : Even × Odd | ‖test z.1‖ ≤ ‖z.2‖ * C} :=
      isClosed_le (hcontinuous.comp continuous_fst).norm
        (continuous_snd.norm.mul continuous_const)
    have hz : ‖test w‖ ≤ ‖(0 : Odd)‖ * C := by
      apply closure_minimal (t := {z : Even × Odd | ‖test z.1‖ ≤ ‖z.2‖ * C}) ?_
        hclosed hwgraph
      intro z hz
      obtain ⟨⟨x, y⟩, rfl⟩ := hrep hz
      exact hbound x y
    exact norm_eq_zero.mp (le_antisymm (by simpa using hz) (norm_nonneg _))
  have hnorm (x : X) (y : Y) :
      ‖a x‖ ≤ ‖(Z (x, y)).2‖ ∧ ‖b x‖ ≤ ‖(Z (x, y)).2‖ ∧
        ‖c y‖ ≤ ‖(Z (x, y)).2‖ ∧ ‖d y‖ ≤ ‖(Z (x, y)).2‖ := by
    have he := henergy x y
    have hn := norm_nonneg (Z (x, y)).2
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [sq_nonneg ‖a x‖, sq_nonneg ‖b x‖, sq_nonneg ‖c y‖, sq_nonneg ‖d y‖]
  have hann₀₀_left (w : Even) (hw : w ∈ (gradedTensorOperator P Q).ker)
      (p : P.adjoint.domain) (k : K₀) :
      inner ℂ (WithLp.ofLp w).1 (↑(P.adjoint p ⊗ₜ[ℂ] k)) = 0 := by
    apply htest w hw (fun v ↦ inner ℂ (WithLp.ofLp v).1 (↑(P.adjoint p ⊗ₜ[ℂ] k)))
      (by fun_prop) ‖(↑((p : H₁) ⊗ₜ[ℂ] k) : H₁₀)‖
    intro x y
    have hpair : inner ℂ (u₀ x) (↑(P.adjoint p ⊗ₜ[ℂ] k)) =
        inner ℂ (a x) (↑((p : H₁) ⊗ₜ[ℂ] k)) := by
      change inner ℂ (↑(TensorProduct.map P.domain.subtype Q.domain.subtype x) : H₀₀) _ =
        inner ℂ (↑(TensorProduct.map P.toFun Q.domain.subtype x) : H₁₀) _
      rw [Completion.inner_coe, Completion.inner_coe]
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, Submodule.subtype_apply]
        exact congrArg₂ (· * ·) ((P.adjoint_isFormalAdjoint hPdense).symm u p).symm rfl
      | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    change ‖inner ℂ (u₀ x) _‖ ≤ _
    rw [hpair]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hnorm x y).1 (norm_nonneg _))
  have hann₀₀_right (w : Even) (hw : w ∈ (gradedTensorOperator P Q).ker)
      (q : Q.adjoint.domain) (h : H₀) :
      inner ℂ (WithLp.ofLp w).1 (↑(h ⊗ₜ[ℂ] Q.adjoint q)) = 0 := by
    apply htest w hw (fun v ↦ inner ℂ (WithLp.ofLp v).1 (↑(h ⊗ₜ[ℂ] Q.adjoint q)))
      (by fun_prop) ‖(↑(h ⊗ₜ[ℂ] (q : K₁)) : H₀₁)‖
    intro x y
    have hpair : inner ℂ (u₀ x) (↑(h ⊗ₜ[ℂ] Q.adjoint q)) =
        inner ℂ (b x) (↑(h ⊗ₜ[ℂ] (q : K₁))) := by
      change inner ℂ (↑(TensorProduct.map P.domain.subtype Q.domain.subtype x) : H₀₀) _ =
        inner ℂ (↑(TensorProduct.map P.domain.subtype Q.toFun x) : H₀₁) _
      rw [Completion.inner_coe, Completion.inner_coe]
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, Submodule.subtype_apply]
        exact congrArg₂ (· * ·) rfl ((Q.adjoint_isFormalAdjoint hQdense).symm v q).symm
      | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    change ‖inner ℂ (u₀ x) _‖ ≤ _
    rw [hpair]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hnorm x y).2.1 (norm_nonneg _))
  have hann₁₁_left (w : Even) (hw : w ∈ (gradedTensorOperator P Q).ker)
      (p : P.domain) (k : K₁) :
      inner ℂ (WithLp.ofLp w).2 (↑(P p ⊗ₜ[ℂ] k)) = 0 := by
    apply htest w hw (fun v ↦ inner ℂ (WithLp.ofLp v).2 (↑(P p ⊗ₜ[ℂ] k)))
      (by fun_prop) ‖(↑((p : H₀) ⊗ₜ[ℂ] k) : H₀₁)‖
    intro x y
    have hpair : inner ℂ (u₁ y) (↑(P p ⊗ₜ[ℂ] k)) =
        inner ℂ (c y) (↑((p : H₀) ⊗ₜ[ℂ] k)) := by
      change inner ℂ (↑(TensorProduct.map P.adjoint.domain.subtype
        Q.adjoint.domain.subtype y) : H₁₁) _ =
        inner ℂ (↑(TensorProduct.map P.adjoint.toFun Q.adjoint.domain.subtype y) : H₀₁) _
      rw [Completion.inner_coe, Completion.inner_coe]
      induction y using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, Submodule.subtype_apply]
        exact congrArg₂ (· * ·) (P.adjoint_isFormalAdjoint hPdense u p).symm rfl
      | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    change ‖inner ℂ (u₁ y) _‖ ≤ _
    rw [hpair]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hnorm x y).2.2.1 (norm_nonneg _))
  have hann₁₁_right (w : Even) (hw : w ∈ (gradedTensorOperator P Q).ker)
      (q : Q.domain) (h : H₁) :
      inner ℂ (WithLp.ofLp w).2 (↑(h ⊗ₜ[ℂ] Q q)) = 0 := by
    apply htest w hw (fun v ↦ inner ℂ (WithLp.ofLp v).2 (↑(h ⊗ₜ[ℂ] Q q)))
      (by fun_prop) ‖(↑(h ⊗ₜ[ℂ] (q : K₀)) : H₁₀)‖
    intro x y
    have hpair : inner ℂ (u₁ y) (↑(h ⊗ₜ[ℂ] Q q)) =
        inner ℂ (d y) (↑(h ⊗ₜ[ℂ] (q : K₀))) := by
      change inner ℂ (↑(TensorProduct.map P.adjoint.domain.subtype
        Q.adjoint.domain.subtype y) : H₁₁) _ =
        inner ℂ (↑(TensorProduct.map P.adjoint.domain.subtype Q.adjoint.toFun y) : H₁₀) _
      rw [Completion.inner_coe, Completion.inner_coe]
      induction y using TensorProduct.inductionOn with
      | tmul u v =>
        simp only [TensorProduct.map_tmul, TensorProduct.inner_tmul, Submodule.subtype_apply]
        exact congrArg₂ (· * ·) rfl (Q.adjoint_isFormalAdjoint hQdense v q).symm
      | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
    change ‖inner ℂ (u₁ y) _‖ ≤ _
    rw [hpair]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hnorm x y).2.2.2 (norm_nonneg _))
  -- Closedness of the original kernels supplies their orthogonal projections.
  have hPker := P.ker_eq_orthogonal_adjoint_range hPdense hPclosed
  have hQker := Q.ker_eq_orthogonal_adjoint_range hQdense hQclosed
  have hPadjker := P.ker_adjoint_eq_orthogonal_range hPdense
  have hQadjker := Q.ker_adjoint_eq_orthogonal_range hQdense
  have hPkc : IsClosed (P.ker : Set H₀) := hPker ▸ P.adjoint.toFun.range.isClosed_orthogonal
  have hQkc : IsClosed (Q.ker : Set K₀) := hQker ▸ Q.adjoint.toFun.range.isClosed_orthogonal
  have hPac : IsClosed (P.adjoint.ker : Set H₁) := hPadjker ▸ P.toFun.range.isClosed_orthogonal
  have hQac : IsClosed (Q.adjoint.ker : Set K₁) := hQadjker ▸ Q.toFun.range.isClosed_orthogonal
  let : CompleteSpace P.ker := hPkc.completeSpace_coe
  let : CompleteSpace Q.ker := hQkc.completeSpace_coe
  let : CompleteSpace P.adjoint.ker := hPac.completeSpace_coe
  let : CompleteSpace Q.adjoint.ker := hQac.completeSpace_coe
  have hi₀ := (TensorProduct.isometry_completion_mapL
    P.ker.subtypeₗᵢ Q.ker.subtypeₗᵢ).injective
  have hi₁ := (TensorProduct.isometry_completion_mapL
    P.adjoint.ker.subtypeₗᵢ Q.adjoint.ker.subtypeₗᵢ).injective
  constructor
  · intro v w hvw
    apply WithLp.ofLp_injective
    have h := congrArg WithLp.ofLp hvw
    change (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL (WithLp.ofLp v).1,
      hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL (WithLp.ofLp v).2) =
      (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL (WithLp.ofLp w).1,
      hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL (WithLp.ofLp w).2) at h
    exact Prod.ext (hi₀ (congrArg Prod.fst h)) (hi₁ (congrArg Prod.snd h))
  · apply le_antisymm
    · rintro w ⟨v, rfl⟩
      have hD := gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed
      have hDc : IsClosed ((gradedTensorOperator P Q).ker : Set Even) := by
        rw [(gradedTensorOperator P Q).ker_eq_orthogonal_adjoint_range hD.2.2.2 hD.2.2.1]
        exact Submodule.isClosed_orthogonal _
      have hgraphker (w : Even) (hw : (w, (0 : Odd)) ∈ gradedTensorGraph P Q) :
          w ∈ (gradedTensorOperator P Q).ker := by
        have hc := (gradedTensorGraph P Q).le_topologicalClosure hw
        rw [← hD.2.1] at hc
        obtain ⟨u, hu, hzero⟩ := (gradedTensorOperator P Q).mem_graph_iff.mp hc
        exact (gradedTensorOperator P Q).mem_ker_iff.mpr ⟨u, hu.symm, hzero⟩
      have hin₀ (z : HilbertTensorProduct P.ker Q.ker) :
          WithLp.toLp 2 (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL z, (0 : H₁₁)) ∈
            (gradedTensorOperator P Q).ker := by
        -- Algebraic kernel tensors already lie in the original graph with zero output.
        induction z using Completion.induction_on with
        | hp => exact hDc.preimage (by fun_prop)
        | ih z =>
          induction z using TensorProduct.inductionOn with
          | tmul p q =>
            obtain ⟨p', hp, hpzero⟩ := P.mem_ker_iff.mp p.property
            obtain ⟨q', hq, hqzero⟩ := Q.mem_ker_iff.mp q.property
            apply hgraphker
            have hg :
                (WithLp.toLp 2 (↑((p' : H₀) ⊗ₜ[ℂ] (q' : K₀)), (0 : H₁₁)),
                  WithLp.toLp 2 (↑(P p' ⊗ₜ[ℂ] (q' : K₀)),
                    ↑((p' : H₀) ⊗ₜ[ℂ] Q q'))) ∈ gradedTensorGraph P Q :=
              Submodule.subset_span (Or.inl ⟨(p', q'), rfl⟩)
            simpa only [hilbertTensorMap, ContinuousLinearMap.completion_apply_coe,
              TensorProduct.mapL_tmul, Submodule.subtypeL_apply, hp, hq, hpzero, hqzero,
              TensorProduct.zero_tmul, TensorProduct.tmul_zero, Completion.coe_zero,
              ← Prod.zero_eq_mk, WithLp.toLp_zero] using hg
          | add x y hx hy =>
            have h := (gradedTensorOperator P Q).ker.add_mem hx hy
            simpa only [Completion.coe_add, map_add, ← WithLp.toLp_add,
              Prod.mk_add_mk, zero_add] using h
      have hin₁ (z : HilbertTensorProduct P.adjoint.ker Q.adjoint.ker) :
          WithLp.toLp 2 ((0 : H₀₀),
            hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL z) ∈
              (gradedTensorOperator P Q).ker := by
        induction z using Completion.induction_on with
        | hp => exact hDc.preimage (by fun_prop)
        | ih z =>
          induction z using TensorProduct.inductionOn with
          | tmul p q =>
            obtain ⟨p', hp, hpzero⟩ := P.adjoint.mem_ker_iff.mp p.property
            obtain ⟨q', hq, hqzero⟩ := Q.adjoint.mem_ker_iff.mp q.property
            apply hgraphker
            have hg :
                (WithLp.toLp 2 ((0 : H₀₀), ↑((p' : H₁) ⊗ₜ[ℂ] (q' : K₁))),
                  WithLp.toLp 2 (-↑((p' : H₁) ⊗ₜ[ℂ] Q.adjoint q'),
                    ↑(P.adjoint p' ⊗ₜ[ℂ] (q' : K₁)))) ∈ gradedTensorGraph P Q :=
              Submodule.subset_span (Or.inr ⟨(p', q'), rfl⟩)
            simpa only [hilbertTensorMap, ContinuousLinearMap.completion_apply_coe,
              TensorProduct.mapL_tmul, Submodule.subtypeL_apply, hp, hq, hpzero, hqzero,
              TensorProduct.zero_tmul, TensorProduct.tmul_zero, Completion.coe_zero, neg_zero,
              ← Prod.zero_eq_mk, WithLp.toLp_zero] using hg
          | add x y hx hy =>
            have h := (gradedTensorOperator P Q).ker.add_mem hx hy
            simpa only [Completion.coe_add, map_add, ← WithLp.toLp_add,
              Prod.mk_add_mk, zero_add] using h
      -- Add the two completed kernel summands through precisely the original inclusion.
      have h := (gradedTensorOperator P Q).ker.add_mem
        (hin₀ (WithLp.ofLp v).1) (hin₁ (WithLp.ofLp v).2)
      change WithLp.toLp 2
        (hilbertTensorMap P.ker.subtypeL Q.ker.subtypeL (WithLp.ofLp v).1,
          hilbertTensorMap P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL (WithLp.ofLp v).2) ∈ _
      simpa only [← WithLp.toLp_add, Prod.mk_add_mk, zero_add, add_zero] using h
    · intro w hw
      have h₀ : (WithLp.ofLp w).1 ∈
          (TensorProduct.mapL P.ker.subtypeL Q.ker.subtypeL).completion.range := by
        apply TensorProduct.mem_range_completion_mapL_subtype_of_orthogonal
        · intro h hh k
          rw [hPker, Submodule.orthogonal_orthogonal_eq_closure] at hh
          apply closure_minimal (t := {h : H₀ | inner ℂ (WithLp.ofLp w).1
            (↑(h ⊗ₜ[ℂ] k)) = 0}) ?_ (isClosed_eq (by fun_prop) continuous_const) hh
          rintro _ ⟨p, rfl⟩
          exact hann₀₀_left w hw p k
        · intro k hk h
          rw [hQker, Submodule.orthogonal_orthogonal_eq_closure] at hk
          apply closure_minimal (t := {k : K₀ | inner ℂ (WithLp.ofLp w).1
            (↑(h ⊗ₜ[ℂ] k)) = 0}) ?_ (isClosed_eq (by fun_prop) continuous_const) hk
          rintro _ ⟨q, rfl⟩
          exact hann₀₀_right w hw q h
      have h₁ : (WithLp.ofLp w).2 ∈
          (TensorProduct.mapL P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL).completion.range := by
        apply TensorProduct.mem_range_completion_mapL_subtype_of_orthogonal
        · intro h hh k
          rw [hPadjker, Submodule.orthogonal_orthogonal_eq_closure] at hh
          apply closure_minimal (t := {h : H₁ | inner ℂ (WithLp.ofLp w).2
            (↑(h ⊗ₜ[ℂ] k)) = 0}) ?_ (isClosed_eq (by fun_prop) continuous_const) hh
          rintro _ ⟨p, rfl⟩
          exact hann₁₁_left w hw p k
        · intro k hk h
          rw [hQadjker, Submodule.orthogonal_orthogonal_eq_closure] at hk
          apply closure_minimal (t := {k : K₁ | inner ℂ (WithLp.ofLp w).2
            (↑(h ⊗ₜ[ℂ] k)) = 0}) ?_ (isClosed_eq (by fun_prop) continuous_const) hk
          rintro _ ⟨q, rfl⟩
          exact hann₁₁_right w hw q h
      obtain ⟨v₀, hv₀⟩ := h₀
      obtain ⟨v₁, hv₁⟩ := h₁
      refine ⟨WithLp.toLp 2 (v₀, v₁), ?_⟩
      apply WithLp.ofLp_injective
      exact Prod.ext hv₀ hv₁

include hH₀ hH₁ hK₀ hK₁ in
open UniformSpace in
/-- Closed factor ranges imply closed range for the original closed graded tensor operator. -/
theorem isClosed_range_gradedTensorOperator
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (hPrange : IsClosed (P.toFun.range : Set H₁))
    (hQrange : IsClosed (Q.toFun.range : Set K₁)) :
    IsClosed ((gradedTensorOperator P Q).toFun.range : Set Odd) := by
  /- Bounded inverses of the factors control the complement of the tensor kernel
  projection on finite domain tensors. The actual core energy bounds every factor
  image by the graded output. The resulting continuous inequality passes to the
  original graph closure, where the closed range criterion applies. -/
  let H₀₀ := HilbertTensorProduct H₀ K₀
  let H₁₀ := HilbertTensorProduct H₁ K₀
  let H₀₁ := HilbertTensorProduct H₀ K₁
  let H₁₁ := HilbertTensorProduct H₁ K₁
  let X := P.domain ⊗[ℂ] Q.domain
  let Y := P.adjoint.domain ⊗[ℂ] Q.adjoint.domain
  let u₀ : X →ₗ[ℂ] H₀₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.domain.subtype Q.domain.subtype)
  let a : X →ₗ[ℂ] H₁₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.toFun Q.domain.subtype)
  let b : X →ₗ[ℂ] H₀₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.domain.subtype Q.toFun)
  let u₁ : Y →ₗ[ℂ] H₁₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.domain.subtype Q.adjoint.domain.subtype)
  let c : Y →ₗ[ℂ] H₀₁ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.toFun Q.adjoint.domain.subtype)
  let d : Y →ₗ[ℂ] H₁₀ := Completion.toComplL.toLinearMap.comp
    (TensorProduct.map P.adjoint.domain.subtype Q.adjoint.toFun)
  let Z : (X × Y) →ₗ[ℂ] (Even × Odd) :=
    ((WithLp.linearEquiv 2 ℂ (H₀₀ × H₁₁)).symm.toLinearMap.comp (u₀.prodMap u₁)).prod
      ((WithLp.linearEquiv 2 ℂ (H₁₀ × H₀₁)).symm.toLinearMap.comp
        ((a.coprod (-d)).prod (b.coprod c)))
  -- Every point of the original algebraic graph has these two finite tensor coordinates.
  have hrep : gradedTensorGraph P Q ≤ Z.range := by
    apply Submodule.span_le.mpr
    rintro z (⟨⟨x, y⟩, rfl⟩ | ⟨⟨x, y⟩, rfl⟩)
    · refine ⟨(x ⊗ₜ[ℂ] y, 0), ?_⟩
      simp only [LinearMap.prod_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.prod_apply, Function.comp_apply, LinearMap.prodMap_apply,
        ContinuousLinearMap.coe_coe, Completion.coe_toComplL, map_zero,
        WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, LinearMap.coprod_apply,
        add_zero, Prod.mk.injEq, WithLp.toLp.injEq,
        and_true, Z, u₀, u₁, a, d, b, c]
      exact ⟨rfl, rfl, rfl⟩
    · refine ⟨(0, x ⊗ₜ[ℂ] y), ?_⟩
      simp only [LinearMap.prod_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
        Function.prod_apply, Function.comp_apply, LinearMap.prodMap_apply,
        ContinuousLinearMap.coe_coe, Completion.coe_toComplL, map_zero,
        WithLp.linearEquiv_symm_apply, AddEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe,
        AddEquiv.coe_toEquiv_symm, WithLp.addEquiv_symm_apply, LinearMap.coprod_apply,
        LinearMap.neg_apply, zero_add, Prod.mk.injEq, WithLp.toLp.injEq,
        true_and, Z, u₀, u₁, a, d, b, c]
      exact ⟨rfl, rfl, rfl⟩
  have henergy (x : X) (y : Y) :
      ‖(Z (x, y)).2‖ ^ 2 = ‖a x‖ ^ 2 + ‖b x‖ ^ 2 + ‖c y‖ ^ 2 + ‖d y‖ ^ 2 := by
    change ‖WithLp.toLp 2 (a x + -(d y), b x + c y)‖ ^ 2 = _
    rw [← sub_eq_add_neg]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    exact LinearPMap.graded_tensor_core_energy P Q hPdense hQdense x y
  have hnorm (x : X) (y : Y) :
      ‖a x‖ ≤ ‖(Z (x, y)).2‖ ∧ ‖b x‖ ≤ ‖(Z (x, y)).2‖ ∧
        ‖c y‖ ≤ ‖(Z (x, y)).2‖ ∧ ‖d y‖ ≤ ‖(Z (x, y)).2‖ := by
    have he := henergy x y
    have hn := norm_nonneg (Z (x, y)).2
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      nlinarith [sq_nonneg ‖a x‖, sq_nonneg ‖b x‖, sq_nonneg ‖c y‖, sq_nonneg ‖d y‖]
  have hPadj := dense_adjoint_domain_of_isClosed P hPclosed
  have hQadj := dense_adjoint_domain_of_isClosed Q hQclosed
  have hPkc : IsClosed (P.ker : Set H₀) := by
    rw [P.ker_eq_orthogonal_adjoint_range hPdense hPclosed]
    exact Submodule.isClosed_orthogonal _
  have hQkc : IsClosed (Q.ker : Set K₀) := by
    rw [Q.ker_eq_orthogonal_adjoint_range hQdense hQclosed]
    exact Submodule.isClosed_orthogonal _
  have hPac : IsClosed (P.adjoint.ker : Set H₁) := by
    rw [P.ker_adjoint_eq_orthogonal_range hPdense]
    exact Submodule.isClosed_orthogonal _
  have hQac : IsClosed (Q.adjoint.ker : Set K₁) := by
    rw [Q.ker_adjoint_eq_orthogonal_range hQdense]
    exact Submodule.isClosed_orthogonal _
  let : CompleteSpace P.ker := hPkc.completeSpace_coe
  let : CompleteSpace Q.ker := hQkc.completeSpace_coe
  let : CompleteSpace P.adjoint.ker := hPac.completeSpace_coe
  let : CompleteSpace Q.adjoint.ker := hQac.completeSpace_coe
  have hPar : IsClosed (P.adjoint.toFun.range : Set H₀) := by
    rw [P.range_adjoint_eq_orthogonal_ker hPdense hPclosed hPrange]
    exact Submodule.isClosed_orthogonal _
  have hQar : IsClosed (Q.adjoint.toFun.range : Set K₀) := by
    rw [Q.range_adjoint_eq_orthogonal_ker hQdense hQclosed hQrange]
    exact Submodule.isClosed_orthogonal _
  obtain ⟨C₀, hC₀, hb₀⟩ := TensorProduct.exists_bound_sub_kernelProjection P Q
    hPdense hQdense hPclosed hQclosed hPrange hQrange
  obtain ⟨C₁, hC₁, hb₁⟩ := TensorProduct.exists_bound_sub_kernelProjection P.adjoint Q.adjoint
    hPadj hQadj (P.adjoint_isClosed hPdense) (Q.adjoint_isClosed hQdense) hPar hQar
  let p₀ := (TensorProduct.mapL P.ker.starProjection Q.ker.starProjection).completion
  let p₁ := (TensorProduct.mapL
    P.adjoint.ker.starProjection Q.adjoint.ker.starProjection).completion
  let π : Even →L[ℂ] Even :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₀₀ H₁₁).symm.toContinuousLinearMap.comp
      ((p₀.prodMap p₁).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ H₀₀ H₁₁).toContinuousLinearMap)
  have hπ (w : Even) : π w ∈ (gradedTensorOperator P Q).ker := by
    rw [← (gradedTensorKernelInclusion_decomposition P Q
      hPdense hQdense hPclosed hQclosed).2]
    refine ⟨WithLp.toLp 2
      ((TensorProduct.mapL P.ker.orthogonalProjectionOnto
        Q.ker.orthogonalProjectionOnto).completion (WithLp.ofLp w).1,
        (TensorProduct.mapL P.adjoint.ker.orthogonalProjectionOnto
          Q.adjoint.ker.orthogonalProjectionOnto).completion (WithLp.ofLp w).2), ?_⟩
    apply WithLp.ofLp_injective
    change
      ((TensorProduct.mapL P.ker.subtypeL Q.ker.subtypeL).completion
        ((TensorProduct.mapL P.ker.orthogonalProjectionOnto
          Q.ker.orthogonalProjectionOnto).completion (WithLp.ofLp w).1),
        (TensorProduct.mapL P.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL).completion
          ((TensorProduct.mapL P.adjoint.ker.orthogonalProjectionOnto
            Q.adjoint.ker.orthogonalProjectionOnto).completion (WithLp.ofLp w).2)) =
        (p₀ (WithLp.ofLp w).1, p₁ (WithLp.ofLp w).2)
    exact Prod.ext
      (congrArg (fun f ↦ f (WithLp.ofLp w).1)
        (TensorProduct.completion_mapL_comp P.ker.subtypeL P.ker.orthogonalProjectionOnto
          Q.ker.subtypeL Q.ker.orthogonalProjectionOnto).symm)
      (congrArg (fun f ↦ f (WithLp.ofLp w).2)
        (TensorProduct.completion_mapL_comp P.adjoint.ker.subtypeL
          P.adjoint.ker.orthogonalProjectionOnto Q.adjoint.ker.subtypeL
            Q.adjoint.ker.orthogonalProjectionOnto).symm)
  have hcore (x : X) (y : Y) :
      ‖(Z (x, y)).1 - π (Z (x, y)).1‖ ≤ (2 * (C₀ + C₁)) * ‖(Z (x, y)).2‖ := by
    have h₀ : ‖u₀ x - p₀ (u₀ x)‖ ≤ (2 * C₀) * ‖(Z (x, y)).2‖ := by
      calc
        _ ≤ C₀ * (‖a x‖ + ‖b x‖) := hb₀ x
        _ ≤ C₀ * (‖(Z (x, y)).2‖ + ‖(Z (x, y)).2‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (hnorm x y).1 (hnorm x y).2.1) hC₀
        _ = _ := by ring
    have h₁ : ‖u₁ y - p₁ (u₁ y)‖ ≤ (2 * C₁) * ‖(Z (x, y)).2‖ := by
      calc
        _ ≤ C₁ * (‖c y‖ + ‖d y‖) := hb₁ y
        _ ≤ C₁ * (‖(Z (x, y)).2‖ + ‖(Z (x, y)).2‖) :=
          mul_le_mul_of_nonneg_left (add_le_add (hnorm x y).2.2.1 (hnorm x y).2.2.2) hC₁
        _ = _ := by ring
    have hlp : ‖WithLp.toLp 2 (u₀ x - p₀ (u₀ x), u₁ y - p₁ (u₁ y))‖ ≤
        ‖u₀ x - p₀ (u₀ x)‖ + ‖u₁ y - p₁ (u₁ y)‖ := by
      have he := WithLp.prod_norm_sq_eq_of_L2
        (WithLp.toLp 2 (u₀ x - p₀ (u₀ x), u₁ y - p₁ (u₁ y)))
      change ‖WithLp.toLp 2 (u₀ x - p₀ (u₀ x), u₁ y - p₁ (u₁ y))‖ ^ 2 =
        ‖u₀ x - p₀ (u₀ x)‖ ^ 2 + ‖u₁ y - p₁ (u₁ y)‖ ^ 2 at he
      nlinarith [norm_nonneg (WithLp.toLp 2 (u₀ x - p₀ (u₀ x), u₁ y - p₁ (u₁ y))),
        norm_nonneg (u₀ x - p₀ (u₀ x)), norm_nonneg (u₁ y - p₁ (u₁ y)),
        mul_nonneg (norm_nonneg (u₀ x - p₀ (u₀ x))) (norm_nonneg (u₁ y - p₁ (u₁ y)))]
    change ‖WithLp.toLp 2 (u₀ x - p₀ (u₀ x), u₁ y - p₁ (u₁ y))‖ ≤ _
    exact hlp.trans ((add_le_add h₀ h₁).trans_eq (by ring))
  have hD := gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed
  -- The estimate is closed in the original graph topology, including its output coordinate.
  have hclosed : IsClosed {z : Even × Odd |
      ‖z.1 - π z.1‖ ≤ (2 * (C₀ + C₁)) * ‖z.2‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  apply (gradedTensorOperator P Q).isClosed_range_of_bound hD.2.2.2 hD.2.2.1 (2 * (C₀ + C₁))
  intro u hu
  have hgraph := (gradedTensorOperator P Q).mem_graph u
  rw [hD.2.1] at hgraph
  have hbound : ‖(u : Even) - π u‖ ≤ (2 * (C₀ + C₁)) * ‖gradedTensorOperator P Q u‖ := by
    apply hclosed.closure_subset_iff.mpr ?_ hgraph
    intro z hz
    obtain ⟨⟨x, y⟩, rfl⟩ := hrep hz
    exact hcore x y
  have horth : inner ℂ (u : Even) (π u) = 0 := inner_eq_zero_symm.mp (hu _ (hπ u))
  have hsq := norm_sub_sq (𝕜 := ℂ) (u : Even) (π u)
  rw [horth] at hsq
  have hnorm : ‖(u : Even)‖ ≤ ‖(u : Even) - π u‖ := by
    simp only [map_zero, mul_zero, sub_zero] at hsq
    nlinarith [norm_nonneg (u : Even), norm_nonneg ((u : Even) - π u), sq_nonneg ‖π u‖]
  exact hnorm.trans hbound

include hH₀ hH₁ hK₀ hK₁ in
open Filter UniformSpace in
open scoped Topology in
/-- The orthogonal complement of the original graded range has only the two odd kernel tensors. -/
theorem mem_orthogonal_range_gradedTensorOperator
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (w : Odd) (hw : w ∈ (gradedTensorOperator P Q).toFun.range.orthogonal) :
    (WithLp.ofLp w).1 ∈
        (hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL).range ∧
      (WithLp.ofLp w).2 ∈
        (hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL).range := by
  /- Regularize the two odd coordinates using the same self-adjoint graph contractions
  in both factors. Original range annihilation makes the reverse graded output zero.
  The already proved kernel decomposition applies to that actual closed reverse graph;
  strong convergence returns the result to the original odd vector. -/
  let H₀₀ := HilbertTensorProduct H₀ K₀
  let H₁₀ := HilbertTensorProduct H₁ K₀
  let H₀₁ := HilbertTensorProduct H₀ K₁
  let H₁₁ := HilbertTensorProduct H₁ K₁
  let w₀ := (WithLp.ofLp w).1
  let w₁ := (WithLp.ofLp w).2
  have hPadj := dense_adjoint_domain_of_isClosed P hPclosed
  have hQadj := dense_adjoint_domain_of_isClosed Q hQclosed
  have hPaa := P.adjoint_adjoint_eq_of_isClosed hPdense hPclosed hPadj
  have hD := gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed
  have hDrev := gradedTensorOperator_realization P.adjoint Q hPadj hQdense
    (P.adjoint_isClosed hPdense) hQclosed
  have htest (u : Even) (v : Odd) (h : (u, v) ∈ gradedTensorGraph P Q) :
      inner ℂ w v = 0 := by
    have hg := (gradedTensorGraph P Q).le_topologicalClosure h
    rw [← hD.2.1] at hg
    obtain ⟨t, _, ht⟩ := (gradedTensorOperator P Q).mem_graph_iff.mp hg
    exact inner_eq_zero_symm.mp (hw v ⟨t, ht⟩)
  have htest₀ (u : P.domain) (v : Q.domain) :
      inner ℂ w₀ (↑(P u ⊗ₜ[ℂ] (v : K₀))) +
        inner ℂ w₁ (↑((u : H₀) ⊗ₜ[ℂ] Q v)) = 0 := by
    have h := htest
      (WithLp.toLp 2 ((↑((u : H₀) ⊗ₜ[ℂ] (v : K₀)) : H₀₀), (0 : H₁₁)))
      (WithLp.toLp 2 ((↑(P u ⊗ₜ[ℂ] (v : K₀)) : H₁₀),
        (↑((u : H₀) ⊗ₜ[ℂ] Q v) : H₀₁)))
      (Submodule.subset_span (Or.inl ⟨(u, v), rfl⟩))
    exact h
  have htest₁ (u : P.adjoint.domain) (v : Q.adjoint.domain) :
      -inner ℂ w₀ (↑((u : H₁) ⊗ₜ[ℂ] Q.adjoint v)) +
        inner ℂ w₁ (↑(P.adjoint u ⊗ₜ[ℂ] (v : K₁))) = 0 := by
    have h := htest
      (WithLp.toLp 2 ((0 : H₀₀), (↑((u : H₁) ⊗ₜ[ℂ] (v : K₁)) : H₁₁)))
      (WithLp.toLp 2 (-(↑((u : H₁) ⊗ₜ[ℂ] Q.adjoint v) : H₁₀),
        (↑(P.adjoint u ⊗ₜ[ℂ] (v : K₁)) : H₀₁)))
      (Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩))
    simpa only [WithLp.prod_inner_apply, WithLp.ofLp_toLp, inner_neg_right] using h
  obtain ⟨R, A, S, hn, hg, hm, hR, hS, hs⟩ :=
    P.exists_selfAdjoint_graph_approximation hPclosed hPdense hPadj
  obtain ⟨R', A', S', hn', hg', hm', hR', hS', hs'⟩ :=
    Q.exists_selfAdjoint_graph_approximation hQclosed hQdense hQadj
  -- Self-adjoint compression also gives regularization into the actual adjoint graph.
  have hga (n : ℕ) (y : H₁) : (S n y, (A n).adjoint y) ∈ P.adjoint.graph := by
    have hr (u : P.domain) : inner ℂ ((A n).adjoint y) (u : H₀) =
        inner ℂ (S n y) (P u) := by
      rw [ContinuousLinearMap.adjoint_inner_left, hm]
      exact ((hs n).2.isSymmetric y (P u)).symm
    have hd : S n y ∈ P.adjoint.domain :=
      P.mem_adjoint_domain_of_exists _ ⟨(A n).adjoint y, hr⟩
    exact P.adjoint.mem_graph_iff.mpr
      ⟨⟨S n y, hd⟩, rfl, P.adjoint_apply_eq hPdense _ hr⟩
  have hga' (n : ℕ) (y : K₁) : (S' n y, (A' n).adjoint y) ∈ Q.adjoint.graph := by
    have hr (u : Q.domain) : inner ℂ ((A' n).adjoint y) (u : K₀) =
        inner ℂ (S' n y) (Q u) := by
      rw [ContinuousLinearMap.adjoint_inner_left, hm']
      exact ((hs' n).2.isSymmetric y (Q u)).symm
    have hd : S' n y ∈ Q.adjoint.domain :=
      Q.mem_adjoint_domain_of_exists _ ⟨(A' n).adjoint y, hr⟩
    exact Q.adjoint.mem_graph_iff.mpr
      ⟨⟨S' n y, hd⟩, rfl, Q.adjoint_apply_eq hQdense _ hr⟩
  let v₀ (n : ℕ) := (TensorProduct.mapL (S n) (R' n)).completion w₀
  let v₁ (n : ℕ) := (TensorProduct.mapL (R n) (S' n)).completion w₁
  let a (n : ℕ) := (TensorProduct.mapL (A n).adjoint (R' n)).completion w₀
  let b (n : ℕ) := (TensorProduct.mapL (S n) (A' n)).completion w₀
  let c (n : ℕ) := (TensorProduct.mapL (A n) (S' n)).completion w₁
  let d (n : ℕ) := (TensorProduct.mapL (R n) (A' n).adjoint).completion w₁
  have hRa (n : ℕ) : (R n).adjoint = R n := (hs n).1.star_eq
  have hSa (n : ℕ) : (S n).adjoint = S n := (hs n).2.star_eq
  have hRa' (n : ℕ) : (R' n).adjoint = R' n := (hs' n).1.star_eq
  have hSa' (n : ℕ) : (S' n).adjoint = S' n := (hs' n).2.star_eq
  have hzero₀ (n : ℕ) : a n + d n = 0 := by
    apply TensorProduct.completion_ext_inner_tmul
    intro x y
    simp only [inner_add_left, inner_zero_left]
    change inner ℂ ((TensorProduct.mapL (A n).adjoint (R' n)).completion w₀) _ +
      inner ℂ ((TensorProduct.mapL (R n) (A' n).adjoint).completion w₁) _ = 0
    rw [TensorProduct.inner_completion_mapL_tmul,
      TensorProduct.inner_completion_mapL_tmul,
      ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_adjoint,
      hRa, hRa']
    obtain ⟨u, hu, hAu⟩ := P.mem_graph_iff.mp (hg n x)
    obtain ⟨v, hv, hAv⟩ := Q.mem_graph_iff.mp (hg' n y)
    dsimp only [Prod.fst, Prod.snd] at hu hv hAu hAv
    rw [← hu, ← hv, ← hAu, ← hAv]
    exact htest₀ u v
  have hzero₁ (n : ℕ) : b n - c n = 0 := by
    apply TensorProduct.completion_ext_inner_tmul
    intro x y
    simp only [inner_sub_left, inner_zero_left]
    change inner ℂ ((TensorProduct.mapL (S n) (A' n)).completion w₀) _ -
      inner ℂ ((TensorProduct.mapL (A n) (S' n)).completion w₁) _ = 0
    rw [TensorProduct.inner_completion_mapL_tmul,
      TensorProduct.inner_completion_mapL_tmul, hSa, hSa']
    obtain ⟨u, hu, hAu⟩ := P.adjoint.mem_graph_iff.mp (hga n x)
    obtain ⟨v, hv, hAv⟩ := Q.adjoint.mem_graph_iff.mp (hga' n y)
    dsimp only [Prod.fst, Prod.snd] at hu hv hAu hAv
    rw [← hu, ← hv, ← hAu, ← hAv]
    have h := htest₁ u v
    linear_combination -h
  have hreg₀ (n : ℕ) (z : H₁₀) :
      (WithLp.toLp 2 ((TensorProduct.mapL (S n) (R' n)).completion z, (0 : H₀₁)),
        WithLp.toLp 2 ((TensorProduct.mapL (A n).adjoint (R' n)).completion z,
          (TensorProduct.mapL (S n) (A' n)).completion z)) ∈
      (gradedTensorOperator P.adjoint Q).graph := by
    refine Completion.induction_on (p := fun z ↦
      (WithLp.toLp 2 ((TensorProduct.mapL (S n) (R' n)).completion z, (0 : H₀₁)),
        WithLp.toLp 2 ((TensorProduct.mapL (A n).adjoint (R' n)).completion z,
          (TensorProduct.mapL (S n) (A' n)).completion z)) ∈
        (gradedTensorOperator P.adjoint Q).graph) z
      (hDrev.2.2.1.preimage (by fun_prop)) ?_
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      obtain ⟨u, hu, hAu⟩ := P.adjoint.mem_graph_iff.mp (hga n x)
      obtain ⟨v, hv, hAv⟩ := Q.mem_graph_iff.mp (hg' n y)
      dsimp only [Prod.fst, Prod.snd] at hu hv hAu hAv
      simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
      rw [← hu, ← hv, ← hAu, ← hAv, hDrev.2.1]
      exact (gradedTensorGraph P.adjoint Q).le_topologicalClosure
        (Submodule.subset_span (Or.inl ⟨(u, v), rfl⟩))
    | add z t hz ht =>
      simpa only [Completion.coe_add, map_add, Prod.mk_add_mk, ← WithLp.toLp_add, add_zero] using
        (gradedTensorOperator P.adjoint Q).graph.add_mem hz ht
  have hreg₁ (n : ℕ) (z : H₀₁) :
      (WithLp.toLp 2 ((0 : H₁₀), (TensorProduct.mapL (R n) (S' n)).completion z),
        WithLp.toLp 2 (-(TensorProduct.mapL (R n) (A' n).adjoint).completion z,
          (TensorProduct.mapL (A n) (S' n)).completion z)) ∈
      (gradedTensorOperator P.adjoint Q).graph := by
    refine Completion.induction_on (p := fun z ↦
      (WithLp.toLp 2 ((0 : H₁₀), (TensorProduct.mapL (R n) (S' n)).completion z),
        WithLp.toLp 2 (-(TensorProduct.mapL (R n) (A' n).adjoint).completion z,
          (TensorProduct.mapL (A n) (S' n)).completion z)) ∈
        (gradedTensorOperator P.adjoint Q).graph) z
      (hDrev.2.2.1.preimage (by fun_prop)) ?_
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul x y =>
      have hx : (R n x, A n x) ∈ P.adjoint.adjoint.graph := by rw [hPaa]; exact hg n x
      obtain ⟨u, hu, hAu⟩ := P.adjoint.adjoint.mem_graph_iff.mp hx
      obtain ⟨v, hv, hAv⟩ := Q.adjoint.mem_graph_iff.mp (hga' n y)
      dsimp only [Prod.fst, Prod.snd] at hu hv hAu hAv
      simp only [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul]
      rw [← hu, ← hv, ← hAu, ← hAv, hDrev.2.1]
      exact (gradedTensorGraph P.adjoint Q).le_topologicalClosure
        (Submodule.subset_span (Or.inr ⟨(u, v), rfl⟩))
    | add z t hz ht =>
      simpa only [Completion.coe_add, map_add, Prod.mk_add_mk, ← WithLp.toLp_add,
        add_zero, neg_add] using
        (gradedTensorOperator P.adjoint Q).graph.add_mem hz ht
  have hmem (n : ℕ) :
      v₀ n ∈ (hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL).range ∧
      v₁ n ∈ (hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL).range := by
    have h := (gradedTensorOperator P.adjoint Q).graph.sub_mem (hreg₀ n w₀) (hreg₁ n w₁)
    change (WithLp.toLp 2 (v₀ n, 0) - WithLp.toLp 2 (0, v₁ n),
      WithLp.toLp 2 (a n, b n) - WithLp.toLp 2 (-d n, c n)) ∈ _ at h
    rw [← WithLp.toLp_sub, ← WithLp.toLp_sub] at h
    simp only [Prod.mk_sub_mk, sub_zero, zero_sub, sub_neg_eq_add, hzero₀, hzero₁] at h
    have hk : WithLp.toLp 2 (v₀ n, -v₁ n) ∈ (gradedTensorOperator P.adjoint Q).ker := by
      obtain ⟨u, hu, hTu⟩ := (gradedTensorOperator P.adjoint Q).mem_graph_iff.mp h
      exact (gradedTensorOperator P.adjoint Q).mem_ker_iff.mpr ⟨u, hu.symm, hTu⟩
    rw [← (gradedTensorKernelInclusion_decomposition P.adjoint Q hPadj hQdense
      (P.adjoint_isClosed hPdense) hQclosed).2] at hk
    obtain ⟨v, hv⟩ := hk
    have hv₀ := congrArg (fun z ↦ (WithLp.ofLp z).1) hv
    have hv₁ := congrArg (fun z ↦ (WithLp.ofLp z).2) hv
    change hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL (WithLp.ofLp v).1 = v₀ n at hv₀
    change hilbertTensorMap P.adjoint.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL
      (WithLp.ofLp v).2 = -v₁ n at hv₁
    refine ⟨⟨(WithLp.ofLp v).1, hv₀⟩, ?_⟩
    have hx : -v₁ n ∈
        (hilbertTensorMap P.adjoint.adjoint.ker.subtypeL Q.adjoint.ker.subtypeL).range :=
      ⟨(WithLp.ofLp v).2, hv₁⟩
    rw [hPaa] at hx
    simpa only [neg_neg] using
      (hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL).range.neg_mem hx
  -- Each inclusion is isometric on the specified completion, so its image is closed.
  have hc₀ : IsClosed
      ((hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL).range : Set H₁₀) :=
    (TensorProduct.isometry_completion_mapL P.adjoint.ker.subtypeₗᵢ
      Q.ker.subtypeₗᵢ).isClosedEmbedding.isClosed_range
  have hc₁ : IsClosed
      ((hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL).range : Set H₀₁) :=
    (TensorProduct.isometry_completion_mapL P.ker.subtypeₗᵢ
      Q.adjoint.ker.subtypeₗᵢ).isClosedEmbedding.isClosed_range
  have ht₀ := TensorProduct.tendsto_completion_mapL_of_contractions S R'
    (fun n ↦ (hn n).2) (fun n ↦ (hn' n).1) hS hR' w₀
  have ht₁ := TensorProduct.tendsto_completion_mapL_of_contractions R S'
    (fun n ↦ (hn n).1) (fun n ↦ (hn' n).2) hR hS' w₁
  exact ⟨hc₀.mem_of_tendsto ht₀ (Eventually.of_forall (fun n ↦ (hmem n).1)),
    hc₁.mem_of_tendsto ht₁ (Eventually.of_forall (fun n ↦ (hmem n).2))⟩


/-- Include the odd kernel tensors, then quotient by the actual tensor-operator range. -/
def gradedTensorCokernelMap :
    KernelOdd →ₗ[ℂ] (Odd ⧸ (gradedTensorOperator P Q).toFun.range) := by
  let inclusion : KernelOdd →L[ℂ] Odd :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ
        (HilbertTensorProduct H₁ K₀) (HilbertTensorProduct H₀ K₁)).symm.toContinuousLinearMap.comp
      (((hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL).prodMap
          (hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ
          (HilbertTensorProduct P.adjoint.ker Q.ker)
          (HilbertTensorProduct P.ker Q.adjoint.ker)).toContinuousLinearMap)
  exact (gradedTensorOperator P Q).toFun.range.mkQ.comp inclusion.toLinearMap

include hH₀ hH₁ hK₀ hK₁ in
open UniformSpace in
/-- Closed factor ranges give the natural odd quotient decomposition and closed output range. -/
theorem gradedTensorCokernelMap_decomposition
    (hPdense : Dense (P.domain : Set H₀)) (hQdense : Dense (Q.domain : Set K₀))
    (hPclosed : P.IsClosed) (hQclosed : Q.IsClosed)
    (hPrange : IsClosed (P.toFun.range : Set H₁))
    (hQrange : IsClosed (Q.toFun.range : Set K₁)) :
    IsClosed ((gradedTensorOperator P Q).toFun.range : Set Odd) ∧
      Function.Bijective (gradedTensorCokernelMap P Q) := by
  /- The core estimate gives closedness of the actual range. Its orthogonal complement
  is the image of precisely the two original odd kernel tensor inclusions. Orthogonal
  decomposition then proves bijectivity after the original quotient map. -/
  have hclosed := isClosed_range_gradedTensorOperator P Q
    hPdense hQdense hPclosed hQclosed hPrange hQrange
  let R := (gradedTensorOperator P Q).toFun.range
  let : CompleteSpace R := hclosed.completeSpace_coe
  let H₀₀ := HilbertTensorProduct H₀ K₀
  let H₁₀ := HilbertTensorProduct H₁ K₀
  let H₀₁ := HilbertTensorProduct H₀ K₁
  let H₁₁ := HilbertTensorProduct H₁ K₁
  let i₀ := hilbertTensorMap P.adjoint.ker.subtypeL Q.ker.subtypeL
  let i₁ := hilbertTensorMap P.ker.subtypeL Q.adjoint.ker.subtypeL
  let I : KernelOdd →L[ℂ] Odd :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ H₁₀ H₀₁).symm.toContinuousLinearMap.comp
      ((i₀.prodMap i₁).comp
        (WithLp.prodContinuousLinearEquiv 2 ℂ
          (HilbertTensorProduct P.adjoint.ker Q.ker)
          (HilbertTensorProduct P.ker Q.adjoint.ker)).toContinuousLinearMap)
  have hmap (v : KernelOdd) : gradedTensorCokernelMap P Q v = R.mkQ (I v) := rfl
  have hPker := P.ker_eq_orthogonal_adjoint_range hPdense hPclosed
  have hQker := Q.ker_eq_orthogonal_adjoint_range hQdense hQclosed
  have hPadjker := P.ker_adjoint_eq_orthogonal_range hPdense
  have hQadjker := Q.ker_adjoint_eq_orthogonal_range hQdense
  -- A tensor containing a factor orthogonal to an original kernel annihilates its inclusion.
  have hpair₀ (x : H₁) (y : K₀)
      (h : (∀ u : P.adjoint.ker, inner ℂ x (u : H₁) = 0) ∨
        (∀ v : Q.ker, inner ℂ y (v : K₀) = 0))
      (z : HilbertTensorProduct P.adjoint.ker Q.ker) :
      inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₁₀) (i₀ z) = 0 := by
    refine Completion.induction_on (p := fun z ↦
      inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₁₀) (i₀ z) = 0) z
      (isClosed_eq (by fun_prop) continuous_const) ?_
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      change inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₁₀)
        ((TensorProduct.mapL P.adjoint.ker.subtypeL Q.ker.subtypeL).completion
          (↑(u ⊗ₜ[ℂ] v))) = 0
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
        Completion.inner_coe, TensorProduct.inner_tmul]
      change inner ℂ x (u : H₁) * inner ℂ y (v : K₀) = 0
      rcases h with h | h
      · rw [h u, zero_mul]
      · rw [h v, mul_zero]
    | add z t hz ht => simp only [Completion.coe_add, map_add, inner_add_right, hz, ht, add_zero]
  have hpair₁ (x : H₀) (y : K₁)
      (h : (∀ u : P.ker, inner ℂ x (u : H₀) = 0) ∨
        (∀ v : Q.adjoint.ker, inner ℂ y (v : K₁) = 0))
      (z : HilbertTensorProduct P.ker Q.adjoint.ker) :
      inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₀₁) (i₁ z) = 0 := by
    refine Completion.induction_on (p := fun z ↦
      inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₀₁) (i₁ z) = 0) z
      (isClosed_eq (by fun_prop) continuous_const) ?_
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul u v =>
      change inner ℂ (↑(x ⊗ₜ[ℂ] y) : H₀₁)
        ((TensorProduct.mapL P.ker.subtypeL Q.adjoint.ker.subtypeL).completion
          (↑(u ⊗ₜ[ℂ] v))) = 0
      rw [ContinuousLinearMap.completion_apply_coe, TensorProduct.mapL_tmul,
        Completion.inner_coe, TensorProduct.inner_tmul]
      change inner ℂ x (u : H₀) * inner ℂ y (v : K₁) = 0
      rcases h with h | h
      · rw [h u, zero_mul]
      · rw [h v, mul_zero]
    | add z t hz ht => simp only [Completion.coe_add, map_add, inner_add_right, hz, ht, add_zero]
  have hIorth (v : KernelOdd) : I v ∈ R.orthogonal := by
    intro y hy
    obtain ⟨u, rfl⟩ := hy
    have hg := (gradedTensorOperator P Q).mem_graph u
    rw [(gradedTensorOperator_realization P Q hPdense hQdense hPclosed hQclosed).2.1] at hg
    have hc : IsClosed {z : Even × Odd | inner ℂ z.2 (I v) = 0} :=
      isClosed_eq (by fun_prop) continuous_const
    apply hc.closure_subset_iff.mpr ?_ hg
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      rcases hz with ⟨⟨p, q⟩, rfl⟩ | ⟨⟨p, q⟩, rfl⟩
      · change inner ℂ (↑(P p ⊗ₜ[ℂ] (q : K₀)) : H₁₀) (i₀ (WithLp.ofLp v).1) +
          inner ℂ (↑((p : H₀) ⊗ₜ[ℂ] Q q) : H₀₁) (i₁ (WithLp.ofLp v).2) = 0
        have h₀ : ∀ t : P.adjoint.ker, inner ℂ (P p) (t : H₁) = 0 := by
          intro t
          have ht : (t : H₁) ∈ P.toFun.range.orthogonal := by
            rw [← hPadjker]
            exact t.property
          exact ht (P p) ⟨p, rfl⟩
        have h₁ : ∀ t : Q.adjoint.ker, inner ℂ (Q q) (t : K₁) = 0 := by
          intro t
          have ht : (t : K₁) ∈ Q.toFun.range.orthogonal := by
            rw [← hQadjker]
            exact t.property
          exact ht (Q q) ⟨q, rfl⟩
        rw [hpair₀ _ _ (Or.inl h₀), hpair₁ _ _ (Or.inr h₁), add_zero]
      · change inner ℂ (-(↑((p : H₁) ⊗ₜ[ℂ] Q.adjoint q) : H₁₀))
            (i₀ (WithLp.ofLp v).1) +
          inner ℂ (↑(P.adjoint p ⊗ₜ[ℂ] (q : K₁)) : H₀₁) (i₁ (WithLp.ofLp v).2) = 0
        have h₀ : ∀ t : Q.ker, inner ℂ (Q.adjoint q) (t : K₀) = 0 := by
          intro t
          have ht : (t : K₀) ∈ Q.adjoint.toFun.range.orthogonal := by
            rw [← hQker]
            exact t.property
          exact ht (Q.adjoint q) ⟨q, rfl⟩
        have h₁ : ∀ t : P.ker, inner ℂ (P.adjoint p) (t : H₀) = 0 := by
          intro t
          have ht : (t : H₀) ∈ P.adjoint.toFun.range.orthogonal := by
            rw [← hPker]
            exact t.property
          exact ht (P.adjoint p) ⟨p, rfl⟩
        rw [inner_neg_left, hpair₀ _ _ (Or.inr h₀), hpair₁ _ _ (Or.inl h₁), neg_zero, add_zero]
    | zero => simp
    | add x y hx hy h₁ h₂ =>
      simpa only [Set.mem_ofPred_eq, Prod.snd_add, inner_add_left, add_zero] using
        congrArg₂ (· + ·) h₁ h₂
    | smul a x hx h₁ =>
      simpa only [Set.mem_ofPred_eq, Prod.smul_snd, inner_smul_left, mul_zero] using
        congrArg (fun z : ℂ ↦ starRingEnd ℂ a * z) h₁
  have hIrange : I.range = R.orthogonal := by
    apply le_antisymm
    · rintro y ⟨v, rfl⟩
      exact hIorth v
    · intro y hy
      obtain ⟨hy₀, hy₁⟩ := mem_orthogonal_range_gradedTensorOperator P Q
        hPdense hQdense hPclosed hQclosed y hy
      obtain ⟨v₀, hv₀⟩ := hy₀
      obtain ⟨v₁, hv₁⟩ := hy₁
      refine ⟨WithLp.toLp 2 (v₀, v₁), ?_⟩
      apply WithLp.ofLp_injective
      exact Prod.ext hv₀ hv₁
  have hi : Function.Injective I := by
    have hi₀ := (TensorProduct.isometry_completion_mapL
      P.adjoint.ker.subtypeₗᵢ Q.ker.subtypeₗᵢ).injective
    have hi₁ := (TensorProduct.isometry_completion_mapL
      P.ker.subtypeₗᵢ Q.adjoint.ker.subtypeₗᵢ).injective
    intro v w hvw
    apply WithLp.ofLp_injective
    have h := congrArg WithLp.ofLp hvw
    change (i₀ (WithLp.ofLp v).1, i₁ (WithLp.ofLp v).2) =
      (i₀ (WithLp.ofLp w).1, i₁ (WithLp.ofLp w).2) at h
    exact Prod.ext (hi₀ (congrArg Prod.fst h)) (hi₁ (congrArg Prod.snd h))
  -- Orthogonal decomposition uses the actual closed range and its original quotient map.
  refine ⟨hclosed, ?_, ?_⟩
  · apply LinearMap.ker_eq_bot.mp
    apply le_antisymm ?_ bot_le
    intro v hv
    change v = 0
    have hv' : R.mkQ (I v) = 0 := hv
    have hvr : I v ∈ R := (Submodule.Quotient.mk_eq_zero R).mp hv'
    have hz : I v = 0 := inner_self_eq_zero.mp (hIorth v _ hvr)
    apply hi
    simpa only [map_zero] using hz
  · intro x
    obtain ⟨w, rfl⟩ := R.mkQ_surjective x
    obtain ⟨r, hr, s, hs, hws⟩ := R.exists_add_mem_mem_orthogonal w
    obtain ⟨v, hv⟩ : s ∈ I.range := hIrange.symm ▸ hs
    refine ⟨v, ?_⟩
    change I v = s at hv
    rw [hmap, hv, hws, map_add]
    have hz : R.mkQ r = 0 := (Submodule.Quotient.mk_eq_zero R).mpr hr
    rw [hz, zero_add]

end AtiyahSinger
