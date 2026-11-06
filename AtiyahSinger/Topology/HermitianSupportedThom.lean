/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.ContinuousHermitianMetric
public import AtiyahSinger.Topology.SupportedBundleThom

/-!
# The supported Thom operator with explicit Hermitian metric data

Public module ID: M1906.

The input is the original complex bundle and a continuous Hermitian metric as
explicit form data. Inside the adapter only, the form supplies the norm needed
by the existing exterior-symbol API. The base, fibers, additive and complex
module structures, original total-space topology and its compact-support K group
are retained. No global metric or norm instance is installed, and no canonical
metric is selected from the existence theorem.

The map is exactly the supported tensor operator from `SupportedBundleThom`.
Its independence from the metric follows by the convex family on the same
original bundle. A fixed input triple uses one common cutoff and the same
compact zero-section control throughout this family. This applies to a given
metric on any locally compact Hausdorff base; paracompactness is needed only
when separately invoking metric existence.

Sources: Karoubi I.8.7 for the convex metric homotopy, IV.1.10--1.11 for the
supported Thom operator, and Spin Geometry C.13. Independence of this specified
operator is the corresponding project argument using those constructions and
the existing uniform compact-control homotopy invariance. The original installed-metric
comparison is proved by equality of the actual tensor triples. Metric independence is proved
by the common-control convex symbol homotopy; supported Thom bijectivity is proved
in `SupportedThomIsomorphism`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle.ContinuousHermitianMetric

open Bundle

open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

section ExplicitMetric

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  {E : X → Type*} [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

/-- The original supported tensor operator, evaluated using this explicit Hermitian form. -/
def supportedThomHom (h : ContinuousHermitianMetric E) :
    CompactSupportKZero X →+ CompactSupportKZero (TotalSpace Unit E) :=
  letI : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  AtiyahSinger.ComplexBundle.supportedThomHom E h.continuous_pairing

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Isolate the common-control homotopy after retaining both original endpoint formulas.
/-- The specified supported Thom homomorphism is independent of the continuous Hermitian metric. -/
theorem supportedThomHom_eq (h₀ h₁ : ContinuousHermitianMetric E) :
    h₀.supportedThomHom = h₁.supportedThomHom := by
  /- Keep the original support triple and one cutoff fixed. Linearity of contraction in
  the Hermitian form makes the forward tensor symbol affine in the metric. Its convex
  family is invertible off the same compact zero control; finite-rank inverse continuity
  then supplies a genuine bundle-isomorphism homotopy, with the original endpoints. -/
  have metric_affine (h₀ h₁ : ContinuousHermitianMetric E) (t : I) (x : X) (v : E x) :
      let C (h : ContinuousHermitianMetric E) : Module.End ℂ (ExteriorAlgebra ℂ (E x)) :=
        letI := (h.toCore x).toNormedAddCommGroup
        letI := InnerProductSpace.ofCore (h.toCore x).toCore
        cliffordSymbol v
      C (h₀.convexCombination h₁ t) =
        (((1 - (t : ℝ) : ℝ) : ℂ)) • C h₀ + ((t : ℝ) : ℂ) • C h₁ := by
    let N (h : ContinuousHermitianMetric E) := (h.toCore x).toNormedAddCommGroup
    let P (h : ContinuousHermitianMetric E) := InnerProductSpace.ofCore (h.toCore x).toCore
    let R (h : ContinuousHermitianMetric E) : E x →ₗ[ℂ] ℂ :=
      letI := N h
      letI := P h
      innerₛₗ ℂ v
    have hR : R (h₀.convexCombination h₁ t) =
        (((1 - (t : ℝ) : ℝ) : ℂ)) • R h₀ + ((t : ℝ) : ℂ) • R h₁ := by
      apply LinearMap.ext
      intro w
      rfl
    let W := Algebra.lmul ℂ (ExteriorAlgebra ℂ (E x)) (ExteriorAlgebra.ι ℂ v)
    change W - CliffordAlgebra.contractLeft (R (h₀.convexCombination h₁ t)) =
      (((1 - (t : ℝ) : ℝ) : ℂ)) •
          (W - CliffordAlgebra.contractLeft (R h₀)) +
        ((t : ℝ) : ℂ) • (W - CliffordAlgebra.contractLeft (R h₁))
    rw [hR, map_add, map_smul, map_smul]
    have ht : (((1 - (t : ℝ) : ℝ) : ℂ)) + ((t : ℝ) : ℂ) = 1 := by
      push_cast
      ring
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, ht, one_smul]
  have metric_tensor_affine {F G : Type _} [AddCommGroup F] [Module ℂ F]
      [AddCommGroup G] [Module ℂ G] (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F)
      (h₀ h₁ : ContinuousHermitianMetric E) (t : I) (x : X) (v : E x) :
      let T (h : ContinuousHermitianMetric E) :=
        letI := (h.toCore x).toNormedAddCommGroup
        letI := InnerProductSpace.ofCore (h.toCore x).toCore
        thomTensorSymbol d d' v
      T (h₀.convexCombination h₁ t) =
        (((1 - (t : ℝ) : ℝ) : ℂ)) • T h₀ + ((t : ℝ) : ℂ) • T h₁ := by
    let C (h : ContinuousHermitianMetric E) (i : ZMod 2) :=
      letI := (h.toCore x).toNormedAddCommGroup
      letI := InnerProductSpace.ofCore (h.toCore x).toCore
      cliffordSymbolParity v i
    have hC (i : ZMod 2) : C (h₀.convexCombination h₁ t) i =
        (((1 - (t : ℝ) : ℝ) : ℂ)) • C h₀ i + ((t : ℝ) : ℂ) • C h₁ i := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact LinearMap.congr_fun (metric_affine h₀ h₁ t x v) w.val
    have ht : (((1 - (t : ℝ) : ℝ) : ℂ)) + ((t : ℝ) : ℂ) = 1 := by
      push_cast
      ring
    let P (i : ZMod 2) : Type _ := CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
    let T (c₀ : P 0 →ₗ[ℂ] P 1) (c₁ : P 1 →ₗ[ℂ] P 0) :=
      ((TensorProduct.map d (LinearMap.id : P 0 →ₗ[ℂ] P 0)).coprod
        (-(TensorProduct.map (LinearMap.id : G →ₗ[ℂ] G) c₁))).prod
          ((TensorProduct.map (LinearMap.id : F →ₗ[ℂ] F) c₀).coprod
            (-(TensorProduct.map d' (LinearMap.id : P 1 →ₗ[ℂ] P 1))))
    have hT (c₀ e₀ : P 0 →ₗ[ℂ] P 1) (c₁ e₁ : P 1 →ₗ[ℂ] P 0)
        (r s : ℂ) (hrs : r + s = 1) :
        T (r • c₀ + s • e₀) (r • c₁ + s • e₁) =
          r • T c₀ c₁ + s • T e₀ e₁ := by
      set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
      as_aux_lemma =>
        apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
          intro a b <;> apply Prod.ext <;>
          simp only [T, LinearMap.coe_comp, LinearMap.coe_inl,
            LinearMap.coe_inr, Function.comp_apply, LinearMap.prod_apply, Function.prod_apply,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.add_apply,
            LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.tmul_add,
            LinearMap.neg_apply, map_zero, add_zero, zero_add, LinearMap.coe_add,
            LinearMap.coe_smul, Pi.add_apply, Pi.smul_apply, Prod.smul_mk,
            TensorProduct.tmul_smul, Prod.mk_add_mk, neg_add_rev, smul_neg]
        · rw [← add_smul, hrs, one_smul]
        · exact add_comm _ _
        · rw [← neg_add, ← add_smul, hrs, one_smul]
    change T (C (h₀.convexCombination h₁ t) 0) (C (h₀.convexCombination h₁ t) 1) =
      (((1 - (t : ℝ) : ℝ) : ℂ)) • T (C h₀ 0) (C h₀ 1) +
        ((t : ℝ) : ℂ) • T (C h₁ 0) (C h₁ 1)
    rw [hC 0, hC 1]
    exact hT (C h₀ 0) (C h₁ 0) (C h₀ 1) (C h₁ 1) _ _ ht
  classical
  -- Fix one original input representative and one common cutoff for both metrics.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective x
  obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  let Source : X → Type _ := fun x ↦
    (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let Target : X → Type _ := fun x ↦
    (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let : IsFiniteRank (p *ᵖ Source) := isFiniteRank_pullback (E := Source) p
  let : IsFiniteRank (p *ᵖ Target) := isFiniteRank_pullback (E := Target) p
  let A (h : ContinuousHermitianMetric E) :
      CompactSupportTriple (p *ᵖ Source) (p *ᵖ Target) :=
    letI : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
    letI : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
      InnerProductSpace.ofCore (h.toCore x).toCore
    supportedThomTriple E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  have hτ (h : ContinuousHermitianMetric E) :
      h.supportedThomHom a.compactSupportClass = (A h).compactSupportClass := by
    let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
    let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
      InnerProductSpace.ofCore (h.toCore x).toCore
    exact supportedThomHom_class E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  rw [hτ, hτ]
  apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
  let K : Set Z := {z | z.proj ∈ L ∧ z.snd = 0}
  have hK : IsCompact K := (A h₀).isCompact_control
  have hleft : (A h₀).control ⊆ K := Set.Subset.refl _
  have hright : (A h₁).control ⊆ K := Set.Subset.refl _
  let e₀ := ((A h₀).enlarge K hK hleft).boundary
  let e₁ := ((A h₁).enlarge K hK hright).boundary
  -- Express both endpoint boundaries by their original tensor symbols.
  have he₀ (z : (Kᶜ : Set Z)) (w : Source z.val.proj) :
      e₀.linearEquiv z w =
      letI := (h₀.toCore z.val.proj).toNormedAddCommGroup
      letI := InnerProductSpace.ofCore (h₀.toCore z.val.proj).toCore
      thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := by
    rw [CompactSupportTriple.enlarge_apply]
    rfl
  have he₁ (z : (Kᶜ : Set Z)) (w : Source z.val.proj) :
      e₁.linearEquiv z w =
      letI := (h₁.toCore z.val.proj).toNormedAddCommGroup
      letI := InnerProductSpace.ofCore (h₁.toCore z.val.proj).toCore
      thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := by
    rw [CompactSupportTriple.enlarge_apply]
    rfl
  have he₀def : e₀ = ((A h₀).enlarge K hK hleft).boundary := rfl
  have he₁def : e₁ = ((A h₁).enlarge K hK hright).boundary := rfl
  clear_value A e₀ e₁
  as_aux_lemma =>
    -- The Hermitian contraction, hence the full forward symbol, is affine in the metric.
    have mixed (t : I) (z : (Kᶜ : Set Z)) (w : Source z.val.proj) :
        let h := h₀.convexCombination h₁ t
        letI := (h.toCore z.val.proj).toNormedAddCommGroup
        letI := InnerProductSpace.ofCore (h.toCore z.val.proj).toCore
        thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w =
          (((1 - (t : ℝ) : ℝ) : ℂ)) • e₀.linearEquiv z w +
            ((t : ℝ) : ℂ) • e₁.linearEquiv z w := by
      have hm := LinearMap.congr_fun (metric_tensor_affine
        (a.datum.cutoffLinearMap ρ z.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.val.proj) h₀ h₁ t z.val.proj z.val.snd) w
      rw [he₀, he₁]
      simpa only [LinearMap.add_apply, LinearMap.smul_apply] using hm
    -- Pull both endpoint maps to the same time-cylinder and take their continuous blend.
    let q : C(I × (Kᶜ : Set Z), (Kᶜ : Set Z)) := ContinuousMap.snd
    let S := (q : I × (Kᶜ : Set Z) → (Kᶜ : Set Z)) *ᵖ (Restrict (p *ᵖ Source) Kᶜ)
    let T := (q : I × (Kᶜ : Set Z) → (Kᶜ : Set Z)) *ᵖ (Restrict (p *ᵖ Target) Kᶜ)
    let : IsFiniteRank (Restrict (p *ᵖ Source) Kᶜ) := isFiniteRank_restrict _
    let : IsFiniteRank (Restrict (p *ᵖ Target) Kᶜ) := isFiniteRank_restrict _
    let : IsFiniteRank S := isFiniteRank_pullback q
    let : IsFiniteRank T := isFiniteRank_pullback q
    let f₀ : Hom S T := e₀.toHom.pullback q
    let f₁ : Hom S T := e₁.toHom.pullback q
    let r : C(I × (Kᶜ : Set Z), ℂ) :=
      ⟨fun z ↦ ((1 - (z.1 : ℝ) : ℝ) : ℂ),
        Complex.continuous_ofReal.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))⟩
    let s : C(I × (Kᶜ : Set Z), ℂ) :=
      ⟨fun z ↦ ((z.1 : ℝ) : ℂ),
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)⟩
    let f : Hom S T :=
      { linearMap z := r z • f₀.linearMap z + s z • f₁.linearMap z
        continuous_total := by
          let p' : C(TotalSpace Unit S, I × (Kᶜ : Set Z)) :=
            ⟨π Unit S, continuous_proj⟩
          let := isFiniteRank_pullback (E := T) p'
          have hf₀ : Continuous (fun z : TotalSpace Unit S ↦
              (⟨z, f₀.linearMap z.proj z.snd⟩ : TotalSpace Unit (p' *ᵖ T))) := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit T p').continuous_iff]
            exact continuous_id.prodMk f₀.continuous_total
          have hf₁ : Continuous (fun z : TotalSpace Unit S ↦
              (⟨z, f₁.linearMap z.proj z.snd⟩ : TotalSpace Unit (p' *ᵖ T))) := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit T p').continuous_iff]
            exact continuous_id.prodMk f₁.continuous_total
          exact (Pullback.continuous_lift Unit T p').comp
            (continuous_add_section (p' *ᵖ T) _ _
              (continuous_smul_section _ (r.comp p') _ hf₀)
              (continuous_smul_section _ (s.comp p') _ hf₁)) }
    -- Each blend is the original convex-metric symbol, with its positive denominator.
    have hbij (z : I × (Kᶜ : Set Z)) : Function.Bijective (f.linearMap z) := by
      let h := h₀.convexCombination h₁ z.1
      let := (h.toCore z.2.val.proj).toNormedAddCommGroup
      let := InnerProductSpace.ofCore (h.toCore z.2.val.proj).toCore
      have hinv := a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.2.val.proj
      have hn : (ρ z.2.val.proj : ℝ) ^ 2 + ‖z.2.val.snd‖ ^ 2 ≠ 0 := by
        by_cases hv : z.2.val.snd = 0
        · have hx : z.2.val.proj ∉ L := fun hx ↦ z.2.property ⟨hx, hv⟩
          rw [hone z.2.val.proj hx, hv]
          norm_num
        · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _)
            (sq_pos_of_pos (norm_pos_iff.mpr hv)))
      let e := thomTensorSymbolEquiv (a.datum.cutoffLinearMap ρ z.2.val.proj)
        (a.datum.inverse.cutoffLinearMap ρ z.2.val.proj)
        (ρ z.2.val.proj : ℝ) z.2.val.snd hinv.1 hinv.2 hn
      have heq : f.linearMap z = e.toLinearMap := by
        apply LinearMap.ext
        intro w
        exact (mixed z.1 z.2 w).symm
      rw [heq]
      exact e.bijective
    -- Finite-rank inverse continuity gives the same-control isomorphism homotopy.
    refine ⟨K, hK, hleft, hright, ⟨{ iso := f.toIso hbij, map_zero := ?_, map_one := ?_ }⟩⟩
    · intro z v
      change r (0, z) • e₀.linearEquiv z v + s (0, z) • e₁.linearEquiv z v = _
      simp only [r, s, ContinuousMap.coe_mk, Set.Icc.coe_zero,
        sub_zero, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, add_zero]
      exact congrArg (fun e ↦ e.linearEquiv z v) he₀def
    · intro z v
      change r (1, z) • e₀.linearEquiv z v + s (1, z) • e₁.linearEquiv z v = _
      simp only [r, s, ContinuousMap.coe_mk, Set.Icc.coe_one,
        sub_self, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, zero_add]
      exact congrArg (fun e ↦ e.linearEquiv z v) he₁def


end ExplicitMetric

section InstalledMetric

open scoped unitInterval TensorProduct

attribute [local instance] isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 500000 in
-- Keep both installed inner-product structures while comparing the original tensor triples.
/-- Exposing the original installed metric as data preserves the existing supported Thom map. -/
theorem supportedThomHom_ofInnerProduct
    (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2)) :
    (ofInnerProduct E hinner).supportedThomHom =
      AtiyahSinger.ComplexBundle.supportedThomHom E hinner := by
  /- Stage 1: the explicit Core obtained from the original inner-product instance
  has the same inner pairing on every original fiber. Its derived norm need not
  be definitionally the original norm, but both squared norms equal that same
  positive diagonal form. The additive and complex module structures agree.
  Stage 2: for one original support triple and one admissible cutoff, the two
  constructions have the same exterior parity bundles, control and forward
  tensor symbol. Equality of the forward fiber maps identifies the relative
  isomorphisms; inverse maps are then forced to agree. The original total-space
  topology has never changed, so these are equal triples in the same class map.
  Stage 3: their representative formulas give equal values on every original
  support representative. Surjectivity gives the displayed homomorphism equality.
  This comparison is not asserted merely by definitional equality of fiber norms. -/
  apply (existsUnique_supportedThomHom E hinner).choose_spec.2
  intro a ρ U hU hcontrol hzero L hL hone
  let modules : ∀ x, Module ℂ (E x) := fun _ ↦ inferInstance
  let oldTriple := supportedThomTriple E hinner a ρ U hU hcontrol hzero L hL hone
  let h := ContinuousHermitianMetric.ofInnerProduct E hinner
  let : ∀ x, NormedAddCommGroup (E x) := fun x ↦ (h.toCore x).toNormedAddCommGroup
  let : ∀ x, Module ℂ (E x) := modules
  let : ∀ x, InnerProductSpace ℂ (E x) := fun x ↦
    InnerProductSpace.ofCore (h.toCore x).toCore
  change AtiyahSinger.ComplexBundle.supportedThomHom E h.continuous_pairing
    a.compactSupportClass = _
  rw [supportedThomHom_class E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone]
  let newTriple := supportedThomTriple E h.continuous_pairing a ρ U hU hcontrol hzero L hL hone
  have htriple : newTriple = oldTriple := by
    change CompactSupportTriple.mk _ _ _ = CompactSupportTriple.mk _ _ _
    congr 1
    apply Iso.ext
    intro z
    apply LinearEquiv.ext
    intro w
    rfl
  let p : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
  let S := fun x : X ↦
    (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let T := fun x : X ↦
    (a.target.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
      (a.source.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
  let : IsFiniteRank (p *ᵖ S) := isFiniteRank_pullback (E := S) p
  let : IsFiniteRank (p *ᵖ T) := isFiniteRank_pullback (E := T) p
  change newTriple.compactSupportClass = oldTriple.compactSupportClass
  rw [htriple]

end InstalledMetric

end AtiyahSinger.ComplexBundle.ContinuousHermitianMetric
