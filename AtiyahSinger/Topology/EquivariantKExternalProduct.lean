/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.EquivariantExternalProduct
public import AtiyahSinger.Topology.EquivariantRepresentationAction
public import AtiyahSinger.Topology.EquivariantSupportFunctoriality
public import AtiyahSinger.Topology.SupportTensorAction

/-!
# External product on the original equivariant support groups

Public module ID: M1791.

The actual reciprocal-cutoff tensor triples determine a unique biadditive
operation on the existing group presentations. Its characterization allows
every invariant cutoff, so it includes independence of those choices. The
operation uses the diagonal action on the product base and retains the full
representation-ring coefficients. Forgetting agrees with the previously
specified ordinary compact-support product after the existing comparison map.

Sources: SG Appendix C.1 and III.13, pp.251--252; Karoubi II.5.21--5.22;
ASI I section 2 for equivariant K theory. The invariant-cutoff presentation
descent is an explicit supplement. Compactness of the acting group supplies
invariant cutoffs. Locally compact Hausdorff bases suffice; no Haar structure,
global metric or paracompactness is assumed. This is not associated-family
descent or a twisted index formula. The original product formulas are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback sectionModule trivialTopology isFiniteRank_trivial

variable {G X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X] [T2Space X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y] [T2Space Y]
  [hG : CompactSpace G] [hX : LocallyCompactSpace X] [hY : LocallyCompactSpace Y]

include hG hX hY in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 16000000 in
-- The proof retains the original tensor topologies through the two presentation descents.
/-- The actual invariant-cutoff tensor triples descend uniquely through both original groups. -/
theorem existsUnique_equivariantSupportKZeroExternalProduct :
    ∃! μ : EquivariantSupportTripleKZero G X →+
        EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y),
      ∀ (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
        (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (ha : a.1.datum.control ⊆ U)
        (hρzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
        (hρone : ∀ x ∉ L, ρ x = 1)
        (τ : C(Y, I)) (V : Set Y) (hV : IsOpen V) (hb : b.1.datum.control ⊆ V)
        (hτzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
        (hτone : ∀ y ∉ M, τ y = 1)
        (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
        (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
        (hτinv : ∀ (g : G) (y : Y), τ (g • y) = τ y)
        (hMinv : ∀ (g : G) (y : Y), g • y ∈ M ↔ y ∈ M),
        μ a.kZeroClass b.kZeroClass =
          (supportedEquivariantExternalProductTriple a b
            ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
            hρinv hLinv hτinv hMinv).kZeroClass := by
  /- Stage 1: use exists_invariant_time_cutoff on each original compact control.
  This supplies actual admissible data and the product triple. Given two choices,
  interpolate each cutoff by its real convex combination. Use the intersection
  of its two zero neighborhoods and the union of its two compact controls.
  The cutoffs remain invariant and equal one outside those unions. The positive
  sum of squares gives both continuous inverse blocks throughout the interval,
  outside the one fixed product of those unions. The existing equivariant
  boundary-homotopy theorem identifies the output classes.
  Stage 2: for a given equivariant isomorphism at infinity, enlarge the input
  control to its common invariant compact set and choose a common cutoff zero
  near it. Both forward and inverse boundary squares tensor to an actual global
  square of the even and odd bundles. Direct sums distribute via the canonical
  equivariant tensor and sum maps. This preserves addition separately in each
  input. For any equivariant identity bundle, take the constant cutoff one and
  empty zero neighborhood/control in that factor. The displayed block is then
  invertible everywhere, hence its triple is isomorphic to an identity triple.
  Arbitrary equivariant stabilizing bundles are allowed, not only representations.
  Stage 3: apply the original equivariant support-group universal property in
  each input. The resulting biadditive operation has the equation for every
  admissible cutoff by Stage 1. Generator spanning gives uniqueness. No
  equivariant compactification comparison, global metric or Bott theorem is used. -/
  classical
  -- Package precisely the admissible data quantified in the original characterization.
  let CX (a : EquivariantSupportBundleTriple G X) :=
    { c : C(X, I) × Set X × Set X //
      IsOpen c.2.1 ∧ a.1.datum.control ⊆ c.2.1 ∧
      (∀ x ∈ c.2.1, c.1 x = 0) ∧ IsCompact c.2.2 ∧
      (∀ x ∉ c.2.2, c.1 x = 1) ∧
      (∀ (g : G) (x : X), c.1 (g • x) = c.1 x) ∧
      ∀ (g : G) (x : X), g • x ∈ c.2.2 ↔ x ∈ c.2.2 }
  let CY (b : EquivariantSupportBundleTriple G Y) :=
    { c : C(Y, I) × Set Y × Set Y //
      IsOpen c.2.1 ∧ b.1.datum.control ⊆ c.2.1 ∧
      (∀ y ∈ c.2.1, c.1 y = 0) ∧ IsCompact c.2.2 ∧
      (∀ y ∉ c.2.2, c.1 y = 1) ∧
      (∀ (g : G) (y : Y), c.1 (g • y) = c.1 y) ∧
      ∀ (g : G) (y : Y), g • y ∈ c.2.2 ↔ y ∈ c.2.2 }
  let product (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c : CX a) (d : CY b) :=
    supportedEquivariantExternalProductTriple a b
      c.val.1 c.val.2.1 c.property.1 c.property.2.1 c.property.2.2.1
      c.val.2.2 c.property.2.2.2.1 c.property.2.2.2.2.1
      d.val.1 d.val.2.1 d.property.1 d.property.2.1 d.property.2.2.1
      d.val.2.2 d.property.2.2.2.1 d.property.2.2.2.2.1
      c.property.2.2.2.2.2.1 c.property.2.2.2.2.2.2
      d.property.2.2.2.2.2.1 d.property.2.2.2.2.2.2
  have nonemptyX (a : EquivariantSupportBundleTriple G X) : Nonempty (CX a) := by
    obtain ⟨U, hU, ha, _, L, hL, _, hLinv, ρ, hρinv, hzero, hone⟩ :=
      exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
    exact ⟨⟨(ρ, U, L), hU, ha, hzero, hL, hone, hρinv, hLinv⟩⟩
  have nonemptyY (b : EquivariantSupportBundleTriple G Y) : Nonempty (CY b) := by
    obtain ⟨V, hV, hb, _, M, hM, _, hMinv, τ, hτinv, hzero, hone⟩ :=
      exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
    exact ⟨⟨(τ, V, M), hV, hb, hzero, hM, hone, hτinv, hMinv⟩⟩
  -- Continuous linear combinations are formed in the original finite bundle topologies.
  have combination {Z : Type _} [TopologicalSpace Z] (S T : FiniteBundle Z)
      (f g : Hom S.Fiber T.Fiber) (r s : C(Z, ℂ)) :
      ∃ q : Hom S.Fiber T.Fiber, ∀ z,
        q.linearMap z = r z • f.linearMap z + s z • g.linearMap z := by
    let p : C(TotalSpace Unit S.Fiber, Z) :=
      ⟨fun z ↦ z.proj, continuous_proj (E := S.Fiber)⟩
    let := isFiniteRank_pullback (E := T.Fiber) p
    have hf : Continuous (fun z : TotalSpace Unit S.Fiber ↦
        (⟨z, f.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ T.Fiber))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
      exact continuous_id.prodMk f.continuous_total
    have hg : Continuous (fun z : TotalSpace Unit S.Fiber ↦
        (⟨z, g.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ T.Fiber))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
      exact continuous_id.prodMk g.continuous_total
    refine ⟨{ linearMap z := r z • f.linearMap z + s z • g.linearMap z
              continuous_total := ?_ }, fun _ ↦ rfl⟩
    exact (Pullback.continuous_lift Unit T.Fiber p).comp
      (continuous_add_section (p *ᵖ T.Fiber) _ _
        (continuous_smul_section _ (r.comp p) _ hf)
        (continuous_smul_section _ (s.comp p) _ hg))
  -- Each cutoff block extends globally as a continuous map, although its inverse need not.
  have globalBlock (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c : CX a) (d : CY b) :
      ∃ q : Hom (a.1.externalProductSource b.1).Fiber
          (a.1.externalProductTarget b.1).Fiber,
        ∀ z, q.linearMap z = reciprocalTensorSymbol
          (a.1.datum.cutoffLinearMap c.val.1 z.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.2) := by
    let D := (a.1.datum.cutoffHom c.val.1 c.val.2.1
      c.property.1 c.property.2.1 c.property.2.2.1).pullback
        (ContinuousMap.fst : C(X × Y, X))
    let D' := (a.1.datum.inverse.cutoffHom c.val.1 c.val.2.1
      c.property.1 c.property.2.1 c.property.2.2.1).pullback
        (ContinuousMap.fst : C(X × Y, X))
    let E := (b.1.datum.cutoffHom d.val.1 d.val.2.1
      d.property.1 d.property.2.1 d.property.2.2.1).pullback
        (ContinuousMap.snd : C(X × Y, Y))
    let E' := (b.1.datum.inverse.cutoffHom d.val.1 d.val.2.1
      d.property.1 d.property.2.1 d.property.2.2.1).pullback
        (ContinuousMap.snd : C(X × Y, Y))
    obtain ⟨upper, hupper⟩ := combination (a.1.externalProductSource b.1)
      ((a.1.target.pullback ContinuousMap.fst).tensor
        (b.1.source.pullback ContinuousMap.snd))
      ((D.tensor (Hom.id _)).comp sumFst) (((Hom.id _).tensor E').comp sumSnd)
      (ContinuousMap.const _ 1) (ContinuousMap.const _ (-1))
    obtain ⟨lower, hlower⟩ := combination (a.1.externalProductSource b.1)
      ((a.1.source.pullback ContinuousMap.fst).tensor
        (b.1.target.pullback ContinuousMap.snd))
      (((Hom.id _).tensor E).comp sumFst) ((D'.tensor (Hom.id _)).comp sumSnd)
      (ContinuousMap.const _ 1) (ContinuousMap.const _ 1)
    refine ⟨{ linearMap z := reciprocalTensorSymbol
                (a.1.datum.cutoffLinearMap c.val.1 z.1)
                (a.1.datum.inverse.cutoffLinearMap c.val.1 z.1)
                (b.1.datum.cutoffLinearMap d.val.1 z.2)
                (b.1.datum.inverse.cutoffLinearMap d.val.1 z.2)
              continuous_total := ?_ }, fun _ ↦ rfl⟩
    apply continuous_induced_rng.mpr
    apply (upper.continuous_total.prodMk lower.continuous_total).congr
    intro z
    apply Prod.ext <;> apply congrArg (TotalSpace.mk z.proj)
    · rw [hupper]
      simp only [ContinuousMap.const_apply, one_smul, neg_one_smul]
      rfl
    · rw [hlower]
      simp only [ContinuousMap.const_apply, one_smul]
      rfl
  have algebraMix {A₀ A₁ B₀ B₁ : Type}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      (d₀ d₁ : A₀ →ₗ[ℂ] A₁) (d₀' d₁' : A₁ →ₗ[ℂ] A₀)
      (e₀ e₁ : B₀ →ₗ[ℂ] B₁) (e₀' e₁' : B₁ →ₗ[ℂ] B₀) (r s : ℂ) :
      reciprocalTensorSymbol (r • d₀ + s • d₁) (r • d₀' + s • d₁')
          (r • e₀ + s • e₁) (r • e₀' + s • e₁') =
        r • reciprocalTensorSymbol d₀ d₀' e₀ e₀' +
          s • reciprocalTensorSymbol d₁ d₁' e₁ e₁' := by
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro u v <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, TensorProduct.add_tmul, TensorProduct.tmul_add,
        TensorProduct.smul_tmul', TensorProduct.tmul_smul]
    all_goals abel
  -- Every enlargement still evaluates to the specified four-block tensor symbol.
  have boundaryValue (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c : CX a) (d : CY b)
      (K : Set (X × Y)) (hK : IsCompact K)
      (h : (product a b c d).1.datum.control ⊆ K)
      (z : (Kᶜ : Set (X × Y))) (v : (a.1.externalProductSource b.1).Fiber z) :
      (((product a b c d).1.datum.enlarge K hK h).boundary.linearEquiv z) v =
        reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) v := by
    rw [CompactSupportTriple.enlarge_apply]
    rfl
  have independent (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c₀ c₁ : CX a) (d₀ d₁ : CY b) :
      (product a b c₀ d₀).kZeroClass = (product a b c₁ d₁).kZeroClass := by
    -- Convex interpolation keeps a common zero neighborhood and a common compact exterior.
    let blend (t r s : I) : I :=
      ⟨(1 - (t : ℝ)) * r + (t : ℝ) * s, by
        constructor
        · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) r.property.1)
            (mul_nonneg t.property.1 s.property.1)
        · calc
            (1 - (t : ℝ)) * r + (t : ℝ) * s ≤
                (1 - (t : ℝ)) * 1 + (t : ℝ) * 1 :=
              add_le_add (mul_le_mul_of_nonneg_left r.property.2
                (sub_nonneg.mpr t.property.2))
                (mul_le_mul_of_nonneg_left s.property.2 t.property.1)
            _ = 1 := by ring⟩
    let ρ (t : I) : C(X, I) :=
      ⟨fun x ↦ blend t (c₀.val.1 x) (c₁.val.1 x), by
        apply Continuous.subtype_mk
        exact (continuous_const.mul
          (continuous_subtype_val.comp c₀.val.1.continuous)).add
            (continuous_const.mul (continuous_subtype_val.comp c₁.val.1.continuous))⟩
    let τ (t : I) : C(Y, I) :=
      ⟨fun y ↦ blend t (d₀.val.1 y) (d₁.val.1 y), by
        apply Continuous.subtype_mk
        exact (continuous_const.mul
          (continuous_subtype_val.comp d₀.val.1.continuous)).add
            (continuous_const.mul (continuous_subtype_val.comp d₁.val.1.continuous))⟩
    let L := c₀.val.2.2 ∪ c₁.val.2.2
    let M := d₀.val.2.2 ∪ d₁.val.2.2
    have hL : IsCompact L := c₀.property.2.2.2.1.union c₁.property.2.2.2.1
    have hM : IsCompact M := d₀.property.2.2.2.1.union d₁.property.2.2.2.1
    have hLinv (g : G) (x : X) : g • x ∈ L ↔ x ∈ L :=
      or_congr (c₀.property.2.2.2.2.2.2 g x) (c₁.property.2.2.2.2.2.2 g x)
    have hMinv (g : G) (y : Y) : g • y ∈ M ↔ y ∈ M :=
      or_congr (d₀.property.2.2.2.2.2.2 g y) (d₁.property.2.2.2.2.2.2 g y)
    have hρzero (t : I) (x : X) (hx : x ∈ c₀.val.2.1 ∩ c₁.val.2.1) : ρ t x = 0 := by
      apply Subtype.ext
      simp only [ρ, ContinuousMap.coe_mk, blend, c₀.property.2.2.1 x hx.1,
        c₁.property.2.2.1 x hx.2, Set.Icc.coe_zero, mul_zero, add_zero]
    have hτzero (t : I) (y : Y) (hy : y ∈ d₀.val.2.1 ∩ d₁.val.2.1) : τ t y = 0 := by
      apply Subtype.ext
      simp only [τ, ContinuousMap.coe_mk, blend, d₀.property.2.2.1 y hy.1,
        d₁.property.2.2.1 y hy.2, Set.Icc.coe_zero, mul_zero, add_zero]
    have hρone (t : I) (x : X) (hx : x ∉ L) : ρ t x = 1 := by
      apply Subtype.ext
      have hx₀ : x ∉ c₀.val.2.2 := fun h ↦ hx (Or.inl h)
      have hx₁ : x ∉ c₁.val.2.2 := fun h ↦ hx (Or.inr h)
      simp only [ρ, ContinuousMap.coe_mk, blend, c₀.property.2.2.2.2.1 x hx₀,
        c₁.property.2.2.2.2.1 x hx₁, Set.Icc.coe_one, mul_one]
      ring
    have hτone (t : I) (y : Y) (hy : y ∉ M) : τ t y = 1 := by
      apply Subtype.ext
      have hy₀ : y ∉ d₀.val.2.2 := fun h ↦ hy (Or.inl h)
      have hy₁ : y ∉ d₁.val.2.2 := fun h ↦ hy (Or.inr h)
      simp only [τ, ContinuousMap.coe_mk, blend, d₀.property.2.2.2.2.1 y hy₀,
        d₁.property.2.2.2.2.1 y hy₁, Set.Icc.coe_one, mul_one]
      ring
    let ct (t : I) : CX a :=
      ⟨(ρ t, c₀.val.2.1 ∩ c₁.val.2.1, L),
        c₀.property.1.inter c₁.property.1,
        fun _ hx ↦ ⟨c₀.property.2.1 hx, c₁.property.2.1 hx⟩,
        hρzero t, hL, hρone t,
        fun g x ↦ by
          change blend t (c₀.val.1 (g • x)) (c₁.val.1 (g • x)) = _
          rw [c₀.property.2.2.2.2.2.1, c₁.property.2.2.2.2.2.1]
          rfl, hLinv⟩
    let dt (t : I) : CY b :=
      ⟨(τ t, d₀.val.2.1 ∩ d₁.val.2.1, M),
        d₀.property.1.inter d₁.property.1,
        fun _ hy ↦ ⟨d₀.property.2.1 hy, d₁.property.2.1 hy⟩,
        hτzero t, hM, hτone t,
        fun g y ↦ by
          change blend t (d₀.val.1 (g • y)) (d₁.val.1 (g • y)) = _
          rw [d₀.property.2.2.2.2.2.1, d₁.property.2.2.2.2.2.1]
          rfl, hMinv⟩
    -- Cutoff maps use the same boundary and are linear in the supplied real cutoff.
    have mixX (e : CompactSupportTriple a.1.source.Fiber a.1.target.Fiber)
        (t : I) (x : X) :
        e.cutoffLinearMap (ρ t) x =
          ((1 - (t : ℝ) : ℝ) : ℂ) • e.cutoffLinearMap c₀.val.1 x +
            ((t : ℝ) : ℂ) • e.cutoffLinearMap c₁.val.1 x := by
      apply LinearMap.ext
      intro v
      by_cases hx : x ∈ e.control
      · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hx,
          LinearMap.zero_apply, smul_zero, add_zero]
      · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx,
          LinearMap.add_apply, ρ, ContinuousMap.coe_mk, blend]
        push_cast
        simp only [add_smul, mul_smul]
        rfl
    have mixX' (t : I) (x : X) :
        a.1.datum.inverse.cutoffLinearMap (ρ t) x =
          ((1 - (t : ℝ) : ℝ) : ℂ) • a.1.datum.inverse.cutoffLinearMap c₀.val.1 x +
            ((t : ℝ) : ℂ) • a.1.datum.inverse.cutoffLinearMap c₁.val.1 x := by
      apply LinearMap.ext
      intro v
      by_cases hx : x ∈ a.1.datum.control
      · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_left hx, LinearMap.zero_apply,
          smul_zero, add_zero]
      · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hx, LinearMap.add_apply, ρ,
          ContinuousMap.coe_mk, blend]
        push_cast
        simp only [add_smul, mul_smul]
        rfl
    have mixY (t : I) (y : Y) :
        b.1.datum.cutoffLinearMap (τ t) y =
          ((1 - (t : ℝ) : ℝ) : ℂ) • b.1.datum.cutoffLinearMap d₀.val.1 y +
            ((t : ℝ) : ℂ) • b.1.datum.cutoffLinearMap d₁.val.1 y := by
      apply LinearMap.ext
      intro v
      by_cases hy : y ∈ b.1.datum.control
      · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_left hy,
          LinearMap.zero_apply, smul_zero, add_zero]
      · simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hy,
          LinearMap.add_apply, τ, ContinuousMap.coe_mk, blend]
        push_cast
        simp only [add_smul, mul_smul]
        rfl
    have mixY' (t : I) (y : Y) :
        b.1.datum.inverse.cutoffLinearMap (τ t) y =
          ((1 - (t : ℝ) : ℝ) : ℂ) • b.1.datum.inverse.cutoffLinearMap d₀.val.1 y +
            ((t : ℝ) : ℂ) • b.1.datum.inverse.cutoffLinearMap d₁.val.1 y := by
      apply LinearMap.ext
      intro v
      by_cases hy : y ∈ b.1.datum.control
      · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_left hy, LinearMap.zero_apply,
          smul_zero, add_zero]
      · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hy, LinearMap.add_apply, τ,
          ContinuousMap.coe_mk, blend]
        push_cast
        simp only [add_smul, mul_smul]
        rfl
    obtain ⟨q₀, hq₀⟩ := globalBlock a b c₀ d₀
    obtain ⟨q₁, hq₁⟩ := globalBlock a b c₁ d₁
    have mixed (t : I) (z : X × Y) :
        reciprocalTensorSymbol (a.1.datum.cutoffLinearMap (ρ t) z.1)
            (a.1.datum.inverse.cutoffLinearMap (ρ t) z.1)
            (b.1.datum.cutoffLinearMap (τ t) z.2)
            (b.1.datum.inverse.cutoffLinearMap (τ t) z.2) =
          ((1 - (t : ℝ) : ℝ) : ℂ) • q₀.linearMap z +
            ((t : ℝ) : ℂ) • q₁.linearMap z := by
      rw [mixX a.1.datum, mixX', mixY, mixY', hq₀, hq₁]
      exact algebraMix _ _ _ _ _ _ _ _ _ _
    -- The original block interpolation is jointly continuous on one fixed exterior.
    let K := Set.prod L M
    have hK : IsCompact K := hL.prod hM
    have hKinv (g : G) (z : X × Y) : g • z ∈ K ↔ z ∈ K :=
      and_congr (hLinv g z.1) (hMinv g z.2)
    let i : C((Kᶜ : Set (X × Y)), X × Y) := ⟨Subtype.val, continuous_subtype_val⟩
    let p : C(I × (Kᶜ : Set (X × Y)), (Kᶜ : Set (X × Y))) := ContinuousMap.snd
    let S := ((a.1.externalProductSource b.1).pullback i).pullback p
    let T := ((a.1.externalProductTarget b.1).pullback i).pullback p
    let r : C(I × (Kᶜ : Set (X × Y)), ℂ) :=
      ⟨fun z ↦ ((1 - (z.1 : ℝ) : ℝ) : ℂ),
        Complex.continuous_ofReal.comp
          (continuous_const.sub (continuous_subtype_val.comp continuous_fst))⟩
    let s : C(I × (Kᶜ : Set (X × Y)), ℂ) :=
      ⟨fun z ↦ ((z.1 : ℝ) : ℂ),
        Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)⟩
    obtain ⟨q, hq⟩ := combination S T ((q₀.pullback i).pullback p)
      ((q₁.pullback i).pullback p) r s
    have hbij (z : I × (Kᶜ : Set (X × Y))) : Function.Bijective (q.linearMap z) := by
      let he := (product a b (ct z.1) (dt z.1)).1.datum.boundary.linearEquiv z.2
      have heq : q.linearMap z = he.toLinearMap := by
        rw [hq]
        dsimp only [r, s, Hom.pullback, he, product, ct, dt,
          supportedEquivariantExternalProductTriple, supportedExternalProductTriple,
          SupportBundleTriple.ofBoundary, supportedExternalProductBoundary,
          reciprocalTensorSymbolEquiv]
        exact (mixed z.1 z.2.val).symm
      rw [heq]
      exact he.bijective
    let e := q.toIso hbij
    have he (z : I × (Kᶜ : Set (X × Y))) (v) :
        e.linearEquiv z v =
          ((1 - (z.1 : ℝ) : ℝ) : ℂ) • q₀.linearMap z.2.val v +
            ((z.1 : ℝ) : ℂ) • q₁.linearMap z.2.val v := by
      change q.linearMap z v = _
      rw [hq]
      rfl
    let A₀ : CompactSupportTriple (a.1.externalProductSource b.1).Fiber
        (a.1.externalProductTarget b.1).Fiber := (product a b c₀ d₀).1.datum
    let A₁ : CompactSupportTriple (a.1.externalProductSource b.1).Fiber
        (a.1.externalProductTarget b.1).Fiber := (product a b c₁ d₁).1.datum
    have hleft : A₀.control ⊆ K :=
      fun _ hz ↦ ⟨Or.inl hz.1, Or.inl hz.2⟩
    have hright : A₁.control ⊆ K :=
      fun _ hz ↦ ⟨Or.inr hz.1, Or.inr hz.2⟩
    let H : CompactSupportTriple.EquivariantHomotopy
        (a.externalProductSourceAction b) (a.externalProductTargetAction b)
        A₀ A₁ :=
      { control := K
        isCompact_control := hK
        invariant_control := hKinv
        left_control := hleft
        right_control := hright
        homotopy :=
          { iso := e
            map_zero := by
              intro z v
              refine (he (0, z) v).trans ?_
              simp only [Set.Icc.coe_zero, sub_zero, Complex.ofReal_one,
                one_smul, Complex.ofReal_zero, zero_smul, add_zero, hq₀]
              rw [Iso.restrictTo_apply]
              rfl
            map_one := by
              intro z v
              refine (he (1, z) v).trans ?_
              simp only [Set.Icc.coe_one, sub_self, Complex.ofReal_zero,
                zero_smul, Complex.ofReal_one, one_smul, zero_add, hq₁]
              rw [Iso.restrictTo_apply]
              rfl }
        intertwines := by
          intro t g z v
          change e.linearEquiv (t, ⟨g • z.val, _⟩)
            ((a.externalProductSourceAction b).linearMap g z.val v) =
              (a.externalProductTargetAction b).linearMap g z.val
                (e.linearEquiv (t, z) v)
          refine (he (t, ⟨g • z.val, _⟩) _).trans ?_
          have h₀ : q₀.linearMap (g • z.val)
              ((a.externalProductSourceAction b).linearMap g z.val v) =
                (a.externalProductTargetAction b).linearMap g z.val
                  (q₀.linearMap z.val v) := by
            rw [hq₀, hq₀]
            exact (boundaryValue a b c₀ d₀ K hK hleft ⟨g • z.val, _⟩ _).symm.trans
              ((((product a b c₀ d₀).2.isEquivariant.enlarge
                K hK hleft hKinv).boundary_intertwines g z v).trans
                (congrArg ((a.externalProductTargetAction b).linearMap g z.val)
                  (boundaryValue a b c₀ d₀ K hK hleft z v)))
          have h₁ : q₁.linearMap (g • z.val)
              ((a.externalProductSourceAction b).linearMap g z.val v) =
                (a.externalProductTargetAction b).linearMap g z.val
                  (q₁.linearMap z.val v) := by
            rw [hq₁, hq₁]
            exact (boundaryValue a b c₁ d₁ K hK hright ⟨g • z.val, _⟩ _).symm.trans
              ((((product a b c₁ d₁).2.isEquivariant.enlarge
                K hK hright hKinv).boundary_intertwines g z v).trans
                (congrArg ((a.externalProductTargetAction b).linearMap g z.val)
                  (boundaryValue a b c₁ d₁ K hK hright z v)))
          rw [h₀, h₁]
          calc
            _ = (a.externalProductTargetAction b).linearMap g z.val
                (((1 - (t : ℝ) : ℝ) : ℂ) • q₀.linearMap z.val v +
                  ((t : ℝ) : ℂ) • q₁.linearMap z.val v) := by
              rw [map_add, map_smul, map_smul]
            _ = _ := congrArg ((a.externalProductTargetAction b).linearMap g z.val)
              (he (t, z) v).symm }
    exact equivariantSupportBundleTriple_kZeroClass_eq_of_homotopic
      (a.1.externalProductSource b.1) (a.1.externalProductTarget b.1)
      (a.externalProductSourceAction b) (a.externalProductTargetAction b)
      _ _ _ _ ⟨H⟩
  have tensorSquare {A₀ A₁ B₀ B₁ C₀ C₁ D₀ D₁ : Type}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
      [AddCommGroup D₀] [Module ℂ D₀] [AddCommGroup D₁] [Module ℂ D₁]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (e : B₀ →ₗ[ℂ] B₁) (e' : B₁ →ₗ[ℂ] B₀)
      (δ : C₀ →ₗ[ℂ] C₁) (δ' : C₁ →ₗ[ℂ] C₀)
      (ε : D₀ →ₗ[ℂ] D₁) (ε' : D₁ →ₗ[ℂ] D₀)
      (u : A₀ →ₗ[ℂ] C₀) (v : A₁ →ₗ[ℂ] C₁)
      (w : B₀ →ₗ[ℂ] D₀) (z : B₁ →ₗ[ℂ] D₁)
      (hD : ∀ a, v (d a) = δ (u a)) (hD' : ∀ a, u (d' a) = δ' (v a))
      (hE : ∀ b, z (e b) = ε (w b)) (hE' : ∀ b, w (e' b) = ε' (z b)) :
      ((TensorProduct.map v w).prodMap (TensorProduct.map u z)).comp
          (reciprocalTensorSymbol d d' e e') =
        (reciprocalTensorSymbol δ δ' ε ε').comp
          ((TensorProduct.map u w).prodMap (TensorProduct.map v z)) := by
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
      intro a b <;> apply Prod.ext <;>
      simp [reciprocalTensorSymbol, hD, hD', hE, hE']
  have naturality (a a' : EquivariantSupportBundleTriple G X)
      (b b' : EquivariantSupportBundleTriple G Y)
      (c : CX a) (c' : CX a') (d : CY b) (d' : CY b')
      (u : Iso a.1.source.Fiber a'.1.source.Fiber)
      (v : Iso a.1.target.Fiber a'.1.target.Fiber)
      (w : Iso b.1.source.Fiber b'.1.source.Fiber)
      (z : Iso b.1.target.Fiber b'.1.target.Fiber)
      (hu : u.IsEquivariant a.2.sourceAction a'.2.sourceAction)
      (hv : v.IsEquivariant a.2.targetAction a'.2.targetAction)
      (hw : w.IsEquivariant b.2.sourceAction b'.2.sourceAction)
      (hz : z.IsEquivariant b.2.targetAction b'.2.targetAction)
      (hD : ∀ x q, v.linearEquiv x (a.1.datum.cutoffLinearMap c.val.1 x q) =
        a'.1.datum.cutoffLinearMap c'.val.1 x (u.linearEquiv x q))
      (hD' : ∀ x q, u.linearEquiv x (a.1.datum.inverse.cutoffLinearMap c.val.1 x q) =
        a'.1.datum.inverse.cutoffLinearMap c'.val.1 x (v.linearEquiv x q))
      (hE : ∀ y q, z.linearEquiv y (b.1.datum.cutoffLinearMap d.val.1 y q) =
        b'.1.datum.cutoffLinearMap d'.val.1 y (w.linearEquiv y q))
      (hE' : ∀ y q, w.linearEquiv y (b.1.datum.inverse.cutoffLinearMap d.val.1 y q) =
        b'.1.datum.inverse.cutoffLinearMap d'.val.1 y (z.linearEquiv y q)) :
      (product a b c d).kZeroClass = (product a' b' c' d').kZeroClass := by
    -- Tensor the supplied global comparisons, rather than choosing new equivariant maps.
    let p : C(X × Y, X) := ⟨Prod.fst, continuous_fst⟩
    let q : C(X × Y, Y) := ⟨Prod.snd, continuous_snd⟩
    let U := ((u.pullback p).tensor (w.pullback q)).sum
      ((v.pullback p).tensor (z.pullback q))
    let V := ((v.pullback p).tensor (w.pullback q)).sum
      ((u.pullback p).tensor (z.pullback q))
    have hux := (EquivariantStructure.pullback_maps _ _ p (fun _ _ ↦ rfl)).2 u hu
    have hvx := (EquivariantStructure.pullback_maps _ _ p (fun _ _ ↦ rfl)).2 v hv
    have hwy := (EquivariantStructure.pullback_maps _ _ q (fun _ _ ↦ rfl)).2 w hw
    have hzy := (EquivariantStructure.pullback_maps _ _ q (fun _ _ ↦ rfl)).2 z hz
    have huw := (EquivariantStructure.tensor_maps _ _ _ _).2 _ _ hux hwy
    have hvz := (EquivariantStructure.tensor_maps _ _ _ _).2 _ _ hvx hzy
    have hvw := (EquivariantStructure.tensor_maps _ _ _ _).2 _ _ hvx hwy
    have huz := (EquivariantStructure.tensor_maps _ _ _ _).2 _ _ hux hzy
    let K := (product a b c d).1.datum.control ∪ (product a' b' c' d').1.datum.control
    have hK : IsCompact K := (product a b c d).1.datum.isCompact_control.union
      (product a' b' c' d').1.datum.isCompact_control
    have hi : (product a b c d).IsIsomorphic (product a' b' c' d') := by
      refine ⟨K, hK, fun g x ↦
        ((product a b c d).2.isEquivariant.invariant_control g x).or
          ((product a' b' c' d').2.isEquivariant.invariant_control g x),
        Set.subset_union_left, Set.subset_union_right, U, V, ?_, ?_, ?_⟩
      · intro g x r
        exact Prod.ext (huw g x r.1) (hvz g x r.2)
      · intro g x r
        exact Prod.ext (hvw g x r.1) (huz g x r.2)
      · intro x r
        rw [boundaryValue, boundaryValue]
        have hm : (V.linearEquiv x).toLinearMap.comp
              (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 x.val.1)
                (a.1.datum.inverse.cutoffLinearMap c.val.1 x.val.1)
                (b.1.datum.cutoffLinearMap d.val.1 x.val.2)
                (b.1.datum.inverse.cutoffLinearMap d.val.1 x.val.2)) =
            (reciprocalTensorSymbol (a'.1.datum.cutoffLinearMap c'.val.1 x.val.1)
                (a'.1.datum.inverse.cutoffLinearMap c'.val.1 x.val.1)
                (b'.1.datum.cutoffLinearMap d'.val.1 x.val.2)
                (b'.1.datum.inverse.cutoffLinearMap d'.val.1 x.val.2)).comp
              (U.linearEquiv x).toLinearMap := by
          exact tensorSquare _ _ _ _ _ _ _ _
            (u.linearEquiv x.val.1).toLinearMap (v.linearEquiv x.val.1).toLinearMap
            (w.linearEquiv x.val.2).toLinearMap (z.linearEquiv x.val.2).toLinearMap
            (hD x.val.1) (hD' x.val.1) (hE x.val.2) (hE' x.val.2)
        exact LinearMap.congr_fun hm r
    exact equivariantSupportTripleKZero_generator_relations.1 _ _ hi
  -- A cutoff which vanishes on the common control extends both original boundary squares.
  have cutoffSquareX (a a' : EquivariantSupportBundleTriple G X)
      (K : Set X) (hK : IsCompact K) (ha : a.1.datum.control ⊆ K)
      (ha' : a'.1.datum.control ⊆ K)
      (u : Iso a.1.source.Fiber a'.1.source.Fiber)
      (v : Iso a.1.target.Fiber a'.1.target.Fiber)
      (h : ∀ (x : (Kᶜ : Set X)) (r : a.1.source.Fiber x),
        v.linearEquiv x ((a.1.datum.enlarge K hK ha).boundary.linearEquiv x r) =
          (a'.1.datum.enlarge K hK ha').boundary.linearEquiv x (u.linearEquiv x r))
      (ρ : C(X, I)) (hzero : ∀ x ∈ K, ρ x = 0) :
      (∀ x r, v.linearEquiv x (a.1.datum.cutoffLinearMap ρ x r) =
        a'.1.datum.cutoffLinearMap ρ x (u.linearEquiv x r)) ∧
      ∀ x r, u.linearEquiv x (a.1.datum.inverse.cutoffLinearMap ρ x r) =
        a'.1.datum.inverse.cutoffLinearMap ρ x (v.linearEquiv x r) := by
    have cutoffZero (E F : FiniteBundle X)
        (a : CompactSupportTriple E.Fiber F.Fiber) (ρ : C(X, I)) (x : X)
        (hx : ρ x = 0) : a.cutoffLinearMap ρ x = 0 := by
      unfold CompactSupportTriple.cutoffLinearMap
      split_ifs
      · rfl
      · simp [hx]
    have hs (x : (Kᶜ : Set X)) (r : a.1.source.Fiber x) :
        v.linearEquiv x
            (a.1.datum.boundary.linearEquiv ⟨x, fun hx ↦ x.property (ha hx)⟩ r) =
          a'.1.datum.boundary.linearEquiv ⟨x, fun hx ↦ x.property (ha' hx)⟩
            (u.linearEquiv x r) := by
      simpa only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] using h x r
    constructor <;> intro x r
    · by_cases hx : x ∈ K
      · rw [cutoffZero _ _ _ _ _ (hzero x hx), cutoffZero _ _ _ _ _ (hzero x hx)]
        simp
      · have hxa : x ∉ a.1.datum.control := fun h ↦ hx (ha h)
        have hxa' : x ∉ a'.1.datum.control := fun h ↦ hx (ha' h)
        simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa,
          dite_eq_right hxa']
        change v.linearEquiv x
            (((ρ x : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv ⟨x, hxa⟩ r) =
          ((ρ x : ℝ) : ℂ) • a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩
            (u.linearEquiv x r)
        rw [map_smul]
        exact congrArg (((ρ x : ℝ) : ℂ) • ·) (hs ⟨x, hx⟩ r)
    · by_cases hx : x ∈ K
      · rw [cutoffZero _ _ _ _ _ (hzero x hx), cutoffZero _ _ _ _ _ (hzero x hx)]
        simp
      · have hxa : x ∉ a.1.datum.control := fun h ↦ hx (ha h)
        have hxa' : x ∉ a'.1.datum.control := fun h ↦ hx (ha' h)
        have hinv : u.linearEquiv x
            ((a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r) =
              (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).symm (v.linearEquiv x r) := by
          apply (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).injective
          rw [LinearEquiv.apply_symm_apply]
          exact (hs ⟨x, hx⟩ ((a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r)).symm.trans
            (congrArg (v.linearEquiv x) (LinearEquiv.apply_symm_apply _ r))
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hxa, dite_eq_right hxa']
        change u.linearEquiv x
            (((ρ x : ℝ) : ℂ) • (a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r) =
          ((ρ x : ℝ) : ℂ) • (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).symm
            (v.linearEquiv x r)
        rw [map_smul]
        exact congrArg (((ρ x : ℝ) : ℂ) • ·) hinv
  have cutoffSquareY (a a' : EquivariantSupportBundleTriple G Y)
      (K : Set Y) (hK : IsCompact K) (ha : a.1.datum.control ⊆ K)
      (ha' : a'.1.datum.control ⊆ K)
      (u : Iso a.1.source.Fiber a'.1.source.Fiber)
      (v : Iso a.1.target.Fiber a'.1.target.Fiber)
      (h : ∀ (x : (Kᶜ : Set Y)) (r : a.1.source.Fiber x),
        v.linearEquiv x ((a.1.datum.enlarge K hK ha).boundary.linearEquiv x r) =
          (a'.1.datum.enlarge K hK ha').boundary.linearEquiv x (u.linearEquiv x r))
      (ρ : C(Y, I)) (hzero : ∀ x ∈ K, ρ x = 0) :
      (∀ x r, v.linearEquiv x (a.1.datum.cutoffLinearMap ρ x r) =
        a'.1.datum.cutoffLinearMap ρ x (u.linearEquiv x r)) ∧
      ∀ x r, u.linearEquiv x (a.1.datum.inverse.cutoffLinearMap ρ x r) =
        a'.1.datum.inverse.cutoffLinearMap ρ x (v.linearEquiv x r) := by
    have cutoffZero (E F : FiniteBundle Y)
        (a : CompactSupportTriple E.Fiber F.Fiber) (ρ : C(Y, I)) (x : Y)
        (hx : ρ x = 0) : a.cutoffLinearMap ρ x = 0 := by
      unfold CompactSupportTriple.cutoffLinearMap
      split_ifs
      · rfl
      · simp [hx]
    have hs (x : (Kᶜ : Set Y)) (r : a.1.source.Fiber x) :
        v.linearEquiv x
            (a.1.datum.boundary.linearEquiv ⟨x, fun hx ↦ x.property (ha hx)⟩ r) =
          a'.1.datum.boundary.linearEquiv ⟨x, fun hx ↦ x.property (ha' hx)⟩
            (u.linearEquiv x r) := by
      simpa only [CompactSupportTriple.enlarge, Iso.restrictTo_apply] using h x r
    constructor <;> intro x r
    · by_cases hx : x ∈ K
      · rw [cutoffZero _ _ _ _ _ (hzero x hx), cutoffZero _ _ _ _ _ (hzero x hx)]
        simp
      · have hxa : x ∉ a.1.datum.control := fun h ↦ hx (ha h)
        have hxa' : x ∉ a'.1.datum.control := fun h ↦ hx (ha' h)
        simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa,
          dite_eq_right hxa']
        change v.linearEquiv x
            (((ρ x : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv ⟨x, hxa⟩ r) =
          ((ρ x : ℝ) : ℂ) • a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩
            (u.linearEquiv x r)
        rw [map_smul]
        exact congrArg (((ρ x : ℝ) : ℂ) • ·) (hs ⟨x, hx⟩ r)
    · by_cases hx : x ∈ K
      · rw [cutoffZero _ _ _ _ _ (hzero x hx), cutoffZero _ _ _ _ _ (hzero x hx)]
        simp
      · have hxa : x ∉ a.1.datum.control := fun h ↦ hx (ha h)
        have hxa' : x ∉ a'.1.datum.control := fun h ↦ hx (ha' h)
        have hinv : u.linearEquiv x
            ((a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r) =
              (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).symm (v.linearEquiv x r) := by
          apply (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).injective
          rw [LinearEquiv.apply_symm_apply]
          exact (hs ⟨x, hx⟩ ((a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r)).symm.trans
            (congrArg (v.linearEquiv x) (LinearEquiv.apply_symm_apply _ r))
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hxa, dite_eq_right hxa']
        change u.linearEquiv x
            (((ρ x : ℝ) : ℂ) • (a.1.datum.boundary.linearEquiv ⟨x, hxa⟩).symm r) =
          ((ρ x : ℝ) : ℂ) • (a'.1.datum.boundary.linearEquiv ⟨x, hxa'⟩).symm
            (v.linearEquiv x r)
        rw [map_smul]
        exact congrArg (((ρ x : ℝ) : ℂ) • ·) hinv
  let value (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) : EquivariantSupportTripleKZero G (X × Y) :=
    (product a b (Classical.choice (nonemptyX a))
      (Classical.choice (nonemptyY b))).kZeroClass
  have value_eq (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c : CX a) (d : CY b) :
      value a b = (product a b c d).kZeroClass :=
    independent a b _ c _ d
  have isoLeft (a a' : EquivariantSupportBundleTriple G X)
      (h : a.IsIsomorphic a') (b : EquivariantSupportBundleTriple G Y) :
      value a b = value a' b := by
    obtain ⟨K, hK, hInv, ha, ha', u, v, hu, hv, hs⟩ := h
    obtain ⟨U, hU, hKU, _, L, hL, _, hLinv, ρ, hρinv, hzero, hone⟩ :=
      exists_invariant_time_cutoff (G := G) K hK
    let c : CX a := ⟨(ρ, U, L), hU, ha.trans hKU, hzero, hL, hone, hρinv, hLinv⟩
    let c' : CX a' := ⟨(ρ, U, L), hU, ha'.trans hKU, hzero, hL, hone, hρinv, hLinv⟩
    let d := Classical.choice (nonemptyY b)
    obtain ⟨hD, hD'⟩ := cutoffSquareX a a' K hK ha ha' u v hs ρ
      (fun x hx ↦ hzero x (hKU hx))
    exact (value_eq a b c d).trans
      ((naturality a a' b b c c' d d u v (Iso.refl _) (Iso.refl _) hu hv
        (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) hD hD'
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)).trans (value_eq a' b c' d).symm)
  have isoRight (b b' : EquivariantSupportBundleTriple G Y)
      (h : b.IsIsomorphic b') (a : EquivariantSupportBundleTriple G X) :
      value a b = value a b' := by
    obtain ⟨K, hK, hInv, hb, hb', w, z, hw, hz, hs⟩ := h
    obtain ⟨V, hV, hKV, _, M, hM, _, hMinv, τ, hτinv, hzero, hone⟩ :=
      exists_invariant_time_cutoff (G := G) K hK
    let c := Classical.choice (nonemptyX a)
    let d : CY b := ⟨(τ, V, M), hV, hb.trans hKV, hzero, hM, hone, hτinv, hMinv⟩
    let d' : CY b' := ⟨(τ, V, M), hV, hb'.trans hKV, hzero, hM, hone, hτinv, hMinv⟩
    obtain ⟨hE, hE'⟩ := cutoffSquareY b b' K hK hb hb' w z hs τ
      (fun y hy ↦ hzero y (hKV hy))
    exact (value_eq a b c d).trans
      ((naturality a a b b' c c d d' (Iso.refl _) (Iso.refl _) w z
        (fun _ _ _ ↦ rfl) (fun _ _ _ ↦ rfl) hw hz
        (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) hE hE').trans (value_eq a b' c d').symm)
  have emptyClass {Z : Type _} [TopologicalSpace Z] [T2Space Z]
      [MulAction G Z] [ContinuousSMul G Z] (a : EquivariantSupportBundleTriple G Z)
      (hempty : a.1.datum.control = ∅) : a.kZeroClass = 0 := by
    -- An empty support lets the original boundary extend across the entire base.
    let ρ : C(Z, I) := ContinuousMap.const Z 1
    have ha : a.1.datum.control ⊆ ∅ := by rw [hempty]
    let q := a.1.datum.cutoffHom ρ ∅ isOpen_empty ha (by simp)
    have hout (x : Z) : x ∉ a.1.datum.control := by simp [hempty]
    have hq (x : Z) (r : a.1.source.Fiber x) :
        q.linearMap x r = a.1.datum.boundary.linearEquiv ⟨x, hout x⟩ r := by
      change a.1.datum.cutoffLinearMap ρ x r = _
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right (hout x),
        ρ, ContinuousMap.const_apply, Set.Icc.coe_one, Complex.ofReal_one, one_smul]
      rfl
    have hbij (x : Z) : Function.Bijective (q.linearMap x) := by
      have hm : q.linearMap x = (a.1.datum.boundary.linearEquiv ⟨x, hout x⟩).toLinearMap :=
        LinearMap.ext (hq x)
      rw [hm]
      exact (a.1.datum.boundary.linearEquiv ⟨x, hout x⟩).bijective
    let e := q.toIso hbij
    have he (x : Z) (r : a.1.source.Fiber x) :
        e.linearEquiv x r = a.1.datum.boundary.linearEquiv ⟨x, hout x⟩ r := hq x r
    have hequiv : e.IsEquivariant a.2.sourceAction a.2.targetAction := by
      intro g x r
      change e.linearEquiv (g • x) (a.2.sourceAction.linearMap g x r) =
        a.2.targetAction.linearMap g x (e.linearEquiv x r)
      rw [he, he]
      exact a.2.isEquivariant.boundary_intertwines g ⟨x, hout x⟩ r
    have hequivInv : e.symm.IsEquivariant a.2.targetAction a.2.sourceAction := by
      intro g x r
      apply (e.linearEquiv (g • x)).injective
      change e.linearEquiv (g • x) ((e.linearEquiv (g • x)).symm
        (a.2.targetAction.linearMap g x r)) =
          e.linearEquiv (g • x) (a.2.sourceAction.linearMap g x ((e.linearEquiv x).symm r))
      refine ((e.linearEquiv (g • x)).apply_symm_apply _).trans ?_
      exact ((hequiv g x ((e.linearEquiv x).symm r)).trans
        (congrArg (a.2.targetAction.linearMap g x)
          ((e.linearEquiv x).apply_symm_apply r))).symm
    have hi : a.IsIsomorphic (EquivariantSupportBundleTriple.identity
        a.1.source a.2.sourceAction) := by
      refine ⟨∅, isCompact_empty, (fun _ _ ↦ Iff.rfl), ha, Set.Subset.refl _,
        Iso.refl _, e.symm, (fun _ _ _ ↦ rfl), hequivInv, ?_⟩
      intro x r
      have hl := a.1.datum.enlarge_apply ∅ isCompact_empty ha x r
      have hr := (SupportBundleTriple.identity a.1.source).datum.enlarge_apply
        ∅ isCompact_empty (Set.Subset.refl _) x r
      rw [hl]
      change (e.linearEquiv x).symm
        (a.1.datum.boundary.linearEquiv ⟨x.val, hout x.val⟩ r) = _
      rw [← he, LinearEquiv.symm_apply_apply]
      exact hr.symm
    exact (equivariantSupportTripleKZero_generator_relations.1 _ _ hi).trans
      (equivariantSupportTripleKZero_generator_relations.2.2 _ _)
  have zeroLeft (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber)
      (b : EquivariantSupportBundleTriple G Y) :
      value (EquivariantSupportBundleTriple.identity E ρE) b = 0 := by
    let a := EquivariantSupportBundleTriple.identity E ρE
    let c : CX a := ⟨(ContinuousMap.const X 1, ∅, ∅), isOpen_empty,
      Set.Subset.refl _, (by simp), isCompact_empty, (by simp), (by simp),
      fun _ _ ↦ Iff.rfl⟩
    let d := Classical.choice (nonemptyY b)
    exact (value_eq a b c d).trans (emptyClass (product a b c d) (by
      change Set.prod (∅ : Set X) d.val.2.2 = ∅
      exact Set.empty_prod))
  have zeroRight (F : FiniteBundle Y) (ρF : EquivariantStructure G F.Fiber)
      (a : EquivariantSupportBundleTriple G X) :
      value a (EquivariantSupportBundleTriple.identity F ρF) = 0 := by
    let b := EquivariantSupportBundleTriple.identity F ρF
    let c := Classical.choice (nonemptyX a)
    let d : CY b := ⟨(ContinuousMap.const Y 1, ∅, ∅), isOpen_empty,
      Set.Subset.refl _, (by simp), isCompact_empty, (by simp), (by simp),
      fun _ _ ↦ Iff.rfl⟩
    exact (value_eq a b c d).trans (emptyClass (product a b c d) (by
      change Set.prod c.val.2.2 (∅ : Set Y) = ∅
      exact Set.prod_empty))
  -- Distribute the same cutoffs over the native equivariant tensor and sum bundles.
  have left_distribution (J J' : FiniteBundle X) (K : FiniteBundle Y)
      (ρJ : EquivariantStructure G J.Fiber) (ρJ2 : EquivariantStructure G J'.Fiber)
      (ρK : EquivariantStructure G K.Fiber) :
      ∃ e : Iso
        (((J.sum J').pullback ContinuousMap.fst).tensor
          (K.pullback ContinuousMap.snd)).Fiber
        ((((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd)).sum
          ((J'.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd))).Fiber),
        (∀ z u v, e.linearEquiv z (u ⊗ₜ[ℂ] v) = (u.1 ⊗ₜ[ℂ] v, u.2 ⊗ₜ[ℂ] v)) ∧
        e.IsEquivariant
          (((ρJ.sum ρJ2).pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
            (ρK.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
          ((((ρJ.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
            (ρK.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).sum
              ((ρJ2.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (ρK.pullback ContinuousMap.snd (fun _ _ ↦ rfl))))) := by
    let p : C(X × Y, X) := ContinuousMap.fst
    let q : C(X × Y, Y) := ContinuousMap.snd
    let A := ((J.sum J').pullback p).tensor (K.pullback q)
    let B := (J.pullback p).tensor (K.pullback q)
    let C := (J'.pullback p).tensor (K.pullback q)
    let f : Hom A.Fiber B.Fiber :=
      ((sumFst (E := J.Fiber) (F := J'.Fiber)).pullback p).tensor (Hom.id _)
    let g : Hom A.Fiber C.Fiber :=
      ((sumSnd (E := J.Fiber) (F := J'.Fiber)).pullback p).tensor (Hom.id _)
    let d (z : X × Y) :=
      TensorProduct.prodLeft ℂ ℂ (J.Fiber z.1) (J'.Fiber z.1) (K.Fiber z.2)
    have hd (z : X × Y) (w : A.Fiber z) :
        d z w = (f.linearMap z w, g.linearMap z w) := by
      have hm : (d z).toLinearMap = (f.linearMap z).prod (g.linearMap z) := by
        apply TensorProduct.ext'
        intro u v
        rfl
      exact LinearMap.congr_fun hm w
    let D : Hom A.Fiber (B.sum C).Fiber :=
      { linearMap z := (d z).toLinearMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply (f.continuous_total.prodMk g.continuous_total).congr
          intro z
          exact congrArg (fun w ↦
            ((⟨z.proj, w.1⟩ : TotalSpace Unit B.Fiber),
              (⟨z.proj, w.2⟩ : TotalSpace Unit C.Fiber))) (hd z.proj z.snd).symm }
    let e := D.toIso (fun z ↦ (d z).bijective)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_⟩
    intro g z w
    let sourceAction := ((ρJ.sum ρJ2).pullback p (fun _ _ ↦ rfl)).tensor
      (ρK.pullback q (fun _ _ ↦ rfl))
    let targetAction := ((ρJ.pullback p (fun _ _ ↦ rfl)).tensor
      (ρK.pullback q (fun _ _ ↦ rfl))).sum
        ((ρJ2.pullback p (fun _ _ ↦ rfl)).tensor
          (ρK.pullback q (fun _ _ ↦ rfl)))
    have hm : (e.linearEquiv (g • z)).toLinearMap.comp
        (sourceAction.linearMap g z) =
        (targetAction.linearMap g z).comp (e.linearEquiv z).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      rfl
    exact LinearMap.congr_fun hm w
  have right_distribution (J : FiniteBundle X) (K K' : FiniteBundle Y)
      (ρJ : EquivariantStructure G J.Fiber) (ρK : EquivariantStructure G K.Fiber)
      (ρK2 : EquivariantStructure G K'.Fiber) :
      ∃ e : Iso
        ((J.pullback ContinuousMap.fst).tensor
          ((K.sum K').pullback ContinuousMap.snd)).Fiber
        ((((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd)).sum
          ((J.pullback ContinuousMap.fst).tensor (K'.pullback ContinuousMap.snd))).Fiber),
        (∀ z u v, e.linearEquiv z (u ⊗ₜ[ℂ] v) = (u ⊗ₜ[ℂ] v.1, u ⊗ₜ[ℂ] v.2)) ∧
        e.IsEquivariant
          ((ρJ.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
            ((ρK.sum ρK2).pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
          ((((ρJ.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
            (ρK.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).sum
              ((ρJ.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (ρK2.pullback ContinuousMap.snd (fun _ _ ↦ rfl))))) := by
    let p : C(X × Y, X) := ContinuousMap.fst
    let q : C(X × Y, Y) := ContinuousMap.snd
    let A := (J.pullback p).tensor ((K.sum K').pullback q)
    let B := (J.pullback p).tensor (K.pullback q)
    let C := (J.pullback p).tensor (K'.pullback q)
    let f : Hom A.Fiber B.Fiber :=
      (Hom.id _).tensor ((sumFst (E := K.Fiber) (F := K'.Fiber)).pullback q)
    let g : Hom A.Fiber C.Fiber :=
      (Hom.id _).tensor ((sumSnd (E := K.Fiber) (F := K'.Fiber)).pullback q)
    let d (z : X × Y) :=
      TensorProduct.prodRight ℂ ℂ (J.Fiber z.1) (K.Fiber z.2) (K'.Fiber z.2)
    have hd (z : X × Y) (w : A.Fiber z) :
        d z w = (f.linearMap z w, g.linearMap z w) := by
      have hm : (d z).toLinearMap = (f.linearMap z).prod (g.linearMap z) := by
        apply TensorProduct.ext'
        intro u v
        rfl
      exact LinearMap.congr_fun hm w
    let D : Hom A.Fiber (B.sum C).Fiber :=
      { linearMap z := (d z).toLinearMap
        continuous_total := by
          apply continuous_induced_rng.mpr
          apply (f.continuous_total.prodMk g.continuous_total).congr
          intro z
          exact congrArg (fun w ↦
            ((⟨z.proj, w.1⟩ : TotalSpace Unit B.Fiber),
              (⟨z.proj, w.2⟩ : TotalSpace Unit C.Fiber))) (hd z.proj z.snd).symm }
    let e := D.toIso (fun z ↦ (d z).bijective)
    refine ⟨e, (fun _ _ _ ↦ rfl), ?_⟩
    intro g z w
    let sourceAction := (ρJ.pullback p (fun _ _ ↦ rfl)).tensor
      ((ρK.sum ρK2).pullback q (fun _ _ ↦ rfl))
    let targetAction := ((ρJ.pullback p (fun _ _ ↦ rfl)).tensor
      (ρK.pullback q (fun _ _ ↦ rfl))).sum
        ((ρJ.pullback p (fun _ _ ↦ rfl)).tensor
          (ρK2.pullback q (fun _ _ ↦ rfl)))
    have hm : (e.linearEquiv (g • z)).toLinearMap.comp
        (sourceAction.linearMap g z) =
        (targetAction.linearMap g z).comp (e.linearEquiv z).toLinearMap := by
      apply TensorProduct.ext'
      intro u v
      rfl
    exact LinearMap.congr_fun hm w
  have shuffle (A B C D : FiniteBundle (X × Y))
      (ρJA : EquivariantStructure G A.Fiber) (ρJB : EquivariantStructure G B.Fiber)
      (ρJC : EquivariantStructure G C.Fiber) (ρJD : EquivariantStructure G D.Fiber) :
      ∃ e : Iso ((A.sum B).sum (C.sum D)).Fiber ((A.sum C).sum (B.sum D)).Fiber,
        (∀ z v, e.linearEquiv z v = ((v.1.1, v.2.1), (v.1.2, v.2.2))) ∧
        e.IsEquivariant ((ρJA.sum ρJB).sum (ρJC.sum ρJD))
          ((ρJA.sum ρJC).sum (ρJB.sum ρJD)) := by
    let S := (A.sum B).sum (C.sum D)
    let p₁ : Hom S.Fiber A.Fiber := sumFst.comp sumFst
    let p₂ : Hom S.Fiber B.Fiber := sumSnd.comp sumFst
    let p₃ : Hom S.Fiber C.Fiber := sumFst.comp sumSnd
    let p₄ : Hom S.Fiber D.Fiber := sumSnd.comp sumSnd
    let f : Hom S.Fiber (A.sum C).Fiber :=
      { linearMap z := (p₁.linearMap z).prod (p₃.linearMap z)
        continuous_total := continuous_induced_rng.mpr
          (p₁.continuous_total.prodMk p₃.continuous_total) }
    let g : Hom S.Fiber (B.sum D).Fiber :=
      { linearMap z := (p₂.linearMap z).prod (p₄.linearMap z)
        continuous_total := continuous_induced_rng.mpr
          (p₂.continuous_total.prodMk p₄.continuous_total) }
    let q : Hom S.Fiber ((A.sum C).sum (B.sum D)).Fiber :=
      { linearMap z :=
          (LinearEquiv.prodProdProdComm ℂ (A.Fiber z) (B.Fiber z)
            (C.Fiber z) (D.Fiber z)).toLinearMap
        continuous_total := continuous_induced_rng.mpr
          (f.continuous_total.prodMk g.continuous_total) }
    let e := q.toIso (fun z ↦
      (LinearEquiv.prodProdProdComm ℂ (A.Fiber z) (B.Fiber z)
        (C.Fiber z) (D.Fiber z)).bijective)
    exact ⟨e, (fun _ _ ↦ rfl), fun _ _ _ ↦ rfl⟩
  have sumCutoffX
      (E F E' F' : FiniteBundle X)
      (a : CompactSupportTriple E.Fiber F.Fiber)
      (a' : CompactSupportTriple E'.Fiber F'.Fiber) (ρ : C(X, I))
      (hzero : ∀ x ∈ a.control ∪ a'.control, ρ x = 0) (x : X) :
      (∀ w, (a.sum a').cutoffLinearMap ρ x w =
        (a.cutoffLinearMap ρ x w.1, a'.cutoffLinearMap ρ x w.2)) ∧
      (∀ w, (a.sum a').inverse.cutoffLinearMap ρ x w =
        (a.inverse.cutoffLinearMap ρ x w.1, a'.inverse.cutoffLinearMap ρ x w.2)) := by
    -- On the union both factors vanish; on its complement the actual boundary splits.
    have zeroMap (J K : FiniteBundle X) (b : CompactSupportTriple J.Fiber K.Fiber)
        (hz : ρ x = 0) : b.cutoffLinearMap ρ x = 0 := by
      unfold CompactSupportTriple.cutoffLinearMap
      split_ifs
      · rfl
      · simp [hz]
    by_cases hx : x ∈ a.control ∪ a'.control
    · have hz := hzero x hx
      constructor
      · intro w
        rw [zeroMap (E.sum E') (F.sum F') (a.sum a') hz,
          zeroMap E F a hz, zeroMap E' F' a' hz]
        rfl
      · intro w
        rw [zeroMap (F.sum F') (E.sum E') (a.sum a').inverse hz,
          zeroMap F E a.inverse hz, zeroMap F' E' a'.inverse hz]
        rfl
    · have ha : x ∉ a.control := fun h ↦ hx (Or.inl h)
      have ha' : x ∉ a'.control := fun h ↦ hx (Or.inr h)
      have hsum (w : E.Fiber x × E'.Fiber x) :
          (a.sum a').boundary.linearEquiv ⟨x, hx⟩ w =
            (a.boundary.linearEquiv ⟨x, ha⟩ w.1,
              a'.boundary.linearEquiv ⟨x, ha'⟩ w.2) := by
        change (RelativeTriple.sum
          (a.enlarge (a.control ∪ a'.control)
            (a.isCompact_control.union a'.isCompact_control) Set.subset_union_left).boundary
          (a'.enlarge (a.control ∪ a'.control)
            (a.isCompact_control.union a'.isCompact_control)
              Set.subset_union_right).boundary).linearEquiv
              ⟨x, hx⟩ w = _
        rw [RelativeTriple.sum_apply, CompactSupportTriple.enlarge_apply,
          CompactSupportTriple.enlarge_apply]
      have hinverse (w : F.Fiber x × F'.Fiber x) :
          ((a.sum a').boundary.linearEquiv ⟨x, hx⟩).symm w =
            ((a.boundary.linearEquiv ⟨x, ha⟩).symm w.1,
              (a'.boundary.linearEquiv ⟨x, ha'⟩).symm w.2) := by
        apply ((a.sum a').boundary.linearEquiv ⟨x, hx⟩).injective
        rw [LinearEquiv.apply_symm_apply, hsum]
        simp only [LinearEquiv.apply_symm_apply]
        exact (Prod.eta w).symm
      have hscontrol : x ∉ (a.sum a').control := hx
      constructor
      · intro w
        unfold CompactSupportTriple.cutoffLinearMap
        rw [dite_eq_right hscontrol, dite_eq_right ha, dite_eq_right ha']
        change ((ρ x : ℝ) : ℂ) • ((a.sum a').boundary.linearEquiv ⟨x, hx⟩ w) = _
        rw [hsum]
        rfl
      · intro w
        dsimp only [CompactSupportTriple.inverse]
        unfold CompactSupportTriple.cutoffLinearMap
        rw [dite_eq_right hscontrol, dite_eq_right ha, dite_eq_right ha']
        change ((ρ x : ℝ) : ℂ) • (((a.sum a').boundary.linearEquiv ⟨x, hx⟩).symm w) = _
        rw [hinverse]
        rfl
  have algebra_left {A₀ A₁ B₀ B₁ C₀ C₁ : Type}
    [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
    [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
    [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (b : B₀ →ₗ[ℂ] B₁) (b' : B₁ →ₗ[ℂ] B₀)
      (e : C₀ →ₗ[ℂ] C₁) (e' : C₁ →ₗ[ℂ] C₀) :
      let U := ((TensorProduct.prodLeft ℂ ℂ A₀ B₀ C₀).prodCongr
        (TensorProduct.prodLeft ℂ ℂ A₁ B₁ C₁)).trans
          (LinearEquiv.prodProdProdComm ℂ (A₀ ⊗[ℂ] C₀) (B₀ ⊗[ℂ] C₀)
            (A₁ ⊗[ℂ] C₁) (B₁ ⊗[ℂ] C₁))
      let V := ((TensorProduct.prodLeft ℂ ℂ A₁ B₁ C₀).prodCongr
        (TensorProduct.prodLeft ℂ ℂ A₀ B₀ C₁)).trans
          (LinearEquiv.prodProdProdComm ℂ (A₁ ⊗[ℂ] C₀) (B₁ ⊗[ℂ] C₀)
            (A₀ ⊗[ℂ] C₁) (B₀ ⊗[ℂ] C₁))
      V.toLinearMap.comp (reciprocalTensorSymbol (d.prodMap b) (d'.prodMap b') e e') =
        ((reciprocalTensorSymbol d d' e e').prodMap
          (reciprocalTensorSymbol b b' e e')).comp U.toLinearMap := by
    dsimp only
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro r s
    all_goals
      rcases r with ⟨r, r'⟩
      simp [reciprocalTensorSymbol]
  have sumLeft (a a' : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) (c : CX (a.sum a')) (d : CY b) :
      let c₀ : CX a := ⟨c.val, c.property.1,
        Set.subset_union_left.trans c.property.2.1, c.property.2.2⟩
      let c₁ : CX a' := ⟨c.val, c.property.1,
        Set.subset_union_right.trans c.property.2.1, c.property.2.2⟩
      (product (a.sum a') b c d).IsIsomorphic
        ((product a b c₀ d).sum (product a' b c₁ d)) := by
    dsimp only
    let c₀ : CX a := ⟨c.val, c.property.1,
      Set.subset_union_left.trans c.property.2.1, c.property.2.2⟩
    let c₁ : CX a' := ⟨c.val, c.property.1,
      Set.subset_union_right.trans c.property.2.1, c.property.2.2⟩
    let p : C(X × Y, X) := ContinuousMap.fst
    let q : C(X × Y, Y) := ContinuousMap.snd
    -- Native tensor distributivity is followed by one equivariant middle-coordinate swap.
    obtain ⟨u₀, hu₀, heU₀⟩ := left_distribution a.1.source a'.1.source b.1.source
      a.2.sourceAction a'.2.sourceAction b.2.sourceAction
    obtain ⟨u₁, hu₁, heU₁⟩ := left_distribution a.1.target a'.1.target b.1.target
      a.2.targetAction a'.2.targetAction b.2.targetAction
    obtain ⟨v₀, hv₀, heV₀⟩ := left_distribution a.1.target a'.1.target b.1.source
      a.2.targetAction a'.2.targetAction b.2.sourceAction
    obtain ⟨v₁, hv₁, heV₁⟩ := left_distribution a.1.source a'.1.source b.1.target
      a.2.sourceAction a'.2.sourceAction b.2.targetAction
    obtain ⟨sU, hsU, heSU⟩ := shuffle
      ((a.1.source.pullback p).tensor (b.1.source.pullback q))
      ((a'.1.source.pullback p).tensor (b.1.source.pullback q))
      ((a.1.target.pullback p).tensor (b.1.target.pullback q))
      ((a'.1.target.pullback p).tensor (b.1.target.pullback q))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a'.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
      ((a'.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
    obtain ⟨sV, hsV, heSV⟩ := shuffle
      ((a.1.target.pullback p).tensor (b.1.source.pullback q))
      ((a'.1.target.pullback p).tensor (b.1.source.pullback q))
      ((a.1.source.pullback p).tensor (b.1.target.pullback q))
      ((a'.1.source.pullback p).tensor (b.1.target.pullback q))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a'.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
      ((a'.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
    let u := (u₀.sum u₁).trans sU
    let v := (v₀.sum v₁).trans sV
    have heU : u.IsEquivariant ((a.sum a').externalProductSourceAction b)
        (((product a b c₀ d).sum (product a' b c₁ d)).2.sourceAction) := by
      intro g z w
      exact (congrArg (sU.linearEquiv (g • z))
        (Prod.ext (heU₀ g z w.1) (heU₁ g z w.2))).trans
          (heSU g z ((u₀.sum u₁).linearEquiv z w))
    have heV : v.IsEquivariant ((a.sum a').externalProductTargetAction b)
        (((product a b c₀ d).sum (product a' b c₁ d)).2.targetAction) := by
      intro g z w
      exact (congrArg (sV.linearEquiv (g • z))
        (Prod.ext (heV₀ g z w.1) (heV₁ g z w.2))).trans
          (heSV g z ((v₀.sum v₁).linearEquiv z w))
    let K : Set (X × Y) := Set.prod c.val.2.2 d.val.2.2
    have hK : IsCompact K := c.property.2.2.2.1.prod d.property.2.2.2.1
    have hleft : (product (a.sum a') b c d).1.datum.control ⊆ K := Set.Subset.refl _
    have hright : ((product a b c₀ d).sum (product a' b c₁ d)).1.datum.control ⊆ K :=
      Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _)
    refine ⟨K, hK, (fun g z ↦ and_congr
      (c.property.2.2.2.2.2.2 g z.1) (d.property.2.2.2.2.2.2 g z.2)),
      hleft, hright, u, v, heU, heV, ?_⟩
    intro z w
    -- The common cutoff vanishes on the entire union, for the forward and inverse maps.
    obtain ⟨hD, hD'⟩ := sumCutoffX a.1.source a.1.target a'.1.source a'.1.target
      a.1.datum a'.1.datum c.val.1
      (fun x hx ↦ c.property.2.2.1 x (c.property.2.1 hx)) z.val.1
    have hR (w : ((product a b c₀ d).sum (product a' b c₁ d)).1.source.Fiber z) :
        ((((product a b c₀ d).sum (product a' b c₁ d)).1.datum.enlarge K
          hK hright).boundary.linearEquiv z) w =
        (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) w.1,
        reciprocalTensorSymbol (a'.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a'.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) w.2) := by
      simp only [EquivariantSupportBundleTriple.sum, SupportBundleTriple.sum,
        SupportBundleTriple.ofBoundary, CompactSupportTriple.sum, CompactSupportTriple.enlarge,
        Iso.restrictTo_apply, RelativeTriple.sum_apply]
      rfl
    -- Identify the native maps with the algebraic distributions using their actual vectors.
    let dU₀ := TensorProduct.prodLeft ℂ ℂ
      (a.1.source.Fiber z.val.1) (a'.1.source.Fiber z.val.1) (b.1.source.Fiber z.val.2)
    let dU₁ := TensorProduct.prodLeft ℂ ℂ
      (a.1.target.Fiber z.val.1) (a'.1.target.Fiber z.val.1) (b.1.target.Fiber z.val.2)
    let dV₀ := TensorProduct.prodLeft ℂ ℂ
      (a.1.target.Fiber z.val.1) (a'.1.target.Fiber z.val.1) (b.1.source.Fiber z.val.2)
    let dV₁ := TensorProduct.prodLeft ℂ ℂ
      (a.1.source.Fiber z.val.1) (a'.1.source.Fiber z.val.1) (b.1.target.Fiber z.val.2)
    let CU := (dU₀.prodCongr dU₁).trans
      (LinearEquiv.prodProdProdComm ℂ
        (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
        (a'.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
        (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
        (a'.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2))
    let CV := (dV₀.prodCongr dV₁).trans
      (LinearEquiv.prodProdProdComm ℂ
        (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
        (a'.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
        (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
        (a'.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2))
    have hU₀ : (u₀.linearEquiv z).toLinearMap = dU₀.toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hu₀ z r s
    have hU₁ : (u₁.linearEquiv z).toLinearMap = dU₁.toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hu₁ z r s
    have hV₀ : (v₀.linearEquiv z).toLinearMap = dV₀.toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hv₀ z r s
    have hV₁ : (v₁.linearEquiv z).toLinearMap = dV₁.toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hv₁ z r s
    have hSU : (sU.linearEquiv z).toLinearMap =
        (LinearEquiv.prodProdProdComm ℂ
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a'.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
          (a'.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)).toLinearMap := by
      apply LinearMap.ext
      intro r
      exact hsU z r
    have hSV : (sV.linearEquiv z).toLinearMap =
        (LinearEquiv.prodProdProdComm ℂ
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a'.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
          (a'.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)).toLinearMap := by
      apply LinearMap.ext
      intro r
      exact hsV z r
    have hUlinear : (u.linearEquiv z).toLinearMap = CU.toLinearMap := by
      change (sU.linearEquiv z).toLinearMap.comp
        ((u₀.linearEquiv z).toLinearMap.prodMap (u₁.linearEquiv z).toLinearMap) = _
      rw [hSU, hU₀, hU₁]
      rfl
    have hVlinear : (v.linearEquiv z).toLinearMap = CV.toLinearMap := by
      change (sV.linearEquiv z).toLinearMap.comp
        ((v₀.linearEquiv z).toLinearMap.prodMap (v₁.linearEquiv z).toLinearMap) = _
      rw [hSV, hV₀, hV₁]
      rfl
    have hDM : (a.sum a').1.datum.cutoffLinearMap c.val.1 z.val.1 =
        (a.1.datum.cutoffLinearMap c.val.1 z.val.1).prodMap
          (a'.1.datum.cutoffLinearMap c.val.1 z.val.1) := LinearMap.ext hD
    have hDM' : (a.sum a').1.datum.inverse.cutoffLinearMap c.val.1 z.val.1 =
        (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1).prodMap
          (a'.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1) := LinearMap.ext hD'
    -- Compare the two linear routes on both tensor summands, retaining the negative block.
    have hm : (v.linearEquiv z).toLinearMap.comp
        (reciprocalTensorSymbol ((a.sum a').1.datum.cutoffLinearMap c.val.1 z.val.1)
          ((a.sum a').1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)) =
        ((reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)).prodMap
        (reciprocalTensorSymbol (a'.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a'.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2))).comp
          (u.linearEquiv z).toLinearMap := by
      rw [hUlinear, hVlinear, hDM, hDM']
      exact algebra_left _ _ _ _ _ _
    exact (congrArg (v.linearEquiv z)
      (boundaryValue (a.sum a') b c d K hK hleft z w)).trans
        ((LinearMap.congr_fun hm w).trans (hR (u.linearEquiv z w)).symm)
  have algebraRight {A₀ A₁ B₀ B₁ C₀ C₁ : Type}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [AddCommGroup C₀] [Module ℂ C₀] [AddCommGroup C₁] [Module ℂ C₁]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (b : B₀ →ₗ[ℂ] B₁) (b' : B₁ →ₗ[ℂ] B₀)
      (e : C₀ →ₗ[ℂ] C₁) (e' : C₁ →ₗ[ℂ] C₀) :
      let U := ((TensorProduct.prodRight ℂ ℂ A₀ B₀ C₀).prodCongr
        (TensorProduct.prodRight ℂ ℂ A₁ B₁ C₁)).trans
          (LinearEquiv.prodProdProdComm ℂ (A₀ ⊗[ℂ] B₀) (A₀ ⊗[ℂ] C₀)
            (A₁ ⊗[ℂ] B₁) (A₁ ⊗[ℂ] C₁))
      let V := ((TensorProduct.prodRight ℂ ℂ A₁ B₀ C₀).prodCongr
        (TensorProduct.prodRight ℂ ℂ A₀ B₁ C₁)).trans
          (LinearEquiv.prodProdProdComm ℂ (A₁ ⊗[ℂ] B₀) (A₁ ⊗[ℂ] C₀)
            (A₀ ⊗[ℂ] B₁) (A₀ ⊗[ℂ] C₁))
      V.toLinearMap.comp (reciprocalTensorSymbol d d' (b.prodMap e) (b'.prodMap e')) =
        ((reciprocalTensorSymbol d d' b b').prodMap
          (reciprocalTensorSymbol d d' e e')).comp U.toLinearMap := by
    dsimp only
    apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro r s
    all_goals
      simp [reciprocalTensorSymbol]
  have sumCutoffY
      (E F E' F' : FiniteBundle Y)
      (a : CompactSupportTriple E.Fiber F.Fiber)
      (a' : CompactSupportTriple E'.Fiber F'.Fiber) (ρ : C(Y, I))
      (hzero : ∀ x ∈ a.control ∪ a'.control, ρ x = 0) (x : Y) :
      (∀ w, (a.sum a').cutoffLinearMap ρ x w =
        (a.cutoffLinearMap ρ x w.1, a'.cutoffLinearMap ρ x w.2)) ∧
      (∀ w, (a.sum a').inverse.cutoffLinearMap ρ x w =
        (a.inverse.cutoffLinearMap ρ x w.1, a'.inverse.cutoffLinearMap ρ x w.2)) := by
    -- On the union both factors vanish; on its complement the actual boundary splits.
    have zeroMap (J K : FiniteBundle Y) (b : CompactSupportTriple J.Fiber K.Fiber)
        (hz : ρ x = 0) : b.cutoffLinearMap ρ x = 0 := by
      unfold CompactSupportTriple.cutoffLinearMap
      split_ifs
      · rfl
      · simp [hz]
    by_cases hx : x ∈ a.control ∪ a'.control
    · have hz := hzero x hx
      constructor
      · intro w
        rw [zeroMap (E.sum E') (F.sum F') (a.sum a') hz,
          zeroMap E F a hz, zeroMap E' F' a' hz]
        rfl
      · intro w
        rw [zeroMap (F.sum F') (E.sum E') (a.sum a').inverse hz,
          zeroMap F E a.inverse hz, zeroMap F' E' a'.inverse hz]
        rfl
    · have ha : x ∉ a.control := fun h ↦ hx (Or.inl h)
      have ha' : x ∉ a'.control := fun h ↦ hx (Or.inr h)
      have hsum (w : E.Fiber x × E'.Fiber x) :
          (a.sum a').boundary.linearEquiv ⟨x, hx⟩ w =
            (a.boundary.linearEquiv ⟨x, ha⟩ w.1,
              a'.boundary.linearEquiv ⟨x, ha'⟩ w.2) := by
        change (RelativeTriple.sum
          (a.enlarge (a.control ∪ a'.control)
            (a.isCompact_control.union a'.isCompact_control) Set.subset_union_left).boundary
          (a'.enlarge (a.control ∪ a'.control)
            (a.isCompact_control.union a'.isCompact_control)
            Set.subset_union_right).boundary).linearEquiv ⟨x, hx⟩ w = _
        rw [RelativeTriple.sum_apply, CompactSupportTriple.enlarge_apply,
          CompactSupportTriple.enlarge_apply]
      have hinverse (w : F.Fiber x × F'.Fiber x) :
          ((a.sum a').boundary.linearEquiv ⟨x, hx⟩).symm w =
            ((a.boundary.linearEquiv ⟨x, ha⟩).symm w.1,
              (a'.boundary.linearEquiv ⟨x, ha'⟩).symm w.2) := by
        apply ((a.sum a').boundary.linearEquiv ⟨x, hx⟩).injective
        rw [LinearEquiv.apply_symm_apply, hsum]
        simp only [LinearEquiv.apply_symm_apply]
        exact (Prod.eta w).symm
      have hscontrol : x ∉ (a.sum a').control := hx
      constructor
      · intro w
        unfold CompactSupportTriple.cutoffLinearMap
        rw [dite_eq_right hscontrol, dite_eq_right ha, dite_eq_right ha']
        change ((ρ x : ℝ) : ℂ) • ((a.sum a').boundary.linearEquiv ⟨x, hx⟩ w) = _
        rw [hsum]
        rfl
      · intro w
        dsimp only [CompactSupportTriple.inverse]
        unfold CompactSupportTriple.cutoffLinearMap
        rw [dite_eq_right hscontrol, dite_eq_right ha, dite_eq_right ha']
        change ((ρ x : ℝ) : ℂ) • (((a.sum a').boundary.linearEquiv ⟨x, hx⟩).symm w) = _
        rw [hinverse]
        rfl
  have sumRight (a : EquivariantSupportBundleTriple G X)
      (b b' : EquivariantSupportBundleTriple G Y) (c : CX a) (d : CY (b.sum b')) :
      let d₀ : CY b := ⟨d.val, d.property.1,
        Set.subset_union_left.trans d.property.2.1, d.property.2.2⟩
      let d₁ : CY b' := ⟨d.val, d.property.1,
        Set.subset_union_right.trans d.property.2.1, d.property.2.2⟩
      (product a (b.sum b') c d).IsIsomorphic
        ((product a b c d₀).sum (product a b' c d₁)) := by
    dsimp only
    let d₀ : CY b := ⟨d.val, d.property.1,
      Set.subset_union_left.trans d.property.2.1, d.property.2.2⟩
    let d₁ : CY b' := ⟨d.val, d.property.1,
      Set.subset_union_right.trans d.property.2.1, d.property.2.2⟩
    let p : C(X × Y, X) := ContinuousMap.fst
    let q : C(X × Y, Y) := ContinuousMap.snd
    -- Distribute the native Y sums, then put the same two even and odd terms together.
    obtain ⟨u₀, hu₀, heU₀⟩ := right_distribution a.1.source b.1.source b'.1.source
      a.2.sourceAction b.2.sourceAction b'.2.sourceAction
    obtain ⟨u₁, hu₁, heU₁⟩ := right_distribution a.1.target b.1.target b'.1.target
      a.2.targetAction b.2.targetAction b'.2.targetAction
    obtain ⟨v₀, hv₀, heV₀⟩ := right_distribution a.1.target b.1.source b'.1.source
      a.2.targetAction b.2.sourceAction b'.2.sourceAction
    obtain ⟨v₁, hv₁, heV₁⟩ := right_distribution a.1.source b.1.target b'.1.target
      a.2.sourceAction b.2.targetAction b'.2.targetAction
    obtain ⟨sU, hsU, heSU⟩ := shuffle
      ((a.1.source.pullback p).tensor (b.1.source.pullback q))
      ((a.1.source.pullback p).tensor (b'.1.source.pullback q))
      ((a.1.target.pullback p).tensor (b.1.target.pullback q))
      ((a.1.target.pullback p).tensor (b'.1.target.pullback q))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b'.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b'.2.targetAction.pullback q (fun _ _ ↦ rfl)))
    obtain ⟨sV, hsV, heSV⟩ := shuffle
      ((a.1.target.pullback p).tensor (b.1.source.pullback q))
      ((a.1.target.pullback p).tensor (b'.1.source.pullback q))
      ((a.1.source.pullback p).tensor (b.1.target.pullback q))
      ((a.1.source.pullback p).tensor (b'.1.target.pullback q))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b'.2.sourceAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback q (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback p (fun _ _ ↦ rfl)).tensor
        (b'.2.targetAction.pullback q (fun _ _ ↦ rfl)))
    let u := (u₀.sum u₁).trans sU
    let v := (v₀.sum v₁).trans sV
    have heU : u.IsEquivariant (a.externalProductSourceAction (b.sum b'))
        (((product a b c d₀).sum (product a b' c d₁)).2.sourceAction) := by
      intro g z w
      exact (congrArg (sU.linearEquiv (g • z))
        (Prod.ext (heU₀ g z w.1) (heU₁ g z w.2))).trans
          (heSU g z ((u₀.sum u₁).linearEquiv z w))
    have heV : v.IsEquivariant (a.externalProductTargetAction (b.sum b'))
        (((product a b c d₀).sum (product a b' c d₁)).2.targetAction) := by
      intro g z w
      exact (congrArg (sV.linearEquiv (g • z))
        (Prod.ext (heV₀ g z w.1) (heV₁ g z w.2))).trans
          (heSV g z ((v₀.sum v₁).linearEquiv z w))
    have hU (z : X × Y) (w : (a.1.externalProductSource (b.sum b').1).Fiber z) :
        u.linearEquiv z w =
          (((u₀.linearEquiv z w.1).1, (u₁.linearEquiv z w.2).1),
            ((u₀.linearEquiv z w.1).2, (u₁.linearEquiv z w.2).2)) :=
      hsU z ((u₀.sum u₁).linearEquiv z w)
    have hV (z : X × Y) (w : (a.1.externalProductTarget (b.sum b').1).Fiber z) :
        v.linearEquiv z w =
          (((v₀.linearEquiv z w.1).1, (v₁.linearEquiv z w.2).1),
            ((v₀.linearEquiv z w.1).2, (v₁.linearEquiv z w.2).2)) :=
      hsV z ((v₀.sum v₁).linearEquiv z w)
    let K : Set (X × Y) := Set.prod c.val.2.2 d.val.2.2
    have hK : IsCompact K := c.property.2.2.2.1.prod d.property.2.2.2.1
    have hleft : (product a (b.sum b') c d).1.datum.control ⊆ K := Set.Subset.refl _
    have hright : ((product a b c d₀).sum (product a b' c d₁)).1.datum.control ⊆ K :=
      Set.union_subset (Set.Subset.refl _) (Set.Subset.refl _)
    refine ⟨K, hK, (fun g z ↦ and_congr
      (c.property.2.2.2.2.2.2 g z.1) (d.property.2.2.2.2.2.2 g z.2)),
      hleft, hright, u, v, heU, heV, ?_⟩
    intro z w
    -- The shared Y cutoff splits both the forward and prescribed inverse boundaries.
    obtain ⟨hD, hD'⟩ := sumCutoffY b.1.source b.1.target b'.1.source b'.1.target
      b.1.datum b'.1.datum d.val.1
      (fun y hy ↦ d.property.2.2.1 y (d.property.2.1 hy)) z.val.2
    have hR (w : ((product a b c d₀).sum (product a b' c d₁)).1.source.Fiber z) :
        ((((product a b c d₀).sum (product a b' c d₁)).1.datum.enlarge
          K hK hright).boundary.linearEquiv z) w =
        (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) w.1,
        reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b'.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b'.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) w.2) := by
      simp only [EquivariantSupportBundleTriple.sum, SupportBundleTriple.sum,
        SupportBundleTriple.ofBoundary, CompactSupportTriple.sum, CompactSupportTriple.enlarge,
        Iso.restrictTo_apply, RelativeTriple.sum_apply]
      rfl
    -- Check the two tensor routes directly, retaining the original negative block.
    have hu₀linear : (u₀.linearEquiv z).toLinearMap =
        (TensorProduct.prodRight ℂ ℂ (a.1.source.Fiber z.val.1)
          (b.1.source.Fiber z.val.2) (b'.1.source.Fiber z.val.2)).toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hu₀ z r s
    have hu₁linear : (u₁.linearEquiv z).toLinearMap =
        (TensorProduct.prodRight ℂ ℂ (a.1.target.Fiber z.val.1)
          (b.1.target.Fiber z.val.2) (b'.1.target.Fiber z.val.2)).toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hu₁ z r s
    have hv₀linear : (v₀.linearEquiv z).toLinearMap =
        (TensorProduct.prodRight ℂ ℂ (a.1.target.Fiber z.val.1)
          (b.1.source.Fiber z.val.2) (b'.1.source.Fiber z.val.2)).toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hv₀ z r s
    have hv₁linear : (v₁.linearEquiv z).toLinearMap =
        (TensorProduct.prodRight ℂ ℂ (a.1.source.Fiber z.val.1)
          (b.1.target.Fiber z.val.2) (b'.1.target.Fiber z.val.2)).toLinearMap := by
      apply TensorProduct.ext'
      intro r s
      exact hv₁ z r s
    have hSUlinear : (sU.linearEquiv z).toLinearMap =
        (LinearEquiv.prodProdProdComm ℂ
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b'.1.source.Fiber z.val.2)
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b'.1.target.Fiber z.val.2)).toLinearMap := by
      apply LinearMap.ext
      intro r
      exact hsU z r
    have hSVlinear : (sV.linearEquiv z).toLinearMap =
        (LinearEquiv.prodProdProdComm ℂ
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
          (a.1.target.Fiber z.val.1 ⊗[ℂ] b'.1.source.Fiber z.val.2)
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
          (a.1.source.Fiber z.val.1 ⊗[ℂ] b'.1.target.Fiber z.val.2)).toLinearMap := by
      apply LinearMap.ext
      intro r
      exact hsV z r
    let U := ((TensorProduct.prodRight ℂ ℂ (a.1.source.Fiber z.val.1)
      (b.1.source.Fiber z.val.2) (b'.1.source.Fiber z.val.2)).prodCongr
        (TensorProduct.prodRight ℂ ℂ (a.1.target.Fiber z.val.1)
          (b.1.target.Fiber z.val.2) (b'.1.target.Fiber z.val.2))).trans
            (LinearEquiv.prodProdProdComm ℂ
              (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
              (a.1.source.Fiber z.val.1 ⊗[ℂ] b'.1.source.Fiber z.val.2)
              (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
              (a.1.target.Fiber z.val.1 ⊗[ℂ] b'.1.target.Fiber z.val.2))
    let V := ((TensorProduct.prodRight ℂ ℂ (a.1.target.Fiber z.val.1)
      (b.1.source.Fiber z.val.2) (b'.1.source.Fiber z.val.2)).prodCongr
        (TensorProduct.prodRight ℂ ℂ (a.1.source.Fiber z.val.1)
          (b.1.target.Fiber z.val.2) (b'.1.target.Fiber z.val.2))).trans
            (LinearEquiv.prodProdProdComm ℂ
              (a.1.target.Fiber z.val.1 ⊗[ℂ] b.1.source.Fiber z.val.2)
              (a.1.target.Fiber z.val.1 ⊗[ℂ] b'.1.source.Fiber z.val.2)
              (a.1.source.Fiber z.val.1 ⊗[ℂ] b.1.target.Fiber z.val.2)
              (a.1.source.Fiber z.val.1 ⊗[ℂ] b'.1.target.Fiber z.val.2))
    have hUlinear : (u.linearEquiv z).toLinearMap = U.toLinearMap := by
      change (sU.linearEquiv z).toLinearMap.comp
        ((u₀.linearEquiv z).toLinearMap.prodMap (u₁.linearEquiv z).toLinearMap) = _
      rw [hSUlinear, hu₀linear, hu₁linear]
      rfl
    have hVlinear : (v.linearEquiv z).toLinearMap = V.toLinearMap := by
      change (sV.linearEquiv z).toLinearMap.comp
        ((v₀.linearEquiv z).toLinearMap.prodMap (v₁.linearEquiv z).toLinearMap) = _
      rw [hSVlinear, hv₀linear, hv₁linear]
      rfl
    have hDmap : (b.sum b').1.datum.cutoffLinearMap d.val.1 z.val.2 =
        (b.1.datum.cutoffLinearMap d.val.1 z.val.2).prodMap
          (b'.1.datum.cutoffLinearMap d.val.1 z.val.2) := by
      apply LinearMap.ext
      exact hD
    have hDmap' : (b.sum b').1.datum.inverse.cutoffLinearMap d.val.1 z.val.2 =
        (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2).prodMap
          (b'.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2) := by
      apply LinearMap.ext
      exact hD'
    have hm : (v.linearEquiv z).toLinearMap.comp
        (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          ((b.sum b').1.datum.cutoffLinearMap d.val.1 z.val.2)
          ((b.sum b').1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)) =
        ((reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)).prodMap
        (reciprocalTensorSymbol (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
          (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
          (b'.1.datum.cutoffLinearMap d.val.1 z.val.2)
          (b'.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2))).comp
          (u.linearEquiv z).toLinearMap := by
      rw [hVlinear, hUlinear, hDmap, hDmap']
      exact algebraRight (a.1.datum.cutoffLinearMap c.val.1 z.val.1)
        (a.1.datum.inverse.cutoffLinearMap c.val.1 z.val.1)
        (b.1.datum.cutoffLinearMap d.val.1 z.val.2)
        (b.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)
        (b'.1.datum.cutoffLinearMap d.val.1 z.val.2)
        (b'.1.datum.inverse.cutoffLinearMap d.val.1 z.val.2)
    exact (congrArg (v.linearEquiv z)
      (boundaryValue a (b.sum b') c d K hK hleft z w)).trans
        ((LinearMap.congr_fun hm w).trans (hR (u.linearEquiv z w)).symm)
  -- Apply the original direct-sum relation to the same common-cutoff comparisons.
  have addLeft (a a' : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) :
      value (a.sum a') b = value a b + value a' b := by
    let c := Classical.choice (nonemptyX (a.sum a'))
    let d := Classical.choice (nonemptyY b)
    let c₀ : CX a := ⟨c.val, c.property.1,
      Set.subset_union_left.trans c.property.2.1, c.property.2.2⟩
    let c₁ : CX a' := ⟨c.val, c.property.1,
      Set.subset_union_right.trans c.property.2.1, c.property.2.2⟩
    calc
      value (a.sum a') b = (product (a.sum a') b c d).kZeroClass :=
        value_eq (a.sum a') b c d
      _ = ((product a b c₀ d).sum (product a' b c₁ d)).kZeroClass :=
        equivariantSupportTripleKZero_generator_relations.1 _ _ (sumLeft a a' b c d)
      _ = (product a b c₀ d).kZeroClass + (product a' b c₁ d).kZeroClass :=
        equivariantSupportTripleKZero_generator_relations.2.1 _ _
      _ = value a b + value a' b :=
        congrArg₂ (· + ·) (value_eq a b c₀ d).symm (value_eq a' b c₁ d).symm
  have addRight (b b' : EquivariantSupportBundleTriple G Y)
      (a : EquivariantSupportBundleTriple G X) :
      value a (b.sum b') = value a b + value a b' := by
    let c := Classical.choice (nonemptyX a)
    let d := Classical.choice (nonemptyY (b.sum b'))
    let d₀ : CY b := ⟨d.val, d.property.1,
      Set.subset_union_left.trans d.property.2.1, d.property.2.2⟩
    let d₁ : CY b' := ⟨d.val, d.property.1,
      Set.subset_union_right.trans d.property.2.1, d.property.2.2⟩
    calc
      value a (b.sum b') = (product a (b.sum b') c d).kZeroClass :=
        value_eq a (b.sum b') c d
      _ = ((product a b c d₀).sum (product a b' c d₁)).kZeroClass :=
        equivariantSupportTripleKZero_generator_relations.1 _ _ (sumRight a b b' c d)
      _ = (product a b c d₀).kZeroClass + (product a b' c d₁).kZeroClass :=
        equivariantSupportTripleKZero_generator_relations.2.1 _ _
      _ = value a b + value a b' :=
        congrArg₂ (· + ·) (value_eq a b c d₀).symm (value_eq a b' c d₁).symm
  have homExt (f g : EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ b : EquivariantSupportBundleTriple G Y, f b.kZeroClass = g b.kZeroClass) :
      f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  -- First descend the original representative values in the second variable.
  let f (a : EquivariantSupportBundleTriple G X) :
      EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y) :=
    (equivariantSupportTripleKZero_universal_property (value a)
      (fun b b' h ↦ isoRight b b' h a) (fun b b' ↦ addRight b b' a)
      (fun F ρF ↦ zeroRight F ρF a)).choose
  have hf (a : EquivariantSupportBundleTriple G X)
      (b : EquivariantSupportBundleTriple G Y) : f a b.kZeroClass = value a b :=
    (equivariantSupportTripleKZero_universal_property (value a)
      (fun b b' h ↦ isoRight b b' h a) (fun b b' ↦ addRight b b' a)
      (fun F ρF ↦ zeroRight F ρF a)).choose_spec.1 b
  have fIso (a a' : EquivariantSupportBundleTriple G X) (h : a.IsIsomorphic a') :
      f a = f a' := by
    apply homExt
    intro b
    exact (hf a b).trans ((isoLeft a a' h b).trans (hf a' b).symm)
  have fAdd (a a' : EquivariantSupportBundleTriple G X) : f (a.sum a') = f a + f a' := by
    apply homExt
    intro b
    exact (hf (a.sum a') b).trans
      ((addLeft a a' b).trans (congrArg₂ (· + ·) (hf a b) (hf a' b)).symm)
  have fZero (E : FiniteBundle X) (ρE : EquivariantStructure G E.Fiber) :
      f (EquivariantSupportBundleTriple.identity E ρE) = 0 := by
    apply homExt
    intro b
    exact (hf _ b).trans (zeroLeft E ρE b)
  -- Then descend the first presentation with additive homomorphisms as values.
  obtain ⟨μ, hμ, hμunique⟩ :=
    equivariantSupportTripleKZero_universal_property f fIso fAdd fZero
  refine ⟨μ, ?_, ?_⟩
  · intro a b ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    rw [hμ]
    exact (hf a b).trans (value_eq a b
      ⟨(ρ, U, L), hU, ha, hρzero, hL, hρone, hρinv, hLinv⟩
      ⟨(τ, V, M), hV, hb, hτzero, hM, hτone, hτinv, hMinv⟩)
  · intro ν hν
    apply hμunique
    intro a
    apply homExt
    intro b
    let c := Classical.choice (nonemptyX a)
    let d := Classical.choice (nonemptyY b)
    have hνvalue : ν a.kZeroClass b.kZeroClass = value a b := by
      exact hν a b
        c.val.1 c.val.2.1 c.property.1 c.property.2.1 c.property.2.2.1
        c.val.2.2 c.property.2.2.2.1 c.property.2.2.2.2.1
        d.val.1 d.val.2.1 d.property.1 d.property.2.1 d.property.2.2.1
        d.val.2.2 d.property.2.2.2.1 d.property.2.2.2.2.1
        c.property.2.2.2.2.2.1 c.property.2.2.2.2.2.2
        d.property.2.2.2.2.2.1 d.property.2.2.2.2.2.2
    exact hνvalue.trans (hf a b).symm

/-- The specified external product on the existing equivariant support groups. -/
def equivariantSupportKZeroExternalProduct :
    EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y) :=
  Classical.choose (existsUnique_equivariantSupportKZeroExternalProduct
    (G := G) (X := X) (Y := Y)).exists

/-- Every original pair of triples evaluates to its actual invariant-cutoff tensor boundary. -/
theorem equivariantSupportKZeroExternalProduct_class
    (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
    (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (ha : a.1.datum.control ⊆ U)
    (hρzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
    (hρone : ∀ x ∉ L, ρ x = 1)
    (τ : C(Y, I)) (V : Set Y) (hV : IsOpen V) (hb : b.1.datum.control ⊆ V)
    (hτzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
    (hτone : ∀ y ∉ M, τ y = 1)
    (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
    (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
    (hτinv : ∀ (g : G) (y : Y), τ (g • y) = τ y)
    (hMinv : ∀ (g : G) (y : Y), g • y ∈ M ↔ y ∈ M) :
    equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass =
      (supportedEquivariantExternalProductTriple a b
        ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
        hρinv hLinv hτinv hMinv).kZeroClass := by
  /- Extract the generator equation from the same unique biadditive witness
  used to define the operation. Its universal quantifiers retain these exact
  two cutoffs, enlarged controls, actions and boundary, without a second choice. -/
  exact (Classical.choose_spec (existsUnique_equivariantSupportKZeroExternalProduct
    (G := G) (X := X) (Y := Y)).exists) a b
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv

/-- Ordinary forgetting recovers the previously specified compact-support external product. -/
theorem equivariantSupportKZeroExternalProduct_forget
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Y) :
    supportTripleKZeroToCompactSupport
      (equivariantSupportTripleKZeroForget (equivariantSupportKZeroExternalProduct a b)) =
        compactSupportKZeroExternalProduct
          (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget a))
          (supportTripleKZeroToCompactSupport (equivariantSupportTripleKZeroForget b)) := by
  /- Stage 1: choose invariant cutoffs for actual input triples. Forgetting their
  product retains exactly the ordinary supportedExternalProductTriple, including
  its even/odd order and L times M control. Apply the ordinary representative
  comparison to the existing compactification product; metrics needed in that
  comparison are only on compact windows, not on either original whole space.
  Stage 2: the original forgetful and support-comparison homomorphisms have the
  stated generator equations. Actual triple representatives reduce arbitrary
  support classes to those equations. Nothing asserts injectivity or
  surjectivity of forgetting. -/
  -- The original equivariant presentation supplies actual representatives for both classes.
  obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective b
  obtain ⟨U, hU, ha, _, L, hL, _, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
  obtain ⟨V, hV, hb, _, M, hM, _, hMinv, τ, hτinv, hτzero, hτone⟩ :=
    exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
  rw [equivariantSupportKZeroExternalProduct_class a b
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv]
  simp only [equivariantSupportTripleKZeroForget_apply,
    supportTripleKZeroToCompactSupport_apply]
  -- Forgetting keeps the literal ordinary reciprocal block and its specified compact control.
  exact supportedExternalProductTriple_compactSupportClass a.1 b.1
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 10000000 in
-- Retain the original tensor topologies through the three additive presentation descents.
/-- A full representation coefficient in the first factor acts on the same product class. -/
theorem equivariantSupportKZeroExternalProduct_smul_left
    (r : RepresentationGrothendieckGroup G)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Y) :
    equivariantSupportKZeroExternalProduct (r • a) b =
      r • equivariantSupportKZeroExternalProduct a b := by
  /- Stage 1: on actual generators, tensor the first triple by the original
  diagonal representation bundle. Use the same cutoff as before; identity
  tensor boundary and its inverse give identity tensor each old cutoff map.
  First compare the pulled diagonal representation bundle with the diagonal
  representation bundle on the product base by the vector-preserving map and
  its inverse, continuous in their original total topologies. Then the actual
  tensor associator identifies both even and odd output bundles
  with the representation tensor the original output. It intertwines all
  four blocks, their signs and the original group action on the same L times M.
  Stage 2: the two generator characterizations identify these classes. Extend
  by additivity in the representation and both support classes. Retain the
  full representation; an integer dimension cannot replace this coefficient. -/
  classical
  let μ : EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y) :=
    equivariantSupportKZeroExternalProduct (G := G) (X := X) (Y := Y)
  have hμ := equivariantSupportKZeroExternalProduct_class (G := G) (X := X) (Y := Y)
  change μ (r • a) b = r • μ a b
  have hclass
      (θ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
      (ρ : C(X, unitInterval)) (U : Set X) (hU : IsOpen U) (ha : a.1.datum.control ⊆ U)
      (hρzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
      (hρone : ∀ x ∉ L, ρ x = 1)
      (τ : C(Y, unitInterval)) (V : Set Y) (hV : IsOpen V) (hb : b.1.datum.control ⊆ V)
      (hτzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
      (hτone : ∀ y ∉ M, τ y = 1)
      (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
      (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
      (hτinv : ∀ (g : G) (y : Y), τ (g • y) = τ y)
      (hMinv : ∀ (g : G) (y : Y), g • y ∈ M ↔ y ∈ M) :
      (supportedEquivariantExternalProductTriple (a.tensorRepresentation θ) b
        ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
        hρinv hLinv hτinv hMinv).kZeroClass =
        ((supportedEquivariantExternalProductTriple a b
          ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
          hρinv hLinv hτinv hMinv).tensorRepresentation θ).kZeroClass := by
    classical
    have corners (ρ : FiniteContinuousRepresentation G)
        (J : FiniteBundle X) (K : FiniteBundle Y)
        (α : EquivariantStructure G J.Fiber) (β : EquivariantStructure G K.Fiber) :
        (∃ e : Iso ((((FiniteBundle.trivial X ρ.dimension).tensor J).pullback
              (ContinuousMap.fst : C(X × Y, X))).tensor
                (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).Fiber
            ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor
              ((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd))).Fiber,
          (∀ (z : X × Y) (u : Fin ρ.dimension → ℂ) (v : J.Fiber z.1) (w : K.Fiber z.2),
            e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
          e.IsEquivariant
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).pullback
              ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl))))) ∧
        ∃ e : Iso ((J.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
              (((FiniteBundle.trivial Y ρ.dimension).tensor K).pullback
                (ContinuousMap.snd : C(X × Y, Y)))).Fiber
            ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor
              ((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd))).Fiber,
          (∀ (z : X × Y) (v : J.Fiber z.1) (u : Fin ρ.dimension → ℂ) (w : K.Fiber z.2),
            e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
          e.IsEquivariant
            ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor β).pullback
                ContinuousMap.snd (fun _ _ ↦ rfl)))
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))) := by
      have comparisons (n : ℕ) (E F : FiniteBundle (X × Y)) :
        (∃ e : Iso (((FiniteBundle.trivial (X × Y) n).tensor E).tensor F).Fiber
            ((FiniteBundle.trivial (X × Y) n).tensor (E.tensor F)).Fiber,
          ∀ (x : (X × Y)) (u : Fin n → ℂ) (v : E.Fiber x) (w : F.Fiber x),
            e.linearEquiv x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
        ∃ e : Iso (E.tensor ((FiniteBundle.trivial (X × Y) n).tensor F)).Fiber
            ((FiniteBundle.trivial (X × Y) n).tensor (E.tensor F)).Fiber,
          ∀ (x : (X × Y)) (v : E.Fiber x) (u : Fin n → ℂ) (w : F.Fiber x),
            e.linearEquiv x (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
        classical
        -- Fixed finite coefficients reduce continuity to actual tensor generators.
        have hcoeff (n : ℕ) (E F : FiniteBundle (X × Y))
            (L : ∀ x, (Fin n → ℂ) ⊗[ℂ] E.Fiber x →ₗ[ℂ] F.Fiber x)
            (hL : ∀ i : Fin n, Continuous (fun z : TotalSpace Unit E.Fiber ↦
              (⟨z.proj, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)⟩ : TotalSpace Unit F.Fiber))) :
            Continuous (fun z : TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor E).Fiber ↦
              (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Unit F.Fiber)) := by
          classical
          -- Test each actual finite-sum generator of the original tensor topology.
          apply continuous_iSup_dom.mpr
          intro m
          apply continuous_coinduced_dom.mpr
          let D := TotalSpace Unit (fun x ↦ (Fin m → Fin n → ℂ) × (Fin m → E.Fiber x))
          let : TopologicalSpace D := TopologicalSpace.induced
            (fun z : D ↦ (z.proj,
              (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) inferInstance
          have hc : Continuous (fun z : D ↦ (z.proj,
              (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) := continuous_induced_dom
          let b : C(D, (X × Y)) := ⟨fun z ↦ z.proj, hc.fst⟩
          have ht : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber ↦
              (z.proj, z.snd)) := continuous_induced_dom
          -- The pullback section module handles finite sums on the generating domain.
          let slice (j : Fin m) (i : Fin n) : continuousSections ((b : D → (X × Y)) *ᵖ F.Fiber) :=
            ⟨fun z ↦ L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j), by
              change Continuous (fun z : D ↦
                (⟨z, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)⟩ :
                  TotalSpace Unit ((b : D → (X × Y)) *ᵖ F.Fiber)))
              rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber b).continuous_iff]
              exact continuous_id.prodMk ((hL i).comp ((continuous_apply j).comp hc.snd.snd))⟩
          let c (j : Fin m) (i : Fin n) : C(D, ℂ) :=
            ⟨fun z ↦ z.snd.1 j i, (continuous_apply i).comp
              (ht.snd.comp ((continuous_apply j).comp hc.snd.fst))⟩
          let sectionSum : continuousSections ((b : D → (X × Y)) *ᵖ F.Fiber) :=
            ∑ j : Fin m, ∑ i : Fin n, c j i • slice j i
          have hsum := (Pullback.continuous_lift Unit F.Fiber b).comp sectionSum.property
          apply hsum.congr
          intro z
          change (⟨z.proj, sectionSum.val z⟩ : TotalSpace Unit F.Fiber) =
            ⟨z.proj, L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)⟩
          apply congrArg (fun w : F.Fiber z.proj ↦ (⟨z.proj, w⟩ : TotalSpace Unit F.Fiber))
          simp only [sectionSum, Submodule.coe_sum, Finset.sum_apply,
            SetLike.val_smul, Pi.smul_apply]
          change (∑ j : Fin m, ∑ i : Fin n,
            z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
              L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)
          -- Standard finite coordinates reconstruct every coefficient, including rank zero.
          have hcoord (u : Fin n → ℂ) : ∑ i : Fin n, u i • Pi.single i 1 = u := by
            ext i
            simp [Pi.single_apply]
          have hpure (j : Fin m) : ∑ i : Fin n,
              z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j) =
                z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j := by
            simpa only [TensorProduct.sum_tmul, TensorProduct.smul_tmul'] using
              congrArg (fun u ↦ u ⊗ₜ[ℂ] z.snd.2 j) (hcoord (z.snd.1 j))
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact (by rw [map_sum]; simp only [map_smul] :
            (∑ i : Fin n, z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
              L z.proj (∑ i : Fin n, z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j))).trans
                (congrArg (L z.proj) (hpure j))
        have hpure (n : ℕ) (J : FiniteBundle (X × Y)) (u : Fin n → ℂ) :
            Continuous (fun z : TotalSpace Unit J.Fiber ↦
              (⟨z.proj, u ⊗ₜ[ℂ] z.snd⟩ :
                TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber)) := by
          let D := TotalSpace Unit (fun x ↦ (Fin 1 → Fin n → ℂ) × (Fin 1 → J.Fiber x))
          let : TopologicalSpace D := TopologicalSpace.induced
            (fun z : D ↦ (z.proj,
              (fun i ↦ (⟨z.proj, z.snd.1 i⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
          have hg : Continuous (fun z : D ↦
              (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber)) :=
            continuous_iSup_rng (i := 1) continuous_coinduced_rng
          let f (z : TotalSpace Unit J.Fiber) : D := ⟨z.proj, fun _ ↦ u, fun _ ↦ z.snd⟩
          have hf : Continuous f := by
            apply continuous_induced_rng.mpr
            refine (continuous_proj (E := J.Fiber)).prodMk
              ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
            intro _
            exact continuous_induced_rng.mpr
              ((continuous_proj (E := J.Fiber)).prodMk continuous_const)
          apply (hg.comp hf).congr
          intro z
          simp only [Function.comp_apply, f, Fin.sum_univ_one]
        -- The canonical tensor symmetry is continuous on every actual finite-sum generator.
        have commCompare (J K : FiniteBundle (X × Y)) :
            ∃ e : Iso (J.tensor K).Fiber (K.tensor J).Fiber,
              ∀ (x : (X × Y)) (v : J.Fiber x) (w : K.Fiber x),
                e.linearEquiv x (v ⊗ₜ[ℂ] w) = w ⊗ₜ[ℂ] v := by
          let c (x : (X × Y)) := TensorProduct.comm ℂ (J.Fiber x) (K.Fiber x)
          let f : Hom (J.tensor K).Fiber (K.tensor J).Fiber :=
            { linearMap x := (c x).toLinearMap
              continuous_total := by
                apply continuous_iSup_dom.mpr
                intro m
                apply continuous_coinduced_dom.mpr
                let D := TotalSpace Unit (fun x ↦ (Fin m → J.Fiber x) × (Fin m → K.Fiber x))
                let D' := TotalSpace Unit (fun x ↦ (Fin m → K.Fiber x) × (Fin m → J.Fiber x))
                let : TopologicalSpace D := TopologicalSpace.induced
                  (fun z : D ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit J.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit K.Fiber)))) inferInstance
                let : TopologicalSpace D' := TopologicalSpace.induced
                  (fun z : D' ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit K.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
                let swapTuple (z : D) : D' := ⟨z.proj, z.snd.2, z.snd.1⟩
                have hc : Continuous (fun z : D ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit J.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit K.Fiber)))) :=
                  continuous_induced_dom
                have hswap : Continuous swapTuple := by
                  apply continuous_induced_rng.mpr
                  exact hc.fst.prodMk (hc.snd.snd.prodMk hc.snd.fst)
                have hg : Continuous (fun z : D' ↦
                    (⟨z.proj, ∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                      TotalSpace Unit (K.tensor J).Fiber)) :=
                  continuous_iSup_rng (i := m) continuous_coinduced_rng
                apply (hg.comp hswap).congr
                intro z
                change (⟨z.proj, ∑ i, z.snd.2 i ⊗ₜ[ℂ] z.snd.1 i⟩ :
                  TotalSpace Unit (K.tensor J).Fiber) =
                    ⟨z.proj, c z.proj (∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩
                apply congrArg (fun t : (K.tensor J).Fiber z.proj ↦
                  (⟨z.proj, t⟩ : TotalSpace Unit (K.tensor J).Fiber))
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro i _
                exact (TensorProduct.comm_tmul ℂ (J.Fiber z.proj) (K.Fiber z.proj) _ _).symm }
          let e := f.toIso (fun x ↦ (c x).bijective)
          refine ⟨e, ?_⟩
          intro x v w
          change c x (v ⊗ₜ[ℂ] w) = w ⊗ₜ[ℂ] v
          exact TensorProduct.comm_tmul ℂ _ _ v w
        -- The inverse associator has a trivial first factor, so coefficient slices suffice.
        have assocCompare (n : ℕ) (J K : FiniteBundle (X × Y)) :
            ∃ e : Iso (((FiniteBundle.trivial (X × Y) n).tensor J).tensor K).Fiber
                ((FiniteBundle.trivial (X × Y) n).tensor (J.tensor K)).Fiber,
              ∀ (x : (X × Y)) (u : Fin n → ℂ) (v : J.Fiber x) (w : K.Fiber x),
                e.linearEquiv x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          let A := (FiniteBundle.trivial (X × Y) n).tensor (J.tensor K)
          let B := ((FiniteBundle.trivial (X × Y) n).tensor J).tensor K
          let c (x : (X × Y)) := (TensorProduct.assoc ℂ (Fin n → ℂ) (J.Fiber x) (K.Fiber x)).symm
          let f : Hom A.Fiber B.Fiber :=
            { linearMap x := (c x).toLinearMap
              continuous_total := by
                apply hcoeff n (J.tensor K) B
                  (fun x ↦ (c x).toLinearMap)
                intro i
                let j : Hom J.Fiber ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber :=
                  { linearMap x := TensorProduct.mk ℂ (Fin n → ℂ) (J.Fiber x) (Pi.single i 1)
                    continuous_total := hpure n J (Pi.single i 1) }
                have hj := (j.tensor (Hom.id K.Fiber)).continuous_total
                apply hj.congr
                intro z
                apply congrArg (fun t : B.Fiber z.proj ↦ (⟨z.proj, t⟩ : TotalSpace Unit B.Fiber))
                change TensorProduct.map (j.linearMap z.proj) LinearMap.id z.snd =
                  c z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)
                induction z.snd using TensorProduct.inductionOn with
                | tmul v w =>
                  simp only [j, c, TensorProduct.map_tmul, TensorProduct.mk_apply,
                    LinearMap.id_apply, TensorProduct.assoc_symm_tmul]
                | add s t hs ht =>
                  simp only [map_add, TensorProduct.tmul_add, hs, ht] }
          let d := f.toIso (fun x ↦ (c x).bijective)
          refine ⟨d.symm, ?_⟩
          intro x u v w
          apply (d.linearEquiv x).injective
          change d.linearEquiv x ((d.linearEquiv x).symm ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w)) =
            c x (u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w))
          rw [LinearEquiv.apply_symm_apply]
          exact (TensorProduct.assoc_symm_tmul u v w).symm
        constructor
        · exact assocCompare n E F
        · obtain ⟨s, hs⟩ := commCompare E ((FiniteBundle.trivial (X × Y) n).tensor F)
          obtain ⟨a, ha⟩ := assocCompare n F E
          obtain ⟨t, ht⟩ := commCompare F E
          let q := (Iso.refl (FiniteBundle.trivial (X × Y) n).Fiber).tensor t
          refine ⟨s.trans (a.trans q), ?_⟩
          intro x v u w
          change q.linearEquiv x (a.linearEquiv x (s.linearEquiv x
            (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)))) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)
          rw [hs, ha]
          change TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (t.linearEquiv x)
            (u ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] v)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)
          simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ht]
      -- Pullback of the coefficient bundle keeps the supplied coordinate vector.
      have pullbackCompareX
          (n : ℕ) (f : C((X × Y), X)) (J : FiniteBundle X) :
          ∃ e : Iso (((FiniteBundle.trivial X n).tensor J).pullback f).Fiber
              ((FiniteBundle.trivial (X × Y) n).tensor (J.pullback f)).Fiber,
            ∀ (y : (X × Y)) (t : (Fin n → ℂ) ⊗[ℂ] J.Fiber (f y)), e.linearEquiv y t = t := by
        let e := (pullbackTensorIso (E := (FiniteBundle.trivial X n).Fiber)
          (F := J.Fiber) f).trans
            ((pullbackTrivialIso f n).tensor (Iso.refl (J.pullback f).Fiber))
        refine ⟨e, ?_⟩
        intro y t
        have hm : ((e.linearEquiv y).toLinearMap) = LinearMap.id := by
          apply TensorProduct.ext'
          intro u v
          change (pullbackTrivialIso f n).linearEquiv y u ⊗ₜ[ℂ] v = u ⊗ₜ[ℂ] v
          rw [pullbackTrivialIso_apply]
        exact DFunLike.congr_fun hm t
      have pullbackCompareY
          (n : ℕ) (f : C((X × Y), Y)) (J : FiniteBundle Y) :
          ∃ e : Iso (((FiniteBundle.trivial Y n).tensor J).pullback f).Fiber
              ((FiniteBundle.trivial (X × Y) n).tensor (J.pullback f)).Fiber,
            ∀ (y : (X × Y)) (t : (Fin n → ℂ) ⊗[ℂ] J.Fiber (f y)), e.linearEquiv y t = t := by
        let e := (pullbackTensorIso (E := (FiniteBundle.trivial Y n).Fiber)
          (F := J.Fiber) f).trans
            ((pullbackTrivialIso f n).tensor (Iso.refl (J.pullback f).Fiber))
        refine ⟨e, ?_⟩
        intro y t
        have hm : ((e.linearEquiv y).toLinearMap) = LinearMap.id := by
          apply TensorProduct.ext'
          intro u v
          change (pullbackTrivialIso f n).linearEquiv y u ⊗ₜ[ℂ] v = u ⊗ₜ[ℂ] v
          rw [pullbackTrivialIso_apply]
        exact DFunLike.congr_fun hm t
      constructor
      · obtain ⟨p, hp⟩ := pullbackCompareX ρ.dimension
          (ContinuousMap.fst : C(X × Y, X)) J
        obtain ⟨a, ha⟩ := (comparisons ρ.dimension
          (J.pullback (ContinuousMap.fst : C(X × Y, X)))
          (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).1
        let e := (p.tensor (Iso.refl (K.pullback ContinuousMap.snd).Fiber)).trans a
        have he (z : X × Y) (u : Fin ρ.dimension → ℂ) (v : J.Fiber z.1)
            (w : K.Fiber z.2) :
            e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          change a.linearEquiv z (p.linearEquiv z (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = _
          rw [hp]
          exact ha z u v w
        refine ⟨e, he, ?_⟩
        intro g z t
        let L := (e.linearEquiv (g • z)).toLinearMap.comp
              (((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).pullback
                ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap g z)
        let R := (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z).comp
              (e.linearEquiv z).toLinearMap
        have hm : L = R := by
          apply TensorProduct.ext'
          intro s w
          induction s using TensorProduct.inductionOn with
          | tmul u v =>
            change e.linearEquiv (g • z)
              (((ρ.representation g) u ⊗ₜ[ℂ] α.linearMap g z.1 v) ⊗ₜ[ℂ]
                β.linearMap g z.2 w) =
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
                ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z)
                    (e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w))
            rw [he, he]
            rfl
          | add s t hs ht =>
            have hsplit : (s + t) ⊗ₜ[ℂ] w = s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w :=
              TensorProduct.add_tmul s t w
            calc
              L ((s + t) ⊗ₜ[ℂ] w) = L (s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w) := congrArg L hsplit
              _ = L (s ⊗ₜ[ℂ] w) + L (t ⊗ₜ[ℂ] w) := L.map_add _ _
              _ = R (s ⊗ₜ[ℂ] w) + R (t ⊗ₜ[ℂ] w) := congrArg₂ (· + ·) hs ht
              _ = R (s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w) := (R.map_add _ _).symm
              _ = R ((s + t) ⊗ₜ[ℂ] w) := congrArg R hsplit.symm
        exact DFunLike.congr_fun hm t
      · obtain ⟨p, hp⟩ := pullbackCompareY ρ.dimension
          (ContinuousMap.snd : C(X × Y, Y)) K
        obtain ⟨a, ha⟩ := (comparisons ρ.dimension
          (J.pullback (ContinuousMap.fst : C(X × Y, X)))
          (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).2
        let e := ((Iso.refl (J.pullback ContinuousMap.fst).Fiber).tensor p).trans a
        have he (z : X × Y) (v : J.Fiber z.1) (u : Fin ρ.dimension → ℂ)
            (w : K.Fiber z.2) :
            e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          change a.linearEquiv z (v ⊗ₜ[ℂ] p.linearEquiv z (u ⊗ₜ[ℂ] w)) = _
          rw [hp]
          exact ha z v u w
        refine ⟨e, he, ?_⟩
        intro g z t
        let L := (e.linearEquiv (g • z)).toLinearMap.comp
              (((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (((EquivariantStructure.ofFiniteRepresentation ρ).tensor β).pullback
                  ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap g z)
        let R := (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z).comp
              (e.linearEquiv z).toLinearMap
        have hm : L = R := by
          apply TensorProduct.ext'
          intro v s
          induction s using TensorProduct.inductionOn with
          | tmul u w =>
            change e.linearEquiv (g • z)
              (α.linearMap g z.1 v ⊗ₜ[ℂ] ((ρ.representation g) u ⊗ₜ[ℂ]
                β.linearMap g z.2 w)) =
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
                ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z)
                    (e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)))
            rw [he, he]
            rfl
          | add s t hs ht =>
            have hsplit : v ⊗ₜ[ℂ] (s + t) = v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t :=
              TensorProduct.tmul_add v s t
            calc
              L (v ⊗ₜ[ℂ] (s + t)) = L (v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t) := congrArg L hsplit
              _ = L (v ⊗ₜ[ℂ] s) + L (v ⊗ₜ[ℂ] t) := L.map_add _ _
              _ = R (v ⊗ₜ[ℂ] s) + R (v ⊗ₜ[ℂ] t) := congrArg₂ (· + ·) hs ht
              _ = R (v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t) := (R.map_add _ _).symm
              _ = R (v ⊗ₜ[ℂ] (s + t)) := congrArg R hsplit.symm
        exact DFunLike.congr_fun hm t
    have combine (ρ : FiniteContinuousRepresentation G)
        (J K A B : FiniteBundle (X × Y))
        (σJ : EquivariantStructure G J.Fiber) (σK : EquivariantStructure G K.Fiber)
        (α : EquivariantStructure G A.Fiber) (β : EquivariantStructure G B.Fiber)
        (c : Iso J.Fiber ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor A).Fiber)
        (d : Iso K.Fiber ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor B).Fiber)
        (hc : c.IsEquivariant σJ ((EquivariantStructure.ofFiniteRepresentation ρ).tensor α))
        (hd : d.IsEquivariant σK ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)) :
        ∃ e : Iso (J.sum K).Fiber
          ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor (A.sum B)).Fiber,
          (∀ (x : (X × Y)) (u : Fin ρ.dimension → ℂ) (v : A.Fiber x) (w : B.Fiber x)
              (s : J.Fiber x) (t : K.Fiber x),
            c.linearEquiv x s = u ⊗ₜ[ℂ] v → d.linearEquiv x t = u ⊗ₜ[ℂ] w →
              e.linearEquiv x (s, t) = u ⊗ₜ[ℂ] (v, w)) ∧
          e.IsEquivariant (σJ.sum σK)
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)) := by
      let V := FiniteBundle.trivial (X × Y) ρ.dimension
      -- Native projections give the actual coefficient distributivity map.
      let p : Hom (V.tensor (A.sum B)).Fiber (V.tensor A).Fiber :=
        (Iso.refl V.Fiber).toHom.tensor (sumFst (E := A.Fiber) (F := B.Fiber))
      let q : Hom (V.tensor (A.sum B)).Fiber (V.tensor B).Fiber :=
        (Iso.refl V.Fiber).toHom.tensor (sumSnd (E := A.Fiber) (F := B.Fiber))
      let D (x : (X × Y)) := TensorProduct.prodRight ℂ ℂ (V.Fiber x) (A.Fiber x) (B.Fiber x)
      have hvalue (x : (X × Y)) (t : (V.tensor (A.sum B)).Fiber x) :
          D x t = (p.linearMap x t, q.linearMap x t) := by
        have hm : (D x).toLinearMap = (p.linearMap x).prod (q.linearMap x) := by
          apply TensorProduct.ext'
          intro u v
          rfl
        exact DFunLike.congr_fun hm t
      let f : Hom (V.tensor (A.sum B)).Fiber ((V.tensor A).sum (V.tensor B)).Fiber :=
        { linearMap x := (D x).toLinearMap
          continuous_total := by
            apply continuous_induced_rng.mpr
            apply (p.continuous_total.prodMk q.continuous_total).congr
            intro z
            exact congrArg (fun w ↦
              ((⟨z.proj, w.1⟩ : TotalSpace Unit (V.tensor A).Fiber),
                (⟨z.proj, w.2⟩ : TotalSpace Unit (V.tensor B).Fiber)))
                  (hvalue z.proj z.snd).symm }
      let δ := f.toIso (fun x ↦ (D x).bijective)
      let e := (c.sum d).trans δ.symm
      refine ⟨e, ?_, ?_⟩
      · intro x u v w s t hs ht
        apply (δ.linearEquiv x).injective
        change δ.linearEquiv x ((δ.linearEquiv x).symm
          (c.linearEquiv x s, d.linearEquiv x t)) = δ.linearEquiv x (u ⊗ₜ[ℂ] (v, w))
        rw [LinearEquiv.apply_symm_apply]
        change (c.linearEquiv x s, d.linearEquiv x t) = (u ⊗ₜ[ℂ] v, u ⊗ₜ[ℂ] w)
        exact Prod.ext hs ht
      · intro g x t
        -- The same distributivity and corner maps intertwine the supplied actions.
        have hnat : (δ.linearEquiv (g • x)).toLinearMap.comp
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)).linearMap g x) =
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).sum
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)).linearMap g x).comp
                (δ.linearEquiv x).toLinearMap := by
          apply TensorProduct.ext'
          intro u v
          rfl
        have h := DFunLike.congr_fun hnat
          ((δ.linearEquiv x).symm (c.linearEquiv x t.1, d.linearEquiv x t.2))
        apply (δ.linearEquiv (g • x)).injective
        change δ.linearEquiv (g • x) ((δ.linearEquiv (g • x)).symm
            (c.linearEquiv (g • x) (σJ.linearMap g x t.1),
              d.linearEquiv (g • x) (σK.linearMap g x t.2))) =
          δ.linearEquiv (g • x)
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)).linearMap g x)
              ((δ.linearEquiv x).symm (c.linearEquiv x t.1, d.linearEquiv x t.2)))
        rw [LinearEquiv.apply_symm_apply]
        have hcancel := congrArg
          ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).sum
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)).linearMap g x)
          ((δ.linearEquiv x).apply_symm_apply (c.linearEquiv x t.1, d.linearEquiv x t.2))
        exact (Prod.ext (hc g x t.1) (hd g x t.2)).trans (h.trans hcancel).symm
    have cutoff (n : ℕ) (E F : FiniteBundle X)
        (a : CompactSupportTriple E.Fiber F.Fiber) :
        (∀ (c : C(X, unitInterval)) (x : X) (u : Fin n → ℂ) (v : E.Fiber x),
          (a.tensorLeft (FiniteBundle.trivial X n).Fiber).cutoffLinearMap c x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.cutoffLinearMap c x v) ∧
        ∀ (c : C(X, unitInterval)) (x : X) (u : Fin n → ℂ) (v : F.Fiber x),
          (a.tensorLeft (FiniteBundle.trivial X n).Fiber).inverse.cutoffLinearMap c x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.inverse.cutoffLinearMap c x v := by
      classical
      have hforward (x : (a.controlᶜ : Set X)) (u : Fin n → ℂ) (v : E.Fiber x) :
          (a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.boundary.linearEquiv x v :=
        RelativeTriple.tensorLeft_tmul (FiniteBundle.trivial X n).Fiber a.boundary x u v
      have hinverse (x : (a.controlᶜ : Set X)) (u : Fin n → ℂ) (v : F.Fiber x) :
          ((a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv x).symm
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] (a.boundary.linearEquiv x).symm v := by
        apply ((a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv x).injective
        exact (LinearEquiv.apply_symm_apply
          ((a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv x) _).trans
            ((hforward x u ((a.boundary.linearEquiv x).symm v)).trans
              (congrArg (fun w ↦ u ⊗ₜ[ℂ] w)
                ((a.boundary.linearEquiv x).apply_symm_apply v))).symm
      constructor
      · intro c x u v
        dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.tensorLeft]
        split_ifs with hx
        · simp
        · change (((c x : ℝ) : ℂ)) •
              (a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv
                ⟨x, hx⟩ (u ⊗ₜ[ℂ] v) =
            u ⊗ₜ[ℂ] ((((c x : ℝ) : ℂ)) • a.boundary.linearEquiv ⟨x, hx⟩ v)
          exact (congrArg (fun w ↦ (((c x : ℝ) : ℂ)) • w)
            (hforward ⟨x, hx⟩ u v)).trans
              (TensorProduct.tmul_smul (R := ℂ) (N := F.Fiber x)
                (((c x : ℝ) : ℂ)) u (a.boundary.linearEquiv ⟨x, hx⟩ v)).symm
      · intro c x u v
        dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          CompactSupportTriple.tensorLeft]
        split_ifs with hx
        · simp
        · change (((c x : ℝ) : ℂ)) •
              ((a.boundary.tensorLeft (FiniteBundle.trivial X n).Fiber).linearEquiv
                ⟨x, hx⟩).symm (u ⊗ₜ[ℂ] v) =
            u ⊗ₜ[ℂ] ((((c x : ℝ) : ℂ)) • (a.boundary.linearEquiv ⟨x, hx⟩).symm v)
          exact (congrArg (fun w ↦ (((c x : ℝ) : ℂ)) • w)
            (hinverse ⟨x, hx⟩ u v)).trans
              (TensorProduct.tmul_smul (R := ℂ) (N := E.Fiber x)
                (((c x : ℝ) : ℂ)) u ((a.boundary.linearEquiv ⟨x, hx⟩).symm v)).symm
    -- Fix the exact product, representation tensor and common compact control.
    let P := supportedEquivariantExternalProductTriple a b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    let S := supportedEquivariantExternalProductTriple (a.tensorRepresentation θ) b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    let T := P.tensorRepresentation θ
    let A₀₀ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₁₁ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₁₀ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₀₁ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₀₀ := ((a.tensorRepresentation θ).1.source.pullback
      (ContinuousMap.fst : C(X × Y, X))).tensor
        (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₁₁ := ((a.tensorRepresentation θ).1.target.pullback
      (ContinuousMap.fst : C(X × Y, X))).tensor
        (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₁₀ := ((a.tensorRepresentation θ).1.target.pullback
      (ContinuousMap.fst : C(X × Y, X))).tensor
        (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₀₁ := ((a.tensorRepresentation θ).1.source.pullback
      (ContinuousMap.fst : C(X × Y, X))).tensor
        (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    obtain ⟨c₀₀, hc₀₀, ec₀₀⟩ :=
      (corners θ a.1.source b.1.source a.2.sourceAction b.2.sourceAction).1
    obtain ⟨c₁₁, hc₁₁, ec₁₁⟩ :=
      (corners θ a.1.target b.1.target a.2.targetAction b.2.targetAction).1
    obtain ⟨c₁₀, hc₁₀, ec₁₀⟩ :=
      (corners θ a.1.target b.1.source a.2.targetAction b.2.sourceAction).1
    obtain ⟨c₀₁, hc₀₁, ec₀₁⟩ :=
      (corners θ a.1.source b.1.target a.2.sourceAction b.2.targetAction).1
    obtain ⟨u, hu, hueq⟩ := combine θ B₀₀ B₁₁ A₀₀ A₁₁
      ((((EquivariantStructure.ofFiniteRepresentation θ).tensor a.2.sourceAction).pullback
        ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((((EquivariantStructure.ofFiniteRepresentation θ).tensor a.2.targetAction).pullback
        ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      c₀₀ c₁₁ ec₀₀ ec₁₁
    obtain ⟨v, hv, hveq⟩ := combine θ B₁₀ B₀₁ A₁₀ A₀₁
      ((((EquivariantStructure.ofFiniteRepresentation θ).tensor a.2.targetAction).pullback
        ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((((EquivariantStructure.ofFiniteRepresentation θ).tensor a.2.sourceAction).pullback
        ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      c₁₀ c₀₁ ec₁₀ ec₀₁
    -- One invariant compact product is used on both sides of the actual square.
    apply equivariantSupportTripleKZero_generator_relations.1 S T
    refine ⟨L ×ˢ M, hL.prod hM,
      (fun g z ↦ and_congr (hLinv g z.1) (hMinv g z.2)),
      Set.Subset.refl _, Set.Subset.refl _, u, v, hueq, hveq, ?_⟩
    intro z s
    -- Compare global fiber maps before restricting to this compact exterior.
    let B := reciprocalTensorSymbol
      (a.1.datum.cutoffLinearMap ρ z.val.1)
      (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
      (b.1.datum.cutoffLinearMap τ z.val.2)
      (b.1.datum.inverse.cutoffLinearMap τ z.val.2)
    let C := reciprocalTensorSymbol
      ((a.tensorRepresentation θ).1.datum.cutoffLinearMap ρ z.val.1)
      ((a.tensorRepresentation θ).1.datum.inverse.cutoffLinearMap ρ z.val.1)
      (b.1.datum.cutoffLinearMap τ z.val.2)
      (b.1.datum.inverse.cutoffLinearMap τ z.val.2)
    have hcut := cutoff θ.dimension a.1.source a.1.target a.1.datum
    have hD (t : Fin θ.dimension → ℂ) (q : a.1.source.Fiber z.val.1) :
        (a.tensorRepresentation θ).1.datum.cutoffLinearMap ρ z.val.1 (t ⊗ₜ[ℂ] q) =
          t ⊗ₜ[ℂ] a.1.datum.cutoffLinearMap ρ z.val.1 q :=
      hcut.1 ρ z.val.1 t q
    have hD' (t : Fin θ.dimension → ℂ) (q : a.1.target.Fiber z.val.1) :
        (a.tensorRepresentation θ).1.datum.inverse.cutoffLinearMap ρ z.val.1 (t ⊗ₜ[ℂ] q) =
          t ⊗ₜ[ℂ] a.1.datum.inverse.cutoffLinearMap ρ z.val.1 q :=
      hcut.2 ρ z.val.1 t q
    let l := (v.linearEquiv z).toLinearMap.comp C
    let r := (TensorProduct.map (LinearMap.id : (Fin θ.dimension → ℂ) →ₗ[ℂ] _) B).comp
      (u.linearEquiv z).toLinearMap
    have hm : l = r := by
      apply LinearMap.prod_ext
      · apply TensorProduct.ext'
        intro q w
        induction q using TensorProduct.inductionOn with
        | tmul t q =>
          change v.linearEquiv z (C ((t ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w, 0)) =
            TensorProduct.map LinearMap.id B (u.linearEquiv z ((t ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w, 0))
          simp only [C, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
            map_zero, add_zero]
          erw [hD]
          erw [hv z.val t _ _ _ _ (hc₁₀ z.val t _ w) (hc₀₁ z.val t q _)]
          erw [hu z.val t (q ⊗ₜ[ℂ] w) (0 : A₁₁.Fiber z.val) _ _ (hc₀₀ z.val t q w)
            (by simp only [map_zero, TensorProduct.tmul_zero])]
          simp [B, reciprocalTensorSymbol, Function.prod]
        | add q₁ q₂ h₁ h₂ =>
          have hsplit : (q₁ + q₂) ⊗ₜ[ℂ] w = q₁ ⊗ₜ[ℂ] w + q₂ ⊗ₜ[ℂ] w :=
            TensorProduct.add_tmul q₁ q₂ w
          change l ((q₁ + q₂) ⊗ₜ[ℂ] w, 0) = r ((q₁ + q₂) ⊗ₜ[ℂ] w, 0)
          exact ((congrArg (fun t ↦ l (t, 0)) hsplit).trans
            ((l.map_add (q₁ ⊗ₜ[ℂ] w, 0) (q₂ ⊗ₜ[ℂ] w, 0)).trans
              ((congrArg₂ (· + ·) h₁ h₂).trans
                ((r.map_add (q₁ ⊗ₜ[ℂ] w, 0) (q₂ ⊗ₜ[ℂ] w, 0)).symm.trans
                  (congrArg (fun t ↦ r (t, 0)) hsplit).symm))))
      · apply TensorProduct.ext'
        intro q w
        induction q using TensorProduct.inductionOn with
        | tmul t q =>
          change v.linearEquiv z (C (0, (t ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w)) =
            TensorProduct.map LinearMap.id B (u.linearEquiv z (0, (t ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] w))
          simp only [C, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
            map_zero, zero_add, LinearMap.neg_apply]
          erw [hD']
          have hneg : c₁₀.linearEquiv z.val
              (-((t ⊗ₜ[ℂ] q) ⊗ₜ[ℂ] (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w))) =
              t ⊗ₜ[ℂ] (-(q ⊗ₜ[ℂ] (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w))) := by
            exact ((c₁₀.linearEquiv z.val).map_neg _).trans
              ((congrArg Neg.neg
                (hc₁₀ z.val t q (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w))).trans
                  (TensorProduct.tmul_neg t _).symm)
          erw [hv z.val t _ _ _ _ hneg (hc₀₁ z.val t _ w)]
          erw [hu z.val t (0 : A₀₀.Fiber z.val) (q ⊗ₜ[ℂ] w) _ _
            (by simp only [map_zero, TensorProduct.tmul_zero])
            (hc₁₁ z.val t q w)]
          simp [B, reciprocalTensorSymbol, Function.prod]
        | add q₁ q₂ h₁ h₂ =>
          have hsplit : (q₁ + q₂) ⊗ₜ[ℂ] w = q₁ ⊗ₜ[ℂ] w + q₂ ⊗ₜ[ℂ] w :=
            TensorProduct.add_tmul q₁ q₂ w
          change l (0, (q₁ + q₂) ⊗ₜ[ℂ] w) = r (0, (q₁ + q₂) ⊗ₜ[ℂ] w)
          exact ((congrArg (fun t ↦ l (0, t)) hsplit).trans
            ((l.map_add (0, q₁ ⊗ₜ[ℂ] w) (0, q₂ ⊗ₜ[ℂ] w)).trans
              ((congrArg₂ (· + ·) h₁ h₂).trans
                ((r.map_add (0, q₁ ⊗ₜ[ℂ] w) (0, q₂ ⊗ₜ[ℂ] w)).symm.trans
                  (congrArg (fun t ↦ r (0, t)) hsplit).symm))))
    have hS : (S.1.datum.enlarge (L ×ˢ M) (hL.prod hM)
        (Set.Subset.refl _)).boundary.linearEquiv z s = C s :=
      (S.1.datum.enlarge_apply _ _ (Set.Subset.refl _) z s).trans rfl
    have hT : (T.1.datum.boundary.linearEquiv z).toLinearMap =
        TensorProduct.map (LinearMap.id : (Fin θ.dimension → ℂ) →ₗ[ℂ] _) B := by
      apply TensorProduct.ext'
      intro t q
      exact RelativeTriple.tensorLeft_tmul (FiniteBundle.trivial (X × Y) θ.dimension).Fiber
        P.1.datum.boundary z t q
    have hTenlarge := T.1.datum.enlarge_apply (L ×ˢ M) (hL.prod hM)
      (Set.Subset.refl _) z (u.linearEquiv z s)
    exact (congrArg (v.linearEquiv z.val) hS).trans
      ((DFunLike.congr_fun hm s).trans
        ((DFunLike.congr_fun hT (u.linearEquiv z s)).symm.trans hTenlarge.symm))
  -- Use one actual pair of invariant cutoffs for both representatives.
  have hfinite (θ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y) :
      μ (a.tensorRepresentation θ).kZeroClass b.kZeroClass =
        equivariantSupportRepresentationAction (finiteRepresentationClass θ)
          (μ a.kZeroClass b.kZeroClass) := by
    obtain ⟨U, hU, ha, _, L, hL, _, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
      exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
    obtain ⟨V, hV, hb, _, M, hM, _, hMinv, τ, hτinv, hτzero, hτone⟩ :=
      exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
    rw [hμ (a.tensorRepresentation θ) b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv]
    rw [hμ a b ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv, equivariantSupportRepresentationAction_finiteClass]
    exact hclass θ a b ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
  have extX (f g : EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ a : EquivariantSupportBundleTriple G X, f a.kZeroClass = g a.kZeroClass) :
      f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have extY (f g : EquivariantSupportTripleKZero G Y →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ b : EquivariantSupportBundleTriple G Y, f b.kZeroClass = g b.kZeroClass) :
      f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have extR (f g : RepresentationGrothendieckGroup G →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ θ : FiniteContinuousRepresentation G,
        f (finiteRepresentationClass θ) = g (finiteRepresentationClass θ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  let α := equivariantSupportRepresentationAction (G := G) (X := X)
  let γ := equivariantSupportRepresentationAction (G := G) (X := X × Y)
  -- Descend through both original support presentations and virtual representations.
  have hX (θ : FiniteContinuousRepresentation G) (b : EquivariantSupportBundleTriple G Y) :
      (μ.flip b.kZeroClass).comp (α (finiteRepresentationClass θ)) =
        (γ (finiteRepresentationClass θ)).comp (μ.flip b.kZeroClass) := by
    apply extX
    intro a
    change μ (equivariantSupportRepresentationAction (finiteRepresentationClass θ) a.kZeroClass)
      b.kZeroClass = _
    rw [equivariantSupportRepresentationAction_finiteClass]
    exact hfinite θ a b
  have hY (θ : FiniteContinuousRepresentation G) :
      μ (α (finiteRepresentationClass θ) a) =
        (γ (finiteRepresentationClass θ)).comp (μ a) := by
    apply extY
    intro b
    exact DFunLike.congr_fun (hX θ b) a
  have hR : (μ.flip b).comp (α.flip a) = γ.flip (μ a b) := by
    apply extR
    intro θ
    exact DFunLike.congr_fun (hY θ) b
  exact DFunLike.congr_fun hR r

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 10000000 in
-- Retain the original tensor topologies through the three additive presentation descents.
/-- Moving a representation coefficient from the second factor preserves its full action. -/
theorem equivariantSupportKZeroExternalProduct_smul_right
    (r : RepresentationGrothendieckGroup G)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Y) :
    equivariantSupportKZeroExternalProduct a (r • b) =
      r • equivariantSupportKZeroExternalProduct a b := by
  /- Stage 1: for an actual representation and pair of triples, move that
  representation factor to the left by the ordinary tensor symmetry and
  associators. Use the same vector-preserving comparison between the pulled
  representation bundle and its original product-base diagonal bundle. It has
  degree zero, so this permutation adds no grading sign.
  These actual maps intertwine the diagonal actions and all four original
  reciprocal blocks, while retaining the same product compact control.
  Stage 2: use the specified generator values and extend through the three
  additive presentations. Together with the left formula this gives the
  usual balancing over the existing representation ring, without dimension
  reduction or any newly imposed exact-sequence relation. -/
  classical
  let μ : EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero G Y →+ EquivariantSupportTripleKZero G (X × Y) :=
    equivariantSupportKZeroExternalProduct (G := G) (X := X) (Y := Y)
  have hμ := equivariantSupportKZeroExternalProduct_class (G := G) (X := X) (Y := Y)
  change μ a (r • b) = r • μ a b
  have hclass
      (θ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y)
      (ρ : C(X, unitInterval)) (U : Set X) (hU : IsOpen U) (ha : a.1.datum.control ⊆ U)
      (hρzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
      (hρone : ∀ x ∉ L, ρ x = 1)
      (τ : C(Y, unitInterval)) (V : Set Y) (hV : IsOpen V) (hb : b.1.datum.control ⊆ V)
      (hτzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
      (hτone : ∀ y ∉ M, τ y = 1)
      (hρinv : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
      (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
      (hτinv : ∀ (g : G) (y : Y), τ (g • y) = τ y)
      (hMinv : ∀ (g : G) (y : Y), g • y ∈ M ↔ y ∈ M) :
      (supportedEquivariantExternalProductTriple a (b.tensorRepresentation θ)
        ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
        hρinv hLinv hτinv hMinv).kZeroClass =
        ((supportedEquivariantExternalProductTriple a b
          ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
          hρinv hLinv hτinv hMinv).tensorRepresentation θ).kZeroClass := by
    classical
    have corners (ρ : FiniteContinuousRepresentation G)
        (J : FiniteBundle X) (K : FiniteBundle Y)
        (α : EquivariantStructure G J.Fiber) (β : EquivariantStructure G K.Fiber) :
        (∃ e : Iso ((((FiniteBundle.trivial X ρ.dimension).tensor J).pullback
              (ContinuousMap.fst : C(X × Y, X))).tensor
                (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).Fiber
            ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor
              ((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd))).Fiber,
          (∀ (z : X × Y) (u : Fin ρ.dimension → ℂ) (v : J.Fiber z.1) (w : K.Fiber z.2),
            e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
          e.IsEquivariant
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).pullback
              ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl))))) ∧
        ∃ e : Iso ((J.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
              (((FiniteBundle.trivial Y ρ.dimension).tensor K).pullback
                (ContinuousMap.snd : C(X × Y, Y)))).Fiber
            ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor
              ((J.pullback ContinuousMap.fst).tensor (K.pullback ContinuousMap.snd))).Fiber,
          (∀ (z : X × Y) (v : J.Fiber z.1) (u : Fin ρ.dimension → ℂ) (w : K.Fiber z.2),
            e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
          e.IsEquivariant
            ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor β).pullback
                ContinuousMap.snd (fun _ _ ↦ rfl)))
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))) := by
      have comparisons (n : ℕ) (E F : FiniteBundle (X × Y)) :
        (∃ e : Iso (((FiniteBundle.trivial (X × Y) n).tensor E).tensor F).Fiber
            ((FiniteBundle.trivial (X × Y) n).tensor (E.tensor F)).Fiber,
          ∀ (x : (X × Y)) (u : Fin n → ℂ) (v : E.Fiber x) (w : F.Fiber x),
            e.linearEquiv x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)) ∧
        ∃ e : Iso (E.tensor ((FiniteBundle.trivial (X × Y) n).tensor F)).Fiber
            ((FiniteBundle.trivial (X × Y) n).tensor (E.tensor F)).Fiber,
          ∀ (x : (X × Y)) (v : E.Fiber x) (u : Fin n → ℂ) (w : F.Fiber x),
            e.linearEquiv x (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
        classical
        -- Fixed finite coefficients reduce continuity to actual tensor generators.
        have hcoeff (n : ℕ) (E F : FiniteBundle (X × Y))
            (L : ∀ x, (Fin n → ℂ) ⊗[ℂ] E.Fiber x →ₗ[ℂ] F.Fiber x)
            (hL : ∀ i : Fin n, Continuous (fun z : TotalSpace Unit E.Fiber ↦
              (⟨z.proj, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)⟩ : TotalSpace Unit F.Fiber))) :
            Continuous (fun z : TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor E).Fiber ↦
              (⟨z.proj, L z.proj z.snd⟩ : TotalSpace Unit F.Fiber)) := by
          classical
          -- Test each actual finite-sum generator of the original tensor topology.
          apply continuous_iSup_dom.mpr
          intro m
          apply continuous_coinduced_dom.mpr
          let D := TotalSpace Unit (fun x ↦ (Fin m → Fin n → ℂ) × (Fin m → E.Fiber x))
          let : TopologicalSpace D := TopologicalSpace.induced
            (fun z : D ↦ (z.proj,
              (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) inferInstance
          have hc : Continuous (fun z : D ↦ (z.proj,
              (fun j ↦ (⟨z.proj, z.snd.1 j⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun j ↦ (⟨z.proj, z.snd.2 j⟩ : TotalSpace Unit E.Fiber)))) := continuous_induced_dom
          let b : C(D, (X × Y)) := ⟨fun z ↦ z.proj, hc.fst⟩
          have ht : Continuous (fun z : TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber ↦
              (z.proj, z.snd)) := continuous_induced_dom
          -- The pullback section module handles finite sums on the generating domain.
          let slice (j : Fin m) (i : Fin n) : continuousSections ((b : D → (X × Y)) *ᵖ F.Fiber) :=
            ⟨fun z ↦ L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j), by
              change Continuous (fun z : D ↦
                (⟨z, L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)⟩ :
                  TotalSpace Unit ((b : D → (X × Y)) *ᵖ F.Fiber)))
              rw [(inducing_pullbackTotalSpaceEmbedding Unit F.Fiber b).continuous_iff]
              exact continuous_id.prodMk ((hL i).comp ((continuous_apply j).comp hc.snd.snd))⟩
          let c (j : Fin m) (i : Fin n) : C(D, ℂ) :=
            ⟨fun z ↦ z.snd.1 j i, (continuous_apply i).comp
              (ht.snd.comp ((continuous_apply j).comp hc.snd.fst))⟩
          let sectionSum : continuousSections ((b : D → (X × Y)) *ᵖ F.Fiber) :=
            ∑ j : Fin m, ∑ i : Fin n, c j i • slice j i
          have hsum := (Pullback.continuous_lift Unit F.Fiber b).comp sectionSum.property
          apply hsum.congr
          intro z
          change (⟨z.proj, sectionSum.val z⟩ : TotalSpace Unit F.Fiber) =
            ⟨z.proj, L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)⟩
          apply congrArg (fun w : F.Fiber z.proj ↦ (⟨z.proj, w⟩ : TotalSpace Unit F.Fiber))
          simp only [sectionSum, Submodule.coe_sum, Finset.sum_apply,
            SetLike.val_smul, Pi.smul_apply]
          change (∑ j : Fin m, ∑ i : Fin n,
            z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
              L z.proj (∑ j : Fin m, z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j)
          -- Standard finite coordinates reconstruct every coefficient, including rank zero.
          have hcoord (u : Fin n → ℂ) : ∑ i : Fin n, u i • Pi.single i 1 = u := by
            ext i
            simp [Pi.single_apply]
          have hpure (j : Fin m) : ∑ i : Fin n,
              z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j) =
                z.snd.1 j ⊗ₜ[ℂ] z.snd.2 j := by
            simpa only [TensorProduct.sum_tmul, TensorProduct.smul_tmul'] using
              congrArg (fun u ↦ u ⊗ₜ[ℂ] z.snd.2 j) (hcoord (z.snd.1 j))
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro j _
          exact (by rw [map_sum]; simp only [map_smul] :
            (∑ i : Fin n, z.snd.1 j i • L z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j)) =
              L z.proj (∑ i : Fin n, z.snd.1 j i • (Pi.single i 1 ⊗ₜ[ℂ] z.snd.2 j))).trans
                (congrArg (L z.proj) (hpure j))
        have hpure (n : ℕ) (J : FiniteBundle (X × Y)) (u : Fin n → ℂ) :
            Continuous (fun z : TotalSpace Unit J.Fiber ↦
              (⟨z.proj, u ⊗ₜ[ℂ] z.snd⟩ :
                TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber)) := by
          let D := TotalSpace Unit (fun x ↦ (Fin 1 → Fin n → ℂ) × (Fin 1 → J.Fiber x))
          let : TopologicalSpace D := TopologicalSpace.induced
            (fun z : D ↦ (z.proj,
              (fun i ↦ (⟨z.proj, z.snd.1 i⟩ :
                TotalSpace Unit (FiniteBundle.trivial (X × Y) n).Fiber)),
              (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
          have hg : Continuous (fun z : D ↦
              (⟨z.proj, ∑ i : Fin 1, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                TotalSpace Unit ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber)) :=
            continuous_iSup_rng (i := 1) continuous_coinduced_rng
          let f (z : TotalSpace Unit J.Fiber) : D := ⟨z.proj, fun _ ↦ u, fun _ ↦ z.snd⟩
          have hf : Continuous f := by
            apply continuous_induced_rng.mpr
            refine (continuous_proj (E := J.Fiber)).prodMk
              ((continuous_pi ?_).prodMk (continuous_pi (fun _ ↦ continuous_id)))
            intro _
            exact continuous_induced_rng.mpr
              ((continuous_proj (E := J.Fiber)).prodMk continuous_const)
          apply (hg.comp hf).congr
          intro z
          simp only [Function.comp_apply, f, Fin.sum_univ_one]
        -- The canonical tensor symmetry is continuous on every actual finite-sum generator.
        have commCompare (J K : FiniteBundle (X × Y)) :
            ∃ e : Iso (J.tensor K).Fiber (K.tensor J).Fiber,
              ∀ (x : (X × Y)) (v : J.Fiber x) (w : K.Fiber x),
                e.linearEquiv x (v ⊗ₜ[ℂ] w) = w ⊗ₜ[ℂ] v := by
          let c (x : (X × Y)) := TensorProduct.comm ℂ (J.Fiber x) (K.Fiber x)
          let f : Hom (J.tensor K).Fiber (K.tensor J).Fiber :=
            { linearMap x := (c x).toLinearMap
              continuous_total := by
                apply continuous_iSup_dom.mpr
                intro m
                apply continuous_coinduced_dom.mpr
                let D := TotalSpace Unit (fun x ↦ (Fin m → J.Fiber x) × (Fin m → K.Fiber x))
                let D' := TotalSpace Unit (fun x ↦ (Fin m → K.Fiber x) × (Fin m → J.Fiber x))
                let : TopologicalSpace D := TopologicalSpace.induced
                  (fun z : D ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit J.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit K.Fiber)))) inferInstance
                let : TopologicalSpace D' := TopologicalSpace.induced
                  (fun z : D' ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit K.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit J.Fiber)))) inferInstance
                let swapTuple (z : D) : D' := ⟨z.proj, z.snd.2, z.snd.1⟩
                have hc : Continuous (fun z : D ↦ (z.proj,
                    (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit J.Fiber)),
                    (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit K.Fiber)))) :=
                  continuous_induced_dom
                have hswap : Continuous swapTuple := by
                  apply continuous_induced_rng.mpr
                  exact hc.fst.prodMk (hc.snd.snd.prodMk hc.snd.fst)
                have hg : Continuous (fun z : D' ↦
                    (⟨z.proj, ∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                      TotalSpace Unit (K.tensor J).Fiber)) :=
                  continuous_iSup_rng (i := m) continuous_coinduced_rng
                apply (hg.comp hswap).congr
                intro z
                change (⟨z.proj, ∑ i, z.snd.2 i ⊗ₜ[ℂ] z.snd.1 i⟩ :
                  TotalSpace Unit (K.tensor J).Fiber) =
                    ⟨z.proj, c z.proj (∑ i, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i)⟩
                apply congrArg (fun t : (K.tensor J).Fiber z.proj ↦
                  (⟨z.proj, t⟩ : TotalSpace Unit (K.tensor J).Fiber))
                rw [map_sum]
                apply Finset.sum_congr rfl
                intro i _
                exact (TensorProduct.comm_tmul ℂ (J.Fiber z.proj) (K.Fiber z.proj) _ _).symm }
          let e := f.toIso (fun x ↦ (c x).bijective)
          refine ⟨e, ?_⟩
          intro x v w
          change c x (v ⊗ₜ[ℂ] w) = w ⊗ₜ[ℂ] v
          exact TensorProduct.comm_tmul ℂ _ _ v w
        -- The inverse associator has a trivial first factor, so coefficient slices suffice.
        have assocCompare (n : ℕ) (J K : FiniteBundle (X × Y)) :
            ∃ e : Iso (((FiniteBundle.trivial (X × Y) n).tensor J).tensor K).Fiber
                ((FiniteBundle.trivial (X × Y) n).tensor (J.tensor K)).Fiber,
              ∀ (x : (X × Y)) (u : Fin n → ℂ) (v : J.Fiber x) (w : K.Fiber x),
                e.linearEquiv x ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          let A := (FiniteBundle.trivial (X × Y) n).tensor (J.tensor K)
          let B := ((FiniteBundle.trivial (X × Y) n).tensor J).tensor K
          let c (x : (X × Y)) := (TensorProduct.assoc ℂ (Fin n → ℂ) (J.Fiber x) (K.Fiber x)).symm
          let f : Hom A.Fiber B.Fiber :=
            { linearMap x := (c x).toLinearMap
              continuous_total := by
                apply hcoeff n (J.tensor K) B
                  (fun x ↦ (c x).toLinearMap)
                intro i
                let j : Hom J.Fiber ((FiniteBundle.trivial (X × Y) n).tensor J).Fiber :=
                  { linearMap x := TensorProduct.mk ℂ (Fin n → ℂ) (J.Fiber x) (Pi.single i 1)
                    continuous_total := hpure n J (Pi.single i 1) }
                have hj := (j.tensor (Hom.id K.Fiber)).continuous_total
                apply hj.congr
                intro z
                apply congrArg (fun t : B.Fiber z.proj ↦ (⟨z.proj, t⟩ : TotalSpace Unit B.Fiber))
                change TensorProduct.map (j.linearMap z.proj) LinearMap.id z.snd =
                  c z.proj (Pi.single i 1 ⊗ₜ[ℂ] z.snd)
                induction z.snd using TensorProduct.inductionOn with
                | tmul v w =>
                  simp only [j, c, TensorProduct.map_tmul, TensorProduct.mk_apply,
                    LinearMap.id_apply, TensorProduct.assoc_symm_tmul]
                | add s t hs ht =>
                  simp only [map_add, TensorProduct.tmul_add, hs, ht] }
          let d := f.toIso (fun x ↦ (c x).bijective)
          refine ⟨d.symm, ?_⟩
          intro x u v w
          apply (d.linearEquiv x).injective
          change d.linearEquiv x ((d.linearEquiv x).symm ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w)) =
            c x (u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w))
          rw [LinearEquiv.apply_symm_apply]
          exact (TensorProduct.assoc_symm_tmul u v w).symm
        constructor
        · exact assocCompare n E F
        · obtain ⟨s, hs⟩ := commCompare E ((FiniteBundle.trivial (X × Y) n).tensor F)
          obtain ⟨a, ha⟩ := assocCompare n F E
          obtain ⟨t, ht⟩ := commCompare F E
          let q := (Iso.refl (FiniteBundle.trivial (X × Y) n).Fiber).tensor t
          refine ⟨s.trans (a.trans q), ?_⟩
          intro x v u w
          change q.linearEquiv x (a.linearEquiv x (s.linearEquiv x
            (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)))) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)
          rw [hs, ha]
          change TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) (t.linearEquiv x)
            (u ⊗ₜ[ℂ] (w ⊗ₜ[ℂ] v)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w)
          simp only [TensorProduct.congr_tmul, LinearEquiv.refl_apply, ht]
      -- Pullback of the coefficient bundle keeps the supplied coordinate vector.
      have pullbackCompareX
          (n : ℕ) (f : C((X × Y), X)) (J : FiniteBundle X) :
          ∃ e : Iso (((FiniteBundle.trivial X n).tensor J).pullback f).Fiber
              ((FiniteBundle.trivial (X × Y) n).tensor (J.pullback f)).Fiber,
            ∀ (y : (X × Y)) (t : (Fin n → ℂ) ⊗[ℂ] J.Fiber (f y)), e.linearEquiv y t = t := by
        let e := (pullbackTensorIso (E := (FiniteBundle.trivial X n).Fiber)
          (F := J.Fiber) f).trans
            ((pullbackTrivialIso f n).tensor (Iso.refl (J.pullback f).Fiber))
        refine ⟨e, ?_⟩
        intro y t
        have hm : ((e.linearEquiv y).toLinearMap) = LinearMap.id := by
          apply TensorProduct.ext'
          intro u v
          change (pullbackTrivialIso f n).linearEquiv y u ⊗ₜ[ℂ] v = u ⊗ₜ[ℂ] v
          rw [pullbackTrivialIso_apply]
        exact DFunLike.congr_fun hm t
      have pullbackCompareY
          (n : ℕ) (f : C((X × Y), Y)) (J : FiniteBundle Y) :
          ∃ e : Iso (((FiniteBundle.trivial Y n).tensor J).pullback f).Fiber
              ((FiniteBundle.trivial (X × Y) n).tensor (J.pullback f)).Fiber,
            ∀ (y : (X × Y)) (t : (Fin n → ℂ) ⊗[ℂ] J.Fiber (f y)), e.linearEquiv y t = t := by
        let e := (pullbackTensorIso (E := (FiniteBundle.trivial Y n).Fiber)
          (F := J.Fiber) f).trans
            ((pullbackTrivialIso f n).tensor (Iso.refl (J.pullback f).Fiber))
        refine ⟨e, ?_⟩
        intro y t
        have hm : ((e.linearEquiv y).toLinearMap) = LinearMap.id := by
          apply TensorProduct.ext'
          intro u v
          change (pullbackTrivialIso f n).linearEquiv y u ⊗ₜ[ℂ] v = u ⊗ₜ[ℂ] v
          rw [pullbackTrivialIso_apply]
        exact DFunLike.congr_fun hm t
      constructor
      · obtain ⟨p, hp⟩ := pullbackCompareX ρ.dimension
          (ContinuousMap.fst : C(X × Y, X)) J
        obtain ⟨a, ha⟩ := (comparisons ρ.dimension
          (J.pullback (ContinuousMap.fst : C(X × Y, X)))
          (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).1
        let e := (p.tensor (Iso.refl (K.pullback ContinuousMap.snd).Fiber)).trans a
        have he (z : X × Y) (u : Fin ρ.dimension → ℂ) (v : J.Fiber z.1)
            (w : K.Fiber z.2) :
            e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          change a.linearEquiv z (p.linearEquiv z (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w) = _
          rw [hp]
          exact ha z u v w
        refine ⟨e, he, ?_⟩
        intro g z t
        let L := (e.linearEquiv (g • z)).toLinearMap.comp
              (((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).pullback
                ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap g z)
        let R := (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z).comp
              (e.linearEquiv z).toLinearMap
        have hm : L = R := by
          apply TensorProduct.ext'
          intro s w
          induction s using TensorProduct.inductionOn with
          | tmul u v =>
            change e.linearEquiv (g • z)
              (((ρ.representation g) u ⊗ₜ[ℂ] α.linearMap g z.1 v) ⊗ₜ[ℂ]
                β.linearMap g z.2 w) =
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
                ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z)
                    (e.linearEquiv z ((u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] w))
            rw [he, he]
            rfl
          | add s t hs ht =>
            have hsplit : (s + t) ⊗ₜ[ℂ] w = s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w :=
              TensorProduct.add_tmul s t w
            calc
              L ((s + t) ⊗ₜ[ℂ] w) = L (s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w) := congrArg L hsplit
              _ = L (s ⊗ₜ[ℂ] w) + L (t ⊗ₜ[ℂ] w) := L.map_add _ _
              _ = R (s ⊗ₜ[ℂ] w) + R (t ⊗ₜ[ℂ] w) := congrArg₂ (· + ·) hs ht
              _ = R (s ⊗ₜ[ℂ] w + t ⊗ₜ[ℂ] w) := (R.map_add _ _).symm
              _ = R ((s + t) ⊗ₜ[ℂ] w) := congrArg R hsplit.symm
        exact DFunLike.congr_fun hm t
      · obtain ⟨p, hp⟩ := pullbackCompareY ρ.dimension
          (ContinuousMap.snd : C(X × Y, Y)) K
        obtain ⟨a, ha⟩ := (comparisons ρ.dimension
          (J.pullback (ContinuousMap.fst : C(X × Y, X)))
          (K.pullback (ContinuousMap.snd : C(X × Y, Y)))).2
        let e := ((Iso.refl (J.pullback ContinuousMap.fst).Fiber).tensor p).trans a
        have he (z : X × Y) (v : J.Fiber z.1) (u : Fin ρ.dimension → ℂ)
            (w : K.Fiber z.2) :
            e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)) = u ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] w) := by
          change a.linearEquiv z (v ⊗ₜ[ℂ] p.linearEquiv z (u ⊗ₜ[ℂ] w)) = _
          rw [hp]
          exact ha z v u w
        refine ⟨e, he, ?_⟩
        intro g z t
        let L := (e.linearEquiv (g • z)).toLinearMap.comp
              (((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (((EquivariantStructure.ofFiniteRepresentation ρ).tensor β).pullback
                  ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap g z)
        let R := (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
              ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z).comp
              (e.linearEquiv z).toLinearMap
        have hm : L = R := by
          apply TensorProduct.ext'
          intro v s
          induction s using TensorProduct.inductionOn with
          | tmul u w =>
            change e.linearEquiv (g • z)
              (α.linearMap g z.1 v ⊗ₜ[ℂ] ((ρ.representation g) u ⊗ₜ[ℂ]
                β.linearMap g z.2 w)) =
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor
                ((α.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                  (β.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))).linearMap g z)
                    (e.linearEquiv z (v ⊗ₜ[ℂ] (u ⊗ₜ[ℂ] w)))
            rw [he, he]
            rfl
          | add s t hs ht =>
            have hsplit : v ⊗ₜ[ℂ] (s + t) = v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t :=
              TensorProduct.tmul_add v s t
            calc
              L (v ⊗ₜ[ℂ] (s + t)) = L (v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t) := congrArg L hsplit
              _ = L (v ⊗ₜ[ℂ] s) + L (v ⊗ₜ[ℂ] t) := L.map_add _ _
              _ = R (v ⊗ₜ[ℂ] s) + R (v ⊗ₜ[ℂ] t) := congrArg₂ (· + ·) hs ht
              _ = R (v ⊗ₜ[ℂ] s + v ⊗ₜ[ℂ] t) := (R.map_add _ _).symm
              _ = R (v ⊗ₜ[ℂ] (s + t)) := congrArg R hsplit.symm
        exact DFunLike.congr_fun hm t
    have combine (ρ : FiniteContinuousRepresentation G)
        (J K A B : FiniteBundle (X × Y))
        (σJ : EquivariantStructure G J.Fiber) (σK : EquivariantStructure G K.Fiber)
        (α : EquivariantStructure G A.Fiber) (β : EquivariantStructure G B.Fiber)
        (c : Iso J.Fiber ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor A).Fiber)
        (d : Iso K.Fiber ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor B).Fiber)
        (hc : c.IsEquivariant σJ ((EquivariantStructure.ofFiniteRepresentation ρ).tensor α))
        (hd : d.IsEquivariant σK ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)) :
        ∃ e : Iso (J.sum K).Fiber
          ((FiniteBundle.trivial (X × Y) ρ.dimension).tensor (A.sum B)).Fiber,
          (∀ (x : (X × Y)) (u : Fin ρ.dimension → ℂ) (v : A.Fiber x) (w : B.Fiber x)
              (s : J.Fiber x) (t : K.Fiber x),
            c.linearEquiv x s = u ⊗ₜ[ℂ] v → d.linearEquiv x t = u ⊗ₜ[ℂ] w →
              e.linearEquiv x (s, t) = u ⊗ₜ[ℂ] (v, w)) ∧
          e.IsEquivariant (σJ.sum σK)
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)) := by
      let V := FiniteBundle.trivial (X × Y) ρ.dimension
      -- Native projections give the actual coefficient distributivity map.
      let p : Hom (V.tensor (A.sum B)).Fiber (V.tensor A).Fiber :=
        (Iso.refl V.Fiber).toHom.tensor (sumFst (E := A.Fiber) (F := B.Fiber))
      let q : Hom (V.tensor (A.sum B)).Fiber (V.tensor B).Fiber :=
        (Iso.refl V.Fiber).toHom.tensor (sumSnd (E := A.Fiber) (F := B.Fiber))
      let D (x : (X × Y)) := TensorProduct.prodRight ℂ ℂ (V.Fiber x) (A.Fiber x) (B.Fiber x)
      have hvalue (x : (X × Y)) (t : (V.tensor (A.sum B)).Fiber x) :
          D x t = (p.linearMap x t, q.linearMap x t) := by
        have hm : (D x).toLinearMap = (p.linearMap x).prod (q.linearMap x) := by
          apply TensorProduct.ext'
          intro u v
          rfl
        exact DFunLike.congr_fun hm t
      let f : Hom (V.tensor (A.sum B)).Fiber ((V.tensor A).sum (V.tensor B)).Fiber :=
        { linearMap x := (D x).toLinearMap
          continuous_total := by
            apply continuous_induced_rng.mpr
            apply (p.continuous_total.prodMk q.continuous_total).congr
            intro z
            exact congrArg (fun w ↦
              ((⟨z.proj, w.1⟩ : TotalSpace Unit (V.tensor A).Fiber),
                (⟨z.proj, w.2⟩ : TotalSpace Unit (V.tensor B).Fiber)))
                  (hvalue z.proj z.snd).symm }
      let δ := f.toIso (fun x ↦ (D x).bijective)
      let e := (c.sum d).trans δ.symm
      refine ⟨e, ?_, ?_⟩
      · intro x u v w s t hs ht
        apply (δ.linearEquiv x).injective
        change δ.linearEquiv x ((δ.linearEquiv x).symm
          (c.linearEquiv x s, d.linearEquiv x t)) = δ.linearEquiv x (u ⊗ₜ[ℂ] (v, w))
        rw [LinearEquiv.apply_symm_apply]
        change (c.linearEquiv x s, d.linearEquiv x t) = (u ⊗ₜ[ℂ] v, u ⊗ₜ[ℂ] w)
        exact Prod.ext hs ht
      · intro g x t
        -- The same distributivity and corner maps intertwine the supplied actions.
        have hnat : (δ.linearEquiv (g • x)).toLinearMap.comp
              (((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)).linearMap g x) =
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).sum
              ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)).linearMap g x).comp
                (δ.linearEquiv x).toLinearMap := by
          apply TensorProduct.ext'
          intro u v
          rfl
        have h := DFunLike.congr_fun hnat
          ((δ.linearEquiv x).symm (c.linearEquiv x t.1, d.linearEquiv x t.2))
        apply (δ.linearEquiv (g • x)).injective
        change δ.linearEquiv (g • x) ((δ.linearEquiv (g • x)).symm
            (c.linearEquiv (g • x) (σJ.linearMap g x t.1),
              d.linearEquiv (g • x) (σK.linearMap g x t.2))) =
          δ.linearEquiv (g • x)
            ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor (α.sum β)).linearMap g x)
              ((δ.linearEquiv x).symm (c.linearEquiv x t.1, d.linearEquiv x t.2)))
        rw [LinearEquiv.apply_symm_apply]
        have hcancel := congrArg
          ((((EquivariantStructure.ofFiniteRepresentation ρ).tensor α).sum
            ((EquivariantStructure.ofFiniteRepresentation ρ).tensor β)).linearMap g x)
          ((δ.linearEquiv x).apply_symm_apply (c.linearEquiv x t.1, d.linearEquiv x t.2))
        exact (Prod.ext (hc g x t.1) (hd g x t.2)).trans (h.trans hcancel).symm
    have cutoff (n : ℕ) (E F : FiniteBundle Y)
        (a : CompactSupportTriple E.Fiber F.Fiber) :
        (∀ (c : C(Y, unitInterval)) (x : Y) (u : Fin n → ℂ) (v : E.Fiber x),
          (a.tensorLeft (FiniteBundle.trivial Y n).Fiber).cutoffLinearMap c x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.cutoffLinearMap c x v) ∧
        ∀ (c : C(Y, unitInterval)) (x : Y) (u : Fin n → ℂ) (v : F.Fiber x),
          (a.tensorLeft (FiniteBundle.trivial Y n).Fiber).inverse.cutoffLinearMap c x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.inverse.cutoffLinearMap c x v := by
      classical
      have hforward (x : (a.controlᶜ : Set Y)) (u : Fin n → ℂ) (v : E.Fiber x) :
          (a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv x
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] a.boundary.linearEquiv x v :=
        RelativeTriple.tensorLeft_tmul (FiniteBundle.trivial Y n).Fiber a.boundary x u v
      have hinverse (x : (a.controlᶜ : Set Y)) (u : Fin n → ℂ) (v : F.Fiber x) :
          ((a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv x).symm
            (u ⊗ₜ[ℂ] v) = u ⊗ₜ[ℂ] (a.boundary.linearEquiv x).symm v := by
        apply ((a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv x).injective
        exact (LinearEquiv.apply_symm_apply
          ((a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv x) _).trans
            ((hforward x u ((a.boundary.linearEquiv x).symm v)).trans
              (congrArg (fun w ↦ u ⊗ₜ[ℂ] w)
                ((a.boundary.linearEquiv x).apply_symm_apply v))).symm
      constructor
      · intro c x u v
        dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.tensorLeft]
        split_ifs with hx
        · simp
        · change (((c x : ℝ) : ℂ)) •
              (a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv
                ⟨x, hx⟩ (u ⊗ₜ[ℂ] v) =
            u ⊗ₜ[ℂ] ((((c x : ℝ) : ℂ)) • a.boundary.linearEquiv ⟨x, hx⟩ v)
          exact (congrArg (fun w ↦ (((c x : ℝ) : ℂ)) • w)
            (hforward ⟨x, hx⟩ u v)).trans
              (TensorProduct.tmul_smul (R := ℂ) (N := F.Fiber x)
                (((c x : ℝ) : ℂ)) u (a.boundary.linearEquiv ⟨x, hx⟩ v)).symm
      · intro c x u v
        dsimp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          CompactSupportTriple.tensorLeft]
        split_ifs with hx
        · simp
        · change (((c x : ℝ) : ℂ)) •
              ((a.boundary.tensorLeft (FiniteBundle.trivial Y n).Fiber).linearEquiv
                ⟨x, hx⟩).symm (u ⊗ₜ[ℂ] v) =
            u ⊗ₜ[ℂ] ((((c x : ℝ) : ℂ)) • (a.boundary.linearEquiv ⟨x, hx⟩).symm v)
          exact (congrArg (fun w ↦ (((c x : ℝ) : ℂ)) • w)
            (hinverse ⟨x, hx⟩ u v)).trans
              (TensorProduct.tmul_smul (R := ℂ) (N := E.Fiber x)
                (((c x : ℝ) : ℂ)) u ((a.boundary.linearEquiv ⟨x, hx⟩).symm v)).symm
    -- Fix the exact product, representation tensor and common compact control.
    let P := supportedEquivariantExternalProductTriple a b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    let S := supportedEquivariantExternalProductTriple a (b.tensorRepresentation θ)
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    let T := P.tensorRepresentation θ
    let A₀₀ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₁₁ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₁₀ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let A₀₁ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      (b.1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₀₀ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      ((b.tensorRepresentation θ).1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₁₁ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      ((b.tensorRepresentation θ).1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₁₀ := (a.1.target.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      ((b.tensorRepresentation θ).1.source.pullback (ContinuousMap.snd : C(X × Y, Y)))
    let B₀₁ := (a.1.source.pullback (ContinuousMap.fst : C(X × Y, X))).tensor
      ((b.tensorRepresentation θ).1.target.pullback (ContinuousMap.snd : C(X × Y, Y)))
    obtain ⟨c₀₀, hc₀₀, ec₀₀⟩ :=
      (corners θ a.1.source b.1.source a.2.sourceAction b.2.sourceAction).2
    obtain ⟨c₁₁, hc₁₁, ec₁₁⟩ :=
      (corners θ a.1.target b.1.target a.2.targetAction b.2.targetAction).2
    obtain ⟨c₁₀, hc₁₀, ec₁₀⟩ :=
      (corners θ a.1.target b.1.source a.2.targetAction b.2.sourceAction).2
    obtain ⟨c₀₁, hc₀₁, ec₀₁⟩ :=
      (corners θ a.1.source b.1.target a.2.sourceAction b.2.targetAction).2
    obtain ⟨u, hu, hueq⟩ := combine θ B₀₀ B₁₁ A₀₀ A₁₁
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (((EquivariantStructure.ofFiniteRepresentation θ).tensor b.2.sourceAction).pullback
          ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (((EquivariantStructure.ofFiniteRepresentation θ).tensor b.2.targetAction).pullback
          ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      c₀₀ c₁₁ ec₀₀ ec₁₁
    obtain ⟨v, hv, hveq⟩ := combine θ B₁₀ B₀₁ A₁₀ A₀₁
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (((EquivariantStructure.ofFiniteRepresentation θ).tensor b.2.sourceAction).pullback
          ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (((EquivariantStructure.ofFiniteRepresentation θ).tensor b.2.targetAction).pullback
          ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
      c₁₀ c₀₁ ec₁₀ ec₀₁
    -- One invariant compact product is used on both sides of the actual square.
    apply equivariantSupportTripleKZero_generator_relations.1 S T
    refine ⟨L ×ˢ M, hL.prod hM,
      (fun g z ↦ and_congr (hLinv g z.1) (hMinv g z.2)),
      Set.Subset.refl _, Set.Subset.refl _, u, v, hueq, hveq, ?_⟩
    intro z s
    -- Compare global fiber maps before restricting to this compact exterior.
    let B := reciprocalTensorSymbol
      (a.1.datum.cutoffLinearMap ρ z.val.1)
      (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
      (b.1.datum.cutoffLinearMap τ z.val.2)
      (b.1.datum.inverse.cutoffLinearMap τ z.val.2)
    let C := reciprocalTensorSymbol
      (a.1.datum.cutoffLinearMap ρ z.val.1)
      (a.1.datum.inverse.cutoffLinearMap ρ z.val.1)
      ((b.tensorRepresentation θ).1.datum.cutoffLinearMap τ z.val.2)
      ((b.tensorRepresentation θ).1.datum.inverse.cutoffLinearMap τ z.val.2)
    have hcut := cutoff θ.dimension b.1.source b.1.target b.1.datum
    have hE (t : Fin θ.dimension → ℂ) (w : b.1.source.Fiber z.val.2) :
        (b.tensorRepresentation θ).1.datum.cutoffLinearMap τ z.val.2 (t ⊗ₜ[ℂ] w) =
          t ⊗ₜ[ℂ] b.1.datum.cutoffLinearMap τ z.val.2 w :=
      hcut.1 τ z.val.2 t w
    have hE' (t : Fin θ.dimension → ℂ) (w : b.1.target.Fiber z.val.2) :
        (b.tensorRepresentation θ).1.datum.inverse.cutoffLinearMap τ z.val.2 (t ⊗ₜ[ℂ] w) =
          t ⊗ₜ[ℂ] b.1.datum.inverse.cutoffLinearMap τ z.val.2 w :=
      hcut.2 τ z.val.2 t w
    let l := (v.linearEquiv z).toLinearMap.comp C
    let r := (TensorProduct.map (LinearMap.id : (Fin θ.dimension → ℂ) →ₗ[ℂ] _) B).comp
      (u.linearEquiv z).toLinearMap
    have hm : l = r := by
      apply LinearMap.prod_ext
      · apply TensorProduct.ext'
        intro q w
        induction w using TensorProduct.inductionOn with
        | tmul t w =>
          change v.linearEquiv z (C (q ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] w), 0)) =
            TensorProduct.map LinearMap.id B (u.linearEquiv z (q ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] w), 0))
          simp only [C, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
            map_zero, add_zero]
          erw [hE]
          erw [hv z.val t _ _ _ _ (hc₁₀ z.val _ t w) (hc₀₁ z.val q t _)]
          erw [hu z.val t (q ⊗ₜ[ℂ] w) (0 : A₁₁.Fiber z.val) _ _ (hc₀₀ z.val q t w)
            (by simp only [map_zero, TensorProduct.tmul_zero])]
          simp [B, reciprocalTensorSymbol, Function.prod]
        | add w₁ w₂ h₁ h₂ =>
          have hsplit : q ⊗ₜ[ℂ] (w₁ + w₂) = q ⊗ₜ[ℂ] w₁ + q ⊗ₜ[ℂ] w₂ :=
            TensorProduct.tmul_add q w₁ w₂
          change l (q ⊗ₜ[ℂ] (w₁ + w₂), 0) = r (q ⊗ₜ[ℂ] (w₁ + w₂), 0)
          exact ((congrArg (fun t ↦ l (t, 0)) hsplit).trans
            ((l.map_add (q ⊗ₜ[ℂ] w₁, 0) (q ⊗ₜ[ℂ] w₂, 0)).trans
              ((congrArg₂ (· + ·) h₁ h₂).trans
                ((r.map_add (q ⊗ₜ[ℂ] w₁, 0) (q ⊗ₜ[ℂ] w₂, 0)).symm.trans
                  (congrArg (fun t ↦ r (t, 0)) hsplit).symm))))
      · apply TensorProduct.ext'
        intro q w
        induction w using TensorProduct.inductionOn with
        | tmul t w =>
          change v.linearEquiv z (C (0, q ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] w))) =
            TensorProduct.map LinearMap.id B (u.linearEquiv z (0, q ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] w)))
          simp only [C, reciprocalTensorSymbol, LinearMap.prod_apply, Function.prod,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.id_apply,
            map_zero, zero_add, LinearMap.neg_apply]
          erw [hE']
          have hneg : c₁₀.linearEquiv z.val
              (-(q ⊗ₜ[ℂ] (t ⊗ₜ[ℂ] (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w)))) =
              t ⊗ₜ[ℂ] (-(q ⊗ₜ[ℂ] (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w))) := by
            exact ((c₁₀.linearEquiv z.val).map_neg _).trans
              ((congrArg Neg.neg
                (hc₁₀ z.val q t (b.1.datum.inverse.cutoffLinearMap τ z.val.2 w))).trans
                  (TensorProduct.tmul_neg t _).symm)
          erw [hv z.val t _ _ _ _ hneg (hc₀₁ z.val _ t w)]
          erw [hu z.val t (0 : A₀₀.Fiber z.val) (q ⊗ₜ[ℂ] w) _ _
            (by simp only [map_zero, TensorProduct.tmul_zero])
            (hc₁₁ z.val q t w)]
          simp [B, reciprocalTensorSymbol, Function.prod]
        | add w₁ w₂ h₁ h₂ =>
          have hsplit : q ⊗ₜ[ℂ] (w₁ + w₂) = q ⊗ₜ[ℂ] w₁ + q ⊗ₜ[ℂ] w₂ :=
            TensorProduct.tmul_add q w₁ w₂
          change l (0, q ⊗ₜ[ℂ] (w₁ + w₂)) = r (0, q ⊗ₜ[ℂ] (w₁ + w₂))
          exact ((congrArg (fun t ↦ l (0, t)) hsplit).trans
            ((l.map_add (0, q ⊗ₜ[ℂ] w₁) (0, q ⊗ₜ[ℂ] w₂)).trans
              ((congrArg₂ (· + ·) h₁ h₂).trans
                ((r.map_add (0, q ⊗ₜ[ℂ] w₁) (0, q ⊗ₜ[ℂ] w₂)).symm.trans
                  (congrArg (fun t ↦ r (0, t)) hsplit).symm))))
    have hS : (S.1.datum.enlarge (L ×ˢ M) (hL.prod hM)
        (Set.Subset.refl _)).boundary.linearEquiv z s = C s :=
      (S.1.datum.enlarge_apply _ _ (Set.Subset.refl _) z s).trans rfl
    have hT : (T.1.datum.boundary.linearEquiv z).toLinearMap =
        TensorProduct.map (LinearMap.id : (Fin θ.dimension → ℂ) →ₗ[ℂ] _) B := by
      apply TensorProduct.ext'
      intro t q
      exact RelativeTriple.tensorLeft_tmul (FiniteBundle.trivial (X × Y) θ.dimension).Fiber
        P.1.datum.boundary z t q
    have hTenlarge := T.1.datum.enlarge_apply (L ×ˢ M) (hL.prod hM)
      (Set.Subset.refl _) z (u.linearEquiv z s)
    exact (congrArg (v.linearEquiv z.val) hS).trans
      ((DFunLike.congr_fun hm s).trans
        ((DFunLike.congr_fun hT (u.linearEquiv z s)).symm.trans hTenlarge.symm))
  -- Use one actual pair of invariant cutoffs for both representatives.
  have hfinite (θ : FiniteContinuousRepresentation G)
      (a : EquivariantSupportBundleTriple G X) (b : EquivariantSupportBundleTriple G Y) :
      μ a.kZeroClass (b.tensorRepresentation θ).kZeroClass =
        equivariantSupportRepresentationAction (finiteRepresentationClass θ)
          (μ a.kZeroClass b.kZeroClass) := by
    obtain ⟨U, hU, ha, _, L, hL, _, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
      exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
    obtain ⟨V, hV, hb, _, M, hM, _, hMinv, τ, hτinv, hτzero, hτone⟩ :=
      exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
    rw [hμ a (b.tensorRepresentation θ)
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv]
    rw [hμ a b ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv, equivariantSupportRepresentationAction_finiteClass]
    exact hclass θ a b ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
  have extX (f g : EquivariantSupportTripleKZero G X →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ a : EquivariantSupportBundleTriple G X, f a.kZeroClass = g a.kZeroClass) :
      f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have extY (f g : EquivariantSupportTripleKZero G Y →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ b : EquivariantSupportBundleTriple G Y, f b.kZeroClass = g b.kZeroClass) :
      f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  have extR (f g : RepresentationGrothendieckGroup G →+
      EquivariantSupportTripleKZero G (X × Y))
      (h : ∀ θ : FiniteContinuousRepresentation G,
        f (finiteRepresentationClass θ) = g (finiteRepresentationClass θ)) : f = g := by
    apply QuotientAddGroup.addMonoidHom_ext
    apply FreeAbelianGroup.lift_ext
    exact h
  let β := equivariantSupportRepresentationAction (G := G) (X := Y)
  let γ := equivariantSupportRepresentationAction (G := G) (X := X × Y)
  -- Keep the second factor's full coefficient through the same three presentations.
  have hY (θ : FiniteContinuousRepresentation G) (a : EquivariantSupportBundleTriple G X) :
      (μ a.kZeroClass).comp (β (finiteRepresentationClass θ)) =
        (γ (finiteRepresentationClass θ)).comp (μ a.kZeroClass) := by
    apply extY
    intro b
    change μ a.kZeroClass
      (equivariantSupportRepresentationAction (finiteRepresentationClass θ) b.kZeroClass) = _
    rw [equivariantSupportRepresentationAction_finiteClass]
    exact hfinite θ a b
  have hX (θ : FiniteContinuousRepresentation G) :
      μ.flip (β (finiteRepresentationClass θ) b) =
        (γ (finiteRepresentationClass θ)).comp (μ.flip b) := by
    apply extX
    intro a
    exact DFunLike.congr_fun (hY θ a) b
  have hR : (μ a).comp (β.flip b) = γ.flip (μ a b) := by
    apply extR
    intro θ
    exact DFunLike.congr_fun (hX θ) a
  exact DFunLike.congr_fun hR r

variable {X' Y' : Type*}
  [TopologicalSpace X'] [MulAction G X'] [ContinuousSMul G X']
  [LocallyCompactSpace X'] [T2Space X']
  [TopologicalSpace Y'] [MulAction G Y'] [ContinuousSMul G Y']
  [LocallyCompactSpace Y'] [T2Space Y']

set_option maxHeartbeats 600000 in
-- Retain the original iterated pullback topologies and the same moving-fiber transports.
/-- Proper equivariant pullbacks preserve the actual external product on the product base. -/
theorem equivariantSupportKZeroExternalProduct_pullback
    (f : C(X', X)) (k : C(Y', Y))
    (heq : ∀ (g : G) (x : X'), f (g • x) = g • f x)
    (keq : ∀ (g : G) (y : Y'), k (g • y) = g • k y)
    (hf : IsProperMap f) (hk : IsProperMap k)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Y) :
    equivariantSupportTripleKZeroPullback (f.prodMap k)
      (fun g z ↦ Prod.ext (heq g z.1) (keq g z.2)) (hf.prodMap hk)
      (equivariantSupportKZeroExternalProduct a b) =
        equivariantSupportKZeroExternalProduct
          (equivariantSupportTripleKZeroPullback f heq hf a)
          (equivariantSupportTripleKZeroPullback k keq hk b) := by
  /- Stage 1: compose each original invariant cutoff with its supplied map.
  The inverse images of its open zero neighborhood and compact enlarged control
  are admissible; properness supplies compactness. Equivariance of f and k
  makes these cutoffs and controls invariant for the original source actions.
  The product control is exactly the inverse image of L times M under f times k.
  Stage 2: the canonical pullback/tensor/sum comparisons retain all four vectors
  and the actual cutoff block. Their moving-fiber transports use the same heq
  and keq as the specified proper pullbacks, so they give an equivariant global
  square of the original product triples on that common exterior.
  Stage 3: use actual triple representatives and the two existing generator
  formulas. Only f and k are required proper; the bundle projections are not. -/
  -- Keep dependent topology comparisons local to this original proof.
  set_option backward.isDefEq.respectTransparency.types false in
    classical
    have tensor_comparison (f : C(X', X)) (k : C(Y', Y))
        (heq : ∀ (g : G) (x : X'), f (g • x) = g • f x)
        (keq : ∀ (g : G) (y : Y'), k (g • y) = g • k y)
        (E : FiniteBundle X) (F : FiniteBundle Y)
        (ρE : EquivariantStructure G E.Fiber) (ρF : EquivariantStructure G F.Fiber) :
        ∃ e : Iso
          ((((E.pullback ContinuousMap.fst).tensor
            (F.pullback ContinuousMap.snd)).pullback (f.prodMap k)).Fiber)
          (((E.pullback f).pullback ContinuousMap.fst).tensor
            ((F.pullback k).pullback ContinuousMap.snd)).Fiber,
          (∀ z v, e.linearEquiv z v = v) ∧
            e.IsEquivariant
              (((ρE.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                (ρF.pullback ContinuousMap.snd (fun _ _ ↦ rfl))).pullback (f.prodMap k)
                  (fun g z ↦ Prod.ext (heq g z.1) (keq g z.2)))
              (((ρE.pullback f heq).pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
                ((ρF.pullback k keq).pullback ContinuousMap.snd (fun _ _ ↦ rfl))) := by
      let p : C(X × Y, X) := ContinuousMap.fst
      let q : C(X × Y, Y) := ContinuousMap.snd
      let p' : C(X' × Y', X') := ContinuousMap.fst
      let q' : C(X' × Y', Y') := ContinuousMap.snd
      let h : C(X' × Y', X × Y) := f.prodMap k
      -- Compare the two actual iterated pullback topologies using the same vectors.
      let eE : Iso (((E.pullback p).pullback h).Fiber)
          (((E.pullback f).pullback p').Fiber) :=
        (pullbackCompIso (E := E.Fiber) p h).trans
          (pullbackCompIso (E := E.Fiber) f p').symm
      let eF : Iso (((F.pullback q).pullback h).Fiber)
          (((F.pullback k).pullback q').Fiber) :=
        (pullbackCompIso (E := F.Fiber) q h).trans
          (pullbackCompIso (E := F.Fiber) k q').symm
      have hE (z : X' × Y') (v : E.Fiber (f z.1)) : eE.linearEquiv z v = v := by
        apply (pullbackCompIso (E := E.Fiber) f p').linearEquiv z |>.injective
        change (pullbackCompIso (E := E.Fiber) f p').linearEquiv z
          (((pullbackCompIso (E := E.Fiber) f p').linearEquiv z).symm
            ((pullbackCompIso (E := E.Fiber) p h).linearEquiv z v)) = _
        rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
      have hF (z : X' × Y') (v : F.Fiber (k z.2)) : eF.linearEquiv z v = v := by
        apply (pullbackCompIso (E := F.Fiber) k q').linearEquiv z |>.injective
        change (pullbackCompIso (E := F.Fiber) k q').linearEquiv z
          (((pullbackCompIso (E := F.Fiber) k q').linearEquiv z).symm
            ((pullbackCompIso (E := F.Fiber) q h).linearEquiv z v)) = _
        rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
      let e := (pullbackTensorIso (E := (E.pullback p).Fiber)
        (F := (F.pullback q).Fiber) h).trans (eE.tensor eF)
      have he (z : X' × Y') (v : E.Fiber (f z.1) ⊗[ℂ] F.Fiber (k z.2)) :
          e.linearEquiv z v = v := by
        change TensorProduct.congr (eE.linearEquiv z) (eF.linearEquiv z) v = v
        have hmap : (TensorProduct.congr (eE.linearEquiv z) (eF.linearEquiv z)).toLinearMap =
            LinearMap.id := by
          apply TensorProduct.ext'
          intro u w
          simp only [LinearEquiv.coe_coe, TensorProduct.congr_tmul, hE, hF]
          rfl
        exact LinearMap.congr_fun hmap v
      refine ⟨e, he, ?_⟩
      intro g z v
      change e.linearEquiv (g • z) _ =
        ((((ρE.pullback f heq).pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          ((ρF.pullback k keq).pullback ContinuousMap.snd (fun _ _ ↦ rfl))).linearMap
          g z (e.linearEquiv z v))
      rw [he, he]
      -- Split transport along the same supplied product equality into its two factors.
      have htransport (x₀ x₁ : X) (y₀ y₁ : Y) (hx : x₀ = x₁) (hy : y₀ = y₁)
          (A : E.Fiber (f z.1) →ₗ[ℂ] E.Fiber x₁)
          (B : F.Fiber (k z.2) →ₗ[ℂ] F.Fiber y₁) :
          (Eq.mpr (congrArg
            (fun w : X × Y ↦ (E.Fiber (f z.1) ⊗[ℂ] F.Fiber (k z.2)) →ₗ[ℂ]
              (E.Fiber w.1 ⊗[ℂ] F.Fiber w.2))
                (show (x₀, y₀) = (x₁, y₁) from Prod.ext hx hy)) (TensorProduct.map A B)) v =
            TensorProduct.map
              (Eq.mpr (congrArg (fun x ↦ E.Fiber (f z.1) →ₗ[ℂ] E.Fiber x) hx) A)
              (Eq.mpr (congrArg (fun y ↦ F.Fiber (k z.2) →ₗ[ℂ] F.Fiber y) hy) B) v := by
        subst x₁
        subst y₁
        rfl
      exact htransport (f (g • z.1)) (g • f z.1) (k (g • z.2)) (g • k z.2)
        (heq g z.1) (keq g z.2) (ρE.linearMap g (f z.1)) (ρF.linearMap g (k z.2))
    have sum_comparison (f : C((X' × Y'), (X × Y)))
        (heq : ∀ (g : G) (w : (X' × Y')), f (g • w) = g • f w)
        (J K : FiniteBundle (X × Y)) (ρJ : EquivariantStructure G J.Fiber)
        (ρK : EquivariantStructure G K.Fiber) :
        ∃ e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber,
          (∀ w v, e.linearEquiv w v = v) ∧
            e.IsEquivariant ((ρJ.sum ρK).pullback f heq)
              ((ρJ.pullback f heq).sum (ρK.pullback f heq)) := by
      -- This comparison is identity on vectors in both native sum/pullback topologies.
      let e : Iso ((J.sum K).pullback f).Fiber ((J.pullback f).sum (K.pullback f)).Fiber :=
        { linearEquiv w := LinearEquiv.refl ℂ (J.Fiber (f w) × K.Fiber (f w))
          continuous_total := by
            apply continuous_induced_rng.mpr
            apply Continuous.prodMk
            · rw [(inducing_pullbackTotalSpaceEmbedding Unit J.Fiber f).continuous_iff]
              exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
                (continuous_sum_fst.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
            · rw [(inducing_pullbackTotalSpaceEmbedding Unit K.Fiber f).continuous_iff]
              exact (Pullback.continuous_proj Unit (J.sum K).Fiber f).prodMk
                (continuous_sum_snd.comp (Pullback.continuous_lift Unit (J.sum K).Fiber f))
          continuous_symm := by
            rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.sum K).Fiber f).continuous_iff]
            apply ((Pullback.continuous_proj Unit J.Fiber f).comp continuous_sum_fst).prodMk
            apply continuous_induced_rng.mpr
            exact ((Pullback.continuous_lift Unit J.Fiber f).comp continuous_sum_fst).prodMk
              ((Pullback.continuous_lift Unit K.Fiber f).comp continuous_sum_snd) }
      refine ⟨e, (fun _ _ ↦ rfl), ?_⟩
      intro g w v
      -- The supplied base equality transports both original sum factors together.
      have htransport (x z : (X × Y)) (hxz : x = z)
          (LJ : J.Fiber (f w) →ₗ[ℂ] J.Fiber z)
          (LK : K.Fiber (f w) →ₗ[ℂ] K.Fiber z) :
          (Eq.mpr (congrArg (fun b ↦ (J.Fiber (f w) × K.Fiber (f w)) →ₗ[ℂ]
            (J.Fiber b × K.Fiber b)) hxz) (LJ.prodMap LK)) v =
          ((Eq.mpr (congrArg (fun b ↦ J.Fiber (f w) →ₗ[ℂ] J.Fiber b) hxz) LJ) v.1,
            (Eq.mpr (congrArg (fun b ↦ K.Fiber (f w) →ₗ[ℂ] K.Fiber b) hxz) LK) v.2) := by
        subst z
        rfl
      exact htransport (f (g • w)) (g • f w) (heq g w)
        (ρJ.linearMap g (f w)) (ρK.linearMap g (f w))
    have hcutoffX (J K : FiniteBundle X) (a : CompactSupportTriple J.Fiber K.Fiber)
        (f : C(X', X)) (hf : IsProperMap f) (ρ : C(X, I)) (x : X') :
        (a.pullback f hf).cutoffLinearMap (ρ.comp f) x = a.cutoffLinearMap ρ (f x) ∧
          (a.pullback f hf).inverse.cutoffLinearMap (ρ.comp f) x =
            a.inverse.cutoffLinearMap ρ (f x) := by
      classical
      by_cases hx : f x ∈ a.control
      · constructor <;>
          simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.pullback,
            CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_true]
          <;> rfl
      · have hb : (a.boundary.pullback f).linearEquiv ⟨x, hx⟩ =
            a.boundary.linearEquiv ⟨f x, hx⟩ := by
          apply LinearEquiv.ext
          intro v
          exact RelativeTriple.pullback_apply a.boundary f ⟨x, hx⟩ v
        constructor <;>
          simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.pullback,
            CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_false]
        · change ((ρ (f x) : ℝ) : ℂ) •
            ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).toLinearMap = _
          rw [hb]
          rfl
        · change ((ρ (f x) : ℝ) : ℂ) •
            ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).symm.toLinearMap = _
          rw [hb]
          rfl
    have hcutoffY (J K : FiniteBundle Y) (a : CompactSupportTriple J.Fiber K.Fiber)
        (f : C(Y', Y)) (hf : IsProperMap f) (ρ : C(Y, I)) (x : Y') :
        (a.pullback f hf).cutoffLinearMap (ρ.comp f) x = a.cutoffLinearMap ρ (f x) ∧
          (a.pullback f hf).inverse.cutoffLinearMap (ρ.comp f) x =
            a.inverse.cutoffLinearMap ρ (f x) := by
      classical
      by_cases hx : f x ∈ a.control
      · constructor <;>
          simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.pullback,
            CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_true]
          <;> rfl
      · have hb : (a.boundary.pullback f).linearEquiv ⟨x, hx⟩ =
            a.boundary.linearEquiv ⟨f x, hx⟩ := by
          apply LinearEquiv.ext
          intro v
          exact RelativeTriple.pullback_apply a.boundary f ⟨x, hx⟩ v
        constructor <;>
          simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.pullback,
            CompactSupportTriple.inverse, Set.mem_preimage, hx, dite_false]
        · change ((ρ (f x) : ℝ) : ℂ) •
            ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).toLinearMap = _
          rw [hb]
          rfl
        · change ((ρ (f x) : ℝ) : ℂ) •
            ((a.boundary.pullback f).linearEquiv ⟨x, hx⟩).symm.toLinearMap = _
          rw [hb]
          rfl
    -- Every original support class has one actual equivariant triple representative.
    obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
    obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective b
    obtain ⟨U, hU, ha, _, L, hL, _, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
      exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
    obtain ⟨V, hV, hb, _, M, hM, _, hMinv, τ, hτinv, hτzero, hτone⟩ :=
      exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
    let h := f.prodMap k
    have hheq (g : G) (z : X' × Y') : h (g • z) = g • h z :=
      Prod.ext (heq g z.1) (keq g z.2)
    have hρinv' (g : G) (x : X') : (ρ.comp f) (g • x) = (ρ.comp f) x := by
      change ρ (f (g • x)) = ρ (f x)
      rw [heq g x, hρinv]
    have hτinv' (g : G) (y : Y') : (τ.comp k) (g • y) = (τ.comp k) y := by
      change τ (k (g • y)) = τ (k y)
      rw [keq g y, hτinv]
    have hLinv' (g : G) (x : X') : g • x ∈ f ⁻¹' L ↔ x ∈ f ⁻¹' L := by
      change f (g • x) ∈ L ↔ f x ∈ L
      rw [heq g x]
      exact hLinv g (f x)
    have hMinv' (g : G) (y : Y') : g • y ∈ k ⁻¹' M ↔ y ∈ k ⁻¹' M := by
      change k (g • y) ∈ M ↔ k y ∈ M
      rw [keq g y]
      exact hMinv g (k y)
    let c := supportedEquivariantExternalProductTriple a b
      ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
      hρinv hLinv hτinv hMinv
    let ap := a.pullback f heq hf
    let bp := b.pullback k keq hk
    let d := supportedEquivariantExternalProductTriple ap bp
      (ρ.comp f) (f ⁻¹' U) (hU.preimage f.continuous) (Set.preimage_mono ha)
      (fun x hx ↦ hρzero (f x) hx) (f ⁻¹' L) (hf.isCompact_preimage hL)
      (fun x hx ↦ hρone (f x) hx)
      (τ.comp k) (k ⁻¹' V) (hV.preimage k.continuous) (Set.preimage_mono hb)
      (fun y hy ↦ hτzero (k y) hy) (k ⁻¹' M) (hk.isCompact_preimage hM)
      (fun y hy ↦ hτone (k y) hy) hρinv' hLinv' hτinv' hMinv'
    let cp := c.pullback h hheq (hf.prodMap hk)
    have hleft : equivariantSupportTripleKZeroPullback h hheq (hf.prodMap hk)
        (equivariantSupportKZeroExternalProduct a.kZeroClass b.kZeroClass) = cp.kZeroClass := by
      rw [equivariantSupportKZeroExternalProduct_class a b
        ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
        hρinv hLinv hτinv hMinv, equivariantSupportTripleKZeroPullback_apply]
    have hright : equivariantSupportKZeroExternalProduct
        (equivariantSupportTripleKZeroPullback f heq hf a.kZeroClass)
        (equivariantSupportTripleKZeroPullback k keq hk b.kZeroClass) = d.kZeroClass := by
      rw [equivariantSupportTripleKZeroPullback_apply,
        equivariantSupportTripleKZeroPullback_apply]
      exact equivariantSupportKZeroExternalProduct_class ap bp
        (ρ.comp f) (f ⁻¹' U) (hU.preimage f.continuous) (Set.preimage_mono ha)
        (fun x hx ↦ hρzero (f x) hx) (f ⁻¹' L) (hf.isCompact_preimage hL)
        (fun x hx ↦ hρone (f x) hx)
        (τ.comp k) (k ⁻¹' V) (hV.preimage k.continuous) (Set.preimage_mono hb)
        (fun y hy ↦ hτzero (k y) hy) (k ⁻¹' M) (hk.isCompact_preimage hM)
        (fun y hy ↦ hτone (k y) hy) hρinv' hLinv' hτinv' hMinv'
    rw [hleft, hright]
    apply equivariantSupportTripleKZero_generator_relations.1 _ _
    -- The comparison uses the same four tensor factors, and each map fixes its vector.
    let J₀ := (a.1.source.pullback ContinuousMap.fst).tensor
      (b.1.source.pullback ContinuousMap.snd)
    let J₁ := (a.1.target.pullback ContinuousMap.fst).tensor
      (b.1.target.pullback ContinuousMap.snd)
    let K₀ := (a.1.target.pullback ContinuousMap.fst).tensor
      (b.1.source.pullback ContinuousMap.snd)
    let K₁ := (a.1.source.pullback ContinuousMap.fst).tensor
      (b.1.target.pullback ContinuousMap.snd)
    let σ₀ := (a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let σ₁ := (a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let θ₀ := (a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    let θ₁ := (a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
    obtain ⟨s, hs, hsG⟩ := sum_comparison h hheq J₀ J₁ σ₀ σ₁
    obtain ⟨t, ht, htG⟩ := sum_comparison h hheq K₀ K₁ θ₀ θ₁
    obtain ⟨e₀₀, he₀₀, he₀₀G⟩ := tensor_comparison f k heq keq
      a.1.source b.1.source a.2.sourceAction b.2.sourceAction
    obtain ⟨e₁₁, he₁₁, he₁₁G⟩ := tensor_comparison f k heq keq
      a.1.target b.1.target a.2.targetAction b.2.targetAction
    obtain ⟨e₁₀, he₁₀, he₁₀G⟩ := tensor_comparison f k heq keq
      a.1.target b.1.source a.2.targetAction b.2.sourceAction
    obtain ⟨e₀₁, he₀₁, he₀₁G⟩ := tensor_comparison f k heq keq
      a.1.source b.1.target a.2.sourceAction b.2.targetAction
    let u : Iso cp.1.source.Fiber d.1.source.Fiber := s.trans (e₀₀.sum e₁₁)
    let v : Iso cp.1.target.Fiber d.1.target.Fiber := t.trans (e₁₀.sum e₀₁)
    have hu (z : X' × Y') (w : cp.1.source.Fiber z) : u.linearEquiv z w = w := by
      change (e₀₀.sum e₁₁).linearEquiv z (s.linearEquiv z w) = w
      rw [hs]
      exact Prod.ext (he₀₀ z w.1) (he₁₁ z w.2)
    have hv (z : X' × Y') (w : cp.1.target.Fiber z) : v.linearEquiv z w = w := by
      change (e₁₀.sum e₀₁).linearEquiv z (t.linearEquiv z w) = w
      rw [ht]
      exact Prod.ext (he₁₀ z w.1) (he₀₁ z w.2)
    let C := Set.prod (f ⁻¹' L) (k ⁻¹' M)
    have hC : IsCompact C := (hf.isCompact_preimage hL).prod (hk.isCompact_preimage hM)
    refine ⟨C, hC, fun g z ↦ and_congr (hLinv' g z.1) (hMinv' g z.2),
      Set.Subset.refl _, Set.Subset.refl _, u, v, ?_, ?_, ?_⟩
    · intro g z w
      exact (congrArg ((e₀₀.sum e₁₁).linearEquiv (g • z)) (hsG g z w)).trans
        (Prod.ext (he₀₀G g z (s.linearEquiv z w).1) (he₁₁G g z (s.linearEquiv z w).2))
    · intro g z w
      exact (congrArg ((e₁₀.sum e₀₁).linearEquiv (g • z)) (htG g z w)).trans
        (Prod.ext (he₁₀G g z (t.linearEquiv z w).1) (he₀₁G g z (t.linearEquiv z w).2))
    · -- All four pulled cutoff maps equal the old maps at the original product image.
      intro z w
      rw [hv, hu]
      have hl := cp.1.datum.enlarge_apply C hC (Set.Subset.refl _) z w
      have hp := RelativeTriple.pullback_apply c.1.datum.boundary h z w
      have hr := d.1.datum.enlarge_apply C hC (Set.Subset.refl _) z w
      apply (hl.trans hp).trans
      apply Eq.trans _ hr.symm
      change reciprocalTensorSymbol
        (a.1.datum.cutoffLinearMap ρ (f z.val.1))
        (a.1.datum.inverse.cutoffLinearMap ρ (f z.val.1))
        (b.1.datum.cutoffLinearMap τ (k z.val.2))
        (b.1.datum.inverse.cutoffLinearMap τ (k z.val.2)) w =
          reciprocalTensorSymbol
            ((a.1.datum.pullback f hf).cutoffLinearMap (ρ.comp f) z.val.1)
            ((a.1.datum.pullback f hf).inverse.cutoffLinearMap (ρ.comp f) z.val.1)
            ((b.1.datum.pullback k hk).cutoffLinearMap (τ.comp k) z.val.2)
            ((b.1.datum.pullback k hk).inverse.cutoffLinearMap (τ.comp k) z.val.2) w
      obtain ⟨ha₀, ha₁⟩ := hcutoffX a.1.source a.1.target a.1.datum f hf ρ z.val.1
      obtain ⟨hb₀, hb₁⟩ := hcutoffY b.1.source b.1.target b.1.datum k hk τ z.val.2
      rw [ha₀, ha₁, hb₀, hb₁]
      rfl

end AtiyahSinger.ComplexBundle
