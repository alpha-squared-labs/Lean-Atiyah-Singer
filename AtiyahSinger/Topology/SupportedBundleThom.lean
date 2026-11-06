/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ThomTensorSymbol
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.BundleThom
public import AtiyahSinger.Topology.CompactSupportContinuity
public import AtiyahSinger.Topology.ExteriorKoszulContinuity
public import AtiyahSinger.Topology.SupportKZeroComparison
public import AtiyahSinger.Topology.SupportTensorAction
public import AtiyahSinger.Topology.SupportTripleCutoff

/-!
# The actual Thom operator over a noncompact base

Public module ID: M2202.

SG C.13 and Karoubi IV.1.10--1.11 multiply a compact-support base class by the
fiberwise exterior symbol. The exterior symbol alone is not a compact-support
class when the base is noncompact. Here the input support triple is extended
using one cutoff for its boundary map and its inverse. Their graded tensor sum
with the original exterior symbol has a compact control: the zero section over
the enlarged compact base control, not the whole zero section.

The resulting map on the existing compact-support K groups is characterized on
every original support triple and every admissible cutoff. The three support
relations establish its descent to a homomorphism. Its
compact-base comparison retains the old exterior class and graph action.

The base is locally compact Hausdorff. The Thom bundle has a given jointly
continuous Hermitian pairing; metric existence is not inferred from local
compactness. The input support-triple bundles need no global Hermitian metric.
Thom bijectivity is proved in `SupportedThomIsomorphism`.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  exteriorTopology exteriorParityTopology isFiniteRank_exteriorParity isFiniteRank_pullback
  t2Space_totalSpace locallyCompactSpace_totalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  (E : X → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, InnerProductSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
  (hinner : Continuous (fun z : TotalSpace Unit (E ×ᵇ E) ↦ inner ℂ z.snd.1 z.snd.2))
  (a : SupportBundleTriple X)

local notation "Even" => fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0
local notation "Odd" => fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1
local notation "Source" => fun x : X ↦
  (a.source.Fiber x ⊗[ℂ] Even x) × (a.target.Fiber x ⊗[ℂ] Odd x)
local notation "Target" => fun x : X ↦
  (a.target.Fiber x ⊗[ℂ] Even x) × (a.source.Fiber x ⊗[ℂ] Odd x)
local notation "PullSource" => (π Unit E) *ᵖ Source
local notation "PullTarget" => (π Unit E) *ᵖ Target

section Cutoff

variable (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
  (hcontrol : a.datum.control ⊆ U) (hzero : ∀ x ∈ U, ρ x = 0)
  (L : Set X) (hL : IsCompact L) (hone : ∀ x ∉ L, ρ x = 1)

local notation "Control" =>
  Set.ofPred (fun z : TotalSpace Unit E ↦
    Bundle.TotalSpace.proj z ∈ L ∧ Bundle.TotalSpace.snd z = 0)
local notation "d" => a.datum.cutoffLinearMap ρ
local notation "d'" => a.datum.inverse.cutoffLinearMap ρ

include hinner hU hcontrol hzero hL hone in
set_option linter.unusedSectionVars false in
/-- The tensor symbol and its explicit inverse are continuous off the compact zero control. -/
theorem supportedThom_symbol_properties :
    (∀ z : (Controlᶜ : Set (TotalSpace Unit E)),
      (ρ z.val.proj : ℝ) ^ 2 + ‖z.val.snd‖ ^ 2 ≠ 0) ∧
    Continuous (fun z : TotalSpace Unit (Restrict PullSource Controlᶜ) ↦
      (⟨z.proj, thomTensorSymbol (d z.proj.val.proj) (d' z.proj.val.proj)
        z.proj.val.snd z.snd⟩ : TotalSpace Unit (Restrict PullTarget Controlᶜ))) ∧
    Continuous (fun z : TotalSpace Unit (Restrict PullTarget Controlᶜ) ↦
      (⟨z.proj, thomTensorSymbolInverse (d z.proj.val.proj) (d' z.proj.val.proj)
        (ρ z.proj.val.proj : ℝ) z.proj.val.snd z.snd⟩ :
          TotalSpace Unit (Restrict PullSource Controlᶜ))) := by
  /- Stage 1: outside the zero control, either the fiber vector is nonzero or its
  base is outside L, where rho=1. Thus the same sum of squares never vanishes.
  Stage 2: the two original cutoff maps and the full Clifford symbol are continuous.
  Their tensor products, transported through the vector-preserving pullback/tensor
  comparisons, give precisely the four signed blocks of the forward symbol.
  Stage 3: restrict that map to the same complement. The already proved tensor
  inverse laws give its fiberwise bijectivity and identify its inverse with the
  specified reciprocal block. Apply finite-rank inverse continuity on the original
  bundle topology; no new inverse, metric or support control is selected. -/
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank PullSource := isFiniteRank_pullback (E := Source) p
  let : IsFiniteRank PullTarget := isFiniteRank_pullback (E := Target) p
  -- The same compact control excludes the joint zero of the cutoff and fiber vector.
  have hnonzero (z : (Controlᶜ : Set Z)) :
      (ρ z.val.proj : ℝ) ^ 2 + ‖z.val.snd‖ ^ 2 ≠ 0 := by
    by_cases hv : z.val.snd = 0
    · have hx : z.val.proj ∉ L := fun hx ↦ z.property ⟨hx, hv⟩
      rw [hone z.val.proj hx, hv]
      norm_num
    · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (norm_pos_iff.mpr hv)))
  let : IsFiniteRank (Restrict PullSource Controlᶜ) := isFiniteRank_restrict _
  let : IsFiniteRank (Restrict PullTarget Controlᶜ) := isFiniteRank_restrict _
  -- The original invertible boundary map has a continuous inverse on this same complement.
  have inverse_continuous
      (g : Hom (Restrict PullSource Controlᶜ) (Restrict PullTarget Controlᶜ))
      (j : ∀ z : (Controlᶜ : Set Z),
        (Restrict PullSource Controlᶜ) z ≃ₗ[ℂ] (Restrict PullTarget Controlᶜ) z)
      (hj : ∀ z, (j z).toLinearMap = g.linearMap z) :
      Continuous (fun z : TotalSpace Unit (Restrict PullTarget Controlᶜ) ↦
        (⟨z.proj, (j z.proj).symm z.snd⟩ :
          TotalSpace Unit (Restrict PullSource Controlᶜ))) := by
    as_aux_lemma =>
      have hg (z : (Controlᶜ : Set Z)) : Function.Bijective (g.linearMap z) := by
        rw [← hj z]
        exact (j z).bijective
      apply (g.continuous_inverse hg).congr
      intro z
      have he : LinearEquiv.ofBijective (g.linearMap z.proj) (hg z.proj) = j z.proj := by
        apply LinearEquiv.ext
        intro v
        rw [LinearEquiv.ofBijective_apply]
        exact LinearMap.congr_fun (hj z.proj).symm v
      exact congrArg (fun t : (Restrict PullSource Controlᶜ) z.proj ≃ₗ[ℂ]
          (Restrict PullTarget Controlᶜ) z.proj ↦ (⟨z.proj, t.symm z.snd⟩ :
            TotalSpace Unit (Restrict PullSource Controlᶜ))) he
  have hforward : Continuous (fun z : TotalSpace Unit PullSource ↦
      (⟨z.proj, thomTensorSymbol (d z.proj.proj) (d' z.proj.proj) z.proj.snd z.snd⟩ :
        TotalSpace Unit PullTarget)) := by
    as_aux_lemma =>
      -- The full exterior symbol, including its zero value, gives continuous parity maps
      -- over the original total space. Its metric is the supplied original pairing.
      let parity (i : ZMod 2) : X → Type _ :=
        fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
      let clifford (i : ZMod 2) : Hom ((p : Z → X) *ᵖ (parity i))
          ((p : Z → X) *ᵖ (parity (i + 1))) :=
        { linearMap := fun z ↦ cliffordSymbolParity z.snd i
          continuous_total := by
            have hv : Continuous (fun z : TotalSpace Unit ((p : Z → X) *ᵖ (parity i)) ↦
                z.proj) := Pullback.continuous_proj Unit (parity i) p
            have ha : Continuous (fun z : TotalSpace Unit ((p : Z → X) *ᵖ (parity i)) ↦
                (⟨z.proj.proj, z.snd.val⟩ :
                  TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := by
              have hi : Continuous (fun z : TotalSpace Unit (parity i) ↦
                  (⟨z.proj, z.snd.val⟩ :
                    TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x)))) := continuous_induced_dom
              exact hi.comp (Pullback.continuous_lift Unit (parity i) p)
            have hpairs : Continuous (fun z : TotalSpace Unit ((p : Z → X) *ᵖ (parity i)) ↦
                (⟨z.proj.proj, (z.proj.snd, z.snd.val)⟩ :
                  TotalSpace Unit (E ×ᵇ (fun x ↦ ExteriorAlgebra ℂ (E x))))) := by
              apply continuous_induced_rng.mpr
              exact hv.prodMk ha
            rw [(inducing_pullbackTotalSpaceEmbedding Unit (parity (i + 1)) p).continuous_iff]
            apply hv.prodMk
            apply continuous_induced_rng.mpr
            dsimp only [Function.comp_def, p]
            change Continuous (fun z : TotalSpace Unit ((p : Z → X) *ᵖ (parity i)) ↦
              (⟨z.proj.proj, cliffordSymbol z.proj.snd z.snd.val⟩ :
                TotalSpace Unit (fun x ↦ ExteriorAlgebra ℂ (E x))))
            exact (continuous_cliffordSymbol E hinner).comp hpairs }
      -- Tensor the original maps after the vector-preserving pullback/tensor comparisons.
      let tensorMap (F G : FiniteBundle X) (H J : X → Type _)
          [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
          [∀ x, AddCommGroup (J x)] [∀ x, Module ℂ (J x)]
          [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
          [TopologicalSpace (TotalSpace Unit J)] [IsFiniteRank J]
          (f : Hom ((p : Z → X) *ᵖ F.Fiber) ((p : Z → X) *ᵖ G.Fiber))
          (g : Hom ((p : Z → X) *ᵖ H) ((p : Z → X) *ᵖ J)) :
          Hom ((p : Z → X) *ᵖ (fun x ↦ F.Fiber x ⊗[ℂ] H x))
            ((p : Z → X) *ᵖ (fun x ↦ G.Fiber x ⊗[ℂ] J x)) :=
        ((pullbackTensorIso (E := G.Fiber) (F := J) p).symm.toHom).comp
          ((f.tensor g).comp (pullbackTensorIso (E := F.Fiber) (F := H) p).toHom)
      let row (S T : Z → Type _) [∀ z, AddCommGroup (S z)] [∀ z, Module ℂ (S z)]
          [∀ z, AddCommGroup (T z)] [∀ z, Module ℂ (T z)]
          [TopologicalSpace (TotalSpace Unit S)] [IsFiniteRank S]
          [TopologicalSpace (TotalSpace Unit T)] [IsFiniteRank T]
          (f g : Hom S T) : Hom S T :=
        { linearMap := fun z ↦ f.linearMap z - g.linearMap z
          continuous_total := by
            let q : C(TotalSpace Unit S, Z) := ⟨π Unit S, continuous_proj⟩
            let := isFiniteRank_pullback (E := T) q
            have hf : Continuous (fun z : TotalSpace Unit S ↦
                (⟨z, f.linearMap z.proj z.snd⟩ :
                  TotalSpace Unit ((q : TotalSpace Unit S → Z) *ᵖ T))) := by
              rw [(inducing_pullbackTotalSpaceEmbedding Unit T q).continuous_iff]
              exact continuous_id.prodMk f.continuous_total
            have hg : Continuous (fun z : TotalSpace Unit S ↦
                (⟨z, g.linearMap z.proj z.snd⟩ :
                  TotalSpace Unit ((q : TotalSpace Unit S → Z) *ᵖ T))) := by
              rw [(inducing_pullbackTotalSpaceEmbedding Unit T q).continuous_iff]
              exact continuous_id.prodMk g.continuous_total
            have hc := (Pullback.continuous_lift Unit T q).comp
              (continuous_add_section _ _ _ hf
                (continuous_smul_section _ (ContinuousMap.const _ (-1 : ℂ)) _ hg))
            change Continuous (fun z : TotalSpace Unit S ↦
              (⟨z.proj, f.linearMap z.proj z.snd + (-1 : ℂ) • g.linearMap z.proj z.snd⟩ :
                TotalSpace Unit T)) at hc
            simpa only [neg_one_smul, sub_eq_add_neg, LinearMap.add_apply,
              LinearMap.neg_apply] using hc }
      let d₀ := (a.datum.cutoffHom ρ U hU hcontrol hzero).pullback p
      let d₁ := (a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).pullback p
      let upper := row PullSource ((p : Z → X) *ᵖ (fun x ↦ a.target.Fiber x ⊗[ℂ] Even x))
        ((tensorMap a.source a.target Even Even d₀ (Hom.id _)).comp (sumFst.pullback p))
        ((tensorMap a.target a.target Odd Even (Hom.id _) (clifford 1)).comp
          (sumSnd.pullback p))
      let lower := row PullSource ((p : Z → X) *ᵖ (fun x ↦ a.source.Fiber x ⊗[ℂ] Odd x))
        ((tensorMap a.source a.source Even Odd (Hom.id _) (clifford 0)).comp
          (sumFst.pullback p))
        ((tensorMap a.target a.source Odd Odd d₁ (Hom.id _)).comp (sumSnd.pullback p))
      rw [(inducing_pullbackTotalSpaceEmbedding Unit Target p).continuous_iff]
      apply (Pullback.continuous_proj Unit Source p).prodMk
      apply continuous_induced_rng.mpr
      have hc := ((Pullback.continuous_lift Unit
        (fun x ↦ a.target.Fiber x ⊗[ℂ] Even x) p).comp upper.continuous_total).prodMk
          ((Pullback.continuous_lift Unit
            (fun x ↦ a.source.Fiber x ⊗[ℂ] Odd x) p).comp lower.continuous_total)
      apply hc.congr
      intro z
      let c₀ : Even z.proj.proj →ₗ[ℂ] Odd z.proj.proj := cliffordSymbolParity z.proj.snd 0
      let c₁ : Odd z.proj.proj →ₗ[ℂ] Even z.proj.proj := cliffordSymbolParity z.proj.snd 1
      apply Prod.ext
      · apply congrArg (TotalSpace.mk z.proj.proj)
        change
          TensorProduct.map (d z.proj.proj) LinearMap.id z.snd.1 -
              TensorProduct.map LinearMap.id c₁ z.snd.2 =
            TensorProduct.map (d z.proj.proj) LinearMap.id z.snd.1 +
              -(TensorProduct.map LinearMap.id c₁ z.snd.2)
        exact sub_eq_add_neg _ _
      · apply congrArg (TotalSpace.mk z.proj.proj)
        change
          TensorProduct.map LinearMap.id c₀ z.snd.1 -
              TensorProduct.map (d' z.proj.proj) LinearMap.id z.snd.2 =
            TensorProduct.map LinearMap.id c₀ z.snd.1 +
              -(TensorProduct.map (d' z.proj.proj) LinearMap.id z.snd.2)
        exact sub_eq_add_neg _ _
  let forward : Hom PullSource PullTarget :=
    { linearMap := fun z ↦ thomTensorSymbol (d z.proj) (d' z.proj) z.snd
      continuous_total := hforward }
  -- Restrict the continuous block to the same exterior, then use its exact inverse laws.
  let f := forward.restrict Controlᶜ
  let e (z : (Controlᶜ : Set Z)) := thomTensorSymbolEquiv (d z.val.proj) (d' z.val.proj)
    (ρ z.val.proj : ℝ) z.val.snd
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.proj).1
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.proj).2
    (hnonzero z)
  refine ⟨hnonzero, f.continuous_total, ?_⟩
  change Continuous (fun z : TotalSpace Unit (Restrict PullTarget Controlᶜ) ↦
    (⟨z.proj, (e z.proj).symm z.snd⟩ : TotalSpace Unit (Restrict PullSource Controlᶜ)))
  apply inverse_continuous f e
  intro z
  rfl

/-- The prescribed graded tensor symbol on the complement of the zero control. -/
def supportedThomBoundary : RelativeTriple PullSource PullTarget Controlᶜ where
  linearEquiv z := thomTensorSymbolEquiv (d z.val.proj) (d' z.val.proj)
    (ρ z.val.proj : ℝ) z.val.snd
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.proj).1
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.proj).2
    ((supportedThom_symbol_properties E hinner a ρ U hU hcontrol hzero L hL hone).1 z)
  continuous_total :=
    (supportedThom_symbol_properties E hinner a ρ U hU hcontrol hzero L hL hone).2.1
  continuous_symm :=
    (supportedThom_symbol_properties E hinner a ρ U hU hcontrol hzero L hL hone).2.2

/-- The supported Thom product has exactly the zero section over the enlarged base control. -/
def supportedThomTriple : CompactSupportTriple PullSource PullTarget where
  control := Control
  isCompact_control := by
    -- Compactness comes from the image of L under the original zero section.
    convert hL.image (continuous_zero_section E) using 1
    ext z
    constructor
    · rintro ⟨hx, hv⟩
      refine ⟨z.proj, hx, ?_⟩
      rcases z with ⟨x, v⟩
      change v = 0 at hv
      cases hv
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
  boundary := supportedThomBoundary E hinner a ρ U hU hcontrol hzero L hL hone

/-- The actual compact-support class of the tensor triple, with the original total-space target. -/
def supportedThomProductClass : CompactSupportKZero (TotalSpace Unit E) :=
  let proj : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj (E := E)⟩
  letI := isFiniteRank_pullback (E := Source) proj
  letI := isFiniteRank_pullback (E := Target) proj
  (supportedThomTriple E hinner a ρ U hU hcontrol hzero L hL hone).compactSupportClass

end Cutoff

/-! ### Descent properties of the specified tensor representatives -/

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Build the cutoff interpolation with one common original compact control.
/-- A common compact zero control makes the representative independent of the cutoff. -/
private theorem supportedThomProductClass_eq_of_cutoff
    (c₀ c₁ : { c : C(X, I) × Set X × Set X //
      IsOpen c.2.1 ∧ a.datum.control ⊆ c.2.1 ∧
      (∀ x ∈ c.2.1, c.1 x = 0) ∧ IsCompact c.2.2 ∧ ∀ x ∉ c.2.2, c.1 x = 1 }) :
    supportedThomProductClass E hinner a c₀.val.1 c₀.val.2.1
      c₀.property.1 c₀.property.2.1 c₀.property.2.2.1
      c₀.val.2.2 c₀.property.2.2.2.1 c₀.property.2.2.2.2 =
    supportedThomProductClass E hinner a c₁.val.1 c₁.val.2.1
      c₁.property.1 c₁.property.2.1 c₁.property.2.2.1
      c₁.val.2.2 c₁.property.2.2.2.1 c₁.property.2.2.2.2 := by
  have thom_affine {A₀ : Type _} {A₁ : Type _} {V : Type _}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [NormedAddCommGroup V] [InnerProductSpace ℂ V]
      (d₀ d₁ : A₀ →ₗ[ℂ] A₁) (d₀' d₁' : A₁ →ₗ[ℂ] A₀)
      (v : V) (r s : ℂ) (hrs : r + s = 1) :
      thomTensorSymbol (r • d₀ + s • d₁) (r • d₀' + s • d₁') v =
        r • thomTensorSymbol d₀ d₀' v + s • thomTensorSymbol d₁ d₁' v := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro a b <;> apply Prod.ext <;>
        simp only [thomTensorSymbol, LinearMap.coe_comp, LinearMap.coe_inl,
            LinearMap.coe_inr, Function.comp_apply, LinearMap.prod_apply, Function.prod_apply,
            LinearMap.coprod_apply, TensorProduct.map_tmul, LinearMap.add_apply,
            LinearMap.smul_apply, LinearMap.id_coe, id_eq, TensorProduct.add_tmul,
            LinearMap.neg_apply, map_zero, add_zero, zero_add, LinearMap.coe_add,
            LinearMap.coe_smul, Pi.add_apply, Pi.smul_apply, Prod.smul_mk,
            TensorProduct.smul_tmul', Prod.mk_add_mk, neg_add_rev, smul_neg]
      · rw [← TensorProduct.add_tmul, ← add_smul, hrs, one_smul]
      · rw [← neg_add, ← TensorProduct.add_tmul, ← add_smul, hrs, one_smul]
      · exact add_comm _ _
  classical
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  let : IsFiniteRank PullSource := isFiniteRank_pullback (E := Source) p
  let : IsFiniteRank PullTarget := isFiniteRank_pullback (E := Target) p
  let A₀ := supportedThomTriple E hinner a c₀.val.1 c₀.val.2.1
    c₀.property.1 c₀.property.2.1 c₀.property.2.2.1
    c₀.val.2.2 c₀.property.2.2.2.1 c₀.property.2.2.2.2
  let A₁ := supportedThomTriple E hinner a c₁.val.1 c₁.val.2.1
    c₁.property.1 c₁.property.2.1 c₁.property.2.2.1
    c₁.val.2.2 c₁.property.2.2.2.1 c₁.property.2.2.2.2
  change A₀.compactSupportClass = A₁.compactSupportClass
  apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
  -- Convex interpolation retains a common zero neighborhood and compact zero control.
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
  let L := c₀.val.2.2 ∪ c₁.val.2.2
  have hL : IsCompact L := c₀.property.2.2.2.1.union c₁.property.2.2.2.1
  have hzero (t : I) (x : X) (hx : x ∈ c₀.val.2.1 ∩ c₁.val.2.1) : ρ t x = 0 := by
    apply Subtype.ext
    simp only [ρ, ContinuousMap.coe_mk, blend, c₀.property.2.2.1 x hx.1,
      c₁.property.2.2.1 x hx.2, Set.Icc.coe_zero, mul_zero, add_zero]
  have hone (t : I) (x : X) (hx : x ∉ L) : ρ t x = 1 := by
    apply Subtype.ext
    have hx₀ : x ∉ c₀.val.2.2 := fun h ↦ hx (Or.inl h)
    have hx₁ : x ∉ c₁.val.2.2 := fun h ↦ hx (Or.inr h)
    simp only [ρ, ContinuousMap.coe_mk, blend, c₀.property.2.2.2.2 x hx₀,
      c₁.property.2.2.2.2 x hx₁, Set.Icc.coe_one, mul_one]
    ring
  let K : Set Z := {z | z.proj ∈ L ∧ z.snd = 0}
  have hK : IsCompact K := by
    convert hL.image (continuous_zero_section E) using 1
    ext z
    constructor
    · rintro ⟨hx, hv⟩
      refine ⟨z.proj, hx, ?_⟩
      rcases z with ⟨x, v⟩
      change v = 0 at hv
      cases hv
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, rfl⟩
  have hleft : A₀.control ⊆ K := fun _ hz ↦ ⟨Or.inl hz.1, hz.2⟩
  have hright : A₁.control ⊆ K := fun _ hz ↦ ⟨Or.inr hz.1, hz.2⟩
  let e₀ := (A₀.enlarge K hK hleft).boundary
  let e₁ := (A₁.enlarge K hK hright).boundary
  -- On the fixed exterior the actual tensor symbols form the same affine combination.
  have mix (t : I) (x : X) (e : CompactSupportTriple a.source.Fiber a.target.Fiber) :
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
  have mix' (t : I) (x : X) :
      a.datum.inverse.cutoffLinearMap (ρ t) x =
        ((1 - (t : ℝ) : ℝ) : ℂ) • a.datum.inverse.cutoffLinearMap c₀.val.1 x +
          ((t : ℝ) : ℂ) • a.datum.inverse.cutoffLinearMap c₁.val.1 x := by
    apply LinearMap.ext
    intro v
    by_cases hx : x ∈ a.datum.control
    · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_left hx, LinearMap.zero_apply, smul_zero, add_zero]
    · simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
        dite_eq_right hx, LinearMap.add_apply, ρ, ContinuousMap.coe_mk, blend]
      push_cast
      simp only [add_smul, mul_smul]
      rfl
  have mixed (t : I) (z : (Kᶜ : Set Z)) (w : Source z.val.proj) :
      thomTensorSymbol (a.datum.cutoffLinearMap (ρ t) z.val.proj)
          (a.datum.inverse.cutoffLinearMap (ρ t) z.val.proj) z.val.snd w =
        ((1 - (t : ℝ) : ℝ) : ℂ) • e₀.linearEquiv z w +
          ((t : ℝ) : ℂ) • e₁.linearEquiv z w := by
    have hv₀ : e₀.linearEquiv z w = thomTensorSymbol
        (a.datum.cutoffLinearMap c₀.val.1 z.val.proj)
        (a.datum.inverse.cutoffLinearMap c₀.val.1 z.val.proj) z.val.snd w := by
      rw [CompactSupportTriple.enlarge_apply]
      rfl
    have hv₁ : e₁.linearEquiv z w = thomTensorSymbol
        (a.datum.cutoffLinearMap c₁.val.1 z.val.proj)
        (a.datum.inverse.cutoffLinearMap c₁.val.1 z.val.proj) z.val.snd w := by
      rw [CompactSupportTriple.enlarge_apply]
      rfl
    refine Eq.trans ?_ (congrArg₂ (fun u v ↦
      ((1 - (t : ℝ) : ℝ) : ℂ) • u + ((t : ℝ) : ℂ) • v) hv₀.symm hv₁.symm)
    rw [mix t z.val.proj a.datum, mix']
    have ht : (((1 - (t : ℝ) : ℝ) : ℂ)) + ((t : ℝ) : ℂ) = 1 := by push_cast; ring
    have h := thom_affine
      (a.datum.cutoffLinearMap c₀.val.1 z.val.proj)
      (a.datum.cutoffLinearMap c₁.val.1 z.val.proj)
      (a.datum.inverse.cutoffLinearMap c₀.val.1 z.val.proj)
      (a.datum.inverse.cutoffLinearMap c₁.val.1 z.val.proj) z.val.snd
      (((1 - (t : ℝ) : ℝ) : ℂ)) ((t : ℝ) : ℂ) ht
    exact LinearMap.congr_fun h w
  clear_value A₀ A₁
  let q : C(I × (Kᶜ : Set Z), (Kᶜ : Set Z)) := ContinuousMap.snd
  let S := (q : I × (Kᶜ : Set Z) → (Kᶜ : Set Z)) *ᵖ (Restrict PullSource Kᶜ)
  let T := (q : I × (Kᶜ : Set Z) → (Kᶜ : Set Z)) *ᵖ (Restrict PullTarget Kᶜ)
  let : IsFiniteRank (Restrict PullSource Kᶜ) := isFiniteRank_restrict _
  let : IsFiniteRank (Restrict PullTarget Kᶜ) := isFiniteRank_restrict _
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
  have hbij (z : I × (Kᶜ : Set Z)) : Function.Bijective (f.linearMap z) := by
    have hcontrol : a.datum.control ⊆ c₀.val.2.1 ∩ c₁.val.2.1 :=
      fun _ hx ↦ ⟨c₀.property.2.1 hx, c₁.property.2.1 hx⟩
    have hinv := a.datum.cutoffHom_inverse_comp (ρ z.1) (c₀.val.2.1 ∩ c₁.val.2.1)
      (c₀.property.1.inter c₁.property.1) hcontrol (hzero z.1) z.2.val.proj
    have hn : (ρ z.1 z.2.val.proj : ℝ) ^ 2 + ‖z.2.val.snd‖ ^ 2 ≠ 0 := by
      by_cases hv : z.2.val.snd = 0
      · have hx : z.2.val.proj ∉ L := fun hx ↦ z.2.property ⟨hx, hv⟩
        rw [hone z.1 z.2.val.proj hx, hv]
        norm_num
      · exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg _)
          (sq_pos_of_pos (norm_pos_iff.mpr hv)))
    let e := thomTensorSymbolEquiv (a.datum.cutoffLinearMap (ρ z.1) z.2.val.proj)
      (a.datum.inverse.cutoffLinearMap (ρ z.1) z.2.val.proj)
      (ρ z.1 z.2.val.proj : ℝ) z.2.val.snd hinv.1 hinv.2 hn
    have heq : f.linearMap z = e.toLinearMap := by
      apply LinearMap.ext
      intro w
      exact (mixed z.1 z.2 w).symm
    rw [heq]
    exact e.bijective
  refine ⟨K, hK, hleft, hright, ⟨{ iso := f.toIso hbij, map_zero := ?_, map_one := ?_ }⟩⟩
  · intro z v
    change r (0, z) • e₀.linearEquiv z v + s (0, z) • e₁.linearEquiv z v = _
    simp [r, s, e₀, e₁]
  · intro z v
    change r (1, z) • e₀.linearEquiv z v + s (1, z) • e₁.linearEquiv z v = _
    simp [r, s, e₀, e₁]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Compare the original reciprocal tensor blocks under both specified bundle isomorphisms.
/-- The two prescribed bundle isomorphisms intertwine the same reciprocal tensor blocks. -/
private theorem supportedThomProductClass_eq_of_intertwining
    (b : SupportBundleTriple X) (c₀ : { c : C(X, I) × Set X × Set X //
      IsOpen c.2.1 ∧ a.datum.control ⊆ c.2.1 ∧
      (∀ x ∈ c.2.1, c.1 x = 0) ∧ IsCompact c.2.2 ∧ ∀ x ∉ c.2.2, c.1 x = 1 })
    (c₁ : { c : C(X, I) × Set X × Set X //
      IsOpen c.2.1 ∧ b.datum.control ⊆ c.2.1 ∧
      (∀ x ∈ c.2.1, c.1 x = 0) ∧ IsCompact c.2.2 ∧ ∀ x ∉ c.2.2, c.1 x = 1 })
    (u : Iso a.source.Fiber b.source.Fiber) (v : Iso a.target.Fiber b.target.Fiber)
    (hD : ∀ x w, v.linearEquiv x (a.datum.cutoffLinearMap c₀.val.1 x w) =
      b.datum.cutoffLinearMap c₁.val.1 x (u.linearEquiv x w))
    (hD' : ∀ x w, u.linearEquiv x (a.datum.inverse.cutoffLinearMap c₀.val.1 x w) =
      b.datum.inverse.cutoffLinearMap c₁.val.1 x (v.linearEquiv x w)) :
    supportedThomProductClass E hinner a c₀.val.1 c₀.val.2.1
      c₀.property.1 c₀.property.2.1 c₀.property.2.2.1
      c₀.val.2.2 c₀.property.2.2.2.1 c₀.property.2.2.2.2 =
    supportedThomProductClass E hinner b c₁.val.1 c₁.val.2.1
      c₁.property.1 c₁.property.2.1 c₁.property.2.2.1
      c₁.val.2.2 c₁.property.2.2.2.1 c₁.property.2.2.2.2 := by
  have support_square
      {X : Type _} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
      [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (u : Iso E G) (v : Iso F H) (K : Set X) (hK : IsCompact K)
      (ha : a.control ⊆ K) (hb : b.control ⊆ K)
      (hs : ∀ (x : (Kᶜ : Set X)) (w : E x.val),
        v.linearEquiv x.val ((a.enlarge K hK ha).boundary.linearEquiv x w) =
          (b.enlarge K hK hb).boundary.linearEquiv x (u.linearEquiv x.val w)) :
      a.compactSupportClass = b.compactSupportClass := by
    as_aux_lemma =>
      rw [← a.compactSupportClass_congr u v]
      apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
      have heq : ((a.congr u v).enlarge K hK ha).boundary =
          (b.enlarge K hK hb).boundary := by
        apply Iso.ext
        intro x
        apply LinearEquiv.ext
        intro w
        have h := hs x ((u.linearEquiv x.val).symm w)
        rw [LinearEquiv.apply_symm_apply] at h
        have hl := (a.congr u v).enlarge_apply K hK ha x w
        have hc := a.congr_apply u v ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w
        have hv := a.enlarge_apply K hK ha x ((u.linearEquiv x.val).symm w)
        exact hl.trans (hc.trans ((congrArg (v.linearEquiv x.val) hv.symm).trans h))
      refine ⟨K, hK, ha, hb, ?_⟩
      rw [heq]
      exact IsoHomotopy.nonempty_refl _
  have thom_square {A₀ : Type _} {A₁ : Type _} {B₀ : Type _} {B₁ : Type _} {W : Type _}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [NormedAddCommGroup W] [InnerProductSpace ℂ W]
      (d : A₀ →ₗ[ℂ] A₁) (d' : A₁ →ₗ[ℂ] A₀)
      (e : B₀ →ₗ[ℂ] B₁) (e' : B₁ →ₗ[ℂ] B₀)
      (u : A₀ →ₗ[ℂ] B₀) (v : A₁ →ₗ[ℂ] B₁) (w : W)
      (h : ∀ x, v (d x) = e (u x)) (h' : ∀ x, u (d' x) = e' (v x)) :
      ((TensorProduct.map v LinearMap.id).prodMap (TensorProduct.map u LinearMap.id)).comp
          (thomTensorSymbol d d' w) =
        (thomTensorSymbol e e' w).comp
          ((TensorProduct.map u LinearMap.id).prodMap (TensorProduct.map v LinearMap.id)) := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro a b <;> apply Prod.ext <;> simp [thomTensorSymbol, h, h']
  classical
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  let S := fun x : X ↦
    (b.source.Fiber x ⊗[ℂ] Even x) × (b.target.Fiber x ⊗[ℂ] Odd x)
  let T := fun x : X ↦
    (b.target.Fiber x ⊗[ℂ] Even x) × (b.source.Fiber x ⊗[ℂ] Odd x)
  let : IsFiniteRank PullSource := isFiniteRank_pullback (E := Source) p
  let : IsFiniteRank PullTarget := isFiniteRank_pullback (E := Target) p
  let : IsFiniteRank (p *ᵖ S) := isFiniteRank_pullback (E := S) p
  let : IsFiniteRank (p *ᵖ T) := isFiniteRank_pullback (E := T) p
  let A₀ := supportedThomTriple E hinner a c₀.val.1 c₀.val.2.1
    c₀.property.1 c₀.property.2.1 c₀.property.2.2.1
    c₀.val.2.2 c₀.property.2.2.2.1 c₀.property.2.2.2.2
  let A₁ := supportedThomTriple E hinner b c₁.val.1 c₁.val.2.1
    c₁.property.1 c₁.property.2.1 c₁.property.2.2.1
    c₁.val.2.2 c₁.property.2.2.2.1 c₁.property.2.2.2.2
  let U : Iso PullSource (p *ᵖ S) :=
    ((u.tensor (Iso.refl Even)).sum (v.tensor (Iso.refl Odd))).pullback p
  let V : Iso PullTarget (p *ᵖ T) :=
    ((v.tensor (Iso.refl Even)).sum (u.tensor (Iso.refl Odd))).pullback p
  change A₀.compactSupportClass = A₁.compactSupportClass
  let K := A₀.control ∪ A₁.control
  have hK : IsCompact K := A₀.isCompact_control.union A₁.isCompact_control
  apply support_square A₀ A₁ U V K hK Set.subset_union_left Set.subset_union_right
  intro z w
  have hl := A₀.enlarge_apply K hK Set.subset_union_left z w
  have hr := A₁.enlarge_apply K hK Set.subset_union_right z (U.linearEquiv z.val w)
  have hsquare := thom_square
    (a.datum.cutoffLinearMap c₀.val.1 z.val.proj)
    (a.datum.inverse.cutoffLinearMap c₀.val.1 z.val.proj)
    (b.datum.cutoffLinearMap c₁.val.1 z.val.proj)
    (b.datum.inverse.cutoffLinearMap c₁.val.1 z.val.proj)
    (u.linearEquiv z.val.proj).toLinearMap (v.linearEquiv z.val.proj).toLinearMap
    z.val.snd (hD z.val.proj) (hD' z.val.proj)
  exact (congrArg (V.linearEquiv z.val) hl).trans
    ((LinearMap.congr_fun hsquare w).trans hr.symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
-- Identify the original direct-sum tensor symbol with the sum of its two support classes.
/-- Tensoring the actual direct-sum representative adds its two prescribed support classes. -/
private theorem supportedThomProductClass_sum
    (b : SupportBundleTriple X) (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
    (ha : a.datum.control ⊆ U) (hb : b.datum.control ⊆ U)
    (hzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
    (hone : ∀ x ∉ L, ρ x = 1) :
    supportedThomProductClass E hinner (a.sum b) ρ U hU
        (Set.union_subset ha hb) hzero L hL hone =
      supportedThomProductClass E hinner a ρ U hU ha hzero L hL hone +
        supportedThomProductClass E hinner b ρ U hU hb hzero L hL hone := by
  have support_square
      {X : Type _} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
      [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (u : Iso E G) (v : Iso F H) (K : Set X) (hK : IsCompact K)
      (ha : a.control ⊆ K) (hb : b.control ⊆ K)
      (hs : ∀ (x : (Kᶜ : Set X)) (w : E x.val),
        v.linearEquiv x.val
            (a.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w) =
          b.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (hb hx)⟩
            (u.linearEquiv x.val w)) :
      a.compactSupportClass = b.compactSupportClass := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    as_aux_lemma =>
      rw [← a.compactSupportClass_congr u v]
      apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
      have heq : ((a.congr u v).enlarge K hK ha).boundary =
          (b.enlarge K hK hb).boundary := by
        apply Iso.ext
        intro x
        apply LinearEquiv.ext
        intro w
        have h := hs x ((u.linearEquiv x.val).symm w)
        rw [LinearEquiv.apply_symm_apply] at h
        have hl := (a.congr u v).enlarge_apply K hK ha x w
        have hc := a.congr_apply u v ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w
        have hv := b.enlarge_apply K hK hb x w
        exact hl.trans (hc.trans (h.trans hv.symm))
      refine ⟨K, hK, ha, hb, ?_⟩
      rw [heq]
      exact IsoHomotopy.nonempty_refl _
  have raw_sum_apply
      {X : Type _} [TopologicalSpace X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)]
      [TopologicalSpace (TotalSpace Unit F)]
      [TopologicalSpace (TotalSpace Unit G)]
      [TopologicalSpace (TotalSpace Unit H)]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (x : ((a.control ∪ b.control)ᶜ : Set X)) (w : E x × G x) :
      (a.sum b).boundary.linearEquiv x w =
        (a.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (Or.inl hx)⟩ w.1,
          b.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (Or.inr hx)⟩ w.2) := by
    set_option backward.isDefEq.respectTransparency.types false in
    as_aux_lemma =>
      have hs := RelativeTriple.sum_apply
        (a.enlarge _ (a.isCompact_control.union b.isCompact_control) Set.subset_union_left).boundary
        (b.enlarge _ (a.isCompact_control.union b.isCompact_control)
          Set.subset_union_right).boundary
        x w
      exact hs.trans (Prod.ext
        (a.enlarge_apply _ (a.isCompact_control.union b.isCompact_control)
          Set.subset_union_left x w.1)
        (b.enlarge_apply _ (a.isCompact_control.union b.isCompact_control)
          Set.subset_union_right x w.2))
  have raw_sum_symm_apply
      {X : Type _} [TopologicalSpace X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)]
      [TopologicalSpace (TotalSpace Unit F)]
      [TopologicalSpace (TotalSpace Unit G)]
      [TopologicalSpace (TotalSpace Unit H)]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (x : ((a.control ∪ b.control)ᶜ : Set X)) (w : F x × H x) :
      ((a.sum b).boundary.linearEquiv x).symm w =
        ((a.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (Or.inl hx)⟩).symm w.1,
          (b.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (Or.inr hx)⟩).symm w.2) := by
    set_option backward.isDefEq.respectTransparency.types false in
    as_aux_lemma =>
      apply ((a.sum b).boundary.linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, raw_sum_apply]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Prod.eta w).symm
  have thom_sum_generic
      {A₀ : Type _} {A₁ : Type _} {B₀ : Type _} {B₁ : Type _} {W : Type _}
      [AddCommGroup A₀] [Module ℂ A₀] [AddCommGroup A₁] [Module ℂ A₁]
      [AddCommGroup B₀] [Module ℂ B₀] [AddCommGroup B₁] [Module ℂ B₁]
      [NormedAddCommGroup W] [InnerProductSpace ℂ W]
      (u₀ : ((A₀ × B₀) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) ≃ₗ[ℂ] ((A₀ ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × (B₀ ⊗[ℂ] (CliffordAlgebra.evenOdd (0
        : QuadraticForm ℂ W) 0))))
      (u₁ : ((A₁ × B₁) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1)) ≃ₗ[ℂ] ((A₁ ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1)) × (B₁ ⊗[ℂ] (CliffordAlgebra.evenOdd (0
        : QuadraticForm ℂ W) 1))))
      (v₀ : ((A₁ × B₁) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) ≃ₗ[ℂ] ((A₁ ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × (B₁ ⊗[ℂ] (CliffordAlgebra.evenOdd (0
        : QuadraticForm ℂ W) 0))))
      (v₁ : ((A₀ × B₀) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1)) ≃ₗ[ℂ] ((A₀ ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1)) × (B₀ ⊗[ℂ] (CliffordAlgebra.evenOdd (0
        : QuadraticForm ℂ W) 1))))
      (hu₀ : ∀ r s, u₀ (r ⊗ₜ[ℂ] s) = (r.1 ⊗ₜ[ℂ] s, r.2 ⊗ₜ[ℂ] s))
      (hu₁ : ∀ r s, u₁ (r ⊗ₜ[ℂ] s) = (r.1 ⊗ₜ[ℂ] s, r.2 ⊗ₜ[ℂ] s))
      (hv₀ : ∀ r s, v₀ (r ⊗ₜ[ℂ] s) = (r.1 ⊗ₜ[ℂ] s, r.2 ⊗ₜ[ℂ] s))
      (hv₁ : ∀ r s, v₁ (r ⊗ₜ[ℂ] s) = (r.1 ⊗ₜ[ℂ] s, r.2 ⊗ₜ[ℂ] s))
      (U : (((A₀ × B₀) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × ((A₁ × B₁) ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1))) ≃ₗ[ℂ]
        (((A₀ ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × (A₁ ⊗[ℂ]
          (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1))) × ((B₀ ⊗[ℂ] (CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ W) 0)) × (B₁ ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
          1)))))
      (V : (((A₁ × B₁) ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × ((A₀ × B₀) ⊗[ℂ]
        (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1))) ≃ₗ[ℂ]
        (((A₁ ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 0)) × (A₀ ⊗[ℂ]
          (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W) 1))) × ((B₁ ⊗[ℂ] (CliffordAlgebra.evenOdd
          (0 : QuadraticForm ℂ W) 0)) × (B₀ ⊗[ℂ] (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ W)
          1)))))
      (hU : ∀ r, U r = (((u₀ r.1).1, (u₁ r.2).1), ((u₀ r.1).2, (u₁ r.2).2)))
      (hV : ∀ r, V r = (((v₀ r.1).1, (v₁ r.2).1), ((v₀ r.1).2, (v₁ r.2).2)))
      (d : (A₀ × B₀) →ₗ[ℂ] (A₁ × B₁))
      (d' : (A₁ × B₁) →ₗ[ℂ] (A₀ × B₀))
      (d₀ : A₀ →ₗ[ℂ] A₁) (d₁ : B₀ →ₗ[ℂ] B₁)
      (d₀' : A₁ →ₗ[ℂ] A₀) (d₁' : B₁ →ₗ[ℂ] B₀)
      (hd : ∀ r, d r = (d₀ r.1, d₁ r.2))
      (hd' : ∀ r, d' r = (d₀' r.1, d₁' r.2)) (w : W) :
      V.toLinearMap.comp (thomTensorSymbol d d' w) =
        ((thomTensorSymbol d₀ d₀' w).prodMap
          (thomTensorSymbol d₁ d₁' w)).comp U.toLinearMap := by
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
    as_aux_lemma =>
      -- Each original summand is determined by its pure tensors, including both parity signs.
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> rintro ⟨r₀, r₁⟩ s <;>
        simp only [thomTensorSymbol, LinearMap.coe_comp, Function.comp_apply,
          LinearMap.inl_apply, LinearMap.inr_apply, LinearMap.prod_apply, Function.prod,
          LinearMap.coprod_apply, LinearMap.prodMap_apply, LinearMap.neg_apply,
          TensorProduct.map_tmul, LinearMap.id_apply, LinearEquiv.coe_coe,
          map_zero, map_neg, zero_add, add_zero,
          Prod.fst_zero, Prod.snd_zero, Prod.fst_neg, Prod.snd_neg,
          hd, hd', hU, hV, hu₀, hu₁, hv₀, hv₁]
  classical
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  have distribution (J J' : FiniteBundle X) (i : ZMod 2) :
      ∃ e : Iso (fun x ↦ (J.Fiber x × J'.Fiber x) ⊗[ℂ]
          CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)
        (fun x ↦ (J.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd
            (0 : QuadraticForm ℂ (E x)) i) ×
          (J'.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i)),
        ∀ x u v, e.linearEquiv x (u ⊗ₜ[ℂ] v) = (u.1 ⊗ₜ[ℂ] v, u.2 ⊗ₜ[ℂ] v) := by
    as_aux_lemma =>
      let W : X → Type _ := fun x ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) i
      let S := fun x ↦ (J.Fiber x × J'.Fiber x) ⊗[ℂ] W x
      let T₀ := fun x ↦ J.Fiber x ⊗[ℂ] W x
      let T₁ := fun x ↦ J'.Fiber x ⊗[ℂ] W x
      let f : Hom S T₀ := (sumFst (E := J.Fiber) (F := J'.Fiber)).tensor (Hom.id W)
      let g : Hom S T₁ := (sumSnd (E := J.Fiber) (F := J'.Fiber)).tensor (Hom.id W)
      let d (x : X) := TensorProduct.prodLeft ℂ ℂ (J.Fiber x) (J'.Fiber x) (W x)
      have hd (x : X) (w : S x) : d x w = (f.linearMap x w, g.linearMap x w) := by
        have hm : (d x).toLinearMap = (f.linearMap x).prod (g.linearMap x) := by
          apply TensorProduct.ext'
          intro u v
          rfl
        exact LinearMap.congr_fun hm w
      let D : Hom S (T₀ ×ᵇ T₁) :=
        { linearMap x := (d x).toLinearMap
          continuous_total := by
            apply continuous_induced_rng.mpr
            apply (f.continuous_total.prodMk g.continuous_total).congr
            intro z
            exact congrArg (fun w ↦
              ((⟨z.proj, w.1⟩ : TotalSpace Unit T₀),
                (⟨z.proj, w.2⟩ : TotalSpace Unit T₁))) (hd z.proj z.snd).symm }
      exact ⟨D.toIso (fun x ↦ (d x).bijective), fun _ _ _ ↦ rfl⟩
  obtain ⟨u₀, hu₀⟩ := distribution a.source b.source 0
  obtain ⟨u₁, hu₁⟩ := distribution a.target b.target 1
  obtain ⟨v₀, hv₀⟩ := distribution a.target b.target 0
  obtain ⟨v₁, hv₁⟩ := distribution a.source b.source 1
  have rearrange (J J' K K' : FiniteBundle X) :
      ∃ e : Iso (fun x ↦ ((J.Fiber x ⊗[ℂ] Even x) × (J'.Fiber x ⊗[ℂ] Even x)) ×
          ((K.Fiber x ⊗[ℂ] Odd x) × (K'.Fiber x ⊗[ℂ] Odd x)))
        (fun x ↦ ((J.Fiber x ⊗[ℂ] Even x) × (K.Fiber x ⊗[ℂ] Odd x)) ×
          ((J'.Fiber x ⊗[ℂ] Even x) × (K'.Fiber x ⊗[ℂ] Odd x))),
        ∀ x w, e.linearEquiv x w = ((w.1.1, w.2.1), (w.1.2, w.2.2)) := by
    as_aux_lemma =>
      let S₀ := fun x ↦ J.Fiber x ⊗[ℂ] Even x
      let S₁ := fun x ↦ J'.Fiber x ⊗[ℂ] Even x
      let T₀ := fun x ↦ K.Fiber x ⊗[ℂ] Odd x
      let T₁ := fun x ↦ K'.Fiber x ⊗[ℂ] Odd x
      let S := (S₀ ×ᵇ S₁) ×ᵇ (T₀ ×ᵇ T₁)
      let p₁ : Hom S S₀ := sumFst.comp sumFst
      let p₂ : Hom S S₁ := sumSnd.comp sumFst
      let p₃ : Hom S T₀ := sumFst.comp sumSnd
      let p₄ : Hom S T₁ := sumSnd.comp sumSnd
      let f : Hom S (S₀ ×ᵇ T₀) :=
        { linearMap x := (p₁.linearMap x).prod (p₃.linearMap x)
          continuous_total := continuous_induced_rng.mpr
            (p₁.continuous_total.prodMk p₃.continuous_total) }
      let g : Hom S (S₁ ×ᵇ T₁) :=
        { linearMap x := (p₂.linearMap x).prod (p₄.linearMap x)
          continuous_total := continuous_induced_rng.mpr
            (p₂.continuous_total.prodMk p₄.continuous_total) }
      let q : Hom S ((S₀ ×ᵇ T₀) ×ᵇ (S₁ ×ᵇ T₁)) :=
        { linearMap x := (LinearEquiv.prodProdProdComm ℂ (S₀ x) (S₁ x)
              (T₀ x) (T₁ x)).toLinearMap
          continuous_total := continuous_induced_rng.mpr
            (f.continuous_total.prodMk g.continuous_total) }
      exact ⟨q.toIso (fun x ↦ (LinearEquiv.prodProdProdComm ℂ (S₀ x) (S₁ x)
        (T₀ x) (T₁ x)).bijective), fun _ _ ↦ rfl⟩
  obtain ⟨U₀, hU₀⟩ := rearrange a.source b.source a.target b.target
  obtain ⟨V₀, hV₀⟩ := rearrange a.target b.target a.source b.source
  let Ubase := (u₀.sum u₁).trans U₀
  let Vbase := (v₀.sum v₁).trans V₀
  have hUv (x : X) (w) : Ubase.linearEquiv x w =
      (((u₀.linearEquiv x w.1).1, (u₁.linearEquiv x w.2).1),
        ((u₀.linearEquiv x w.1).2, (u₁.linearEquiv x w.2).2)) :=
    hU₀ x _
  have hVv (x : X) (w) : Vbase.linearEquiv x w =
      (((v₀.linearEquiv x w.1).1, (v₁.linearEquiv x w.2).1),
        ((v₀.linearEquiv x w.1).2, (v₁.linearEquiv x w.2).2)) :=
    hV₀ x _
  clear_value Ubase Vbase
  let source (c : SupportBundleTriple X) : X → Type _ := fun x ↦
    (c.source.Fiber x ⊗[ℂ] Even x) × (c.target.Fiber x ⊗[ℂ] Odd x)
  let target (c : SupportBundleTriple X) : X → Type _ := fun x ↦
    (c.target.Fiber x ⊗[ℂ] Even x) × (c.source.Fiber x ⊗[ℂ] Odd x)
  let (c : SupportBundleTriple X) : IsFiniteRank (p *ᵖ (source c)) :=
    isFiniteRank_pullback (E := source c) p
  let (c : SupportBundleTriple X) : IsFiniteRank (p *ᵖ (target c)) :=
    isFiniteRank_pullback (E := target c) p
  let Umap : Hom (p *ᵖ (source (a.sum b))) ((p *ᵖ (source a)) ×ᵇ (p *ᵖ (source b))) :=
    { linearMap z := (Ubase.linearEquiv z.proj).toLinearMap
      continuous_total := continuous_induced_rng.mpr
        ((((sumFst (E := source a) (F := source b)).pullback p).comp
          (Ubase.pullback p).toHom).continuous_total.prodMk
            (((sumSnd (E := source a) (F := source b)).pullback p).comp
              (Ubase.pullback p).toHom).continuous_total) }
  let Vmap : Hom (p *ᵖ (target (a.sum b))) ((p *ᵖ (target a)) ×ᵇ (p *ᵖ (target b))) :=
    { linearMap z := (Vbase.linearEquiv z.proj).toLinearMap
      continuous_total := continuous_induced_rng.mpr
        ((((sumFst (E := target a) (F := target b)).pullback p).comp
          (Vbase.pullback p).toHom).continuous_total.prodMk
            (((sumSnd (E := target a) (F := target b)).pullback p).comp
              (Vbase.pullback p).toHom).continuous_total) }
  let e := Umap.toIso (fun z ↦ (Ubase.linearEquiv z.proj).bijective)
  let f := Vmap.toIso (fun z ↦ (Vbase.linearEquiv z.proj).bijective)
  have he (z : Z) (w) : e.linearEquiv z w = Ubase.linearEquiv z.proj w := rfl
  have hf (z : Z) (w) : f.linearEquiv z w = Vbase.linearEquiv z.proj w := rfl
  clear_value e f Umap Vmap
  let Aab := supportedThomTriple E hinner (a.sum b) ρ U hU
    (Set.union_subset ha hb) hzero L hL hone
  let Aa := supportedThomTriple E hinner a ρ U hU ha hzero L hL hone
  let Ab := supportedThomTriple E hinner b ρ U hU hb hzero L hL hone
  change Aab.compactSupportClass = Aa.compactSupportClass + Ab.compactSupportClass
  let K : Set Z := {z | z.proj ∈ L ∧ z.snd = 0}
  have hK : IsCompact K := Aab.isCompact_control
  have habK : Aab.control ⊆ K := fun _ hz ↦ hz
  have haK : Aa.control ⊆ K := fun _ hz ↦ hz
  have hbK : Ab.control ⊆ K := fun _ hz ↦ hz
  have hab_formula (z : (Kᶜ : Set Z)) (w : (p *ᵖ (source (a.sum b))) z.val) :
      Aab.boundary.linearEquiv ⟨z.val, fun hz ↦ z.property (habK hz)⟩ w =
        thomTensorSymbol ((a.sum b).datum.cutoffLinearMap ρ z.val.proj)
          ((a.sum b).datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := by rfl
  have ha_formula (z : (Kᶜ : Set Z)) (w : (p *ᵖ (source a)) z.val) :
      Aa.boundary.linearEquiv ⟨z.val, fun hz ↦ z.property (haK hz)⟩ w =
        thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := by rfl
  have hb_formula (z : (Kᶜ : Set Z)) (w : (p *ᵖ (source b)) z.val) :
      Ab.boundary.linearEquiv ⟨z.val, fun hz ↦ z.property (hbK hz)⟩ w =
        thomTensorSymbol (b.datum.cutoffLinearMap ρ z.val.proj)
          (b.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd w := by rfl
  clear_value Aab Aa Ab
  rw [← Aa.compactSupportClass_sum Ab]
  have hsubset : (Aa.sum Ab).control ⊆ K := fun _ hz ↦ hz.elim (fun h ↦ haK h) (fun h ↦ hbK h)
  apply support_square Aab (Aa.sum Ab) e f K hK habK hsubset
  -- The base cutoff maps commute with direct sums, including the common zero region.
  have hd (x : X) (w : a.source.Fiber x × b.source.Fiber x) :
      (a.sum b).datum.cutoffLinearMap ρ x w =
        (a.datum.cutoffLinearMap ρ x w.1, b.datum.cutoffLinearMap ρ x w.2) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    by_cases hx : x ∈ U
    · simp only [CompactSupportTriple.cutoffLinearMap]
      split_ifs <;> simp [hzero x hx] <;> rfl
    · have hxa : x ∉ a.datum.control := fun h ↦ hx (ha h)
      have hxb : x ∉ b.datum.control := fun h ↦ hx (hb h)
      have hxab : x ∉ (a.sum b).datum.control := fun h ↦ h.elim hxa hxb
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa, dite_eq_right hxb,
        dite_eq_right hxab ]
      exact congrArg (fun w : a.target.Fiber x × b.target.Fiber x ↦
        ((ρ x : ℝ) : ℂ) • w) (raw_sum_apply a.datum b.datum ⟨x, hxab⟩ w)
  have hd' (x : X) (w : a.target.Fiber x × b.target.Fiber x) :
      (a.sum b).datum.inverse.cutoffLinearMap ρ x w =
        (a.datum.inverse.cutoffLinearMap ρ x w.1,
          b.datum.inverse.cutoffLinearMap ρ x w.2) := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    by_cases hx : x ∈ U
    · simp only [CompactSupportTriple.cutoffLinearMap]
      split_ifs <;> simp [hzero x hx] <;> rfl
    · have hxa : x ∉ a.datum.inverse.control := fun h ↦ hx (ha h)
      have hxb : x ∉ b.datum.inverse.control := fun h ↦ hx (hb h)
      have hxab : x ∉ (a.sum b).datum.inverse.control := fun h ↦ h.elim hxa hxb
      simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa, dite_eq_right hxb,
        dite_eq_right hxab ]
      exact congrArg (fun w : a.source.Fiber x × b.source.Fiber x ↦
        ((ρ x : ℝ) : ℂ) • w) (raw_sum_symm_apply a.datum b.datum ⟨x, hxab⟩ w)
  intro z w
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
  have hsquare : (Vbase.linearEquiv z.val.proj).toLinearMap.comp
      (thomTensorSymbol ((a.sum b).datum.cutoffLinearMap ρ z.val.proj)
        ((a.sum b).datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd) =
      ((thomTensorSymbol (a.datum.cutoffLinearMap ρ z.val.proj)
          (a.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd).prodMap
        (thomTensorSymbol (b.datum.cutoffLinearMap ρ z.val.proj)
          (b.datum.inverse.cutoffLinearMap ρ z.val.proj) z.val.snd)).comp
        (Ubase.linearEquiv z.val.proj).toLinearMap := by
    exact thom_sum_generic
      (u₀.linearEquiv z.val.proj) (u₁.linearEquiv z.val.proj)
      (v₀.linearEquiv z.val.proj) (v₁.linearEquiv z.val.proj)
      (hu₀ z.val.proj) (hu₁ z.val.proj) (hv₀ z.val.proj) (hv₁ z.val.proj)
      (Ubase.linearEquiv z.val.proj) (Vbase.linearEquiv z.val.proj)
      (hUv z.val.proj) (hVv z.val.proj)
      ((a.sum b).datum.cutoffLinearMap ρ z.val.proj)
      ((a.sum b).datum.inverse.cutoffLinearMap ρ z.val.proj)
      (a.datum.cutoffLinearMap ρ z.val.proj) (b.datum.cutoffLinearMap ρ z.val.proj)
      (a.datum.inverse.cutoffLinearMap ρ z.val.proj)
      (b.datum.inverse.cutoffLinearMap ρ z.val.proj)
      (hd z.val.proj) (hd' z.val.proj) z.val.snd
  let zsum : (((Aa.sum Ab).control)ᶜ : Set Z) :=
    ⟨z.val, fun hz ↦ z.property (hsubset hz)⟩
  have hl := (hf z.val _).trans
    (congrArg (Vbase.linearEquiv z.val.proj) (hab_formula z w))
  have hpair := congrArg₂
    (fun (r : (p *ᵖ (target a)) z.val) (s : (p *ᵖ (target b)) z.val) ↦ (r, s))
    (ha_formula z (Ubase.linearEquiv z.val.proj w).1)
    (hb_formula z (Ubase.linearEquiv z.val.proj w).2)
  have hraw := RelativeTriple.sum_apply
    (Aa.enlarge _ (Aa.isCompact_control.union Ab.isCompact_control)
      Set.subset_union_left).boundary
    (Ab.enlarge _ (Aa.isCompact_control.union Ab.isCompact_control)
      Set.subset_union_right).boundary zsum (Ubase.linearEquiv z.val.proj w)
  have hraw' : (Aa.sum Ab).boundary.linearEquiv zsum
      (Ubase.linearEquiv z.val.proj w) =
      (Aa.boundary.linearEquiv ⟨zsum.val, fun hz ↦ zsum.property (Or.inl hz)⟩
          (Ubase.linearEquiv z.val.proj w).1,
        Ab.boundary.linearEquiv ⟨zsum.val, fun hz ↦ zsum.property (Or.inr hz)⟩
          (Ubase.linearEquiv z.val.proj w).2) := hraw.trans (Prod.ext
    (Aa.enlarge_apply _ (Aa.isCompact_control.union Ab.isCompact_control)
      Set.subset_union_left zsum (Ubase.linearEquiv z.val.proj w).1)
    (Ab.enlarge_apply _ (Aa.isCompact_control.union Ab.isCompact_control)
      Set.subset_union_right zsum (Ubase.linearEquiv z.val.proj w).2))
  have hr := (congrArg ((Aa.sum Ab).boundary.linearEquiv zsum) (he z.val w)).trans
    (hraw'.trans hpair)
  exact hl.trans ((LinearMap.congr_fun hsquare w).trans hr.symm)

omit a in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
-- Descend the prescribed tensor representatives through all support-triple relations.
/-- KA IV.1.10: tensoring every support representative defines one specified Thom operator. -/
theorem existsUnique_supportedThomHom :
    ∃! τ : CompactSupportKZero X →+ CompactSupportKZero (TotalSpace Unit E),
      ∀ (a : SupportBundleTriple X) (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
        (hcontrol : a.datum.control ⊆ U) (hzero : ∀ x ∈ U, ρ x = 0)
        (L : Set X) (hL : IsCompact L) (hone : ∀ x ∉ L, ρ x = 1),
        τ a.compactSupportClass =
          supportedThomProductClass E hinner a ρ U hU hcontrol hzero L hL hone := by
  /- Stage 1: exists_time_cutoff supplies admissible data for every original
  support triple. For two choices, pass to the union of compact controls and
  interpolate their cutoffs. Each interpolation still vanishes on a common
  neighborhood of the original control and equals one outside the common
  compact set. The tensor inverse formula yields a uniform boundary homotopy.
  Stage 2: the same tensor construction preserves isomorphism at infinity,
  direct sums and identity-triple relations. For an identity input one can
  use the constant cutoff one and empty control; its tensor symbol is globally
  invertible. For a general commuting boundary square, first enlarge the
  control so the square holds there, then choose a common vanishing cutoff.
  The inverse block transforms by the inverse square as well.
  Stage 3: descend through the existing supportTripleKZero universal property
  and its specified compact-support equivalence. Surjectivity of actual support
  representatives gives uniqueness. No class of the bare noncompact zero
  section and no arbitrary equivalence of K groups enters the construction.
  The cutoff pair gives a base odd operator of square -rho^2, while
  the exterior operator has square -norm(v)^2. The graded blocks therefore
  compose to -(rho^2 + norm(v)^2) times the identity; their inverse uses
  the negative reciprocal of this sum of squares. -/
  classical
  -- Choose admissible data only after showing that every such choice gives the same class.
  let CutoffData (a : SupportBundleTriple X) : Type _ :=
    { c : C(X, I) × Set X × Set X //
      IsOpen c.2.1 ∧ a.datum.control ⊆ c.2.1 ∧
      (∀ x ∈ c.2.1, c.1 x = 0) ∧ IsCompact c.2.2 ∧ ∀ x ∉ c.2.2, c.1 x = 1 }
  have hc (a : SupportBundleTriple X) : Nonempty (CutoffData a) := by
    obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
      exists_time_cutoff a.datum.control a.datum.isCompact_control
    exact ⟨⟨(ρ, U, L), hU, hcontrol, hzero, hL, hone⟩⟩
  let c (a : SupportBundleTriple X) : CutoffData a := Classical.choice (hc a)
  let value (a : SupportBundleTriple X) :=
    supportedThomProductClass E hinner a (c a).val.1 (c a).val.2.1
      (c a).property.1 (c a).property.2.1 (c a).property.2.2.1
      (c a).val.2.2 (c a).property.2.2.2.1 (c a).property.2.2.2.2
  have chosen (a : SupportBundleTriple X) (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
      (hcontrol : a.datum.control ⊆ U) (hzero : ∀ x ∈ U, ρ x = 0)
      (L : Set X) (hL : IsCompact L) (hone : ∀ x ∉ L, ρ x = 1) :
      value a = supportedThomProductClass E hinner a ρ U hU hcontrol hzero L hL hone :=
    supportedThomProductClass_eq_of_cutoff E hinner a (c a)
      ⟨(ρ, U, L), hU, hcontrol, hzero, hL, hone⟩
  -- First relation: enlarge the original isomorphism square, then use one cutoff on its exterior.
  have thom_isomorphic
      (a : SupportBundleTriple X)
      (b : SupportBundleTriple X)
      (K : Set X) (hK : IsCompact K) (ha : a.datum.control ⊆ K)
      (hb : b.datum.control ⊆ K)
      (u : Iso a.source.Fiber b.source.Fiber) (v : Iso a.target.Fiber b.target.Fiber)
      (hs : ∀ (x : (Kᶜ : Set X)) (w : a.source.Fiber x),
        v.linearEquiv x ((a.datum.enlarge K hK ha).boundary.linearEquiv x w) =
          (b.datum.enlarge K hK hb).boundary.linearEquiv x (u.linearEquiv x w))
      (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hKU : K ⊆ U)
      (hzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
      (hone : ∀ x ∉ L, ρ x = 1) :
      supportedThomProductClass E hinner a ρ U hU (ha.trans hKU) hzero L hL hone =
        supportedThomProductClass E hinner b ρ U hU (hb.trans hKU) hzero L hL hone := by
    as_aux_lemma =>
      classical
      apply supportedThomProductClass_eq_of_intertwining E hinner a b
        ⟨(ρ, U, L), hU, ha.trans hKU, hzero, hL, hone⟩
        ⟨(ρ, U, L), hU, hb.trans hKU, hzero, hL, hone⟩ u v
      · intro x w
        by_cases hx : x ∈ U
        · simp only [CompactSupportTriple.cutoffLinearMap, hzero x hx,
            Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
          split_ifs <;> exact map_zero _
        · have hxa : x ∉ a.datum.control := fun h ↦ hx (hKU (ha h))
          have hxb : x ∉ b.datum.control := fun h ↦ hx (hKU (hb h))
          let y : (Kᶜ : Set X) := ⟨x, fun h ↦ hx (hKU h)⟩
          have hh := hs y w
          rw [a.datum.enlarge_apply, b.datum.enlarge_apply] at hh
          simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa, dite_eq_right hxb]
          change v.linearEquiv x (((ρ x : ℝ) : ℂ) •
              a.datum.boundary.linearEquiv ⟨x, hxa⟩ w) =
            ((ρ x : ℝ) : ℂ) • b.datum.boundary.linearEquiv ⟨x, hxb⟩ (u.linearEquiv x w)
          rw [map_smul]
          exact congrArg (fun z ↦ (((ρ x : ℝ) : ℂ)) • z) hh
      · intro x w
        by_cases hx : x ∈ U
        · simp only [CompactSupportTriple.cutoffLinearMap, hzero x hx,
            Set.Icc.coe_zero, Complex.ofReal_zero, zero_smul]
          split_ifs <;> exact map_zero _
        · have hxa : x ∉ a.datum.inverse.control := fun h ↦ hx (hKU (ha h))
          have hxb : x ∉ b.datum.inverse.control := fun h ↦ hx (hKU (hb h))
          let y : (Kᶜ : Set X) := ⟨x, fun h ↦ hx (hKU h)⟩
          let ea := a.datum.boundary.linearEquiv ⟨x, hxa⟩
          let eb := b.datum.boundary.linearEquiv ⟨x, hxb⟩
          have hh : u.linearEquiv x (ea.symm w) = eb.symm (v.linearEquiv x w) := by
            apply eb.injective
            rw [LinearEquiv.apply_symm_apply]
            have hc := hs y (ea.symm w)
            rw [a.datum.enlarge_apply, b.datum.enlarge_apply] at hc
            change v.linearEquiv x (ea (ea.symm w)) = eb (u.linearEquiv x (ea.symm w)) at hc
            rw [LinearEquiv.apply_symm_apply] at hc
            exact hc.symm
          simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hxa, dite_eq_right hxb]
          change u.linearEquiv x (((ρ x : ℝ) : ℂ) • ea.symm w) =
            ((ρ x : ℝ) : ℂ) • eb.symm (v.linearEquiv x w)
          rw [map_smul]
          exact congrArg (fun z ↦ (((ρ x : ℝ) : ℂ)) • z) hh
  have hi (a b : SupportBundleTriple X) (hab : a.IsIsomorphic b) : value a = value b := by
    obtain ⟨K, hK, ha, hb, u, v, hs⟩ := hab
    obtain ⟨U, hU, hKU, L, hL, _hUL, ρ, hzero, hone⟩ := exists_time_cutoff K hK
    exact (chosen a ρ U hU (ha.trans hKU) hzero L hL hone).trans
      ((thom_isomorphic a b K hK ha hb u v hs ρ U hU hKU hzero L hL hone).trans
        (chosen b ρ U hU (hb.trans hKU) hzero L hL hone).symm)
  -- Second relation: use one cutoff for the union of the two original controls.
  have hs (a b : SupportBundleTriple X) : value (a.sum b) = value a + value b := by
    obtain ⟨U, hU, hcontrol, L, hL, _hUL, ρ, hzero, hone⟩ :=
      exists_time_cutoff (a.datum.control ∪ b.datum.control)
        (a.datum.isCompact_control.union b.datum.isCompact_control)
    have ha : a.datum.control ⊆ U := Set.subset_union_left.trans hcontrol
    have hb : b.datum.control ⊆ U := Set.subset_union_right.trans hcontrol
    exact (chosen (a.sum b) ρ U hU hcontrol hzero L hL hone).trans
      ((supportedThomProductClass_sum E hinner a b ρ U hU ha hb hzero L hL hone).trans
        (congrArg₂ (· + ·) (chosen a ρ U hU ha hzero L hL hone).symm
          (chosen b ρ U hU hb hzero L hL hone).symm))
  -- Third relation: the constant-one cutoff for an identity triple has empty zero control.
  have hz (F : FiniteBundle X) : value (SupportBundleTriple.identity F) = 0 := by
    rw [chosen (SupportBundleTriple.identity F) (ContinuousMap.const X 1) ∅
      isOpen_empty (Set.empty_subset _) (by simp) ∅ isCompact_empty (by simp)]
    let proj : C(TotalSpace Unit E, X) := ⟨π Unit E, continuous_proj⟩
    let G : X → Type _ := fun x ↦
      (F.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
        (F.Fiber x ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
    let : IsFiniteRank ((π Unit E) *ᵖ G) := isFiniteRank_pullback (E := G) proj
    have empty_control_class
        (c : CompactSupportTriple (proj *ᵖ G) (proj *ᵖ G)) (hempty : c.control = ∅) :
        c.compactSupportClass = 0 := by
      -- With empty control the original boundary is a global bundle isomorphism.
      let ρ : C(TotalSpace Unit E, I) := ContinuousMap.const (TotalSpace Unit E) 1
      have ha : c.control ⊆ ∅ := by rw [hempty]
      let q := c.cutoffHom ρ ∅ isOpen_empty ha (by simp)
      have hout (x : TotalSpace Unit E) : x ∉ c.control := by simp [hempty]
      have hq (x : TotalSpace Unit E) (v : (proj *ᵖ G) x) :
          q.linearMap x v = c.boundary.linearEquiv ⟨x, hout x⟩ v := by
        change c.cutoffLinearMap ρ x v = _
        simp only [CompactSupportTriple.cutoffLinearMap,
          ρ, ContinuousMap.const_apply, Set.Icc.coe_one, Complex.ofReal_one, one_smul]
        rw [dite_eq_right (hout x)]
        rfl
      have hbij (x : TotalSpace Unit E) : Function.Bijective (q.linearMap x) := by
        have hm : q.linearMap x = (c.boundary.linearEquiv ⟨x, hout x⟩).toLinearMap :=
          LinearMap.ext (hq x)
        rw [hm]
        exact (c.boundary.linearEquiv ⟨x, hout x⟩).bijective
      let e := q.toIso hbij
      let b := CompactSupportTriple.ofIso e
      have hb : b.control ⊆ ∅ := Set.empty_subset _
      -- The empty-window comparison keeps exactly this boundary and this inverse.
      have hboundary : (c.enlarge ∅ isCompact_empty ha).boundary =
          (b.enlarge ∅ isCompact_empty hb).boundary := by
        apply Iso.ext
        intro x
        apply LinearEquiv.ext
        intro v
        rw [c.enlarge_apply, b.enlarge_apply]
        change c.boundary.linearEquiv ⟨x.val, _⟩ v = e.linearEquiv x.val v
        exact (hq x.val v).symm
      have hhom : c.Homotopic b := by
        refine ⟨∅, isCompact_empty, ha, hb, ?_⟩
        rw [hboundary]
        exact IsoHomotopy.nonempty_refl _
      exact (c.compactSupportClass_eq_of_homotopic b hhom).trans
        (CompactSupportTriple.compactSupportClass_ofIso e)
    change (supportedThomTriple E hinner (SupportBundleTriple.identity F)
      (ContinuousMap.const X 1) ∅ isOpen_empty (Set.empty_subset _) (by simp)
      ∅ isCompact_empty (by simp)).compactSupportClass = 0
    apply empty_control_class
    ext z
    change (z.proj ∈ (∅ : Set X) ∧ z.snd = 0) ↔ z ∈ (∅ : Set (TotalSpace Unit E))
    simp
  -- Descend through the actual three-relation presentation and its specified geometric comparison.
  obtain ⟨τ, hτ, _hunique⟩ := supportTripleKZero_universal_property X value hi hs hz
  let τc := τ.comp (supportTripleKZeroCompactSupportEquiv (X := X)).symm.toAddMonoidHom
  have hτc (a : SupportBundleTriple X) (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
      (hcontrol : a.datum.control ⊆ U) (hzero : ∀ x ∈ U, ρ x = 0)
      (L : Set X) (hL : IsCompact L) (hone : ∀ x ∉ L, ρ x = 1) :
      τc a.compactSupportClass =
        supportedThomProductClass E hinner a ρ U hU hcontrol hzero L hL hone := by
    change τ (supportTripleKZeroCompactSupportEquiv.symm a.compactSupportClass) = _
    rw [supportTripleKZeroCompactSupportEquiv_symm_apply, hτ]
    exact chosen a ρ U hU hcontrol hzero L hL hone
  refine ⟨τc, hτc, ?_⟩
  intro other hother
  apply AddMonoidHom.ext
  intro z
  obtain ⟨a, rfl⟩ := supportBundleTriple_compactSupportClass_surjective z
  exact (hother a (c a).val.1 (c a).val.2.1 (c a).property.1 (c a).property.2.1
    (c a).property.2.2.1 (c a).val.2.2 (c a).property.2.2.2.1 (c a).property.2.2.2.2).trans
    (hτc a (c a).val.1 (c a).val.2.1 (c a).property.1 (c a).property.2.1
      (c a).property.2.2.1 (c a).val.2.2 (c a).property.2.2.2.1
      (c a).property.2.2.2.2).symm

omit a in
/-- The actual noncompact-base Thom homomorphism, fixed by all tensor representatives. -/
def supportedThomHom : CompactSupportKZero X →+ CompactSupportKZero (TotalSpace Unit E) :=
  (existsUnique_supportedThomHom E hinner).choose

/-- The Thom operator evaluates to the specified tensor triple for any admissible cutoff. -/
theorem supportedThomHom_class (ρ : C(X, I)) (U : Set X) (hU : IsOpen U)
    (hcontrol : a.datum.control ⊆ U) (hzero : ∀ x ∈ U, ρ x = 0)
    (L : Set X) (hL : IsCompact L) (hone : ∀ x ∉ L, ρ x = 1) :
    supportedThomHom E hinner a.compactSupportClass =
      supportedThomProductClass E hinner a ρ U hU hcontrol hzero L hL hone := by
  /- The defining unique homomorphism carries this equation for every original
  triple and every admissible cutoff. Extract that same characterization;
  no representative, boundary map or control is chosen independently. -/
  exact (existsUnique_supportedThomHom E hinner).choose_spec.1
    a ρ U hU hcontrol hzero L hL hone

set_option maxHeartbeats 600000 in
-- Compare original positive bundle generators with the compact-base exterior Thom action.
omit a in
attribute [local instance] trivialTopology isFiniteRank_trivial
  IdempotentMatrix.fiberTotalSpaceTopology IdempotentMatrix.isFiniteRank_fiber in
/-- On a compact base, the specified operator is the old action on the actual Thom class. -/
theorem supportedThomHom_compact [CompactSpace X] :
    supportedThomHom E hinner = (exteriorThomHom E hinner).comp
      (compactSupportKZeroCompactEquiv X).toAddMonoidHom := by
  /- On a compact base, first compute the original positive bundle generators using the
  zero cutoff and a zero-rank target. The canonical ungraded tensor flip identifies the
  remaining exterior block with the original graph action, without a sign change.
  Every absolute class is a difference of such generators; additivity and the specified
  compact-to-absolute equivalence then determine the full supported homomorphism. -/
  classical
  let τ := supportedThomHom E hinner
  have hτ := supportedThomHom_class E hinner
  have support_square
      {X : Type _} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
      {E F G H : X → Type _}
      [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
      [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
      [∀ x, AddCommGroup (G x)] [∀ x, Module ℂ (G x)]
      [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
      [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
      [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
      [TopologicalSpace (TotalSpace Unit G)] [IsFiniteRank G]
      [TopologicalSpace (TotalSpace Unit H)] [IsFiniteRank H]
      (a : CompactSupportTriple E F) (b : CompactSupportTriple G H)
      (u : Iso E G) (v : Iso F H) (K : Set X) (hK : IsCompact K)
      (ha : a.control ⊆ K) (hb : b.control ⊆ K)
      (hs : ∀ (x : (Kᶜ : Set X)) (w : E x.val),
        v.linearEquiv x.val
            (a.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w) =
          b.boundary.linearEquiv ⟨x.val, fun hx ↦ x.property (hb hx)⟩
            (u.linearEquiv x.val w)) :
      a.compactSupportClass = b.compactSupportClass := by
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    as_aux_lemma =>
      rw [← a.compactSupportClass_congr u v]
      apply CompactSupportTriple.compactSupportClass_eq_of_homotopic
      have heq : ((a.congr u v).enlarge K hK ha).boundary =
          (b.enlarge K hK hb).boundary := by
        apply Iso.ext
        intro x
        apply LinearEquiv.ext
        intro w
        have h := hs x ((u.linearEquiv x.val).symm w)
        rw [LinearEquiv.apply_symm_apply] at h
        have hl := (a.congr u v).enlarge_apply K hK ha x w
        have hc := a.congr_apply u v ⟨x.val, fun hx ↦ x.property (ha hx)⟩ w
        have hv := b.enlarge_apply K hK hb x w
        exact hl.trans (hc.trans (h.trans hv.symm))
      refine ⟨K, hK, ha, hb, ?_⟩
      rw [heq]
      exact IsoHomotopy.nonempty_refl _
  let e := compactSupportKZeroCompactEquiv X
  let Z := TotalSpace Unit E
  let p : C(Z, X) := ⟨π Unit E, continuous_proj⟩
  let evenPart : X → Type _ := fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0
  let oddPart : X → Type _ := fun x : X ↦ CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1
  let : IsFiniteRank ((π Unit E) *ᵖ evenPart) := isFiniteRank_pullback (E := evenPart) p
  let : IsFiniteRank ((π Unit E) *ᵖ oddPart) := isFiniteRank_pullback (E := oddPart) p
  -- This elementary tensor calculation is independent of support choices and bundle charts.
  have fiber_comm (x : X) (F G : Type) [AddCommGroup F] [Module ℂ F]
      [AddCommGroup G] [Module ℂ G] [Subsingleton G]
      (d : F →ₗ[ℂ] G) (d' : G →ₗ[ℂ] F) (v : E x)
      (w : (F ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) ×
        (G ⊗[ℂ] CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)) :
      TensorProduct.comm ℂ F (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 1)
          ((thomTensorSymbol d d' v w).2) =
        TensorProduct.map (cliffordSymbolParity v 0) (LinearMap.id : F →ₗ[ℂ] F)
          (TensorProduct.comm ℂ F (CliffordAlgebra.evenOdd (0 : QuadraticForm ℂ (E x)) 0) w.1) := by
    have hw : w.2 = 0 := Subsingleton.elim _ _
    simp only [thomTensorSymbol, LinearMap.prod_apply, Function.prod, LinearMap.coprod_apply,
      hw, map_zero, add_zero]
    induction w.1 using TensorProduct.inductionOn with
    | tmul x y => simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        TensorProduct.comm_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  -- It suffices to compute positive bundle generators: additivity then handles differences.
  have positive (W : FiniteBundle X) :
      τ (e.symm W.kZeroClass) = exteriorThomHom E hinner W.kZeroClass := by
    let O := FiniteBundle.trivial X 0
    let a : SupportBundleTriple X :=
      { source := W
        target := O
        datum :=
          { control := Set.univ
            isCompact_control := isCompact_univ
            boundary :=
              { linearEquiv x := False.elim (x.property (Set.mem_univ x.val))
                continuous_total := by
                  apply continuous_iff_continuousAt.mpr
                  intro z
                  exact False.elim (z.proj.property (Set.mem_univ _))
                continuous_symm := by
                  apply continuous_iff_continuousAt.mpr
                  intro z
                  exact False.elim (z.proj.property (Set.mem_univ _)) } } }
    have ha : e a.compactSupportClass = W.kZeroClass := by
      change compactSupportKZeroToAbsolute a.compactSupportClass = _
      rw [SupportBundleTriple.compactSupportClass_toAbsolute]
      change W.kZeroClass - kZeroClass (Bundle.Trivial X (Fin 0 → ℂ)) = _
      rw [kZeroClass_trivial_zero, sub_zero]
    have hae : e.symm W.kZeroClass = a.compactSupportClass := by
      rw [← ha, e.symm_apply_apply]
    rw [hae, hτ a (ContinuousMap.const X 0) Set.univ isOpen_univ
      (Set.subset_univ _) (by simp) Set.univ isCompact_univ (by simp)]
    let S := fun x : X ↦ (W.Fiber x ⊗[ℂ] evenPart x) × (O.Fiber x ⊗[ℂ] oddPart x)
    let T := fun x : X ↦ (O.Fiber x ⊗[ℂ] evenPart x) × (W.Fiber x ⊗[ℂ] oddPart x)
    let : IsFiniteRank ((π Unit E) *ᵖ S) := isFiniteRank_pullback (E := S) p
    let : IsFiniteRank ((π Unit E) *ᵖ T) := isFiniteRank_pullback (E := T) p
    let : IsFiniteRank ((π Unit E) *ᵖ W.Fiber) := isFiniteRank_pullback (E := W.Fiber) p
    let b : CompactSupportTriple ((π Unit E) *ᵖ S) ((π Unit E) *ᵖ T) :=
      supportedThomTriple E hinner a (ContinuousMap.const X 0)
      Set.univ isOpen_univ (Set.subset_univ _) (by simp)
      Set.univ isCompact_univ (by simp)
    let c : CompactSupportTriple
        (fun z : Z ↦ ((π Unit E) *ᵖ evenPart) z ⊗[ℂ] ((π Unit E) *ᵖ W.Fiber) z)
        (fun z : Z ↦ ((π Unit E) *ᵖ oddPart) z ⊗[ℂ] ((π Unit E) *ᵖ W.Fiber) z) :=
      (exteriorThomTriple E hinner).tensorRight ((π Unit E) *ᵖ W.Fiber)
    -- The coefficient bundle is ungraded, so interchanging it introduces no sign.
    let flip (H : X → Type _) [∀ x, AddCommGroup (H x)] [∀ x, Module ℂ (H x)]
        [TopologicalSpace (TotalSpace Unit H)] :
        Hom (fun x ↦ W.Fiber x ⊗[ℂ] H x) (fun x ↦ H x ⊗[ℂ] W.Fiber x) :=
      { linearMap x := (TensorProduct.comm ℂ (W.Fiber x) (H x)).toLinearMap
        continuous_total := by
          apply continuous_iSup_dom.mpr
          intro k
          apply continuous_coinduced_dom.mpr
          let D := TotalSpace Unit (fun x : X ↦ (Fin k → W.Fiber x) × (Fin k → H x))
          let D' := TotalSpace Unit (fun x : X ↦ (Fin k → H x) × (Fin k → W.Fiber x))
          let : TopologicalSpace D := TopologicalSpace.induced
            (fun z : D ↦ (z.proj,
              (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit W.Fiber)),
              (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit H)))) inferInstance
          let : TopologicalSpace D' := TopologicalSpace.induced
            (fun z : D' ↦ (z.proj,
              (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit H)),
              (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit W.Fiber)))) inferInstance
          have hd : Continuous (fun z : D ↦ (z.proj,
              (fun i ↦ (⟨z.proj, z.snd.1 i⟩ : TotalSpace Unit W.Fiber)),
              (fun i ↦ (⟨z.proj, z.snd.2 i⟩ : TotalSpace Unit H)))) := continuous_induced_dom
          let swap (z : D) : D' := ⟨z.proj, z.snd.2, z.snd.1⟩
          have hs : Continuous swap :=
            continuous_induced_rng.mpr (hd.fst.prodMk (hd.snd.snd.prodMk hd.snd.fst))
          have hg : Continuous (fun z : D' ↦
              (⟨z.proj, ∑ i : Fin k, z.snd.1 i ⊗ₜ[ℂ] z.snd.2 i⟩ :
                TotalSpace Unit (fun x : X ↦ H x ⊗[ℂ] W.Fiber x))) :=
            continuous_iSup_rng (i := k) continuous_coinduced_rng
          apply (hg.comp hs).congr
          intro z
          simp only [Function.comp_apply, swap, map_sum]
          rfl }
    let u₀ := ((pullbackTensorIso (E := evenPart) (F := W.Fiber) p).toHom).comp
      (((flip evenPart).pullback p).comp
        ((sumFst (E := fun x ↦ W.Fiber x ⊗[ℂ] evenPart x)
          (F := fun x ↦ O.Fiber x ⊗[ℂ] oddPart x)).pullback p))
    let v₀ := ((pullbackTensorIso (E := oddPart) (F := W.Fiber) p).toHom).comp
      (((flip oddPart).pullback p).comp
        ((sumSnd (E := fun x ↦ O.Fiber x ⊗[ℂ] evenPart x)
          (F := fun x ↦ W.Fiber x ⊗[ℂ] oddPart x)).pullback p))
    have hu (z : Z) : Function.Bijective (u₀.linearMap z) := by
      change Function.Bijective (fun w : S z.proj ↦
        TensorProduct.comm ℂ (W.Fiber z.proj) (evenPart z.proj) w.1)
      constructor
      · intro w w' h
        exact Prod.ext ((TensorProduct.comm ℂ _ _).injective h) (Subsingleton.elim _ _)
      · intro w
        exact ⟨((TensorProduct.comm ℂ _ _).symm w, 0),
          (TensorProduct.comm ℂ _ _).apply_symm_apply w⟩
    have hv (z : Z) : Function.Bijective (v₀.linearMap z) := by
      change Function.Bijective (fun w : T z.proj ↦
        TensorProduct.comm ℂ (W.Fiber z.proj) (oddPart z.proj) w.2)
      constructor
      · intro w w' h
        exact Prod.ext (Subsingleton.elim _ _) ((TensorProduct.comm ℂ _ _).injective h)
      · intro w
        exact ⟨(0, (TensorProduct.comm ℂ _ _).symm w),
          (TensorProduct.comm ℂ _ _).apply_symm_apply w⟩
    let u := u₀.toIso hu
    let v := v₀.toIso hv
    have hb : b.control ⊆ c.control := fun _ h ↦ h.2
    have hc : c.control ⊆ c.control := Set.Subset.rfl
    have hright : c.compactSupportClass = exteriorThomHom E hinner W.kZeroClass :=
      CompactSupportTriple.compactSupportClass_tensorRight_pullback
        W.Fiber (exteriorThomTriple E hinner) p
    have hleft : supportedThomProductClass E hinner a (ContinuousMap.const X 0)
        Set.univ isOpen_univ (Set.subset_univ _) (by simp)
        Set.univ isCompact_univ (by simp) = b.compactSupportClass := rfl
    have hbmap (z : (b.controlᶜ : Set Z)) (w : S z.val.proj) :
        b.boundary.linearEquiv z w = thomTensorSymbol
          (a.datum.cutoffLinearMap (ContinuousMap.const X 0) z.val.proj)
          (a.datum.inverse.cutoffLinearMap (ContinuousMap.const X 0) z.val.proj) z.val.snd w := rfl
    have hcmap (z : (c.controlᶜ : Set Z))
        (w : evenPart z.val.proj ⊗[ℂ] W.Fiber z.val.proj) :
        c.boundary.linearEquiv z w =
          TensorProduct.map (cliffordSymbolParity z.val.snd 0)
            (LinearMap.id : W.Fiber z.val.proj →ₗ[ℂ] W.Fiber z.val.proj) w := rfl
    have humap (z : Z) (w : S z.proj) : u.linearEquiv z w =
        TensorProduct.comm ℂ (W.Fiber z.proj) (evenPart z.proj) w.1 := rfl
    have hvmap (z : Z) (w : T z.proj) : v.linearEquiv z w =
        TensorProduct.comm ℂ (W.Fiber z.proj) (oddPart z.proj) w.2 := rfl
    clear_value b c u v u₀ v₀
    have hclass : b.compactSupportClass = c.compactSupportClass := by
      apply support_square b c u v c.control c.isCompact_control hb hc
      intro z w
      let zb : (b.controlᶜ : Set Z) := ⟨z.val, fun hz ↦ z.property (hb hz)⟩
      let d := a.datum.cutoffLinearMap (ContinuousMap.const X 0) z.val.proj
      let d' := a.datum.inverse.cutoffLinearMap (ContinuousMap.const X 0) z.val.proj
      let out := thomTensorSymbol d d' z.val.snd w
      let m := TensorProduct.map (cliffordSymbolParity z.val.snd 0)
        (LinearMap.id : W.Fiber z.val.proj →ₗ[ℂ] W.Fiber z.val.proj)
      have h₁ := hbmap zb w
      have h₂ := hvmap z.val out
      have h₃ := fiber_comm z.val.proj (W.Fiber z.val.proj) (O.Fiber z.val.proj)
        d d' z.val.snd w
      have h₄ := humap z.val w
      have h₅ := hcmap z (u.linearEquiv z.val w)
      change v.linearEquiv z.val (b.boundary.linearEquiv zb w) =
        c.boundary.linearEquiv z (u.linearEquiv z.val w)
      exact (congrArg (v.linearEquiv z.val) h₁).trans
        (h₂.trans (h₃.trans ((congrArg m h₄.symm).trans h₅.symm)))
    exact hleft.trans (hclass.trans hright)
  -- Every original absolute class is a difference of these actual bundle classes.
  apply AddMonoidHom.ext
  intro x
  obtain ⟨q, n, hq⟩ := exists_class_sub_trivial (e x)
  let W := smallBundle (fun x ↦ q.fiber x)
  have hW : W.kZeroClass = kZeroClass (fun x ↦ q.fiber x) :=
    (kZeroClass_eq_of_iso (smallBundleIso (fun x ↦ q.fiber x))).symm
  rw [← hW] at hq
  have hx : x = e.symm W.kZeroClass - e.symm (FiniteBundle.trivial X n).kZeroClass := by
    apply e.injective
    rw [map_sub, e.apply_symm_apply, e.apply_symm_apply]
    exact hq
  change τ x = exteriorThomHom E hinner (e x)
  rw [hx, map_sub, positive W, positive (FiniteBundle.trivial X n),
    map_sub, e.apply_symm_apply, e.apply_symm_apply, map_sub]


end AtiyahSinger.ComplexBundle
