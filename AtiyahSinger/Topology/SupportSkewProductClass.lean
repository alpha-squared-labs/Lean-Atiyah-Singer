/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.SupportSkewProductNormalization
public import AtiyahSinger.Topology.SupportTripleHomotopy
public import AtiyahSinger.Topology.ThomTensorReassociation

/-!
# The supported product of two actual skew symbols

Public module ID: M2188.

A fixed compact enlargement supports the whole reciprocal-cutoff homotopy.
The terminal map is the positive-convention reciprocal block with negative
skew reverse maps. This sign is kept explicit for the Clifford comparison.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback

private def addHom {Z : Type*} [TopologicalSpace Z] {E F : Z → Type*}
    [∀ z, AddCommGroup (E z)] [∀ z, Module ℂ (E z)]
    [∀ z, AddCommGroup (F z)] [∀ z, Module ℂ (F z)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (a b : Hom E F) (c : ℂ) : Hom E F where
  linearMap z := a.linearMap z + c • b.linearMap z
  continuous_total := by
    let p : C(TotalSpace Unit E, Z) := ⟨π Unit E, continuous_proj⟩
    have ha : Continuous (fun z : TotalSpace Unit E ↦
        (⟨z, a.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ F))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact continuous_id.prodMk a.continuous_total
    have hb : Continuous (fun z : TotalSpace Unit E ↦
        (⟨z, b.linearMap z.proj z.snd⟩ : TotalSpace Unit (p *ᵖ F))) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit F p).continuous_iff]
      exact continuous_id.prodMk b.continuous_total
    exact (Pullback.continuous_lift Unit F p).comp
      (continuous_add_section (p *ᵖ F) _ _ ha
        (continuous_smul_section _ (ContinuousMap.const _ c) _ hb))

/-- The original reciprocal tensor block is continuous in the native tensor and sum bundles. -/
def reciprocalTensorHom {Z : Type*} [TopologicalSpace Z]
    {E₀ E₁ F₀ F₁ : Z → Type*}
    [∀ z, AddCommGroup (E₀ z)] [∀ z, Module ℂ (E₀ z)]
    [∀ z, AddCommGroup (E₁ z)] [∀ z, Module ℂ (E₁ z)]
    [∀ z, AddCommGroup (F₀ z)] [∀ z, Module ℂ (F₀ z)]
    [∀ z, AddCommGroup (F₁ z)] [∀ z, Module ℂ (F₁ z)]
    [TopologicalSpace (TotalSpace Unit E₀)] [IsFiniteRank E₀]
    [TopologicalSpace (TotalSpace Unit E₁)] [IsFiniteRank E₁]
    [TopologicalSpace (TotalSpace Unit F₀)] [IsFiniteRank F₀]
    [TopologicalSpace (TotalSpace Unit F₁)] [IsFiniteRank F₁]
    (d : Hom E₀ E₁) (d' : Hom E₁ E₀) (e : Hom F₀ F₁) (e' : Hom F₁ F₀) :
    Hom (fun z ↦ (E₀ z ⊗[ℂ] F₀ z) × (E₁ z ⊗[ℂ] F₁ z))
      (fun z ↦ (E₁ z ⊗[ℂ] F₀ z) × (E₀ z ⊗[ℂ] F₁ z)) where
  linearMap z := reciprocalTensorSymbol (d.linearMap z) (d'.linearMap z)
    (e.linearMap z) (e'.linearMap z)
  continuous_total := by
    let upper := addHom ((d.tensor (Hom.id _)).comp sumFst)
      (((Hom.id _).tensor e').comp sumSnd) (-1)
    let lower := addHom (((Hom.id _).tensor e).comp sumFst)
      ((d'.tensor (Hom.id _)).comp sumSnd) 1
    apply continuous_induced_rng.mpr
    apply (upper.continuous_total.prodMk lower.continuous_total).congr
    intro z
    apply Prod.ext <;> apply congrArg (TotalSpace.mk z.proj) <;>
      simp only [upper, lower, addHom, Hom.comp, Hom.tensor, Hom.id, sumFst, sumSnd,
        reciprocalTensorSymbol, LinearMap.prod_apply, LinearMap.coprod_apply,
        LinearMap.comp_apply, LinearMap.add_apply, LinearMap.neg_apply,
        LinearMap.fst_apply, LinearMap.snd_apply, Function.prod, neg_one_smul, one_smul]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exists_cylinderPullbackHom {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {E F : X → Type*}
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)]
    [TopologicalSpace (TotalSpace Unit E)] [IsFiniteRank E]
    [TopologicalSpace (TotalSpace Unit F)] [IsFiniteRank F]
    (f : C(Y, X))
    (d : Hom ((Prod.snd : I × X → X) *ᵖ E) ((Prod.snd : I × X → X) *ᵖ F)) :
    ∃ D : Hom ((Prod.snd : I × Y → Y) *ᵖ (f *ᵖ E))
      ((Prod.snd : I × Y → Y) *ᵖ (f *ᵖ F)),
      ∀ z, D.linearMap z = d.linearMap (z.1, f z.2) := by
  let pX : C(I × X, X) := ContinuousMap.snd
  let pY : C(I × Y, Y) := ContinuousMap.snd
  let q : C(I × Y, I × X) := ⟨fun z ↦ (z.1, f z.2),
    continuous_fst.prodMk (f.continuous.comp continuous_snd)⟩
  let iE := (pullbackCompIso (E := E) f pY).trans
    (pullbackCompIso (E := E) pX q).symm
  let iF := (pullbackCompIso (E := F) f pY).trans
    (pullbackCompIso (E := F) pX q).symm
  have hiE (z : I × Y) (v : E (f z.2)) : iE.linearEquiv z v = v := by
    apply (pullbackCompIso (E := E) pX q).linearEquiv z |>.injective
    change (pullbackCompIso (E := E) pX q).linearEquiv z
      (((pullbackCompIso (E := E) pX q).linearEquiv z).symm
        ((pullbackCompIso (E := E) f pY).linearEquiv z v)) = _
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  have hiF (z : I × Y) (v : F (f z.2)) : (iF.linearEquiv z).symm v = v := by
    change ((pullbackCompIso (E := F) f pY).linearEquiv z).symm
      ((pullbackCompIso (E := F) pX q).linearEquiv z v) = v
    apply ((pullbackCompIso (E := F) f pY).linearEquiv z).injective
    rw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, pullbackCompIso_apply]
  refine ⟨iF.symm.toHom.comp ((d.pullback q).comp iE.toHom), ?_⟩
  intro z
  apply LinearMap.ext
  intro v
  change (iF.linearEquiv z).symm (d.linearMap (z.1, f z.2) (iE.linearEquiv z v)) = _
  rw [hiE, hiF]
  rfl

set_option maxHeartbeats 1800000 in

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The actual positive tensor block of two skew symbols represents their supported product. -/
theorem SupportBundleTriple.compactSupportClass_externalProduct_of_skew
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] [T2Space Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    (a : SupportBundleTriple X) (b : SupportBundleTriple Y)
    (c : Hom a.source.Fiber a.target.Fiber) (c' : Hom a.target.Fiber a.source.Fiber)
    (e : Hom b.source.Fiber b.target.Fiber) (e' : Hom b.target.Fiber b.source.Fiber)
    (r : X → ℝ) (s : Y → ℝ)
    (hc : ∀ x : (a.datum.controlᶜ : Set X),
      (a.datum.boundary.linearEquiv x).toLinearMap = c.linearMap x.val)
    (he : ∀ y : (b.datum.controlᶜ : Set Y),
      (b.datum.boundary.linearEquiv y).toLinearMap = e.linearMap y.val)
    (hcq : ∀ x, (c'.linearMap x).comp (c.linearMap x) = -(r x : ℂ) • LinearMap.id ∧
      (c.linearMap x).comp (c'.linearMap x) = -(r x : ℂ) • LinearMap.id)
    (heq : ∀ y, (e'.linearMap y).comp (e.linearMap y) = -(s y : ℂ) • LinearMap.id ∧
      (e.linearMap y).comp (e'.linearMap y) = -(s y : ℂ) • LinearMap.id)
    (hr : ∀ x, 0 ≤ r x) (hs : ∀ y, 0 ≤ s y)
    (hrpos : ∀ x ∉ a.datum.control, 0 < r x)
    (hspos : ∀ y ∉ b.datum.control, 0 < s y)
    (k : CompactSupportTriple (a.externalProductSource b).Fiber
      (a.externalProductTarget b).Fiber)
    (hkcontrol : k.control ⊆ a.datum.control ×ˢ b.datum.control)
    (hk : ∀ z : (k.controlᶜ : Set (X × Y)),
      (k.boundary.linearEquiv z).toLinearMap =
        reciprocalTensorSymbol (c.linearMap z.val.1) (-c'.linearMap z.val.1)
          (e.linearMap z.val.2) (-e'.linearMap z.val.2)) :
    k.compactSupportClass =
      compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  classical
  -- Choose one compact product control for the entire homotopy.
  obtain ⟨U, hU, haU, L, hL, hUL, ρ, hzero, hone⟩ :=
    exists_time_cutoff a.datum.control a.datum.isCompact_control
  obtain ⟨V, hV, hbV, M, hM, hVM, τ, hbzero, hbone⟩ :=
    exists_time_cutoff b.datum.control b.datum.isCompact_control
  obtain ⟨d, d', hd, hd', hdq, hdnonneg, hdpos⟩ :=
    a.datum.exists_skew_cutoff_homotopy c c' r hc hcq hr hrpos
      ρ U hU haU hzero L hUL hone
  obtain ⟨f, f', hf, hf', hfq, hfnonneg, hfpos⟩ :=
    b.datum.exists_skew_cutoff_homotopy e e' s he heq hs hspos
      τ V hV hbV hbzero M hVM hbone
  let q (z : I × X) : ℝ :=
    (1 - (z.1 : ℝ)) ^ 2 * (ρ z.2 : ℝ) ^ 2 +
      (z.1 : ℝ) * (1 - (z.1 : ℝ)) * (ρ z.2 : ℝ) * (1 + r z.2) +
      (z.1 : ℝ) ^ 2 * r z.2
  let q' (z : I × Y) : ℝ :=
    (1 - (z.1 : ℝ)) ^ 2 * (τ z.2 : ℝ) ^ 2 +
      (z.1 : ℝ) * (1 - (z.1 : ℝ)) * (τ z.2 : ℝ) * (1 + s z.2) +
      (z.1 : ℝ) ^ 2 * s z.2
  let p : C(I × (X × Y), X × Y) := ContinuousMap.snd
  let p₁ : C(X × Y, X) := ContinuousMap.fst
  let p₂ : C(X × Y, Y) := ContinuousMap.snd
  let E₀ := p₁ *ᵖ a.source.Fiber
  let E₁ := p₁ *ᵖ a.target.Fiber
  let F₀ := p₂ *ᵖ b.source.Fiber
  let F₁ := p₂ *ᵖ b.target.Fiber
  let : IsFiniteRank ((Prod.snd : I × (X × Y) → X × Y) *ᵖ E₀) :=
    isFiniteRank_pullback p
  let : IsFiniteRank ((Prod.snd : I × (X × Y) → X × Y) *ᵖ E₁) :=
    isFiniteRank_pullback p
  let : IsFiniteRank ((Prod.snd : I × (X × Y) → X × Y) *ᵖ F₀) :=
    isFiniteRank_pullback p
  let : IsFiniteRank ((Prod.snd : I × (X × Y) → X × Y) *ᵖ F₁) :=
    isFiniteRank_pullback p
  -- Native pullback comparisons retain the same tensor vectors over the cylinder.
  obtain ⟨D, hD⟩ := exists_cylinderPullbackHom p₁ d
  obtain ⟨D', hD'⟩ := exists_cylinderPullbackHom p₁ d'
  obtain ⟨F, hF⟩ := exists_cylinderPullbackHom p₂ f
  obtain ⟨F', hF'⟩ := exists_cylinderPullbackHom p₂ f'
  obtain ⟨iS, hiS⟩ := tensorSum_pullback_comparison
    (E := E₀) (F := F₀) (G := E₁) (H := F₁) p
  obtain ⟨iT, hiT⟩ := tensorSum_pullback_comparison
    (E := E₁) (F := F₀) (G := E₀) (H := F₁) p
  let block := reciprocalTensorHom D D' F F'
  let family : Hom (p *ᵖ (a.externalProductSource b).Fiber)
      (p *ᵖ (a.externalProductTarget b).Fiber) :=
    iT.toHom.comp (block.comp iS.symm.toHom)
  have hfamily (z : I × (X × Y)) : family.linearMap z =
      reciprocalTensorSymbol (d.linearMap (z.1, z.2.1)) (d'.linearMap (z.1, z.2.1))
        (f.linearMap (z.1, z.2.2)) (f'.linearMap (z.1, z.2.2)) := by
    apply LinearMap.ext
    intro v
    have hiSi : (iS.linearEquiv z).symm v = v := by
      apply (iS.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply, hiS]
    change iT.linearEquiv z (block.linearMap z ((iS.linearEquiv z).symm v)) = _
    rw [hiT, hiSi]
    change reciprocalTensorSymbol (D.linearMap z) (D'.linearMap z)
      (F.linearMap z) (F'.linearMap z) v = _
    rw [hD, hD', hF, hF']
    rfl
  let K : Set (X × Y) := L ×ˢ M
  have hK : IsCompact K := hL.prod hM
  have hkK : k.control ⊆ K := fun z hz ↦
    ⟨hUL (haU (hkcontrol hz).1), hVM (hbV (hkcontrol hz).2)⟩
  let inc : C((Kᶜ : Set (X × Y)), X × Y) := ⟨Subtype.val, continuous_subtype_val⟩
  obtain ⟨R, hR⟩ := exists_cylinderPullbackHom inc family
  let pK : C(I × (Kᶜ : Set (X × Y)), (Kᶜ : Set (X × Y))) := ContinuousMap.snd
  let : IsFiniteRank ((Prod.snd : I × (Kᶜ : Set (X × Y)) → _) *ᵖ
      (inc *ᵖ (a.externalProductSource b).Fiber)) := isFiniteRank_pullback pK
  let : IsFiniteRank ((Prod.snd : I × (Kᶜ : Set (X × Y)) → _) *ᵖ
      (inc *ᵖ (a.externalProductTarget b).Fiber)) := isFiniteRank_pullback pK
  have hbij (z : I × (Kᶜ : Set (X × Y))) : Function.Bijective (R.linearMap z) := by
    rw [hR, hfamily]
    have hpositive : 0 < q (z.1, z.2.val.1) + q' (z.1, z.2.val.2) := by
      rcases not_and_or.mp z.2.property with hx | hy
      · exact add_pos_of_pos_of_nonneg (hdpos (z.1, z.2.val.1) hx)
          (hfnonneg (z.1, z.2.val.2))
      · exact add_pos_of_nonneg_of_pos (hdnonneg (z.1, z.2.val.1))
          (hfpos (z.1, z.2.val.2) hy)
    have hnonzero : (q (z.1, z.2.val.1) : ℂ) + (q' (z.1, z.2.val.2) : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt hpositive)
    exact (reciprocalTensorSymbolEquiv _ _ _ _ _ _
      (hdq (z.1, z.2.val.1)).1 (hdq (z.1, z.2.val.1)).2
      (hfq (z.1, z.2.val.2)).1 (hfq (z.1, z.2.val.2)).2 hnonzero).bijective
  let c₀ := supportedExternalProductTriple a b ρ U hU haU hzero L hL hone
    τ V hV hbV hbzero M hM hbone
  -- At time zero the maps are the prescribed cutoffs; at one the reverse maps are negative.
  have hhom : c₀.datum.Homotopic k := by
    refine ⟨K, hK, Set.Subset.refl _, hkK, ⟨{
      iso := R.toIso hbij
      map_zero := ?_
      map_one := ?_ }⟩⟩
    · intro z v
      rw [CompactSupportTriple.enlarge_apply]
      change R.linearMap (0, z) v = _
      rw [hR, hfamily, hd, hd', hf, hf']
      simp only [Set.Icc.coe_zero, sub_zero, Complex.ofReal_one, Complex.ofReal_zero,
        one_smul, zero_smul, add_zero]
      rfl
    · intro z v
      rw [CompactSupportTriple.enlarge_apply]
      change R.linearMap (1, z) v = _
      rw [hR, hfamily, hd, hd', hf, hf']
      simp only [Set.Icc.coe_one, sub_self, Complex.ofReal_one, Complex.ofReal_zero,
        one_smul, zero_smul, zero_add, zero_sub]
      exact (LinearMap.congr_fun (hk ⟨z.val, fun hz ↦ z.property (hkK hz)⟩) v).symm
  calc
    k.compactSupportClass = c₀.datum.compactSupportClass :=
      (c₀.datum.compactSupportClass_eq_of_homotopic k hhom).symm
    _ = c₀.compactSupportClass :=
      compactSupportTriple_compactSupportClass_ofBoundary c₀.source c₀.target c₀.datum
    _ = compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass :=
      supportedExternalProductTriple_compactSupportClass a b ρ U hU haU hzero L hL hone
        τ V hV hbV hbzero M hM hbone

end AtiyahSinger.ComplexBundle
