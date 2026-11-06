/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Algebra.ReciprocalTensorSymbol
public import AtiyahSinger.Topology.BundleTensor
public import AtiyahSinger.Topology.BundleTensorKZero
public import AtiyahSinger.Topology.CompactSupportProduct
public import AtiyahSinger.Topology.RelativeKZeroProduct
public import AtiyahSinger.Topology.SupportKZeroComparison
public import AtiyahSinger.Topology.SupportTensorAction
public import AtiyahSinger.Topology.SupportTripleCutoff

/-!
# The actual external product of two compact-support triples

Public module ID: M2193.

Both original triples are extended by their supplied reciprocal cutoffs. Their
graded tensor block acts on the original pullback, tensor and sum bundles over
X times Y. The inverse uses the sum of the two squared cutoffs. Its possible
singular locus is contained in the product of the supplied enlarged controls,
which is the exact compact control chosen below. No cutoff is chosen internally.

Sources: KA II.5.21--II.5.22 and SG Appendix C.1 for the graded tensor product.
The typed target order is (E1 tensor F0) plus (E0 tensor F1), with lower-left
block identity tensor the second forward map. This follows KA's graded rule;
the printed target order and lower-left block in II.5.22 need that correction.
Reciprocal cutoffs and their explicit inverse are project supplements to its
adjoint presentation.

Given the cutoffs, Hausdorffness and local finite rank suffice for continuity.
Local compactness enters only the comparison with the existing compact-support
K model. Pullback along the two projections is used only for bundles and maps;
neither projection is asserted proper. The geometric symbol and its prescribed
inverse and the compact-support K-class comparison are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [CompactSpace X] [T2Space X] [CompactSpace Y] [T2Space Y]

/-- Relative forgetting is injective for the product of two specified retract pairs.
This split-pair consequence of KA II.3.23 is used to compare classes on the product
of two clutching doubles. The product union need not itself be a retract. -/
theorem relativeKZeroForget_injective_of_product_retractions
    (A : Set X) (hA : IsClosed A) (B : Set Y) (hB : IsClosed B)
    (rA : C(X, A)) (hrA : ∀ a : A, rA a = a)
    (rB : C(Y, B)) (hrB : ∀ b : B, rB b = b) :
    Function.Injective
      (relativeKZeroForget.{_, 0} (relativeProductSubset A B)
        (isClosed_relativeProductSubset A hA B hB)) := by
  classical
  let T := X × Y
  let W := relativeProductSubset A B
  have hW : IsClosed W := isClosed_relativeProductSubset A hA B hB
  let := hW.isClosedEmbedding_subtypeVal.compactSpace
  -- Extend the actual preceding K-minus-one class, rather than retracting the union.
  have restrictionSurjective :
      Function.Surjective (ComplexBundle.bundleKMinusOneRestriction W) := by
    intro a
    obtain ⟨α, hα⟩ := ComplexBundle.bundleAutomorphism_kMinusOneClass_surjective a
    obtain ⟨n, β, hβ⟩ := α.exists_trivial_representative
    let := ComplexBundle.trivialTopology (X := T) n
    let := ComplexBundle.trivialTopology (X := W) n
    -- These maps have images in the two product pieces and their intersection.
    let r₁ : C(T, W) :=
      ⟨fun z ↦ ⟨(z.1, (rB z.2).val), Or.inr (rB z.2).property⟩,
        (continuous_fst.prodMk
          (continuous_subtype_val.comp (rB.continuous.comp continuous_snd))).subtype_mk _⟩
    let r₂ : C(T, W) :=
      ⟨fun z ↦ ⟨((rA z.1).val, z.2), Or.inl (rA z.1).property⟩,
        ((continuous_subtype_val.comp (rA.continuous.comp continuous_fst)).prodMk
          continuous_snd).subtype_mk _⟩
    let r₀ : C(T, W) :=
      ⟨fun z ↦ ⟨((rA z.1).val, (rB z.2).val), Or.inl (rA z.1).property⟩,
        ((continuous_subtype_val.comp (rA.continuous.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp (rB.continuous.comp continuous_snd))).subtype_mk _⟩
    let lift (f : C(T, W)) :
        ComplexBundle.Iso (ComplexBundle.FiniteBundle.trivial T n).Fiber
          (ComplexBundle.FiniteBundle.trivial T n).Fiber :=
      (((ComplexBundle.pullbackTrivialIso f n).symm.trans (β.pullback f)).trans
        (ComplexBundle.pullbackTrivialIso f n))
    have htrivial (f : C(T, W)) (x : T) (v : Fin n → ℂ) :
        ((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).symm v = v := by
      apply ((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).injective
      rw [LinearEquiv.apply_symm_apply, ComplexBundle.pullbackTrivialIso_apply]
    have hlift (f : C(T, W)) (x : T) : (lift f).linearEquiv x = β.linearEquiv (f x) := by
      apply LinearEquiv.ext
      intro v
      change (ComplexBundle.pullbackTrivialIso f n).linearEquiv x
        (β.linearEquiv (f x) (((ComplexBundle.pullbackTrivialIso f n).linearEquiv x).symm v)) = _
      rw [ComplexBundle.pullbackTrivialIso_apply, htrivial]
    -- The overlap correction cancels on either piece, without commuting the matrices.
    let γ := ((lift r₂).trans (lift r₀).symm).trans (lift r₁)
    have hγ (w : W) (v : Fin n → ℂ) : γ.linearEquiv w.val v = β.linearEquiv w v := by
      change (lift r₁).linearEquiv w.val
        (((lift r₀).linearEquiv w.val).symm ((lift r₂).linearEquiv w.val v)) = _
      rw [hlift, hlift, hlift]
      rcases w.property with hw | hw
      · have hx : (rA w.val.1).val = w.val.1 :=
          congrArg Subtype.val (hrA ⟨w.val.1, hw⟩)
        have h₁ : r₁ w.val = r₀ w.val := Subtype.ext (Prod.ext hx.symm rfl)
        have h₂ : r₂ w.val = w := Subtype.ext (Prod.ext hx rfl)
        rw [h₁, h₂, LinearEquiv.apply_symm_apply]
      · have hy : (rB w.val.2).val = w.val.2 :=
          congrArg Subtype.val (hrB ⟨w.val.2, hw⟩)
        have h₂ : r₂ w.val = r₀ w.val := Subtype.ext (Prod.ext rfl hy.symm)
        have h₁ : r₁ w.val = w := Subtype.ext (Prod.ext rfl hy)
        rw [h₁, h₂, LinearEquiv.symm_apply_apply]
    let Γ : ComplexBundle.BundleAutomorphism T :=
      ⟨ComplexBundle.FiniteBundle.trivial T n, γ⟩
    let j : C(W, T) := ⟨Subtype.val, continuous_subtype_val⟩
    have hIso : (Γ.pullback j).IsIsomorphic ⟨ComplexBundle.FiniteBundle.trivial W n, β⟩ := by
      refine ⟨ComplexBundle.pullbackTrivialIso j n, ?_⟩
      intro w v
      change Fin n → ℂ at v
      change (ComplexBundle.pullbackTrivialIso j n).linearEquiv w (γ.linearEquiv w.val v) =
        β.linearEquiv w ((ComplexBundle.pullbackTrivialIso j n).linearEquiv w v)
      rw [ComplexBundle.pullbackTrivialIso_apply, ComplexBundle.pullbackTrivialIso_apply, hγ]
    refine ⟨Γ.kMinusOneClass, ?_⟩
    change ComplexBundle.bundleKMinusOnePullback j Γ.kMinusOneClass = a
    rw [ComplexBundle.bundleKMinusOnePullback_class]
    exact (ComplexBundle.BundleAutomorphism.kMinusOneClass_eq_of_isIsomorphic _ _ hIso).trans
      (hβ.trans hα)
  -- Exactness kills every element of the original forgetful kernel.
  let F : RelativeKZero.{_, 0} W hW →+ ComplexKZero T := relativeKZeroForget W hW
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  change F z = 0 at hz
  have hexact : (ComplexBundle.bundleKMinusOneBoundary W hW).range = F.ker :=
    ComplexBundle.range_bundleKMinusOneBoundary W hW
  obtain ⟨v, hv⟩ := hexact.ge hz
  obtain ⟨w, hw⟩ := restrictionSurjective v
  have hzero : ComplexBundle.bundleKMinusOneBoundary W hW v = 0 :=
    (ComplexBundle.range_bundleKMinusOneRestriction W hW).le ⟨w, hw⟩
  exact hv.symm.trans hzero

end AtiyahSinger

namespace AtiyahSinger.ComplexBundle

open Bundle
open scoped TensorProduct unitInterval

attribute [local instance] sumTopology isFiniteRank_sum tensorTopology isFiniteRank_tensor
  isFiniteRank_pullback

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The even tensor bundle on the original product base, with its original induced topologies. -/
@[reducible]
def SupportBundleTriple.externalProductSource (a : SupportBundleTriple X)
    (b : SupportBundleTriple Y) : FiniteBundle (X × Y) :=
  ((a.source.pullback ContinuousMap.fst).tensor (b.source.pullback ContinuousMap.snd)).sum
    ((a.target.pullback ContinuousMap.fst).tensor (b.target.pullback ContinuousMap.snd))

/-- The odd tensor bundle, ordered as E1 tensor F0 followed by E0 tensor F1. -/
@[reducible]
def SupportBundleTriple.externalProductTarget (a : SupportBundleTriple X)
    (b : SupportBundleTriple Y) : FiniteBundle (X × Y) :=
  ((a.target.pullback ContinuousMap.fst).tensor (b.source.pullback ContinuousMap.snd)).sum
    ((a.source.pullback ContinuousMap.fst).tensor (b.target.pullback ContinuousMap.snd))

variable [T2Space X] [T2Space Y]
  (a : SupportBundleTriple X) (b : SupportBundleTriple Y)
  (ρ : C(X, I)) (U : Set X) (hU : IsOpen U) (hcontrol : a.datum.control ⊆ U)
  (hzero : ∀ x ∈ U, ρ x = 0) (L : Set X) (hL : IsCompact L)
  (hone : ∀ x ∉ L, ρ x = 1)
  (τ : C(Y, I)) (V : Set Y) (hV : IsOpen V) (hbcontrol : b.datum.control ⊆ V)
  (hbzero : ∀ y ∈ V, τ y = 0) (M : Set Y) (hM : IsCompact M)
  (hbone : ∀ y ∉ M, τ y = 1)

local notation "Source" => FiniteBundle.Fiber (SupportBundleTriple.externalProductSource a b)
local notation "Target" => FiniteBundle.Fiber (SupportBundleTriple.externalProductTarget a b)
local notation "Control" => Set.prod L M
local notation "d" => a.datum.cutoffLinearMap ρ
local notation "d'" => a.datum.inverse.cutoffLinearMap ρ
local notation "e" => b.datum.cutoffLinearMap τ
local notation "e'" => b.datum.inverse.cutoffLinearMap τ

set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in
include hU hcontrol hzero hL hone hV hbcontrol hbzero hM hbone in
/-- The exact tensor block and its reciprocal inverse are continuous off the product control. -/
theorem supportedExternalProduct_symbol_properties :
    (∀ z : (Controlᶜ : Set (X × Y)),
      (((ρ z.val.1 : ℝ) : ℂ) ^ 2 + ((τ z.val.2 : ℝ) : ℂ) ^ 2) ≠ 0) ∧
    Continuous (fun z : TotalSpace Unit (Restrict Source Controlᶜ) ↦
      (⟨z.proj, reciprocalTensorSymbol (d z.proj.val.1) (d' z.proj.val.1)
        (e z.proj.val.2) (e' z.proj.val.2) z.snd⟩ :
          TotalSpace Unit (Restrict Target Controlᶜ))) ∧
    Continuous (fun z : TotalSpace Unit (Restrict Target Controlᶜ) ↦
      (⟨z.proj, reciprocalTensorSymbolInverse (d z.proj.val.1) (d' z.proj.val.1)
        (e z.proj.val.2) (e' z.proj.val.2)
        (((ρ z.proj.val.1 : ℝ) : ℂ) ^ 2) (((τ z.proj.val.2 : ℝ) : ℂ) ^ 2) z.snd⟩ :
          TotalSpace Unit (Restrict Source Controlᶜ))) := by
  /- Stage 1: outside L times M, either x is outside L or y is outside M.
  The corresponding supplied cutoff equals one. Both real squared cutoffs
  are nonnegative, so their sum is strictly positive and its complex cast
  is nonzero. The control must be the enlarged L times M: the cutoffs can
  vanish at points outside the original two controls.
  Stage 2: the four original cutoffHom maps are continuous, using their
  supplied open zero neighborhoods and the original Hausdorff bases. Pull
  these bundle maps back along the actual product projections. Tensor and
  sum charts make each displayed block continuous in the specified original
  product-bundle topologies, and restriction retains those same maps.
  Stage 3: the reciprocal identities make this forward block bijective on
  the exact exterior. Finite-rank bundle inversion gives a continuous inverse;
  its uniqueness identifies it with the displayed reciprocal reverse block.
  Thus continuity holds for the specified inverse itself. No global metric,
  compactification extension or properness of a projection is used. -/
  -- Outside the specified product control one of the original cutoffs equals one.
  have hnonzero (z : (Controlᶜ : Set (X × Y))) :
      (((ρ z.val.1 : ℝ) : ℂ) ^ 2 + ((τ z.val.2 : ℝ) : ℂ) ^ 2) ≠ 0 := by
    have hout : z.val.1 ∉ L ∨ z.val.2 ∉ M := not_and_or.mp z.property
    have hpositive : 0 < (ρ z.val.1 : ℝ) ^ 2 + (τ z.val.2 : ℝ) ^ 2 := by
      rcases hout with hx | hy
      · rw [hone z.val.1 hx]
        norm_num only [Set.Icc.coe_one, one_pow]
        positivity
      · rw [hbone z.val.2 hy]
        norm_num only [Set.Icc.coe_one, one_pow]
        positivity
    exact_mod_cast (ne_of_gt hpositive)
  -- A signed row is a sum of the actual continuous bundle maps in finite charts.
  let row (S T : FiniteBundle (X × Y)) (f g : Hom S.Fiber T.Fiber) (c : ℂ) :
      Hom S.Fiber T.Fiber :=
    { linearMap z := f.linearMap z + c • g.linearMap z
      continuous_total := by
        let p : C(TotalSpace Unit S.Fiber, X × Y) :=
          ⟨fun z ↦ z.proj, continuous_proj (E := S.Fiber)⟩
        let := isFiniteRank_pullback (E := T.Fiber) p
        have hf : Continuous (fun z : TotalSpace Unit S.Fiber ↦
            (⟨z, f.linearMap z.proj z.snd⟩ :
              TotalSpace Unit ((p : TotalSpace Unit S.Fiber → X × Y) *ᵖ T.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
          exact continuous_id.prodMk f.continuous_total
        have hg : Continuous (fun z : TotalSpace Unit S.Fiber ↦
            (⟨z, g.linearMap z.proj z.snd⟩ :
              TotalSpace Unit ((p : TotalSpace Unit S.Fiber → X × Y) *ᵖ T.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
          exact continuous_id.prodMk g.continuous_total
        exact (Pullback.continuous_lift Unit T.Fiber p).comp
          (continuous_add_section ((p : TotalSpace Unit S.Fiber → X × Y) *ᵖ T.Fiber)
            _ _ hf (continuous_smul_section _ (ContinuousMap.const _ c) _ hg)) }
  let D := (a.datum.cutoffHom ρ U hU hcontrol hzero).pullback
    (ContinuousMap.fst : C(X × Y, X))
  let D' := (a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).pullback
    (ContinuousMap.fst : C(X × Y, X))
  let E := (b.datum.cutoffHom τ V hV hbcontrol hbzero).pullback
    (ContinuousMap.snd : C(X × Y, Y))
  let E' := (b.datum.inverse.cutoffHom τ V hV hbcontrol hbzero).pullback
    (ContinuousMap.snd : C(X × Y, Y))
  let upper := row (a.externalProductSource b)
    ((a.target.pullback ContinuousMap.fst).tensor (b.source.pullback ContinuousMap.snd))
    ((D.tensor (Hom.id _)).comp sumFst) (((Hom.id _).tensor E').comp sumSnd) (-1)
  let lower := row (a.externalProductSource b)
    ((a.source.pullback ContinuousMap.fst).tensor (b.target.pullback ContinuousMap.snd))
    (((Hom.id _).tensor E).comp sumFst) ((D'.tensor (Hom.id _)).comp sumSnd) 1
  let forward : Hom Source Target :=
    { linearMap z := reciprocalTensorSymbol (d z.1) (d' z.1) (e z.2) (e' z.2)
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply (upper.continuous_total.prodMk lower.continuous_total).congr
        intro z
        apply Prod.ext <;> apply congrArg (TotalSpace.mk z.proj) <;>
          simp only [upper, lower, row, Hom.comp, Hom.tensor, Hom.id, Hom.pullback,
          CompactSupportTriple.cutoffHom, D, D', E, E', sumFst, sumSnd,
          reciprocalTensorSymbol, LinearMap.prod_apply, LinearMap.coprod_apply,
          LinearMap.comp_apply, LinearMap.add_apply,
          LinearMap.neg_apply, LinearMap.fst_apply, LinearMap.snd_apply,
          Function.prod, neg_one_smul, one_smul]
        all_goals rfl }
  -- Restriction retains this forward map and its original finite bundle topology.
  let restricted := forward.pullback
    (⟨Subtype.val, continuous_subtype_val⟩ : C((Controlᶜ : Set (X × Y)), X × Y))
  let fiberEquiv (z : (Controlᶜ : Set (X × Y))) :=
    reciprocalTensorSymbolEquiv (d z.val.1) (d' z.val.1) (e z.val.2) (e' z.val.2)
      (((ρ z.val.1 : ℝ) : ℂ) ^ 2) (((τ z.val.2 : ℝ) : ℂ) ^ 2)
      (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.1).1
      (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.1).2
      (b.datum.cutoffHom_inverse_comp τ V hV hbcontrol hbzero z.val.2).1
      (b.datum.cutoffHom_inverse_comp τ V hV hbcontrol hbzero z.val.2).2 (hnonzero z)
  have hbijective (z : (Controlᶜ : Set (X × Y))) :
      Function.Bijective (restricted.linearMap z) := (fiberEquiv z).bijective
  refine ⟨hnonzero, restricted.continuous_total, ?_⟩
  -- Finite-rank inversion is continuous; uniqueness identifies the prescribed inverse formula.
  apply (restricted.continuous_inverse hbijective).congr
  intro z
  apply congrArg (TotalSpace.mk z.proj)
  apply (fiberEquiv z.proj).injective
  exact (LinearEquiv.apply_symm_apply
    (LinearEquiv.ofBijective (restricted.linearMap z.proj) (hbijective z.proj)) z.snd).trans
      ((fiberEquiv z.proj).apply_symm_apply z.snd).symm

/-- The actual boundary block with the supplied reciprocal cutoffs and its explicit inverse. -/
def supportedExternalProductBoundary : RelativeTriple Source Target Controlᶜ where
  linearEquiv z := reciprocalTensorSymbolEquiv (d z.val.1) (d' z.val.1)
    (e z.val.2) (e' z.val.2) (((ρ z.val.1 : ℝ) : ℂ) ^ 2)
    (((τ z.val.2 : ℝ) : ℂ) ^ 2)
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.1).1
    (a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero z.val.1).2
    (b.datum.cutoffHom_inverse_comp τ V hV hbcontrol hbzero z.val.2).1
    (b.datum.cutoffHom_inverse_comp τ V hV hbcontrol hbzero z.val.2).2
    ((supportedExternalProduct_symbol_properties a b ρ U hU hcontrol hzero L hL hone
      τ V hV hbcontrol hbzero M hM hbone).1 z)
  continuous_total :=
    (supportedExternalProduct_symbol_properties a b ρ U hU hcontrol hzero L hL hone
      τ V hV hbcontrol hbzero M hM hbone).2.1
  continuous_symm :=
    (supportedExternalProduct_symbol_properties a b ρ U hU hcontrol hzero L hL hone
      τ V hV hbcontrol hbzero M hM hbone).2.2

/-- The product uses the original tensor bundles and exactly the enlarged product control. -/
@[reducible]
def supportedExternalProductTriple : SupportBundleTriple (X × Y) :=
  SupportBundleTriple.ofBoundary (a.externalProductSource b) (a.externalProductTarget b)
    { control := Control
      isCompact_control := hL.prod hM
      boundary := supportedExternalProductBoundary a b ρ U hU hcontrol hzero L hL hone
        τ V hV hbcontrol hbzero M hM hbone }


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 3600000 in

open Topology in
/-- The actual positive-convention triple represents the existing compact-support product. -/
theorem supportedExternalProductTriple_compactSupportClass
    [LocallyCompactSpace X] [LocallyCompactSpace Y] :
    (supportedExternalProductTriple a b ρ U hU hcontrol hzero L hL hone
      τ V hV hbcontrol hbzero M hM hbone).compactSupportClass =
        compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
  /- Stage 1: choose compact windows around the supplied controls, retaining
  the given reciprocal cutoffs and boundary maps. On each clutching
  double, glue those maps on the left to identity maps on the right.
  The gluing seam agrees because the cutoffs equal one there. Both
  reciprocal compositions have the specified scalar coefficient.
  Stage 2: form the positive reciprocal tensor block on the product of
  these doubles. Its even-minus-odd bundle difference is the product of
  the two original differences. Relative forgetting is injective for
  this product of the two right retract pairs, so the same equality
  holds for the actual relative classes.
  Stage 3: pull back through the left-left chart. Its inverse-image
  relative subset is exactly the union of the two window boundaries.
  The original tensor and sum charts identify every reciprocal block
  with the given product-window boundary, including its signs.
  Stage 4: pass through the complement homeomorphisms and extend openly.
  Relative-product and open-extension naturality identify this class
  with compactSupportKZeroExternalProduct. No Hermitian metric or
  properness of either product projection is used. -/

  classical
  let (E F : X → Type) [TopologicalSpace (TotalSpace Unit E)]
      [TopologicalSpace (TotalSpace Unit F)] :
      TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) := sumTopology
  -- A local construction is instantiated separately for the two original universes.
  have doubleMapsX {Z : Type _} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (c : BundleTriple A)
      (δ : Hom c.source.Fiber c.target.Fiber) (δi : Hom c.target.Fiber c.source.Fiber)
      (s : Z → ℝ) (hs : ∀ x : Z, 0 ≤ s x)
      (hcomposition : ∀ x : Z,
        (δi.linearMap x).comp (δ.linearMap x) =
          (s x : ℂ) • (LinearMap.id : c.source.Fiber x →ₗ[ℂ] c.source.Fiber x) ∧
        (δ.linearMap x).comp (δi.linearMap x) =
          (s x : ℂ) • (LinearMap.id : c.target.Fiber x →ₗ[ℂ] c.target.Fiber x))
      (hboundary : ∀ x : A, δ.linearMap x = (c.boundary.linearEquiv x).toLinearMap)
      (hboundaryi : ∀ x : A, δi.linearMap x = (c.boundary.linearEquiv x).symm.toLinearMap)
      (hboundarys : ∀ x : A, s x = 1) :
      letI := DoubleSpace.t2Space A hA
      let C := clutchingBundle hA c
      let P := c.target.pullback (DoubleSpace.projMap A)
      ∃ Δ : Hom C.Fiber P.Fiber, ∃ Δi : Hom P.Fiber C.Fiber,
      ∃ r : DoubleSpace A → ℝ,
        (∀ z, 0 ≤ r z) ∧ (∀ x : Z, r (DoubleSpace.right A x) = 1) ∧
        (∀ z, (Δi.linearMap z).comp (Δ.linearMap z) =
          (r z : ℂ) • (LinearMap.id : C.Fiber z →ₗ[ℂ] C.Fiber z) ∧
          (Δ.linearMap z).comp (Δi.linearMap z) =
          (r z : ℂ) • (LinearMap.id : P.Fiber z →ₗ[ℂ] P.Fiber z)) ∧
        (∀ x v, Δ.linearMap (DoubleSpace.left A x) v =
          δ.linearMap x ((clutchingLeftIso hA c).linearEquiv x v)) ∧
        (∀ x v, Δi.linearMap (DoubleSpace.left A x) v =
          ((clutchingLeftIso hA c).linearEquiv x).symm (δi.linearMap x v)) := by
    let := DoubleSpace.t2Space A hA
    -- Glue actual linear maps across the two closed sides of one clutching double.
    have glueHom
        (A : Set Z) (hA : IsClosed A) (E F : FiniteBundle (DoubleSpace A))
        (l : Hom (E.pullback (DoubleSpace.leftMap A)).Fiber
          (F.pullback (DoubleSpace.leftMap A)).Fiber)
        (r : Hom (E.pullback (DoubleSpace.rightMap A)).Fiber
          (F.pullback (DoubleSpace.rightMap A)).Fiber)
        (hseam : ∀ x : A, HEq (l.linearMap x.val) (r.linearMap x.val)) :
        ∃ δ : Hom E.Fiber F.Fiber,
          (∀ x : Z, δ.linearMap (DoubleSpace.left A x) = l.linearMap x) ∧
          (∀ x : Z, δ.linearMap (DoubleSpace.right A x) = r.linearMap x) := by
      let := DoubleSpace.t2Space A hA
      let move {z w : DoubleSpace A} (h : z = w)
          (f : E.Fiber z →ₗ[ℂ] F.Fiber z) : E.Fiber w →ₗ[ℂ] F.Fiber w := h ▸ f
      have hmove {z w : DoubleSpace A} (h : z = w)
          (f : E.Fiber z →ₗ[ℂ] F.Fiber z) : HEq (move h f) f := by
        cases h
        rfl
      have hright (z : DoubleSpace A) (h : DoubleSpace.left A (DoubleSpace.proj A z) ≠ z) :
          DoubleSpace.right A (DoubleSpace.proj A z) = z := by
        induction z using Quotient.inductionOn with
        | h s =>
          cases s with
          | inl x => exact (h rfl).elim
          | inr x => rfl
      let f (z : DoubleSpace A) : E.Fiber z →ₗ[ℂ] F.Fiber z :=
        if h : DoubleSpace.left A (DoubleSpace.proj A z) = z then
          move h (l.linearMap (DoubleSpace.proj A z))
        else move (hright z h) (r.linearMap (DoubleSpace.proj A z))
      have hfL (x : Z) : f (DoubleSpace.left A x) = l.linearMap x := by
        simp only [f, DoubleSpace.proj_left]
        rfl
      have hfR (x : Z) : f (DoubleSpace.right A x) = r.linearMap x := by
        dsimp only [f, DoubleSpace.proj_right]
        split_ifs with h
        · have hx : x ∈ A := ((DoubleSpace.left_eq_right_iff A x x).mp h).2
          exact eq_of_heq ((hmove h (l.linearMap x)).trans (hseam ⟨x, hx⟩))
        · rfl
      -- The two closed total-space inclusions cover every original fiber vector.
      have hlift (K : FiniteBundle (DoubleSpace A)) (g : C(Z, DoubleSpace A))
          (hg : IsClosedEmbedding g) :
          IsClosedEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) g) := by
        let j : TotalSpace Unit ((g : Z → DoubleSpace A) *ᵖ K.Fiber) →
            Z × TotalSpace Unit K.Fiber := pullbackTotalSpaceEmbedding g
        have hj : IsEmbedding j := by
          refine ⟨inducing_pullbackTotalSpaceEmbedding Unit K.Fiber g, ?_⟩
          rintro ⟨x, v⟩ ⟨y, w⟩ h
          have hxy : x = y := congrArg Prod.fst h
          subst y
          have hvw : v = w := TotalSpace.mk_injective (g x) (congrArg Prod.snd h)
          subst w
          rfl
        let graph : TotalSpace Unit K.Fiber → DoubleSpace A × TotalSpace Unit K.Fiber :=
          fun z ↦ (z.proj, z)
        have hgraph : Continuous graph := (continuous_proj (E := K.Fiber)).prodMk continuous_id
        have hcomp : IsEmbedding (graph ∘ Pullback.lift (F := Unit) (E := K.Fiber) g) :=
          (hg.isEmbedding.prodMap IsEmbedding.id).comp hj
        have hemb : IsEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) g) :=
          IsEmbedding.of_comp (Pullback.continuous_lift Unit K.Fiber g) hgraph hcomp
        have hrange : Set.range (Pullback.lift (F := Unit) (E := K.Fiber) g) =
            (π Unit K.Fiber) ⁻¹' Set.range g := by
          ext ⟨y, v⟩
          constructor
          · rintro ⟨⟨x, w⟩, h⟩
            exact ⟨x, congrArg (π Unit K.Fiber) h⟩
          · rintro ⟨x, h⟩
            change g x = y at h
            subst y
            exact ⟨⟨x, v⟩, rfl⟩
        exact ⟨hemb, hrange ▸ hg.isClosed_range.preimage (continuous_proj (E := K.Fiber))⟩
      let left := Pullback.lift (F := Unit) (E := E.Fiber) (DoubleSpace.leftMap A)
      let right := Pullback.lift (F := Unit) (E := E.Fiber) (DoubleSpace.rightMap A)
      have hl := hlift E (DoubleSpace.leftMap A) (DoubleSpace.isClosedEmbedding_left A hA)
      have hr := hlift E (DoubleSpace.rightMap A) (DoubleSpace.isClosedEmbedding_right A hA)
      let total (z : TotalSpace Unit E.Fiber) : TotalSpace Unit F.Fiber :=
        ⟨z.proj, f z.proj z.snd⟩
      have hL : ContinuousOn total (Set.range left) := by
        erw [← Set.image_univ]
        apply hl.isEmbedding.isInducing.continuousOn_image_iff.mpr
        have hc := (Pullback.continuous_lift Unit F.Fiber
          (DoubleSpace.leftMap A)).comp l.continuous_total
        convert hc.continuousOn using 1
        funext z
        change (⟨DoubleSpace.left A z.proj, f (DoubleSpace.left A z.proj) z.snd⟩ :
          TotalSpace Unit F.Fiber) = ⟨_, l.linearMap z.proj z.snd⟩
        erw [hfL]
        rfl
      have hR : ContinuousOn total (Set.range right) := by
        erw [← Set.image_univ]
        apply hr.isEmbedding.isInducing.continuousOn_image_iff.mpr
        have hc := (Pullback.continuous_lift Unit F.Fiber
          (DoubleSpace.rightMap A)).comp r.continuous_total
        convert hc.continuousOn using 1
        funext z
        change (⟨DoubleSpace.right A z.proj, f (DoubleSpace.right A z.proj) z.snd⟩ :
          TotalSpace Unit F.Fiber) = ⟨_, r.linearMap z.proj z.snd⟩
        erw [hfR]
        rfl
      have hcover : Set.range left ∪ Set.range right = Set.univ := by
        apply Set.eq_univ_of_forall
        rintro ⟨z, v⟩
        induction z using Quotient.inductionOn with
        | h s =>
          cases s with
          | inl x => exact Or.inl ⟨⟨x, v⟩, rfl⟩
          | inr x => exact Or.inr ⟨⟨x, v⟩, rfl⟩
      have hc : Continuous total := by
        erw [← continuousOn_univ, ← hcover]
        exact hL.union_of_isClosed hR hl.isClosed_range hr.isClosed_range
      exact ⟨⟨f, hc⟩, hfL, hfR⟩
    let C := clutchingBundle hA c
    let P := c.target.pullback (DoubleSpace.projMap A)
    let el := clutchingLeftIso hA c
    let er := clutchingRightIso hA c
    let pl : Iso (P.pullback (DoubleSpace.leftMap A)).Fiber c.target.Fiber :=
      (pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.leftMap A)).trans (pullbackIdIso (E := c.target.Fiber))
    let pr : Iso (P.pullback (DoubleSpace.rightMap A)).Fiber c.target.Fiber :=
      (pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.rightMap A)).trans (pullbackIdIso (E := c.target.Fiber))
    have hpl (x : Z) (v : P.Fiber (DoubleSpace.left A x)) :
        pl.linearEquiv x v = v := by
      change (pullbackIdIso (E := c.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
          (DoubleSpace.leftMap A)).linearEquiv x v) = v
      erw [pullbackCompIso_apply, pullbackIdIso_apply]
    have hpr (x : Z) (v : P.Fiber (DoubleSpace.right A x)) :
        pr.linearEquiv x v = v := by
      change (pullbackIdIso (E := c.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
          (DoubleSpace.rightMap A)).linearEquiv x v) = v
      erw [pullbackCompIso_apply, pullbackIdIso_apply]
    have hpli (x : Z) (v : c.target.Fiber x) :
        (pl.linearEquiv x).symm v = v := by
      apply (pl.linearEquiv x).injective
      erw [LinearEquiv.apply_symm_apply, hpl]
    have hpri (x : Z) (v : c.target.Fiber x) :
        (pr.linearEquiv x).symm v = v := by
      apply (pr.linearEquiv x).injective
      erw [LinearEquiv.apply_symm_apply, hpr]
    let ll := pl.symm.toHom.comp (δ.comp el.toHom)
    let rr := pr.symm.toHom.comp er.toHom
    let lli := el.symm.toHom.comp (δi.comp pl.toHom)
    let rri := er.symm.toHom.comp pr.toHom
    have hll (x : Z) (v : C.Fiber (DoubleSpace.left A x)) :
        ll.linearMap x v = δ.linearMap x (el.linearEquiv x v) := by
      exact hpli x _
    have hrr (x : Z) (v : C.Fiber (DoubleSpace.right A x)) :
        rr.linearMap x v = er.linearEquiv x v := by
      exact hpri x _
    have hlli (x : Z) (v : P.Fiber (DoubleSpace.left A x)) :
        lli.linearMap x v = (el.linearEquiv x).symm (δi.linearMap x v) := by
      change (el.linearEquiv x).symm (δi.linearMap x (pl.linearEquiv x v)) = _
      erw [hpl]
    have hrri (x : Z) (v : P.Fiber (DoubleSpace.right A x)) :
        rri.linearMap x v = (er.linearEquiv x).symm v := by
      change (er.linearEquiv x).symm (pr.linearEquiv x v) = _
      erw [hpr]
    have hcastP (x : A) (v : c.target.Fiber x) :
        cast (congrArg P.Fiber (DoubleSpace.left_eq_right A x)) v = v := by
      have hp : congrArg P.Fiber (DoubleSpace.left_eq_right A x) = rfl :=
        Subsingleton.elim _ _
      exact congrArg (fun h : c.target.Fiber x = c.target.Fiber x ↦ cast h v) hp
    have transport {z w : DoubleSpace A} (h : z = w)
        (f : C.Fiber z →ₗ[ℂ] P.Fiber z) (g : C.Fiber w →ₗ[ℂ] P.Fiber w)
        (hf : ∀ v, cast (congrArg P.Fiber h) (f v) =
          g (cast (congrArg C.Fiber h) v)) : HEq f g := by
      cases h
      exact heq_of_eq (LinearMap.ext hf)
    have transporti {z w : DoubleSpace A} (h : z = w)
        (f : P.Fiber z →ₗ[ℂ] C.Fiber z) (g : P.Fiber w →ₗ[ℂ] C.Fiber w)
        (hf : ∀ v, cast (congrArg C.Fiber h) (f v) =
          g (cast (congrArg P.Fiber h) v)) : HEq f g := by
      cases h
      exact heq_of_eq (LinearMap.ext hf)
    have hseam : ∀ x : A, HEq (ll.linearMap x.val) (rr.linearMap x.val) := by
      intro x
      apply transport (DoubleSpace.left_eq_right A x)
      intro v
      erw [hll, hcastP, hrr, hboundary x]
      change c.boundary.linearEquiv x (el.linearEquiv x v) =
        er.linearEquiv x (cast (congrArg C.Fiber (DoubleSpace.left_eq_right A x)) v)
      simpa only [el, er, LinearEquiv.symm_apply_apply] using
        (clutching_seam_apply hA c x (el.linearEquiv x v)).symm
    have hseami : ∀ x : A, HEq (lli.linearMap x.val) (rri.linearMap x.val) := by
      intro x
      apply transporti (DoubleSpace.left_eq_right A x)
      intro v
      erw [hlli, hcastP, hrri]
      apply (er.linearEquiv x).injective
      erw [clutching_seam_apply, LinearEquiv.apply_symm_apply, hboundaryi x]
      exact (c.boundary.linearEquiv x).apply_symm_apply v
    obtain ⟨Δ, hΔl, hΔr⟩ := glueHom A hA C P ll rr hseam
    obtain ⟨Δi, hΔil, hΔir⟩ := glueHom A hA P C lli rri hseami
    -- The same scalar is rho squared on the left and one on the right.
    let r (z : DoubleSpace A) : ℝ :=
      if DoubleSpace.left A (DoubleSpace.proj A z) = z then s (DoubleSpace.proj A z) else 1
    have hrl (x : Z) : r (DoubleSpace.left A x) = s x := by
      simp only [r, DoubleSpace.proj_left, ite_true]
    have hrright (x : Z) : r (DoubleSpace.right A x) = 1 := by
      dsimp only [r, DoubleSpace.proj_right]
      split_ifs with h
      · exact hboundarys ⟨x, ((DoubleSpace.left_eq_right_iff A x x).mp h).2⟩
      · rfl
    have hrpos (z : DoubleSpace A) : 0 ≤ r z := by
      dsimp only [r]
      split_ifs
      · exact hs _
      · norm_num
    refine ⟨Δ, Δi, r, hrpos, hrright, ?_, ?_, ?_⟩
    · intro z
      induction z using Quotient.inductionOn with
      | h z =>
        cases z with
        | inl x =>
          erw [hrl]
          constructor
          · apply LinearMap.ext
            intro v
            change Δi.linearMap (DoubleSpace.left A x)
              (Δ.linearMap (DoubleSpace.left A x) v) = (s x : ℂ) • v
            erw [hΔl, hΔil, hll, hlli]
            have h := congrArg (fun f ↦ f (el.linearEquiv x v)) (hcomposition x).1
            change δi.linearMap x (δ.linearMap x (el.linearEquiv x v)) =
              (s x : ℂ) • el.linearEquiv x v at h
            erw [h, map_smul, LinearEquiv.symm_apply_apply]
          · apply LinearMap.ext
            intro v
            change Δ.linearMap (DoubleSpace.left A x)
              (Δi.linearMap (DoubleSpace.left A x) v) = (s x : ℂ) • v
            erw [hΔl, hΔil, hlli, hll, LinearEquiv.apply_symm_apply]
            exact congrArg (fun f ↦ f v) (hcomposition x).2
        | inr x =>
          erw [hrright]
          constructor
          · apply LinearMap.ext
            intro v
            change Δi.linearMap (DoubleSpace.right A x)
              (Δ.linearMap (DoubleSpace.right A x) v) = (1 : ℂ) • v
            erw [hΔr, hΔir, hrr, hrri, LinearEquiv.symm_apply_apply, one_smul]
          · apply LinearMap.ext
            intro v
            change Δ.linearMap (DoubleSpace.right A x)
              (Δi.linearMap (DoubleSpace.right A x) v) = (1 : ℂ) • v
            erw [hΔr, hΔir, hrri, hrr, LinearEquiv.apply_symm_apply, one_smul]
    · intro x v
      erw [hΔl]
      exact hll x v
    · intro x v
      erw [hΔil]
      exact hlli x v
  have doubleMapsY {Z : Type _} [TopologicalSpace Z] [CompactSpace Z] [T2Space Z]
      (A : Set Z) (hA : IsClosed A) (c : BundleTriple A)
      (δ : Hom c.source.Fiber c.target.Fiber) (δi : Hom c.target.Fiber c.source.Fiber)
      (s : Z → ℝ) (hs : ∀ x : Z, 0 ≤ s x)
      (hcomposition : ∀ x : Z,
        (δi.linearMap x).comp (δ.linearMap x) =
          (s x : ℂ) • (LinearMap.id : c.source.Fiber x →ₗ[ℂ] c.source.Fiber x) ∧
        (δ.linearMap x).comp (δi.linearMap x) =
          (s x : ℂ) • (LinearMap.id : c.target.Fiber x →ₗ[ℂ] c.target.Fiber x))
      (hboundary : ∀ x : A, δ.linearMap x = (c.boundary.linearEquiv x).toLinearMap)
      (hboundaryi : ∀ x : A, δi.linearMap x = (c.boundary.linearEquiv x).symm.toLinearMap)
      (hboundarys : ∀ x : A, s x = 1) :
      letI := DoubleSpace.t2Space A hA
      let C := clutchingBundle hA c
      let P := c.target.pullback (DoubleSpace.projMap A)
      ∃ Δ : Hom C.Fiber P.Fiber, ∃ Δi : Hom P.Fiber C.Fiber,
      ∃ r : DoubleSpace A → ℝ,
        (∀ z, 0 ≤ r z) ∧ (∀ x : Z, r (DoubleSpace.right A x) = 1) ∧
        (∀ z, (Δi.linearMap z).comp (Δ.linearMap z) =
          (r z : ℂ) • (LinearMap.id : C.Fiber z →ₗ[ℂ] C.Fiber z) ∧
          (Δ.linearMap z).comp (Δi.linearMap z) =
          (r z : ℂ) • (LinearMap.id : P.Fiber z →ₗ[ℂ] P.Fiber z)) ∧
        (∀ x v, Δ.linearMap (DoubleSpace.left A x) v =
          δ.linearMap x ((clutchingLeftIso hA c).linearEquiv x v)) ∧
        (∀ x v, Δi.linearMap (DoubleSpace.left A x) v =
          ((clutchingLeftIso hA c).linearEquiv x).symm (δi.linearMap x v)) := by
    let := DoubleSpace.t2Space A hA
    -- Glue actual linear maps across the two closed sides of one clutching double.
    have glueHom
        (A : Set Z) (hA : IsClosed A) (E F : FiniteBundle (DoubleSpace A))
        (l : Hom (E.pullback (DoubleSpace.leftMap A)).Fiber
          (F.pullback (DoubleSpace.leftMap A)).Fiber)
        (r : Hom (E.pullback (DoubleSpace.rightMap A)).Fiber
          (F.pullback (DoubleSpace.rightMap A)).Fiber)
        (hseam : ∀ x : A, HEq (l.linearMap x.val) (r.linearMap x.val)) :
        ∃ δ : Hom E.Fiber F.Fiber,
          (∀ x : Z, δ.linearMap (DoubleSpace.left A x) = l.linearMap x) ∧
          (∀ x : Z, δ.linearMap (DoubleSpace.right A x) = r.linearMap x) := by
      let := DoubleSpace.t2Space A hA
      let move {z w : DoubleSpace A} (h : z = w)
          (f : E.Fiber z →ₗ[ℂ] F.Fiber z) : E.Fiber w →ₗ[ℂ] F.Fiber w := h ▸ f
      have hmove {z w : DoubleSpace A} (h : z = w)
          (f : E.Fiber z →ₗ[ℂ] F.Fiber z) : HEq (move h f) f := by
        cases h
        rfl
      have hright (z : DoubleSpace A) (h : DoubleSpace.left A (DoubleSpace.proj A z) ≠ z) :
          DoubleSpace.right A (DoubleSpace.proj A z) = z := by
        induction z using Quotient.inductionOn with
        | h s =>
          cases s with
          | inl x => exact (h rfl).elim
          | inr x => rfl
      let f (z : DoubleSpace A) : E.Fiber z →ₗ[ℂ] F.Fiber z :=
        if h : DoubleSpace.left A (DoubleSpace.proj A z) = z then
          move h (l.linearMap (DoubleSpace.proj A z))
        else move (hright z h) (r.linearMap (DoubleSpace.proj A z))
      have hfL (x : Z) : f (DoubleSpace.left A x) = l.linearMap x := by
        simp only [f, DoubleSpace.proj_left]
        rfl
      have hfR (x : Z) : f (DoubleSpace.right A x) = r.linearMap x := by
        dsimp only [f, DoubleSpace.proj_right]
        split_ifs with h
        · have hx : x ∈ A := ((DoubleSpace.left_eq_right_iff A x x).mp h).2
          exact eq_of_heq ((hmove h (l.linearMap x)).trans (hseam ⟨x, hx⟩))
        · rfl
      -- The two closed total-space inclusions cover every original fiber vector.
      have hlift (K : FiniteBundle (DoubleSpace A)) (g : C(Z, DoubleSpace A))
          (hg : IsClosedEmbedding g) :
          IsClosedEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) g) := by
        let j : TotalSpace Unit ((g : Z → DoubleSpace A) *ᵖ K.Fiber) →
            Z × TotalSpace Unit K.Fiber := pullbackTotalSpaceEmbedding g
        have hj : IsEmbedding j := by
          refine ⟨inducing_pullbackTotalSpaceEmbedding Unit K.Fiber g, ?_⟩
          rintro ⟨x, v⟩ ⟨y, w⟩ h
          have hxy : x = y := congrArg Prod.fst h
          subst y
          have hvw : v = w := TotalSpace.mk_injective (g x) (congrArg Prod.snd h)
          subst w
          rfl
        let graph : TotalSpace Unit K.Fiber → DoubleSpace A × TotalSpace Unit K.Fiber :=
          fun z ↦ (z.proj, z)
        have hgraph : Continuous graph := (continuous_proj (E := K.Fiber)).prodMk continuous_id
        have hcomp : IsEmbedding (graph ∘ Pullback.lift (F := Unit) (E := K.Fiber) g) :=
          (hg.isEmbedding.prodMap IsEmbedding.id).comp hj
        have hemb : IsEmbedding (Pullback.lift (F := Unit) (E := K.Fiber) g) :=
          IsEmbedding.of_comp (Pullback.continuous_lift Unit K.Fiber g) hgraph hcomp
        have hrange : Set.range (Pullback.lift (F := Unit) (E := K.Fiber) g) =
            (π Unit K.Fiber) ⁻¹' Set.range g := by
          ext ⟨y, v⟩
          constructor
          · rintro ⟨⟨x, w⟩, h⟩
            exact ⟨x, congrArg (π Unit K.Fiber) h⟩
          · rintro ⟨x, h⟩
            change g x = y at h
            subst y
            exact ⟨⟨x, v⟩, rfl⟩
        exact ⟨hemb, hrange ▸ hg.isClosed_range.preimage (continuous_proj (E := K.Fiber))⟩
      let left := Pullback.lift (F := Unit) (E := E.Fiber) (DoubleSpace.leftMap A)
      let right := Pullback.lift (F := Unit) (E := E.Fiber) (DoubleSpace.rightMap A)
      have hl := hlift E (DoubleSpace.leftMap A) (DoubleSpace.isClosedEmbedding_left A hA)
      have hr := hlift E (DoubleSpace.rightMap A) (DoubleSpace.isClosedEmbedding_right A hA)
      let total (z : TotalSpace Unit E.Fiber) : TotalSpace Unit F.Fiber :=
        ⟨z.proj, f z.proj z.snd⟩
      have hL : ContinuousOn total (Set.range left) := by
        erw [← Set.image_univ]
        apply hl.isEmbedding.isInducing.continuousOn_image_iff.mpr
        have hc := (Pullback.continuous_lift Unit F.Fiber
          (DoubleSpace.leftMap A)).comp l.continuous_total
        convert hc.continuousOn using 1
        funext z
        change (⟨DoubleSpace.left A z.proj, f (DoubleSpace.left A z.proj) z.snd⟩ :
          TotalSpace Unit F.Fiber) = ⟨_, l.linearMap z.proj z.snd⟩
        erw [hfL]
        rfl
      have hR : ContinuousOn total (Set.range right) := by
        erw [← Set.image_univ]
        apply hr.isEmbedding.isInducing.continuousOn_image_iff.mpr
        have hc := (Pullback.continuous_lift Unit F.Fiber
          (DoubleSpace.rightMap A)).comp r.continuous_total
        convert hc.continuousOn using 1
        funext z
        change (⟨DoubleSpace.right A z.proj, f (DoubleSpace.right A z.proj) z.snd⟩ :
          TotalSpace Unit F.Fiber) = ⟨_, r.linearMap z.proj z.snd⟩
        erw [hfR]
        rfl
      have hcover : Set.range left ∪ Set.range right = Set.univ := by
        apply Set.eq_univ_of_forall
        rintro ⟨z, v⟩
        induction z using Quotient.inductionOn with
        | h s =>
          cases s with
          | inl x => exact Or.inl ⟨⟨x, v⟩, rfl⟩
          | inr x => exact Or.inr ⟨⟨x, v⟩, rfl⟩
      have hc : Continuous total := by
        erw [← continuousOn_univ, ← hcover]
        exact hL.union_of_isClosed hR hl.isClosed_range hr.isClosed_range
      exact ⟨⟨f, hc⟩, hfL, hfR⟩
    let C := clutchingBundle hA c
    let P := c.target.pullback (DoubleSpace.projMap A)
    let el := clutchingLeftIso hA c
    let er := clutchingRightIso hA c
    let pl : Iso (P.pullback (DoubleSpace.leftMap A)).Fiber c.target.Fiber :=
      (pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.leftMap A)).trans (pullbackIdIso (E := c.target.Fiber))
    let pr : Iso (P.pullback (DoubleSpace.rightMap A)).Fiber c.target.Fiber :=
      (pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.rightMap A)).trans (pullbackIdIso (E := c.target.Fiber))
    have hpl (x : Z) (v : P.Fiber (DoubleSpace.left A x)) :
        pl.linearEquiv x v = v := by
      change (pullbackIdIso (E := c.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
          (DoubleSpace.leftMap A)).linearEquiv x v) = v
      erw [pullbackCompIso_apply, pullbackIdIso_apply]
    have hpr (x : Z) (v : P.Fiber (DoubleSpace.right A x)) :
        pr.linearEquiv x v = v := by
      change (pullbackIdIso (E := c.target.Fiber)).linearEquiv x
        ((pullbackCompIso (E := c.target.Fiber) (DoubleSpace.projMap A)
          (DoubleSpace.rightMap A)).linearEquiv x v) = v
      erw [pullbackCompIso_apply, pullbackIdIso_apply]
    have hpli (x : Z) (v : c.target.Fiber x) :
        (pl.linearEquiv x).symm v = v := by
      apply (pl.linearEquiv x).injective
      erw [LinearEquiv.apply_symm_apply, hpl]
    have hpri (x : Z) (v : c.target.Fiber x) :
        (pr.linearEquiv x).symm v = v := by
      apply (pr.linearEquiv x).injective
      erw [LinearEquiv.apply_symm_apply, hpr]
    let ll := pl.symm.toHom.comp (δ.comp el.toHom)
    let rr := pr.symm.toHom.comp er.toHom
    let lli := el.symm.toHom.comp (δi.comp pl.toHom)
    let rri := er.symm.toHom.comp pr.toHom
    have hll (x : Z) (v : C.Fiber (DoubleSpace.left A x)) :
        ll.linearMap x v = δ.linearMap x (el.linearEquiv x v) := by
      exact hpli x _
    have hrr (x : Z) (v : C.Fiber (DoubleSpace.right A x)) :
        rr.linearMap x v = er.linearEquiv x v := by
      exact hpri x _
    have hlli (x : Z) (v : P.Fiber (DoubleSpace.left A x)) :
        lli.linearMap x v = (el.linearEquiv x).symm (δi.linearMap x v) := by
      change (el.linearEquiv x).symm (δi.linearMap x (pl.linearEquiv x v)) = _
      erw [hpl]
    have hrri (x : Z) (v : P.Fiber (DoubleSpace.right A x)) :
        rri.linearMap x v = (er.linearEquiv x).symm v := by
      change (er.linearEquiv x).symm (pr.linearEquiv x v) = _
      erw [hpr]
    have hcastP (x : A) (v : c.target.Fiber x) :
        cast (congrArg P.Fiber (DoubleSpace.left_eq_right A x)) v = v := by
      have hp : congrArg P.Fiber (DoubleSpace.left_eq_right A x) = rfl :=
        Subsingleton.elim _ _
      exact congrArg (fun h : c.target.Fiber x = c.target.Fiber x ↦ cast h v) hp
    have transport {z w : DoubleSpace A} (h : z = w)
        (f : C.Fiber z →ₗ[ℂ] P.Fiber z) (g : C.Fiber w →ₗ[ℂ] P.Fiber w)
        (hf : ∀ v, cast (congrArg P.Fiber h) (f v) =
          g (cast (congrArg C.Fiber h) v)) : HEq f g := by
      cases h
      exact heq_of_eq (LinearMap.ext hf)
    have transporti {z w : DoubleSpace A} (h : z = w)
        (f : P.Fiber z →ₗ[ℂ] C.Fiber z) (g : P.Fiber w →ₗ[ℂ] C.Fiber w)
        (hf : ∀ v, cast (congrArg C.Fiber h) (f v) =
          g (cast (congrArg P.Fiber h) v)) : HEq f g := by
      cases h
      exact heq_of_eq (LinearMap.ext hf)
    have hseam : ∀ x : A, HEq (ll.linearMap x.val) (rr.linearMap x.val) := by
      intro x
      apply transport (DoubleSpace.left_eq_right A x)
      intro v
      erw [hll, hcastP, hrr, hboundary x]
      change c.boundary.linearEquiv x (el.linearEquiv x v) =
        er.linearEquiv x (cast (congrArg C.Fiber (DoubleSpace.left_eq_right A x)) v)
      simpa only [el, er, LinearEquiv.symm_apply_apply] using
        (clutching_seam_apply hA c x (el.linearEquiv x v)).symm
    have hseami : ∀ x : A, HEq (lli.linearMap x.val) (rri.linearMap x.val) := by
      intro x
      apply transporti (DoubleSpace.left_eq_right A x)
      intro v
      erw [hlli, hcastP, hrri]
      apply (er.linearEquiv x).injective
      erw [clutching_seam_apply, LinearEquiv.apply_symm_apply, hboundaryi x]
      exact (c.boundary.linearEquiv x).apply_symm_apply v
    obtain ⟨Δ, hΔl, hΔr⟩ := glueHom A hA C P ll rr hseam
    obtain ⟨Δi, hΔil, hΔir⟩ := glueHom A hA P C lli rri hseami
    -- The same scalar is rho squared on the left and one on the right.
    let r (z : DoubleSpace A) : ℝ :=
      if DoubleSpace.left A (DoubleSpace.proj A z) = z then s (DoubleSpace.proj A z) else 1
    have hrl (x : Z) : r (DoubleSpace.left A x) = s x := by
      simp only [r, DoubleSpace.proj_left, ite_true]
    have hrright (x : Z) : r (DoubleSpace.right A x) = 1 := by
      dsimp only [r, DoubleSpace.proj_right]
      split_ifs with h
      · exact hboundarys ⟨x, ((DoubleSpace.left_eq_right_iff A x x).mp h).2⟩
      · rfl
    have hrpos (z : DoubleSpace A) : 0 ≤ r z := by
      dsimp only [r]
      split_ifs
      · exact hs _
      · norm_num
    refine ⟨Δ, Δi, r, hrpos, hrright, ?_, ?_, ?_⟩
    · intro z
      induction z using Quotient.inductionOn with
      | h z =>
        cases z with
        | inl x =>
          erw [hrl]
          constructor
          · apply LinearMap.ext
            intro v
            change Δi.linearMap (DoubleSpace.left A x)
              (Δ.linearMap (DoubleSpace.left A x) v) = (s x : ℂ) • v
            erw [hΔl, hΔil, hll, hlli]
            have h := congrArg (fun f ↦ f (el.linearEquiv x v)) (hcomposition x).1
            change δi.linearMap x (δ.linearMap x (el.linearEquiv x v)) =
              (s x : ℂ) • el.linearEquiv x v at h
            erw [h, map_smul, LinearEquiv.symm_apply_apply]
          · apply LinearMap.ext
            intro v
            change Δ.linearMap (DoubleSpace.left A x)
              (Δi.linearMap (DoubleSpace.left A x) v) = (s x : ℂ) • v
            erw [hΔl, hΔil, hlli, hll, LinearEquiv.apply_symm_apply]
            exact congrArg (fun f ↦ f v) (hcomposition x).2
        | inr x =>
          erw [hrright]
          constructor
          · apply LinearMap.ext
            intro v
            change Δi.linearMap (DoubleSpace.right A x)
              (Δ.linearMap (DoubleSpace.right A x) v) = (1 : ℂ) • v
            erw [hΔr, hΔir, hrr, hrri, LinearEquiv.symm_apply_apply, one_smul]
          · apply LinearMap.ext
            intro v
            change Δ.linearMap (DoubleSpace.right A x)
              (Δi.linearMap (DoubleSpace.right A x) v) = (1 : ℂ) • v
            erw [hΔr, hΔir, hrri, hrr, LinearEquiv.apply_symm_apply, one_smul]
    · intro x v
      erw [hΔl]
      exact hll x v
    · intro x v
      erw [hΔil]
      exact hlli x v
  -- Choose compact windows around the supplied enlarged controls, preserving those controls.
  have haL : a.datum.control ⊆ L := by
    intro x hx
    by_contra hxL
    have h := hone x hxL
    rw [hzero x (hcontrol hx)] at h
    exact zero_ne_one h
  have hbM : b.datum.control ⊆ M := by
    intro y hy
    by_contra hyM
    have h := hbone y hyM
    rw [hbzero y (hbcontrol hy)] at h
    exact zero_ne_one h
  let N := supportNeighborhood L hL
  let O := supportNeighborhood M hM
  have hN : IsCompact N := isCompact_supportNeighborhood L hL
  have hO : IsCompact O := isCompact_supportNeighborhood M hM
  have hLN : L ⊆ interior N := subset_interior_supportNeighborhood L hL
  have hMO : M ⊆ interior O := subset_interior_supportNeighborhood M hM
  have haN : a.datum.control ⊆ interior N := haL.trans hLN
  have hbO : b.datum.control ⊆ interior O := hbM.trans hMO
  let := isCompact_iff_compactSpace.mp hN
  let := isCompact_iff_compactSpace.mp hO
  let A := supportWindowBoundary N
  let B := supportWindowBoundary O
  have hA : IsClosed A := isClosed_supportWindowBoundary N
  have hB : IsClosed B := isClosed_supportWindowBoundary O
  let aw := a.windowTriple N haN
  let bw := b.windowTriple O hbO
  let iN : C(N, X) := ⟨Subtype.val, continuous_subtype_val⟩
  let iO : C(O, Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let δa := (a.datum.cutoffHom ρ U hU hcontrol hzero).pullback iN
  let δai := (a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).pullback iN
  let δb := (b.datum.cutoffHom τ V hV hbcontrol hbzero).pullback iO
  let δbi := (b.datum.inverse.cutoffHom τ V hV hbcontrol hbzero).pullback iO
  have hρA (x : A) : ρ x.val.val = 1 :=
    hone x.val.val (supportWindowBoundary_subset L N hLN x.property)
  have hτB (y : B) : τ y.val.val = 1 :=
    hbone y.val.val (supportWindowBoundary_subset M O hMO y.property)
  have hδaBoundary (x : A) :
      δa.linearMap x = (aw.boundary.linearEquiv x).toLinearMap ∧
      δai.linearMap x = (aw.boundary.linearEquiv x).symm.toLinearMap := by
    let z : (a.datum.controlᶜ : Set X) :=
      ⟨x.val.val, supportWindowBoundary_subset a.datum.control N haN x.property⟩
    have hw : aw.boundary.linearEquiv x = a.datum.boundary.linearEquiv z := by
      apply LinearEquiv.ext
      intro v
      exact a.windowBoundary_apply N haN x v
    have h := a.datum.cutoffHom_boundary ρ U hU hcontrol hzero z (hρA x)
    change (a.datum.cutoffHom ρ U hU hcontrol hzero).linearMap z = _ ∧
      (a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).linearMap z = _
    rw [hw]
    exact h
  have hδbBoundary (y : B) :
      δb.linearMap y = (bw.boundary.linearEquiv y).toLinearMap ∧
      δbi.linearMap y = (bw.boundary.linearEquiv y).symm.toLinearMap := by
    let z : (b.datum.controlᶜ : Set Y) :=
      ⟨y.val.val, supportWindowBoundary_subset b.datum.control O hbO y.property⟩
    have hw : bw.boundary.linearEquiv y = b.datum.boundary.linearEquiv z := by
      apply LinearEquiv.ext
      intro v
      exact b.windowBoundary_apply O hbO y v
    have h := b.datum.cutoffHom_boundary τ V hV hbcontrol hbzero z (hτB y)
    change (b.datum.cutoffHom τ V hV hbcontrol hbzero).linearMap z = _ ∧
      (b.datum.inverse.cutoffHom τ V hV hbcontrol hbzero).linearMap z = _
    rw [hw]
    exact h
  let := DoubleSpace.t2Space A hA
  let := DoubleSpace.t2Space B hB
  let := DoubleSpace.compactSpace A
  let := DoubleSpace.compactSpace B
  let Ca := clutchingBundle hA aw
  let Pa := aw.target.pullback (DoubleSpace.projMap A)
  let Cb := clutchingBundle hB bw
  let Pb := bw.target.pullback (DoubleSpace.projMap B)
  have hcompa (x : N) :
      (δai.linearMap x).comp (δa.linearMap x) =
        (((ρ x.val : ℝ) ^ 2 : ℝ) : ℂ) • (LinearMap.id :
          aw.source.Fiber x →ₗ[ℂ] aw.source.Fiber x) ∧
      (δa.linearMap x).comp (δai.linearMap x) =
        (((ρ x.val : ℝ) ^ 2 : ℝ) : ℂ) • (LinearMap.id :
          aw.target.Fiber x →ₗ[ℂ] aw.target.Fiber x) := by
    change ((a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).linearMap x.val).comp
        ((a.datum.cutoffHom ρ U hU hcontrol hzero).linearMap x.val) =
          (((ρ x.val : ℝ) ^ 2 : ℝ) : ℂ) • LinearMap.id ∧
      ((a.datum.cutoffHom ρ U hU hcontrol hzero).linearMap x.val).comp
        ((a.datum.inverse.cutoffHom ρ U hU hcontrol hzero).linearMap x.val) =
          (((ρ x.val : ℝ) ^ 2 : ℝ) : ℂ) • LinearMap.id
    simpa only [Complex.ofReal_pow] using
      a.datum.cutoffHom_inverse_comp ρ U hU hcontrol hzero x.val
  have hcompb (y : O) :
      (δbi.linearMap y).comp (δb.linearMap y) =
        (((τ y.val : ℝ) ^ 2 : ℝ) : ℂ) • (LinearMap.id :
          bw.source.Fiber y →ₗ[ℂ] bw.source.Fiber y) ∧
      (δb.linearMap y).comp (δbi.linearMap y) =
        (((τ y.val : ℝ) ^ 2 : ℝ) : ℂ) • (LinearMap.id :
          bw.target.Fiber y →ₗ[ℂ] bw.target.Fiber y) := by
    change ((b.datum.inverse.cutoffHom τ V hV hbcontrol hbzero).linearMap y.val).comp
        ((b.datum.cutoffHom τ V hV hbcontrol hbzero).linearMap y.val) =
          (((τ y.val : ℝ) ^ 2 : ℝ) : ℂ) • LinearMap.id ∧
      ((b.datum.cutoffHom τ V hV hbcontrol hbzero).linearMap y.val).comp
        ((b.datum.inverse.cutoffHom τ V hV hbcontrol hbzero).linearMap y.val) =
          (((τ y.val : ℝ) ^ 2 : ℝ) : ℂ) • LinearMap.id
    simpa only [Complex.ofReal_pow] using
      b.datum.cutoffHom_inverse_comp τ V hV hbcontrol hbzero y.val
  obtain ⟨Δa, Δai, ra, hra, hraRight, hΔacomp, hΔaLeft, hΔaiLeft⟩ :=
    doubleMapsX A hA aw δa δai (fun x : N ↦ (ρ x.val : ℝ) ^ 2)
      (fun x ↦ sq_nonneg _) hcompa (fun x ↦ (hδaBoundary x).1)
      (fun x ↦ (hδaBoundary x).2) (by intro x; rw [hρA x]; norm_num)
  obtain ⟨Δb, Δbi, rb, hrb, hrbRight, hΔbcomp, hΔbLeft, hΔbiLeft⟩ :=
    doubleMapsY B hB bw δb δbi (fun y : O ↦ (τ y.val : ℝ) ^ 2)
      (fun y ↦ sq_nonneg _) hcompb (fun y ↦ (hδbBoundary y).1)
      (fun y ↦ (hδbBoundary y).2) (by intro y; rw [hτB y]; norm_num)
  -- On the product of the actual doubles, form exactly the positive reciprocal block.
  let Z := DoubleSpace A × DoubleSpace B
  let RA := DoubleSpace.rightRange A
  let RB := DoubleSpace.rightRange B
  have hRA : IsClosed RA := DoubleSpace.isClosed_rightRange A hA
  have hRB : IsClosed RB := DoubleSpace.isClosed_rightRange B hB
  let Q := relativeProductSubset RA RB
  have hQ : IsClosed Q := isClosed_relativeProductSubset RA hRA RB hRB
  let Even := ((Ca.pullback ContinuousMap.fst).tensor (Cb.pullback ContinuousMap.snd)).sum
    ((Pa.pullback ContinuousMap.fst).tensor (Pb.pullback ContinuousMap.snd))
  let Odd := ((Pa.pullback ContinuousMap.fst).tensor (Cb.pullback ContinuousMap.snd)).sum
    ((Ca.pullback ContinuousMap.fst).tensor (Pb.pullback ContinuousMap.snd))
  have hnonzero (z : Q) : (ra z.val.1 : ℂ) + (rb z.val.2 : ℂ) ≠ 0 := by
    have hp : 0 < ra z.val.1 + rb z.val.2 := by
      rcases z.property with hx | hy
      · obtain ⟨x, hx⟩ := hx
        rw [← hx, hraRight]
        linarith [hrb z.val.2]
      · obtain ⟨y, hy⟩ := hy
        rw [← hy, hrbRight]
        linarith [hra z.val.1]
    exact_mod_cast (ne_of_gt hp)
  let row (S T : FiniteBundle Z) (f g : Hom S.Fiber T.Fiber) (c : ℂ) :
      Hom S.Fiber T.Fiber :=
    { linearMap z := f.linearMap z + c • g.linearMap z
      continuous_total := by
        let p : C(TotalSpace Unit S.Fiber, Z) :=
          ⟨fun z ↦ z.proj, continuous_proj (E := S.Fiber)⟩
        let := isFiniteRank_pullback (E := T.Fiber) p
        have hf : Continuous (fun z : TotalSpace Unit S.Fiber ↦
            (⟨z, f.linearMap z.proj z.snd⟩ :
              TotalSpace Unit ((p : TotalSpace Unit S.Fiber → Z) *ᵖ T.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
          exact continuous_id.prodMk f.continuous_total
        have hg : Continuous (fun z : TotalSpace Unit S.Fiber ↦
            (⟨z, g.linearMap z.proj z.snd⟩ :
              TotalSpace Unit ((p : TotalSpace Unit S.Fiber → Z) *ᵖ T.Fiber))) := by
          rw [(inducing_pullbackTotalSpaceEmbedding Unit T.Fiber p).continuous_iff]
          exact continuous_id.prodMk g.continuous_total
        exact (Pullback.continuous_lift Unit T.Fiber p).comp
          (continuous_add_section ((p : TotalSpace Unit S.Fiber → Z) *ᵖ T.Fiber)
            _ _ hf (continuous_smul_section _ (ContinuousMap.const _ c) _ hg)) }
  let φa := Δa.pullback (ContinuousMap.fst : C(Z, DoubleSpace A))
  let ψa := Δai.pullback (ContinuousMap.fst : C(Z, DoubleSpace A))
  let φb := Δb.pullback (ContinuousMap.snd : C(Z, DoubleSpace B))
  let ψb := Δbi.pullback (ContinuousMap.snd : C(Z, DoubleSpace B))
  let upper := row Even ((Pa.pullback ContinuousMap.fst).tensor (Cb.pullback ContinuousMap.snd))
    ((φa.tensor (Hom.id _)).comp sumFst) (((Hom.id _).tensor ψb).comp sumSnd) (-1)
  let lower := row Even ((Ca.pullback ContinuousMap.fst).tensor (Pb.pullback ContinuousMap.snd))
    (((Hom.id _).tensor φb).comp sumFst) ((ψa.tensor (Hom.id _)).comp sumSnd) 1
  let forward : Hom Even.Fiber Odd.Fiber :=
    { linearMap z := reciprocalTensorSymbol (Δa.linearMap z.1) (Δai.linearMap z.1)
        (Δb.linearMap z.2) (Δbi.linearMap z.2)
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply (upper.continuous_total.prodMk lower.continuous_total).congr
        intro z
        apply Prod.ext <;> apply congrArg (TotalSpace.mk z.proj) <;>
          simp only [upper, lower, row, Hom.comp, Hom.tensor, Hom.id, Hom.pullback,
          φa, ψa, φb, ψb, sumFst, sumSnd, reciprocalTensorSymbol,
          neg_one_smul, one_smul]
        all_goals rfl }
  let restricted := forward.pullback
    (⟨Subtype.val, continuous_subtype_val⟩ : C(Q, Z))
  let fiberEquiv (z : Q) := reciprocalTensorSymbolEquiv
    (Δa.linearMap z.val.1) (Δai.linearMap z.val.1)
    (Δb.linearMap z.val.2) (Δbi.linearMap z.val.2)
    (ra z.val.1 : ℂ) (rb z.val.2 : ℂ)
    (hΔacomp z.val.1).1 (hΔacomp z.val.1).2
    (hΔbcomp z.val.2).1 (hΔbcomp z.val.2).2 (hnonzero z)
  have hbijective (z : Q) : Function.Bijective (restricted.linearMap z) :=
    (fiberEquiv z).bijective
  let boundary : RelativeTriple Even.Fiber Odd.Fiber Q :=
    { linearEquiv := fiberEquiv
      continuous_total := restricted.continuous_total
      continuous_symm := by
        apply (restricted.continuous_inverse hbijective).congr
        intro z
        apply congrArg (TotalSpace.mk z.proj)
        apply (fiberEquiv z.proj).injective
        exact (LinearEquiv.apply_symm_apply
          (LinearEquiv.ofBijective (restricted.linearMap z.proj) (hbijective z.proj))
            z.snd).trans ((fiberEquiv z.proj).apply_symm_apply z.snd).symm }
  let cD := BundleTriple.ofBoundary Even Odd boundary
  -- Forget only on the product of the two specified right retract pairs.
  have hclassD : cD.relativeClass.{_, 0} hQ = relativeKZeroExternalProduct RA hRA RB hRB
      (aw.differenceLift.{_, 0} hA) (bw.differenceLift.{_, 0} hB) := by
    apply relativeKZeroForget_injective_of_product_retractions RA hRA RB hRB
      (DoubleSpace.rightRetraction A) (DoubleSpace.rightRetraction_apply A)
      (DoubleSpace.rightRetraction B) (DoubleSpace.rightRetraction_apply B)
    rw [BundleTriple.relativeClass_forget, relativeKZeroForget_externalProduct,
      BundleTriple.forget_differenceLift, BundleTriple.forget_differenceLift]
    have hPa : Pa.kZeroClass = complexKZeroPullback (DoubleSpace.projMap A)
        aw.target.kZeroClass := FiniteBundle.kZeroClass_pullback _ _
    have hPb : Pb.kZeroClass = complexKZeroPullback (DoubleSpace.projMap B)
        bw.target.kZeroClass := FiniteBundle.kZeroClass_pullback _ _
    change Even.kZeroClass - Odd.kZeroClass = complexKZeroExternalProduct
      (Ca.kZeroClass - complexKZeroPullback (DoubleSpace.projMap A) aw.target.kZeroClass)
      (Cb.kZeroClass - complexKZeroPullback (DoubleSpace.projMap B) bw.target.kZeroClass)
    rw [← hPa, ← hPb]
    have tensorClass (E F : FiniteBundle Z) :
        (E.tensor F).kZeroClass = kZeroMul C(Z, ℂ) E.kZeroClass F.kZeroClass := by
      exact kZeroClass_tensor
    change (((Ca.pullback ContinuousMap.fst).tensor (Cb.pullback ContinuousMap.snd)).sum
      ((Pa.pullback ContinuousMap.fst).tensor (Pb.pullback ContinuousMap.snd))).kZeroClass -
      (((Pa.pullback ContinuousMap.fst).tensor (Cb.pullback ContinuousMap.snd)).sum
        ((Ca.pullback ContinuousMap.fst).tensor (Pb.pullback ContinuousMap.snd))).kZeroClass = _
    rw [FiniteBundle.kZeroClass_sum, FiniteBundle.kZeroClass_sum,
      tensorClass, tensorClass, tensorClass, tensorClass]
    simp only [FiniteBundle.kZeroClass_pullback]
    change kZeroMul C(Z, ℂ) _ _ + kZeroMul C(Z, ℂ) _ _ -
      (kZeroMul C(Z, ℂ) _ _ + kZeroMul C(Z, ℂ) _ _) =
        kZeroMul C(Z, ℂ)
          (complexKZeroPullback ContinuousMap.fst (Ca.kZeroClass - Pa.kZeroClass))
          (complexKZeroPullback ContinuousMap.snd (Cb.kZeroClass - Pb.kZeroClass))
    simp only [map_sub, AddMonoidHom.sub_apply]
    abel
  -- The left-left pullback sees exactly the original union of window boundaries.
  let T := N × O
  let leftLeft : C(T, Z) := (DoubleSpace.leftMap A).prodMap (DoubleSpace.leftMap B)
  let Q0 := relativeProductSubset A B
  have hQ0 : IsClosed Q0 := isClosed_relativeProductSubset A hA B hB
  have hleftA : (DoubleSpace.leftMap A) ⁻¹' RA = A := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      exact ((DoubleSpace.left_eq_right_iff A x y).mp hy.symm).2
    · exact fun hx ↦ DoubleSpace.left_mapsTo A hx
  have hleftB : (DoubleSpace.leftMap B) ⁻¹' RB = B := by
    ext y
    constructor
    · rintro ⟨z, hz⟩
      exact ((DoubleSpace.left_eq_right_iff B y z).mp hz.symm).2
    · exact fun hy ↦ DoubleSpace.left_mapsTo B hy
  have hleftPreimage : leftLeft ⁻¹' Q = Q0 := by
    ext z
    change ((DoubleSpace.leftMap A) z.1 ∈ RA ∨ (DoubleSpace.leftMap B) z.2 ∈ RB) ↔
      (z.1 ∈ A ∨ z.2 ∈ B)
    change (z.1 ∈ (DoubleSpace.leftMap A) ⁻¹' RA ∨
      z.2 ∈ (DoubleSpace.leftMap B) ⁻¹' RB) ↔ _
    rw [hleftA, hleftB]
  have hleftPair : Set.MapsTo leftLeft Q0 Q := by
    intro z hz
    exact hz.elim (fun hx ↦ Or.inl (DoubleSpace.left_mapsTo A hx))
      (fun hy ↦ Or.inr (DoubleSpace.left_mapsTo B hy))
  have hclassLeft : relativeKZeroPullback Q0 hQ0 Q hQ leftLeft hleftPair
      (cD.relativeClass.{_, 0} hQ) = relativeKZeroExternalProduct A hA B hB
        (aw.relativeClass.{_, 0} hA) (bw.relativeClass.{_, 0} hB) := by
    rw [hclassD]
    exact relativeKZeroExternalProduct_natural A hA B hB RA hRA RB hRB
      (DoubleSpace.leftMap A) (DoubleSpace.leftMap B)
      (DoubleSpace.left_mapsTo A) (DoubleSpace.left_mapsTo B)
      (aw.differenceLift.{_, 0} hA) (bw.differenceLift.{_, 0} hB)
  -- A map with the exact inverse-image boundary retains the original pulled-back triple.
  have pairPullbackClass {R : Type _} [TopologicalSpace R] [CompactSpace R] [T2Space R]
      (S : Set R) (hS : IsClosed S) (c : BundleTriple S)
      (B0 : Set T) (hB0 : IsClosed B0) (f : C(T, R))
      (hf : Set.MapsTo f B0 S) (hpre : f ⁻¹' S = B0) :
      (BundleTriple.ofBoundary (c.source.pullback f) (c.target.pullback f)
        ((c.boundary.pullback f).restrict hf)).relativeClass.{_, 0} hB0 =
      relativeKZeroPullback B0 hB0 S hS f hf (c.relativeClass.{_, 0} hS) := by
    subst B0
    have hIso : (BundleTriple.ofBoundary (c.source.pullback f) (c.target.pullback f)
        ((c.boundary.pullback f).restrict hf)).IsIsomorphic (c.pullback f) := by
      refine ⟨Iso.refl _, Iso.refl _, ?_⟩
      intro z v
      exact Iso.restrictTo_apply (c.boundary.pullback f) hf z v
    exact (BundleTriple.relativeClass_eq_of_isIsomorphic hB0 _ _ hIso).trans
      (BundleTriple.relativeClass_pullback hS c f)
  let cLeft := BundleTriple.ofBoundary (cD.source.pullback leftLeft)
    (cD.target.pullback leftLeft) ((cD.boundary.pullback leftLeft).restrict hleftPair)
  have hclassCLeft : cLeft.relativeClass.{_, 0} hQ0 =
      relativeKZeroExternalProduct A hA B hB
        (aw.relativeClass.{_, 0} hA) (bw.relativeClass.{_, 0} hB) :=
    (pairPullbackClass Q hQ cD Q0 hQ0 leftLeft hleftPair hleftPreimage).trans hclassLeft
  -- Pullback and direct sum use the same vectors with their actual finite bundle topologies.
  let sumPullback {R : Type _} [TopologicalSpace R]
      (E F : FiniteBundle R) (f : C(T, R)) :
      Iso ((E.sum F).pullback f).Fiber ((E.pullback f).sum (F.pullback f)).Fiber := by
    let h : Hom ((E.sum F).pullback f).Fiber ((E.pullback f).sum (F.pullback f)).Fiber :=
      { linearMap := fun _ ↦ LinearMap.id
        continuous_total := by
          apply continuous_induced_rng.mpr
          exact ((sumFst (E := E.Fiber) (F := F.Fiber)).pullback f).continuous_total.prodMk
            ((sumSnd (E := E.Fiber) (F := F.Fiber)).pullback f).continuous_total }
    let j := h.toIso (fun _ ↦ Function.bijective_id)
    refine { linearEquiv := fun z ↦ LinearEquiv.refl ℂ (E.Fiber (f z) × F.Fiber (f z))
             continuous_total := h.continuous_total
             continuous_symm := ?_ }
    apply j.continuous_symm.congr
    intro z
    apply congrArg (TotalSpace.mk z.proj)
    exact (j.linearEquiv z.proj).apply_symm_apply z.snd
  let inc : C(T, X × Y) := iN.prodMap iO
  -- The four factor comparisons retain their actual left clutching charts.
  let chartA (W : FiniteBundle (DoubleSpace A)) (E : FiniteBundle X)
      (j : Iso (W.pullback (DoubleSpace.leftMap A)).Fiber (E.restrict N).Fiber) :
      Iso ((W.pullback ContinuousMap.fst).pullback leftLeft).Fiber
        ((E.pullback ContinuousMap.fst).pullback inc).Fiber :=
    (((pullbackCompIso (E := W.Fiber) ContinuousMap.fst leftLeft).trans
      (pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap A) ContinuousMap.fst).symm).trans
        (j.pullback ContinuousMap.fst)).trans
          ((pullbackCompIso (E := E.Fiber) iN ContinuousMap.fst).trans
            (pullbackCompIso (E := E.Fiber) ContinuousMap.fst inc).symm)
  have hchartA (W : FiniteBundle (DoubleSpace A)) (E : FiniteBundle X)
      (j : Iso (W.pullback (DoubleSpace.leftMap A)).Fiber (E.restrict N).Fiber)
      (z : T) (v : W.Fiber (DoubleSpace.left A z.1)) :
      (chartA W E j).linearEquiv z v = j.linearEquiv z.1 v := by
    have hi (w : W.Fiber (DoubleSpace.left A z.1)) :
        ((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap A)
          (ContinuousMap.fst : C(T, N))).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap A)
          (ContinuousMap.fst : C(T, N))).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    have hi' (w : E.Fiber z.1.val) :
        ((pullbackCompIso (E := E.Fiber) (ContinuousMap.fst : C(X × Y, X))
          inc).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := E.Fiber) (ContinuousMap.fst : C(X × Y, X))
          inc).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    change ((pullbackCompIso (E := E.Fiber) ContinuousMap.fst inc).linearEquiv z).symm
      ((pullbackCompIso (E := E.Fiber) iN ContinuousMap.fst).linearEquiv z
        (j.linearEquiv z.1
          (((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap A)
            ContinuousMap.fst).linearEquiv z).symm
              ((pullbackCompIso (E := W.Fiber) ContinuousMap.fst leftLeft).linearEquiv z v)))) = _
    erw [pullbackCompIso_apply, hi, pullbackCompIso_apply, hi']
  let chartB (W : FiniteBundle (DoubleSpace B)) (F : FiniteBundle Y)
      (j : Iso (W.pullback (DoubleSpace.leftMap B)).Fiber (F.restrict O).Fiber) :
      Iso ((W.pullback ContinuousMap.snd).pullback leftLeft).Fiber
        ((F.pullback ContinuousMap.snd).pullback inc).Fiber :=
    (((pullbackCompIso (E := W.Fiber) ContinuousMap.snd leftLeft).trans
      (pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap B) ContinuousMap.snd).symm).trans
        (j.pullback ContinuousMap.snd)).trans
          ((pullbackCompIso (E := F.Fiber) iO ContinuousMap.snd).trans
            (pullbackCompIso (E := F.Fiber) ContinuousMap.snd inc).symm)
  have hchartB (W : FiniteBundle (DoubleSpace B)) (F : FiniteBundle Y)
      (j : Iso (W.pullback (DoubleSpace.leftMap B)).Fiber (F.restrict O).Fiber)
      (z : T) (v : W.Fiber (DoubleSpace.left B z.2)) :
      (chartB W F j).linearEquiv z v = j.linearEquiv z.2 v := by
    have hi (w : W.Fiber (DoubleSpace.left B z.2)) :
        ((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap B)
          (ContinuousMap.snd : C(T, O))).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap B)
          (ContinuousMap.snd : C(T, O))).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    have hi' (w : F.Fiber z.2.val) :
        ((pullbackCompIso (E := F.Fiber) (ContinuousMap.snd : C(X × Y, Y))
          inc).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := F.Fiber) (ContinuousMap.snd : C(X × Y, Y))
          inc).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    change ((pullbackCompIso (E := F.Fiber) ContinuousMap.snd inc).linearEquiv z).symm
      ((pullbackCompIso (E := F.Fiber) iO ContinuousMap.snd).linearEquiv z
        (j.linearEquiv z.2
          (((pullbackCompIso (E := W.Fiber) (DoubleSpace.leftMap B)
            ContinuousMap.snd).linearEquiv z).symm
              ((pullbackCompIso (E := W.Fiber) ContinuousMap.snd leftLeft).linearEquiv z v)))) = _
    erw [pullbackCompIso_apply, hi, pullbackCompIso_apply, hi']
  let paLeft : Iso (Pa.pullback (DoubleSpace.leftMap A)).Fiber aw.target.Fiber :=
    (pullbackCompIso (E := aw.target.Fiber) (DoubleSpace.projMap A)
      (DoubleSpace.leftMap A)).trans (pullbackIdIso (E := aw.target.Fiber))
  let pbLeft : Iso (Pb.pullback (DoubleSpace.leftMap B)).Fiber bw.target.Fiber :=
    (pullbackCompIso (E := bw.target.Fiber) (DoubleSpace.projMap B)
      (DoubleSpace.leftMap B)).trans (pullbackIdIso (E := bw.target.Fiber))
  let a0 := chartA Ca a.source (clutchingLeftIso hA aw)
  let a1 := chartA Pa a.target paLeft
  let b0 := chartB Cb b.source (clutchingLeftIso hB bw)
  let b1 := chartB Pb b.target pbLeft
  have ha0 (z : T) (v : Ca.Fiber (DoubleSpace.left A z.1)) :
      a0.linearEquiv z v = (clutchingLeftIso hA aw).linearEquiv z.1 v :=
    hchartA Ca a.source _ z v
  have hb0 (z : T) (v : Cb.Fiber (DoubleSpace.left B z.2)) :
      b0.linearEquiv z v = (clutchingLeftIso hB bw).linearEquiv z.2 v :=
    hchartB Cb b.source _ z v
  have ha1 (z : T) (v : Pa.Fiber (DoubleSpace.left A z.1)) : a1.linearEquiv z v = v := by
    erw [hchartA]
    change (pullbackIdIso (E := aw.target.Fiber)).linearEquiv z.1
      ((pullbackCompIso (E := aw.target.Fiber) (DoubleSpace.projMap A)
        (DoubleSpace.leftMap A)).linearEquiv z.1 v) = v
    rw [pullbackCompIso_apply, pullbackIdIso_apply]
  have hb1 (z : T) (v : Pb.Fiber (DoubleSpace.left B z.2)) : b1.linearEquiv z v = v := by
    erw [hchartB]
    change (pullbackIdIso (E := bw.target.Fiber)).linearEquiv z.2
      ((pullbackCompIso (E := bw.target.Fiber) (DoubleSpace.projMap B)
        (DoubleSpace.leftMap B)).linearEquiv z.2 v) = v
    rw [pullbackCompIso_apply, pullbackIdIso_apply]
  let tensorCompare (E F : FiniteBundle Z) (E' F' : FiniteBundle (X × Y))
      (j : Iso (E.pullback leftLeft).Fiber (E'.pullback inc).Fiber)
      (k : Iso (F.pullback leftLeft).Fiber (F'.pullback inc).Fiber) :
      Iso ((E.tensor F).pullback leftLeft).Fiber ((E'.tensor F').pullback inc).Fiber :=
    ((pullbackTensorIso leftLeft).trans (j.tensor k)).trans (pullbackTensorIso inc).symm
  let e00 := tensorCompare (Ca.pullback ContinuousMap.fst) (Cb.pullback ContinuousMap.snd)
    (a.source.pullback ContinuousMap.fst) (b.source.pullback ContinuousMap.snd) a0 b0
  let e11 := tensorCompare (Pa.pullback ContinuousMap.fst) (Pb.pullback ContinuousMap.snd)
    (a.target.pullback ContinuousMap.fst) (b.target.pullback ContinuousMap.snd) a1 b1
  let e10 := tensorCompare (Pa.pullback ContinuousMap.fst) (Cb.pullback ContinuousMap.snd)
    (a.target.pullback ContinuousMap.fst) (b.source.pullback ContinuousMap.snd) a1 b0
  let e01 := tensorCompare (Ca.pullback ContinuousMap.fst) (Pb.pullback ContinuousMap.snd)
    (a.source.pullback ContinuousMap.fst) (b.target.pullback ContinuousMap.snd) a0 b1
  let eSource0 : Iso (Even.pullback leftLeft).Fiber
      ((a.externalProductSource b).pullback inc).Fiber :=
    ((sumPullback _ _ leftLeft).trans (e00.sum e11)).trans (sumPullback _ _ inc).symm
  let eTarget0 : Iso (Odd.pullback leftLeft).Fiber
      ((a.externalProductTarget b).pullback inc).Fiber :=
    ((sumPullback _ _ leftLeft).trans (e10.sum e01)).trans (sumPullback _ _ inc).symm
  have heSource0 (z : T) (v : Even.Fiber (leftLeft z)) : eSource0.linearEquiv z v =
      ((TensorProduct.congr (a0.linearEquiv z) (b0.linearEquiv z)) v.1,
        (TensorProduct.congr (a1.linearEquiv z) (b1.linearEquiv z)) v.2) := by
    rfl
  have heTarget0 (z : T) (v : Odd.Fiber (leftLeft z)) : eTarget0.linearEquiv z v =
      ((TensorProduct.congr (a1.linearEquiv z) (b0.linearEquiv z)) v.1,
        (TensorProduct.congr (a0.linearEquiv z) (b1.linearEquiv z)) v.2) := by
    rfl
  -- Compare with the actual product-window triple over the same coordinates.
  let c := supportedExternalProductTriple a b ρ U hU hcontrol hzero L hL hone
    τ V hV hbcontrol hbzero M hM hbone
  have hc : c.datum.control ⊆ interior (N ×ˢ O) := by
    rw [interior_prod_eq]
    intro z hz
    exact ⟨hLN hz.1, hMO hz.2⟩
  let K := N ×ˢ O
  let := isCompact_iff_compactSpace.mp (hN.prod hO)
  let W := supportWindowBoundary K
  have hW : IsClosed W := isClosed_supportWindowBoundary K
  let eW := (Homeomorph.Set.prod N O).symm
  let fW : C(T, K) := ⟨eW, eW.continuous⟩
  have hwindowPair (z : T) : fW z ∈ W ↔ z ∈ Q0 := by
    change ((z.1.val, z.2.val) ∉ interior (N ×ˢ O)) ↔
      (z.1.val ∉ interior N ∨ z.2.val ∉ interior O)
    rw [interior_prod_eq]
    simp only [Set.mem_prod, not_and_or]
  have hwindowMap : Set.MapsTo fW Q0 W := fun z hz ↦ (hwindowPair z).mpr hz
  have hwindowPreimage : fW ⁻¹' W = Q0 := Set.ext hwindowPair
  let cW := c.windowTriple K hc
  let wLeft := BundleTriple.ofBoundary (cW.source.pullback fW) (cW.target.pullback fW)
    ((cW.boundary.pullback fW).restrict hwindowMap)
  let iW : C(K, X × Y) := ⟨Subtype.val, continuous_subtype_val⟩
  let eSource : Iso cLeft.source.Fiber wLeft.source.Fiber :=
    eSource0.trans (pullbackCompIso (E := c.source.Fiber) iW fW).symm
  let eTarget : Iso cLeft.target.Fiber wLeft.target.Fiber :=
    eTarget0.trans (pullbackCompIso (E := c.target.Fiber) iW fW).symm
  have heSource (z : T) (v : Even.Fiber (leftLeft z)) : eSource.linearEquiv z v =
      ((TensorProduct.congr (a0.linearEquiv z) (b0.linearEquiv z)) v.1,
        (TensorProduct.congr (a1.linearEquiv z) (b1.linearEquiv z)) v.2) := by
    change ((pullbackCompIso (E := c.source.Fiber) iW fW).linearEquiv z).symm
      (eSource0.linearEquiv z v) = _
    have hi (w : c.source.Fiber (inc z)) :
        ((pullbackCompIso (E := c.source.Fiber) iW fW).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := c.source.Fiber) iW fW).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    erw [hi]
    exact heSource0 z v
  have heTarget (z : T) (v : Odd.Fiber (leftLeft z)) : eTarget.linearEquiv z v =
      ((TensorProduct.congr (a1.linearEquiv z) (b0.linearEquiv z)) v.1,
        (TensorProduct.congr (a0.linearEquiv z) (b1.linearEquiv z)) v.2) := by
    change ((pullbackCompIso (E := c.target.Fiber) iW fW).linearEquiv z).symm
      (eTarget0.linearEquiv z v) = _
    have hi (w : c.target.Fiber (inc z)) :
        ((pullbackCompIso (E := c.target.Fiber) iW fW).linearEquiv z).symm w = w :=
      by
        apply ((pullbackCompIso (E := c.target.Fiber) iW fW).linearEquiv z).injective
        erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply]
    erw [hi]
    exact heTarget0 z v
  have hcLeft (z : Q0) (v : Even.Fiber (leftLeft z.val)) :
      cLeft.boundary.linearEquiv z v = reciprocalTensorSymbol
        (Δa.linearMap (DoubleSpace.left A z.val.1))
        (Δai.linearMap (DoubleSpace.left A z.val.1))
        (Δb.linearMap (DoubleSpace.left B z.val.2))
        (Δbi.linearMap (DoubleSpace.left B z.val.2)) v := by
    have h₁ := Iso.restrictTo_apply (cD.boundary.pullback leftLeft) hleftPair z v
    have h₂ := RelativeTriple.pullback_apply cD.boundary leftLeft
      ⟨z.val, hleftPair z.property⟩ v
    exact h₁.trans h₂
  have hwLeft (z : Q0) (v : cW.source.Fiber (fW z.val)) :
      wLeft.boundary.linearEquiv z v = reciprocalTensorSymbol
        (a.datum.cutoffLinearMap ρ z.val.1.val)
        (a.datum.inverse.cutoffLinearMap ρ z.val.1.val)
        (b.datum.cutoffLinearMap τ z.val.2.val)
        (b.datum.inverse.cutoffLinearMap τ z.val.2.val) v := by
    have h₁ := Iso.restrictTo_apply (cW.boundary.pullback fW) hwindowMap z v
    have h₂ := RelativeTriple.pullback_apply cW.boundary fW
      ⟨z.val, hwindowMap z.property⟩ v
    have h₃ := c.windowBoundary_apply K hc ⟨fW z.val, hwindowMap z.property⟩ v
    exact h₁.trans (h₂.trans h₃)
  have hIso : cLeft.IsIsomorphic wLeft := by
    refine ⟨eSource, eTarget, ?_⟩
    intro z v
    change eTarget.linearEquiv z.val (cLeft.boundary.linearEquiv z v) =
      wLeft.boundary.linearEquiv z (eSource.linearEquiv z.val v)
    erw [hcLeft, heTarget, hwLeft, heSource]
    -- The actual four reciprocal maps commute with these same four factor charts.
    have hd0 (w : Ca.Fiber (DoubleSpace.left A z.val.1)) :
        a1.linearEquiv z.val (Δa.linearMap (DoubleSpace.left A z.val.1) w) =
          a.datum.cutoffLinearMap ρ z.val.1.val (a0.linearEquiv z.val w) := by
      erw [ha1, ha0, hΔaLeft]
      rfl
    have hd1 (w : Pa.Fiber (DoubleSpace.left A z.val.1)) :
        a0.linearEquiv z.val (Δai.linearMap (DoubleSpace.left A z.val.1) w) =
          a.datum.inverse.cutoffLinearMap ρ z.val.1.val (a1.linearEquiv z.val w) := by
      erw [ha0, ha1, hΔaiLeft, LinearEquiv.apply_symm_apply]
      rfl
    have he0 (w : Cb.Fiber (DoubleSpace.left B z.val.2)) :
        b1.linearEquiv z.val (Δb.linearMap (DoubleSpace.left B z.val.2) w) =
          b.datum.cutoffLinearMap τ z.val.2.val (b0.linearEquiv z.val w) := by
      erw [hb1, hb0, hΔbLeft]
      rfl
    have he1 (w : Pb.Fiber (DoubleSpace.left B z.val.2)) :
        b0.linearEquiv z.val (Δbi.linearMap (DoubleSpace.left B z.val.2) w) =
          b.datum.inverse.cutoffLinearMap τ z.val.2.val (b1.linearEquiv z.val w) := by
      erw [hb0, hb1, hΔbiLeft, LinearEquiv.apply_symm_apply]
      rfl
    -- Tensor induction checks the signed block on each original pure tensor generator.
    have hlinear :
        (LinearEquiv.prodCongr
          (TensorProduct.congr (a1.linearEquiv z.val) (b0.linearEquiv z.val))
          (TensorProduct.congr (a0.linearEquiv z.val) (b1.linearEquiv z.val))).toLinearMap.comp
            (reciprocalTensorSymbol
              (Δa.linearMap (DoubleSpace.left A z.val.1))
              (Δai.linearMap (DoubleSpace.left A z.val.1))
              (Δb.linearMap (DoubleSpace.left B z.val.2))
              (Δbi.linearMap (DoubleSpace.left B z.val.2))) =
        (reciprocalTensorSymbol
          (a.datum.cutoffLinearMap ρ z.val.1.val)
          (a.datum.inverse.cutoffLinearMap ρ z.val.1.val)
          (b.datum.cutoffLinearMap τ z.val.2.val)
          (b.datum.inverse.cutoffLinearMap τ z.val.2.val)).comp
            (LinearEquiv.prodCongr
              (TensorProduct.congr (a0.linearEquiv z.val) (b0.linearEquiv z.val))
              (TensorProduct.congr (a1.linearEquiv z.val) (b1.linearEquiv z.val))).toLinearMap := by
      apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
        intro x y <;> apply Prod.ext <;>
        simp only [LinearEquiv.coe_prodCongr, TensorProduct.toLinearMap_congr,
          LinearMap.coe_comp, LinearMap.coe_inl, LinearMap.coe_inr,
          Function.comp_apply, LinearMap.prodMap_apply]
      · change a1.linearEquiv z.val (Δa.linearMap (DoubleSpace.left A z.val.1) x) ⊗ₜ[ℂ]
            b0.linearEquiv z.val y =
          a.datum.cutoffLinearMap ρ z.val.1.val (a0.linearEquiv z.val x) ⊗ₜ[ℂ]
            b0.linearEquiv z.val y
        exact congrArg (fun w : a.target.Fiber z.val.1.val ↦
          w ⊗ₜ[ℂ] b0.linearEquiv z.val y) (hd0 x)
      · change a0.linearEquiv z.val x ⊗ₜ[ℂ]
            b1.linearEquiv z.val (Δb.linearMap (DoubleSpace.left B z.val.2) y) =
          a0.linearEquiv z.val x ⊗ₜ[ℂ]
            b.datum.cutoffLinearMap τ z.val.2.val (b0.linearEquiv z.val y)
        exact congrArg (fun w : b.target.Fiber z.val.2.val ↦
          a0.linearEquiv z.val x ⊗ₜ[ℂ] w) (he0 y)
      · change TensorProduct.map (a1.linearEquiv z.val).toLinearMap
            (b0.linearEquiv z.val).toLinearMap
            (-(x ⊗ₜ[ℂ] Δbi.linearMap (DoubleSpace.left B z.val.2) y)) =
          -(a1.linearEquiv z.val x ⊗ₜ[ℂ]
            b.datum.inverse.cutoffLinearMap τ z.val.2.val (b1.linearEquiv z.val y))
        rw [map_neg, TensorProduct.map_tmul]
        exact congrArg (fun w : b.source.Fiber z.val.2.val ↦
          -(a1.linearEquiv z.val x ⊗ₜ[ℂ] w)) (he1 y)
      · change a0.linearEquiv z.val (Δai.linearMap (DoubleSpace.left A z.val.1) x) ⊗ₜ[ℂ]
            b1.linearEquiv z.val y =
          a.datum.inverse.cutoffLinearMap ρ z.val.1.val (a1.linearEquiv z.val x) ⊗ₜ[ℂ]
            b1.linearEquiv z.val y
        exact congrArg (fun w : a.source.Fiber z.val.1.val ↦
          w ⊗ₜ[ℂ] b1.linearEquiv z.val y) (hd1 x)
    exact LinearMap.congr_fun hlinear v
  have hrelativeWindow : relativeKZeroPullback Q0 hQ0 W hW fW hwindowMap
      (cW.relativeClass.{_, 0} hW) = relativeKZeroExternalProduct A hA B hB
        (aw.relativeClass.{_, 0} hA) (bw.relativeClass.{_, 0} hB) :=
    (pairPullbackClass W hW cW Q0 hQ0 fW hwindowMap hwindowPreimage).symm.trans
      ((BundleTriple.relativeClass_eq_of_isIsomorphic hQ0 cLeft wLeft hIso).symm.trans
        hclassCLeft)
  -- Pass through the same complement and open-inclusion maps of the original windows.
  have closeProductWindows (a : SupportBundleTriple X) (b : SupportBundleTriple Y)
      (c : SupportBundleTriple (X × Y)) (N : Set X) (O : Set Y)
      (hN : IsCompact N) (hO : IsCompact O)
      (ha : a.datum.control ⊆ interior N) (hb : b.datum.control ⊆ interior O)
      (hc : c.datum.control ⊆ interior (N ×ˢ O)) :
      letI := isCompact_iff_compactSpace.mp hN
      letI := isCompact_iff_compactSpace.mp hO
      letI := isCompact_iff_compactSpace.mp (hN.prod hO)
      let A := supportWindowBoundary N
      let B := supportWindowBoundary O
      let Q := relativeProductSubset A B
      let W := supportWindowBoundary (N ×ˢ O)
      let eW := (Homeomorph.Set.prod N O).symm
      ∀ hmap : Set.MapsTo eW Q W,
        relativeKZeroPullback Q
            (isClosed_relativeProductSubset A (isClosed_supportWindowBoundary N)
              B (isClosed_supportWindowBoundary O)) W (isClosed_supportWindowBoundary _)
            ⟨eW, eW.continuous⟩ hmap
            ((c.windowTriple (N ×ˢ O) hc).relativeClass.{_, 0} (isClosed_supportWindowBoundary _)) =
          relativeKZeroExternalProduct A (isClosed_supportWindowBoundary N)
            B (isClosed_supportWindowBoundary O)
            ((a.windowTriple N ha).relativeClass.{_, 0} (isClosed_supportWindowBoundary N))
            ((b.windowTriple O hb).relativeClass.{_, 0} (isClosed_supportWindowBoundary O)) →
        c.compactSupportClass =
          compactSupportKZeroExternalProduct a.compactSupportClass b.compactSupportClass := by
    classical
    let := isCompact_iff_compactSpace.mp hN
    let := isCompact_iff_compactSpace.mp hO
    let := isCompact_iff_compactSpace.mp (hN.prod hO)
    let A := supportWindowBoundary N
    let B := supportWindowBoundary O
    let Q := relativeProductSubset A B
    let W := supportWindowBoundary (N ×ˢ O)
    let eW := (Homeomorph.Set.prod N O).symm
    dsimp only
    intro hmap hrel
    have hA : IsClosed A := isClosed_supportWindowBoundary N
    have hB : IsClosed B := isClosed_supportWindowBoundary O
    have hQ : IsClosed Q := isClosed_relativeProductSubset A hA B hB
    have hW : IsClosed W := isClosed_supportWindowBoundary _
    let := hA.isOpen_compl.locallyCompactSpace
    let := hB.isOpen_compl.locallyCompactSpace
    let := hQ.isOpen_compl.locallyCompactSpace
    let := hW.isOpen_compl.locallyCompactSpace
    let := (isOpen_interior (s := N)).locallyCompactSpace
    let := (isOpen_interior (s := O)).locallyCompactSpace
    let := (isOpen_interior (s := N ×ˢ O)).locallyCompactSpace
    let tA := (a.windowTriple N ha).relativeClass.{_, 0} hA
    let tB := (b.windowTriple O hb).relativeClass.{_, 0} hB
    let tW := (c.windowTriple (N ×ˢ O) hc).relativeClass.{_, 0} hW
    let tQ := relativeKZeroPullback Q hQ W hW ⟨eW, eW.continuous⟩ hmap tW
    -- The product pair is exactly the boundary of the original product window.
    have hpair (z : N × O) : eW z ∈ W ↔ z ∈ Q := by
      change ((z.1.val, z.2.val) ∉ interior (N ×ˢ O)) ↔
        (z.1.val ∉ interior N ∨ z.2.val ∉ interior O)
      rw [interior_prod_eq]
      simp only [Set.mem_prod, not_and_or]
    let eC : (Qᶜ : Set (N × O)) ≃ₜ (Wᶜ : Set (N ×ˢ O)) := {
      toFun := fun z ↦ ⟨eW z.val, fun hz ↦ z.property ((hpair z.val).mp hz)⟩
      invFun := fun z ↦ ⟨eW.symm z.val, fun hz ↦ z.property (by
        have h := (hpair (eW.symm z.val)).mpr hz
        simpa only [eW.apply_symm_apply] using h)⟩
      left_inv := fun _ ↦ Subtype.ext (eW.symm_apply_apply _)
      right_inv := fun _ ↦ Subtype.ext (eW.apply_symm_apply _)
      continuous_toFun := (eW.continuous.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (eW.symm.continuous.comp continuous_subtype_val).subtype_mk _ }
    -- The specified quotient pullback becomes the same complement homeomorphism pullback.
    have hcomplement : relativeKZeroToCompactSupport Q hQ tQ =
        compactSupportKZeroPullback ⟨eC, eC.continuous⟩ eC.isProperMap
          (relativeKZeroToCompactSupport W hW tW) := by
      let := PointedQuotient.t2Space.{_, 0} Q hQ
      let := PointedQuotient.t2Space.{_, 0} W hW
      let eQ := PointedQuotient.onePointHomeomorph.{_, 0} Q hQ
      let eR := PointedQuotient.onePointHomeomorph.{_, 0} W hW
      let q := PointedQuotient.mapContinuous Q W ⟨eW, eW.continuous⟩ hmap
      let iQ : C(OnePoint (Qᶜ : Set (N × O)), PointedQuotient Q) :=
        ⟨eQ.symm, eQ.symm.continuous⟩
      let iR : C(OnePoint (Wᶜ : Set (N ×ˢ O)), PointedQuotient W) :=
        ⟨eR.symm, eR.symm.continuous⟩
      let P := properOnePointMap ⟨eC, eC.continuous⟩ eC.isProperMap
      have hsquare : q.comp iQ = iR.comp P := by
        ext z
        cases z using OnePoint.rec with
        | infty =>
          change q (eQ.symm OnePoint.infty) = eR.symm OnePoint.infty
          rw [PointedQuotient.onePointHomeomorph_symm_infty,
            PointedQuotient.onePointHomeomorph_symm_infty]
          rfl
        | coe z =>
          have hqz : eQ.symm (z : OnePoint (Qᶜ : Set (N × O))) =
              PointedQuotient.of Q z := eQ.symm_apply_eq.mpr
            (PointedQuotient.onePointHomeomorph_of Q hQ z).symm
          have hrz : eR.symm ((eC z : (Wᶜ : Set (N ×ˢ O))) :
              OnePoint (Wᶜ : Set (N ×ˢ O))) = PointedQuotient.of W (eW z) :=
            eR.symm_apply_eq.mpr (PointedQuotient.onePointHomeomorph_of W hW (eC z)).symm
          change q (eQ.symm (z : OnePoint (Qᶜ : Set (N × O)))) =
            eR.symm ((eC z : (Wᶜ : Set (N ×ˢ O))) : OnePoint (Wᶜ : Set (N ×ˢ O)))
          rw [hqz, hrz]
          rfl
      apply Subtype.ext
      change complexKZeroPullback iQ (complexKZeroPullback q tW.val) =
        complexKZeroPullback P (complexKZeroPullback iR tW.val)
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp,
        ← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hsquare]
    -- Regard each original open-subset extension as its specified open pushforward.
    have pushN : compactSupportKZeroOpenPushforward
        (Subtype.val : interior N → X) isOpen_interior.isOpenEmbedding_subtypeVal =
        compactSupportKZeroOpenExtension (interior N) isOpen_interior := by
      let U := interior N
      have hU : IsOpen U := isOpen_interior
      let j : U → X := Subtype.val
      have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal
      let := hj.isOpen_range.locallyCompactSpace
      let er := hj.isEmbedding.toHomeomorph
      let i : C(Set.range j, U) := ⟨er.symm, er.symm.continuous⟩
      let k : C(OnePoint X, OnePoint (Set.range j)) :=
        ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
      let collapse : C(OnePoint X, OnePoint U) :=
        ⟨onePointCollapse U, continuous_onePointCollapse _ hU⟩
      have hm : (properOnePointMap i er.symm.isProperMap).comp k = collapse := by
        ext z
        cases z using OnePoint.rec with
        | infty => rfl
        | coe x =>
          by_cases hx : x ∈ U
          · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_mem _ _ hrange,
              onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
            apply congrArg OnePoint.some
            apply Subtype.ext
            exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
          · have hrange : x ∉ Set.range j := by
              rintro ⟨x', rfl⟩
              exact hx x'.property
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_notMem _ _ hrange,
              onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
      apply AddMonoidHom.ext
      intro t
      apply Subtype.ext
      change complexKZeroPullback k
        (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) t.val) =
        complexKZeroPullback collapse t.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hm]
    have pushO : compactSupportKZeroOpenPushforward
        (Subtype.val : interior O → Y) isOpen_interior.isOpenEmbedding_subtypeVal =
        compactSupportKZeroOpenExtension (interior O) isOpen_interior := by
      let U := interior O
      have hU : IsOpen U := isOpen_interior
      let j : U → Y := Subtype.val
      have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal
      let := hj.isOpen_range.locallyCompactSpace
      let er := hj.isEmbedding.toHomeomorph
      let i : C(Set.range j, U) := ⟨er.symm, er.symm.continuous⟩
      let k : C(OnePoint Y, OnePoint (Set.range j)) :=
        ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
      let collapse : C(OnePoint Y, OnePoint U) :=
        ⟨onePointCollapse U, continuous_onePointCollapse _ hU⟩
      have hm : (properOnePointMap i er.symm.isProperMap).comp k = collapse := by
        ext z
        cases z using OnePoint.rec with
        | infty => rfl
        | coe x =>
          by_cases hx : x ∈ U
          · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_mem _ _ hrange,
              onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
            apply congrArg OnePoint.some
            apply Subtype.ext
            exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
          · have hrange : x ∉ Set.range j := by
              rintro ⟨x', rfl⟩
              exact hx x'.property
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_notMem _ _ hrange,
              onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
      apply AddMonoidHom.ext
      intro t
      apply Subtype.ext
      change complexKZeroPullback k
        (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) t.val) =
        complexKZeroPullback collapse t.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hm]
    have pushW : compactSupportKZeroOpenPushforward
        (Subtype.val : interior (N ×ˢ O) → (X × Y)) isOpen_interior.isOpenEmbedding_subtypeVal =
        compactSupportKZeroOpenExtension (interior (N ×ˢ O)) isOpen_interior := by
      let U := interior (N ×ˢ O)
      have hU : IsOpen U := isOpen_interior
      let j : U → (X × Y) := Subtype.val
      have hj : IsOpenEmbedding j := hU.isOpenEmbedding_subtypeVal
      let := hj.isOpen_range.locallyCompactSpace
      let er := hj.isEmbedding.toHomeomorph
      let i : C(Set.range j, U) := ⟨er.symm, er.symm.continuous⟩
      let k : C(OnePoint (X × Y), OnePoint (Set.range j)) :=
        ⟨onePointCollapse (Set.range j), continuous_onePointCollapse _ hj.isOpen_range⟩
      let collapse : C(OnePoint (X × Y), OnePoint U) :=
        ⟨onePointCollapse U, continuous_onePointCollapse _ hU⟩
      have hm : (properOnePointMap i er.symm.isProperMap).comp k = collapse := by
        ext z
        cases z using OnePoint.rec with
        | infty => rfl
        | coe x =>
          by_cases hx : x ∈ U
          · have hrange : x ∈ Set.range j := ⟨⟨x, hx⟩, rfl⟩
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_mem _ _ hrange,
              onePointCollapse_coe_of_mem _ _ hx, OnePoint.map_some]
            apply congrArg OnePoint.some
            apply Subtype.ext
            exact congrArg (fun z : Set.range j ↦ z.val) (er.apply_symm_apply ⟨x, hrange⟩)
          · have hrange : x ∉ Set.range j := by
              rintro ⟨x', rfl⟩
              exact hx x'.property
            change OnePoint.map i (onePointCollapse (Set.range j) x) = onePointCollapse U x
            rw [onePointCollapse_coe_of_notMem _ _ hrange,
              onePointCollapse_coe_of_notMem _ _ hx, OnePoint.map_infty]
      apply AddMonoidHom.ext
      intro t
      apply Subtype.ext
      change complexKZeroPullback k
        (complexKZeroPullback (properOnePointMap i er.symm.isProperMap) t.val) =
        complexKZeroPullback collapse t.val
      rw [← AddMonoidHom.comp_apply, ← complexKZeroPullback_comp, hm]
    let uA := relativeKZeroToCompactSupport A hA tA
    let uB := relativeKZeroToCompactSupport B hB tB
    let uQ := relativeKZeroToCompactSupport Q hQ tQ
    let uW := relativeKZeroToCompactSupport W hW tW
    let eA := supportWindowInteriorHomeomorph N
    let eB := supportWindowInteriorHomeomorph O
    let eR := supportWindowInteriorHomeomorph (N ×ˢ O)
    let e0 := relativeProductComplementHomeomorph A B
    let eI := eA.prodCongr eB
    let eF := e0.trans eI
    let eP := eC.trans eR
    -- The relative-product comparison retains exactly the original complement coordinates.
    have hp : compactSupportKZeroHomeomorph e0 uQ =
        compactSupportKZeroExternalProduct uA uB := by
      have h := relativeKZeroExternalProduct_complement A hA B hB tA tB
      change compactSupportKZeroHomeomorph e0
        (relativeKZeroToCompactSupport Q hQ
          (relativeKZeroExternalProduct A hA B hB tA tB)) = _ at h
      rw [← show tQ = relativeKZeroExternalProduct A hA B hB tA tB from hrel] at h
      exact h
    have hpI : compactSupportKZeroHomeomorph eF uQ =
        compactSupportKZeroExternalProduct (compactSupportKZeroHomeomorph eA uA)
          (compactSupportKZeroHomeomorph eB uB) := by
      have h := congrArg (compactSupportKZeroHomeomorph eI) hp
      have hcomp : compactSupportKZeroHomeomorph eI
          (compactSupportKZeroHomeomorph e0 uQ) =
          compactSupportKZeroHomeomorph eF uQ := by
        change compactSupportKZeroPullback ⟨eI.symm, eI.symm.continuous⟩ _
          (compactSupportKZeroPullback ⟨e0.symm, e0.symm.continuous⟩ _ uQ) = _
        rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
        rfl
      rw [hcomp] at h
      exact h.trans (compactSupportKZeroExternalProduct_properPullback
        ⟨eA.symm, eA.symm.continuous⟩ eA.symm.isProperMap
        ⟨eB.symm, eB.symm.continuous⟩ eB.symm.isProperMap uA uB)
    have hP : compactSupportKZeroHomeomorph eP uQ =
        compactSupportKZeroHomeomorph eR uW := by
      change compactSupportKZeroHomeomorph eP
        (relativeKZeroToCompactSupport Q hQ tQ) = _
      rw [hcomplement]
      change compactSupportKZeroPullback ⟨eP.symm, eP.symm.continuous⟩ _
        (compactSupportKZeroPullback ⟨eC, eC.continuous⟩ _ uW) = _
      rw [← AddMonoidHom.comp_apply, ← compactSupportKZeroPullback_comp]
      have hmaps : (⟨eC, eC.continuous⟩ : C(_, _)).comp
          ⟨eP.symm, eP.symm.continuous⟩ = ⟨eR.symm, eR.symm.continuous⟩ := by
        apply ContinuousMap.ext
        intro z
        exact eC.apply_symm_apply (eR.symm z)
      simp only [hmaps]
      rfl
    -- The two open inclusions agree after the actual point-preserving identifications.
    let jW : interior (N ×ˢ O) → X × Y := Subtype.val
    let jA : interior N → X := Subtype.val
    let jB : interior O → Y := Subtype.val
    let jF := Prod.map jA jB
    have hjW : IsOpenEmbedding jW := isOpen_interior.isOpenEmbedding_subtypeVal
    have hjA : IsOpenEmbedding jA := isOpen_interior.isOpenEmbedding_subtypeVal
    have hjB : IsOpenEmbedding jB := isOpen_interior.isOpenEmbedding_subtypeVal
    have hsquare : jW ∘ eP = jF ∘ eF := rfl
    have hopen : compactSupportKZeroOpenPushforward jW hjW
        (compactSupportKZeroHomeomorph eP uQ) =
        compactSupportKZeroOpenPushforward jF (hjA.prodMap hjB)
          (compactSupportKZeroHomeomorph eF uQ) := by
      calc
        _ = compactSupportKZeroOpenPushforward (jW ∘ eP)
            (hjW.comp eP.isOpenEmbedding) uQ := by
          rw [← compactSupportKZeroOpenPushforward_homeomorph]
          exact (DFunLike.congr_fun
            (compactSupportKZeroOpenPushforward_comp eP eP.isOpenEmbedding jW hjW) uQ).symm
        _ = compactSupportKZeroOpenPushforward (jF ∘ eF)
            ((hjA.prodMap hjB).comp eF.isOpenEmbedding) uQ := by
          simp only [hsquare]
          rfl
        _ = _ := by
          rw [← compactSupportKZeroOpenPushforward_homeomorph]
          exact DFunLike.congr_fun (compactSupportKZeroOpenPushforward_comp
            eF eF.isOpenEmbedding jF (hjA.prodMap hjB)) uQ
    -- Extend the compared classes through the same three original support windows.
    rw [c.compactSupportClass_eq_windowClass (N ×ˢ O) (hN.prod hO) hc,
      a.compactSupportClass_eq_windowClass N hN ha,
      b.compactSupportClass_eq_windowClass O hO hb]
    change compactSupportKZeroOpenExtension (interior (N ×ˢ O)) isOpen_interior
        (compactSupportKZeroHomeomorph eR uW) =
      compactSupportKZeroExternalProduct
        (compactSupportKZeroOpenExtension (interior N) isOpen_interior
          (compactSupportKZeroHomeomorph eA uA))
        (compactSupportKZeroOpenExtension (interior O) isOpen_interior
          (compactSupportKZeroHomeomorph eB uB))
    rw [← pushW, ← hP, hopen, hpI]
    have hproduct := compactSupportKZeroExternalProduct_openPushforward
      jA hjA jB hjB (compactSupportKZeroHomeomorph eA uA)
        (compactSupportKZeroHomeomorph eB uB)
    rw [pushN, pushO] at hproduct
    exact hproduct
  exact closeProductWindows a b c N O hN hO haN hbO hc hwindowMap hrelativeWindow

end AtiyahSinger.ComplexBundle
