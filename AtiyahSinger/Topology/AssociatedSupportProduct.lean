/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.AssociatedBundleProduct
public import AtiyahSinger.Topology.AssociatedSupportKZero
public import AtiyahSinger.Topology.EquivariantKExternalProduct

/-!
# Associated descent of the equivariant external product

Public module ID: M1552.

The associated quotient of X times Y maps into the product of the two associated
spaces by retaining the same principal representative. Its image is the closed
fiber product over B. The existing equivariant external product descends to the
proper pullback of the ordinary external product along this exact map.

Sources: SG III.13, pp.251--252, and Appendix C.1; KA II.5.21--5.22 for the
graded product. The exact representative comparison on the associated fiber
product is a supplementary argument. Compact G supplies the invariant cutoffs
in the existing equivariant product. Compact Hausdorff B gives compact descended
controls. The individual bundle projections need not be proper. This is a
topological product comparison, not the sphere-bundle analytic index formula.
The explicit same-representative bundle comparisons and the original support-product
compatibility are proved below.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped TensorProduct

attribute [local instance] associatedEquivariantFiberAddCommGroup
  associatedEquivariantFiberModule associatedEquivariantTotalTopology
  isFiniteRank_associatedEquivariant tensorTopology isFiniteRank_tensor isFiniteRank_pullback
  sumTopology isFiniteRank_sum

variable {G P B X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace P] [TopologicalSpace B]
  [MulAction Gᵐᵒᵖ P] [ContinuousSMul Gᵐᵒᵖ P] {projection : P → B}
  [CompactSpace B] [T2Space B]
  [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
  [LocallyCompactSpace X] [T2Space X]
  [TopologicalSpace Y] [MulAction G Y] [ContinuousSMul G Y]
  [LocallyCompactSpace Y] [T2Space Y]

omit [CompactSpace G] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace Y] [T2Space Y] in
/-- The associated bundle of an equivariant pullback is the original pullback of the
associated bundle, with its map evaluated at the same principal representative. -/
theorem exists_associatedEquivariantFiber_pullback_iso {X : Type*} [TopologicalSpace X]
    [MulAction G X] [ContinuousSMul G X]
    (hP : IsPrincipalBundle G projection) (f : C(X, Y))
    (heq : ∀ (g : G) (x : X), f (g • x) = g • f x) (E : Y → Type)
    [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [TopologicalSpace (Bundle.TotalSpace Unit E)] [IsFiniteRank E]
    (σ : EquivariantStructure G E) :
    let q := associatedBundleMap (P := P) f heq
    letI := isFiniteRank_pullback (E := E) f
    letI := associatedEquivariantFiberAddCommGroup hP σ
    letI := associatedEquivariantFiberModule hP σ
    letI := associatedEquivariantTotalTopology hP σ
    letI := associatedEquivariantFiberAddCommGroup hP (σ.pullback f heq)
    letI := associatedEquivariantFiberModule hP (σ.pullback f heq)
    letI := associatedEquivariantTotalTopology hP (σ.pullback f heq)
    ∃ u : Iso (AssociatedEquivariantFiber hP (σ.pullback f heq))
        ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
          (AssociatedEquivariantFiber hP σ)),
      ∀ (p : P) (x : X) {z : AssociatedBundle G P X}
        (hz : associatedBundleMk G P X p x = z) (v : E (f x)),
        u.linearEquiv z
            (associatedEquivariantFiberMk hP (σ.pullback f heq) p x hz v) =
          associatedEquivariantFiberMk hP σ p (f x) (congrArg q hz) v := by
  let q := associatedBundleMap (P := P) f heq
  let := isFiniteRank_pullback (E := E) f
  let := associatedEquivariantFiberAddCommGroup hP σ
  let := associatedEquivariantFiberModule hP σ
  let := associatedEquivariantTotalTopology hP σ
  let := associatedEquivariantFiberAddCommGroup hP (σ.pullback f heq)
  let := associatedEquivariantFiberModule hP (σ.pullback f heq)
  let := associatedEquivariantTotalTopology hP (σ.pullback f heq)
  let := isFiniteRank_associatedEquivariant hP σ
  let := isFiniteRank_associatedEquivariant hP (σ.pullback f heq)
  let := isFiniteRank_pullback (E := AssociatedEquivariantFiber hP σ) q
  let ρ := σ.pullback f heq
  let : MulAction G (Bundle.TotalSpace Unit E) := σ.toMulAction
  let : MulAction G (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) := ρ.toMulAction
  let : ContinuousSMul G (Bundle.TotalSpace Unit E) := ⟨σ.continuous_action⟩
  let : ContinuousSMul G (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) :=
    ⟨ρ.continuous_action⟩
  have htotal (g : G) (w : Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E)) :
      Bundle.Pullback.lift f (g • w) = g • Bundle.Pullback.lift f w := by
    have hcast (a b : Y) (hab : a = b) (L : E (f w.proj) →ₗ[ℂ] E b) :
        (⟨a, (Eq.mpr (congrArg (fun x ↦ E (f w.proj) →ₗ[ℂ] E x) hab) L) w.snd⟩ :
          Bundle.TotalSpace Unit E) = ⟨b, L w.snd⟩ := by
      subst b
      rfl
    exact hcast (f (g • w.proj)) (g • f w.proj) (heq g w.proj)
      (σ.linearMap g (f w.proj))
  let Q := associatedBundleMap (P := P)
    ⟨Bundle.Pullback.lift f, Pullback.continuous_lift Unit E f⟩ htotal
  have hproj (w : AssociatedBundle G P (Bundle.TotalSpace Unit ((f : X → Y) *ᵖ E))) :
      associatedEquivariantProjection σ (Q w) =
        q (associatedEquivariantProjection ρ w) := by
    induction w using Quotient.inductionOn with
    | h w => rfl
  let fiberMap (z : AssociatedBundle G P X) (v : AssociatedEquivariantFiber hP ρ z) :
      AssociatedEquivariantFiber hP σ (q z) :=
    ⟨Q v.val, (hproj v.val).trans (congrArg q v.property)⟩
  have hformula (p : P) (x : X) {z : AssociatedBundle G P X}
      (hz : associatedBundleMk G P X p x = z) (v : E (f x)) :
      fiberMap z (associatedEquivariantFiberMk hP ρ p x hz v) =
        associatedEquivariantFiberMk hP σ p (f x) (congrArg q hz) v := rfl
  -- Common original representatives prove linearity and bijectivity of this exact map.
  have hlinear (z : AssociatedBundle G P X) : IsLinearMap ℂ (fiberMap z) := by
    let p := (Quotient.out z).1
    let x := (Quotient.out z).2
    have hz : associatedBundleMk G P X p x = z := Quotient.out_eq z
    have hE := associatedEquivariantFiberMk_isLinear hP ρ p x hz
    have hF := associatedEquivariantFiberMk_isLinear hP σ p (f x) (congrArg q hz)
    have hsurj := (associatedEquivariantFiberMk_bijective hP ρ p x hz).2
    constructor
    · intro u v
      obtain ⟨u₀, rfl⟩ := hsurj u
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_add]
      exact (hformula p x hz (u₀ + v₀)).trans ((hF.map_add u₀ v₀).trans
        (congrArg₂ (· + ·) (hformula p x hz u₀).symm (hformula p x hz v₀).symm))
    · intro c v
      obtain ⟨v₀, rfl⟩ := hsurj v
      rw [← hE.map_smul]
      exact (hformula p x hz (c • v₀)).trans ((hF.map_smul c v₀).trans
        (congrArg (c • ·) (hformula p x hz v₀).symm))
  have hbij (z : AssociatedBundle G P X) : Function.Bijective (fiberMap z) := by
    let p := (Quotient.out z).1
    let x := (Quotient.out z).2
    have hz : associatedBundleMk G P X p x = z := Quotient.out_eq z
    have hE := associatedEquivariantFiberMk_bijective hP ρ p x hz
    have hF := associatedEquivariantFiberMk_bijective hP σ p (f x) (congrArg q hz)
    constructor
    · intro u v huv
      obtain ⟨u₀, rfl⟩ := hE.2 u
      obtain ⟨v₀, rfl⟩ := hE.2 v
      have hv := (hformula p x hz u₀).symm.trans (huv.trans (hformula p x hz v₀))
      exact congrArg (associatedEquivariantFiberMk hP ρ p x hz) (hF.1 hv)
    · intro v
      obtain ⟨v₀, rfl⟩ := hF.2 v
      exact ⟨associatedEquivariantFiberMk hP ρ p x hz v₀, hformula p x hz v₀⟩
  -- Native pullback topology records the base and the original associated total vector.
  let HE := associatedEquivariantTotalHomeomorph hP ρ
  let HF := associatedEquivariantTotalHomeomorph hP σ
  have hcontinuous : Continuous
      (fun w : Bundle.TotalSpace Unit (AssociatedEquivariantFiber hP ρ) ↦
        (⟨w.proj, fiberMap w.proj w.snd⟩ : Bundle.TotalSpace Unit
          ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
            (AssociatedEquivariantFiber hP σ)))) := by
    apply (inducing_pullbackTotalSpaceEmbedding Unit
      (AssociatedEquivariantFiber hP σ) q).continuous_iff.mpr
    apply (continuous_proj (E := AssociatedEquivariantFiber hP ρ)).prodMk
    have hc := HF.symm.continuous_toFun.comp (Q.continuous.comp HE.continuous_toFun)
    apply hc.congr
    intro w
    apply HF.injective
    exact HF.apply_symm_apply (Q w.snd.val)
  let u : Hom (AssociatedEquivariantFiber hP ρ)
      ((q : AssociatedBundle G P X → AssociatedBundle G P Y) *ᵖ
        (AssociatedEquivariantFiber hP σ)) :=
    { linearMap z := IsLinearMap.mk' (fiberMap z) (hlinear z)
      continuous_total := hcontinuous }
  exact ⟨u.toIso hbij, hformula⟩

omit [CompactSpace G] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace Y] [T2Space Y] in
/-- Associated descent preserves direct sums with the original common representative
in both summands and the original quotient and sum topologies. -/
theorem exists_associatedEquivariantFiber_sum_iso (hP : IsPrincipalBundle G projection)
    (E F : Y → Type)
    [∀ y, AddCommGroup (E y)] [∀ y, Module ℂ (E y)]
    [∀ y, AddCommGroup (F y)] [∀ y, Module ℂ (F y)]
    [TopologicalSpace (TotalSpace Unit E)] [TopologicalSpace (TotalSpace Unit F)]
    [IsFiniteRank E] [IsFiniteRank F]
    (σ : EquivariantStructure G E) (τ : EquivariantStructure G F) :
    let := sumTopology (E := E) (F := F)
    let := isFiniteRank_sum (E := E) (F := F)
    let := sumTopology (E := AssociatedEquivariantFiber hP σ)
      (F := AssociatedEquivariantFiber hP τ)
    let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP σ)
      (F := AssociatedEquivariantFiber hP τ)
    ∃ u : Iso (AssociatedEquivariantFiber hP (σ.sum τ))
        (AssociatedEquivariantFiber hP σ ×ᵇ AssociatedEquivariantFiber hP τ),
      ∀ (p : P) (y : Y) {z : AssociatedBundle G P Y} (hz : associatedBundleMk G P Y p y = z)
        (w : E y × F y),
        u.linearEquiv z (associatedEquivariantFiberMk hP (σ.sum τ) p y hz w) =
          (associatedEquivariantFiberMk hP σ p y hz w.1,
            associatedEquivariantFiberMk hP τ p y hz w.2) := by
  let := sumTopology (E := E) (F := F)
  let := isFiniteRank_sum (E := E) (F := F)
  let := sumTopology (E := AssociatedEquivariantFiber hP σ)
    (F := AssociatedEquivariantFiber hP τ)
  let := isFiniteRank_sum (E := AssociatedEquivariantFiber hP σ)
    (F := AssociatedEquivariantFiber hP τ)
  let l := associatedEquivariantHom hP (σ.sum τ) σ
    (sumFst (E := E) (F := F)) (fun _ _ _ ↦ rfl)
  let r := associatedEquivariantHom hP (σ.sum τ) τ
    (sumSnd (E := E) (F := F)) (fun _ _ _ ↦ rfl)
  let a : Hom (AssociatedEquivariantFiber hP (σ.sum τ))
      (AssociatedEquivariantFiber hP σ ×ᵇ AssociatedEquivariantFiber hP τ) :=
    { linearMap z := (l.linearMap z).prod (r.linearMap z)
      continuous_total := continuous_induced_rng.mpr
        (l.continuous_total.prodMk r.continuous_total) }
  have hformula (p : P) (y : Y) {z : AssociatedBundle G P Y}
      (hz : associatedBundleMk G P Y p y = z) (w : E y × F y) :
      a.linearMap z (associatedEquivariantFiberMk hP (σ.sum τ) p y hz w) =
        (associatedEquivariantFiberMk hP σ p y hz w.1,
          associatedEquivariantFiberMk hP τ p y hz w.2) := by
    exact Prod.ext
      (associatedEquivariantHom_apply hP (σ.sum τ) σ
        (sumFst (E := E) (F := F)) (fun _ _ _ ↦ rfl) p y hz w)
      (associatedEquivariantHom_apply hP (σ.sum τ) τ
        (sumSnd (E := E) (F := F)) (fun _ _ _ ↦ rfl) p y hz w)
  have hbij (z : AssociatedBundle G P Y) : Function.Bijective (a.linearMap z) := by
    let p := (Quotient.out z).1
    let y := (Quotient.out z).2
    have hz : associatedBundleMk G P Y p y = z := Quotient.out_eq z
    have hsource := associatedEquivariantFiberMk_bijective hP (σ.sum τ) p y hz
    have hleft := associatedEquivariantFiberMk_bijective hP σ p y hz
    have hright := associatedEquivariantFiberMk_bijective hP τ p y hz
    constructor
    · intro v w hvw
      obtain ⟨v₀, rfl⟩ := hsource.2 v
      obtain ⟨w₀, rfl⟩ := hsource.2 w
      rw [hformula, hformula] at hvw
      exact congrArg (associatedEquivariantFiberMk hP (σ.sum τ) p y hz)
        (Prod.ext (hleft.1 (congrArg Prod.fst hvw))
          (hright.1 (congrArg Prod.snd hvw)))
    · rintro ⟨v, w⟩
      obtain ⟨v₀, rfl⟩ := hleft.2 v
      obtain ⟨w₀, rfl⟩ := hright.2 w
      exact ⟨associatedEquivariantFiberMk hP (σ.sum τ) p y hz (v₀, w₀),
        hformula p y hz (v₀, w₀)⟩
  exact ⟨a.toIso hbij, hformula⟩

omit [CompactSpace G] [CompactSpace B] [T2Space B]
  [LocallyCompactSpace Y] [T2Space Y] in
set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
-- Retain the original quotient and tensor topologies through the finite-rank inverse.
/-- Associated descent preserves tensor products using the same principal representative
in both factors, with the original diagonal action and tensor topology. -/
theorem exists_associatedEquivariantFiber_tensor_iso (hP : IsPrincipalBundle G projection)
    (J K : FiniteBundle Y) (σ : EquivariantStructure G J.Fiber)
    (τ : EquivariantStructure G K.Fiber) :
    ∃ e : Iso (AssociatedEquivariantFiber hP (σ.tensor τ))
        (fun z ↦ AssociatedEquivariantFiber hP σ z ⊗[ℂ]
          AssociatedEquivariantFiber hP τ z),
      ∀ (p : P) (y : Y) {z : AssociatedBundle G P Y}
        (hz : associatedBundleMk G P Y p y = z) (u : J.Fiber y) (v : K.Fiber y),
        e.linearEquiv z (associatedEquivariantFiberMk hP (σ.tensor τ) p y hz (u ⊗ₜ[ℂ] v)) =
          associatedEquivariantFiberMk hP σ p y hz u ⊗ₜ[ℂ]
            associatedEquivariantFiberMk hP τ p y hz v := by
  classical
  let Z := AssociatedBundle G P Y
  let A := AssociatedEquivariantFiber hP σ
  let B := AssociatedEquivariantFiber hP τ
  let T := AssociatedEquivariantFiber hP (σ.tensor τ)
  let mkJ (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
    LinearEquiv.ofBijective
      (IsLinearMap.mk' (associatedEquivariantFiberMk hP σ p y hz)
        (associatedEquivariantFiberMk_isLinear hP σ p y hz))
      (associatedEquivariantFiberMk_bijective hP σ p y hz)
  let mkK (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
    LinearEquiv.ofBijective
      (IsLinearMap.mk' (associatedEquivariantFiberMk hP τ p y hz)
        (associatedEquivariantFiberMk_isLinear hP τ p y hz))
      (associatedEquivariantFiberMk_bijective hP τ p y hz)
  let mkT (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z) :=
    LinearEquiv.ofBijective
      (IsLinearMap.mk' (associatedEquivariantFiberMk hP (σ.tensor τ) p y hz)
        (associatedEquivariantFiberMk_isLinear hP (σ.tensor τ) p y hz))
      (associatedEquivariantFiberMk_bijective hP (σ.tensor τ) p y hz)
  let c (z : Z) : T z ≃ₗ[ℂ] A z ⊗[ℂ] B z :=
    (mkT (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z)).symm.trans
      (TensorProduct.congr
        (mkJ (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z))
        (mkK (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z)))
  -- One orbit relation transports both factors and the common principal point.
  have formula (p : P) (y : Y) {z : Z} (hz : associatedBundleMk G P Y p y = z)
      (u : J.Fiber y) (v : K.Fiber y) :
      c z (associatedEquivariantFiberMk hP (σ.tensor τ) p y hz (u ⊗ₜ[ℂ] v)) =
        associatedEquivariantFiberMk hP σ p y hz u ⊗ₜ[ℂ]
          associatedEquivariantFiberMk hP τ p y hz v := by
    let : MulAction G (TotalSpace Unit J.Fiber) := σ.toMulAction
    let : MulAction G (TotalSpace Unit K.Fiber) := τ.toMulAction
    let : MulAction G (TotalSpace Unit (J.tensor K).Fiber) := (σ.tensor τ).toMulAction
    obtain ⟨g, hg⟩ := Quotient.exact (hz.trans (Quotient.out_eq z).symm)
    have hp : (Quotient.out z).1 = MulOpposite.op g • p := congrArg Prod.fst hg
    have hy : g⁻¹ • y = (Quotient.out z).2 := (congrArg Prod.snd hg).symm
    let u' := cast (congrArg J.Fiber hy) (σ.linearMap g⁻¹ y u)
    let v' := cast (congrArg K.Fiber hy) (τ.linearMap g⁻¹ y v)
    have castTensor {y₀ y₁ : Y} (h : y₀ = y₁) (u : J.Fiber y₀) (v : K.Fiber y₀) :
        (⟨y₁, cast (congrArg J.Fiber h) u ⊗ₜ[ℂ] cast (congrArg K.Fiber h) v⟩ :
          TotalSpace Unit (J.tensor K).Fiber) = ⟨y₀, u ⊗ₜ[ℂ] v⟩ := by
      subst y₁
      rfl
    have hT : associatedEquivariantFiberMk hP (σ.tensor τ) p y hz (u ⊗ₜ[ℂ] v) =
        mkT (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z) (u' ⊗ₜ[ℂ] v') := by
      apply Subtype.ext
      apply Quotient.sound
      refine ⟨g, Prod.ext hp ?_⟩
      change (⟨(Quotient.out z).2, u' ⊗ₜ[ℂ] v'⟩ : TotalSpace Unit (J.tensor K).Fiber) =
        ⟨g⁻¹ • y, TensorProduct.map (σ.linearMap g⁻¹ y) (τ.linearMap g⁻¹ y)
          (u ⊗ₜ[ℂ] v)⟩
      rw [TensorProduct.map_tmul]
      exact castTensor hy _ _
    have hJ : associatedEquivariantFiberMk hP σ p y hz u =
        mkJ (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z) u' := by
      apply Subtype.ext
      apply Quotient.sound
      exact ⟨g, Prod.ext hp (TotalSpace.mk_cast (F := Unit) (E := J.Fiber)
        hy (σ.linearMap g⁻¹ y u))⟩
    have hK : associatedEquivariantFiberMk hP τ p y hz v =
        mkK (Quotient.out z).1 (Quotient.out z).2 (Quotient.out_eq z) v' := by
      apply Subtype.ext
      apply Quotient.sound
      exact ⟨g, Prod.ext hp (TotalSpace.mk_cast (F := Unit) (E := K.Fiber)
        hy (τ.linearMap g⁻¹ y v))⟩
    rw [hT, hJ, hK]
    change TensorProduct.congr _ _ ((mkT _ _ _).symm ((mkT _ _ _) _)) = _
    rw [LinearEquiv.symm_apply_apply, TensorProduct.congr_tmul]
  -- Form the continuous tensor map before descending through the original quotient.
  let s : C(P × Y, Y) := ContinuousMap.snd
  let m : C(P × Y, Z) := ⟨fun z ↦ associatedBundleMk G P Y z.1 z.2, continuous_quot_mk⟩
  have liftHom (L : FiniteBundle Y) (ρ : EquivariantStructure G L.Fiber) :
      ∃ u : Hom ((s : P × Y → Y) *ᵖ L.Fiber)
          ((m : P × Y → Z) *ᵖ (AssociatedEquivariantFiber hP ρ)),
        ∀ z w, u.linearMap z w = associatedEquivariantFiberMk hP ρ z.1 z.2 rfl w := by
    refine ⟨
      { linearMap z := IsLinearMap.mk' _
          (associatedEquivariantFiberMk_isLinear hP ρ z.1 z.2 rfl)
        continuous_total := ?_ }, fun _ _ ↦ rfl⟩
    let D := TotalSpace Unit ((s : P × Y → Y) *ᵖ L.Fiber)
    have hb : Continuous (fun z : D ↦ z.proj) := Pullback.continuous_proj Unit _ s
    have hl : Continuous (fun z : D ↦ (⟨z.proj.2, z.snd⟩ : TotalSpace Unit L.Fiber)) :=
      Pullback.continuous_lift Unit _ s
    have hc := (associatedEquivariantTotalHomeomorph hP ρ).symm.continuous.comp
      (continuous_quot_mk.comp (hb.fst.prodMk hl))
    rw [(inducing_pullbackTotalSpaceEmbedding Unit
      (AssociatedEquivariantFiber hP ρ) (m : P × Y → Z)).continuous_iff]
    exact hb.prodMk hc
  obtain ⟨uJ, huJ⟩ := liftHom J σ
  obtain ⟨uK, huK⟩ := liftHom K τ
  let liftMap := (pullbackTensorIso (E := A) (F := B) m).symm.toHom.comp
    ((uJ.tensor uK).comp
      (pullbackTensorIso (E := J.Fiber) (F := K.Fiber) s).toHom)
  have liftFormula (p : P) (y : Y) (t : J.Fiber y ⊗[ℂ] K.Fiber y) :
      liftMap.linearMap (p, y) t = c (associatedBundleMk G P Y p y)
        (associatedEquivariantFiberMk hP (σ.tensor τ) p y rfl t) := by
    change liftMap.linearMap (p, y) t = c (associatedBundleMk G P Y p y) (mkT p y rfl t)
    induction t using TensorProduct.inductionOn with
    | tmul u v =>
      change _ = c _ (associatedEquivariantFiberMk hP (σ.tensor τ) p y rfl (u ⊗ₜ[ℂ] v))
      rw [formula]
      change (TensorProduct.map (uJ.linearMap (p, y)) (uK.linearMap (p, y)))
        (u ⊗ₜ[ℂ] v) = _
      rw [TensorProduct.map_tmul, huJ, huK]
    | add t w ht hw => simp only [map_add, ht, hw]
  have hc : Continuous (fun d : P × TotalSpace Unit (J.tensor K).Fiber ↦
      (⟨associatedBundleMk G P Y d.1 d.2.proj,
        c (associatedBundleMk G P Y d.1 d.2.proj)
          (associatedEquivariantFiberMk hP (σ.tensor τ) d.1 d.2.proj rfl d.2.snd)⟩ :
        TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] B z))) := by
    let D := P × TotalSpace Unit (J.tensor K).Fiber
    let intoPullback (d : D) : TotalSpace Unit ((s : P × Y → Y) *ᵖ (J.tensor K).Fiber) :=
      ⟨(d.1, d.2.proj), d.2.snd⟩
    have hi : Continuous intoPullback := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (J.tensor K).Fiber
        (s : P × Y → Y)).continuous_iff]
      exact (continuous_fst.prodMk ((continuous_proj (E := (J.tensor K).Fiber)).comp
        continuous_snd)).prodMk continuous_snd
    have hl := (Pullback.continuous_lift Unit (fun z : Z ↦ A z ⊗[ℂ] B z)
      (m : P × Y → Z)).comp (liftMap.continuous_total.comp hi)
    apply hl.congr
    intro d
    exact congrArg (fun w ↦ (⟨associatedBundleMk G P Y d.1 d.2.proj, w⟩ :
      TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] B z))) (liftFormula d.1 d.2.proj d.2.snd)
  let a : Hom T (fun z : Z ↦ A z ⊗[ℂ] B z) :=
    { linearMap z := (c z).toLinearMap
      continuous_total := by
        let : MulAction G (TotalSpace Unit (J.tensor K).Fiber) := (σ.tensor τ).toMulAction
        let : ContinuousSMul G (TotalSpace Unit (J.tensor K).Fiber) :=
          ⟨(σ.tensor τ).continuous_action⟩
        let H := associatedEquivariantTotalHomeomorph hP (σ.tensor τ)
        have hquot : Continuous (fun z : AssociatedBundle G P
            (TotalSpace Unit (J.tensor K).Fiber) ↦
            (⟨(H.symm z).proj, c (H.symm z).proj (H.symm z).snd⟩ :
              TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] B z))) := by
          apply isQuotientMap_quotient_mk'.continuous_iff.mpr
          exact hc
        apply (hquot.comp H.continuous).congr
        intro z
        exact congrArg (fun w : TotalSpace Unit T ↦ (⟨w.proj, c w.proj w.snd⟩ :
          TotalSpace Unit (fun z : Z ↦ A z ⊗[ℂ] B z))) (H.symm_apply_apply z) }
  exact ⟨a.toIso (fun z ↦ (c z).bijective), formula⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3600000 in
-- Keep the exact quotient, pullback and small-model structures in the dependent boundary square.
/-- The equivariant product descends to the ordinary product restricted to the same-base locus. -/
theorem associatedSupportKZero_externalProduct (hP : IsPrincipalBundle G projection)
    (a : EquivariantSupportTripleKZero G X) (b : EquivariantSupportTripleKZero G Y) :
    letI := associatedBundle_t2Space (Y := X) hP
    letI := associatedBundle_locallyCompactSpace (Y := X) hP
    letI := associatedBundle_t2Space (Y := Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := Y) hP
    letI := associatedBundle_t2Space (Y := X × Y) hP
    letI := associatedBundle_locallyCompactSpace (Y := X × Y) hP
    associatedSupportKZero hP (equivariantSupportKZeroExternalProduct a b) =
      compactSupportKZeroPullback (associatedBundleProdMap G P X Y)
        (associatedBundleProdMap_properties hP).1.isProperMap
        (compactSupportKZeroExternalProduct
          (associatedSupportKZero hP a) (associatedSupportKZero hP b)) := by
  /- Compare the native associated bundles with the ordinary product bundles over
  the same principal representative. Descend the specified invariant cutoffs,
  then check their four signed reciprocal blocks under those same isomorphisms.
  The exact compact controls agree under the proper paired map, so conjugation
  and proper pullback identify the classes. Actual triple representatives cover
  arbitrary input classes by the existing presentation's surjectivity. -/
  classical
  let := associatedBundle_t2Space (Y := X) hP
  let := associatedBundle_locallyCompactSpace (Y := X) hP
  let := associatedBundle_t2Space (Y := Y) hP
  let := associatedBundle_locallyCompactSpace (Y := Y) hP
  let := associatedBundle_t2Space (Y := X × Y) hP
  let := associatedBundle_locallyCompactSpace (Y := X × Y) hP
  let ZX := AssociatedBundle G P X
  let ZY := AssociatedBundle G P Y
  let Z := AssociatedBundle G P (X × Y)
  let q := associatedBundleProdMap G P X Y
  have hq : IsProperMap q := (associatedBundleProdMap_properties hP).1.isProperMap
  -- Bundle, cutoff and boundary comparisons retain the original base universes.
  have pairComparison
      (J : FiniteBundle X) (K : FiniteBundle Y)
      (σ : EquivariantStructure G J.Fiber) (τ : EquivariantStructure G K.Fiber) :
      let q := associatedBundleProdMap G P X Y
      let A := smallBundle (AssociatedEquivariantFiber hP σ)
      let B := smallBundle (AssociatedEquivariantFiber hP τ)
      let S := (σ.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
        (τ.pullback ContinuousMap.snd (fun _ _ ↦ rfl))
      ∃ e : Iso (AssociatedEquivariantFiber hP S)
          (((A.pullback ContinuousMap.fst).tensor (B.pullback ContinuousMap.snd)).pullback q).Fiber,
        ∀ (p : P) (x : X) (y : Y) {z : AssociatedBundle G P (X × Y)}
          (hz : associatedBundleMk G P (X × Y) p (x, y) = z)
          (u : J.Fiber x) (v : K.Fiber y),
          e.linearEquiv z (associatedEquivariantFiberMk hP S p (x, y) hz (u ⊗ₜ[ℂ] v)) =
            (smallBundleIso (AssociatedEquivariantFiber hP σ)).linearEquiv (q z).1
              (associatedEquivariantFiberMk hP σ p x (congrArg (fun z ↦ (q z).1) hz) u) ⊗ₜ[ℂ]
            (smallBundleIso (AssociatedEquivariantFiber hP τ)).linearEquiv (q z).2
              (associatedEquivariantFiberMk hP τ p y (congrArg (fun z ↦ (q z).2) hz) v) := by
    let q := associatedBundleProdMap G P X Y
    let A := smallBundle (AssociatedEquivariantFiber hP σ)
    let B := smallBundle (AssociatedEquivariantFiber hP τ)
    let σf := σ.pullback (ContinuousMap.fst : C(X × Y, X)) (fun _ _ ↦ rfl)
    let τs := τ.pullback (ContinuousMap.snd : C(X × Y, Y)) (fun _ _ ↦ rfl)
    let qx := associatedBundleMap (G := G) (P := P) (ContinuousMap.fst : C(X × Y, X))
      (fun _ _ ↦ rfl)
    let qy := associatedBundleMap (G := G) (P := P) (ContinuousMap.snd : C(X × Y, Y))
      (fun _ _ ↦ rfl)
    obtain ⟨c, hc⟩ := exists_associatedEquivariantFiber_tensor_iso hP
      (J.pullback ContinuousMap.fst) (K.pullback ContinuousMap.snd) σf τs
    obtain ⟨l, hl⟩ := exists_associatedEquivariantFiber_pullback_iso hP
      (ContinuousMap.fst : C(X × Y, X)) (fun _ _ ↦ rfl) J.Fiber σ
    obtain ⟨r, hr⟩ := exists_associatedEquivariantFiber_pullback_iso hP
      (ContinuousMap.snd : C(X × Y, Y)) (fun _ _ ↦ rfl) K.Fiber τ
    let l' := (l.trans ((smallBundleIso (AssociatedEquivariantFiber hP σ)).pullback qx)).trans
      (pullbackCompIso (E := A.Fiber) ContinuousMap.fst q).symm
    let r' := (r.trans ((smallBundleIso (AssociatedEquivariantFiber hP τ)).pullback qy)).trans
      (pullbackCompIso (E := B.Fiber) ContinuousMap.snd q).symm
    let e := (c.trans (l'.tensor r')).trans
      (pullbackTensorIso (E := (A.pullback ContinuousMap.fst).Fiber)
        (F := (B.pullback ContinuousMap.snd).Fiber) q).symm
    refine ⟨e, ?_⟩
    intro p x y z hz u v
    change TensorProduct.congr (l'.linearEquiv z) (r'.linearEquiv z)
      (c.linearEquiv z (associatedEquivariantFiberMk hP (σf.tensor τs) p (x,y) hz
        (u ⊗ₜ[ℂ] v))) = _
    rw [hc, TensorProduct.congr_tmul]
    have hl' : l'.linearEquiv z (associatedEquivariantFiberMk hP σf p (x, y) hz u) =
        (smallBundleIso (AssociatedEquivariantFiber hP σ)).linearEquiv (qx z)
          (associatedEquivariantFiberMk hP σ p x (congrArg qx hz) u) := by
      change ((pullbackCompIso (E := A.Fiber) ContinuousMap.fst q).linearEquiv z).symm
        ((smallBundleIso (AssociatedEquivariantFiber hP σ)).linearEquiv (qx z)
          (l.linearEquiv z (associatedEquivariantFiberMk hP σf p (x, y) hz u))) = _
      apply ((pullbackCompIso (E := A.Fiber) ContinuousMap.fst q).linearEquiv z).injective
      erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, hl]
      rfl
    have hr' : r'.linearEquiv z (associatedEquivariantFiberMk hP τs p (x, y) hz v) =
        (smallBundleIso (AssociatedEquivariantFiber hP τ)).linearEquiv (qy z)
          (associatedEquivariantFiberMk hP τ p y (congrArg qy hz) v) := by
      change ((pullbackCompIso (E := B.Fiber) ContinuousMap.snd q).linearEquiv z).symm
        ((smallBundleIso (AssociatedEquivariantFiber hP τ)).linearEquiv (qy z)
          (r.linearEquiv z (associatedEquivariantFiberMk hP τs p (x, y) hz v))) = _
      apply ((pullbackCompIso (E := B.Fiber) ContinuousMap.snd q).linearEquiv z).injective
      erw [LinearEquiv.apply_symm_apply, pullbackCompIso_apply, hr]
      rfl
    rw [hl', hr']
    rfl
  have cutoffComparisonX
      (ρ : C(X, unitInterval)) (hρ : ∀ (g : G) (x : X), ρ (g • x) = ρ x)
      (U L : Set X) (hU : IsOpen U)
      (hUinv : ∀ (g : G) (x : X), g • x ∈ U ↔ x ∈ U)
      (hLinv : ∀ (g : G) (x : X), g • x ∈ L ↔ x ∈ L)
      (hzero : ∀ x ∈ U, ρ x = 0) (hone : ∀ x ∉ L, ρ x = 1) :
      ∃ r : C(AssociatedBundle G P X, unitInterval),
        (∀ p x, r (associatedBundleMk G P X p x) = ρ x) ∧
        IsOpen (associatedControl G P X U) ∧
        (∀ z ∈ associatedControl G P X U, r z = 0) ∧
        ∀ z ∉ associatedControl G P X L, r z = 1 := by
    let r : C(AssociatedBundle G P X, unitInterval) :=
      { toFun := Quotient.lift (fun z : P × X ↦ ρ z.2) (by
          rintro x y ⟨g, rfl⟩
          exact (hρ g⁻¹ x.2).symm)
        continuous_toFun := continuous_quot_lift _ (ρ.continuous.comp continuous_snd) }
    have hopen : IsOpen (associatedControl G P X U) := by
      apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
      have hpre : (@Quotient.mk' (P × X) (associatedBundleSetoid G P X)) ⁻¹'
          associatedControl G P X U = Set.univ ×ˢ U := by
        ext px
        exact associatedControl_mk_mem_iff U hUinv px.1 px.2 |>.trans
          (and_iff_right (Set.mem_univ px.1)).symm
      rw [hpre]
      exact isOpen_univ.prod hU
    refine ⟨r, fun _ _ ↦ rfl, hopen, ?_, ?_⟩
    · intro z hz
      induction z using Quotient.inductionOn with
      | h px => exact hzero px.2 ((associatedControl_mk_mem_iff U hUinv px.1 px.2).mp hz)
    · intro z hz
      induction z using Quotient.inductionOn with
      | h px => exact hone px.2 (fun hx ↦ hz
          ((associatedControl_mk_mem_iff L hLinv px.1 px.2).mpr hx))
  -- Descend the second cutoff on its original base universe as well.
  have cutoffComparisonY
      (ρ : C(Y, unitInterval)) (hρ : ∀ (g : G) (x : Y), ρ (g • x) = ρ x)
      (U L : Set Y) (hU : IsOpen U)
      (hUinv : ∀ (g : G) (x : Y), g • x ∈ U ↔ x ∈ U)
      (hLinv : ∀ (g : G) (x : Y), g • x ∈ L ↔ x ∈ L)
      (hzero : ∀ x ∈ U, ρ x = 0) (hone : ∀ x ∉ L, ρ x = 1) :
      ∃ r : C(AssociatedBundle G P Y, unitInterval),
        (∀ p x, r (associatedBundleMk G P Y p x) = ρ x) ∧
        IsOpen (associatedControl G P Y U) ∧
        (∀ z ∈ associatedControl G P Y U, r z = 0) ∧
        ∀ z ∉ associatedControl G P Y L, r z = 1 := by
    let r : C(AssociatedBundle G P Y, unitInterval) :=
      { toFun := Quotient.lift (fun z : P × Y ↦ ρ z.2) (by
          rintro x y ⟨g, rfl⟩
          exact (hρ g⁻¹ x.2).symm)
        continuous_toFun := continuous_quot_lift _ (ρ.continuous.comp continuous_snd) }
    have hopen : IsOpen (associatedControl G P Y U) := by
      apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
      have hpre : (@Quotient.mk' (P × Y) (associatedBundleSetoid G P Y)) ⁻¹'
          associatedControl G P Y U = Set.univ ×ˢ U := by
        ext px
        exact associatedControl_mk_mem_iff U hUinv px.1 px.2 |>.trans
          (and_iff_right (Set.mem_univ px.1)).symm
      rw [hpre]
      exact isOpen_univ.prod hU
    refine ⟨r, fun _ _ ↦ rfl, hopen, ?_, ?_⟩
    · intro z hz
      induction z using Quotient.inductionOn with
      | h px => exact hzero px.2 ((associatedControl_mk_mem_iff U hUinv px.1 px.2).mp hz)
    · intro z hz
      induction z using Quotient.inductionOn with
      | h px => exact hone px.2 (fun hx ↦ hz
          ((associatedControl_mk_mem_iff L hLinv px.1 px.2).mpr hx))
  have cutoffSquareX
      (a : EquivariantSupportBundleTriple G X) (ρ : C(X, unitInterval))
      (r : C(AssociatedBundle G P X, unitInterval))
      (hr : ∀ p x, r (associatedBundleMk G P X p x) = ρ x) (p : P) (x : X)
      (mE : a.1.source.Fiber x ≃ₗ[ℂ]
        (smallBundle (AssociatedEquivariantFiber hP a.2.sourceAction)).Fiber
          (associatedBundleMk G P X p x))
      (mF : a.1.target.Fiber x ≃ₗ[ℂ]
        (smallBundle (AssociatedEquivariantFiber hP a.2.targetAction)).Fiber
          (associatedBundleMk G P X p x))
      (hmE : ∀ u, mE u =
        (smallBundleIso (AssociatedEquivariantFiber hP a.2.sourceAction)).linearEquiv _
          (associatedEquivariantFiberMk hP a.2.sourceAction p x rfl u))
      (hmF : ∀ v, mF v =
        (smallBundleIso (AssociatedEquivariantFiber hP a.2.targetAction)).linearEquiv _
          (associatedEquivariantFiberMk hP a.2.targetAction p x rfl v)) :
      let da := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
        a.2.isEquivariant
      let A := da.toSupportBundleTriple
      (∀ u, mF (a.1.datum.cutoffLinearMap ρ x u) =
        A.datum.cutoffLinearMap r (associatedBundleMk G P X p x) (mE u)) ∧
      (∀ v, mE (a.1.datum.inverse.cutoffLinearMap ρ x v) =
        A.datum.inverse.cutoffLinearMap r (associatedBundleMk G P X p x) (mF v)) := by
    let da := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
      a.2.isEquivariant
    let A := da.toSupportBundleTriple
    let z := associatedBundleMk G P X p x
    have hmem : z ∈ A.datum.control ↔ x ∈ a.1.datum.control :=
      associatedControl_mk_mem_iff a.1.datum.control a.2.isEquivariant.invariant_control p x
    change (∀ u, mF (a.1.datum.cutoffLinearMap ρ x u) = A.datum.cutoffLinearMap r z (mE u)) ∧
      (∀ v, mE (a.1.datum.inverse.cutoffLinearMap ρ x v) =
        A.datum.inverse.cutoffLinearMap r z (mF v))
    by_cases hx : x ∈ a.1.datum.control
    · have hz := hmem.mpr hx
      constructor <;> intro w <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_left hx, dite_eq_left hz, LinearMap.zero_apply, map_zero]
    · have hz : z ∉ A.datum.control := fun h ↦ hx (hmem.mp h)
      have boundary (u : a.1.source.Fiber x) :
          A.datum.boundary.linearEquiv ⟨z, hz⟩ (mE u) =
            mF (a.1.datum.boundary.linearEquiv ⟨x, hx⟩ u) := by
        rw [hmE, hmF]
        rw [da.toSupportBundleTriple_apply]
        exact congrArg ((smallBundleIso
          (AssociatedEquivariantFiber hP a.2.targetAction)).linearEquiv z)
            (associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction a.2.targetAction
              a.2.isEquivariant p ⟨x, hx⟩ u)
      have inverse (v : a.1.target.Fiber x) :
          A.datum.inverse.boundary.linearEquiv ⟨z, hz⟩ (mF v) =
            mE (a.1.datum.inverse.boundary.linearEquiv ⟨x, hx⟩ v) := by
        apply (A.datum.boundary.linearEquiv ⟨z, hz⟩).injective
        change A.datum.boundary.linearEquiv ⟨z, hz⟩
          ((A.datum.boundary.linearEquiv ⟨z, hz⟩).symm (mF v)) =
          A.datum.boundary.linearEquiv ⟨z, hz⟩
            (mE ((a.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm v))
        rw [LinearEquiv.apply_symm_apply, boundary, LinearEquiv.apply_symm_apply]
      have hscalar : r z = ρ x := hr p x
      constructor
      · intro u
        simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx, dite_eq_right hz]
        change mF (((ρ x : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv ⟨x, hx⟩ u) =
          ((r z : ℝ) : ℂ) • A.datum.boundary.linearEquiv ⟨z, hz⟩ (mE u)
        rw [map_smul, boundary, hscalar]
      · intro v
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hx, dite_eq_right hz]
        change mE (((ρ x : ℝ) : ℂ) • a.1.datum.inverse.boundary.linearEquiv ⟨x, hx⟩ v) =
          ((r z : ℝ) : ℂ) • A.datum.inverse.boundary.linearEquiv ⟨z, hz⟩ (mF v)
        rw [map_smul, inverse, hscalar]
  -- The second factor retains the same forward and inverse cutoff square.
  have cutoffSquareY
      (a : EquivariantSupportBundleTriple G Y) (ρ : C(Y, unitInterval))
      (r : C(AssociatedBundle G P Y, unitInterval))
      (hr : ∀ p x, r (associatedBundleMk G P Y p x) = ρ x) (p : P) (x : Y)
      (mE : a.1.source.Fiber x ≃ₗ[ℂ]
        (smallBundle (AssociatedEquivariantFiber hP a.2.sourceAction)).Fiber
          (associatedBundleMk G P Y p x))
      (mF : a.1.target.Fiber x ≃ₗ[ℂ]
        (smallBundle (AssociatedEquivariantFiber hP a.2.targetAction)).Fiber
          (associatedBundleMk G P Y p x))
      (hmE : ∀ u, mE u =
        (smallBundleIso (AssociatedEquivariantFiber hP a.2.sourceAction)).linearEquiv _
          (associatedEquivariantFiberMk hP a.2.sourceAction p x rfl u))
      (hmF : ∀ v, mF v =
        (smallBundleIso (AssociatedEquivariantFiber hP a.2.targetAction)).linearEquiv _
          (associatedEquivariantFiberMk hP a.2.targetAction p x rfl v)) :
      let da := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
        a.2.isEquivariant
      let A := da.toSupportBundleTriple
      (∀ u, mF (a.1.datum.cutoffLinearMap ρ x u) =
        A.datum.cutoffLinearMap r (associatedBundleMk G P Y p x) (mE u)) ∧
      (∀ v, mE (a.1.datum.inverse.cutoffLinearMap ρ x v) =
        A.datum.inverse.cutoffLinearMap r (associatedBundleMk G P Y p x) (mF v)) := by
    let da := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
      a.2.isEquivariant
    let A := da.toSupportBundleTriple
    let z := associatedBundleMk G P Y p x
    have hmem : z ∈ A.datum.control ↔ x ∈ a.1.datum.control :=
      associatedControl_mk_mem_iff a.1.datum.control a.2.isEquivariant.invariant_control p x
    change (∀ u, mF (a.1.datum.cutoffLinearMap ρ x u) = A.datum.cutoffLinearMap r z (mE u)) ∧
      (∀ v, mE (a.1.datum.inverse.cutoffLinearMap ρ x v) =
        A.datum.inverse.cutoffLinearMap r z (mF v))
    by_cases hx : x ∈ a.1.datum.control
    · have hz := hmem.mpr hx
      constructor <;> intro w <;>
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_left hx, dite_eq_left hz, LinearMap.zero_apply, map_zero]
    · have hz : z ∉ A.datum.control := fun h ↦ hx (hmem.mp h)
      have boundary (u : a.1.source.Fiber x) :
          A.datum.boundary.linearEquiv ⟨z, hz⟩ (mE u) =
            mF (a.1.datum.boundary.linearEquiv ⟨x, hx⟩ u) := by
        rw [hmE, hmF]
        rw [da.toSupportBundleTriple_apply]
        exact congrArg ((smallBundleIso
          (AssociatedEquivariantFiber hP a.2.targetAction)).linearEquiv z)
            (associatedSupportBoundary_apply hP a.1.datum a.2.sourceAction a.2.targetAction
              a.2.isEquivariant p ⟨x, hx⟩ u)
      have inverse (v : a.1.target.Fiber x) :
          A.datum.inverse.boundary.linearEquiv ⟨z, hz⟩ (mF v) =
            mE (a.1.datum.inverse.boundary.linearEquiv ⟨x, hx⟩ v) := by
        apply (A.datum.boundary.linearEquiv ⟨z, hz⟩).injective
        change A.datum.boundary.linearEquiv ⟨z, hz⟩
          ((A.datum.boundary.linearEquiv ⟨z, hz⟩).symm (mF v)) =
          A.datum.boundary.linearEquiv ⟨z, hz⟩
            (mE ((a.1.datum.boundary.linearEquiv ⟨x, hx⟩).symm v))
        rw [LinearEquiv.apply_symm_apply, boundary, LinearEquiv.apply_symm_apply]
      have hscalar : r z = ρ x := hr p x
      constructor
      · intro u
        simp only [CompactSupportTriple.cutoffLinearMap, dite_eq_right hx, dite_eq_right hz]
        change mF (((ρ x : ℝ) : ℂ) • a.1.datum.boundary.linearEquiv ⟨x, hx⟩ u) =
          ((r z : ℝ) : ℂ) • A.datum.boundary.linearEquiv ⟨z, hz⟩ (mE u)
        rw [map_smul, boundary, hscalar]
      · intro v
        simp only [CompactSupportTriple.cutoffLinearMap, CompactSupportTriple.inverse,
          dite_eq_right hx, dite_eq_right hz]
        change mE (((ρ x : ℝ) : ℂ) • a.1.datum.inverse.boundary.linearEquiv ⟨x, hx⟩ v) =
          ((r z : ℝ) : ℂ) • A.datum.inverse.boundary.linearEquiv ⟨z, hz⟩ (mF v)
        rw [map_smul, inverse, hscalar]
  -- Use actual triple representatives and the invariant cutoffs of the existing product.
  obtain ⟨a, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective a
  obtain ⟨b, rfl⟩ := equivariantSupportBundleTriple_kZeroClass_surjective b
  obtain ⟨U, hU, ha, hUinv, L, hL, _, hLinv, ρ, hρinv, hρzero, hρone⟩ :=
    exists_invariant_time_cutoff (G := G) a.1.datum.control a.1.datum.isCompact_control
  obtain ⟨V, hV, hb, hVinv, M, hM, _, hMinv, τ, hτinv, hτzero, hτone⟩ :=
    exists_invariant_time_cutoff (G := G) b.1.datum.control b.1.datum.isCompact_control
  let da := associatedSupportTriple hP a.1.datum a.2.sourceAction a.2.targetAction
    a.2.isEquivariant
  let db := associatedSupportTriple hP b.1.datum b.2.sourceAction b.2.targetAction
    b.2.isEquivariant
  let A := da.toSupportBundleTriple
  let B₀ := db.toSupportBundleTriple
  let UA := associatedControl G P X U
  let VB := associatedControl G P Y V
  let LA := associatedControl G P X L
  let MB := associatedControl G P Y M
  have hLA : IsCompact LA := isCompact_associatedControl hP L hL hLinv
  have hMB : IsCompact MB := isCompact_associatedControl hP M hM hMinv
  obtain ⟨ρA, hρA, hUA, hρAzero, hρAone⟩ := cutoffComparisonX ρ hρinv U L hU hUinv hLinv
    hρzero hρone
  obtain ⟨τB, hτB, hVB, hτBzero, hτBone⟩ := cutoffComparisonY τ hτinv V M hV hVinv hMinv
    hτzero hτone
  have hA : A.datum.control ⊆ UA := by
    rintro z ⟨px, hpx, rfl⟩
    exact ⟨px, ⟨hpx.1, ha hpx.2⟩, rfl⟩
  have hB : B₀.datum.control ⊆ VB := by
    rintro z ⟨py, hpy, rfl⟩
    exact ⟨py, ⟨hpy.1, hb hpy.2⟩, rfl⟩
  let c := supportedEquivariantExternalProductTriple a b
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv
  let dc := associatedSupportTriple hP c.1.datum c.2.sourceAction c.2.targetAction
    c.2.isEquivariant
  let d := supportedExternalProductTriple A B₀
    ρA UA hUA hA hρAzero LA hLA hρAone τB VB hVB hB hτBzero MB hMB hτBone
  let dp := d.datum.pullback q hq
  -- The same four factor isomorphisms give the prescribed even and odd bundle comparisons.
  obtain ⟨e00, he00⟩ := pairComparison a.1.source b.1.source a.2.sourceAction b.2.sourceAction
  obtain ⟨e11, he11⟩ := pairComparison a.1.target b.1.target a.2.targetAction b.2.targetAction
  obtain ⟨e10, he10⟩ := pairComparison a.1.target b.1.source a.2.targetAction b.2.sourceAction
  obtain ⟨e01, he01⟩ := pairComparison a.1.source b.1.target a.2.sourceAction b.2.targetAction
  obtain ⟨s, hs⟩ := exists_associatedEquivariantFiber_sum_iso hP _ _
    ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
    ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
  obtain ⟨t, ht⟩ := exists_associatedEquivariantFiber_sum_iso hP _ _
    ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
    ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
      (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl)))
  let sumPullback (E F : FiniteBundle (ZX × ZY)) :
      Iso ((E.sum F).pullback q).Fiber ((E.pullback q).sum (F.pullback q)).Fiber := by
    let h : Hom ((E.sum F).pullback q).Fiber ((E.pullback q).sum (F.pullback q)).Fiber :=
      { linearMap := fun _ ↦ LinearMap.id
        continuous_total := by
          apply continuous_induced_rng.mpr
          exact ((sumFst (E := E.Fiber) (F := F.Fiber)).pullback q).continuous_total.prodMk
            ((sumSnd (E := E.Fiber) (F := F.Fiber)).pullback q).continuous_total }
    let j := h.toIso (fun _ ↦ Function.bijective_id)
    refine { linearEquiv := fun z ↦ LinearEquiv.refl ℂ (E.Fiber (q z) × F.Fiber (q z))
             continuous_total := h.continuous_total
             continuous_symm := ?_ }
    apply j.continuous_symm.congr
    intro z
    apply congrArg (TotalSpace.mk z.proj)
    exact (j.linearEquiv z.proj).apply_symm_apply z.snd
  let eSource : Iso (AssociatedEquivariantFiber hP c.2.sourceAction)
      ((q : Z → ZX × ZY) *ᵖ d.source.Fiber) :=
    (s.trans (e00.sum e11)).trans (sumPullback _ _).symm
  let eTarget : Iso (AssociatedEquivariantFiber hP c.2.targetAction)
      ((q : Z → ZX × ZY) *ᵖ d.target.Fiber) :=
    (t.trans (e10.sum e01)).trans (sumPullback _ _).symm
  have hcontrol : dc.control = dp.control := by
    ext z
    induction z using Quotient.inductionOn with
    | h px =>
      change associatedBundleMk G P (X × Y) px.1 px.2 ∈
        associatedControl G P (X × Y) (L ×ˢ M) ↔
        (associatedBundleMk G P X px.1 px.2.1 ∈ LA ∧
          associatedBundleMk G P Y px.1 px.2.2 ∈ MB)
      rw [associatedControl_mk_mem_iff (L ×ˢ M)
        (fun g xy ↦ and_congr (hLinv g xy.1) (hMinv g xy.2)),
        associatedControl_mk_mem_iff L hLinv, associatedControl_mk_mem_iff M hMinv]
      rfl
  have square (z : Z) (hz : z ∉ dc.control) (hp : z ∉ dp.control)
      (w : AssociatedEquivariantFiber hP c.2.sourceAction z) :
      eTarget.linearEquiv z (dc.boundary.linearEquiv ⟨z, hz⟩ w) =
        dp.boundary.linearEquiv ⟨z, hp⟩ (eSource.linearEquiv z w) := by
    induction z using Quotient.inductionOn with
    | h px =>
      rcases px with ⟨p, x, y⟩
      let z := associatedBundleMk G P (X × Y) p (x, y)
      obtain ⟨w₀, rfl⟩ :=
        (associatedEquivariantFiberMk_bijective hP c.2.sourceAction p (x, y) rfl).2 w
      have hxy : (x, y) ∉ c.1.datum.control := by
        intro h
        exact hz ((associatedControl_mk_mem_iff c.1.datum.control
          c.2.isEquivariant.invariant_control p (x, y)).mpr h)
      let a0 := (LinearEquiv.ofBijective
        (IsLinearMap.mk' (associatedEquivariantFiberMk hP a.2.sourceAction p x rfl)
          (associatedEquivariantFiberMk_isLinear hP a.2.sourceAction p x rfl))
        (associatedEquivariantFiberMk_bijective hP a.2.sourceAction p x rfl)).trans
          ((smallBundleIso (AssociatedEquivariantFiber hP a.2.sourceAction)).linearEquiv _)
      let a1 := (LinearEquiv.ofBijective
        (IsLinearMap.mk' (associatedEquivariantFiberMk hP a.2.targetAction p x rfl)
          (associatedEquivariantFiberMk_isLinear hP a.2.targetAction p x rfl))
        (associatedEquivariantFiberMk_bijective hP a.2.targetAction p x rfl)).trans
          ((smallBundleIso (AssociatedEquivariantFiber hP a.2.targetAction)).linearEquiv _)
      let b0 := (LinearEquiv.ofBijective
        (IsLinearMap.mk' (associatedEquivariantFiberMk hP b.2.sourceAction p y rfl)
          (associatedEquivariantFiberMk_isLinear hP b.2.sourceAction p y rfl))
        (associatedEquivariantFiberMk_bijective hP b.2.sourceAction p y rfl)).trans
          ((smallBundleIso (AssociatedEquivariantFiber hP b.2.sourceAction)).linearEquiv _)
      let b1 := (LinearEquiv.ofBijective
        (IsLinearMap.mk' (associatedEquivariantFiberMk hP b.2.targetAction p y rfl)
          (associatedEquivariantFiberMk_isLinear hP b.2.targetAction p y rfl))
        (associatedEquivariantFiberMk_bijective hP b.2.targetAction p y rfl)).trans
          ((smallBundleIso (AssociatedEquivariantFiber hP b.2.targetAction)).linearEquiv _)
      let ms := IsLinearMap.mk'
        (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl)
        (associatedEquivariantFiberMk_isLinear hP c.2.sourceAction p (x, y) rfl)
      let mt := IsLinearMap.mk'
        (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl)
        (associatedEquivariantFiberMk_isLinear hP c.2.targetAction p (x, y) rfl)
      let ES := (TensorProduct.map a0.toLinearMap b0.toLinearMap).prodMap
        (TensorProduct.map a1.toLinearMap b1.toLinearMap)
      let ET := (TensorProduct.map a1.toLinearMap b0.toLinearMap).prodMap
        (TensorProduct.map a0.toLinearMap b1.toLinearMap)
      have hz00 : associatedEquivariantFiberMk hP
        ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))) p (x, y) rfl 0 = 0 :=
        (associatedEquivariantFiberMk_isLinear hP _ p (x, y) rfl).map_zero
      have hz11 : associatedEquivariantFiberMk hP
        ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))) p (x, y) rfl 0 = 0 :=
        (associatedEquivariantFiberMk_isLinear hP _ p (x, y) rfl).map_zero
      have hz10 : associatedEquivariantFiberMk hP
        ((a.2.targetAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.sourceAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))) p (x, y) rfl 0 = 0 :=
        (associatedEquivariantFiberMk_isLinear hP _ p (x, y) rfl).map_zero
      have hz01 : associatedEquivariantFiberMk hP
        ((a.2.sourceAction.pullback ContinuousMap.fst (fun _ _ ↦ rfl)).tensor
          (b.2.targetAction.pullback ContinuousMap.snd (fun _ _ ↦ rfl))) p (x, y) rfl 0 = 0 :=
        (associatedEquivariantFiberMk_isLinear hP _ p (x, y) rfl).map_zero
      have hS : (eSource.linearEquiv z).toLinearMap.comp ms = ES := by
        apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro u v
        · change (eSource.linearEquiv z)
            (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl (u ⊗ₜ[ℂ] v, 0)) = _
          change ((e00.linearEquiv z)
              ((s.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl (u ⊗ₜ[ℂ] v, 0))).1),
            (e11.linearEquiv z)
              ((s.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl
                  (u ⊗ₜ[ℂ] v, 0))).2)) = _
          erw [hs, he00, hz11, map_zero]
          simp only [ES, LinearMap.comp_apply, LinearMap.inl_apply]
          rfl
        · change (eSource.linearEquiv z)
            (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl (0, u ⊗ₜ[ℂ] v)) = _
          change ((e00.linearEquiv z)
              ((s.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl (0, u ⊗ₜ[ℂ] v))).1),
            (e11.linearEquiv z)
              ((s.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.sourceAction p (x, y) rfl
                  (0, u ⊗ₜ[ℂ] v))).2)) = _
          erw [hs, he11, hz00, map_zero]
          simp only [ES, LinearMap.comp_apply, LinearMap.inr_apply]
          rfl
      have hT : (eTarget.linearEquiv z).toLinearMap.comp mt = ET := by
        apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;> intro u v
        · change (eTarget.linearEquiv z)
            (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl (u ⊗ₜ[ℂ] v, 0)) = _
          change ((e10.linearEquiv z)
              ((t.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl (u ⊗ₜ[ℂ] v, 0))).1),
            (e01.linearEquiv z)
              ((t.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl
                  (u ⊗ₜ[ℂ] v, 0))).2)) = _
          erw [ht, he10, hz01, map_zero]
          simp only [ET, LinearMap.comp_apply, LinearMap.inl_apply]
          rfl
        · change (eTarget.linearEquiv z)
            (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl (0, u ⊗ₜ[ℂ] v)) = _
          change ((e10.linearEquiv z)
              ((t.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl (0, u ⊗ₜ[ℂ] v))).1),
            (e01.linearEquiv z)
              ((t.linearEquiv z
                (associatedEquivariantFiberMk hP c.2.targetAction p (x, y) rfl
                  (0, u ⊗ₜ[ℂ] v))).2)) = _
          erw [ht, he01, hz10, map_zero]
          simp only [ET, LinearMap.comp_apply, LinearMap.inr_apply]
          rfl
      have haMaps := cutoffSquareX a ρ ρA hρA p x a0 a1
        (fun _ ↦ rfl) (fun _ ↦ rfl)
      have hbMaps := cutoffSquareY b τ τB hτB p y b0 b1
        (fun _ ↦ rfl) (fun _ ↦ rfl)
      have hlinear : ET.comp (reciprocalTensorSymbol
          (a.1.datum.cutoffLinearMap ρ x) (a.1.datum.inverse.cutoffLinearMap ρ x)
          (b.1.datum.cutoffLinearMap τ y) (b.1.datum.inverse.cutoffLinearMap τ y)) =
        (reciprocalTensorSymbol
          (A.datum.cutoffLinearMap ρA (associatedBundleMk G P X p x))
          (A.datum.inverse.cutoffLinearMap ρA (associatedBundleMk G P X p x))
          (B₀.datum.cutoffLinearMap τB (associatedBundleMk G P Y p y))
          (B₀.datum.inverse.cutoffLinearMap τB (associatedBundleMk G P Y p y))).comp ES := by
        apply LinearMap.prod_ext <;> apply TensorProduct.ext' <;>
          intro u v <;> apply Prod.ext
        · change a1 (a.1.datum.cutoffLinearMap ρ x u) ⊗ₜ[ℂ] b0 v =
            A.datum.cutoffLinearMap ρA (associatedBundleMk G P X p x) (a0 u) ⊗ₜ[ℂ] b0 v
          exact congrArg (fun w ↦ w ⊗ₜ[ℂ] b0 v) (haMaps.1 u)
        · change a0 u ⊗ₜ[ℂ] b1 (b.1.datum.cutoffLinearMap τ y v) =
            a0 u ⊗ₜ[ℂ] B₀.datum.cutoffLinearMap τB (associatedBundleMk G P Y p y) (b0 v)
          exact congrArg (fun w ↦ a0 u ⊗ₜ[ℂ] w) (hbMaps.1 v)
        · change TensorProduct.map a1.toLinearMap b0.toLinearMap
              (-(u ⊗ₜ[ℂ] b.1.datum.inverse.cutoffLinearMap τ y v)) =
            -(a1 u ⊗ₜ[ℂ] B₀.datum.inverse.cutoffLinearMap τB
              (associatedBundleMk G P Y p y) (b1 v))
          rw [map_neg, TensorProduct.map_tmul]
          exact congrArg (fun w ↦ -(a1 u ⊗ₜ[ℂ] w)) (hbMaps.2 v)
        · change a0 (a.1.datum.inverse.cutoffLinearMap ρ x u) ⊗ₜ[ℂ] b1 v =
            A.datum.inverse.cutoffLinearMap ρA (associatedBundleMk G P X p x) (a1 u) ⊗ₜ[ℂ]
              b1 v
          exact congrArg (fun w ↦ w ⊗ₜ[ℂ] b1 v) (haMaps.2 u)
      have hboundary := associatedSupportBoundary_apply hP c.1.datum c.2.sourceAction
        c.2.targetAction c.2.isEquivariant p ⟨(x, y), hxy⟩ w₀
      change eTarget.linearEquiv z
        (dc.boundary.linearEquiv ⟨z, hz⟩ (ms w₀)) =
        dp.boundary.linearEquiv ⟨z, hp⟩ (eSource.linearEquiv z (ms w₀))
      erw [hboundary]
      have hsvalue := LinearMap.congr_fun hS w₀
      have htvalue := LinearMap.congr_fun hT (c.1.datum.boundary.linearEquiv ⟨(x, y), hxy⟩ w₀)
      change eSource.linearEquiv z (ms w₀) = ES w₀ at hsvalue
      change eTarget.linearEquiv z
        (mt (c.1.datum.boundary.linearEquiv ⟨(x, y), hxy⟩ w₀)) =
          ET (c.1.datum.boundary.linearEquiv ⟨(x, y), hxy⟩ w₀) at htvalue
      erw [hsvalue]
      change eTarget.linearEquiv z (mt _) = _
      erw [htvalue]
      exact (LinearMap.congr_fun hlinear w₀).trans
        (RelativeTriple.pullback_apply d.datum.boundary q ⟨z, hp⟩ (ES w₀)).symm
  have hclass : dc.compactSupportClass = dp.compactSupportClass := by
    have hsub : dc.control ⊆ dp.control := hcontrol ▸ Set.Subset.refl _
    have heq : (dc.enlarge dp.control dp.isCompact_control hsub).congr eSource eTarget = dp := by
      change CompactSupportTriple.mk dp.control dp.isCompact_control _ =
        CompactSupportTriple.mk dp.control dp.isCompact_control _
      congr 1
      apply Iso.ext
      intro z
      apply LinearEquiv.ext
      intro w
      change eTarget.linearEquiv z
        ((dc.enlarge dp.control dp.isCompact_control hsub).boundary.linearEquiv z
          (eSource.symm.linearEquiv z w)) = dp.boundary.linearEquiv z w
      rw [dc.enlarge_apply]
      exact (square z (fun hz ↦ z.property (hsub hz)) z.property
        (eSource.symm.linearEquiv z w)).trans
          (congrArg (dp.boundary.linearEquiv z)
            ((eSource.linearEquiv z).apply_symm_apply w))
    calc
      dc.compactSupportClass =
          (dc.enlarge dp.control dp.isCompact_control hsub).compactSupportClass :=
        (dc.compactSupportClass_enlarge dp.control dp.isCompact_control hsub).symm
      _ = ((dc.enlarge dp.control dp.isCompact_control hsub).congr
          eSource eTarget).compactSupportClass :=
        ((dc.enlarge dp.control dp.isCompact_control hsub).compactSupportClass_congr
          eSource eTarget).symm
      _ = dp.compactSupportClass := congrArg _ heq
  rw [equivariantSupportKZeroExternalProduct_class a b
    ρ U hU ha hρzero L hL hρone τ V hV hb hτzero M hM hτone
    hρinv hLinv hτinv hMinv, associatedSupportKZero_class,
    associatedSupportKZero_class, associatedSupportKZero_class]
  change dc.compactSupportClass = compactSupportKZeroPullback q hq
    (compactSupportKZeroExternalProduct A.compactSupportClass B₀.compactSupportClass)
  rw [← supportedExternalProductTriple_compactSupportClass A B₀
    ρA UA hUA hA hρAzero LA hLA hρAone τB VB hVB hB hτBzero MB hMB hτBone]
  change dc.compactSupportClass = compactSupportKZeroPullback q hq d.compactSupportClass
  exact hclass.trans ((d.datum.compactSupportClass_pullback q hq).trans
    (congrArg (compactSupportKZeroPullback q hq)
      (compactSupportTriple_compactSupportClass_ofBoundary d.source d.target d.datum)))


end AtiyahSinger
