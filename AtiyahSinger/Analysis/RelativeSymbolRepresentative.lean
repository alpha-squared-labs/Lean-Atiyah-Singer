/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Analysis.EllipticRepresentative
public import AtiyahSinger.Analysis.RelativeHomogeneousTripleSmoothing
public import AtiyahSinger.Geometry.AtlasBundleMapComposition
public import AtiyahSinger.Geometry.ExteriorSmoothBundleMap
public import AtiyahSinger.Geometry.NativeAtlasBundleMap
public import AtiyahSinger.Geometry.RelativeSmoothModel
public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Topology.RelativeCotangentRepresentative

/-!
# Smooth relative representatives with a prescribed exterior identity

Public module ID: M0923.

P01/UL03: the smooth cotangent specialization of SG III.13.3 and (13.9).
A finite CW homotopy-type witness and preconnectedness are explicit. The latter
is the current fixed-rank analysis boundary, not an assumption of the book.
The output retains the original K class, the boundary action, smooth exterior
frames, and a global zero-order map agreeing with the symbol outside a compact
base set. Relative smoothing is a project supplement to the source argument.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 40

attribute [local instance] trivialTopology

section Framing

variable {n : ℕ} {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hY : T2Space Y]

include hM hT hSC hY

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Adapt the same exterior frame to canonical native coordinates in both bundle models. -/
private theorem exists_smooth_relative_framing
    (C : Set Y) [Topology.CWComplex C] [Topology.CWComplex.Finite C]
    (h : ContinuousMap.HomotopyEquiv M C) (E : FiniteBundle M) (r : ℕ)
    (hr : ∀ x : M, Module.finrank ℂ (E.Fiber x) = r)
    (K L : Set M) (hK : IsCompact K) (hKL : K ⊆ interior L)
    (τ : RelativeTriple E.Fiber (Bundle.Trivial M (Fin r → ℂ)) Kᶜ) :
    ∃ F : SmoothFiniteComplexBundle (n := n) M, F.rank = r ∧
      letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      let U : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
      ∃ e : Iso E.Fiber F.Fiber,
        ∃ b : ∀ x : U, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin r),
          IsSmoothBundleMap (n := n) (r := F.rank) (q := r) (M := U)
            (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ F.Fiber))
            (F := Bundle.Trivial U (EuclideanSpace ℂ (Fin r)))
            (fun x ↦ (b x).toLinearMap) ∧
          ∀ (x : M) (hx : x ∉ interior L) (v : E.Fiber x),
            b ⟨x, fun hxK ↦ hx (hKL hxK)⟩ (e.linearEquiv x v) =
              (EuclideanSpace.equiv (Fin r) ℂ).symm
                (τ.linearEquiv ⟨x, fun hxK ↦ hx (hKL hxK)⟩ v) := by
  classical
  let V := EuclideanSpace ℂ (Fin r)
  let hsm : IsSmoothComplexBundle (n := n) (r := r) (Bundle.Trivial M V) := by
    constructor
    intro e f he hf
    obtain rfl := Bundle.Trivial.eq_trivialization M V e
    obtain rfl := Bundle.Trivial.eq_trivialization M V f
    have heq (x : M) : ((Bundle.Trivial.trivialization M V).coordChangeL ℂ
        (Bundle.Trivial.trivialization M V) x : V →L[ℂ] V) =
        ContinuousLinearMap.id ℂ V := by
      exact congrArg ContinuousLinearEquiv.toContinuousLinearMap
        (Bundle.Trivial.trivialization.coordChangeL (𝕜 := ℂ) M V x)
    simp only [heq]
    exact contMDiffOn_const
  let T : SmoothFiniteComplexBundle (n := n) M :=
    { rank := r
      Fiber := Bundle.Trivial M V
      isSmooth := hsm }
  let := modelTopology V T.Fiber
  let d := EuclideanSpace.equiv (Fin r) ℂ
  let u : TotalSpace Unit T.Fiber ≃ₜ M × V :=
    (unitTotalHomeomorph V T.Fiber).trans (Bundle.Trivial.homeomorphProd M V)
  have hsrc : Continuous (fun z : TotalSpace Unit (Bundle.Trivial M (Fin r → ℂ)) ↦
      (z.proj, z.snd)) := continuous_induced_dom
  let k : Iso (Bundle.Trivial M (Fin r → ℂ)) T.Fiber :=
    { linearEquiv _ := d.symm.toLinearEquiv
      continuous_total := u.continuous_symm.comp
        (hsrc.fst.prodMk (d.symm.continuous.comp hsrc.snd))
      continuous_symm := continuous_induced_rng.mpr
        (u.continuous.fst.prodMk (d.continuous.comp u.continuous.snd)) }
  let U : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  let p : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let a : Iso ((p : U → M) *ᵖ E.Fiber) ((p : U → M) *ᵖ T.Fiber) :=
    τ.trans (k.pullback p)
  obtain ⟨F, hF, e, b, hb, he⟩ := E.exists_smooth_model_preserving_exterior
    C h r hr T U a (interior L)ᶜ isOpen_interior.isClosed_compl
      (fun _ hx hxK ↦ hx (hKL hxK))
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  refine ⟨F, hF, e, b.linearEquiv, ?_, ?_⟩
  · -- The canonical trivial frame and its pullback have the same fiber coordinate.
    intro e₀ he₀ f hf j
    obtain rfl := Bundle.Trivial.eq_trivialization U V f
    let t := Bundle.Trivial.trivialization M V
    let : MemTrivializationAtlas t := ⟨rfl⟩
    let : MemTrivializationAtlas (t.pullback p) := ⟨t, inferInstance, rfl⟩
    exact hb e₀ (t.pullback p) j
  · intro x hx v
    exact he x hx v


end Framing

section FrameRestriction

variable {n q : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Restriction keeps the specified exterior frame and the native pullback atlas. -/
private theorem isSmooth_exterior_framing_restrict
    (E : SmoothFiniteComplexBundle (n := n) M)
    (U W : Opens M) (hWU : (W : Set M) ⊆ (U : Set M))
    (b : ∀ x : U, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin q))
    (hb : IsSmoothBundleMap (n := n) (r := E.rank) (q := q) (M := U)
      (E := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ E.Fiber))
      (F := Bundle.Trivial U (EuclideanSpace ℂ (Fin q))) (fun x ↦ (b x).toLinearMap)) :
    IsSmoothBundleMap (n := n) (r := E.rank) (q := q) (M := W)
      (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E.Fiber))
      (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin q)))
      (fun x ↦ (b (Set.inclusion hWU x)).toLinearMap) := by
  let iU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  let iW : C(W, M) := ContinuousMap.subtypeVal (W : Set M)
  let t := Bundle.Trivial.trivialization U (EuclideanSpace ℂ (Fin q))
  let : MemTrivializationAtlas t := ⟨rfl⟩
  intro d hd f hf k
  obtain ⟨d₀, hd₀, rfl⟩ := hd
  let : MemTrivializationAtlas d₀ := hd₀
  let : MemTrivializationAtlas (d₀.pullback iU) := ⟨d₀, hd₀, rfl⟩
  obtain rfl := Bundle.Trivial.eq_trivialization W (EuclideanSpace ℂ (Fin q)) f
  have hs := (hb (d₀.pullback iU) t k).comp
    (contMDiff_inclusion hWU).contMDiffOn
      (fun x (hx : x ∈ (d₀.pullback iW).baseSet ∩ Set.univ) ↦
        ⟨hx.1, Set.mem_univ _⟩)
  apply hs.congr
  intro x hx
  have heW : (d₀.pullback iW).symmL ℂ x (EuclideanSpace.single k 1) =
      d₀.symmL ℂ x.val (EuclideanSpace.single k 1) := by
    rw [(d₀.pullback iW).symmL_apply (R := ℂ) hx.1]
    change (d₀.pullback iW).symm x (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (iW x) (EuclideanSpace.single k 1)
    rw [d₀.symmL_apply (R := ℂ) hx.1, (d₀.pullback iW).symm_apply hx.1]
    rfl
  have heU : (d₀.pullback iU).symmL ℂ (Set.inclusion hWU x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ x.val (EuclideanSpace.single k 1) := by
    rw [(d₀.pullback iU).symmL_apply (R := ℂ) hx.1]
    change (d₀.pullback iU).symm (Set.inclusion hWU x) (EuclideanSpace.single k 1) =
      d₀.symmL ℂ (iU (Set.inclusion hWU x)) (EuclideanSpace.single k 1)
    have hxU : iU (Set.inclusion hWU x) ∈ d₀.baseSet := hx.1
    rw [d₀.symmL_apply (R := ℂ) hxU, (d₀.pullback iU).symm_apply hxU]
    rfl
  change b (Set.inclusion hWU x) ((d₀.pullback iW).symmL ℂ x _) =
    b (Set.inclusion hWU x) ((d₀.pullback iU).symmL ℂ (Set.inclusion hWU x) _)
  rw [heW, heU]

end FrameRestriction

variable {n : ℕ} {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [hT : T2Space M] [hSC : SecondCountableTopology M] [hP : PreconnectedSpace M]
  [hY : T2Space Y] (C : Set Y) [hCW : Topology.CWComplex C] [hfin : Topology.CWComplex.Finite C]
  (e : ContinuousMap.HomotopyEquiv M C)

attribute [local instance] t2Space_cotangent locallyCompactSpace_cotangent isFiniteRank_pullback

include hM hT hSC hP hY hCW hfin e

set_option maxHeartbeats 2000000 in
-- The relative construction retains native models, nested pullbacks and one raw support class.
/-- A preconnected base of finite CW type has smooth relative cotangent representatives. -/
theorem exists_smooth_relative_cotangent_representative
    (u : CompactSupportKZero (CotangentTotalSpace (n := n) (M := M))) :
    ∃ E F : SmoothFiniteComplexBundle (n := n) M,
      ∃ (K : Set M) (hK : IsCompact K),
      let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
      ∃ (τE : ∀ x : W, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank))
        (τF : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank)),
        IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ E.Fiber))
          (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
          (fun x ↦ (τE x).toLinearMap) ∧
        IsSmoothBundleMap (n := n) (r := F.rank) (q := E.rank) (M := W)
          (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ F.Fiber))
          (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
          (fun x ↦ (τF x).toLinearMap) ∧
        ∃ c : ∀ x, E.Fiber x →L[ℂ] F.Fiber x,
          IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank)
            (fun x ↦ (c x).toLinearMap) ∧
          ∃ a : homogeneousGlobalSymbolSpace (n := n) (r := E.rank) (q := F.rank)
              E.Fiber F.Fiber 0,
            IsEllipticGlobalSymbol E.Fiber F.Fiber a.val ∧
            (∀ (x : W) (ξ : CotangentFiber (n := n) x.val), a.val x.val ξ = c x.val) ∧
            (∀ (x : W) (v : E.Fiber x.val), τF x (c x.val v) = τE x v) ∧
            (letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
             letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
             letI := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
             letI := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
             ∃ b : CompactSupportTriple
                 ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ E.Fiber)
                 ((cotangentProjection (n := n) (M := M) : _ → M) *ᵖ F.Fiber),
               b.control = cotangentZeroSection '' K ∧
               (∀ (z : (b.controlᶜ : Set (CotangentTotalSpace (n := n) (M := M))))
                 (v : E.Fiber z.val.proj),
                 b.boundary.linearEquiv z v = a.val z.val.proj z.val.snd v) ∧
               b.compactSupportClass = u) :=
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in by
  classical
  let : LocallyCompactSpace M :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) M
  by_cases hcompact : IsCompact (Set.univ : Set M)
  · -- Compact bases may have an empty exterior, so their two ranks remain independent.
    let : CompactSpace M := ⟨hcompact⟩
    obtain ⟨E, F, s, hs, hu⟩ := exists_smooth_elliptic_representative_of_preconnected u 0
    let W : Opens M := ⟨(Set.univ : Set M)ᶜ, isClosed_univ.isOpen_compl⟩
    let : IsEmpty W := ⟨fun x ↦ x.property (Set.mem_univ x.val)⟩
    let τE : ∀ x : W, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
      fun x ↦ isEmptyElim x
    let τF : ∀ x : W, F.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank) :=
      fun x ↦ isEmptyElim x
    refine ⟨E, F, Set.univ, hcompact, τE, τF, ?_, ?_, (fun _ ↦ 0), ?_,
      s, hs, ?_, ?_, ?_⟩
    · intro _ _ _ _ _ x
      exact isEmptyElim x
    · intro _ _ _ _ _ x
      exact isEmptyElim x
    · intro d hd f hf j
      apply (contMDiffOn_const (c := (0 : EuclideanSpace ℂ (Fin F.rank)))).congr
      intro x hx
      exact (f.linearEquivAt ℂ x hx.2).map_zero
    · intro x
      exact isEmptyElim x
    · intro x
      exact isEmptyElim x
    · let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
      let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
      refine ⟨ellipticSymbolTriple s.val s.property.1.continuous hs, ?_, ?_, ?_⟩
      · change cotangentZeroSet = cotangentZeroSection '' Set.univ
        rw [Set.image_univ, range_cotangentZeroSection]
      · exact ellipticSymbolTriple_boundary_apply s.val s.property.1.continuous hs
      · exact (symbolKClass_eq_triple s.val s.property.1.continuous hs).symm.trans hu
  · -- The specified finite CW witness supplies the original continuous relative triple.
    obtain ⟨E₀, F₀, K₀, hK₀, r, τE₀, τF₀, a, ha, hhom, hext, hu⟩ :=
      exists_relative_homogeneous_cotangent_representative C e u
    obtain ⟨x₀, hx₀⟩ : ∃ x : M, x ∉ K₀ := by
      by_contra hn
      have hKall : K₀ = Set.univ := Set.eq_univ_of_forall (by simpa using hn)
      exact hcompact (hKall ▸ hK₀)
    have hrE (x : M) : Module.finrank ℂ (E₀.Fiber x) = r := by
      obtain ⟨r₀, hr₀⟩ := (isLocallyConstant_finrank E₀.Fiber).exists_eq_const
      have hbase : Module.finrank ℂ (E₀.Fiber x₀) = r := by
        have hd : E₀.Fiber x₀ ≃ₗ[ℂ] (Fin r → ℂ) := τE₀.linearEquiv ⟨x₀, hx₀⟩
        exact hd.finrank_eq.trans (by simp)
      exact (congrFun hr₀ x).trans ((congrFun hr₀ x₀).symm.trans hbase)
    have hrF (x : M) : Module.finrank ℂ (F₀.Fiber x) = r := by
      obtain ⟨r₀, hr₀⟩ := (isLocallyConstant_finrank F₀.Fiber).exists_eq_const
      have hbase : Module.finrank ℂ (F₀.Fiber x₀) = r := by
        have hd : F₀.Fiber x₀ ≃ₗ[ℂ] (Fin r → ℂ) := τF₀.linearEquiv ⟨x₀, hx₀⟩
        exact hd.finrank_eq.trans (by simp)
      exact (congrFun hr₀ x).trans ((congrFun hr₀ x₀).symm.trans hbase)
    obtain ⟨K₁, hK₁, hK₀₁, _⟩ :=
      exists_compact_between hK₀ isOpen_univ (Set.subset_univ K₀)
    -- Change the global model comparisons, retaining exactly the prescribed farther frames.
    obtain ⟨E, hEr, eE, τE, hτE, heE⟩ := exists_smooth_relative_framing (n := n)
      C e E₀ r hrE K₀ K₁ hK₀ hK₀₁ τE₀
    obtain ⟨F, hFr, eF, τF, hτF, heF⟩ := exists_smooth_relative_framing (n := n)
      C e F₀ r hrF K₀ K₁ hK₀ hK₀₁ τF₀
    cases hEr
    let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    let := isFiniteRank_model (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    let U : Opens M := ⟨K₀ᶜ, hK₀.isClosed.isOpen_compl⟩
    let iU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
    let EU := (iU : U → M) *ᵖ E.Fiber
    let FU := (iU : U → M) *ᵖ F.Fiber
    let (x : U) : FiniteDimensional ℂ (EU x) :=
      FiniteDimensional.of_injective (τE x).toLinearMap (τE x).injective
    let (x : U) : FiniteDimensional ℂ (FU x) :=
      FiniteDimensional.of_injective (τF x).toLinearMap (τF x).injective
    let σ (x : U) : EU x →L[ℂ] FU x :=
      let eσ : EU x ≃ₗ[ℂ] FU x := (τE x).trans (τF x).symm
      eσ.toContinuousLinearEquiv.toContinuousLinearMap
    have hσ : IsSmoothBundleMap (n := n) (r := E.rank) (q := F.rank) (M := U)
        (E := EU) (F := FU) (fun x ↦ (σ x).toLinearMap) := by
      -- The common native atlas identifies this map with the composition of the same two frames.
      let TU := Bundle.Trivial U (EuclideanSpace ℂ (Fin E.rank))
      let : IsSmoothComplexBundle (n := n) (r := E.rank) EU :=
        isSmoothComplexBundle_pullback E.Fiber iU contMDiff_subtype_val
      let : IsSmoothComplexBundle (n := n) (r := F.rank) FU :=
        isSmoothComplexBundle_pullback F.Fiber iU contMDiff_subtype_val
      let : IsSmoothComplexBundle (n := n) (r := E.rank) TU := by
        constructor
        intro d f hd hf
        obtain rfl := Bundle.Trivial.eq_trivialization U (EuclideanSpace ℂ (Fin E.rank)) d
        obtain rfl := Bundle.Trivial.eq_trivialization U (EuclideanSpace ℂ (Fin E.rank)) f
        have heq (x : U) :
            ((Bundle.Trivial.trivialization U (EuclideanSpace ℂ (Fin E.rank))).coordChangeL ℂ
              (Bundle.Trivial.trivialization U (EuclideanSpace ℂ (Fin E.rank))) x :
                EuclideanSpace ℂ (Fin E.rank) →L[ℂ] EuclideanSpace ℂ (Fin E.rank)) =
              ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin E.rank)) :=
          congrArg ContinuousLinearEquiv.toContinuousLinearMap
            (Bundle.Trivial.trivialization.coordChangeL (𝕜 := ℂ) U
              (EuclideanSpace ℂ (Fin E.rank)) x)
        simp only [heq]
        exact contMDiffOn_const
      have hτFi := IsSmoothBundleMap.symm (n := n) (r := F.rank) (q := E.rank)
        (E := FU) (F := TU) τF hτF
      let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) EU
      let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) FU
      let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) TU
      have he := (isSmoothAtlasBundleMap_native_iff
        (n := n) (r := E.rank) (q := E.rank) (E := EU) (F := TU) _).mpr hτE
      have hf := (isSmoothAtlasBundleMap_native_iff
        (n := n) (r := E.rank) (q := F.rank) (E := TU) (F := FU) _).mpr hτFi
      exact (isSmoothAtlasBundleMap_native_iff
        (n := n) (r := E.rank) (q := F.rank) (E := EU) (F := FU) _).mp (hf.comp he)
    obtain ⟨K₂, hK₂, hK₁₂, c, hc, hcσ⟩ :=
      exists_smoothBundleMap_extension_of_exterior U K₁ hK₁
        (fun _ hx hxK₀ ↦ hx (interior_subset (hK₀₁ hxK₀))) σ hσ
    let p : C(CotangentTotalSpace (n := n) (M := M), M) := cotangentProjection
    let b₀ := a.congr (eE.pullback p) (eF.pullback p)
    have hb₀ : b₀.control = cotangentZeroSection '' K₀ := ha
    have h₀₂ : K₀ ⊆ K₂ := (hK₀₁.trans interior_subset).trans (hK₁₂.trans interior_subset)
    let Z₂ := cotangentZeroSection (n := n) (M := M) '' K₂
    have hZ₂ : IsCompact Z₂ := hK₂.image continuous_cotangentZeroSection
    have hbZ : b₀.control ⊆ Z₂ := by
      rw [hb₀]
      exact Set.image_mono h₀₂
    let b₂ := b₀.enlarge Z₂ hZ₂ hbZ
    have hb₂hom (x : M) (ξ : CotangentFiber (n := n) x) (t : ℝ) (ht : 0 < t)
        (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b₂.controlᶜ)
        (htξ : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ b₂.controlᶜ) :
        b₂.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξ⟩ =
          b₂.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ := by
      apply LinearEquiv.ext
      intro v
      change E.Fiber x at v
      have hξa : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := fun hz ↦ hξ (hbZ hz)
      have htξa : (⟨x, t • ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ :=
        fun hz ↦ htξ (hbZ hz)
      refine (b₀.enlarge_apply Z₂ hZ₂ hbZ ⟨⟨x, t • ξ⟩, htξ⟩ v).trans
        (Eq.trans ?_ (b₀.enlarge_apply Z₂ hZ₂ hbZ ⟨⟨x, ξ⟩, hξ⟩ v).symm)
      change eF.linearEquiv x (a.boundary.linearEquiv ⟨⟨x, t • ξ⟩, htξa⟩
        ((eE.linearEquiv x).symm v)) = eF.linearEquiv x
          (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξa⟩ ((eE.linearEquiv x).symm v))
      rw [hhom x ξ t ht hξa htξa]
      rfl
    have hb₂c (x : M) (hx : x ∉ K₂) (ξ : CotangentFiber (n := n) x)
        (hξ : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ b₂.controlᶜ) (v : E.Fiber x) :
        b₂.boundary.linearEquiv ⟨⟨x, ξ⟩, hξ⟩ v = c x v := by
      have hx₁ : x ∉ interior K₁ := fun hk ↦ hx (interior_subset
        (hK₁₂ (interior_subset hk)))
      have hx₀ : x ∉ K₀ := fun hk ↦ hx (h₀₂ hk)
      rw [hcσ ⟨x, hx₀⟩ hx]
      apply (τF ⟨x, hx₀⟩).injective
      have hξa : (⟨x, ξ⟩ : CotangentTotalSpace) ∈ a.controlᶜ := fun hz ↦ hξ (hbZ hz)
      have htrans := b₀.enlarge_apply Z₂ hZ₂ hbZ ⟨⟨x, ξ⟩, hξ⟩ v
      rw [htrans]
      change τF ⟨x, hx₀⟩ (eF.linearEquiv x
        (a.boundary.linearEquiv ⟨⟨x, ξ⟩, hξa⟩ ((eE.linearEquiv x).symm v))) =
          τF ⟨x, hx₀⟩ ((τF ⟨x, hx₀⟩).symm (τE ⟨x, hx₀⟩ v))
      rw [LinearEquiv.apply_symm_apply, heF x hx₁,
        hext x hx₀ ξ _ ((eE.linearEquiv x).symm v)]
      have he := heE x hx₁ ((eE.linearEquiv x).symm v)
      rw [LinearEquiv.apply_symm_apply] at he
      exact he.symm
    -- Smooth the same conjugated raw triple, with one compact control for its whole homotopy.
    obtain ⟨K₃, hK₃, hK₂₃, _⟩ :=
      exists_compact_between hK₂ isOpen_univ (Set.subset_univ K₂)
    obtain ⟨g⟩ := SmoothCotangentMetric.nonempty (n := n) (M := M)
    obtain ⟨s, hs, hsc, b, hb, hbs, hbclass⟩ :=
      exists_smooth_homogeneous_triple_relative g K₂ K₃ hK₂ hK₃ hK₂₃ c hc b₂ rfl
        hb₂hom hb₂c
    let W : Opens M := ⟨K₃ᶜ, hK₃.isClosed.isOpen_compl⟩
    have h₀₃ : K₀ ⊆ K₃ := h₀₂.trans (hK₂₃.trans interior_subset)
    have hWU : (W : Set M) ⊆ (U : Set M) := fun _ hx hk ↦ hx (h₀₃ hk)
    let j : W → U := Set.inclusion hWU
    refine ⟨E, F, K₃, hK₃, (fun x ↦ τE (j x)), (fun x ↦ τF (j x)),
      isSmooth_exterior_framing_restrict E U W hWU τE hτE,
      isSmooth_exterior_framing_restrict F U W hWU τF hτF,
      c, hc, s, hs, ?_, ?_, b, hb, hbs, ?_⟩
    · intro x ξ
      exact hsc x.val x.property ξ
    · intro x v
      have hx₂ : x.val ∉ K₂ := fun hk ↦ x.property (interior_subset (hK₂₃ hk))
      rw [hcσ (j x) hx₂]
      change τF (j x) ((τF (j x)).symm (τE (j x) v)) = τE (j x) v
      exact (τF (j x)).apply_symm_apply _
    · exact hbclass.trans ((b₀.compactSupportClass_enlarge Z₂ hZ₂ hbZ).trans
        ((a.compactSupportClass_congr (eE.pullback p) (eF.pullback p)).trans hu))

end AtiyahSinger
