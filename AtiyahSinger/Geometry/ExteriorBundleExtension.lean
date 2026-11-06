/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.SmoothBundleMaps
public import AtiyahSinger.Geometry.SmoothBundlePullback
public import AtiyahSinger.Geometry.SmoothFiniteComplexBundle

/-!
# Extending a bundle with a prescribed exterior trivialization

Public module ID: M1226.

E01/UL03: the relative bundle construction in SG III.13.4, pp.248--249.
On a Hausdorff smooth manifold, an actual smooth bundle over an open
submanifold, trivialized outside an ambient compact set, extends to the
ambient manifold. The conclusion supplies
smooth fiber isomorphisms and explicitly retains the given exterior frame.
The ambient manifold need not be compact. This does not produce the initial
relative K representative required by III.13 Lemma 13.3.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle TopologicalSpace
open scoped Manifold ContDiff

set_option maxSynthPendingDepth 25

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [hM : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [hT : T2Space M]

include hM hT

/-- A smooth bundle trivialized outside K extends while retaining that specified trivialization. -/
theorem exists_smoothBundle_extension_of_exterior_trivialization
    (U : Opens M) (K : Set M) (hK : IsCompact K) (hKU : K ⊆ (U : Set M))
    (E : SmoothFiniteComplexBundle (n := n) U) :
    let V : Opens U := ⟨(Subtype.val : U → M) ⁻¹' Kᶜ,
      hK.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
    let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
    ∀ τ : ∀ x : V, E.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank),
      IsSmoothBundleMap (n := n) (r := E.rank) (q := E.rank) (M := V)
        (E := ((ContinuousMap.subtypeVal (V : Set U) : V → U) *ᵖ E.Fiber))
        (F := Bundle.Trivial V (EuclideanSpace ℂ (Fin E.rank)))
        (fun x ↦ (τ x).toLinearMap) →
      ∃ G : SmoothFiniteComplexBundle (n := n) M, G.rank = E.rank ∧
        ∃ e : ∀ x : U, E.Fiber x ≃ₗ[ℂ] G.Fiber x.val,
          IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := U)
            (E := E.Fiber)
            (F := ((ContinuousMap.subtypeVal (U : Set M) : U → M) *ᵖ G.Fiber))
            (fun x ↦ (e x).toLinearMap) ∧
          ∃ σ : ∀ x : W, G.Fiber x.val ≃ₗ[ℂ] EuclideanSpace ℂ (Fin E.rank),
            IsSmoothBundleMap (n := n) (r := G.rank) (q := E.rank) (M := W)
              (E := ((ContinuousMap.subtypeVal (W : Set M) : W → M) *ᵖ G.Fiber))
              (F := Bundle.Trivial W (EuclideanSpace ℂ (Fin E.rank)))
              (fun x ↦ (σ x).toLinearMap) ∧
            ∀ (x : V) (v : E.Fiber x.val),
              σ ⟨x.val.val, x.property⟩ (e x.val v) = τ x v := by
  /- Stage 1: use the open cover U and W=M\K. On U use all the original
  frames of E; on W use the prescribed exterior frame τ in the same finite
  model. Arbitrary pointwise coordinates R express their transitions.
  Stage 2: realize a bundle core with the finite model as every concrete fiber.
  The two appearances of R cancel in each transition, leaving the original
  frame transitions or the matrices of τ. Smooth inversion supplies the
  reverse mixed transitions. The cocycle defines the total-space topology
  and smooth complex atlas; all concrete fibers carry the model norms.
  Stage 3: the core charts give e and σ. Although R itself is an arbitrary
  pointwise choice, its cancellation in these charts proves bundle smoothness
  of e. The overlap equation retains the supplied exterior frame. K⊆U makes
  the opens cover M. No finite-topological-type hypothesis is required once
  this fixed-rank bundle and exterior frame are given. -/
  classical
  let V : Opens U := ⟨(Subtype.val : U → M) ⁻¹' Kᶜ,
    hK.isClosed.isOpen_compl.preimage continuous_subtype_val⟩
  let W : Opens M := ⟨Kᶜ, hK.isClosed.isOpen_compl⟩
  dsimp only
  intro τ hτ
  let Model := EuclideanSpace ℂ (Fin E.rank)
  -- Use every original local frame on U and the one prescribed exterior frame on W.
  let d (u : U) := trivializationAt Model E.Fiber u
  let O : Option U → Set M := fun i ↦ match i with
    | none => Kᶜ
    | some u => (Subtype.val : U → M) '' (d u).baseSet
  have hOopen (i : Option U) : IsOpen (O i) := by
    cases i with
    | none => exact hK.isClosed.isOpen_compl
    | some u => exact U.isOpen.isOpenMap_subtype_val _ (d u).open_baseSet
  have hOinside (u : U) (x : M) : x ∈ O (some u) ↔
      ∃ hx : x ∈ U, (⟨x, hx⟩ : U) ∈ (d u).baseSet := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hx, hxd⟩
      exact ⟨⟨x, hx⟩, hxd, rfl⟩
  /- The core realization has the finite model as every concrete fiber. R only selects
  pointwise coordinates; no smoothness of this arbitrary pointwise choice is claimed.
  In each transition, the two occurrences of R cancel. The resulting transitions are
  exactly the old bundle transitions, the supplied τ, or their actual inverses. -/
  let R (x : U) : E.Fiber x ≃ₗ[ℂ] Model :=
    (d x).linearEquivAt ℂ x (mem_baseSet_trivializationAt Model E.Fiber x)
  let φ (i : Option U) (x : M) (hx : x ∈ O i) : Model ≃ₗ[ℂ] Model := by
    by_cases hxU : x ∈ U
    · cases i with
      | none => exact (R ⟨x, hxU⟩).symm.trans (τ ⟨⟨x, hxU⟩, hx⟩)
      | some u =>
        exact (R ⟨x, hxU⟩).symm.trans
          ((d u).linearEquivAt ℂ ⟨x, hxU⟩ ((hOinside u x).mp hx).choose_spec)
    · cases i with
      | none => exact LinearEquiv.refl ℂ Model
      | some u => exact False.elim (hxU ((hOinside u x).mp hx).choose)
  let a (i j : Option U) (x : M) : Model →L[ℂ] Model :=
    if hx : x ∈ O i ∩ O j then
      ((φ i x hx.1).symm.trans (φ j x hx.2)).toLinearMap.toContinuousLinearMap
    else 0
  have ha (i j : Option U) (x : M) (hx : x ∈ O i ∩ O j) (v : Model) :
      a i j x v = φ j x hx.2 ((φ i x hx.1).symm v) := by
    dsimp only [a]
    rw [dite_eq_left hx]
    rfl
  have haSelf (i : Option U) (x : M) (hx : x ∈ O i) (v : Model) :
      a i i x v = v := by
    rw [ha i i x ⟨hx, hx⟩, LinearEquiv.apply_symm_apply]
  have haComp (i j k : Option U) (x : M) (hx : x ∈ O i ∩ O j ∩ O k)
      (v : Model) : a j k x (a i j x v) = a i k x v := by
    rw [ha j k x ⟨hx.1.2, hx.2⟩, ha i j x hx.1, ha i k x ⟨hx.1.1, hx.2⟩]
    rw [LinearEquiv.symm_apply_apply]
  have hφSome (u x : U) (hx : x.val ∈ O (some u)) :
      φ (some u) x.val hx = (R x).symm.trans
        ((d u).linearEquivAt ℂ x ((hOinside u x.val).mp hx).choose_spec) := by
    simp only [φ, dite_eq_left x.property]
  have hφNone (x : V) :
      φ none x.val.val x.property = (R x.val).symm.trans (τ x) := by
    simp only [φ, dite_eq_left x.val.property]
    rfl
  let T (d₀ : Trivialization Model (π Model E.Fiber)) [MemTrivializationAtlas d₀]
      (j : Option U) (x : U) : Model →L[ℂ] Model := match j with
    | some u => (d₀.coordChangeL ℂ (d u) x : Model →L[ℂ] Model)
    | none => if hx : x.val ∉ K then
        ((τ ⟨x, hx⟩).toLinearMap.comp (d₀.symmL ℂ x).toLinearMap).toContinuousLinearMap
      else 0
  have hTframe (d₀ : Trivialization Model (π Model E.Fiber)) [MemTrivializationAtlas d₀]
      (j : Option U) (x : U) (hxd : x ∈ d₀.baseSet) (hxj : x.val ∈ O j) (v : Model) :
      T d₀ j x v = φ j x.val hxj (R x (d₀.symmL ℂ x v)) := by
    cases j with
    | some u =>
      rw [hφSome u x hxj, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      change d₀.coordChangeL ℂ (d u) x v = _
      rw [d₀.coordChangeL_apply (R := ℂ) (d u) ⟨hxd, ((hOinside u x.val).mp hxj).choose_spec⟩,
        Trivialization.linearEquivAt_apply, d₀.symmL_apply hxd]
    | none =>
      rw [hφNone ⟨x, hxj⟩, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
      dsimp only [T]
      rw [dite_eq_left (show x.val ∉ K from hxj)]
      rfl
  have haT (u : U) (j : Option U) (x : U) (hx : x.val ∈ O (some u) ∩ O j) :
      a (some u) j x.val = T (d u) j x := by
    apply ContinuousLinearMap.ext
    intro v
    rw [ha (some u) j x.val hx, hφSome u x hx.1,
      LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, hTframe (d u) j x
        ((hOinside u x.val).mp hx.1).choose_spec hx.2]
    rw [Trivialization.linearEquivAt_symm_apply, (d u).symmL_apply
      ((hOinside u x.val).mp hx.1).choose_spec]
  have haInv (i j : Option U) (x : M) (hx : x ∈ O i ∩ O j) :
      (a i j x).inverse = a j i x := by
    let C : Model ≃L[ℂ] Model :=
      ((φ i x hx.1).symm.trans (φ j x hx.2)).toContinuousLinearEquiv
    have hC : C.toContinuousLinearMap = a i j x := by
      apply ContinuousLinearMap.ext
      intro v
      exact (ha i j x hx v).symm
    rw [← hC, ContinuousLinearMap.inverse_equiv]
    apply ContinuousLinearMap.ext
    intro v
    rw [ha j i x hx.symm]
    rfl
  -- Assemble the exact smooth columns of τ in each original frame.
  have hτmatrix (d₀ : Trivialization Model (π Model E.Fiber))
      [MemTrivializationAtlas d₀] :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Model →L[ℂ] Model) ∞
        (fun y : V ↦ ((τ y).toLinearMap.comp
          (d₀.symmL ℂ y.val).toLinearMap).toContinuousLinearMap)
        ((Subtype.val : V → U) ⁻¹' d₀.baseSet) := by
    classical
    let I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
    let F := EuclideanSpace ℂ (Fin E.rank)
    let incl : C(V, U) := ContinuousMap.subtypeVal (V : Set U)
    let t := Bundle.Trivial.trivialization V F
    let : MemTrivializationAtlas t := ⟨rfl⟩
    let : MemTrivializationAtlas (d₀.pullback incl) := ⟨⟨d₀, inferInstance, rfl⟩⟩
    let L (y : V) : F →L[ℂ] F :=
      ((τ y).toLinearMap.comp (d₀.symmL ℂ y.val).toLinearMap).toContinuousLinearMap
    -- The native smoothness predicate supplies each column in the original exterior frame.
    have hcolumn (j : Fin E.rank) : ContMDiffOn I 𝓘(ℝ, F) ∞
        (fun y : V ↦ τ y (d₀.symmL ℂ y.val (EuclideanSpace.single j 1)))
        ((Subtype.val : V → U) ⁻¹' d₀.baseSet) := by
      have hj := hτ (d₀.pullback incl) t j
      simp only [t, Bundle.Trivial.trivialization_baseSet, Set.inter_univ,
        Bundle.Trivialization.pullback_baseSet] at hj
      apply hj.congr
      intro y hy
      change τ y (d₀.symmL ℂ y.val (EuclideanSpace.single j 1)) =
        τ y ((d₀.pullback incl).symmL ℂ y (EuclideanSpace.single j 1))
      erw [d₀.symmL_apply (show y.val ∈ d₀.baseSet from hy),
        (d₀.pullback incl).symmL_apply hy]
      simp [Trivialization.symm_apply, hy, incl, Trivialization.pullback]
      rfl
    -- The finite standard basis reconstructs the very same continuous linear operator.
    have hsum : ContMDiffOn I 𝓘(ℝ, F →L[ℂ] F) ∞
        (fun y : V ↦ ∑ j : Fin E.rank,
          ContinuousLinearMap.smulRightL ℂ F F (PiLp.proj 2 (fun _ : Fin E.rank ↦ ℂ) j)
            (τ y (d₀.symmL ℂ y.val (EuclideanSpace.single j 1))))
        ((Subtype.val : V → U) ⁻¹' d₀.baseSet) := by
      apply contMDiffOn_finsetSum
      intro j _
      let C := (ContinuousLinearMap.smulRightL ℂ F F
        (PiLp.proj 2 (fun _ : Fin E.rank ↦ ℂ) j)).restrictScalars ℝ
      exact C.contMDiff.comp_contMDiffOn (hcolumn j)
    apply hsum.congr
    intro y hy
    apply ContinuousLinearMap.ext
    intro v
    have hexpand := congrArg (L y) ((EuclideanSpace.basisFun (Fin E.rank) ℂ).sum_repr v)
    simpa [L, Model, map_sum, map_smul, EuclideanSpace.basisFun_apply,
      EuclideanSpace.basisFun_repr] using hexpand.symm
  have hT (d₀ : Trivialization Model (π Model E.Fiber)) [MemTrivializationAtlas d₀]
      (j : Option U) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Model →L[ℂ] Model) ∞
        (T d₀ j) (d₀.baseSet ∩ (Subtype.val : U → M) ⁻¹' O j) := by
    cases j with
    | some u =>
      apply (IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E.Fiber)
        d₀ (d u)).mono
      intro x hx
      exact ⟨hx.1, ((hOinside u x.val).mp hx.2).choose_spec⟩
    | none =>
      intro x hx
      let x' : V := ⟨x, hx.2⟩
      have hxd : x' ∈ (Subtype.val : V → U) ⁻¹' d₀.baseSet := hx.1
      have hm := (hτmatrix d₀).contMDiffAt
        ((d₀.open_baseSet.preimage continuous_subtype_val).mem_nhds hxd)
      have hlocal : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, Model →L[ℂ] Model) ∞ (fun y : V ↦ T d₀ none y.val) x' := by
        apply hm.congr_of_eventuallyEq
        apply Filter.Eventually.of_forall
        intro y
        dsimp only [T]
        rw [dite_eq_left (show y.val.val ∉ K from y.property)]
      exact ((contMDiffAt_subtype_iff (U := V) (x := x')).mp hlocal).contMDiffWithinAt
  have hAsome (u : U) (j : Option U) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Model →L[ℂ] Model) ∞
        (a (some u) j) (O (some u) ∩ O j) := by
    intro x hx
    obtain ⟨hxU, hxd⟩ := (hOinside u x).mp hx.1
    let x' : U := ⟨x, hxU⟩
    have hx' : x' ∈ (d u).baseSet ∩ (Subtype.val : U → M) ⁻¹' O j := ⟨hxd, hx.2⟩
    have hopen := (d u).open_baseSet.inter ((hOopen j).preimage continuous_subtype_val)
    have hm := (hT (d u) j).contMDiffAt (hopen.mem_nhds hx')
    have hlocal : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Model →L[ℂ] Model) ∞ (fun y : U ↦ a (some u) j y.val) x' := by
      apply hm.congr_of_eventuallyEq
      filter_upwards [hopen.mem_nhds hx'] with y hy
      exact haT u j y ⟨(hOinside u y.val).mpr ⟨y.property, hy.1⟩, hy.2⟩
    exact ((contMDiffAt_subtype_iff (U := U) (x := x')).mp hlocal).contMDiffWithinAt
  -- Reverse mixed transitions by smooth inversion of these same finite matrices.
  have hAsmooth (i j : Option U) :
      ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, Model →L[ℂ] Model) ∞
        (a i j) (O i ∩ O j) := by
    cases i with
    | some u => exact hAsome u j
    | none =>
      cases j with
      | none =>
        intro x hx
        have hc : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
            𝓘(ℝ, Model →L[ℂ] Model) ∞ (fun _ : M ↦ ContinuousLinearMap.id ℂ Model) x :=
          contMDiffAt_const
        apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [(hOopen none).mem_nhds hx.1] with y hy
        apply ContinuousLinearMap.ext
        intro v
        exact haSelf none y hy v
      | some u =>
        intro x hx
        let C : Model ≃L[ℂ] Model :=
          ((φ (some u) x hx.2).symm.trans (φ none x hx.1)).toContinuousLinearEquiv
        have hC : C.toContinuousLinearMap = a (some u) none x := by
          apply ContinuousLinearMap.ext
          intro v
          exact (ha (some u) none x hx.symm v).symm
        have hinv := (contDiffAt_map_inverse (n := ∞) C).restrict_scalars ℝ
        rw [hC] at hinv
        have hc := hinv.comp_contMDiffAt ((hAsome u none).contMDiffAt
          (((hOopen (some u)).inter (hOopen none)).mem_nhds hx.symm))
        apply (hc.congr_of_eventuallyEq ?_).contMDiffWithinAt
        filter_upwards [((hOopen none).inter (hOopen (some u))).mem_nhds hx] with y hy
        exact (haInv (some u) none y hy.symm).symm
  let idx (x : M) : Option U := if hx : x ∈ U then some ⟨x, hx⟩ else none
  have hidx (x : M) : x ∈ O (idx x) := by
    dsimp only [idx]
    split_ifs with hx
    · exact (hOinside _ x).mpr
        ⟨hx, mem_baseSet_trivializationAt Model E.Fiber ⟨x, hx⟩⟩
    · exact fun hxK ↦ hx (hKU hxK)
  have hφidx (x : M) : φ (idx x) x (hidx x) = LinearEquiv.refl ℂ Model := by
    by_cases hx : x ∈ U
    · simp only [idx, dite_eq_left hx, φ]
      apply LinearEquiv.ext
      intro v
      exact (R ⟨x, hx⟩).apply_symm_apply v
    · simp only [idx, dite_eq_right hx, φ]
  -- The verified cocycle defines the actual total topology and native vector-bundle atlas.
  let Z : VectorBundleCore ℂ M Model (Option U) :=
    { baseSet := O
      isOpen_baseSet := hOopen
      indexAt := idx
      mem_baseSet_at := hidx
      coordChange := a
      coordChange_self := haSelf
      continuousOn_coordChange := fun i j ↦ (contMDiffOn_iff.mp (hAsmooth i j)).1
      coordChange_comp := haComp }
  let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup Model)
  let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedSpace ℂ Model)
  let : IsSmoothComplexBundle (n := n) (r := E.rank) Z.Fiber := by
    constructor
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    apply (hAsmooth i j).congr
    intro x hx
    apply ContinuousLinearMap.ext
    intro v
    exact Z.localTriv_coordChange_eq i j hx v
  let G : SmoothFiniteComplexBundle (n := n) M :=
    { rank := E.rank
      Fiber := Z.Fiber }
  -- Each native core chart and inverse are the specified frame, after cancellation of R.
  have htriv (j : Option U) (x : M) (hx : x ∈ O j) (v : Model) :
      ((Z.localTriv j) ⟨x, v⟩).2 = φ j x hx v := by
    change a (idx x) j x v = _
    rw [ha (idx x) j x ⟨hidx x, hx⟩, hφidx]
    rfl
  have hsym (j : Option U) (x : M) (hx : x ∈ O j) (v : Model) :
      (Z.localTriv j).symmL ℂ x v = (φ j x hx).symm v := by
    rw [Z.localTriv_symmL hx]
    change a j (idx x) x v = _
    rw [ha j (idx x) x ⟨hx, hidx x⟩, hφidx]
    rfl
  let e (x : U) : E.Fiber x ≃ₗ[ℂ] G.Fiber x.val := R x
  let iU : C(U, M) := ContinuousMap.subtypeVal (U : Set M)
  have he : IsSmoothBundleMap (n := n) (r := E.rank) (q := G.rank) (M := U)
      (E := E.Fiber) (F := (iU : U → M) *ᵖ G.Fiber)
      (fun x ↦ (e x).toLinearMap) := by
    intro d₀ hd₀ f hf col
    let := hd₀
    rcases hf with ⟨f, hf, rfl⟩
    rcases hf with ⟨j, rfl⟩
    have hcol := ((ContinuousLinearMap.apply ℂ Model
      (EuclideanSpace.single col (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn
        (hT d₀ j)
    apply hcol.congr
    intro x hx
    change ((Z.localTriv j) ⟨x.val,
      R x (d₀.symmL ℂ x (EuclideanSpace.single col 1))⟩).2 = _
    rw [htriv j x.val hx.2, ← hTframe d₀ j x hx.1 hx.2]
    rfl
  -- The exterior map is the supplied exterior chart of this very same glued bundle.
  let σ (x : W) : G.Fiber x.val ≃ₗ[ℂ] Model := φ none x.val x.property
  let iW : C(W, M) := ContinuousMap.subtypeVal (W : Set M)
  have hσ : IsSmoothBundleMap (n := n) (r := G.rank) (q := E.rank) (M := W)
      (E := (iW : W → M) *ᵖ G.Fiber) (F := Bundle.Trivial W Model)
      (fun x ↦ (σ x).toLinearMap) := by
    intro d₀ hd₀ f hf col
    rcases hd₀ with ⟨d₀, hd₀, rfl⟩
    rcases hd₀ with ⟨j, rfl⟩
    rcases hf with ⟨rfl⟩
    have hm : ContMDiffOn 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        𝓘(ℝ, Model →L[ℂ] Model) ∞ (fun x : W ↦ a j none x.val)
        ((Subtype.val : W → M) ⁻¹' O j) :=
      (hAsmooth j none).comp contMDiff_subtype_val.contMDiffOn
        (fun x hx ↦ ⟨hx, x.property⟩)
    have hcol := ((ContinuousLinearMap.apply ℂ Model
      (EuclideanSpace.single col (1 : ℂ))).restrictScalars ℝ).contMDiff.comp_contMDiffOn hm
    simp only [Bundle.Trivial.trivialization_baseSet, Set.inter_univ]
    apply hcol.congr
    intro x hx
    change φ none x.val x.property
      (((Z.localTriv j).pullback iW).symmL ℂ x (EuclideanSpace.single col 1)) = _
    have hpull : ((Z.localTriv j).pullback iW).symmL ℂ x
        (EuclideanSpace.single col 1) =
          (Z.localTriv j).symmL ℂ x.val (EuclideanSpace.single col 1) := by
      rw [((Z.localTriv j).pullback iW).symmL_apply hx]
      change ((Z.localTriv j).pullback iW).symm x (EuclideanSpace.single col 1) =
        (Z.localTriv j).symmL ℂ (iW x) (EuclideanSpace.single col 1)
      erw [(Z.localTriv j).symmL_apply hx,
        ((Z.localTriv j).pullback iW).symm_apply hx]
      rfl
    rw [hpull, hsym j x.val hx]
    exact (ha j none x.val ⟨hx, x.property⟩ (EuclideanSpace.single col 1)).symm
  refine ⟨G, rfl, e, he, σ, hσ, ?_⟩
  intro x v
  change φ none x.val.val x.property (R x.val v) = τ x v
  rw [hφNone x, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

end AtiyahSinger
