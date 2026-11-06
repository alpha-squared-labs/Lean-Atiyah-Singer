/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType
public import AtiyahSinger.Topology.RealBundleRadial
public import AtiyahSinger.Topology.RealBundleSupport
public import AtiyahSinger.Topology.RelativeBundleHomotopy
public import AtiyahSinger.Topology.SupportKZeroComparison
public import AtiyahSinger.Topology.SupportTripleTransport
public import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Relative homogeneous representatives on arbitrary finite-rank real bundles

Public module ID: M2037.

SG III.13 Lemma 13.3, pp.245--246, for the original real total space.
The real rank is locally finite and may vary between components. The base
is a second-countable Hausdorff smooth manifold with a specified homotopy
equivalence to a finite CW complex. Neither compactness nor connectedness
of the base is imposed.

The relative pullback isomorphism records the exterior-frame equation in
SG (13.6). Its continuous homotopy proof is a project supplement to the book's
connection and parallel-transport argument. The main theorem retains the
original compact-support K class, the two actual complex bundles, and their
specified exterior frames. It concerns continuous representatives. Smooth
parameter families belong to later index-independence constructions.
-/

@[expose] public noncomputable section

namespace AtiyahSinger.RealBundle

open Bundle ComplexBundle
open scoped Manifold ContDiff unitInterval

variable {n : ℕ} {X : Type*} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [hX : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ X]
  [hT : T2Space X] [hSC : SecondCountableTopology X]
  (G : Type*) (V : X → Type*) [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [TopologicalSpace (TotalSpace G V)] [hV : RealBundle.IsFiniteRank G V]

attribute [local instance] t2Space_totalSpace locallyCompactSpace_totalSpace
  secondCountableTopology_totalSpace ComplexBundle.isFiniteRank_pullback
  ComplexBundle.trivialTopology

include hX hT hSC hV

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedSectionVars false in

/-- SG (13.6): zero-section pullback preserves the specified exterior frame. -/
theorem exists_relative_zero_pullback_iso
    (P : FiniteBundle (TotalSpace G V)) (K : Set X) (hK : IsCompact K) (r : ℕ)
    (τ : RelativeTriple P.Fiber (Bundle.Trivial (TotalSpace G V) (Fin r → ℂ))
      ((projection G V : TotalSpace G V → X) ⁻¹' Kᶜ)) :
    ∃ L : Set X, IsCompact L ∧ ∃ hKL : K ⊆ L,
      ∃ f : Iso P.Fiber
        ((projection G V : TotalSpace G V → X) *ᵖ
          ((zeroSection G V : X → TotalSpace G V) *ᵖ P.Fiber)),
        ∀ (z : TotalSpace G V) (hz : z.proj ∉ L) (v : P.Fiber z),
          τ.linearEquiv
            ⟨zeroSection G V z.proj, fun h ↦ hz (hKL h)⟩ (f.linearEquiv z v) =
              τ.linearEquiv ⟨z, fun h ↦ hz (hKL h)⟩ v := by
  classical
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) X
  let Z := TotalSpace G V
  -- Enlarge the compact base control and pull the original bundle along actual fiber scaling.
  obtain ⟨L, hL, hKL⟩ := exists_compact_superset hK
  let B := Z × unitInterval
  let f : C(B, Z) :=
    ⟨fun z ↦ ⟨z.1.proj, (z.2 : ℝ) • z.1.snd⟩,
      (continuous_scaling G V).comp
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)⟩
  let Q := P.pullback f
  let p₀ : C(Z, B) := ⟨fun z ↦ (z, 0), continuous_id.prodMk continuous_const⟩
  let p₁ : C(Z, B) := ⟨fun z ↦ (z, 1), continuous_id.prodMk continuous_const⟩
  let O : Set Z := (projection G V : Z → X) ⁻¹' Kᶜ
  let A : Set Z := (projection G V : Z → X) ⁻¹' (interior L)ᶜ
  have hO : IsOpen O := hK.isClosed.isOpen_compl.preimage (continuous_projection G V)
  have hA : IsClosed A := isOpen_interior.isClosed_compl.preimage (continuous_projection G V)
  have hAO : A ⊆ O := fun z hz hx ↦ hz (hKL hx)
  let T : RelativeTriple Q.Fiber (Bundle.Trivial B (Fin r → ℂ)) (Prod.fst ⁻¹' O) :=
    (RelativeTriple.pullback τ f).trans
      ((pullbackTrivialIso f r).restrict (Prod.fst ⁻¹' O))
  have hT (z : Prod.fst ⁻¹' O) (v : Q.Fiber z.val) :
      T.linearEquiv z v = τ.linearEquiv ⟨f z.val, z.property⟩ v := by
    change ((pullbackTrivialIso f r).restrict _).linearEquiv z
      ((RelativeTriple.pullback τ f).linearEquiv z v) = _
    change (pullbackTrivialIso f r).linearEquiv z.val
      ((RelativeTriple.pullback τ f).linearEquiv z v) = _
    rw [pullbackTrivialIso_apply, RelativeTriple.pullback_apply]
  obtain ⟨e, he⟩ := exists_endpoint_pullback_iso_preserving_trivialization Q A O hA hO hAO r T
  -- Endpoint comparison maps retain the actual vectors, including the endpoint equalities.
  have congrPullback (a b : C(Z, Z)) (hab : a = b) :
      ∃ j : Iso ((a : Z → Z) *ᵖ P.Fiber) ((b : Z → Z) *ᵖ P.Fiber),
        ∀ z v, (⟨b z, j.linearEquiv z v⟩ : TotalSpace Unit P.Fiber) = ⟨a z, v⟩ := by
    subst b
    exact ⟨Iso.refl _, fun _ _ ↦ rfl⟩
  have hf₀ : f.comp p₀ = (zeroSection G V).comp (projection G V) := by
    apply ContinuousMap.ext
    intro z
    change (⟨z.proj, (0 : ℝ) • z.snd⟩ : Z) = ⟨z.proj, 0⟩
    simp only [zero_smul]
  have hf₁ : f.comp p₁ = ContinuousMap.id Z := by
    apply ContinuousMap.ext
    intro z
    change (⟨z.proj, (1 : ℝ) • z.snd⟩ : Z) = z
    simp only [one_smul]
    rfl
  obtain ⟨j₀, hj₀⟩ := congrPullback _ _ hf₀
  obtain ⟨j₁, hj₁⟩ := congrPullback _ _ hf₁
  let d := pullbackCompIso (E := P.Fiber) (zeroSection G V) (projection G V)
  let c₀ : Iso ((p₀ : Z → B) *ᵖ Q.Fiber)
      ((projection G V : Z → X) *ᵖ ((zeroSection G V : X → Z) *ᵖ P.Fiber)) :=
    (pullbackCompIso (E := P.Fiber) f p₀).trans (j₀.trans d.symm)
  let c₁ : Iso ((p₁ : Z → B) *ᵖ Q.Fiber) P.Fiber :=
    (pullbackCompIso (E := P.Fiber) f p₁).trans
      (j₁.trans (pullbackIdIso (E := P.Fiber)))
  have hc₀ (z : Z) (v : Q.Fiber (p₀ z)) :
      (⟨zeroSection G V z.proj, c₀.linearEquiv z v⟩ : TotalSpace Unit P.Fiber) =
        ⟨f (p₀ z), v⟩ := by
    have hd (w : P.Fiber (zeroSection G V z.proj)) : (d.linearEquiv z).symm w = w := by
      apply (d.linearEquiv z).injective
      rw [LinearEquiv.apply_symm_apply]
      exact (pullbackCompIso_apply (zeroSection G V) (projection G V) z w).symm
    dsimp only [c₀, Iso.trans, Iso.symm, LinearEquiv.trans_apply]
    rw [pullbackCompIso_apply, hd]
    exact hj₀ z v
  have hc₁ (z : Z) (v : Q.Fiber (p₁ z)) :
      (⟨z, c₁.linearEquiv z v⟩ : TotalSpace Unit P.Fiber) = ⟨f (p₁ z), v⟩ := by
    dsimp only [c₁, Iso.trans, LinearEquiv.trans_apply]
    rw [pullbackCompIso_apply, pullbackIdIso_apply]
    exact hj₁ z v
  let result := c₁.symm.trans (e.symm.trans c₀)
  have hKL' : K ⊆ L := hKL.trans interior_subset
  refine ⟨L, hL, hKL', result, ?_⟩
  intro z hz v
  have hzA : z ∈ A := fun h ↦ hz (interior_subset h)
  have hzO : z ∈ O := fun h ↦ hz (hKL' h)
  let w := (c₁.linearEquiv z).symm v
  let u := (e.linearEquiv z).symm w
  have hboundary := he z hzA u
  rw [LinearEquiv.apply_symm_apply] at hboundary
  rw [hT, hT] at hboundary
  -- Equality in the original total space transports precisely the supplied exterior coordinates.
  have hcoords {a b : Z} (ha : a ∈ O) (hb : b ∈ O) (v : P.Fiber a) (w : P.Fiber b)
      (hv : (⟨a, v⟩ : TotalSpace Unit P.Fiber) = ⟨b, w⟩) :
      τ.linearEquiv ⟨a, ha⟩ v = τ.linearEquiv ⟨b, hb⟩ w := by
    let eval (z : {z : TotalSpace Unit P.Fiber // z.proj ∈ O}) : Fin r → ℂ :=
      τ.linearEquiv ⟨z.val.proj, z.property⟩ z.val.snd
    exact congrArg eval (show (⟨⟨a, v⟩, ha⟩ :
      {z : TotalSpace Unit P.Fiber // z.proj ∈ O}) = ⟨⟨b, w⟩, hb⟩ from Subtype.ext hv)
  have hleft := hcoords (a := zeroSection G V z.proj) (b := f (p₀ z)) hzO hzO
    (c₀.linearEquiv z u) u (hc₀ z u)
  have hright := hcoords (a := z) (b := f (p₁ z)) hzO hzO v w (by
    have h := hc₁ z w
    rw [LinearEquiv.apply_symm_apply] at h
    exact h)
  exact hleft.trans (hboundary.symm.trans hright.symm)

variable {Y : Type*} [TopologicalSpace Y] [hY : T2Space Y]
  (C : Set Y) [hCW : Topology.CWComplex C] [hfin : Topology.CWComplex.Finite C]
  (e : ContinuousMap.HomotopyEquiv X C)

include hY hCW hfin e

attribute [local instance] sumTopology isFiniteRank_sum

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 800000 in

/-- SG 13.3 on the original real bundle, retaining its class and exterior frames. -/
theorem exists_relative_homogeneous_representative :
    letI : LocallyCompactSpace X :=
      ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) X
    ∀ u : CompactSupportKZero (TotalSpace G V),
    ∃ E F : FiniteBundle X, ∃ K : Set X, IsCompact K ∧
      ∃ (r : ℕ) (τE : RelativeTriple E.Fiber (Bundle.Trivial X (Fin r → ℂ)) Kᶜ)
        (τF : RelativeTriple F.Fiber (Bundle.Trivial X (Fin r → ℂ)) Kᶜ),
      ∃ a : CompactSupportTriple
        ((projection G V : TotalSpace G V → X) *ᵖ E.Fiber)
        ((projection G V : TotalSpace G V → X) *ᵖ F.Fiber),
        a.control = zeroSection G V '' K ∧
        (∀ (x : X) (v : V x) (t : ℝ), 0 < t →
          ∀ (hv : (⟨x, v⟩ : TotalSpace G V) ∈ a.controlᶜ)
            (htv : (⟨x, t • v⟩ : TotalSpace G V) ∈ a.controlᶜ),
            a.boundary.linearEquiv ⟨⟨x, t • v⟩, htv⟩ =
              a.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩) ∧
        (∀ (x : X) (hx : x ∉ K) (v : V x)
          (hv : (⟨x, v⟩ : TotalSpace G V) ∈ a.controlᶜ) (w : E.Fiber x),
            τF.linearEquiv ⟨x, hx⟩ (a.boundary.linearEquiv ⟨⟨x, v⟩, hv⟩ w) =
              τE.linearEquiv ⟨x, hx⟩ w) ∧
        a.compactSupportClass = u := by
  classical
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin n)) X
  intro u
  let Z := TotalSpace G V
  let πV := projection G V
  let z₀ := zeroSection G V
  -- Stabilize the original representative by the same identity summand on both sides.
  obtain ⟨a₀, ha₀⟩ := supportBundleTriple_compactSupportClass_surjective u
  obtain ⟨Q, r, ⟨j⟩⟩ := FiniteBundle.exists_complement_of_homotopyEquiv_finiteCW C
    ((homotopyEquiv G V).trans e) a₀.source
  let P := a₀.source.sum Q
  let R := a₀.target.sum Q
  let a : CompactSupportTriple P.Fiber R.Fiber :=
    a₀.datum.sum (CompactSupportTriple.ofIso (Iso.refl Q.Fiber))
  have ha : a.compactSupportClass = u := by
    rw [CompactSupportTriple.compactSupportClass_sum,
      CompactSupportTriple.compactSupportClass_ofIso, add_zero]
    exact (compactSupportTriple_compactSupportClass_ofBoundary a₀.source a₀.target a₀.datum).trans
      ha₀
  let K₀ : Set X := πV '' a.control
  have hK₀ : IsCompact K₀ := a.isCompact_control.image πV.continuous
  let U : Set Z := (πV : Z → X) ⁻¹' K₀ᶜ
  have hU : U ⊆ a.controlᶜ := by
    intro z hz ha
    exact hz (Set.mem_image_of_mem πV ha)
  let τP : RelativeTriple P.Fiber (Bundle.Trivial Z (Fin r → ℂ)) U := j.restrict U
  let τR : RelativeTriple R.Fiber (Bundle.Trivial Z (Fin r → ℂ)) U :=
    (a.boundary.restrictTo hU).symm.trans τP
  have hframes (z : U) (v : P.Fiber z.val) :
      τR.linearEquiv z (a.boundary.linearEquiv ⟨z.val, hU z.property⟩ v) =
        τP.linearEquiv z v := by
    have h := Iso.restrictTo_apply a.boundary hU z v
    change τP.linearEquiv z
      (((a.boundary.restrictTo hU).linearEquiv z).symm
        (a.boundary.linearEquiv ⟨z.val, hU z.property⟩ v)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
  -- Relative zero pullback retains both of these specified frames on a common exterior.
  obtain ⟨L, hL, hKL, f, hf⟩ := exists_relative_zero_pullback_iso (n := n) G V P K₀ hK₀ r τP
  obtain ⟨N, hN, hKN, g, hg⟩ := exists_relative_zero_pullback_iso (n := n) G V R K₀ hK₀ r τR
  let K := L ∪ N
  have hK : IsCompact K := hL.union hN
  have hK₀K : K₀ ⊆ K := hKL.trans Set.subset_union_left
  let E := P.pullback z₀
  let F := R.pullback z₀
  let a' : CompactSupportTriple ((πV : Z → X) *ᵖ E.Fiber)
      ((πV : Z → X) *ᵖ F.Fiber) := a.congr f g
  let τE₀ : RelativeTriple E.Fiber (Bundle.Trivial X (Fin r → ℂ)) K₀ᶜ :=
    (RelativeTriple.pullback τP z₀).trans ((pullbackTrivialIso z₀ r).restrict K₀ᶜ)
  let τF₀ : RelativeTriple F.Fiber (Bundle.Trivial X (Fin r → ℂ)) K₀ᶜ :=
    (RelativeTriple.pullback τR z₀).trans ((pullbackTrivialIso z₀ r).restrict K₀ᶜ)
  let τE := τE₀.restrictTo (Set.compl_subset_compl.mpr hK₀K)
  let τF := τF₀.restrictTo (Set.compl_subset_compl.mpr hK₀K)
  have hτE (x : X) (hx : x ∉ K) (v : E.Fiber x) :
      τE.linearEquiv ⟨x, hx⟩ v =
        τP.linearEquiv ⟨z₀ x, fun h ↦ hx (hK₀K h)⟩ v := by
    rw [Iso.restrictTo_apply]
    change (pullbackTrivialIso z₀ r).linearEquiv x
      ((RelativeTriple.pullback τP z₀).linearEquiv ⟨x, _⟩ v) = _
    rw [pullbackTrivialIso_apply, RelativeTriple.pullback_apply]
  have hτF (x : X) (hx : x ∉ K) (v : F.Fiber x) :
      τF.linearEquiv ⟨x, hx⟩ v =
        τR.linearEquiv ⟨z₀ x, fun h ↦ hx (hK₀K h)⟩ v := by
    rw [Iso.restrictTo_apply]
    change (pullbackTrivialIso z₀ r).linearEquiv x
      ((RelativeTriple.pullback τR z₀).linearEquiv ⟨x, _⟩ v) = _
    rw [pullbackTrivialIso_apply, RelativeTriple.pullback_apply]
  have hcontrol (z : Z) (hz : z ∈ a'.control) : z.proj ∈ K :=
    hK₀K (Set.mem_image_of_mem πV hz)
  have hrelative (z : Z) (hz : z.proj ∉ K) (ha : z ∈ a'.controlᶜ)
      (v : E.Fiber z.proj) :
      τF.linearEquiv ⟨z.proj, hz⟩ (a'.boundary.linearEquiv ⟨z, ha⟩ v) =
        τE.linearEquiv ⟨z.proj, hz⟩ v := by
    have hzL : z.proj ∉ L := fun h ↦ hz (Or.inl h)
    have hzN : z.proj ∉ N := fun h ↦ hz (Or.inr h)
    have hz₀ : z.proj ∉ K₀ := fun h ↦ hz (hK₀K h)
    let w := (f.linearEquiv z).symm v
    rw [hτF, hτE]
    erw [a.congr_apply f g]
    have hleft := hg z hzN (a.boundary.linearEquiv ⟨z, ha⟩ w)
    have hmiddle := hframes ⟨z, hz₀⟩ w
    have hright := hf z hzL w
    rw [LinearEquiv.apply_symm_apply] at hright
    exact hleft.trans (hmiddle.trans hright.symm)
  let τ := τE.trans τF.symm
  have hτ (z : Z) (hz : z.proj ∉ K) (ha : z ∈ a'.controlᶜ) :
      a'.boundary.linearEquiv ⟨z, ha⟩ = τ.linearEquiv ⟨z.proj, hz⟩ := by
    apply LinearEquiv.ext
    intro v
    apply (τF.linearEquiv ⟨z.proj, hz⟩).injective
    exact (hrelative z hz ha v).trans
      ((τF.linearEquiv ⟨z.proj, hz⟩).apply_symm_apply _).symm
  -- Radial normalization sharpens the control to zero(K), retaining the actual original class.
  obtain ⟨b, hb, hhom, hframe, hclass⟩ :=
    exists_radial_representative G V E F a' K hK hcontrol τ hτ
  refine ⟨E, F, K, hK, r, τE, τF, b, hb, hhom, ?_, ?_⟩
  · intro x hx v hv w
    rw [hframe ⟨x, v⟩ hx hv]
    exact (τF.linearEquiv ⟨x, hx⟩).apply_symm_apply _
  · exact hclass.trans ((a.compactSupportClass_congr f g).trans ha)

end AtiyahSinger.RealBundle
