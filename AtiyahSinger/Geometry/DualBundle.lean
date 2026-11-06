/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.DualSections

/-!
# The Euclidean model of the actual complex dual bundle

Public module ID: M1168.

D01/D04: retain the actual fibers E_x* and mathlib's Hom-bundle topology, and
replace the model fiber (C^r)* by C^r using evaluation on the standard basis.
The atlas consists exactly of the induced dual frames. No Hermitian metric is used.
This makes the coefficient definition of smooth dual sections available
through the common smoothSections and SmoothBundlePresentation APIs.

Sources: the usual dual-bundle construction, used in SG III.2.15(2), (3.18), (5.1);
mathlib Topology.VectorBundle.Hom supplies the original topological dual bundle.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle
open scoped Manifold ContDiff

/-- The complex-linear identification of the model dual with its basis coefficients. -/
theorem existsUnique_dualModelEquiv (r : ℕ) :
    ∃! T : StrongDual ℂ (EuclideanSpace ℂ (Fin r)) ≃L[ℂ] EuclideanSpace ℂ (Fin r),
      ∀ (α : StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (i : Fin r),
        T α i = α (EuclideanSpace.single i 1) := by
  classical
  let c := EuclideanSpace.equiv (Fin r) ℂ
  -- Evaluate the actual complex-linear covector on the original standard basis.
  let T : StrongDual ℂ (EuclideanSpace ℂ (Fin r)) ≃L[ℂ]
      EuclideanSpace ℂ (Fin r) :=
    ((c.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)).trans
      (ContinuousLinearEquiv.piRing (Fin r))).trans c.symm
  have hT (α : StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (i : Fin r) :
      T α i = α (EuclideanSpace.single i 1) := by
    rfl
  refine ⟨T, hT, ?_⟩
  -- The evaluations specify every coordinate of the same continuous linear equivalence.
  intro S hS
  apply ContinuousLinearEquiv.ext
  funext α
  ext i
  exact (hS α i).trans (hT α i).symm

/-- The model change specified by actual basis evaluations, not the Hermitian Riesz map. -/
def dualModelEquiv (r : ℕ) :
    StrongDual ℂ (EuclideanSpace ℂ (Fin r)) ≃L[ℂ] EuclideanSpace ℂ (Fin r) :=
  Classical.choose (existsUnique_dualModelEquiv r).exists

/-- The chosen model change evaluates the covector on each standard basis vector. -/
theorem dualModelEquiv_apply (r : ℕ)
    (α : StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (i : Fin r) :
    dualModelEquiv r α i = α (EuclideanSpace.single i 1) := by
  -- Use the evaluation property of the same selected unique equivalence.
  exact (existsUnique_dualModelEquiv r).exists.choose_spec α i

variable {r : ℕ} {M : Type*} [TopologicalSpace M]
  (E : M → Type*) [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
  [TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) E)]
  [FiberBundle (EuclideanSpace ℂ (Fin r)) E]
  [VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) E]

/-- Changing the phantom model tag leaves each base point and actual dual vector unchanged. -/
def dualTotalSpaceEquiv :
    TotalSpace (EuclideanSpace ℂ (Fin r)) (DualBundle E) ≃
      TotalSpace (StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (DualBundle E) where
  toFun p := ⟨p.1, p.2⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical Hom-bundle topology transported across the unchanged total-space carrier. -/
@[instance_reducible]
def dualEuclideanTotalSpaceTopology :
    TopologicalSpace (TotalSpace (EuclideanSpace ℂ (Fin r)) (DualBundle E)) :=
  TopologicalSpace.induced (dualTotalSpaceEquiv (r := r) E) inferInstance

attribute [instance] dualEuclideanTotalSpaceTopology

/-- The two model tags describe homeomorphic total spaces with exactly the same fiber values. -/
def dualTotalSpaceHomeomorph :
    TotalSpace (EuclideanSpace ℂ (Fin r)) (DualBundle E) ≃ₜ
      TotalSpace (StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (DualBundle E) :=
  (dualTotalSpaceEquiv E).toHomeomorphOfIsInducing ⟨rfl⟩

/-- The dual frame obtained from a primal frame by precomposition and basis evaluation. -/
def dualFrame
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] :
    Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) (DualBundle E)) := by
  letI : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℂ) := ⟨rfl⟩
  exact ((e.continuousLinearMap (RingHom.id ℂ) (Bundle.Trivial.trivialization M ℂ)).compHomeomorph
    (dualTotalSpaceHomeomorph E)).transFiberHomeomorph (dualModelEquiv r).toHomeomorph

/-- The induced dual frame has the same base set as its primal frame. -/
theorem dualFrame_baseSet
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] : (dualFrame E e).baseSet = e.baseSet := by
  -- The scalar trivial bundle contributes the whole base; both model changes preserve it.
  change e.baseSet ∩ Set.univ = e.baseSet
  exact Set.inter_univ _

/-- Inclusion of each actual dual fiber induces its given operator-norm topology. -/
theorem dualTotalSpaceMk_isInducing (x : M) :
    Topology.IsInducing (@TotalSpace.mk M (EuclideanSpace ℂ (Fin r)) (DualBundle E) x) := by
  -- The retyping homeomorphism identifies this inclusion with the original Hom inclusion.
  have h := FiberBundle.totalSpaceMk_isInducing
    (StrongDual ℂ (EuclideanSpace ℂ (Fin r))) (DualBundle E) x
  exact (dualTotalSpaceHomeomorph E).isInducing.of_comp_iff.mp h

/-- The fiber-bundle atlas is precisely the family of induced primal dual frames. -/
@[instance_reducible]
def dualEuclideanFiberBundle : FiberBundle (EuclideanSpace ℂ (Fin r)) (DualBundle E) where
  totalSpaceMk_isInducing' := dualTotalSpaceMk_isInducing E
  trivializationAtlas' := {d | ∃ (e : Trivialization (EuclideanSpace ℂ (Fin r))
    (π (EuclideanSpace ℂ (Fin r)) E)) (_he : MemTrivializationAtlas e), d = dualFrame E e}
  trivializationAt' x := dualFrame E (trivializationAt (EuclideanSpace ℂ (Fin r)) E x)
  mem_baseSet_trivializationAt' x := by
    rw [dualFrame_baseSet]
    exact mem_baseSet_trivializationAt _ _ x
  trivialization_mem_atlas' x := ⟨_, inferInstance, rfl⟩

attribute [instance] dualEuclideanFiberBundle

/-- Each induced dual frame belongs to the specified Euclidean-model atlas. -/
theorem memTrivializationAtlas_dualFrame
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] : MemTrivializationAtlas (dualFrame E e) := by
  -- Membership retains exactly this original primal frame and its atlas certificate.
  exact ⟨e, inferInstance, rfl⟩

attribute [instance] memTrivializationAtlas_dualFrame

/-- The Euclidean-model atlas defines the ordinary complex dual vector bundle. -/
theorem vectorBundle_dualBundle :
    VectorBundle ℂ (EuclideanSpace ℂ (Fin r)) (DualBundle E) := by
  let c := dualModelEquiv r
  let scalarFrame := Bundle.Trivial.trivialization M ℂ
  let : MemTrivializationAtlas scalarFrame := ⟨rfl⟩
  -- Each unchanged Hom frame is complex-linear, and the model conversion is complex-linear.
  have hlinear : ∀ (d : Trivialization (EuclideanSpace ℂ (Fin r))
      (π (EuclideanSpace ℂ (Fin r)) (DualBundle E))) [MemTrivializationAtlas d],
      d.IsLinear ℂ := by
    rintro _ ⟨e, he, rfl⟩
    let := he
    constructor
    intro x hx
    let d := e.continuousLinearMap (RingHom.id ℂ) scalarFrame
    have hx' : x ∈ d.baseSet :=
      ⟨by simpa only [dualFrame_baseSet] using hx, Set.mem_univ x⟩
    change IsLinearMap ℂ (fun α : DualBundle E x ↦ c ((d ⟨x, α⟩).2))
    exact (c.toLinearMap.comp ((d.linear ℂ hx').mk' _)).isLinear
  refine { trivialization_linear' := hlinear, continuousOn_coordChange' := ?_ }
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  let := he
  let := he'
  let := hlinear (dualFrame E e)
  let := hlinear (dualFrame E e')
  let d := e.continuousLinearMap (RingHom.id ℂ) scalarFrame
  let d' := e'.continuousLinearMap (RingHom.id ℂ) scalarFrame
  let C := c.arrowCongr c
  -- The same model conversion conjugates the actual native Hom transition operators.
  have htransition := continuousOn_coordChange ℂ d d'
  have hconverted := C.continuous.comp_continuousOn htransition
  have hbase : d.baseSet ∩ d'.baseSet =
      (dualFrame E e).baseSet ∩ (dualFrame E e').baseSet := by
    simp only [dualFrame_baseSet]
    change (e.baseSet ∩ Set.univ) ∩ (e'.baseSet ∩ Set.univ) = e.baseSet ∩ e'.baseSet
    simp only [Set.inter_univ]
  rw [hbase] at hconverted
  apply hconverted.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  change (dualFrame E e).coordChangeL ℂ (dualFrame E e') x v =
    C (d.coordChangeL ℂ d' x) v
  rw [(dualFrame E e).coordChangeL_apply' (R := ℂ) (dualFrame E e') hx]
  change c (d' (d.toOpenPartialHomeomorph.symm (x, c.symm v))).2 =
    c (d.coordChangeL ℂ d' x (c.symm v))
  exact congrArg c (d.coordChangeL_apply' d' (hbase.symm ▸ hx) (c.symm v)).symm

attribute [instance] vectorBundle_dualBundle

/-- The induced frame gives exactly the coefficients in dualSectionInFrame. -/
theorem dualFrame_apply_snd
    (e : Trivialization (EuclideanSpace ℂ (Fin r)) (π (EuclideanSpace ℂ (Fin r)) E))
    [MemTrivializationAtlas e] (α : ∀ x, DualBundle E x) (x : M) (hx : x ∈ e.baseSet) :
    (dualFrame E e ⟨x, α x⟩).2 = dualSectionInFrame E e α x := by
  -- The original Hom frame precomposes the covector with the inverse primal frame.
  ext i
  change dualModelEquiv r
    (((Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt ℂ x).comp
      ((α x).comp (e.symmL ℂ x))) i = _
  rw [dualModelEquiv_apply]
  change (Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt ℂ x
    (α x (e.symmL ℂ x (EuclideanSpace.single i 1))) = _
  rw [(Bundle.Trivial.trivialization M ℂ).continuousLinearMapAt_apply_of_mem ℂ
    (Set.mem_univ x)]
  -- On the stated frame domain, both sides evaluate the same genuine inverse-frame vector.
  change α x (e.symmL ℂ x (EuclideanSpace.single i 1)) =
    α x (e.symmL ℂ x (EuclideanSpace.single i 1))
  rw [e.symmL_apply hx]

variable {n : ℕ} [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]

/-- Smoothness through the common bundle API agrees with smooth dual coefficients. -/
theorem isSmoothSection_dualBundle_iff (α : ∀ x, DualBundle E x) :
    IsSmoothSection (n := n) (r := r) (DualBundle E) α ↔
      IsSmoothDualSection (n := n) (r := r) E α := by
  constructor
  · -- Each original primal frame supplies the corresponding designated dual frame.
    intro h e he
    let := he
    have hd := h (dualFrame E e) inferInstance
    rw [dualFrame_baseSet] at hd
    exact hd.congr (fun x hx ↦ (dualFrame_apply_snd E e α x hx).symm)
  · -- Every chart in the dual atlas arises from exactly such a primal frame.
    intro h
    rintro _ ⟨e, he, rfl⟩
    let := he
    rw [dualFrame_baseSet]
    exact (h e he).congr (fun x hx ↦ dualFrame_apply_snd E e α x hx)

/-- The identity on actual covector sections identifies the two smooth-section APIs. -/
def dualSectionsEquiv :
    smoothDualSections (n := n) (r := r) E ≃ₗ[ℂ]
      smoothSections (n := n) (r := r) (DualBundle E) where
  toFun α := ⟨α.val, (isSmoothSection_dualBundle_iff E α.val).2 α.property⟩
  invFun α := ⟨α.val, (isSmoothSection_dualBundle_iff E α.val).1 α.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Real-smooth complex primal transitions induce real-smooth complex dual transitions. -/
theorem isSmoothComplexBundle_dualBundle [IsSmoothComplexBundle (n := n) (r := r) E] :
    IsSmoothComplexBundle (n := n) (r := r) (DualBundle E) := by
  classical
  constructor
  rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
  let := he
  let := he'
  let V := EuclideanSpace ℂ (Fin r)
  let c := dualModelEquiv r
  let d := dualFrame E e
  let d' := dualFrame E e'
  -- Covectors act on coordinates without conjugation: the change is inverse transpose.
  have heval (v w : V) : (c.symm v) w = ∑ j, w j * v j := by
    have hcoord (j : Fin r) : (c.symm v) (EuclideanSpace.single j 1) = v j := by
      have h := dualModelEquiv_apply r (c.symm v) j
      change c (c.symm v) j = _ at h
      rw [c.apply_symm_apply] at h
      exact h.symm
    have hexpand := (EuclideanSpace.basisFun (Fin r) ℂ).sum_repr w
    conv_lhs => rw [← hexpand, map_sum]
    simp only [map_smul, EuclideanSpace.basisFun_repr,
      EuclideanSpace.basisFun_apply, hcoord, smul_eq_mul]
  have hcoords (x : M) (hx : x ∈ d.baseSet ∩ d'.baseSet) (v : V) (i : Fin r) :
      d.coordChangeL ℂ d' x v i =
        ∑ j, (e'.coordChangeL ℂ e x (EuclideanSpace.single i 1)) j * v j := by
    have hx' : x ∈ e.baseSet ∩ e'.baseSet := by
      simpa only [d, d', dualFrame_baseSet] using hx
    let α (y : M) : DualBundle E y := d.symm y v
    have h := dualSectionInFrame_coordChange E e e' α x hx' i
    rw [← dualFrame_apply_snd E e' α x hx'.2,
      ← dualFrame_apply_snd E e α x hx'.1] at h
    have hsource : (d ⟨x, α x⟩).2 = v :=
      congrArg Prod.snd (d.apply_mk_symm hx.1 v)
    change (d' ⟨x, α x⟩).2 i = _ at h
    change (d' ⟨x, α x⟩).2 i = ∑ j,
      (e'.coordChangeL ℂ e x (EuclideanSpace.single i 1)) j * (d ⟨x, α x⟩).2 j at h
    rw [hsource] at h
    rw [d.coordChangeL_apply d' hx]
    exact h
  -- Precomposition is a continuous complex-linear operation on the original model operators.
  let L := (ContinuousLinearMap.compL ℂ V V ℂ).flip
  let C := (c.arrowCongr c).toContinuousLinearMap.comp L
  have htransition := IsSmoothComplexBundle.contMDiffOn_coordChange (n := n) (E := E) e' e
  have hconverted := (C.restrictScalars ℝ).contMDiff.comp_contMDiffOn htransition
  have hbase : e'.baseSet ∩ e.baseSet = d.baseSet ∩ d'.baseSet := by
    simp only [d, d', dualFrame_baseSet, Set.inter_comm]
  rw [hbase] at hconverted
  apply hconverted.congr
  intro x hx
  apply ContinuousLinearMap.ext
  intro v
  ext i
  change d.coordChangeL ℂ d' x v i =
    dualModelEquiv r ((c.symm v).comp (e'.coordChangeL ℂ e x).toContinuousLinearMap) i
  rw [dualModelEquiv_apply]
  change d.coordChangeL ℂ d' x v i =
    (c.symm v) (e'.coordChangeL ℂ e x (EuclideanSpace.single i 1))
  rw [hcoords x hx, heval]

attribute [instance] isSmoothComplexBundle_dualBundle

end AtiyahSinger
