/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.GradedDifferentialFormBundle
public import AtiyahSinger.Geometry.OrthogonalSmoothAction
public import AtiyahSinger.Geometry.SmoothEquivariantBundle

/-!
# The natural action on a native finite family of sphere forms

Public module ID: M1237.

The supplied finite form model keeps its original native tensor charts.
Inverse tangent pullback gives a jointly smooth orthogonal-group action on
that same bundle. The chart matrices are polynomial alternating pullbacks of
the original inverse derivative, and the group laws retain its contravariant
composition order. The construction includes empty degree families and rank zero.

Source: SG III.9, the natural de Rham group action, with explicit finite native
bundle coordinates. The sphere and orthogonal-group atlases are unchanged.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter IsManifold Set
open scoped Manifold ContDiff Topology Matrix.Norms.L2Operator

attribute [local instance] continuousSMul_orthogonalSphere lieGroup_orthogonalGroup

set_option maxHeartbeats 4000000 in
-- Retain both native charts, the differentiated joint family and finite tensor action.
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The prescribed finite native form model carries its actual smooth inverse-pullback action. -/
theorem exists_finiteSphereFormEquivariantStructure (r R : ℕ)
    {ι : Type} [Finite ι] (degree : ι → ℕ)
    (Z : VectorBundleCore ℂ (OrthogonalSphere r) (EuclideanSpace ℂ (Fin R))
      (atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)))
    (e : ((j : ι) → EuclideanSpace ℝ (Fin r) [⋀^Fin (degree j)]→L[ℝ] ℂ) ≃L[ℂ]
      EuclideanSpace ℂ (Fin R))
    (hbase : ∀ i, Z.baseSet i = i.val.source)
    (hchart : ∀ (c : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
      (x : OrthogonalSphere r) (_ : x ∈ c.source)
      (a : (j : ι) → DifferentialFormFiber (n := r) (degree j) x),
      (Z.localTriv ⟨c, hc⟩ ⟨x, e a⟩).2 = e (fun j ↦ (a j).compContinuousLinearMap
        (mfderiv (𝓡 r) (𝓡 r) c.symm (c x)))) :
    letI : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    letI : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    letI := modelTopology (EuclideanSpace ℂ (Fin R)) Z.Fiber
    ∃ σ : EquivariantStructure (Matrix.orthogonalGroup (Fin r) ℝ) Z.Fiber,
      σ.IsSmooth (n := r) (r := R) 𝓘(ℝ, OrthogonalGroupModel r) ∧
      ∀ (A : Matrix.orthogonalGroup (Fin r) ℝ) (x : OrthogonalSphere r)
        (a : (j : ι) → DifferentialFormFiber (n := r) (degree j) x),
        σ.linearMap A x (e a) = e (fun j ↦ (a j).compContinuousLinearMap
          (mfderiv (𝓡 r) (𝓡 r) (fun z : OrthogonalSphere r ↦ A⁻¹ • z) (A • x))) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  -- First differentiate the actual smooth inverse action in fixed native sphere charts.
  have hderivative
      (c d : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
      (hc : c ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r))
      (hd : d ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)) :
      ContMDiffOn (𝓘(ℝ, OrthogonalGroupModel r).prod (𝓡 r))
        𝓘(ℝ, EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) ∞
        (fun p : Matrix.orthogonalGroup (Fin r) ℝ × OrthogonalSphere r ↦
          (show EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r) from
          (mfderiv (𝓡 r) (𝓡 r) c p.2).comp
            ((mfderiv (𝓡 r) (𝓡 r) (fun z : OrthogonalSphere r ↦ p.1⁻¹ • z)
              (p.1 • p.2)).comp (mfderiv (𝓡 r) (𝓡 r) d.symm (d (p.1 • p.2))))))
        {p | p.2 ∈ c.source ∧ p.1 • p.2 ∈ d.source} := by
    classical
    let S := OrthogonalSphere r
    let G := Matrix.orthogonalGroup (Fin r) ℝ
    let V := EuclideanSpace ℝ (Fin r)
    let I := 𝓡 r
    let IG := 𝓘(ℝ, OrthogonalGroupModel r)
    let IP := IG.prod I
    let W : Set (G × S) := {p | p.2 ∈ c.source ∧ p.1 • p.2 ∈ d.source}
    have hact : ContMDiff IP I ∞ (fun p : G × S ↦ p.1 • p.2) :=
      ContMDiffSMul.contMDiff_smul
    have hopen : IsOpen W := (c.open_source.preimage continuous_snd).inter
      (d.open_source.preimage hact.continuous)
    intro p hp
    let f (q : G × S) (v : V) : V := c (q.1⁻¹ • d.symm v)
    let a (q : G × S) : V := d (q.1 • q.2)
    have hdlocal : ContMDiffAt I I ∞ d (p.1 • p.2) :=
      (contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd)).contMDiffAt
          (d.open_source.mem_nhds hp.2)
    have hclocal : ContMDiffAt I I ∞ c p.2 :=
      (contMDiffOn_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hc)).contMDiffAt
          (c.open_source.mem_nhds hp.1)
    have hdinv : ContMDiffAt I I ∞ d.symm (d (p.1 • p.2)) :=
      (contMDiffOn_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas (I := I) (n := ∞) hd)).contMDiffAt
          (d.open_target.mem_nhds (d.map_source hp.2))
    have hpoint : p.1⁻¹ • d.symm (a p) = p.2 := by
      rw [show a p = d (p.1 • p.2) from rfl, d.left_inv hp.2, inv_smul_smul]
    have ha : ContMDiffAt IP I ∞ a p := hdlocal.comp p hact.contMDiffAt
    have hfamily : ContMDiffAt (IP.prod I) I ∞ (Function.uncurry f) (p, a p) := by
      have hsource : ContMDiffAt (IP.prod I) I ∞
          (fun q : (G × S) × V ↦ q.1.1⁻¹ • d.symm q.2) (p, a p) :=
        (contMDiffAt_fst.fst.inv).smul (hdinv.comp (p, a p) contMDiffAt_snd)
      have hc' : ContMDiffAt I I ∞ c (p.1⁻¹ • d.symm (a p)) := by
        rw [hpoint]
        exact hclocal
      exact hc'.comp (p, a p) hsource
    have hder := ContMDiffAt.mfderiv f a hfamily ha
      (m := (∞ : WithTop ℕ∞)) (by simp)
    have hder' : ContMDiffAt IP 𝓘(ℝ, V →L[ℝ] V) ∞
        (fun q ↦ (show V →L[ℝ] V from mfderiv I I (f q) (a q))) p := by
      simpa only [inTangentCoordinates_model_space] using hder
    apply (hder'.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [hopen.mem_nhds hp] with q hq
    have hdq := (mdifferentiable_of_mem_atlas (I := I) hd).mdifferentiableAt_symm
      (d.map_source hq.2)
    have hcq := (mdifferentiable_of_mem_atlas (I := I) hc).mdifferentiableAt hq.1
    have hA := (contMDiff_orthogonalSphere_smul r q.1⁻¹).mdifferentiable (by simp)
    change (mfderiv I I c q.2).comp
        ((mfderiv I I (fun z : S ↦ q.1⁻¹ • z) (q.1 • q.2)).comp
          (mfderiv I I d.symm (d (q.1 • q.2)))) = mfderiv I I (f q) (a q)
    symm
    change mfderiv I I (c ∘ ((fun z : S ↦ q.1⁻¹ • z) ∘ d.symm))
        (d (q.1 • q.2)) = _
    rw [mfderiv_comp _ (by simpa only [Function.comp_apply, d.left_inv hq.2,
      inv_smul_smul] using hcq) ((hA _).comp _ hdq), mfderiv_comp _ (hA _) hdq]
    dsimp only [Function.comp_apply]
    erw [d.left_inv hq.2, inv_smul_smul]
  let S := OrthogonalSphere r
  let G := Matrix.orthogonalGroup (Fin r) ℝ
  let V := EuclideanSpace ℝ (Fin r)
  let I := 𝓡 r
  let IG := 𝓘(ℝ, OrthogonalGroupModel r)
  let IP := IG.prod I
  let W := (j : ι) → V [⋀^Fin (degree j)]→L[ℝ] ℂ
  let VZ := EuclideanSpace ℂ (Fin R)
  let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup VZ)
  let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦ inferInstanceAs (NormedSpace ℂ VZ)
  let := modelTopology VZ Z.Fiber
  -- Alternating pullback is polynomial in this same inverse derivative in each finite degree.
  let C (L : V →L[ℝ] V) : VZ →L[ℂ] VZ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun a ↦ e (fun j ↦ (e.symm a j).compContinuousLinearMap L)
        map_add' := by
          intro a b
          rw [e.symm.map_add, ← e.map_add]
          apply congrArg e
          funext j
          ext v
          rfl
        map_smul' := by
          intro c a
          rw [e.symm.map_smul, RingHom.id_apply, ← e.map_smul]
          apply congrArg e
          funext j
          ext v
          rfl }
  have hCsmooth : ContDiff ℝ ∞ C := by
    let e₀ := EuclideanSpace.equiv (Fin R) ℂ
    let cols := (e₀.arrowCongr (ContinuousLinearEquiv.refl ℂ VZ)).trans
      (ContinuousLinearEquiv.piRing (Fin R))
    have hc : ContDiff ℝ ∞ (fun L ↦ cols (C L)) := by
      apply contDiff_pi.mpr
      intro i
      apply (e.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      apply contDiff_pi.mpr
      intro j
      have hB : ContDiff ℝ ∞
          (ContinuousAlternatingMap.compContinuousLinearMapCLM :
            (V →L[ℝ] V) → (V [⋀^Fin (degree j)]→L[ℝ] ℂ) →L[ℝ]
              (V [⋀^Fin (degree j)]→L[ℝ] ℂ)) :=
        contDiff_iff_contDiffAt.mpr fun L ↦
          (ContinuousAlternatingMap.analyticAt_compContinuousLinearMapCLM L).contDiffAt
      exact hB.clm_apply contDiff_const
    convert (cols.symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp hc using 1
    funext L
    exact (cols.symm_apply_apply (C L)).symm
  let dA (A : G) (x : S) : V →L[ℝ] V :=
    mfderiv I I (fun z : S ↦ A⁻¹ • z) (A • x)
  let L (A : G) (x : S) : Z.Fiber x →ₗ[ℂ] Z.Fiber (A • x) := (C (dA A x)).toLinearMap
  -- The original inverse derivative composition gives the two action laws.
  have hdOne (x : S) : dA 1 x = ContinuousLinearMap.id ℝ V := by
    dsimp only [dA]
    have hmap : (fun z : S ↦ (1 : G)⁻¹ • z) = id := by
      funext z
      simp
    erw [hmap, one_smul, mfderiv_id]
    rfl
  have hdMul (A B : G) (x : S) : dA (A * B) x = (dA B x).comp (dA A (B • x)) := by
    have hmaps : (fun z : S ↦ (A * B)⁻¹ • z) =
        (fun z : S ↦ B⁻¹ • z) ∘ (fun z : S ↦ A⁻¹ • z) := by
      funext z
      rw [mul_inv_rev, mul_smul]
      rfl
    dsimp only [dA]
    rw [hmaps, mfderiv_comp _
      ((contMDiff_orthogonalSphere_smul r B⁻¹).mdifferentiable (by simp) _)
      ((contMDiff_orthogonalSphere_smul r A⁻¹).mdifferentiable (by simp) _)]
    erw [mul_smul, inv_smul_smul]
  have hone (x : S) (v : VZ) :
      (⟨(1 : G) • x, L 1 x v⟩ : TotalSpace Unit Z.Fiber) = ⟨x, v⟩ := by
    change (⟨(1 : G) • x, C (dA 1 x) v⟩ : TotalSpace Unit Z.Fiber) = ⟨x, v⟩
    rw [hdOne]
    erw [one_smul]
    congr 1
    change e (fun j ↦ (e.symm v j).compContinuousLinearMap (ContinuousLinearMap.id ℝ V)) = v
    convert e.apply_symm_apply v using 1
    apply congrArg e
    funext j
    ext w
    rfl
  have hmul (A B : G) (x : S) (v : VZ) :
      (⟨(A * B) • x, L (A * B) x v⟩ : TotalSpace Unit Z.Fiber) =
        ⟨A • (B • x), L A (B • x) (L B x v)⟩ := by
    change (⟨(A * B) • x, C (dA (A * B) x) v⟩ : TotalSpace Unit Z.Fiber) =
      ⟨A • (B • x), C (dA A (B • x)) (C (dA B x) v)⟩
    rw [hdMul]
    erw [mul_smul]
    congr 1
    change e (fun j ↦ (e.symm v j).compContinuousLinearMap
      ((dA B x).comp (dA A (B • x)))) = e (fun j ↦
        ContinuousAlternatingMap.compContinuousLinearMap
          (e.symm (e (fun k ↦ (e.symm v k).compContinuousLinearMap (dA B x))) j)
          (dA A (B • x)))
    rw [e.symm_apply_apply]
    apply congrArg e
    funext j
    ext w
    rfl
  -- Native form charts express the same action by these finite coordinate matrices.
  let D (c d : atlas V S) (q : G × S) : V →L[ℝ] V :=
    (mfderiv I I c.val q.2).comp
      ((dA q.1 q.2).comp (mfderiv I I d.val.symm (d.val (q.1 • q.2))))
  have hD (c d : atlas V S) :
      ContMDiffOn IP 𝓘(ℝ, V →L[ℝ] V) ∞ (D c d)
        {p | p.2 ∈ c.val.source ∧ p.1 • p.2 ∈ d.val.source} :=
    hderivative c.val d.val c.property d.property
  have hcoordinates (c d : atlas V S) (A : G) (x : S) (v : VZ)
      (hx : x ∈ c.val.source) (hy : A • x ∈ d.val.source) :
      (Z.localTriv d ⟨A • x, L A x v⟩).2 =
        C (D c d (A, x)) ((Z.localTriv c ⟨x, v⟩).2) := by
    have hs : (Z.localTriv c ⟨x, v⟩).2 =
        e (fun j ↦ (e.symm v j).compContinuousLinearMap
          (mfderiv I I c.val.symm (c.val x))) := by
      simpa only [e.apply_symm_apply] using hchart c.val c.property x hx (e.symm v)
    change (Z.localTriv d ⟨A • x,
      e (fun j ↦ (e.symm v j).compContinuousLinearMap (dA A x))⟩).2 = _
    rw [hchart d.val d.property _ hy, hs]
    change e (fun j ↦ ContinuousAlternatingMap.compContinuousLinearMap
      ((e.symm v j).compContinuousLinearMap (dA A x))
      (mfderiv I I d.val.symm (d.val (A • x)))) =
        e (fun j ↦ (e.symm (e (fun k ↦ (e.symm v k).compContinuousLinearMap
          (mfderiv I I c.val.symm (c.val x)))) j).compContinuousLinearMap (D c d (A, x)))
    rw [e.symm_apply_apply]
    apply congrArg e
    funext j
    ext w
    apply congrArg (e.symm v j)
    funext i
    have hi := (mdifferentiable_of_mem_atlas (I := I) c.property).symm_comp_deriv hx
    exact (congrArg (fun T : V →L[ℝ] V ↦ T
      (dA A x (mfderiv I I d.val.symm (d.val (A • x)) (w i)))) hi).symm
  have hact : ContMDiff IP I ∞ (fun p : G × S ↦ p.1 • p.2) :=
    ContMDiffSMul.contMDiff_smul
  have hformula (A : G) (x : S) (a : W) : L A x (e a) =
      e (fun j ↦ (a j).compContinuousLinearMap
        (mfderiv I I (fun z : S ↦ A⁻¹ • z) (A • x))) := by
    change e (fun j ↦ (e.symm (e a) j).compContinuousLinearMap (dA A x)) = _
    rw [e.symm_apply_apply]
  clear_value C L D dA
  -- Joint continuity is tested in the original total-space charts.
  have hcontinuous : Continuous (fun p : G × TotalSpace VZ Z.Fiber ↦
      (⟨p.1 • p.2.proj, L p.1 p.2.proj p.2.snd⟩ : TotalSpace VZ Z.Fiber)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hsource := (FiberBundle.continuousAt_totalSpace (F := VZ)
      (E := Z.Fiber) (f := fun q : G × TotalSpace VZ Z.Fiber ↦ q.2) (x₀ := p)).mp
        continuousAt_snd
    let c : atlas V S := Z.indexAt p.2.proj
    let d : atlas V S := Z.indexAt (p.1 • p.2.proj)
    have hc : p.2.proj ∈ c.val.source := by
      rw [← hbase c]
      exact Z.mem_baseSet_at _
    have hd : p.1 • p.2.proj ∈ d.val.source := by
      rw [← hbase d]
      exact Z.mem_baseSet_at _
    have hparameter : ContinuousAt (fun q : G × TotalSpace VZ Z.Fiber ↦
        (q.1, q.2.proj)) p := continuousAt_fst.prodMk hsource.1
    have hopen : IsOpen {q : G × S | q.2 ∈ c.val.source ∧ q.1 • q.2 ∈ d.val.source} :=
      (c.val.open_source.preimage continuous_snd).inter
        (d.val.open_source.preimage hact.continuous)
    have hdc : ContinuousOn (D c d)
        {q : G × S | q.2 ∈ c.val.source ∧ q.1 • q.2 ∈ d.val.source} :=
      (hD c d).continuousOn
    have hdat : ContinuousAt (D c d) (p.1, p.2.proj) :=
      hdc.continuousAt (hopen.mem_nhds ⟨hc, hd⟩)
    have hdparam : ContinuousAt (fun q : G × TotalSpace VZ Z.Fiber ↦
        D c d (q.1, q.2.proj)) p :=
      ContinuousAt.comp (f := fun q : G × TotalSpace VZ Z.Fiber ↦ (q.1, q.2.proj))
        (g := D c d) hdat hparameter
    have hmatrix : ContinuousAt (fun q : G × TotalSpace VZ Z.Fiber ↦
        C (D c d (q.1, q.2.proj))) p :=
      ContinuousAt.comp (f := fun q : G × TotalSpace VZ Z.Fiber ↦ D c d (q.1, q.2.proj))
        (g := C) hCsmooth.continuous.continuousAt hdparam
    rw [FiberBundle.continuousAt_totalSpace]
    refine ⟨continuousAt_fst.smul hsource.1, ?_⟩
    apply (hmatrix.clm_apply hsource.2).congr_of_eventuallyEq
    filter_upwards [hparameter.preimage_mem_nhds (hopen.mem_nhds ⟨hc, hd⟩)] with q hq
    exact hcoordinates c d q.1 q.2.proj q.2.snd hq.1 hq.2
  let σ : EquivariantStructure G Z.Fiber := {
    linearMap := L
    one_map := hone
    mul_map := hmul
    continuous_action := (continuous_unitTotalEquiv_symm VZ Z.Fiber).comp
      (hcontinuous.comp (continuous_fst.prodMk
        ((continuous_unitTotalEquiv VZ Z.Fiber).comp continuous_snd))) }
  -- Each original local frame column varies jointly smoothly in the group and base point.
  have hσ : σ.IsSmooth (n := r) (r := R) IG := by
    rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩ j
    change ContMDiffOn IP 𝓘(ℝ, VZ) ∞ _
      {p : G × S | p.2 ∈ Z.baseSet c ∧ p.1 • p.2 ∈ Z.baseSet d}
    rw [hbase c, hbase d]
    have hmatrix := hCsmooth.contMDiff.comp_contMDiffOn (hD c d)
    let ev : (VZ →L[ℂ] VZ) →L[ℝ] VZ :=
      (ContinuousLinearMap.apply ℂ VZ (EuclideanSpace.single j (1 : ℂ))).restrictScalars ℝ
    have hcolumn := ev.contMDiff.comp_contMDiffOn hmatrix
    apply hcolumn.congr
    intro p hp
    have hcZ : p.2 ∈ (Z.localTriv c).baseSet := by
      change p.2 ∈ Z.baseSet c
      rw [hbase c]
      exact hp.1
    change (Z.localTriv d ⟨p.1 • p.2, L p.1 p.2
      ((Z.localTriv c).symmL ℂ p.2 (EuclideanSpace.single j (1 : ℂ)))⟩).2 =
        C (D c d p) (EuclideanSpace.single j (1 : ℂ))
    refine (hcoordinates c d p.1 p.2 _ hp.1 hp.2).trans ?_
    apply congrArg (C (D c d p))
    erw [(Z.localTriv c).symmL_apply hcZ]
    exact congrArg Prod.snd ((Z.localTriv c).apply_mk_symm hcZ
      (EuclideanSpace.single j (1 : ℂ)))
  exact ⟨σ, hσ, hformula⟩

end AtiyahSinger
