/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Geometry.ComplexifiedTangentParityForms
public import AtiyahSinger.Geometry.GradedDifferentialFormBundle
public import AtiyahSinger.Geometry.SmoothBundleIsoFromSections
public import AtiyahSinger.Geometry.SphereComplexifiedTangent

/-!
# The original exterior and native differential form bundle comparison

Public module ID: M1138.

The metric exterior map is continuous for the original finite wedge-sum topology
and the actual native differential form charts. In these charts its coefficients
are determinants of the original musical pairing with the inverse-chart tangent
frame. Restriction to the original parity fibers therefore gives the specified
continuous bundle isomorphisms, retaining the supplied native section coordinates.

Source: SG II.5 and Appendix C, the metric exterior realization of differential forms.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle Filter Module Set Topology
open scoped BigOperators DirectSum Manifold ContDiff TensorProduct Topology

attribute [local instance] sphereComplexifiedTangentTopology exteriorTopology exteriorParityTopology
  isFiniteRank_model isFiniteRank_exteriorParity

set_option maxSynthPendingDepth 30

set_option maxHeartbeats 1800000 in
-- Keep all original generator topologies, degree projections and native chart coordinates together.
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual metric exterior projections are continuous in every specified finite form model. -/
theorem continuous_sphereExteriorFormCoordinates (r R : ℕ) {ι : Type} [Finite ι]
    (degree : ι → ℕ)
    (Z : VectorBundleCore ℂ (OrthogonalSphere r) (EuclideanSpace ℂ (Fin R))
      (atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)))
    (c : ((j : ι) → EuclideanSpace ℝ (Fin r) [⋀^Fin (degree j)]→L[ℝ] ℂ) ≃L[ℂ]
      EuclideanSpace ℂ (Fin R))
    (hbase : ∀ i, Z.baseSet i = i.val.source)
    (hchart : ∀ (a : OpenPartialHomeomorph (OrthogonalSphere r) (EuclideanSpace ℝ (Fin r)))
      (ha : a ∈ atlas (EuclideanSpace ℝ (Fin r)) (OrthogonalSphere r)) (x)
      (_ : x ∈ a.source) (v : (j : ι) → DifferentialFormFiber (n := r) (degree j) x),
      (Z.localTriv ⟨a, ha⟩ ⟨x, c v⟩).2 = c (fun j ↦ (v j).compContinuousLinearMap
        (mfderiv (𝓡 r) (𝓡 r) a.symm (a x)))) :
    letI : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    letI : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    letI := modelTopology (EuclideanSpace ℂ (Fin R)) Z.Fiber
    Continuous (fun z : TotalSpace Unit
        (fun x ↦ ExteriorAlgebra ℂ (SphereComplexifiedTangent r x)) ↦
      (⟨z.proj, c (fun j ↦ complexifiedTangentExteriorEquiv
        (orthogonalSphereRoundMetric r) (degree j) z.proj
          (DirectSum.decompose (fun k : ℕ ↦ ⋀[ℂ]^k (SphereComplexifiedTangent r z.proj))
            z.snd (degree j)))⟩ : TotalSpace Unit Z.Fiber)) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let S := OrthogonalSphere r
  let V := EuclideanSpace ℝ (Fin r)
  let VZ := EuclideanSpace ℂ (Fin R)
  let I := 𝓡 r
  let E := fun x : S ↦ TangentSpace I x
  let C := SphereComplexifiedTangent r
  let A := fun x : S ↦ ExteriorAlgebra ℂ (C x)
  let g := orthogonalSphereRoundMetric r
  let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
    inferInstanceAs (NormedAddCommGroup VZ)
  let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦ inferInstanceAs (NormedSpace ℂ VZ)
  let := modelTopology VZ Z.Fiber
  let : RiemannianBundle E := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle V E :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ ↦ rfl⟩⟩
  -- Finite basis evaluations detect the original norm topology on each alternating tensor.
  have heval (p : ℕ) : ∃ L : (V [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ] ((Fin p → Fin r) → ℂ),
      IsInducing L ∧ ∀ a j, L a j = a (fun k ↦ EuclideanSpace.single (j k) 1) := by
    let b := (EuclideanSpace.basisFun (Fin r) ℝ).toBasis
    let L : (V [⋀^Fin p]→L[ℝ] ℂ) →ₗ[ℂ] ((Fin p → Fin r) → ℂ) := {
      toFun a j := a (fun k ↦ b (j k))
      map_add' a b := rfl
      map_smul' z a := rfl }
    have hL : Function.Injective L := by
      intro a d h
      have h' : a.toAlternatingMap = d.toAlternatingMap := by
        apply b.ext_alternating
        intro j hj
        exact congrFun h j
      ext v
      exact congrArg (fun f : V [⋀^Fin p]→ₗ[ℝ] ℂ ↦ f v) h'
    let : FiniteDimensional ℂ (V [⋀^Fin p]→L[ℝ] ℂ) := FiniteDimensional.of_injective L hL
    refine ⟨L, (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hL)).isEmbedding.isInducing, ?_⟩
    intro a j
    change a (fun k ↦ EuclideanSpace.basisFun (Fin r) ℝ (j k)) = _
    simp only [EuclideanSpace.basisFun_apply]
  let L (x : S) (p : ℕ) : A x →ₗ[ℂ] DifferentialFormFiber (n := r) p x :=
    (complexifiedTangentExteriorEquiv g p x).toLinearMap.comp
      ((DirectSum.component ℂ ℕ (fun k ↦ ⋀[ℂ]^k (C x)) p).comp
        (DirectSum.decomposeLinearEquiv (fun k : ℕ ↦ ⋀[ℂ]^k (C x))).toLinearMap)
  have hproject (x : S) (p q : ℕ) (hpq : p = q) (u : Fin p → C x)
      (w : Fin q → E x) :
      L x q (ExteriorAlgebra.ιMulti ℂ p u) w = Matrix.det
        (Matrix.of (fun i j : Fin p ↦ complexifiedTangentCovectorMap g x
          (u i) (w (Fin.cast hpq j)))) := by
    subst q
    change complexifiedTangentExteriorEquiv g p x
      (DirectSum.decompose (fun k : ℕ ↦ ⋀[ℂ]^k (C x))
        (ExteriorAlgebra.ιMulti ℂ p u) p) w = _
    rw [show ExteriorAlgebra.ιMulti ℂ p u =
      (exteriorPower.ιMulti ℂ p u : ExteriorAlgebra ℂ (C x)) from rfl]
    rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
    exact complexifiedTangentExteriorEquiv_ιMulti g p x u w
  -- The complexified musical pairing uses the actual continuous real and imaginary vectors.
  have hpair {Y : Type} [TopologicalSpace Y] (f : Y → S)
      (u : ∀ y, C (f y)) (w : ∀ y, E (f y)) {y : Y}
      (hu : ContinuousAt (fun z ↦ (⟨f z, u z⟩ : TotalSpace Unit C)) y)
      (hw : ContinuousAt (fun z ↦ (⟨f z, w z⟩ : TangentBundle I S)) y) :
      ContinuousAt (fun z ↦ complexifiedTangentCovectorMap g (f z) (u z) (w z)) y := by
    let e := complexificationDoubleTotalHomeomorph V E
    let d := FiberBundle.Prod.isInducing_diag V E V E
    have hcoords := (d.continuous.comp e.continuous).continuousAt.comp hu
    have hre := hcoords.fst.inner_bundle hw
    have him := hcoords.snd.inner_bundle hw
    apply ((Complex.continuous_ofReal.continuousAt.comp hre).add
      ((continuousAt_const (y := Complex.I)).mul
        (Complex.continuous_ofReal.continuousAt.comp him))).congr
    filter_upwards [] with z
    let v := complexificationReIm (E (f z)) (u z)
    have hz : u z = (1 : ℂ) ⊗ₜ[ℝ] v.1 + Complex.I ⊗ₜ[ℝ] v.2 :=
      ((complexificationReIm (E (f z))).symm_apply_apply (u z)).symm.trans
        ((complexificationReIm_properties (E (f z))).2.1 v.1 v.2)
    rw [hz, map_add]
    change (g.inner (f z) v.1 (w z) : ℂ) + Complex.I *
      (g.inner (f z) v.2 (w z) : ℂ) =
        (1 : ℂ) * (g.inner (f z) v.1 (w z) : ℂ) +
          Complex.I * (g.inner (f z) v.2 (w z) : ℂ)
    rw [one_mul]
  -- Test continuity on the very wedge-sum generators defining the original exterior topology.
  change @Continuous (TotalSpace Unit A) _ exteriorTopology _ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom]
  intro m k
  let D := TotalSpace Unit (fun x : S ↦ (Fin m → ℂ) × (∀ i : Fin m, Fin (k i) → C x))
  let : TopologicalSpace D := TopologicalSpace.induced
    (fun z : D ↦ (z.proj, z.snd.1,
      fun (i : Fin m) (j : Fin (k i)) ↦ (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit C)))
    inferInstance
  have hdata : Continuous (fun z : D ↦ (z.proj, z.snd.1,
      fun (i : Fin m) (j : Fin (k i)) ↦ (⟨z.proj, z.snd.2 i j⟩ : TotalSpace Unit C))) :=
    continuous_induced_dom
  apply continuous_induced_rng.mpr
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let a : atlas V S := Z.indexAt z₀.proj
  have ha : z₀.proj ∈ a.val.source := by
    rw [← hbase a]
    exact Z.mem_baseSet_at _
  have hnear : ∀ᶠ z : D in 𝓝 z₀, z.proj ∈ a.val.source :=
    hdata.fst.continuousAt.preimage_mem_nhds (a.val.open_source.mem_nhds ha)
  have hframe (v : V) : ContinuousAt (fun x : S ↦
      (⟨x, mfderiv I I a.val.symm (a.val x) v⟩ : TangentBundle I S)) z₀.proj := by
    have hcsm : ContMDiffAt I I ∞ a.val.symm (a.val z₀.proj) :=
      contMDiffAt_symm_of_mem_maximalAtlas
        (IsManifold.subset_maximalAtlas a.property) (a.val.map_source ha)
    have hconst : ContMDiffAt I I.tangent ∞
        (fun z : V ↦ (⟨z, v⟩ : TangentBundle I V)) (a.val z₀.proj) := by
      apply contMDiffAt_totalSpace.mpr
      refine ⟨contMDiffAt_id, ?_⟩
      simpa only [trivializationAt_model_space_apply] using
        (contMDiffAt_const : ContMDiffAt I 𝓘(ℝ, V) ∞ (fun _ : V ↦ v) (a.val z₀.proj))
    have ht₀ : ContMDiffAt I I.tangent ∞ (fun y : V ↦
        (⟨a.val.symm y, mfderiv I I a.val.symm y v⟩ : TangentBundle I S))
          (a.val z₀.proj) :=
      (hcsm.contMDiffAt_tangentMap (X := ⟨a.val z₀.proj, v⟩)
        (m := ∞) (by simp)).comp (a.val z₀.proj) hconst
    have ht := ht₀.continuousAt.comp (a.val.continuousAt ha)
    apply ht.congr_of_eventuallyEq
    filter_upwards [a.val.open_source.mem_nhds ha] with x hx
    change (⟨x, mfderiv I I a.val.symm (a.val x) v⟩ : TangentBundle I S) =
      ⟨a.val.symm (a.val x), mfderiv I I a.val.symm (a.val x) v⟩
    rw [a.val.left_inv hx]
  have hterm (i : Fin m) (j : ι) : ContinuousAt (fun z : D ↦
      (L z.proj (degree j) (ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i))).compContinuousLinearMap
        (mfderiv I I a.val.symm (a.val z.proj))) z₀ := by
    by_cases hk : k i = degree j
    · obtain ⟨ev, hev, heq⟩ := heval (degree j)
      apply hev.continuousAt_iff.mpr
      apply continuousAt_pi.mpr
      intro t
      have hmatrix : ContinuousAt (fun z : D ↦ Matrix.of (fun l s : Fin (k i) ↦
          complexifiedTangentCovectorMap g z.proj (z.snd.2 i l)
            (mfderiv I I a.val.symm (a.val z.proj)
              (EuclideanSpace.single (t (Fin.cast hk s)) 1)))) z₀ := by
        apply continuousAt_pi.mpr
        intro l
        apply continuousAt_pi.mpr
        intro s
        exact hpair (fun z : D ↦ z.proj) (fun z ↦ z.snd.2 i l)
          (fun z ↦ mfderiv I I a.val.symm (a.val z.proj)
            (EuclideanSpace.single (t (Fin.cast hk s)) 1))
          (((continuous_apply l).comp ((continuous_apply i).comp hdata.snd.snd)).continuousAt)
          ((hframe _).comp hdata.fst.continuousAt)
      have hdet := (continuous_id.matrix_det.continuousAt).comp hmatrix
      apply hdet.congr
      filter_upwards [] with z
      dsimp only [Function.comp_apply, id_eq]
      erw [heq]
      change _ = L z.proj (degree j) (ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i))
        (fun l ↦ mfderiv I I a.val.symm (a.val z.proj) (EuclideanSpace.single (t l) 1))
      exact (hproject z.proj (k i) (degree j) hk (z.snd.2 i)
        (fun l ↦ mfderiv I I a.val.symm (a.val z.proj)
          (EuclideanSpace.single (t l) 1))).symm
    · have hzero (z : D) : L z.proj (degree j)
          (ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i)) = 0 := by
        change complexifiedTangentExteriorEquiv g (degree j) z.proj
          (DirectSum.decompose (fun q : ℕ ↦ ⋀[ℂ]^q (C z.proj))
            (ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i)) (degree j)) = 0
        rw [show ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i) =
          (exteriorPower.ιMulti ℂ (k i) (z.snd.2 i) : ExteriorAlgebra ℂ (C z.proj)) from rfl]
        rw [DirectSum.decompose_coe, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hk)]
        exact (complexifiedTangentExteriorEquiv g (degree j) z.proj).map_zero
      apply (continuousAt_const (y := (0 : V [⋀^Fin (degree j)]→L[ℝ] ℂ))).congr
      filter_upwards [] with z
      rw [hzero]
      ext v
      rfl
  have hsum : ContinuousAt (fun z : D ↦ c (fun j ↦
      ∑ i : Fin m, z.snd.1 i •
        ContinuousAlternatingMap.compContinuousLinearMap
          (L z.proj (degree j) (ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i)))
          (mfderiv I I a.val.symm (a.val z.proj)))) z₀ := by
    apply c.continuous.continuousAt.comp
    apply continuousAt_pi.mpr
    intro j
    apply tendsto_finsetSum
    intro i hi
    exact (((continuous_apply i).comp hdata.snd.fst).continuousAt).smul (hterm i j)
  rw [FiberBundle.continuousAt_totalSpace]
  refine ⟨hdata.fst.continuousAt, ?_⟩
  apply hsum.congr_of_eventuallyEq
  filter_upwards [hnear] with z hz
  erw [hchart a.val a.property z.proj hz]
  apply congrArg c
  funext j
  change ContinuousAlternatingMap.compContinuousLinearMap (L z.proj (degree j)
    (∑ i : Fin m, z.snd.1 i • ExteriorAlgebra.ιMulti ℂ (k i) (z.snd.2 i)))
      (mfderiv I I a.val.symm (a.val z.proj)) = _
  rw [map_sum]
  ext v
  simp

set_option maxHeartbeats 2200000 in
-- Retain the original parity, finite model and supplied native section witnesses in one transport.
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 100000 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The prescribed metric parity maps give bundle isomorphisms to the same native form bundles. -/
theorem exists_sphereComplexifiedTangentFormIso (r : ℕ)
    (E F : SmoothFiniteComplexBundle (n := r) (OrthogonalSphere r))
    (e : ∀ x, ((p : {p : Fin (r + 1) // Even p.val}) →
      DifferentialFormFiber (n := r) p.val.val x) ≃ₗ[ℂ] E.Fiber x)
    (f : ∀ x, ((p : {p : Fin (r + 1) // Odd p.val}) →
      DifferentialFormFiber (n := r) p.val.val x) ≃ₗ[ℂ] F.Fiber x)
    (Φ : evenSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := E.rank) E.Fiber)
    (hΦ : ∀ u x, (Φ u).val x = e x (fun p ↦ (u.val p.val.val).val x))
    (Ψ : oddSmoothDifferentialForms (n := r) (M := OrthogonalSphere r) ≃ₗ[ℂ]
      smoothSections (n := r) (r := F.rank) F.Fiber)
    (hΨ : ∀ u x, (Ψ u).val x = f x (fun p ↦ (u.val p.val.val).val x)) :
    letI := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
    letI := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
    ∃ bE : Iso (fun x ↦ CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) 0) E.Fiber,
    ∃ bF : Iso (fun x ↦ CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) 1) F.Fiber,
      (∀ x v, bE.linearEquiv x v =
        e x (complexifiedTangentEvenFormEquiv (orthogonalSphereRoundMetric r) x v)) ∧
      (∀ x v, bF.linearEquiv x v =
        f x (complexifiedTangentOddFormEquiv (orthogonalSphereRoundMetric r) x v)) := by
  classical
  let S := OrthogonalSphere r
  let g := orthogonalSphereRoundMetric r
  let := modelTopology (EuclideanSpace ℂ (Fin E.rank)) E.Fiber
  let := modelTopology (EuclideanSpace ℂ (Fin F.rank)) F.Fiber
  let : IsFiniteRank (SphereComplexifiedTangent r) := isFiniteRank_sphereComplexifiedTangent r
  -- The same transport argument applies to the two actual parity decompositions.
  have htransport {ι : Type} [Fintype ι] (degree : ι → ℕ) (i : ZMod 2)
      (A : SmoothFiniteComplexBundle (n := r) S)
      (a : ∀ x, ((j : ι) → DifferentialFormFiber (n := r) (degree j) x) ≃ₗ[ℂ] A.Fiber x)
      (ΦA : ((j : ι) → SmoothDifferentialForm (n := r) S (degree j)) ≃ₗ[ℂ]
        smoothSections (n := r) (r := A.rank) A.Fiber)
      (hΦA : ∀ u x, (ΦA u).val x = a x (fun j ↦ (u j).val x))
      (η : ∀ x, CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i ≃ₗ[ℂ]
          ((j : ι) → DifferentialFormFiber (n := r) (degree j) x))
      (hη : ∀ x v j, η x v j = complexifiedTangentExteriorEquiv g (degree j) x
        (DirectSum.decompose (fun k : ℕ ↦ ⋀[ℂ]^k (SphereComplexifiedTangent r x))
          v.val (degree j))) :
      letI := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
      ∃ b : Iso (fun x ↦ CliffordAlgebra.evenOdd
        (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i) A.Fiber,
        ∀ x v, b.linearEquiv x v = a x (η x v) := by
    let := modelTopology (EuclideanSpace ℂ (Fin A.rank)) A.Fiber
    let P (x : S) : Type := CliffordAlgebra.evenOdd
      (0 : QuadraticForm ℂ (SphereComplexifiedTangent r x)) i
    obtain ⟨R, Z, c, hZ⟩ := exists_finiteDifferentialForm_bundleModel g degree
    let : ∀ x, NormedAddCommGroup (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℂ (Fin R)))
    let : ∀ x, NormedSpace ℂ (Z.Fiber x) := fun _ ↦
      inferInstanceAs (NormedSpace ℂ (EuclideanSpace ℂ (Fin R)))
    obtain ⟨hSmooth, hbase, hchart, Φ₀, hΦ₀, _, _⟩ := hZ
    let : IsSmoothComplexBundle (n := r) (r := R) Z.Fiber := hSmooth
    let := modelTopology (EuclideanSpace ℂ (Fin R)) Z.Fiber
    -- Restrict the continuous original exterior map through the original parity inclusion.
    have hinc : Continuous (fun z : TotalSpace Unit P ↦
        (⟨z.proj, z.snd.val⟩ : TotalSpace Unit
          (fun x ↦ ExteriorAlgebra ℂ (SphereComplexifiedTangent r x)))) :=
      continuous_induced_dom
    have hcont := (continuous_sphereExteriorFormCoordinates r R degree Z c hbase hchart).comp hinc
    let d : Hom P Z.Fiber := {
      linearMap x := c.toLinearEquiv.toLinearMap.comp (η x).toLinearMap
      continuous_total := by
        apply hcont.congr
        intro z
        apply congrArg (TotalSpace.mk z.proj)
        apply congrArg c
        funext j
        exact (hη z.proj z.snd j).symm }
    let d₀ : Iso P Z.Fiber := d.toIso (fun x ↦ c.bijective.comp (η x).bijective)
    -- The prescribed section equality gives exactly the same native Z-to-A coordinate map.
    let b (x : S) : Z.Fiber x ≃ₗ[ℂ] A.Fiber x := c.symm.toLinearEquiv.trans (a x)
    let Γ := Φ₀.symm.trans ΦA
    have hΓ (u : smoothSections (n := r) (r := R) Z.Fiber) (x : S) :
        (Γ u).val x = b x (u.val x) := by
      change (ΦA (Φ₀.symm u)).val x = a x (c.symm (u.val x))
      rw [hΦA]
      have h := hΦ₀ (Φ₀.symm u) x
      rw [Φ₀.apply_symm_apply] at h
      rw [h, c.symm_apply_apply]
    obtain ⟨_, b₀, hb₀⟩ := exists_smoothBundleIso_of_sectionEquiv b Γ hΓ
    refine ⟨d₀.trans b₀, ?_⟩
    intro x v
    change b₀.linearEquiv x (c (η x v)) = a x (η x v)
    rw [hb₀]
    change a x (c.symm (c (η x v))) = a x (η x v)
    rw [c.symm_apply_apply]
  -- Restriction to all degrees up to the dimension is the original total-form equivalence.
  obtain ⟨⟨e₀, he₀⟩, ⟨f₀, hf₀⟩⟩ :=
    exists_finiteParityDifferentialForm_equiv (n := r) (M := S)
  let Φfin := e₀.symm.trans Φ
  let Ψfin := f₀.symm.trans Ψ
  have hΦfin u x : (Φfin u).val x = e x (fun p ↦ (u p).val x) := by
    change (Φ (e₀.symm u)).val x = _
    rw [hΦ]
    apply congrArg (e x)
    funext p
    have h := he₀ (e₀.symm u) p
    rw [e₀.apply_symm_apply] at h
    exact congrFun (congrArg Subtype.val h.symm) x
  have hΨfin u x : (Ψfin u).val x = f x (fun p ↦ (u p).val x) := by
    change (Ψ (f₀.symm u)).val x = _
    rw [hΨ]
    apply congrArg (f x)
    funext p
    have h := hf₀ (f₀.symm u) p
    rw [f₀.apply_symm_apply] at h
    exact congrFun (congrArg Subtype.val h.symm) x
  obtain ⟨bE, hbE⟩ := htransport (fun p : {p : Fin (r + 1) // Even p.val} ↦ p.val.val)
    0 E e Φfin hΦfin (complexifiedTangentEvenFormEquiv g)
      (complexifiedTangentEvenFormEquiv_apply g)
  obtain ⟨bF, hbF⟩ := htransport (fun p : {p : Fin (r + 1) // Odd p.val} ↦ p.val.val)
    1 F f Ψfin hΨfin (complexifiedTangentOddFormEquiv g)
      (complexifiedTangentOddFormEquiv_apply g)
  exact ⟨bE, bF, hbE, hbF⟩

end AtiyahSinger
