/-
Copyright (c) 2026 Alpha Squared Labs. All rights reserved.
Released under Apache 2.0 license as described in LICENSE.
Authors: Alpha Squared Labs, Codex
-/
module

public import AtiyahSinger.Topology.BundleHomotopyType
public import AtiyahSinger.Topology.CircleMatrixLoop
public import AtiyahSinger.Topology.ComplexDisk
public import AtiyahSinger.Topology.StableMatrixLoop
public import AtiyahSinger.Topology.TripleKZeroComparison
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Matrix loops and geometric triples on the disk pair

Public module ID: M1955.

Karoubi III.1.6--1.8, pp.113--114, identifies stable based matrix loops over
C(X,ℂ) with K(X × D², X × S¹), for compact Hausdorff X. The forward construction
below evaluates the original matrix loop on the boundary of the actual closed
complex disk and uses that matrix as the boundary map of two trivial bundles.
The relative class is the existing difference-bundle class of this triple.

Normalization, stabilization, and homotopy are retained in the comparison theorem.
In particular, the additive equivalence is built from this specified forward map;
it is not an arbitrary equivalence between the two groups. No Bott-periodicity
statement or oriented generator identification is used in this construction.
-/

@[expose] public noncomputable section

namespace AtiyahSinger

open Bundle ComplexBundle
open scoped Matrix unitInterval

universe u

namespace FiniteMatrixLoop

variable {A : Type u} [NormedRing A]

/-- The circle map obtained by descending the same based interval loop. -/
def circleMap (p : FiniteMatrixLoop A) :
    C(Circle, (Matrix (Fin p.size) (Fin p.size) A)ˣ) :=
  (exists_circleMap_of_path 1 p.loop).choose

/-- The descended circle map retains every value of the original parametrized loop. -/
theorem circleMap_parameter (p : FiniteMatrixLoop A) (t : I) :
    p.circleMap (Circle.exp (2 * Real.pi * (t : ℝ))) = p.loop t := by
  /- The existence theorem choosing circleMap specifies equality of the resulting
  circleMapPath with p.loop. Evaluate that equality at t; the positive circle
  parametrization is the one used in the original path-descent theorem. -/
  -- Evaluate the specification of this same chosen circle map, with its original base point.
  obtain ⟨hbase, hpath⟩ := (exists_circleMap_of_path 1 p.loop).choose_spec
  exact congrArg
    (fun q : Path (1 : (Matrix (Fin p.size) (Fin p.size) A)ˣ) 1 ↦ q t) hpath

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]

attribute [local instance] complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space
  trivialTopology isFiniteRank_trivial

/-- The original boundary matrix, evaluated at x, acts on the standard complex fiber. -/
def diskBoundaryLinearEquiv (p : FiniteMatrixLoop C(X, ℂ))
    (z : complexDiskBoundaryProduct X) : (Fin p.size → ℂ) ≃ₗ[ℂ] (Fin p.size → ℂ) :=
  (Matrix.GeneralLinearGroup.toLin
    (Matrix.GeneralLinearGroup.map
      (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom
      (p.circleMap (complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩)))).toLinearEquiv


set_option linter.unusedSectionVars false in
/-- Continuity certificates for the specified boundary matrix action and its inverse. -/
theorem diskBoundary_continuity (p : FiniteMatrixLoop C(X, ℂ)) :
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial (X × Complex.UnitClosedDisc) (Fin p.size → ℂ))
        (complexDiskBoundaryProduct X)) ↦
      (⟨z.proj, p.diskBoundaryLinearEquiv z.proj z.snd⟩ : TotalSpace Unit
        (Restrict (Bundle.Trivial (X × Complex.UnitClosedDisc) (Fin p.size → ℂ))
          (complexDiskBoundaryProduct X)))) ∧
    Continuous (fun z : TotalSpace Unit
      (Restrict (Bundle.Trivial (X × Complex.UnitClosedDisc) (Fin p.size → ℂ))
        (complexDiskBoundaryProduct X)) ↦
      (⟨z.proj, (p.diskBoundaryLinearEquiv z.proj).symm z.snd⟩ : TotalSpace Unit
        (Restrict (Bundle.Trivial (X × Complex.UnitClosedDisc) (Fin p.size → ℂ))
          (complexDiskBoundaryProduct X)))) := by
  /- Stage 1: joint evaluation C(X,ℂ) × X → ℂ is continuous for compact Hausdorff X.
  Compose it entrywise with the original circle map and the boundary identification.
  Finite matrix multiplication therefore acts continuously on the product fibers.
  Stage 2: the units topology also records the inverse matrix continuously. Apply
  the same argument to that inverse, and transport the product maps through the
  restriction topology. These are exactly the two displayed total-space maps. -/
  classical
  let F := Bundle.Trivial (X × Complex.UnitClosedDisc) (Fin p.size → ℂ)
  let D := complexDiskBoundaryProduct X
  let Z := TotalSpace Unit (Restrict F D)
  -- The restriction topology remembers the original base and original trivial fiber.
  have hbase : Continuous (fun z : Z ↦ z.proj) :=
    Pullback.continuous_proj Unit F (Subtype.val : D → X × Complex.UnitClosedDisc)
  have hprod : Continuous (fun z : TotalSpace Unit F ↦ (z.proj, z.snd)) :=
    continuous_induced_dom
  have hvec : Continuous (fun z : Z ↦ z.snd) :=
    continuous_snd.comp
      (hprod.comp (Pullback.continuous_lift Unit F
        (Subtype.val : D → X × Complex.UnitClosedDisc)))
  have hx : Continuous (fun z : Z ↦ z.proj.val.1) :=
    continuous_fst.comp (continuous_subtype_val.comp hbase)
  let boundaryPoint : D → complexDiskBoundary := fun z ↦ ⟨z.val.2, z.property⟩
  have hboundary : Continuous boundaryPoint :=
    (continuous_snd.comp continuous_subtype_val).subtype_mk _
  let c : Z → (Matrix (Fin p.size) (Fin p.size) C(X, ℂ))ˣ := fun z ↦
    p.circleMap (complexDiskBoundaryHomeomorph (boundaryPoint z.proj))
  have hc : Continuous c :=
    p.circleMap.continuous.comp
      (complexDiskBoundaryHomeomorph.continuous.comp (hboundary.comp hbase))
  -- Joint evaluation works for every coefficient of both the matrix and its unit inverse.
  have hmatrix (a : Z → Matrix (Fin p.size) (Fin p.size) C(X, ℂ))
      (ha : Continuous a) :
      Continuous (fun z : Z ↦ fun i j ↦ a z i j z.proj.val.1) := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact ((continuous_apply j).comp ((continuous_apply i).comp ha)).eval hx
  have hforward := hmatrix (fun z ↦ (c z).val) (Units.continuous_val.comp hc)
  have hinverse := hmatrix (fun z ↦ (c z).inv) (Units.continuous_coe_inv.comp hc)
  -- Return the two continuous matrix actions to the same original restricted total space.
  have htotal (f : Z → Fin p.size → ℂ) (hf : Continuous f) :
      Continuous (fun z : Z ↦ (⟨z.proj, f z⟩ : Z)) := by
    rw [(inducing_pullbackTotalSpaceEmbedding Unit F
      (Subtype.val : D → X × Complex.UnitClosedDisc)).continuous_iff]
    exact hbase.prodMk (continuous_induced_rng.mpr
      ((continuous_subtype_val.comp hbase).prodMk hf))
  constructor
  · apply htotal
    change Continuous (fun z : Z ↦ (fun i j ↦ (c z).val i j z.proj.val.1) *ᵥ z.snd)
    exact hforward.matrix_mulVec hvec
  · apply htotal
    change Continuous (fun z : Z ↦ (fun i j ↦ (c z).inv i j z.proj.val.1) *ᵥ z.snd)
    exact hinverse.matrix_mulVec hvec

/-- The geometric relative triple with the actual original loop as its boundary action. -/
def diskTriple (p : FiniteMatrixLoop C(X, ℂ)) :
    BundleTriple (complexDiskBoundaryProduct X) where
  source := FiniteBundle.trivial (X × Complex.UnitClosedDisc) p.size
  target := FiniteBundle.trivial (X × Complex.UnitClosedDisc) p.size
  boundary :=
    { linearEquiv := p.diskBoundaryLinearEquiv
      continuous_total := p.diskBoundary_continuity.1
      continuous_symm := p.diskBoundary_continuity.2 }

/-- On the oriented boundary parameter, the triple acts by the same original path matrix. -/
theorem diskTriple_boundary_apply (p : FiniteMatrixLoop C(X, ℂ)) (x : X) (t : I)
    (v : Fin p.size → ℂ) :
    p.diskTriple.boundary.linearEquiv
        ⟨(x, (complexDiskBoundaryHomeomorph.symm
          (Circle.exp (2 * Real.pi * (t : ℝ)))).val),
          (complexDiskBoundaryHomeomorph.symm
            (Circle.exp (2 * Real.pi * (t : ℝ)))).property⟩ v =
      (fun i j ↦ (p.loop t).val i j x) *ᵥ v := by
  /- Use the inverse law of the boundary homeomorphism, then circleMap_parameter.
  Evaluation of the matrix ring homomorphism and the standard matrix-to-linear-map
  equivalence gives precisely the displayed multiplication on column vectors. -/
  -- The stored boundary map evaluates the original unit matrix on the actual disk boundary.
  change (fun i j ↦ (p.circleMap (complexDiskBoundaryHomeomorph
    (complexDiskBoundaryHomeomorph.symm (Circle.exp (2 * Real.pi * (t : ℝ)))))).val
      i j x) *ᵥ v = _
  -- The boundary homeomorphism and positive parameter retain this exact loop value.
  rw [complexDiskBoundaryHomeomorph.apply_symm_apply, p.circleMap_parameter t]

/-- The relative difference class of the specified loop triple. -/
def diskRelativeClass (p : FiniteMatrixLoop C(X, ℂ)) :
    RelativeKZero.{_, 0} (complexDiskBoundaryProduct X) (isClosed_complexDiskBoundaryProduct X) :=
  p.diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X)

set_option backward.isDefEq.respectTransparency false in
/-- Karoubi III.1.6: equality of normalized disk classes is exactly stable based homotopy. -/
theorem diskRelativeClass_eq_iff_stablyHomotopic (p q : FiniteMatrixLoop C(X, ℂ)) :
    p.diskRelativeClass = q.diskRelativeClass ↔ p.StablyHomotopic q := by
  /- Stage 1: evaluate a stable based loop homotopy on the actual boundary cylinder.
  Identity blocks add identity triples, so the relative classes agree.
  Stage 2: conversely, equality of relative classes gives a stable commuting
  square with two actual added bundles. Add a complement of the first bundle
  and trivialize both stabilizing bundles using the same global square map.
  This gives two global coordinate maps intertwining the literally padded
  boundary matrices, with equal total sizes even when the base is empty.
  Stage 3: evaluate those coordinate maps along the affine disk contraction
  to the boundary point 1. The resulting based homotopy joins a constant
  conjugate of the first stabilized loop to the second. Stable conjugation
  invariance removes that conjugate, giving the required stable relation. -/

  classical
  let B := X × Complex.UnitClosedDisc
  let D := complexDiskBoundaryProduct X
  let T (n : ℕ) := FiniteBundle.trivial B n
  let (E F : B → Type) [TopologicalSpace (TotalSpace Unit E)]
      [TopologicalSpace (TotalSpace Unit F)] :
      TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) := sumTopology
  -- The same finite coordinate order identifies a direct sum with the block-size bundle.
  let join (n m : ℕ) : ((Fin n → ℂ) × (Fin m → ℂ)) ≃ₗ[ℂ] (Fin (n + m) → ℂ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℂ ℂ).symm.trans
      (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)
  let sumIso (n m : ℕ) : Iso ((T n).sum (T m)).Fiber (T (n + m)).Fiber :=
    { linearEquiv := fun _ ↦ join n m
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hp₁ : Continuous (fun z : TotalSpace Unit (T n).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have hp₂ : Continuous (fun z : TotalSpace Unit (T m).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have h₁ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            (z.proj, z.snd.1)) := hp₁.comp
          (continuous_sum_fst (E := (T n).Fiber) (F := (T m).Fiber))
        have h₂ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            (z.proj, z.snd.2)) := hp₂.comp
          (continuous_sum_snd (E := (T n).Fiber) (F := (T m).Fiber))
        have hv₁ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            z.snd.1) := h₁.snd
        have hv₂ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            z.snd.2) := h₂.snd
        exact (continuous_fst.comp h₁).prodMk
          ((join n m).toLinearMap.continuous_of_finiteDimensional.comp (hv₁.prodMk hv₂))
      continuous_symm := by
        apply continuous_induced_rng.mpr
        have hc : Continuous (fun z : TotalSpace Unit (T (n + m)).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have hv := (join n m).symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_snd.comp hc)
        apply Continuous.prodMk <;> apply continuous_induced_rng.mpr
        · exact (continuous_fst.comp hc).prodMk (continuous_fst.comp hv)
        · exact (continuous_fst.comp hc).prodMk (continuous_snd.comp hv) }
  -- Every boundary point has the original positive interval parameter.
  have hsurj : Function.Surjective
      (fun t : I ↦ Circle.exp (2 * Real.pi * (t : ℝ))) := by
    intro z
    let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
    have hz : e.symm z ∈ (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Set.Icc 0 (0 + 1) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ _
    obtain ⟨t, ht, he⟩ := hz
    refine ⟨⟨t, by simpa using ht⟩, ?_⟩
    have := congrArg e he
    simpa [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] using this
  have hcircle (p q : FiniteMatrixLoop C(X, ℂ)) (z : Circle) :
      (p.blockSum q).circleMap z = matrixUnitBlockSum (p.circleMap z) (q.circleMap z) := by
    obtain ⟨t, rfl⟩ := hsurj z
    simp only [FiniteMatrixLoop.circleMap_parameter]
    rfl
  have hblock (p q : FiniteMatrixLoop C(X, ℂ)) (z : D)
      (v : (Fin p.size → ℂ) × (Fin q.size → ℂ)) :
      join p.size q.size (p.diskBoundaryLinearEquiv z v.1, q.diskBoundaryLinearEquiv z v.2) =
        (p.blockSum q).diskBoundaryLinearEquiv z (join p.size q.size v) := by
    let c := complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩
    change join p.size q.size
      (((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)) *ᵥ v.1,
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)) *ᵥ v.2) =
      (((p.blockSum q).circleMap c).val.map
          (fun f ↦ f z.val.1)) *ᵥ (join p.size q.size v)
    rw [hcircle]
    have hmatrix : (matrixUnitBlockSum (p.circleMap c) (q.circleMap c)).val.map
        (fun f ↦ f z.val.1) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks
        ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map (fun f ↦ f z.val.1))
        0 0
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1))) := by
      ext i j
      change (Matrix.fromBlocks (p.circleMap c).val 0 0 (q.circleMap c).val
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) z.val.1 =
        Matrix.fromBlocks
          ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map
            (fun f ↦ f z.val.1)) 0 0
          ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
            (fun f ↦ f z.val.1)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> rfl
    erw [hmatrix]
    change _ = (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks
        ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map (fun f ↦ f z.val.1))
        0 0
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)))).mulVecLin (join p.size q.size v)
    rw [Matrix.mulVecLin_reindex]
    have hcancel (w : Fin p.size ⊕ Fin q.size → ℂ) :
        LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv
          (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm w) = w := by
      funext i
      simp
    dsimp only [join]
    simp only [LinearEquiv.trans_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcancel]
    apply congrArg (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)
    simp only [Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec]
    rcases v with ⟨v, w⟩
    funext i
    cases i <;> simp [Function.comp_def]
  -- Identity blocks are compared with the same ordered trivial-bundle coordinates.
  have hconstant (n : ℕ) (z : D) (w : Fin n → ℂ) :
      (constant (A := C(X, ℂ)) n).diskBoundaryLinearEquiv z w = w := by
    let c := complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩
    have hc : (constant (A := C(X, ℂ)) n).circleMap c = 1 := by
      obtain ⟨t, ht⟩ := hsurj c
      rw [← ht, circleMap_parameter]
      rfl
    change (Matrix.GeneralLinearGroup.toLin
      (Matrix.GeneralLinearGroup.map (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom
        ((constant (A := C(X, ℂ)) n).circleMap c))).toLinearEquiv w = w
    simp only [hc, map_one]
    rfl
  let frame (r : FiniteMatrixLoop C(X, ℂ)) (E : FiniteBundle B) (n : ℕ)
      (e : Iso E.Fiber (T n).Fiber) :
      Iso ((T r.size).sum E).Fiber (T (r.size + n)).Fiber :=
    ((Iso.refl (T r.size).Fiber).sum e).trans (sumIso r.size n)
  have hframe (r : FiniteMatrixLoop C(X, ℂ)) (E : FiniteBundle B) (n : ℕ)
      (e : Iso E.Fiber (T n).Fiber) (z : D) (v : ((T r.size).sum E).Fiber z.val) :
      (frame r E n e).linearEquiv z.val (r.diskBoundaryLinearEquiv z v.1, v.2) =
        (r.stabilize n).diskBoundaryLinearEquiv z
          ((frame r E n e).linearEquiv z.val v) := by
    change join r.size n (r.diskBoundaryLinearEquiv z v.1, e.linearEquiv z.val v.2) =
      (r.stabilize n).diskBoundaryLinearEquiv z
        (join r.size n (v.1, e.linearEquiv z.val v.2))
    have h := hblock r (constant (A := C(X, ℂ)) n) z
      (v.1, e.linearEquiv z.val v.2)
    rw [hconstant] at h
    exact h
  have hstabilize (r : FiniteMatrixLoop C(X, ℂ)) (n : ℕ) :
      (r.stabilize n).diskRelativeClass = r.diskRelativeClass := by
    let c := r.diskTriple.sum (BundleTriple.identity D (T n))
    have hi : c.IsIsomorphic (r.stabilize n).diskTriple := by
      refine ⟨frame r (T n) n (Iso.refl _), frame r (T n) n (Iso.refl _), ?_⟩
      intro z v
      change (frame r (T n) n (Iso.refl _)).linearEquiv z.val
        ((RelativeTriple.sum r.diskTriple.boundary
          (RelativeTriple.identity (T n).Fiber D)).linearEquiv z v) = _
      rw [RelativeTriple.sum_apply]
      exact hframe r (T n) n (Iso.refl _) z v
    change (r.stabilize n).diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X) = _
    calc
      _ = c.relativeClass (isClosed_complexDiskBoundaryProduct X) :=
        (c.relativeClass_eq_of_isIsomorphic (isClosed_complexDiskBoundaryProduct X) _ hi).symm
      _ = r.diskRelativeClass := by
        rw [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity, add_zero]
        rfl
  -- A based matrix homotopy is evaluated on the actual boundary cylinder.
  have hhomotopy {n : ℕ}
      (a b : Path (1 : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) 1)
      (hab : Path.Homotopic a b) :
      (⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).diskRelativeClass =
        (⟨n, b⟩ : FiniteMatrixLoop C(X, ℂ)).diskRelativeClass := by
    let r : FiniteMatrixLoop C(X, ℂ) := ⟨n, a⟩
    let s : FiniteMatrixLoop C(X, ℂ) := ⟨n, b⟩
    have hr : r.circleMap 1 = 1 := by simpa using r.circleMap_parameter 0
    have hs : s.circleMap 1 = 1 := by simpa using s.circleMap_parameter 0
    have hra : circleMapPath r.circleMap 1 hr = a := by
      apply Path.ext
      funext t
      exact r.circleMap_parameter t
    have hsb : circleMapPath s.circleMap 1 hs = b := by
      apply Path.ext
      funext t
      exact s.circleMap_parameter t
    have hab' : Path.Homotopic (circleMapPath r.circleMap 1 hr)
        (circleMapPath s.circleMap 1 hs) := by
      rwa [hra, hsb]
    obtain ⟨H⟩ := (circleMapPath_homotopic_iff r.circleMap s.circleMap 1 hr hs).mp hab'
    let R := Restrict (T n).Fiber D
    let projTime : I × D → D := Prod.snd
    let Z := TotalSpace Unit (projTime *ᵖ R)
    let c : I × D → (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ := fun z ↦
      H (z.1, complexDiskBoundaryHomeomorph ⟨z.2.val.2, z.2.property⟩)
    have hc : Continuous c := H.continuous.comp
      (continuous_fst.prodMk
        (complexDiskBoundaryHomeomorph.continuous.comp
          ((continuous_snd.comp (continuous_subtype_val.comp continuous_snd)).subtype_mk _)))
    have hbase : Continuous (fun z : Z ↦ z.proj) :=
      Pullback.continuous_proj Unit R projTime
    have hcoord : Continuous (fun z : TotalSpace Unit (T n).Fiber ↦
        (z.proj, z.snd)) := continuous_induced_dom
    have hvec : Continuous (fun z : Z ↦ z.snd) := hcoord.snd.comp
      ((Pullback.continuous_lift Unit (T n).Fiber
        (Subtype.val : D → B)).comp (Pullback.continuous_lift Unit R projTime))
    have hx : Continuous (fun z : Z ↦ z.proj.2.val.1) :=
      continuous_fst.comp (continuous_subtype_val.comp hbase.snd)
    have hmatrix (f : Z → Matrix (Fin n) (Fin n) C(X, ℂ)) (hf : Continuous f) :
        Continuous (fun z : Z ↦ fun i j ↦ f z i j z.proj.2.val.1) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro j
      exact ((continuous_apply j).comp ((continuous_apply i).comp hf)).eval hx
    have hforward := hmatrix (fun z ↦ (c z.proj).val)
      (Units.continuous_val.comp (hc.comp hbase))
    have hinverse := hmatrix (fun z ↦ (c z.proj).inv)
      (Units.continuous_coe_inv.comp (hc.comp hbase))
    have htotal (f : Z → Fin n → ℂ) (hf : Continuous f) :
        Continuous (fun z : Z ↦ (⟨z.proj, f z⟩ : Z)) := by
      rw [(inducing_pullbackTotalSpaceEmbedding Unit R projTime).continuous_iff]
      apply hbase.prodMk
      rw [(inducing_pullbackTotalSpaceEmbedding Unit (T n).Fiber
        (Subtype.val : D → B)).continuous_iff]
      exact hbase.snd.prodMk (continuous_induced_rng.mpr
        ((continuous_subtype_val.comp hbase.snd).prodMk hf))
    let K : IsoHomotopy r.diskTriple.boundary s.diskTriple.boundary :=
      { iso :=
          { linearEquiv z := (Matrix.GeneralLinearGroup.toLin
              (Matrix.GeneralLinearGroup.map
                (ContinuousMap.evalAlgHom ℂ ℂ z.2.val.1).toRingHom (c z))).toLinearEquiv
            continuous_total := by
              apply htotal
              change Continuous (fun z : Z ↦
                (fun i j ↦ (c z.proj).val i j z.proj.2.val.1) *ᵥ z.snd)
              exact hforward.matrix_mulVec hvec
            continuous_symm := by
              apply htotal
              change Continuous (fun z : Z ↦
                (fun i j ↦ (c z.proj).inv i j z.proj.2.val.1) *ᵥ z.snd)
              exact hinverse.matrix_mulVec hvec }
        map_zero := by
          intro z v
          change (Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.map
              (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom
                (H (0, complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩)))).toLinearEquiv v = _
          rw [H.apply_zero]
          rfl
        map_one := by
          intro z v
          change (Matrix.GeneralLinearGroup.toLin
            (Matrix.GeneralLinearGroup.map
              (ContinuousMap.evalAlgHom ℂ ℂ z.val.1).toRingHom
                (H (1, complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩)))).toLinearEquiv v = _
          rw [H.apply_one]
          rfl }
    exact bundleTriple_relativeClass_eq_of_homotopy (isClosed_complexDiskBoundaryProduct X)
      (T n) (T n) r.diskTriple.boundary s.diskTriple.boundary K
  -- A stable global square gives a based homotopy after removing its constant conjugation.
  have hiso {n m : ℕ} (hnm : n = m)
      (a : Path (1 : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) 1)
      (b : Path (1 : (Matrix (Fin m) (Fin m) C(X, ℂ))ˣ) 1)
      (eU eV : Iso (T n).Fiber (T m).Fiber)
      (hsquare : ∀ z : D, ∀ w : Fin n → ℂ,
        eV.linearEquiv z.val ((⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).diskBoundaryLinearEquiv z w) =
          (⟨m, b⟩ : FiniteMatrixLoop C(X, ℂ)).diskBoundaryLinearEquiv z
            (eU.linearEquiv z.val w)) :
      (⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).StablyHomotopic ⟨m, b⟩ := by
    subst m
    -- Obtain both matrices from the actual isomorphisms on the same trivial section module.
    let sec (e : Iso (T n).Fiber (T n).Fiber) :
        (Fin n → C(B, ℂ)) ≃ₗ[C(B, ℂ)] (Fin n → C(B, ℂ)) :=
      ((trivialSectionEquiv (X := B) n).trans e.sectionLinearEquiv).trans
        (trivialSectionEquiv (X := B) n).symm
    let matrix (e : Iso (T n).Fiber (T n).Fiber) :
        (Matrix (Fin n) (Fin n) C(B, ℂ))ˣ :=
      Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv (sec e))
    have hcoordinate (v : continuousSections (T n).Fiber) (i : Fin n) (z : B) :
        (trivialSectionEquiv n).symm v i z = v.val z i := by
      have h := congrArg (fun v' ↦ v'.val z i) ((trivialSectionEquiv n).apply_symm_apply v)
      exact (trivialSectionEquiv_apply n _ z i).symm.trans h
    have hsec (e : Iso (T n).Fiber (T n).Fiber) (v : Fin n → C(B, ℂ))
        (z : B) (i : Fin n) :
        sec e v i z = e.linearEquiv z (fun j ↦ v j z) i := by
      change (trivialSectionEquiv n).symm
        (e.sectionLinearEquiv ((trivialSectionEquiv n) v)) i z = _
      rw [hcoordinate, Iso.sectionLinearEquiv_apply]
      rfl
    have hmatrix (e : Iso (T n).Fiber (T n).Fiber) (z : B) (w : Fin n → ℂ) :
        (fun i j ↦ (matrix e).val i j z) *ᵥ w = e.linearEquiv z w := by
      have hmul (v : Fin n → C(B, ℂ)) : (matrix e).val *ᵥ v = sec e v :=
        congrArg (fun g : LinearMap.GeneralLinearGroup C(B, ℂ) (Fin n → C(B, ℂ)) ↦
          g.toLinearEquiv v) (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
            (LinearMap.GeneralLinearGroup.ofLinearEquiv (sec e)))
      have hentry (i j : Fin n) :
          (matrix e).val i j z = e.linearEquiv z (Pi.single j 1) i := by
        have hsingle : (fun k : Fin n ↦
            ((Pi.single j (1 : C(B, ℂ)) : Fin n → C(B, ℂ)) k) z) = Pi.single j (1 : ℂ) := by
          funext k
          by_cases hk : k = j
          · subst k
            simp
          · simp [hk]
        have h := congrArg (fun v ↦ v i z) (hmul (Pi.single j 1))
        rw [hsec, hsingle] at h
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
      have hmat : (fun i j ↦ (matrix e).val i j z) =
          LinearMap.toMatrix' (e.linearEquiv z).toLinearMap := by
        ext i j
        rw [LinearMap.toMatrix'_apply, hentry]
        rfl
      rw [hmat, LinearMap.toMatrix'_mulVec]
      rfl
    -- The affine disk contraction fixes its boundary point 1 at every time.
    let w : C(I, Complex.UnitClosedDisc) :=
      ⟨fun t ↦ (complexDiskBoundaryHomeomorph.symm
        (Circle.exp (2 * Real.pi * (t : ℝ)))).val,
        continuous_subtype_val.comp (complexDiskBoundaryHomeomorph.symm.continuous.comp
          (by fun_prop))⟩
    have hw0 : w 0 = 1 := by
      apply Subtype.ext
      change (Circle.exp (2 * Real.pi * ((0 : I) : ℝ)) : ℂ) = 1
      simp
    have hw1 : w 1 = 1 := by
      apply Subtype.ext
      change (Circle.exp (2 * Real.pi * ((1 : I) : ℝ)) : ℂ) = 1
      simp
    let disk (s t : I) : Complex.UnitClosedDisc := Complex.UnitClosedDisc.mk
      ((1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (w t : ℂ)) (by
        calc
          ‖(1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (w t : ℂ)‖ ≤
              ‖(1 - (s : ℝ)) • (1 : ℂ)‖ + ‖(s : ℝ) • (w t : ℂ)‖ := norm_add_le _ _
          _ = (1 - (s : ℝ)) + (s : ℝ) * ‖(w t : ℂ)‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (sub_nonneg.mpr s.property.2), abs_of_nonneg s.property.1,
              norm_one, mul_one]
          _ ≤ 1 := by nlinarith [(w t).norm_le_one, s.property.1, s.property.2])
    have hdisk : Continuous (fun st : I × I ↦ disk st.1 st.2) := by
      apply Continuous.subtype_mk
      exact ((continuous_const.sub continuous_fst.subtype_val).smul continuous_const).add
        (continuous_fst.subtype_val.smul (Complex.UnitClosedDisc.continuous_coe.comp
          (w.continuous.comp continuous_snd)))
    have hdisk0 (t : I) : disk 0 t = 1 := by
      apply Subtype.ext
      simp [disk]
    have hdisk1 (t : I) : disk 1 t = w t := by
      apply Subtype.ext
      simp [disk]
    have hdiskBase (s : I) : disk s 0 = 1 := by
      apply Subtype.ext
      change (1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (w 0 : ℂ) = 1
      rw [hw0]
      change (1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (1 : ℂ) = 1
      rw [← add_smul]
      simp
    have hdiskTarget (s : I) : disk s 1 = 1 := by
      apply Subtype.ext
      change (1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (w 1 : ℂ) = 1
      rw [hw1]
      change (1 - (s : ℝ)) • (1 : ℂ) + (s : ℝ) • (1 : ℂ) = 1
      rw [← add_smul]
      simp
    let rad (st : I × I) : C(X, B) :=
      ⟨fun x ↦ (x, disk st.1 st.2), continuous_id.prodMk continuous_const⟩
    have hrad : Continuous (fun stx : (I × I) × X ↦ rad stx.1 stx.2) :=
      continuous_snd.prodMk (hdisk.comp continuous_fst)
    let along (e : Iso (T n).Fiber (T n).Fiber) (st : I × I) :
        (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ :=
      Matrix.GeneralLinearGroup.map (ContinuousMap.compRightAlgHom ℂ ℂ (rad st)).toRingHom
        (matrix e)
    have halong (e : Iso (T n).Fiber (T n).Fiber) : Continuous (along e) := by
      apply Units.continuous_iff.mpr
      constructor
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact ((matrix e).val i j).continuous.comp hrad
      · apply continuous_pi
        intro i
        apply continuous_pi
        intro j
        apply ContinuousMap.continuous_of_continuous_uncurry
        exact ((matrix e).inv i j).continuous.comp hrad
    have halong_eq (e : Iso (T n).Fiber (T n).Fiber) (st st' : I × I)
        (h : disk st.1 st.2 = disk st'.1 st'.2) : along e st = along e st' := by
      apply Units.ext
      ext i j x
      change (matrix e).val i j (rad st x) = (matrix e).val i j (rad st' x)
      exact congrArg ((matrix e).val i j) (Prod.ext rfl h)
    let ev (x : X) : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ →*
        LinearMap.GeneralLinearGroup ℂ (Fin n → ℂ) :=
      Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
        (Matrix.GeneralLinearGroup.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)
    have haction (e : Iso (T n).Fiber (T n).Fiber) (st : I × I)
        (x : X) (v : Fin n → ℂ) :
        (ev x (along e st)).toLinearEquiv v = e.linearEquiv (rad st x) v := by
      change (fun i j ↦ (matrix e).val i j (rad st x)) *ᵥ v = _
      exact hmatrix e (rad st x) v
    have hunits (U V : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ)
        (h : ∀ x : X, ∀ v : Fin n → ℂ,
          (ev x U).toLinearEquiv v = (ev x V).toLinearEquiv v) : U = V := by
      apply Units.ext
      ext i j x
      have hv := congrArg (fun v : Fin n → ℂ ↦ v i) (h x (Pi.single j 1))
      change ((fun k l ↦ U.val k l x) *ᵥ Pi.single j 1) i =
        ((fun k l ↦ V.val k l x) *ᵥ Pi.single j 1) i at hv
      simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hv
    let boundary (x : X) (t : I) : D :=
      ⟨(x, w t), (complexDiskBoundaryHomeomorph.symm
        (Circle.exp (2 * Real.pi * (t : ℝ)))).property⟩
    have hprod (t : I) : along eV (1, t) * a t = b t * along eU (1, t) := by
      apply hunits
      intro x v
      simp only [map_mul, LinearMap.GeneralLinearGroup.toLinearEquiv_mul]
      change (ev x (along eV (1, t))).toLinearEquiv ((ev x (a t)).toLinearEquiv v) =
        (ev x (b t)).toLinearEquiv ((ev x (along eU (1, t))).toLinearEquiv v)
      rw [haction, haction]
      have hr : rad (1, t) x = (boundary x t).val := Prod.ext rfl (hdisk1 t)
      rw [hr]
      have ha := (⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).diskTriple_boundary_apply x t v
      have hb := (⟨n, b⟩ : FiniteMatrixLoop C(X, ℂ)).diskTriple_boundary_apply x t
        (eU.linearEquiv (boundary x t).val v)
      change (⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).diskBoundaryLinearEquiv
        (boundary x t) v = (ev x (a t)).toLinearEquiv v at ha
      change (⟨n, b⟩ : FiniteMatrixLoop C(X, ℂ)).diskBoundaryLinearEquiv
        (boundary x t) (eU.linearEquiv (boundary x t).val v) =
          (ev x (b t)).toLinearEquiv (eU.linearEquiv (boundary x t).val v) at hb
      rw [← ha, ← hb]
      exact hsquare (boundary x t) v
    have hbase (e : Iso (T n).Fiber (T n).Fiber) (s : I) :
        along e (s, 0) = along e (0, 0) :=
      halong_eq e (s, 0) (0, 0) ((hdiskBase s).trans (hdisk0 0).symm)
    have htarget (e : Iso (T n).Fiber (T n).Fiber) (s : I) :
        along e (s, 1) = along e (0, 0) :=
      halong_eq e (s, 1) (0, 0) ((hdiskTarget s).trans (hdisk0 0).symm)
    have hUV : along eV (0, 0) = along eU (0, 0) := by
      simpa only [a.source, b.source, hbase, mul_one, one_mul] using hprod 0
    let c : Path (1 : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) 1 :=
      { toFun t := along eV (0, 0) * a t * (along eV (0, 0))⁻¹
        continuous_toFun := (continuous_const.mul a.continuous).mul continuous_const
        source' := by simp
        target' := by simp }
    let H : c.Homotopy b :=
      { toFun st := along eV st * a st.2 * (along eU st)⁻¹
        continuous_toFun := ((halong eV).mul
          (a.continuous.comp continuous_snd)).mul (halong eU).inv
        map_zero_left := by
          intro t
          have hV := halong_eq eV (0, t) (0, 0) ((hdisk0 t).trans (hdisk0 0).symm)
          have hU := halong_eq eU (0, t) (0, 0) ((hdisk0 t).trans (hdisk0 0).symm)
          change along eV (0, t) * a t * (along eU (0, t))⁻¹ = c t
          rw [hV, hU, ← hUV]
          rfl
        map_one_left := by
          intro t
          change along eV (1, t) * a t * (along eU (1, t))⁻¹ = b t
          rw [hprod, mul_assoc, mul_inv_cancel, mul_one]
        prop' := by
          intro s t ht
          rcases ht with ht | ht
          · subst t
            change along eV (s, 0) * a 0 * (along eU (s, 0))⁻¹ = c 0
            simp only [a.source, c.source, hbase, hUV, mul_one, mul_inv_cancel]
          · have ht' : t = 1 := ht
            subst t
            change along eV (s, 1) * a 1 * (along eU (s, 1))⁻¹ = c 1
            simp only [a.target, c.target, htarget, hUV, mul_one, mul_inv_cancel] }
    have hc : (⟨n, c⟩ : FiniteMatrixLoop C(X, ℂ)).StablyHomotopic ⟨n, b⟩ := by
      refine ⟨0, 0, rfl, ⟨{
        toFun st := matrixUnitBlockSum (H st) (1 : (Matrix (Fin 0) (Fin 0) C(X, ℂ))ˣ)
        continuous_toFun := (continuous_matrixUnitBlockSum n 0).comp
          (H.continuous.prodMk continuous_const)
        map_zero_left := ?_
        map_one_left := ?_
        prop' := ?_ }⟩⟩
      · intro t
        change matrixUnitBlockSum (H (0, t)) 1 = matrixUnitBlockSum (c t) 1
        rw [H.apply_zero]
        rfl
      · intro t
        change matrixUnitBlockSum (H (1, t)) 1 = matrixUnitBlockSum (b t) 1
        rw [H.apply_one]
        rfl
      · intro s t ht
        rcases ht with ht | ht
        · subst t
          change matrixUnitBlockSum (H (s, 0)) 1 = matrixUnitBlockSum (c 0) 1
          rw [H.source, c.source]
        · have ht' : t = 1 := ht
          subst t
          change matrixUnitBlockSum (H (s, 1)) 1 = matrixUnitBlockSum (c 1) 1
          rw [H.target, c.target]
    exact stablyHomotopic_equivalence.trans
      (stablyHomotopic_of_conjugate a c (along eV (0, 0)) (fun _ ↦ rfl)) hc
  -- Size transports retain the same matrices, and introduce no new stable relation.
  let P (n : ℕ) := Path (1 : (Matrix (Fin n) (Fin n) C(X, ℂ))ˣ) 1
  have hcast {n m : ℕ} (h : n = m) (a : P n) :
      (⟨n, a⟩ : FiniteMatrixLoop C(X, ℂ)).diskRelativeClass =
        (⟨m, cast (congrArg P h) a⟩ : FiniteMatrixLoop C(X, ℂ)).diskRelativeClass := by
    subst m
    rfl
  constructor
  · intro he
    -- Retain the two actual stabilizing bundles and their original commuting square.
    obtain ⟨E, F, u, v, huv⟩ :=
      (p.diskTriple.relativeClass_eq_iff_stable
        (isClosed_complexDiskBoundaryProduct X) q.diskTriple).mp he
    let : IsFiniteRank E.Fiber := E.isFiniteRank
    obtain ⟨c, ⟨e⟩⟩ := exists_complement_bundle (E := E.Fiber)
    let := IdempotentMatrix.fiberTotalSpaceTopology c.complement
    let := IdempotentMatrix.isFiniteRank_fiber c.complement
    let G := FiniteBundle.ofFamily (fun z ↦ c.complement.fiber z)
    let C := G.sum (T q.size)
    let nP := c.size + q.size
    let nQ := p.size + c.size
    -- Trivialize both added bundles using this complement and the same global u.
    -- Moving the q coordinates through u avoids a fiber-rank argument, even when X is empty.
    let eE : Iso (E.sum C).Fiber (T nP).Fiber :=
      ((E.sumAssocIso G (T q.size)).symm.trans
        (e.sum (Iso.refl (T q.size).Fiber))).trans (sumIso c.size q.size)
    let turn : Iso (F.sum C).Fiber (((T q.size).sum F).sum G).Fiber :=
      (((F.sumAssocIso G (T q.size)).symm.trans
        (sumCommIso : Iso ((F.sum G).sum (T q.size)).Fiber
          ((T q.size).sum (F.sum G)).Fiber)).trans
            ((T q.size).sumAssocIso F G).symm)
    let eF : Iso (F.sum C).Fiber (T nQ).Fiber :=
      ((turn.trans (u.symm.sum (Iso.refl G.Fiber))).trans
        (((T p.size).sumAssocIso E G).trans
          ((Iso.refl (T p.size).Fiber).sum e))).trans (sumIso p.size c.size)
    let nestedFrame (r : FiniteMatrixLoop C(X, ℂ)) (J K : FiniteBundle B) (n : ℕ)
        (f : Iso (J.sum K).Fiber (T n).Fiber) :
        Iso (((T r.size).sum J).sum K).Fiber (T (r.size + n)).Fiber :=
      ((T r.size).sumAssocIso J K).trans (frame r (J.sum K) n f)
    have hnested (r : FiniteMatrixLoop C(X, ℂ)) (J K : FiniteBundle B) (n : ℕ)
        (f : Iso (J.sum K).Fiber (T n).Fiber) (z : D)
        (w : (((T r.size).sum J).sum K).Fiber z.val) :
        (nestedFrame r J K n f).linearEquiv z.val
            ((r.diskBoundaryLinearEquiv z w.1.1, w.1.2), w.2) =
          (r.stabilize n).diskBoundaryLinearEquiv z
            ((nestedFrame r J K n f).linearEquiv z.val w) := by
      change (frame r (J.sum K) n f).linearEquiv z.val
        (((T r.size).sumAssocIso J K).linearEquiv z.val
          ((r.diskBoundaryLinearEquiv z w.1.1, w.1.2), w.2)) =
        (r.stabilize n).diskBoundaryLinearEquiv z
          ((frame r (J.sum K) n f).linearEquiv z.val
            (((T r.size).sumAssocIso J K).linearEquiv z.val w))
      erw [FiniteBundle.sumAssocIso_apply, FiniteBundle.sumAssocIso_apply]
      exact hframe r (J.sum K) n f z (w.1.1, w.1.2, w.2)
    let S := nestedFrame p E C nP eE
    let Q := nestedFrame q F C nQ eF
    let cP := (p.diskTriple.sum (BundleTriple.identity D E)).sum (BundleTriple.identity D C)
    let cQ := (q.diskTriple.sum (BundleTriple.identity D F)).sum (BundleTriple.identity D C)
    have hS (z : D) (w : cP.source.Fiber z.val) :
        S.linearEquiv z.val (cP.boundary.linearEquiv z w) =
          (p.stabilize nP).diskBoundaryLinearEquiv z (S.linearEquiv z.val w) := by
      change S.linearEquiv z.val
        ((RelativeTriple.sum
          (RelativeTriple.sum p.diskTriple.boundary (RelativeTriple.identity E.Fiber D))
          (RelativeTriple.identity C.Fiber D)).linearEquiv z w) = _
      rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply]
      exact hnested p E C nP eE z w
    have hQ (z : D) (w : cQ.source.Fiber z.val) :
        Q.linearEquiv z.val (cQ.boundary.linearEquiv z w) =
          (q.stabilize nQ).diskBoundaryLinearEquiv z (Q.linearEquiv z.val w) := by
      change Q.linearEquiv z.val
        ((RelativeTriple.sum
          (RelativeTriple.sum q.diskTriple.boundary (RelativeTriple.identity F.Fiber D))
          (RelativeTriple.identity C.Fiber D)).linearEquiv z w) = _
      rw [RelativeTriple.sum_apply, RelativeTriple.sum_apply]
      exact hnested q F C nQ eF z w
    have huvC (z : D) (w : cP.source.Fiber z.val) :
        (v.sum (Iso.refl C.Fiber)).linearEquiv z.val (cP.boundary.linearEquiv z w) =
          cQ.boundary.linearEquiv z ((u.sum (Iso.refl C.Fiber)).linearEquiv z.val w) := by
      change ((v.sum (Iso.refl C.Fiber)).linearEquiv z.val
        ((RelativeTriple.sum
          (RelativeTriple.sum p.diskTriple.boundary (RelativeTriple.identity E.Fiber D))
          (RelativeTriple.identity C.Fiber D)).linearEquiv z w)) =
        (RelativeTriple.sum
          (RelativeTriple.sum q.diskTriple.boundary (RelativeTriple.identity F.Fiber D))
          (RelativeTriple.identity C.Fiber D)).linearEquiv z
            ((u.sum (Iso.refl C.Fiber)).linearEquiv z.val w)
      rw [RelativeTriple.sum_apply]
      conv_rhs => rw [RelativeTriple.sum_apply]
      change (v.linearEquiv z.val
        (((p.diskTriple.sum (BundleTriple.identity D E)).boundary).linearEquiv z w.1), w.2) =
        (((q.diskTriple.sum (BundleTriple.identity D F)).boundary).linearEquiv z
          (u.linearEquiv z.val w.1), w.2)
      exact Prod.ext (huv z w.1) rfl
    -- These global coordinate maps intertwine the original, literally padded boundary matrices.
    let U := S.symm.trans ((u.sum (Iso.refl C.Fiber)).trans Q)
    let V := S.symm.trans ((v.sum (Iso.refl C.Fiber)).trans Q)
    have hcoordinates (z : D) (w : Fin (p.size + nP) → ℂ) :
        V.linearEquiv z.val ((p.stabilize nP).diskBoundaryLinearEquiv z w) =
          (q.stabilize nQ).diskBoundaryLinearEquiv z (U.linearEquiv z.val w) := by
      have hs : (S.linearEquiv z.val).symm
          ((p.stabilize nP).diskBoundaryLinearEquiv z w) =
            cP.boundary.linearEquiv z ((S.linearEquiv z.val).symm w) := by
        have ht := congrArg (S.linearEquiv z.val).symm
          (hS z ((S.linearEquiv z.val).symm w))
        simp only [LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply] at ht
        exact ht.symm
      change Q.linearEquiv z.val
        ((v.sum (Iso.refl C.Fiber)).linearEquiv z.val
          ((S.linearEquiv z.val).symm ((p.stabilize nP).diskBoundaryLinearEquiv z w))) =
        (q.stabilize nQ).diskBoundaryLinearEquiv z
          (Q.linearEquiv z.val ((u.sum (Iso.refl C.Fiber)).linearEquiv z.val
            ((S.linearEquiv z.val).symm w)))
      rw [hs]
      exact (congrArg (Q.linearEquiv z.val)
        (huvC z ((S.linearEquiv z.val).symm w))).trans
          (hQ z ((u.sum (Iso.refl C.Fiber)).linearEquiv z.val
            ((S.linearEquiv z.val).symm w)))
    have hsize : p.size + nP = q.size + nQ := by
      dsimp only [nP, nQ]
      omega
    have hstable : (p.stabilize nP).StablyHomotopic (q.stabilize nQ) :=
      hiso hsize (p.stabilize nP).loop (q.stabilize nQ).loop U V hcoordinates
    apply (stableMatrixLoopClass_eq_iff p q).mp
    calc
      stableMatrixLoopClass p = stableMatrixLoopClass (p.stabilize nP) :=
        (stableMatrixLoopClass_stabilize p nP).symm
      _ = stableMatrixLoopClass (q.stabilize nQ) :=
        (stableMatrixLoopClass_eq_iff _ _).mpr hstable
      _ = stableMatrixLoopClass q := stableMatrixLoopClass_stabilize q nQ
  · rintro ⟨k, l, h, H⟩
    calc
      p.diskRelativeClass = (p.stabilize k).diskRelativeClass := (hstabilize p k).symm
      _ = (⟨q.size + l, cast (congrArg P h) (p.stabilize k).loop⟩ :
          FiniteMatrixLoop C(X, ℂ)).diskRelativeClass := hcast h (p.stabilize k).loop
      _ = (q.stabilize l).diskRelativeClass :=
        hhomotopy (cast (congrArg P h) (p.stabilize k).loop) (q.stabilize l).loop H
      _ = q.diskRelativeClass := hstabilize q l

/-- Karoubi III.1.6: every disk-pair class has a normalized finite matrix-loop representative. -/
theorem diskRelativeClass_surjective :
    Function.Surjective (diskRelativeClass (X := X)) := by
  /- Stage 1: represent the relative class by a geometric triple. Contract the
  disk to 1; bundle homotopy invariance identifies its source and target with
  pullbacks from X. The boundary value at 1 identifies the two base bundles.
  Stage 2: add a complement over X, pull it back to the disk and trivialize
  both stabilized bundles. The same boundary automorphism is represented by
  an invertible matrix on the actual trivial section module.
  Stage 3: evaluate this matrix along the positive circle parameter to get
  a continuous unit path V with V 1 = V 0. The loop V t * (V 0)⁻¹ is based
  at the identity. Its normalization is a global change of source frame,
  so the original stabilized triple and this disk triple have the same class.
  Empty bases and locally varying ranks are allowed. -/
  classical
  let D := X × Complex.UnitClosedDisc
  let (J K : X → Type) [TopologicalSpace (TotalSpace Unit J)]
      [TopologicalSpace (TotalSpace Unit K)] :
      TopologicalSpace (TotalSpace Unit (J ×ᵇ K)) := sumTopology
  let (J K : D → Type) [TopologicalSpace (TotalSpace Unit J)]
      [TopologicalSpace (TotalSpace Unit K)] :
      TopologicalSpace (TotalSpace Unit (J ×ᵇ K)) := sumTopology
  let A := complexDiskBoundaryProduct X
  have hA : IsClosed A := isClosed_complexDiskBoundaryProduct X
  let proj : C(D, X) := ContinuousMap.fst
  let z : C(X, D) :=
    ⟨fun x ↦ (x, 1), continuous_id.prodMk continuous_const⟩
  let i : C(A, D) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj (x : X) : z x ∈ A := by
    change ‖(1 : ℂ)‖ = 1
    exact norm_one
  let j : C(X, A) := ⟨fun x ↦ ⟨z x, hj x⟩, z.continuous.subtype_mk hj⟩
  -- The compact disk contraction compares actual bundles, before any K-class calculation.
  let H : ContinuousMap.Homotopy (ContinuousMap.id D) (z.comp proj) :=
    { toFun tw := (tw.2.1, Complex.UnitClosedDisc.mk
        ((1 - (tw.1 : ℝ)) • (tw.2.2 : ℂ) + (tw.1 : ℝ) • (1 : ℂ)) (by
          calc
            ‖(1 - (tw.1 : ℝ)) • (tw.2.2 : ℂ) + (tw.1 : ℝ) • (1 : ℂ)‖ ≤
                ‖(1 - (tw.1 : ℝ)) • (tw.2.2 : ℂ)‖ + ‖(tw.1 : ℝ) • (1 : ℂ)‖ :=
              norm_add_le _ _
            _ = (1 - (tw.1 : ℝ)) * ‖(tw.2.2 : ℂ)‖ + (tw.1 : ℝ) := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (sub_nonneg.mpr tw.1.property.2),
                abs_of_nonneg tw.1.property.1, norm_one, mul_one]
            _ ≤ 1 := by
              nlinarith [tw.2.2.norm_le_one, tw.1.property.1, tw.1.property.2]) )
      continuous_toFun := continuous_snd.fst.prodMk (by
        apply Continuous.subtype_mk
        exact ((continuous_const.sub continuous_fst.subtype_val).smul
          (Complex.UnitClosedDisc.continuous_coe.comp continuous_snd.snd)).add
            (continuous_fst.subtype_val.smul continuous_const))
      map_zero_left := by
        intro w
        refine Prod.ext ?_ ?_
        · rfl
        · apply Subtype.ext
          simp
      map_one_left := by
        intro w
        refine Prod.ext ?_ ?_
        · rfl
        · apply Subtype.ext
          simp [z, proj] }
  let pullIso (P : FiniteBundle D) : Iso P.Fiber ((P.pullback z).pullback proj).Fiber :=
    (((pullbackIdIso (E := P.Fiber)).symm.trans
      (nonempty_pullback_iso_of_homotopy (V := P.Fiber)
        (ContinuousMap.id D) (z.comp proj) H).some).trans
          (pullbackCompIso (E := P.Fiber) z proj).symm)
  intro u
  obtain ⟨a, ha⟩ := bundleTriple_relativeClass_surjective A hA u
  let E := a.source.pullback z
  let F := a.target.pullback z
  let : IsFiniteRank E.Fiber := E.isFiniteRank
  let : IsFiniteRank F.Fiber := F.isFiniteRank
  let s₀ : Iso a.source.Fiber (E.pullback proj).Fiber := pullIso a.source
  let t₀ : Iso a.target.Fiber (F.pullback proj).Fiber := pullIso a.target
  -- The boundary at the specified point 1 identifies the two base bundles.
  let b : Iso E.Fiber F.Fiber :=
    (((pullbackCompIso (E := a.source.Fiber) i j).symm.trans
      (Iso.pullback j a.boundary)).trans (pullbackCompIso (E := a.target.Fiber) i j))
  obtain ⟨p, ⟨e⟩⟩ := exists_complement_bundle (E := E.Fiber)
  let := IdempotentMatrix.fiberTotalSpaceTopology p.complement
  let := IdempotentMatrix.isFiniteRank_fiber p.complement
  let G := FiniteBundle.ofFamily (fun x ↦ p.complement.fiber x)
  let T := FiniteBundle.trivial D p.size
  let Gproj := G.pullback proj
  -- Pullback and direct sum have their original topologies; the comparison fixes vectors.
  let compare : Iso ((E.sum G).pullback proj).Fiber ((E.pullback proj).sum Gproj).Fiber :=
    { linearEquiv w := LinearEquiv.refl ℂ (E.Fiber w.1 × G.Fiber w.1)
      continuous_total := by
        apply continuous_induced_rng.mpr
        apply Continuous.prodMk
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit E.Fiber proj).continuous_iff]
          exact (Pullback.continuous_proj Unit (E.sum G).Fiber proj).prodMk
            (continuous_sum_fst.comp (Pullback.continuous_lift Unit (E.sum G).Fiber proj))
        · rw [(inducing_pullbackTotalSpaceEmbedding Unit G.Fiber proj).continuous_iff]
          exact (Pullback.continuous_proj Unit (E.sum G).Fiber proj).prodMk
            (continuous_sum_snd.comp (Pullback.continuous_lift Unit (E.sum G).Fiber proj))
      continuous_symm := by
        rw [(inducing_pullbackTotalSpaceEmbedding Unit (E.sum G).Fiber proj).continuous_iff]
        apply ((Pullback.continuous_proj Unit E.Fiber proj).comp continuous_sum_fst).prodMk
        apply continuous_induced_rng.mpr
        exact ((Pullback.continuous_lift Unit E.Fiber proj).comp continuous_sum_fst).prodMk
          ((Pullback.continuous_lift Unit G.Fiber proj).comp continuous_sum_snd) }
  let frame : Iso ((E.pullback proj).sum Gproj).Fiber T.Fiber :=
    (compare.symm.trans (e.pullback proj)).trans (pullbackTrivialIso proj p.size)
  let s : Iso (a.source.sum Gproj).Fiber T.Fiber :=
    (s₀.sum (Iso.refl Gproj.Fiber)).trans frame
  let t : Iso (a.target.sum Gproj).Fiber T.Fiber :=
    ((t₀.sum (Iso.refl Gproj.Fiber)).trans
      ((b.symm.pullback proj).sum (Iso.refl Gproj.Fiber))).trans frame
  let c := a.sum (BundleTriple.identity A Gproj)
  let δ : RelativeTriple T.Fiber T.Fiber A :=
    (((s.restrict A).symm.trans c.boundary).trans (t.restrict A))
  let q := pullbackTrivialIso i p.size
  let β : Iso (FiniteBundle.trivial A p.size).Fiber (FiniteBundle.trivial A p.size).Fiber :=
    (q.symm.trans δ).trans q
  -- The matrix represents this same boundary automorphism on its actual section module.
  let eSec := ((trivialSectionEquiv (X := A) p.size).trans β.sectionLinearEquiv).trans
    (trivialSectionEquiv (X := A) p.size).symm
  let U : (Matrix (Fin p.size) (Fin p.size) C(A, ℂ))ˣ :=
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv eSec)
  have hcoordinate (v : continuousSections (FiniteBundle.trivial A p.size).Fiber)
      (k : Fin p.size) (w : A) :
      (trivialSectionEquiv p.size).symm v k w = v.val w k := by
    have h := congrArg (fun v' ↦ v'.val w k)
      ((trivialSectionEquiv p.size).apply_symm_apply v)
    exact (trivialSectionEquiv_apply p.size _ w k).symm.trans h
  have hSec (v : Fin p.size → C(A, ℂ)) (w : A) (k : Fin p.size) :
      eSec v k w = β.linearEquiv w (fun l ↦ v l w) k := by
    change (trivialSectionEquiv p.size).symm
      (β.sectionLinearEquiv ((trivialSectionEquiv p.size) v)) k w = _
    rw [hcoordinate, Iso.sectionLinearEquiv_apply]
    rfl
  have hU (v : Fin p.size → C(A, ℂ)) : U.val *ᵥ v = eSec v := by
    exact congrArg (fun g : LinearMap.GeneralLinearGroup C(A, ℂ)
      (Fin p.size → C(A, ℂ)) ↦ g.toLinearEquiv v)
      (Matrix.GeneralLinearGroup.toLin.apply_symm_apply
        (LinearMap.GeneralLinearGroup.ofLinearEquiv eSec))
  have hUentry (w : A) (k l : Fin p.size) :
      U.val k l w = β.linearEquiv w (Pi.single l 1) k := by
    have hsingle : (fun j : Fin p.size ↦
        ((Pi.single l (1 : C(A, ℂ)) : Fin p.size → C(A, ℂ)) j) w) =
        Pi.single l (1 : ℂ) := by
      funext j
      by_cases hj : j = l
      · subst j
        simp
      · simp [hj]
    have h := congrArg (fun v ↦ v k w) (hU (Pi.single l 1))
    rw [hSec, hsingle] at h
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h
  have hUaction (w : A) (v : Fin p.size → ℂ) :
      (fun k l ↦ U.val k l w) *ᵥ v = β.linearEquiv w v := by
    have hm : (fun k l ↦ U.val k l w) =
        LinearMap.toMatrix' (β.linearEquiv w).toLinearMap := by
      ext k l
      rw [LinearMap.toMatrix'_apply, hUentry]
      rfl
    rw [hm, LinearMap.toMatrix'_mulVec]
    rfl
  -- Keep the positive circle parameter, then normalize only its base-point value.
  let w : C(I, Complex.UnitClosedDisc) :=
    ⟨fun t ↦ (complexDiskBoundaryHomeomorph.symm
      (Circle.exp (2 * Real.pi * (t : ℝ)))).val,
      continuous_subtype_val.comp (complexDiskBoundaryHomeomorph.symm.continuous.comp
        (by fun_prop))⟩
  let r (t : I) : C(X, A) :=
    ⟨fun x ↦ ⟨(x, w t), (complexDiskBoundaryHomeomorph.symm
      (Circle.exp (2 * Real.pi * (t : ℝ)))).property⟩,
      (continuous_id.prodMk continuous_const).subtype_mk _⟩
  have hr : Continuous (fun tx : I × X ↦ r tx.1 tx.2) :=
    (continuous_snd.prodMk (w.continuous.comp continuous_fst)).subtype_mk _
  have hw0 : w 0 = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * ((0 : I) : ℝ)) : ℂ) = 1
    simp
  have hw1 : w 1 = 1 := by
    apply Subtype.ext
    change (Circle.exp (2 * Real.pi * ((1 : I) : ℝ)) : ℂ) = 1
    simp
  let V (t : I) : (Matrix (Fin p.size) (Fin p.size) C(X, ℂ))ˣ :=
    Matrix.GeneralLinearGroup.map (ContinuousMap.compRightAlgHom ℂ ℂ (r t)).toRingHom U
  have hV : Continuous V := by
    apply Units.continuous_iff.mpr
    constructor
    · apply continuous_pi
      intro k
      apply continuous_pi
      intro l
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (U.val k l).continuous.comp hr
    · apply continuous_pi
      intro k
      apply continuous_pi
      intro l
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (U.inv k l).continuous.comp hr
  have hV1 : V 1 = V 0 := by
    apply Units.ext
    ext k l x
    change U.val k l (r 1 x) = U.val k l (r 0 x)
    apply congrArg (U.val k l)
    apply Subtype.ext
    exact Prod.ext rfl (hw1.trans hw0.symm)
  let loop : FiniteMatrixLoop C(X, ℂ) :=
    { size := p.size
      loop :=
        { toFun := fun t ↦ V t * (V 0)⁻¹
          continuous_toFun := hV.mul continuous_const
          source' := by simp
          target' := by rw [hV1]; simp } }
  let ev (x : X) : (Matrix (Fin p.size) (Fin p.size) C(X, ℂ))ˣ →*
      LinearMap.GeneralLinearGroup ℂ (Fin p.size → ℂ) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (Matrix.GeneralLinearGroup.map (ContinuousMap.evalAlgHom ℂ ℂ x).toRingHom)
  have hVapply (t : I) (x : X) :
      (ev x (V t)).toLinearEquiv = β.linearEquiv (r t x) := by
    apply LinearEquiv.ext
    intro v
    change (fun k l ↦ U.val k l (r t x)) *ᵥ v = _
    exact hUaction (r t x) v
  have hloop (t : I) (x : X) (v : Fin p.size → ℂ) :
      (ev x (loop.loop t)).toLinearEquiv v =
        β.linearEquiv (r t x) ((β.linearEquiv (r 0 x)).symm v) := by
    change (ev x (V t * (V 0)⁻¹)).toLinearEquiv v = _
    rw [map_mul, map_inv, LinearMap.GeneralLinearGroup.toLinearEquiv_mul,
      LinearMap.GeneralLinearGroup.toLinearEquiv_inv, hVapply, hVapply]
    rfl
  let k : C(D, A) := j.comp proj
  let qk := pullbackTrivialIso k p.size
  let B : Iso T.Fiber T.Fiber :=
    (qk.symm.trans (Iso.pullback k β)).trans qk
  have hq (a : A) (v : Fin p.size → ℂ) : q.linearEquiv a v = v :=
    pullbackTrivialIso_apply i p.size a v
  have hqi (a : A) (v : Fin p.size → ℂ) : (q.linearEquiv a).symm v = v := by
    have h := (q.linearEquiv a).symm_apply_apply v
    rw [hq] at h
    exact h
  have hβ (a : A) (v : Fin p.size → ℂ) :
      β.linearEquiv a v = t.linearEquiv a.val
        (c.boundary.linearEquiv a ((s.linearEquiv a.val).symm v)) := by
    change q.linearEquiv a
      (δ.linearEquiv a ((q.linearEquiv a).symm v)) = _
    erw [hq, hqi]
    rfl
  have hB (a : D) : B.linearEquiv a = β.linearEquiv (k a) := by
    apply LinearEquiv.ext
    intro v
    have hqk (v : Fin p.size → ℂ) : qk.linearEquiv a v = v :=
      pullbackTrivialIso_apply k p.size a v
    have hqki (v : Fin p.size → ℂ) : (qk.linearEquiv a).symm v = v := by
      have h := (qk.linearEquiv a).symm_apply_apply v
      rw [hqk] at h
      exact h
    change qk.linearEquiv a
      (β.linearEquiv (k a) ((qk.linearEquiv a).symm v)) = _
    rw [hqk, hqki]
  have hbase (a : D) : r 0 a.1 = k a := by
    apply Subtype.ext
    exact Prod.ext rfl hw0
  -- Every original boundary point has this same positive interval parameter.
  have hsurj : Function.Surjective
      (fun t : I ↦ Circle.exp (2 * Real.pi * (t : ℝ))) := by
    intro a
    let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
    have ha : e.symm a ∈
        (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Set.Icc 0 (0 + 1) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ _
    obtain ⟨t, ht, he⟩ := ha
    refine ⟨⟨t, by simpa using ht⟩, ?_⟩
    have h := congrArg e he
    simpa [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] using h
  have hboundary (a : A) (v : Fin p.size → ℂ) :
      loop.diskBoundaryLinearEquiv a v =
        β.linearEquiv a ((B.linearEquiv a.val).symm v) := by
    obtain ⟨t, ht⟩ := hsurj
      (complexDiskBoundaryHomeomorph ⟨a.val.2, a.property⟩)
    change Circle.exp (2 * Real.pi * (t : ℝ)) =
      complexDiskBoundaryHomeomorph ⟨a.val.2, a.property⟩ at ht
    have hrt : r t a.val.1 = a := by
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · rfl
      · change (complexDiskBoundaryHomeomorph.symm
          (Circle.exp (2 * Real.pi * (t : ℝ)))).val = a.val.2
        rw [ht, complexDiskBoundaryHomeomorph.symm_apply_apply]
    change (ev a.val.1 (loop.circleMap
      (complexDiskBoundaryHomeomorph ⟨a.val.2, a.property⟩))).toLinearEquiv v = _
    rw [← ht, loop.circleMap_parameter, hloop, hrt, hbase, hB]
  -- The normalization is an actual global change of source frame, not a changed K class.
  have hc : c.IsIsomorphic loop.diskTriple := by
    refine ⟨s.trans B, t, ?_⟩
    intro a v
    change t.linearEquiv a.val (c.boundary.linearEquiv a v) =
      loop.diskBoundaryLinearEquiv a (B.linearEquiv a.val (s.linearEquiv a.val v))
    rw [hboundary, LinearEquiv.symm_apply_apply, hβ, LinearEquiv.symm_apply_apply]
  refine ⟨loop, ?_⟩
  change loop.diskTriple.relativeClass hA = u
  calc
    _ = c.relativeClass hA :=
      (BundleTriple.relativeClass_eq_of_isIsomorphic hA c loop.diskTriple hc).symm
    _ = a.relativeClass hA := by
      change (a.sum (BundleTriple.identity A Gproj)).relativeClass hA = _
      rw [BundleTriple.relativeClass_sum, BundleTriple.relativeClass_identity, add_zero]
    _ = u := ha

/-- The loop-to-triple construction respects the specified zero and block-sum operations. -/
theorem diskRelativeClass_additive :
    (constant (A := C(X, ℂ)) 0).diskRelativeClass = 0 ∧
      ∀ p q : FiniteMatrixLoop C(X, ℂ),
        (p.blockSum q).diskRelativeClass = p.diskRelativeClass + q.diskRelativeClass := by
  /- The zero-size loop gives the zero-rank identity triple. For block sum, the
  fixed finite-coordinate reindexing identifies the disk triple with the direct
  sum of the two original triples, including their boundary matrices. Apply the
  identity and direct-sum formulas for the existing relative difference class. -/
  classical
  let B := X × Complex.UnitClosedDisc
  let D := complexDiskBoundaryProduct X
  let T (n : ℕ) := FiniteBundle.trivial B n
  let (E F : B → Type) [TopologicalSpace (TotalSpace Unit E)]
      [TopologicalSpace (TotalSpace Unit F)] :
      TopologicalSpace (TotalSpace Unit (E ×ᵇ F)) := sumTopology
  -- The same finite coordinate order identifies a direct sum with the block-size bundle.
  let join (n m : ℕ) : ((Fin n → ℂ) × (Fin m → ℂ)) ≃ₗ[ℂ] (Fin (n + m) → ℂ) :=
    (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin m) ℂ ℂ).symm.trans
      (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)
  let sumIso (n m : ℕ) : Iso ((T n).sum (T m)).Fiber (T (n + m)).Fiber :=
    { linearEquiv := fun _ ↦ join n m
      continuous_total := by
        apply continuous_induced_rng.mpr
        have hp₁ : Continuous (fun z : TotalSpace Unit (T n).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have hp₂ : Continuous (fun z : TotalSpace Unit (T m).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have h₁ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            (z.proj, z.snd.1)) := hp₁.comp
          (continuous_sum_fst (E := (T n).Fiber) (F := (T m).Fiber))
        have h₂ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            (z.proj, z.snd.2)) := hp₂.comp
          (continuous_sum_snd (E := (T n).Fiber) (F := (T m).Fiber))
        have hv₁ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            z.snd.1) := h₁.snd
        have hv₂ : Continuous (fun z : TotalSpace Unit ((T n).sum (T m)).Fiber ↦
            z.snd.2) := h₂.snd
        exact (continuous_fst.comp h₁).prodMk
          ((join n m).toLinearMap.continuous_of_finiteDimensional.comp (hv₁.prodMk hv₂))
      continuous_symm := by
        apply continuous_induced_rng.mpr
        have hc : Continuous (fun z : TotalSpace Unit (T (n + m)).Fiber ↦
            (z.proj, z.snd)) := continuous_induced_dom
        have hv := (join n m).symm.toLinearMap.continuous_of_finiteDimensional.comp
          (continuous_snd.comp hc)
        apply Continuous.prodMk <;> apply continuous_induced_rng.mpr
        · exact (continuous_fst.comp hc).prodMk (continuous_fst.comp hv)
        · exact (continuous_fst.comp hc).prodMk (continuous_snd.comp hv) }
  -- Every boundary point has the original positive interval parameter.
  have hsurj : Function.Surjective
      (fun t : I ↦ Circle.exp (2 * Real.pi * (t : ℝ))) := by
    intro z
    let e := AddCircle.homeomorphCircle (by norm_num : (1 : ℝ) ≠ 0)
    have hz : e.symm z ∈ (fun t : ℝ ↦ (t : AddCircle (1 : ℝ))) '' Set.Icc 0 (0 + 1) := by
      rw [AddCircle.coe_image_Icc_eq]
      exact Set.mem_univ _
    obtain ⟨t, ht, he⟩ := hz
    refine ⟨⟨t, by simpa using ht⟩, ?_⟩
    have := congrArg e he
    simpa [e, AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk] using this
  have hcircle (p q : FiniteMatrixLoop C(X, ℂ)) (z : Circle) :
      (p.blockSum q).circleMap z = matrixUnitBlockSum (p.circleMap z) (q.circleMap z) := by
    obtain ⟨t, rfl⟩ := hsurj z
    simp only [FiniteMatrixLoop.circleMap_parameter]
    rfl
  have hblock (p q : FiniteMatrixLoop C(X, ℂ)) (z : D)
      (v : (Fin p.size → ℂ) × (Fin q.size → ℂ)) :
      join p.size q.size (p.diskBoundaryLinearEquiv z v.1, q.diskBoundaryLinearEquiv z v.2) =
        (p.blockSum q).diskBoundaryLinearEquiv z (join p.size q.size v) := by
    let c := complexDiskBoundaryHomeomorph ⟨z.val.2, z.property⟩
    change join p.size q.size
      (((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)) *ᵥ v.1,
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)) *ᵥ v.2) =
      (((p.blockSum q).circleMap c).val.map
          (fun f ↦ f z.val.1)) *ᵥ (join p.size q.size v)
    rw [hcircle]
    have hmatrix : (matrixUnitBlockSum (p.circleMap c) (q.circleMap c)).val.map
        (fun f ↦ f z.val.1) = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks
        ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map (fun f ↦ f z.val.1))
        0 0
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1))) := by
      ext i j
      change (Matrix.fromBlocks (p.circleMap c).val 0 0 (q.circleMap c).val
          (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) z.val.1 =
        Matrix.fromBlocks
          ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map
            (fun f ↦ f z.val.1)) 0 0
          ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
            (fun f ↦ f z.val.1)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
      cases finSumFinEquiv.symm i <;> cases finSumFinEquiv.symm j <;> rfl
    erw [hmatrix]
    change _ = (Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks
        ((p.circleMap c : Matrix (Fin p.size) (Fin p.size) C(X, ℂ)).map (fun f ↦ f z.val.1))
        0 0
        ((q.circleMap c : Matrix (Fin q.size) (Fin q.size) C(X, ℂ)).map
          (fun f ↦ f z.val.1)))).mulVecLin (join p.size q.size v)
    rw [Matrix.mulVecLin_reindex]
    have hcancel (w : Fin p.size ⊕ Fin q.size → ℂ) :
        LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv
          (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm w) = w := by
      funext i
      simp
    dsimp only [join]
    simp only [LinearEquiv.trans_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hcancel]
    apply congrArg (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)
    simp only [Matrix.mulVecLin_apply, Matrix.fromBlocks_mulVec]
    rcases v with ⟨v, w⟩
    funext i
    cases i <;> simp [Function.comp_def]
  constructor
  · -- In zero coordinates the original boundary is the identity on the original zero bundle.
    let p := FiniteMatrixLoop.constant (A := C(X, ℂ)) 0
    have hi : p.diskTriple.IsIsomorphic (BundleTriple.identity D (T 0)) := by
      refine ⟨Iso.refl _, Iso.refl _, ?_⟩
      intro z v
      funext i
      exact Fin.elim0 i
    change p.diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X) = 0
    exact (p.diskTriple.relativeClass_eq_of_isIsomorphic
      (isClosed_complexDiskBoundaryProduct X) _ hi).trans
        (BundleTriple.relativeClass_identity (isClosed_complexDiskBoundaryProduct X) (T 0))
  · intro p q
    -- The two global coordinate isomorphisms intertwine the actual boundary block.
    have hi : (p.diskTriple.sum q.diskTriple).IsIsomorphic (p.blockSum q).diskTriple := by
      refine ⟨sumIso p.size q.size, sumIso p.size q.size, ?_⟩
      intro z v
      change (join p.size q.size)
        ((RelativeTriple.sum p.diskTriple.boundary q.diskTriple.boundary).linearEquiv z v) = _
      rw [RelativeTriple.sum_apply]
      change join p.size q.size
        (p.diskBoundaryLinearEquiv z v.1, q.diskBoundaryLinearEquiv z v.2) =
          (p.blockSum q).diskBoundaryLinearEquiv z (join p.size q.size v)
      exact hblock p q z v
    change (p.blockSum q).diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X) =
      p.diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X) +
        q.diskTriple.relativeClass (isClosed_complexDiskBoundaryProduct X)
    rw [← BundleTriple.relativeClass_sum]
    exact (p.diskTriple.sum q.diskTriple).relativeClass_eq_of_isIsomorphic
      (isClosed_complexDiskBoundaryProduct X) _ hi |>.symm

end FiniteMatrixLoop

variable (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]

attribute [local instance] complexUnitClosedDisc_compactSpace complexUnitClosedDisc_t2Space

/-- The actual disk-triple comparison descended to stable based loop classes. -/
def stableMatrixLoopToDiskRelative :
    StableMatrixLoopClass C(X, ℂ) →+ RelativeKZero.{_, 0}
      (complexDiskBoundaryProduct X) (isClosed_complexDiskBoundaryProduct X) where
  toFun := Quotient.lift FiniteMatrixLoop.diskRelativeClass
    (fun p q h ↦ (p.diskRelativeClass_eq_iff_stablyHomotopic q).2 h)
  map_zero' := FiniteMatrixLoop.diskRelativeClass_additive.1
  map_add' := fun p q ↦ Quotient.inductionOn₂ p q
    (FiniteMatrixLoop.diskRelativeClass_additive.2)

/-- Karoubi III.1.8: the specified loop-to-difference-class homomorphism is bijective. -/
theorem stableMatrixLoopToDiskRelative_bijective :
    Function.Bijective (stableMatrixLoopToDiskRelative X) := by
  /- Surjectivity follows from normalized finite-loop representatives. For
  injectivity, choose finite representatives of two stable loop classes and use
  diskRelativeClass_eq_iff_stablyHomotopic. The equivalence relation obtained is
  exactly the one defining StableMatrixLoopClass, with no additional relations. -/
  constructor
  · intro a b
    refine Quotient.inductionOn₂ a b ?_
    intro p q h
    exact Quotient.sound ((p.diskRelativeClass_eq_iff_stablyHomotopic q).mp h)
  · intro z
    obtain ⟨p, hp⟩ := FiniteMatrixLoop.diskRelativeClass_surjective z
    exact ⟨stableMatrixLoopClass p, hp⟩

/-- The additive identification whose forward map is the actual disk-triple construction. -/
def stableMatrixLoopDiskRelativeEquiv : StableMatrixLoopClass C(X, ℂ) ≃+
    RelativeKZero.{_, 0} (complexDiskBoundaryProduct X) (isClosed_complexDiskBoundaryProduct X) :=
  AddEquiv.ofBijective (stableMatrixLoopToDiskRelative X)
    (stableMatrixLoopToDiskRelative_bijective X)

end AtiyahSinger
